/*
 *
 *  Adapted by Sam Siewert for use with UVC web cameras and Bt878 frame
 *  grabber NTSC cameras to acquire digital video from a source,
 *  time-stamp each frame acquired, save to a PGM or PPM file.
 *
 *  The original code adapted was open source from V4L2 API and had the
 *  following use and incorporation policy:
 * 
 *  This program can be used and distributed without restrictions.
 *
 *      This program is provided with the V4L2 API
 * see http://linuxtv.org/docs.php for more information
 */

#define __GNU_SOURCE
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <assert.h>

#include <getopt.h>             /* getopt_long() */

#include <fcntl.h>              /* low-level i/o */
#include <unistd.h>
#include <errno.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <sys/time.h>
#include <sys/mman.h>
#include <sys/ioctl.h>
#include <math.h>
#include <linux/videodev2.h>
#include <syslog.h>
#include <time.h>


#define CLEAR(x) memset(&(x), 0, sizeof(x))
//#define COLOR_CONVERT_RGB

#define MAX_WIDTH 1280   //using what I saw for bigbuff
#define MAX_HEIGHT 960 //using what I saw for bigbuff
#define HRES 640
#define VRES 480
#define HRES_STR "640"
#define VRES_STR "480"
//#define HRES 320
//#define VRES 240
//#define HRES_STR "320"
//#define VRES_STR "240"

//ITEMS FOR TIMEKEEPING
#define SAMPLE_COUNT 135

static double acq_times_ms[SAMPLE_COUNT];
static double proc_times_ms[SAMPLE_COUNT];
static double write_times_ms[SAMPLE_COUNT];
static double frame_times_ms[SAMPLE_COUNT];
struct timespec t_frame_start[SAMPLE_COUNT];
struct timespec t_frame_end[SAMPLE_COUNT];


int g_frame_idx = 0;   // increments as count decrements
int warmup_frames = 35; // discard first 20 frames

static unsigned char convert_buf[MAX_WIDTH * MAX_HEIGHT];
static unsigned char dest_buf[MAX_WIDTH * MAX_HEIGHT];


// Format is used by a number of functions, so made as a file global
static struct v4l2_format fmt;
// always ignore first 20 frames
int framecnt=-35;

enum io_method 
{
        IO_METHOD_READ,
        IO_METHOD_MMAP,
        IO_METHOD_USERPTR,
};

struct buffer 
{
        void   *start;
        size_t  length;
};

static char            *dev_name;
//static enum io_method   io = IO_METHOD_USERPTR;
//static enum io_method   io = IO_METHOD_READ;
static enum io_method   io = IO_METHOD_MMAP;
static int              fd = -1;
struct buffer          *buffers;
static unsigned int     n_buffers;
static int              out_buf;
static int              force_format=1;
static int              frame_count = (135);


//TIME HELPERS
//Simple helper to convert a timespec to ms
static inline double diff_ms(const struct timespec *start,
                             const struct timespec *end)
{
    long sec  = end->tv_sec  - start->tv_sec;
    long nsec = end->tv_nsec - start->tv_nsec;
    return (double)sec * 1000.0 + (double)nsec / 1e6;
}


//STAT COMPUTE
//Structure to contain mean, max, and min computed from doubles, in my case time in ms
typedef struct {
    double mean;
    double min;
    double max;
    int    count;   /* number of valid samples used */
} stats_t;


static stats_t compute_stats_range(const double *arr, int start, int end)
{
    /* begin with 0 initialized stat structure for mean, min, max, sample count
    */
    stats_t s = {0.0, 0.0, 0.0, 0};
    //quick bound check
    if (start > end) return s;

    /* find first valid sample to initialize min/max */
    int i = start;
    while (i <= end && isnan(arr[i])) ++i;  //while in range and timespec is not a NaN
    if (i > end) return s; /* all NaNs or no data */

    double sum = 0.0;
    double minv = arr[i];   //begin with min and max on first valid entry
    double maxv = arr[i];
    int valid = 0;

    for (int j = start; j <= end; ++j) {
        double v = arr[j];
        if (isnan(v)) continue; 
        sum += v;
        if (v < minv) minv = v;
        if (v > maxv) maxv = v;
        ++valid;        //only increment on valid number
    }

    if (valid > 0) {
        s.mean  = sum / valid;
        s.min   = minv;
        s.max   = maxv;
        s.count = valid;
    }
    return s;
}




static void errno_exit(const char *s)
{
        fprintf(stderr, "%s error %d, %s\n", s, errno, strerror(errno));
        exit(EXIT_FAILURE);
}

static int xioctl(int fh, int request, void *arg)
{
        int r;

        do 
        {
            r = ioctl(fh, request, arg);

        } while (-1 == r && EINTR == errno);

        return r;
}

//AI was used to aid in the developmnt of this one helper function and the file dump
static int save_final_pgm(const char *filename,
                          const unsigned char *buf,
                          int width, int height)
{
    FILE *f = fopen(filename, "wb");
    if (!f) {
        perror("fopen");
        return -1;
    }

    /* Write ASCII header */
    if (fprintf(f, "P5\n%d %d\n255\n", width, height) < 0) {
        perror("fprintf");
        fclose(f);
        return -1;
    }

    /* Write image bytes; ensure all bytes are written */
    size_t to_write = (size_t)width * height;
    size_t written = 0;
    while (written < to_write) {
        size_t w = fwrite(buf + written, 1, to_write - written, f);
        if (w == 0) {
            if (ferror(f)) {
                perror("fwrite");
                fclose(f);
                return -1;
            }
        }
        written += w;
    }

    /* Flush and close to ensure data hits disk */
    fflush(f);
    fsync(fileno(f));
    fclose(f);
    return 0;
}

//AI aided in this dump function for my timings 
static int save_timings_csv(const char *filename,
                            const double *acq, const double *proc,
                            const double *write, const double *frame,
                            int start_idx, int end_idx)
{
    if (!filename || start_idx > end_idx) return -1;

    FILE *f = fopen(filename, "w");
    if (!f) {
        perror("fopen");
        return -1;
    }

    /* Header */
    fprintf(f, "index,acq_ms,proc_ms,write_ms,frame_ms\n");

    /* Write rows for indices in [start_idx, end_idx] */
    for (int i = start_idx; i <= end_idx; ++i) {
        /* Print NaN as empty field so tools can ignore it */
        if (isnan(acq[i]) && isnan(proc[i]) && isnan(write[i]) && isnan(frame[i])) {
            /* all NaNs: write index with empty fields */
            fprintf(f, "%d,, , ,\n", i);
            continue;
        }

        /* Use empty fields for individual NaNs */
        if (isnan(acq[i])) fprintf(f, "%d,,", i);
        else fprintf(f, "%d,%.6f,", i, acq[i]);

        if (isnan(proc[i])) fprintf(f, ",");
        else fprintf(f, "%.6f,", proc[i]);

        if (isnan(write[i])) fprintf(f, ",");
        else fprintf(f, "%.6f,", write[i]);

        if (isnan(frame[i])) fprintf(f, "\n");
        else fprintf(f, "%.6f\n", frame[i]);
    }

    /* Ensure data hits disk for final verification */
    fflush(f);
    fsync(fileno(f));
    fclose(f);
    return 0;
}

char ppm_header[]="P6\n#9999999999 sec 9999999999 msec \n"HRES_STR" "VRES_STR"\n255\n";
char ppm_dumpname[]="frames/test0000.ppm";

static void dump_ppm(const void *p, int size, unsigned int tag, struct timespec *time)
{
    int written, i, total, dumpfd;
   
    snprintf(&ppm_dumpname[11], 9, "%04d", tag);
    strncat(&ppm_dumpname[15], ".ppm", 5);
    dumpfd = open(ppm_dumpname, O_WRONLY | O_NONBLOCK | O_CREAT, 00666);

    snprintf(&ppm_header[4], 11, "%010d", (int)time->tv_sec);
    strncat(&ppm_header[14], " sec ", 5);
    snprintf(&ppm_header[19], 11, "%010d", (int)((time->tv_nsec)/1000000));
    strncat(&ppm_header[29], " msec \n"HRES_STR" "VRES_STR"\n255\n", 19);
    written=write(dumpfd, ppm_header, sizeof(ppm_header));

    total=0;

    do
    {
        written=write(dumpfd, p, size);
        total+=written;
    } while(total < size);

    printf("wrote %d bytes\n", total);

    close(dumpfd);
    
}


char pgm_header[]="P5\n#9999999999 sec 9999999999 msec \n"HRES_STR" "VRES_STR"\n255\n";
char pgm_dumpname[]="frames/test0000.pgm";

static void dump_pgm(const void *p, int size, unsigned int tag, struct timespec *time)
{
    int written, i, total, dumpfd;
   
    snprintf(&pgm_dumpname[11], 9, "%04d", tag);
    strncat(&pgm_dumpname[15], ".pgm", 5);
    dumpfd = open(pgm_dumpname, O_WRONLY | O_NONBLOCK | O_CREAT, 00666);

    snprintf(&pgm_header[4], 11, "%010d", (int)time->tv_sec);
    strncat(&pgm_header[14], " sec ", 5);
    snprintf(&pgm_header[19], 11, "%010d", (int)((time->tv_nsec)/1000000));
    strncat(&pgm_header[29], " msec \n"HRES_STR" "VRES_STR"\n255\n", 19);
    written=write(dumpfd, pgm_header, sizeof(pgm_header));

    total=0;

    do
    {
        written=write(dumpfd, p, size);
        total+=written;
    } while(total < size);

    printf("wrote %d bytes\n", total);

    close(dumpfd);
    
}


void yuv2rgb_float(float y, float u, float v, 
                   unsigned char *r, unsigned char *g, unsigned char *b)
{
    float r_temp, g_temp, b_temp;

    // R = 1.164(Y-16) + 1.1596(V-128)
    r_temp = 1.164*(y-16.0) + 1.1596*(v-128.0);  
    *r = r_temp > 255.0 ? 255 : (r_temp < 0.0 ? 0 : (unsigned char)r_temp);

    // G = 1.164(Y-16) - 0.813*(V-128) - 0.391*(U-128)
    g_temp = 1.164*(y-16.0) - 0.813*(v-128.0) - 0.391*(u-128.0);
    *g = g_temp > 255.0 ? 255 : (g_temp < 0.0 ? 0 : (unsigned char)g_temp);

    // B = 1.164*(Y-16) + 2.018*(U-128)
    b_temp = 1.164*(y-16.0) + 2.018*(u-128.0);
    *b = b_temp > 255.0 ? 255 : (b_temp < 0.0 ? 0 : (unsigned char)b_temp);
}


// This is probably the most acceptable conversion from camera YUYV to RGB
//
// Wikipedia has a good discussion on the details of various conversions and cites good references:
// http://en.wikipedia.org/wiki/YUV
//
// Also http://www.fourcc.org/yuv.php
//
// What's not clear without knowing more about the camera in question is how often U & V are sampled compared
// to Y.
//
// E.g. YUV444, which is equivalent to RGB, where both require 3 bytes for each pixel
//      YUV422, which we assume here, where there are 2 bytes for each pixel, with two Y samples for one U & V,
//              or as the name implies, 4Y and 2 UV pairs
//      YUV420, where for every 4 Ys, there is a single UV pair, 1.5 bytes for each pixel or 36 bytes for 24 pixels

void yuv2rgb(int y, int u, int v, unsigned char *r, unsigned char *g, unsigned char *b)
{
   int r1, g1, b1;

   // replaces floating point coefficients
   int c = y-16, d = u - 128, e = v - 128;       

   // Conversion that avoids floating point
   r1 = (298 * c           + 409 * e + 128) >> 8;
   g1 = (298 * c - 100 * d - 208 * e + 128) >> 8;
   b1 = (298 * c + 516 * d           + 128) >> 8;

   // Computed values may need clipping.
   if (r1 > 255) r1 = 255;
   if (g1 > 255) g1 = 255;
   if (b1 > 255) b1 = 255;

   if (r1 < 0) r1 = 0;
   if (g1 < 0) g1 = 0;
   if (b1 < 0) b1 = 0;

   *r = r1 ;
   *g = g1 ;
   *b = b1 ;
}


static void process_image(const void *p, int size)
{
    int i, out_i, newsize=0;
    unsigned char *pptr = (unsigned char *)p;
    struct timespec t_proc_start, t_proc_end, t_write_start, t_write_end;
    size_t gray_bytes = (size_t) size/2; //grayscale conversion is half frame size

    // record when process was called
    clock_gettime(CLOCK_MONOTONIC, &t_proc_start);

    //increment frame counter, once crosses 0 begin saving frames
    framecnt++;

    // This just dumps the frame to a file now, but you could replace with whatever image
    // processing you wish.

    if(fmt.fmt.pix.pixelformat == V4L2_PIX_FMT_YUYV)
    {
        // Pixels are YU and YV alternating, so YUYV which is 4 bytes
        // We want Y, so YY which is 2 bytes        
        
        for(i=0, out_i=0; i+3<size && out_i < (int)gray_bytes; i=i+4, out_i=out_i+2) //added +3 for safety if not %4 for some reason
        {
            // Y1=first byte and Y2=third byte
            convert_buf[out_i]=pptr[i];
            convert_buf[out_i+1]=pptr[i+2];
            
        }
        clock_gettime(CLOCK_MONOTONIC, &t_proc_end);
                if(g_frame_idx < SAMPLE_COUNT)
            {
                proc_times_ms[g_frame_idx] = diff_ms(&t_proc_start, &t_proc_end);
            }

        
        /*once past 20 frames, begin a memcpy. This mimics sending to output, so the location is overwritten and one final image is saved. No saving 
        requirements were given in the assignment so hopefully this is all that was required.*/
        if(framecnt > -1)
        {
             //copy over to destination and measure time
            clock_gettime(CLOCK_MONOTONIC, &t_write_start);
            if (gray_bytes > sizeof(dest_buf)) errno_exit("frame too large");   //guard memcopy
            memcpy(dest_buf, convert_buf, gray_bytes);
            clock_gettime(CLOCK_MONOTONIC, &t_write_end);
            clock_gettime(CLOCK_MONOTONIC, &t_frame_end[g_frame_idx]);
            if(g_frame_idx < SAMPLE_COUNT)
            {
                write_times_ms[g_frame_idx] = diff_ms(&t_write_start, &t_write_end);
            }
            //prints removed now tht verified to work
            //printf("Dump YUYV converted to YY size %d\n", size);
            //syslog(LOG_INFO, "Frame %d saved", g_frame_idx);
        }
    }
    else
    {
        printf("ERROR - unknown dump format\n");
    }

    fflush(stderr);
    fflush(stdout);
    g_frame_idx++;
}


static int read_frame(void)
{
    struct timespec t_acq_start, t_acq_end;
    struct v4l2_buffer buf;
    unsigned int i;

    switch (io)
    {

        // this is our method to take frames from system / kernel buffer
        case IO_METHOD_MMAP:
            //timestamp entry to read case
            
            CLEAR(buf);

            buf.type = V4L2_BUF_TYPE_VIDEO_CAPTURE;
            buf.memory = V4L2_MEMORY_MMAP;
            clock_gettime(CLOCK_MONOTONIC, &t_acq_start);
            clock_gettime(CLOCK_MONOTONIC, &t_frame_start[g_frame_idx]);
            
            if (-1 == xioctl(fd, VIDIOC_DQBUF, &buf))
            {
                switch (errno)
                {
                    case EAGAIN:
                        return 0;

                    case EIO:
                        /* Could ignore EIO, but drivers should only set for serious errors, although some set for
                           non-fatal errors too.
                         */
                        return 0;


                    default:
                        printf("mmap failure\n");
                        errno_exit("VIDIOC_DQBUF");
                }
            }
            clock_gettime(CLOCK_MONOTONIC, &t_acq_end);
            // store aquisition time in buffer for analysis
            if(g_frame_idx < SAMPLE_COUNT)
            {
                acq_times_ms[g_frame_idx] = diff_ms(&t_acq_start, &t_acq_end);
            }
            assert(buf.index < n_buffers);

            process_image(buffers[buf.index].start, buf.bytesused);
            //gather frame from kernel buffer
            if (-1 == xioctl(fd, VIDIOC_QBUF, &buf))
                    errno_exit("VIDIOC_QBUF");
            break;

    }

    //printf("R");
    return 1;
}


static void mainloop(void)
{
    unsigned int count;
    struct timespec read_delay;
    struct timespec time_error;
    struct timespec t_frame_start;
    struct timespec t_frame_end;


    // Replace this with a sequencer DELAY
    //
    // 250 million nsec is a 250 msec delay, for 4 fps
    // 1 sec for 1 fps
    //
    read_delay.tv_sec=1;
    read_delay.tv_nsec=0;

    count = frame_count;

    while (count > 0)
    {
        
        for (;;)
        {
 
            fd_set fds;
            struct timeval tv;
            int r;

            FD_ZERO(&fds);
            FD_SET(fd, &fds);

            /* Timeout. */
            tv.tv_sec = 2;
            tv.tv_usec = 0;
            //wait for frame or timeout
            r = select(fd + 1, &fds, NULL, NULL, &tv);
            //error
            if (-1 == r)
            {
                if (EINTR == errno)
                    continue;
                errno_exit("select");
            }
            //timeout
            if (0 == r)
            {
                fprintf(stderr, "select timeout\n");
                exit(EXIT_FAILURE);
            }
            //r>0 frame is available
            if (read_frame())
            {
                if(nanosleep(&read_delay, &time_error) != 0)
                    perror("nanosleep");
                else
                    //printf("time_error.tv_sec=%ld, time_error.tv_nsec=%ld\n", time_error.tv_sec, time_error.tv_nsec);

                count--;
                break;
            }

            /* EAGAIN - continue select loop unless count done. */
            if(count <= 0) break;
        }

        if(count <= 0) break;
    }
}

static void stop_capturing(void)
{
        enum v4l2_buf_type type;

        switch (io) {
        case IO_METHOD_READ:
                /* Nothing to do. */
                break;

        case IO_METHOD_MMAP:
        case IO_METHOD_USERPTR:
                type = V4L2_BUF_TYPE_VIDEO_CAPTURE;
                if (-1 == xioctl(fd, VIDIOC_STREAMOFF, &type))
                        errno_exit("VIDIOC_STREAMOFF");
                break;
        }
}

static void start_capturing(void)
{
        unsigned int i;
        enum v4l2_buf_type type;

        switch (io) 
        {

        case IO_METHOD_READ:
                /* Nothing to do. */
                break;

        case IO_METHOD_MMAP:
                for (i = 0; i < n_buffers; ++i) 
                {
                        printf("allocated buffer %d\n", i);
                        struct v4l2_buffer buf;

                        CLEAR(buf);
                        buf.type = V4L2_BUF_TYPE_VIDEO_CAPTURE;
                        buf.memory = V4L2_MEMORY_MMAP;
                        buf.index = i;

                        if (-1 == xioctl(fd, VIDIOC_QBUF, &buf))
                                errno_exit("VIDIOC_QBUF");
                }
                type = V4L2_BUF_TYPE_VIDEO_CAPTURE;
                if (-1 == xioctl(fd, VIDIOC_STREAMON, &type))
                        errno_exit("VIDIOC_STREAMON");
                break;

        case IO_METHOD_USERPTR:
                for (i = 0; i < n_buffers; ++i) {
                        struct v4l2_buffer buf;

                        CLEAR(buf);
                        buf.type = V4L2_BUF_TYPE_VIDEO_CAPTURE;
                        buf.memory = V4L2_MEMORY_USERPTR;
                        buf.index = i;
                        buf.m.userptr = (unsigned long)buffers[i].start;
                        buf.length = buffers[i].length;

                        if (-1 == xioctl(fd, VIDIOC_QBUF, &buf))
                                errno_exit("VIDIOC_QBUF");
                }
                type = V4L2_BUF_TYPE_VIDEO_CAPTURE;
                if (-1 == xioctl(fd, VIDIOC_STREAMON, &type))
                        errno_exit("VIDIOC_STREAMON");
                break;
        }
}

static void uninit_device(void)
{
        unsigned int i;

        switch (io) {
        case IO_METHOD_READ:
                free(buffers[0].start);
                break;

        case IO_METHOD_MMAP:
                for (i = 0; i < n_buffers; ++i)
                        if (-1 == munmap(buffers[i].start, buffers[i].length))
                                errno_exit("munmap");
                break;

        case IO_METHOD_USERPTR:
                for (i = 0; i < n_buffers; ++i)
                        free(buffers[i].start);
                break;
        }

        free(buffers);
}

static void init_read(unsigned int buffer_size)
{
        buffers = calloc(1, sizeof(*buffers));

        if (!buffers) 
        {
                fprintf(stderr, "Out of memory\n");
                exit(EXIT_FAILURE);
        }

        buffers[0].length = buffer_size;
        buffers[0].start = malloc(buffer_size);

        if (!buffers[0].start) 
        {
                fprintf(stderr, "Out of memory\n");
                exit(EXIT_FAILURE);
        }
}

static void init_mmap(void)
{
        struct v4l2_requestbuffers req;

        CLEAR(req);

        req.count = 6;
        req.type = V4L2_BUF_TYPE_VIDEO_CAPTURE;
        req.memory = V4L2_MEMORY_MMAP;

        if (-1 == xioctl(fd, VIDIOC_REQBUFS, &req)) 
        {
                if (EINVAL == errno) 
                {
                        fprintf(stderr, "%s does not support "
                                 "memory mapping\n", dev_name);
                        exit(EXIT_FAILURE);
                } else 
                {
                        errno_exit("VIDIOC_REQBUFS");
                }
        }

        if (req.count < 2) 
        {
                fprintf(stderr, "Insufficient buffer memory on %s\n", dev_name);
                exit(EXIT_FAILURE);
        }

        buffers = calloc(req.count, sizeof(*buffers));

        if (!buffers) 
        {
                fprintf(stderr, "Out of memory\n");
                exit(EXIT_FAILURE);
        }

        for (n_buffers = 0; n_buffers < req.count; ++n_buffers) {
                struct v4l2_buffer buf;

                CLEAR(buf);

                buf.type        = V4L2_BUF_TYPE_VIDEO_CAPTURE;
                buf.memory      = V4L2_MEMORY_MMAP;
                buf.index       = n_buffers;

                if (-1 == xioctl(fd, VIDIOC_QUERYBUF, &buf))
                        errno_exit("VIDIOC_QUERYBUF");

                buffers[n_buffers].length = buf.length;
                buffers[n_buffers].start =
                        mmap(NULL /* start anywhere */,
                              buf.length,
                              PROT_READ | PROT_WRITE /* required */,
                              MAP_SHARED /* recommended */,
                              fd, buf.m.offset);

                if (MAP_FAILED == buffers[n_buffers].start)
                        errno_exit("mmap");
        }
}

static void init_userp(unsigned int buffer_size)
{
        struct v4l2_requestbuffers req;

        CLEAR(req);

        req.count  = 4;
        req.type   = V4L2_BUF_TYPE_VIDEO_CAPTURE;
        req.memory = V4L2_MEMORY_USERPTR;

        if (-1 == xioctl(fd, VIDIOC_REQBUFS, &req)) {
                if (EINVAL == errno) {
                        fprintf(stderr, "%s does not support "
                                 "user pointer i/o\n", dev_name);
                        exit(EXIT_FAILURE);
                } else {
                        errno_exit("VIDIOC_REQBUFS");
                }
        }

        buffers = calloc(4, sizeof(*buffers));

        if (!buffers) {
                fprintf(stderr, "Out of memory\n");
                exit(EXIT_FAILURE);
        }

        for (n_buffers = 0; n_buffers < 4; ++n_buffers) {
                buffers[n_buffers].length = buffer_size;
                buffers[n_buffers].start = malloc(buffer_size);

                if (!buffers[n_buffers].start) {
                        fprintf(stderr, "Out of memory\n");
                        exit(EXIT_FAILURE);
                }
        }
}

static void init_device(void)
{
    struct v4l2_capability cap;
    struct v4l2_cropcap cropcap;
    struct v4l2_crop crop;
    unsigned int min;

    if (-1 == xioctl(fd, VIDIOC_QUERYCAP, &cap))
    {
        if (EINVAL == errno) {
            fprintf(stderr, "%s is no V4L2 device\n",
                     dev_name);
            exit(EXIT_FAILURE);
        }
        else
        {
                errno_exit("VIDIOC_QUERYCAP");
        }
    }

    if (!(cap.capabilities & V4L2_CAP_VIDEO_CAPTURE))
    {
        fprintf(stderr, "%s is no video capture device\n",
                 dev_name);
        exit(EXIT_FAILURE);
    }

    switch (io)
    {
        case IO_METHOD_READ:
            if (!(cap.capabilities & V4L2_CAP_READWRITE))
            {
                fprintf(stderr, "%s does not support read i/o\n",
                         dev_name);
                exit(EXIT_FAILURE);
            }
            break;

        case IO_METHOD_MMAP:
        case IO_METHOD_USERPTR:
            if (!(cap.capabilities & V4L2_CAP_STREAMING))
            {
                fprintf(stderr, "%s does not support streaming i/o\n",
                         dev_name);
                exit(EXIT_FAILURE);
            }
            break;
    }


    /* Select video input, video standard and tune here. */


    CLEAR(cropcap);

    cropcap.type = V4L2_BUF_TYPE_VIDEO_CAPTURE;

    if (0 == xioctl(fd, VIDIOC_CROPCAP, &cropcap))
    {
        crop.type = V4L2_BUF_TYPE_VIDEO_CAPTURE;
        crop.c = cropcap.defrect; /* reset to default */

        if (-1 == xioctl(fd, VIDIOC_S_CROP, &crop))
        {
            switch (errno)
            {
                case EINVAL:
                    /* Cropping not supported. */
                    break;
                default:
                    /* Errors ignored. */
                        break;
            }
        }

    }
    else
    {
        /* Errors ignored. */
    }


    CLEAR(fmt);

    fmt.type = V4L2_BUF_TYPE_VIDEO_CAPTURE;

    if (force_format)
    {
        printf("FORCING FORMAT\n");
        fmt.fmt.pix.width       = HRES;
        fmt.fmt.pix.height      = VRES;

        // Specify the Pixel Coding Formate here

        // This one works for Logitech C200
        fmt.fmt.pix.pixelformat = V4L2_PIX_FMT_YUYV;

        //fmt.fmt.pix.pixelformat = V4L2_PIX_FMT_UYVY;
        //fmt.fmt.pix.pixelformat = V4L2_PIX_FMT_VYUY;

        // Would be nice if camera supported
        //fmt.fmt.pix.pixelformat = V4L2_PIX_FMT_GREY;
        //fmt.fmt.pix.pixelformat = V4L2_PIX_FMT_RGB24;

        //fmt.fmt.pix.field       = V4L2_FIELD_INTERLACED;
        fmt.fmt.pix.field       = V4L2_FIELD_NONE;

        if (-1 == xioctl(fd, VIDIOC_S_FMT, &fmt))
                errno_exit("VIDIOC_S_FMT");

        /* Note VIDIOC_S_FMT may change width and height. */
    }
    else
    {
        printf("ASSUMING FORMAT\n");
        /* Preserve original settings as set by v4l2-ctl for example */
        if (-1 == xioctl(fd, VIDIOC_G_FMT, &fmt))
                    errno_exit("VIDIOC_G_FMT");
    }

    /* Buggy driver paranoia. */
    min = fmt.fmt.pix.width * 2;
    if (fmt.fmt.pix.bytesperline < min)
            fmt.fmt.pix.bytesperline = min;
    min = fmt.fmt.pix.bytesperline * fmt.fmt.pix.height;
    if (fmt.fmt.pix.sizeimage < min)
            fmt.fmt.pix.sizeimage = min;

    switch (io)
    {
        case IO_METHOD_READ:
            init_read(fmt.fmt.pix.sizeimage);
            break;

        case IO_METHOD_MMAP:
            init_mmap();
            break;

        case IO_METHOD_USERPTR:
            init_userp(fmt.fmt.pix.sizeimage);
            break;
    }
}


static void close_device(void)
{
        if (-1 == close(fd))
                errno_exit("close");

        fd = -1;
}

static void open_device(void)
{
        struct stat st;

        if (-1 == stat(dev_name, &st)) {
                fprintf(stderr, "Cannot identify '%s': %d, %s\n",
                         dev_name, errno, strerror(errno));
                exit(EXIT_FAILURE);
        }

        if (!S_ISCHR(st.st_mode)) {
                fprintf(stderr, "%s is no device\n", dev_name);
                exit(EXIT_FAILURE);
        }

        fd = open(dev_name, O_RDWR /* required */ | O_NONBLOCK, 0);

        if (-1 == fd) {
                fprintf(stderr, "Cannot open '%s': %d, %s\n",
                         dev_name, errno, strerror(errno));
                exit(EXIT_FAILURE);
        }
}

static void usage(FILE *fp, int argc, char **argv)
{
        fprintf(fp,
                 "Usage: %s [options]\n\n"
                 "Version 1.3\n"
                 "Options:\n"
                 "-d | --device name   Video device name [%s]\n"
                 "-h | --help          Print this message\n"
                 "-m | --mmap          Use memory mapped buffers [default]\n"
                 "-r | --read          Use read() calls\n"
                 "-u | --userp         Use application allocated buffers\n"
                 "-o | --output        Outputs stream to stdout\n"
                 "-f | --format        Force format to 640x480 GREY\n"
                 "-c | --count         Number of frames to grab [%i]\n"
                 "",
                 argv[0], dev_name, frame_count);
}

static const char short_options[] = "d:hmruofc:";

static const struct option
long_options[] = {
        { "device", required_argument, NULL, 'd' },
        { "help",   no_argument,       NULL, 'h' },
        { "mmap",   no_argument,       NULL, 'm' },
        { "read",   no_argument,       NULL, 'r' },
        { "userp",  no_argument,       NULL, 'u' },
        { "output", no_argument,       NULL, 'o' },
        { "format", no_argument,       NULL, 'f' },
        { "count",  required_argument, NULL, 'c' },
        { 0, 0, 0, 0 }
};

int main(int argc, char **argv)
{
    if(argc > 1)
        dev_name = argv[1];
    else
        dev_name = "/dev/video0";

    for (;;)
    {
        int idx;
        int c;

        c = getopt_long(argc, argv,
                    short_options, long_options, &idx);

        if (-1 == c)
            break;

        switch (c)
        {
            case 0: /* getopt_long() flag */
                break;

            case 'd':
                dev_name = optarg;
                break;

            case 'h':
                usage(stdout, argc, argv);
                exit(EXIT_SUCCESS);

            case 'm':
                io = IO_METHOD_MMAP;
                break;

            case 'r':
                io = IO_METHOD_READ;
                break;

            case 'u':
                io = IO_METHOD_USERPTR;
                break;

            case 'o':
                out_buf++;
                break;

            case 'f':
                force_format++;
                break;

            case 'c':
                errno = 0;
                frame_count = strtol(optarg, NULL, 0);
                if (errno)
                        errno_exit(optarg);
                break;

            default:
                usage(stderr, argc, argv);
                exit(EXIT_FAILURE);
        }
    }
    //initialize timing arrays to NaN for safety
    for (int k = 0; k < SAMPLE_COUNT; ++k) {
    acq_times_ms[k] = proc_times_ms[k] = write_times_ms[k] = frame_times_ms[k] = NAN;
    }


    // initialization of V4L2
    open_device();
    init_device();
    openlog("capture", LOG_PID | LOG_CONS, LOG_USER);
    start_capturing();

    // service loop frame read
    mainloop();

    //calculate frame time 
    for(int i = 0; i<g_frame_idx && i<SAMPLE_COUNT; i++){
        frame_times_ms[i] = diff_ms(&t_frame_start[i], &t_frame_end[i]);
    }

    // save final image to show processing is proper
    save_final_pgm("final_gray.pgm", dest_buf, fmt.fmt.pix.width, fmt.fmt.pix.height);

    //compute stats on acq, convert, and write back
    stats_t acq_stats = compute_stats_range(acq_times_ms, warmup_frames, g_frame_idx-1);
    stats_t conv_stats = compute_stats_range(proc_times_ms, warmup_frames, g_frame_idx-1);
    stats_t write_stats = compute_stats_range(write_times_ms, warmup_frames, g_frame_idx-1);
    stats_t frame_stats = compute_stats_range(frame_times_ms, warmup_frames, g_frame_idx-1);

    syslog(LOG_INFO, "Capture complete with grayscale conversion: stored_samples=%d warmup=%d", g_frame_idx, warmup_frames);

    syslog(LOG_INFO, "Acquisition ms: mean=%.3f min=%.3f max=%.3f (n=%d)",
       acq_stats.mean, acq_stats.min, acq_stats.max, acq_stats.count);

    syslog(LOG_INFO, "Conversion ms: mean=%.3f min=%.3f max=%.3f (n=%d)",
       conv_stats.mean, conv_stats.min, conv_stats.max, conv_stats.count);

    syslog(LOG_INFO, "Write ms: mean=%.3f min=%.3f max=%.3f (n=%d)",
       write_stats.mean, write_stats.min, write_stats.max, write_stats.count);

    syslog(LOG_INFO, "Full frame ms: mean=%.3f min=%.3f max=%.3f (n=%d)",
       frame_stats.mean, frame_stats.min, frame_stats.max, frame_stats.count);

    save_timings_csv("timings.csv", acq_times_ms, proc_times_ms, write_times_ms, frame_times_ms, warmup_frames, (g_frame_idx-1));

    // shutdown of frame acquisition service
    stop_capturing();
    uninit_device();
    close_device();
    fprintf(stderr, "\n");
    closelog();
    return 0;
}
