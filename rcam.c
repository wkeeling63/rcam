/*
 *  rcam.c 
 * This program creates a video H.264 stream using MMAL and a raw audio stream 
 * from ALSA using Adafruit I2S MEMS Microphone (SPH0645LM4H).  The audio 
 * stream is encoded to ACC and both streams are added to flash video 
 * container by FFMPEG api.
 *     
 */  
/* add crap */
#include <getopt.h>
#include <string.h>
#include <ctype.h>
#include <alsa/asoundlib.h>
#include <sys/time.h>
#include <sys/signal.h>
#include "gettext.h"

#include <stdio.h>
#include <stdlib.h>
#include <memory.h>
#include <sysexits.h>
#include <sys/socket.h>
#include <time.h>
#include <semaphore.h>
#include <stdbool.h>

#include <libavformat/avformat.h>
#include <libavcodec/avcodec.h>
#include "libavformat/avio.h"
#include "libavutil/audio_fifo.h"
#include "libavutil/avassert.h"
#include "libavutil/avstring.h"
#include "libavutil/frame.h"
#include "libavutil/opt.h"
#include "libswresample/swresample.h"
#include <libavutil/channel_layout.h>
#include <libavutil/mathematics.h>
#include <libavutil/timestamp.h>

#include "bcm_host.h"
#include "interface/vcos/vcos.h"

#include "interface/mmal/mmal.h"
#include "interface/mmal/mmal_logging.h"
#include "interface/mmal/mmal_buffer.h"
#include "interface/mmal/util/mmal_util.h"
#include "interface/mmal/util/mmal_util_params.h"
#include "interface/mmal/util/mmal_default_components.h"
#include "interface/mmal/util/mmal_connection.h"
#include "interface/mmal/mmal_parameters_camera.h"

#include "rcamCamControl.h"
#include "rcamHelpers.h"
#include "racecam.h"


#ifndef LLONG_MAX
#define LLONG_MAX    9223372036854775807LL
#endif

#define DEFAULT_FORMAT		SND_PCM_FORMAT_S32_LE
#define DEFAULT_SPEED 		44100
#define BUFFER_SIZE		262144
#define DEFAULT_CHANNELS_IN	2
#define DEFAULT_FPS		25

static char *command;
static snd_pcm_t *handle;
static struct {
	snd_pcm_format_t format;
	unsigned int channels;
	unsigned int rate;
} hwparams, rhwparams;
static int timelimit = 0;
static snd_pcm_stream_t stream = SND_PCM_STREAM_PLAYBACK;
static u_char *audiobuf = NULL, *rlbufs = NULL;
static snd_pcm_uframes_t chunk_size = 0;
static snd_pcm_uframes_t buffer_frames = 0;
static size_t bits_per_sample, bits_per_frame;
static size_t chunk_bytes;
static snd_output_t *logerr;
static long long max_file_size = 0;
static int badparm=0;
static int height = 1080;
static int width = 1920;
static int camera = 1;
static int stereo_mode = -1;
static int intraframe = 30;
static int quantisation = 0;
static int abort_flg = 0;
static int channel_num = 1;
static int write_video_msg = 0;
static int write_audio_msg = 0;

static int64_t start, atime, vtime, wstart;

static off64_t pbrec_count = LLONG_MAX; 

char file_name[128];
AVFormatContext *flv_frmtctx = NULL;
AVIOContext *io_ctx = NULL;
AVCodecContext *raw_codec_ctx = NULL, *aac_codec_ctx = NULL, *h264_codec_ctx = NULL;
AVCodec *aac_codec = NULL, *raw_codec = NULL, *h264_codec = NULL;
AVStream *aac_audio_strm = NULL, *h264_video_strm = NULL;
SwrContext *resample_ctx = NULL;
AVAudioFifo *fifo = NULL;
AVFrame *infrm, *outfrm;

int64_t audio_samples=0; 

#define error(...) do {\
	fprintf(stderr, "%s: %s:%d: ", command, __FUNCTION__, __LINE__); \
	fprintf(stderr, __VA_ARGS__); \
	putc('\n', stderr); \
} while (0)

static void prt_hours(int64_t ticks)
{
	int64_t msec, sec, min, hr;
	msec = ticks%1000000ULL;
	ticks -= msec;
	ticks = ticks/1000000ULL;
	sec = ticks%60;
	ticks -=sec;
	ticks = ticks/60;
	min = ticks%60;
	ticks -=min;
	hr = ticks/60;
	fprintf(stderr, "%4llu:%02llu:%02llu.%06llu", hr, min, sec, msec);
}

static void prt_secs(int64_t ticks)
{
	int64_t msec, sec;
	msec = ticks%1000000ULL;
	ticks -= msec;
	sec = ticks%60;
	fprintf(stderr, "%2llu.%06llu", sec, msec);
}

static void usage(char *command)
{
	printf(
("Usage: %s [OPTION]... [FILE]...\n"
"\n"
"-?, --help              help\n"
"-D, --device=NAME       select PCM by name\n"  
"-d, --duration=#        interrupt after # seconds\n"
"-h, --height=#        	 height # pixels - defaults to max 1080\n"
"-w, --width=#        	 width # pixels - defaults to max 1920\n"
"-c, --camera=#        	 camera # - defaults to 1 \n"
"-s, --stereo=#        	 stereo video mode off, sbs or tb - defaults to tb\n"
"-q, --quantisation=#    quantisation parameter\n"
"-n, --number=#          number of audio channels\n"
"-i, --intraframe=#    	 intra key frame rate # frame\n"  
"-v, --verbose=#    	 write info messages to STDERR 1=video, 2=audio or 3=both\n")   
		, command);
} 
int init_avapi(char *filename)
{
	int status=0;

//  setup format context and io context

	if ((status = avio_open(&io_ctx, filename, AVIO_FLAG_WRITE)))
		{
		fprintf(stderr, "Could not open output file '%s' (error '%s')\n", filename, av_err2str(status));
		return -1;
		}
	avformat_alloc_output_context2(&flv_frmtctx, NULL, "flv", NULL);
	if (!flv_frmtctx) 
		{
		fprintf(stderr, "Could not allocate output format context\n");
		return -1;
		}
	flv_frmtctx->pb = io_ctx;
	if (!(flv_frmtctx->url = av_strdup(filename))) 
		{
        fprintf(stderr, "Could not copy url.\n");
        return -1;
		}
		
// Setup  H264 codec
	h264_codec = avcodec_find_encoder(AV_CODEC_ID_H264);
	if (!h264_codec)
		{
		fprintf(stderr, "H264 codec id not found!\n");
		return -1;
		}	

	h264_video_strm = avformat_new_stream(flv_frmtctx, NULL);
	if (!h264_video_strm) 
		{
		fprintf(stderr, "Could not allocate H264 stream\n");
		return -1;
		}
        
	h264_codec_ctx = avcodec_alloc_context3(h264_codec); 
	if (!h264_codec_ctx) 
		{
		fprintf(stderr, "Could not alloc an video encoding context\n");
		return -1;
		}
    
   	h264_codec_ctx->codec_id = AV_CODEC_ID_H264;
	h264_codec_ctx->bit_rate = 400000;
	h264_codec_ctx->width = width;
	h264_codec_ctx->height = height;
	h264_codec_ctx->sample_rate    = DEFAULT_FPS;
	h264_codec_ctx->gop_size      = intraframe;                  
	h264_codec_ctx->pix_fmt       = AV_PIX_FMT_YUVJ420P;   

	h264_video_strm->time_base.den = DEFAULT_FPS;   // Set the sample rate for the container
	h264_video_strm->time_base.num = 1;
	h264_video_strm->avg_frame_rate.num = DEFAULT_FPS;   // Set the sample rate for the container
	h264_video_strm->avg_frame_rate.den = 1;
	h264_video_strm->r_frame_rate.num = DEFAULT_FPS;   // Set the sample rate for the container
	h264_video_strm->r_frame_rate.den = 1;

	if (flv_frmtctx->oformat->flags & AVFMT_GLOBALHEADER) { // Some container formats (like MP4) require global headers to be present.
		h264_codec_ctx->flags |= AV_CODEC_FLAG_GLOBAL_HEADER;}
        
	status = avcodec_parameters_from_context(h264_video_strm->codecpar, h264_codec_ctx);
	if (status < 0) 
		{
		fprintf(stderr, "Could not initialize stream parameters\n");
		return -1;
		}
		
//  setup ACC codec and stream context
	aac_codec = avcodec_find_encoder(AV_CODEC_ID_AAC);
	if (!aac_codec)
		{
		fprintf(stderr, "AAC codec id not found!\n");
		return -1;
		}	
	aac_audio_strm = avformat_new_stream(flv_frmtctx, NULL);
	if (!aac_audio_strm) 
		{
		fprintf(stderr, "Could not allocate AAC stream\n");
		return -1;
		}
        
	aac_codec_ctx = avcodec_alloc_context3(aac_codec); 
	if (!aac_codec_ctx) 
		{
		fprintf(stderr, "Could not alloc an encoding context\n");
		return -1;
		}
    
	aac_codec_ctx->channels       = channel_num;
	aac_codec_ctx->channel_layout = av_get_default_channel_layout(channel_num);
	aac_codec_ctx->sample_rate    = DEFAULT_SPEED;
	aac_codec_ctx->sample_fmt     = aac_codec->sample_fmts[0];
	aac_codec_ctx->bit_rate       = 64000;
	aac_codec_ctx->strict_std_compliance = FF_COMPLIANCE_EXPERIMENTAL;  // Allow the use of the experimental AAC encoder.

	aac_audio_strm->time_base.den = DEFAULT_SPEED;   // Set the sample rate for the container
	aac_audio_strm->time_base.num = 1;
    
	if (flv_frmtctx->oformat->flags & AVFMT_GLOBALHEADER)  // Some container formats (like MP4) require global headers to be present.
		aac_codec_ctx->flags |= AV_CODEC_FLAG_GLOBAL_HEADER;
        
	if ((status = avcodec_open2(aac_codec_ctx, aac_codec, NULL) < 0)) 
		{
		fprintf(stderr, "Could not open output codec (error '%s')\n", av_err2str(status));
		return -1;
		}
	status = avcodec_parameters_from_context(aac_audio_strm->codecpar, aac_codec_ctx);
	if (status < 0) 
		{
		fprintf(stderr, "Could not initialize stream parameters\n");
		return -1;
		}

//  	av_dump_format(flv_frmtctx, 0, "stderr", 1);

//  setup RAW codec and context
	raw_codec = avcodec_find_encoder(AV_CODEC_ID_PCM_S32LE_PLANAR);
	if (!raw_codec)
		{
		fprintf(stderr, "PCM_S32_LE codec id not found!\n");
		return -1;
		}	
	raw_codec_ctx = avcodec_alloc_context3(raw_codec); 
	if (!aac_codec_ctx) 
		{
		fprintf(stderr, "Could not alloc RAW context\n");
		return -1;
		}
    
	raw_codec_ctx->channels       = DEFAULT_CHANNELS_IN;
	raw_codec_ctx->channel_layout = av_get_default_channel_layout(DEFAULT_CHANNELS_IN);
	raw_codec_ctx->sample_rate    = DEFAULT_SPEED;
	raw_codec_ctx->sample_fmt     = raw_codec->sample_fmts[0];  // AV_SAMPLE_FMT_S32
	raw_codec_ctx->bit_rate       = 2822400;  // or 64000
	raw_codec_ctx->time_base.num  = 1;
	raw_codec_ctx->time_base.den  = DEFAULT_SPEED;
	raw_codec_ctx->strict_std_compliance = FF_COMPLIANCE_EXPERIMENTAL;   // Allow the use of the experimental AAC encoder.
    
//  setup resampler context
	resample_ctx = swr_alloc_set_opts(NULL, av_get_default_channel_layout(aac_codec_ctx->channels), aac_codec_ctx->sample_fmt,
		aac_codec_ctx->sample_rate, av_get_default_channel_layout(raw_codec_ctx->channels), raw_codec_ctx->sample_fmt,
		raw_codec_ctx->sample_rate, 0, NULL);
	if (!resample_ctx) 
		{
		fprintf(stderr, "Could not allocate resample context\n");
		return -1;
		}
	if ((status = swr_init(resample_ctx)) < 0) 
		{
		fprintf(stderr, "Could not open resample context\n");
		swr_free(&resample_ctx);
		return -1;
		}

//  write flv header 
//	flv_frmtctx->start_time_realtime=0;  // 0 should user system clock
	flv_frmtctx->start_time_realtime=get_microseconds64();
	status = avformat_write_header(flv_frmtctx, NULL);  // null if AVDictionary is unneeded????
	if (status < 0)
		{
		fprintf(stderr, "Write ouput header failed! STATUS %d\n", status);
		return -1;
		}


// setup fifo sample queue
	if (!(fifo = av_audio_fifo_alloc(AV_SAMPLE_FMT_S32P, DEFAULT_CHANNELS_IN, 1))) 
		{
		fprintf(stderr, "Could not allocate FIFO\n");
		return -1;
		}
    
// allocate and init work frames
	infrm=av_frame_alloc();	
	if (!infrm) {fprintf(stderr, "unable to allocate in frame!\n");}

	infrm->channel_layout=raw_codec_ctx->channel_layout;
	infrm->sample_rate=raw_codec_ctx->sample_rate;
	infrm->format=raw_codec_ctx->sample_fmt;
	infrm->nb_samples=aac_codec_ctx->frame_size;  
    
	status=av_frame_get_buffer(infrm, 0);  
	if (status) {fprintf(stderr, "unable to allocate in frame data! %d %s\n", status, av_err2str(status));}
    
	outfrm=av_frame_alloc();	
	if (!outfrm) {fprintf(stderr, "unable to allocate out frame!\n");}
	outfrm->channel_layout=aac_codec_ctx->channel_layout;
	outfrm->sample_rate=aac_codec_ctx->sample_rate;
	outfrm->format=aac_codec_ctx->sample_fmt;
	outfrm->nb_samples=aac_codec_ctx->frame_size;

	status=av_frame_get_buffer(outfrm, 0);
	if (status) {fprintf(stderr, "unable to allocate out frame data!\n");}

	return 0; 
}
int close_avapi(char *filename)
{
	int status;

	fprintf(stderr, "\n");

	if (outfrm) {av_frame_free(&outfrm);}
	if (infrm) {av_frame_free(&infrm);}
	
	if (fifo) {av_audio_fifo_free(fifo);}

	if (resample_ctx) {swr_init(resample_ctx);}

	if (aac_codec_ctx)
		{
		AVPacket packet;
		av_init_packet(&packet);  
		packet.data = NULL;
		packet.size = 0;
		avcodec_send_frame(aac_codec_ctx, NULL); 
		avcodec_receive_packet(aac_codec_ctx, &packet);
		do 	{
			av_write_frame(flv_frmtctx, &packet);
			status = avcodec_receive_packet(aac_codec_ctx, &packet);
			} 
		while (!status);
		}

	if (raw_codec_ctx) {avcodec_free_context(&raw_codec_ctx);}
	if (h264_codec_ctx) {avcodec_free_context(&h264_codec_ctx);}
	if (aac_codec_ctx) {avcodec_free_context(&aac_codec_ctx);}
		
	if (flv_frmtctx)
		{
//		if ((strncmp("file:", filename, 5))) 
//			{
//			status = av_write_trailer(flv_frmtctx);  
//			if (status < 0) {fprintf(stderr, "Write ouput trailer failed! STATUS %d\n", status);}
//			}   
		avformat_free_context(flv_frmtctx);
		}
	
	if (io_ctx)
		{
		if ((status = avio_close(io_ctx))) 
			{
			fprintf(stderr, "Could not close output file (error '%s')\n", av_err2str(status));
			return -1; 
			}
		}
	return 0;
}
static void encoder_buffer_callback(MMAL_PORT_T *port, MMAL_BUFFER_HEADER_T *buffer)
{

	MMAL_BUFFER_HEADER_T *new_buffer;
	static int64_t framecnt=0;

	PORT_USERDATA *pData = (PORT_USERDATA *)port->userdata;
	int *ap = pData->abort_ptr;
	if (*ap) {return;}

	if (pData)
		{
		int bytes_written = buffer->length;
		if (buffer->length)
			{
			mmal_buffer_header_mem_lock(buffer);
			if(buffer->flags & MMAL_BUFFER_HEADER_FLAG_CODECSIDEINFO)
				{
				bytes_written = buffer->length;
				fprintf(stderr, "skipped due to flag %d \n", buffer->flags);
				}
			else
				{			
				AVPacket *packet=pData->vpckt;
				int status;
				if (buffer->flags & MMAL_BUFFER_HEADER_FLAG_FRAME_END) 
					{
					if (buffer->flags & MMAL_BUFFER_HEADER_FLAG_KEYFRAME)
						{
						packet->flags=AV_PKT_FLAG_KEY+AV_PKT_FLAG_TRUSTED;
						}
					else
						{
						packet->flags=AV_PKT_FLAG_TRUSTED;
						}
					if (pData->vbuf_ptr == 0)
						{
						packet->data=buffer->data;
						packet->size=buffer->length;
						} 
					else
						{
						memcpy(pData->vbuf+pData->vbuf_ptr, buffer->data+buffer->offset, buffer->length);
						pData->vbuf_ptr += buffer->length;
						packet->data=pData->vbuf;
						packet->size=pData->vbuf_ptr;
						pData->vbuf_ptr=0;
						}
					packet->dts = packet->pts = (double) 1000 / DEFAULT_FPS * framecnt - 1023;
					sem_wait(pData->mutex);
					wstart = get_microseconds64();
					status=av_write_frame(flv_frmtctx, packet);
					int64_t etime = get_microseconds64();
					if (write_video_msg) 
						{
						prt_hours(etime  - start);
						fprintf(stderr, "    ");
						prt_secs(etime - wstart);
						fprintf(stderr, "    %6d  %4lld/μs  ", packet->size, packet->size/(etime - wstart));
						prt_secs(etime - vtime);
						fprintf(stderr, " Video %8lld \r", framecnt);
						}
					vtime = etime;
					sem_post(pData->mutex);
					if (status)
						{
						fprintf(stderr, "frame write error or flush %d\n", status);
						bytes_written = 0;
						}
					else 
						{
						++framecnt;
						bytes_written = buffer->length;
						}				
					}

				else
					{
					if (buffer->length >  BUFFER_SIZE - pData->vbuf_ptr) 
						{
						fprintf(stderr, "save vbuf to small\n");
						*ap = 1;
						}
					else
						{
						memcpy(pData->vbuf+pData->vbuf_ptr, buffer->data+buffer->offset, buffer->length);
						pData->vbuf_ptr+=buffer->length;
						bytes_written = buffer->length;	
						}
					}
				}

				mmal_buffer_header_mem_unlock(buffer);
				if (bytes_written != buffer->length)
					{
					vcos_log_error("Failed to write buffer data (%d from %d)- aborting", bytes_written, buffer->length);
					*ap = 1;
					}
			}
		}
	else
		{
		vcos_log_error("Received a encoder buffer callback with no state");
		}

	mmal_buffer_header_release(buffer);
	if (port->is_enabled)
		{
		MMAL_STATUS_T status;
		new_buffer = mmal_queue_get(pData->pstate->encoder_pool->queue);
		if (new_buffer)
			status = mmal_port_send_buffer(port, new_buffer);
		if (!new_buffer || status != MMAL_SUCCESS)
			vcos_log_error("Unable to return a buffer to the encoder port");
		}
}

int encode_and_write(u_char **data_in, int flush, sem_t *mutex)
{
	int status;
	int min_samples=infrm->nb_samples; 
	AVPacket packet;
	int64_t save_pts=0;

	if (flush) {min_samples=1;}

	while (av_audio_fifo_size(fifo) >= min_samples)
	{
	outfrm->pts = outfrm->pkt_dts = save_pts = (double) audio_samples * 1000 / DEFAULT_SPEED;
	status = av_audio_fifo_read(fifo, (void **)infrm->data, infrm->nb_samples);
	if (status < 0) 
		{
		fprintf(stderr, "fifo read failed! %d %s\n", status, av_err2str(status));
		return -1;
		}
	else
		{
		audio_samples+=status;
		}
	
	status = swr_convert_frame(resample_ctx, outfrm, infrm);
	if (status) {fprintf(stderr, "Frame convert %d (error '%s')\n", status, av_err2str(status));}
	
	av_init_packet(&packet); // Set the packet data and size so that it is recognized as being empty. 
	packet.data = NULL;
	packet.size = 0;


	status = avcodec_send_frame(aac_codec_ctx, outfrm);  
	if (status == AVERROR_EOF) // The encoder signals that it has nothing more to encode.
		{
		status = 0;
		fprintf(stderr, "EOF at send frame\n");
		goto cleanup;
		}
	 else 
		if (status < 0)
			{
			fprintf(stderr, "Could not send packet for encoding (error '%s')\n", av_err2str(status));
			return status;
			}
	status = avcodec_receive_packet(aac_codec_ctx, &packet);

	if (status == AVERROR(EAGAIN)) // If the encoder asks for more data to be able to provide an encoded frame, return indicating that no data is present.
		{
		status = 0;
		} 
	else 
		if (status == AVERROR_EOF) // If the last frame has been encoded, stop encoding.
			{
			status = 0;
			fprintf(stderr, "EOF at receive packet\n");
			goto cleanup;
			} 
		else 
			if (status < 0) 
				{
				fprintf(stderr, "Could not encode frame (error '%s')\n", av_err2str(status));  //get this if not loaded frame
				goto cleanup;
    			} 
			else 
				{
				packet.duration=0;
				packet.pos=-1;
				packet.dts=packet.pts=save_pts-1023;
				packet.stream_index = 1;
				sem_wait(mutex);
				wstart = get_microseconds64();
				status = av_write_frame(flv_frmtctx, &packet);
				int64_t etime = get_microseconds64();
				if (write_audio_msg)
					{
					prt_hours(etime  - start);
					fprintf(stderr, "    ");
					prt_secs(etime - wstart);
					fprintf(stderr, "    %6d  %4lld/μs  ", packet.size, packet.size/(etime - wstart));
					prt_secs(etime - atime);
					fprintf(stderr, " Audio %8lld\r", save_pts);
					}
				sem_post(mutex); 
				atime = etime;
				if (status < 0) 
					{
					fprintf(stderr, "Could not write frame (error '%s')\n", av_err2str(status));
					goto cleanup;
					}

				}
	}
	return status;


cleanup:
	av_packet_unref(&packet);
	return status;
}

/*
 *	Subroutine to clean up before exit.
 */
static void prg_exit(int code) 
{
	if (handle)
		snd_pcm_close(handle);
	exit(code);
}

static void signal_handler(int sig)
{
	static int in_aborting;

	if (in_aborting)
		return;

	in_aborting = 1;

	if (stream == SND_PCM_STREAM_CAPTURE) 
		{
		stream = -1;
		}

	if (handle && sig != SIGABRT) 
		{
		snd_pcm_close(handle);
		handle = NULL;
		}
	prg_exit(EXIT_FAILURE);
}


static void set_params(void)
{
	snd_pcm_hw_params_t *params;
	snd_pcm_uframes_t buffer_size;
	int err;

	snd_pcm_hw_params_alloca(&params);
	err = snd_pcm_hw_params_any(handle, params);
	if (err < 0) 
		{
		error(_("Broken configuration for this PCM: no configurations available"));
		prg_exit(EXIT_FAILURE);
		}
	err = snd_pcm_hw_params_set_access(handle, params, SND_PCM_ACCESS_RW_INTERLEAVED);

	if (err < 0) 
		{
		error(_("Access type not available"));
		prg_exit(EXIT_FAILURE);
		}
	err = snd_pcm_hw_params_set_format(handle, params, hwparams.format);
	if (err < 0) 
		{
		error(_("Sample format non available"));
		prg_exit(EXIT_FAILURE);
		}
	err = snd_pcm_hw_params_set_channels(handle, params, hwparams.channels);
	if (err < 0) 
		{
		error(_("Channels count non available"));
		prg_exit(EXIT_FAILURE);
		}


	err = snd_pcm_hw_params_set_rate_near(handle, params, &hwparams.rate, 0);
	assert(err >= 0);

	err = snd_pcm_hw_params(handle, params);
	if (err < 0) 
		{
		error(_("Unable to install hw params:"));
		snd_pcm_hw_params_dump(params, logerr);
		prg_exit(EXIT_FAILURE);
		}
	snd_pcm_hw_params_get_period_size(params, &chunk_size, 0);
	snd_pcm_hw_params_get_buffer_size(params, &buffer_size);
	if (chunk_size == buffer_size) 
		{
		error(_("Can't use period equal to buffer size (%lu == %lu)"),
		      chunk_size, buffer_size);
		prg_exit(EXIT_FAILURE);
		}

	bits_per_sample = snd_pcm_format_physical_width(hwparams.format);
	bits_per_frame = bits_per_sample * hwparams.channels;
	chunk_bytes = chunk_size * bits_per_frame / 8;

	audiobuf = (u_char *)malloc(chunk_bytes);
	if (audiobuf == NULL) 
		{
		error(_("not enough memory"));
		prg_exit(EXIT_FAILURE);
		}
	rlbufs = (u_char *)malloc(chunk_bytes);
	if (rlbufs == NULL) 
		{
		error(_("not enough memory"));
		prg_exit(EXIT_FAILURE);
		}

	buffer_frames = buffer_size;	/* for position test */
}

/* I/O error handler */
static void xrun(void)
{
	snd_pcm_status_t *status;
	int res;
	snd_pcm_status_alloca(&status);
	if ((res = snd_pcm_status(handle, status))<0) 
		{
		error(_("status error: %s"), snd_strerror(res));
		prg_exit(EXIT_FAILURE);
		}
	
	if (snd_pcm_status_get_state(status) == SND_PCM_STATE_XRUN) 
		{
		if ((res = snd_pcm_prepare(handle))<0) 
			{
			error(_("xrun: prepare error: %s"), snd_strerror(res));
			prg_exit(EXIT_FAILURE);
			}
		return;		/* ok, data should be accepted again */
		} 
		if (snd_pcm_status_get_state(status) == SND_PCM_STATE_DRAINING) 
			{
			if (stream == SND_PCM_STREAM_CAPTURE) 
				{
				fprintf(stderr, _("capture stream format change? attempting recover...\n"));
				if ((res = snd_pcm_prepare(handle))<0) 
					{
					error(_("xrun(DRAINING): prepare error: %s"), snd_strerror(res));
					prg_exit(EXIT_FAILURE);
					}
				return;
				}
			}

		error(_("read/write error, state = %s"), snd_pcm_state_name(snd_pcm_status_get_state(status)));
		prg_exit(EXIT_FAILURE);
}

/* I/O suspend handler */
static void suspend(void)
{
	int res;

	while ((res = snd_pcm_resume(handle)) == -EAGAIN)
		sleep(1);	/* wait until suspend flag is released */
	if (res < 0) {
		if ((res = snd_pcm_prepare(handle)) < 0) {
			error(_("suspend: prepare error: %s"), snd_strerror(res));
			prg_exit(EXIT_FAILURE);
		}
	}
}

/*
 *  read function
 */

static ssize_t pcm_read(u_char *data, u_char **data_out,size_t rcount)
{
	ssize_t r, size;
	size_t result = 0;
	size_t count = rcount;
	u_char *data_in=data;
	if (count != chunk_size) 
		{
		count = chunk_size;
		}
	

	while (count > 0) 
		{
		r = snd_pcm_readi(handle, data, count);
		
		if (r == -EAGAIN || (r >= 0 && (size_t)r < count)) 
			{
			fprintf(stderr, "wait\n");
			snd_pcm_wait(handle, 100);
			}
		else if (r == -EPIPE) 
			{
			xrun();
			} 
		else if (r == -ESTRPIPE)
			{
			suspend();
			} 
		else if (r < 0) 
			{
			error(_("read error: %s"), snd_strerror(r));
			prg_exit(EXIT_FAILURE);	
			}
			if (r > 0) 
				{
				result += r;
				count -= r;
				data += r * bits_per_frame / 8;
				}
		}
	size = r * bits_per_frame / 8;


	size_t i;   
	int s, x, lr=0;
	u_char *lptr=data_out[0], *rptr=data_out[1];
	x=chunk_bytes/4;
	for (i=0; i < x; ++i) {
		for (s=0;s < 4; ++s) {
			if (lr) {
				*rptr = *data_in;
				++rptr;}
			else {
				*lptr = *data_in;
				++lptr;}
			++data_in;}
			if (lr) {lr=0;}
			else {lr=1;}}

	int status;		
	status=av_audio_fifo_write(fifo, (void **)data_out, r);
	if (status < 0)
		{
		fprintf(stderr, "fifo write failed!\n");
		}
	else
		if (status != r) 
			{
			fprintf(stderr, "fifo did not write all! to write %d written %d\n", r, status);
			}
	return rcount;
}

/* calculate the data count to read from/to dsp */
static off64_t calc_count(void)
{
	off64_t count;

	if (timelimit == 0) 
		{
		count = pbrec_count;
		} 
	else 
		{
		count = snd_pcm_format_size(hwparams.format, hwparams.rate * hwparams.channels);
		count *= (off64_t)timelimit;
		}
	return count < pbrec_count ? count : pbrec_count;
}

static void capture(char *orig_name)
{
	u_char *bufs[2];
	int i;
	size_t vsize;
	RASPIVID_STATE state;

// alocate video work area
	AVPacket video_packet;
	av_init_packet(&video_packet);

	video_packet.stream_index=0;
	video_packet.duration=0;
	video_packet.pos=-1;

	char *name = orig_name;	/* current filename */
	off64_t count, rest;		/* number of bytes to capture */
	int status=0;
	/* get number of bytes to capture */
	count = calc_count();
	if (count == 0)
		count = LLONG_MAX;

	/* setup sound hardware */
	set_params();
	status=init_avapi(name);

	bcm_host_init(); 
	vcos_log_register("rcam", VCOS_LOG_CATEGORY);
 
	default_status(&state);

	state.camera_parameters.stereo_mode.mode = stereo_mode;
	state.common_settings.width = width;
	state.common_settings.height = height;
	state.intraperiod = intraframe;
	state.common_settings.cameraNum = camera;
	state.quantisationParameter = quantisation;

	// param parsing was here in raspivid but done before state is allocated so needs to hold in temp vars then move to state here
	status = setup_cam_and_encoder(&state);	 
	state.callback_data.pstate = &state;
	state.callback_data.abort_ptr = &abort_flg;
	state.callback_data.fctx = flv_frmtctx;
	state.callback_data.vpckt=&video_packet;
	state.callback_data.vbuf_ptr=0;

	state.callback_data.vbuf = (u_char *)malloc(BUFFER_SIZE);
	if (state.callback_data.vbuf == NULL) 
		{
		error(_("not enough memory vbuf"));
		prg_exit(EXIT_FAILURE);
		}
	sem_t def_mutex;
	sem_init(&def_mutex, 0, 1);
	state.callback_data.mutex=&def_mutex;

         // Set up our userdata - this is passed though to the callback where we need the information.
	state.encoder_component->output[0]->userdata = (struct MMAL_PORT_USERDATA_T *)&state.callback_data;

         // Enable the encoder output port and tell it its callback function
	status = mmal_port_enable(state.encoder_component->output[0], encoder_buffer_callback);
	if (status) 
		{
		fprintf(stderr, "enable port failed\n");
		}
	
	// Send all the buffers to the encoder output port
	int num = mmal_queue_length(state.encoder_pool->queue);    
	int q;
	for (q=0; q<num; q++)
		{
		MMAL_BUFFER_HEADER_T *buffer = mmal_queue_get(state.encoder_pool->queue);
		if (!buffer)
			vcos_log_error("Unable to get a required buffer %d from pool queue", q);
		if (mmal_port_send_buffer(state.encoder_component->output[0], buffer)!= MMAL_SUCCESS)
			vcos_log_error("Unable to send a buffer to encoder output port (%d)", q);
		}
        

	
	vsize = chunk_bytes / 2;
	for (i = 0; i < 2; ++i)
		bufs[i] = rlbufs + vsize * i;

	if (count > 2147483648LL)
		count = 2147483648LL;

	do 
		{
		rest = count;

		if (rest > 2147483648LL)
			rest = 2147483648LL;
			
		if (max_file_size && (rest > max_file_size)) 
			rest = max_file_size;

                start = atime = vtime = get_microseconds64();
		if (write_audio_msg || write_video_msg)
			{
			fprintf(stderr, "      Stream time   Time/Write      Size Bytes/μs Time/Frame  Type  Samples\n");
			}

		// capture 
		snd_pcm_drop(handle);
		snd_pcm_prepare(handle);

		mmal_port_parameter_set_boolean(state.camera_component->output[MMAL_CAMERA_VIDEO_PORT], MMAL_PARAMETER_CAPTURE, 1);

		while (rest > 0) 
			{
			size_t c = (rest <= (off64_t)chunk_bytes) ? (size_t)rest : chunk_bytes;
			size_t f = c * 8 / bits_per_frame;

			if (pcm_read(audiobuf, bufs, f) != f)
				break;
			if (encode_and_write(bufs, 0, &def_mutex) < 0) 
				{
				fprintf(stderr, "encode/write failed!\n");
				close_avapi(name);
				prg_exit(EXIT_FAILURE);
				}

			count -= c;
			rest -= c;
			if (abort_flg) {count = rest = 0; fprintf(stderr, "abort\n");}
			}
		
		mmal_port_parameter_set_boolean(state.camera_component->output[MMAL_CAMERA_VIDEO_PORT], MMAL_PARAMETER_CAPTURE, 0);
		
		if (encode_and_write(bufs, 1, &def_mutex) < 0) 
			{
			fprintf(stderr, "encode/write last failed!\n");
			close_avapi(name);
			prg_exit(EXIT_FAILURE);
			}
		close_cam_and_encoder(&state);
		close_avapi(name);
		sem_destroy(&def_mutex);
		} while (count > 0);
}

int main(int argc, char *argv[])
{

	int option_index;
	static const char short_options[] = "?D:d:h:w:c:s:q:i:n:v:";
	static const struct option long_options[] = {
		{"help", 0, 0, '?'},
		{"device", 1, 0, 'D'},
		{"duration", 1, 0,'d'},
		{"height", 1, 0, 'h'},
		{"width", 1, 0, 'w'},
		{"camera", 1, 0, 'c'},
		{"stereo", 1, 0, 's'},
		{"quantisation", 1, 0, 'q'},
		{"intraframe", 1, 0, 'i'},
		{"number", 1, 0, 'n'},
		{"verbose", 1, 0, 'v'},
		{0, 0, 0, 0}
		};
	char *pcm_name = "default";
	char *stereo_str = "sbs";
	int err, c;
	snd_pcm_info_t *info;

	snd_pcm_info_alloca(&info);

	err = snd_output_stdio_attach(&logerr, stderr, 0);
	assert(err >= 0);

	command = argv[0];
	stream = SND_PCM_STREAM_CAPTURE;

	while ((c = getopt_long(argc, argv, short_options, long_options, &option_index)) != -1) {
		switch (c) {
		case '?':
			usage(command);
			return 0;
		case 'D':
			pcm_name = optarg;
			break;
		case 'd':
			timelimit = strtol(optarg, NULL, 0);
			break;
		case 'h':
			height = strtol(optarg, NULL, 0);
			if (height > 1344) {
				fprintf(stderr, "Height > than 1080 %d\n", height);
				badparm=1;}
			break;
		case 'w':
			width = strtol(optarg, NULL, 0);
			if (width > 1920) {
				fprintf(stderr, "Width > than 1920 %d\n", width);
				badparm=1;}
			break;
		case 'c':
			camera = strtol(optarg, NULL, 0);
			if (camera > 1 || camera < 0) {
				fprintf(stderr, "Camera must be 0 or 1 %d\n", camera);
				badparm=1;}
			break;
		case 'q':
			quantisation = strtol(optarg, NULL, 0);
			if (quantisation > 50 || quantisation < 0) {
				fprintf(stderr, "quantisation parameter must be 0 to 50 %d\n", quantisation);
				badparm=1;}
			break;
		case 'n':
			channel_num = strtol(optarg, NULL, 0);
			if (channel_num > 2 || channel_num < 1) {
				fprintf(stderr, "number of audio channels must be 1 or 2 %d\n", channel_num);
				badparm=1;}
			break;
		case 's':
			stereo_str = optarg;
			if (!(strcmp(stereo_str, "off"))) {stereo_mode = MMAL_STEREOSCOPIC_MODE_NONE;}
			if (!(strcmp(stereo_str, "sbs"))) {stereo_mode = MMAL_STEREOSCOPIC_MODE_SIDE_BY_SIDE;}
			if (!(strcmp(stereo_str, "tb"))) {stereo_mode = MMAL_STEREOSCOPIC_MODE_TOP_BOTTOM;}
			if (stereo_mode == -1) {
				fprintf(stderr, "Invalid mode - must be off, sbs or tb! %s\n", stereo_str);
				badparm=1;}
			break;
		case 'i':
			intraframe = strtol(optarg, NULL, 0);
			if (intraframe > 60) {
				fprintf(stderr, "Intra frame rate should be < 60  %d\n", intraframe);
				badparm=1;}
			break;
		case 'v':
			write_video_msg = write_audio_msg = strtol(optarg, NULL, 0);
			if (write_video_msg > 3 || write_video_msg < 0) {
				fprintf(stderr, "Verbose must be 0, 1, 2 or 3 %d\n", camera);
				badparm=1;}
			else
				if (write_video_msg == 2) {
					write_video_msg = 0;}
				else if (write_video_msg == 1) {
					write_audio_msg = 0;}
			break;


		default:
			fprintf(stderr, _("Try `%s --help' for more information.\n"), command);
			return 1;
		}
	}

	if (stereo_mode == -1) {stereo_mode = MMAL_STEREOSCOPIC_MODE_TOP_BOTTOM;}

	if (badparm == 1) {
		return 1;
	}

	err = snd_pcm_open(&handle, pcm_name, stream, 0);
	if (err < 0) {
		error(_("audio open error: %s"), snd_strerror(err));
		return 1;
	}

	rhwparams.format = DEFAULT_FORMAT;
	rhwparams.rate = DEFAULT_SPEED;
	rhwparams.channels = DEFAULT_CHANNELS_IN;
	chunk_size = 1024;
	hwparams = rhwparams;

	signal(SIGINT, signal_handler);
	signal(SIGTERM, signal_handler);
	signal(SIGABRT, signal_handler);

	if (optind > argc - 1)  
		{
	fprintf(stderr, "Must have file or stream address\n");
		} 
	else 
		{
		capture(argv[optind++]);
		}
	
	snd_pcm_close(handle);
	handle = NULL;
	free(audiobuf);
	free(rlbufs);
	
	snd_output_close(logerr);
	snd_config_update_free_global();
	prg_exit(EXIT_SUCCESS);
	return EXIT_SUCCESS;
}

