 

#ifndef RASPICAM_HELPERS
#define RASPICAM_HELPERS

void default_signal_handler(int signal_number);
int mmal_status_to_int(MMAL_STATUS_T status);
uint64_t get_microseconds64();

#endif
