#include <stdarg.h>
#include <stdio.h>      /* vsnprintf */
#include <stdlib.h>
#include <string.h>
#include <immintrin.h>
#include <cpuid.h>

#include "Enclave_t.h"

extern void printf(const char *fmt, ...);

//global variables
volatile unsigned long current_time = 0;
volatile unsigned long previous_time = 0;
int infinite_loop_flag = 1;
volatile int int_flag;

void my_delay(unsigned long loops)
{
	 __asm volatile(
                  "       test %0,%0      \n"
                  "       jz 3f           \n"
                  "       jmp 1f          \n"
  
                  ".align 16              \n"
                  "1:     jmp 2f          \n"
  
                  ".align 16              \n"
                  "2:     dec %0          \n"
                  "       jnz 2b          \n"
                  "3:     dec %0          \n"
 
                  : /* we don't need output */
                  :"a" (loops)
          );
}

void my_const_udelay(unsigned long xloops)
{
        int d0;
 
        xloops *= 4;
        __asm("mull %%edx"
                :"=d" (xloops), "=&a" (d0)
                :"1" (xloops), ""
                ((1UL<<32) * (100/4)));
 
        my_delay(++xloops);
}

void my_udelay(unsigned long usecs)
{
	my_const_udelay(usecs * 0x000010c7);
}

void secure_timer()
{

	current_time = 0;
	// error message
	int_flag = 0;

	register int rand,i,k;

	//printf("timer starts.\n");
	//printf("get_time at the beginning of timer: %lu\n", get_time(1));

	//outer loop
	//while(1)
	int outloop, round = 10000;
	while(infinite_loop_flag)
	//for (outloop = 0; outloop < round; outloop++)
	{

		//generate a random number
		// tsx and inner loop
		if(_xbegin() == _XBEGIN_STARTED)
		{
			__asm volatile
			(
				"rdrand %0\n\t"
				:"=r"(rand)
			);
			// convert a to a positive integer between 1 and 10 inclusive
			rand = (rand & 0x7) +1;

			for(i = 0; i < rand; i++)
			{
				for (k = 0; k < 5; k++);
				my_udelay(1);
			}

			_xend();
		}
		else
		{
			int_flag++;
			//rand = i;
			//handle_abort_time();
			
			//printf("sec: %llu, nsec: %llu\n", sec, nsec);

			//current_time = 0;
			//continue;
		}

		//previous_time = current_time;
		current_time = current_time + rand;

		//printf("%llu\n", current_time);
		//printf("current time: %llu\n", current_time);
		//*t = *t + rand;
		//printf("*t: %lu\n", *t);


	}
	//printf("timer ends.\n");
	//printf("get_time at the end of timer: %lu\n", get_time(1));

}

void set_infinite_loop_flag_false(int i)
{
	infinite_loop_flag = 0;
	printf("\nint_flag: %d\n", int_flag);
	//while(1);

	//printf("infinite_loop_flag: %d\n", infinite_loop_flag);
}









