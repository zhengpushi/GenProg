/*
  2023.09.13
  由DPIA.v生成的C代码。

  由 reduce 生成的 sum
*/

#include <stdio.h>
#include <stdbool.h>
#include <stdlib.h>
#include <time.h>				/* time() */
#include <sys/time.h>			/* gettimeofday() */

/* 测量时间
   用法：传入 true 则开始计时，传入 false 则停止计时并打印耗时
 */
/* 测量时间结束，并报告耗时 */
void time_measure(bool start, char *title) {
  static struct timeval t1,t2;
  if (start) {
	gettimeofday(&t1, NULL);
  } else {
	gettimeofday(&t2, NULL);
	double timeuse = (t2.tv_sec - t1.tv_sec)
	  + (double)(t2.tv_usec - t1.tv_usec) / 1000000.0;
	printf("%s time : %12f\n", title, timeuse);
  }
}

float f() {
  int n = 4;
  float v0[4] = {1,2,3,4};
  /* 
	 x1 = 1;
	 x1 = 4*3*2*1*1 = 24;
	 x2 = 24
	 x2 = 4/(3/(2/(1/24))) = 4/(3/48) = 64
	 x3 = 64
	 x3 = 4 - (3 - (2 - (1 - 64))) = 66
	 x4 = 66
	 x4 = 4 + 3 + 2 + 1 + 66 = 76
 */
  
  float x0;
  {
	float x1;
	x1 = 1;
	for (int i3 = 0; i3 < n; i3 += 1) {
	  x1 = v0[i3] * x1;
	}
	{
	  float x2;
	  x2 = x1;
	  for (int i3 = 0; i3 < n; i3 += 1) {
		x2 = v0[i3] / x2;
	  }
	  {
		float x3;
		x3 = x2;
		for (int i3 = 0; i3 < n; i3 += 1) {
		  x3 = (v0[i3] - x3);
		}
		{
		  float x4;
		  x4 = x3;
		  for (int i3 = 0; i3 < n; i3 += 1) {
			x4 = (v0[i3] + x4);
		  }
		  x0 = x4;
		}
	  }
	}
  }

  return x0;
}


int main() {
  printf("%.f\n", f());
  return 0;
}
