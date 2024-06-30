/*
  2023.09.13
  由DPIA.v生成的C代码。

  ??
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

float a() {
  float v3[n];
  for (int i0 = 0; i0 < n; i0 += 1) {
	v3[i0] = ((v0[i0] + v1[i0]) + v1[i0]);
  }
  for (int i0 = 0; i0 < n; i0 += 1) {
	v2[i0] = v3[i0];
  }
}

float b() {
  float v3[3];
  {
	float v4[3];
	for (int i0 = 0; i0 < 3; i0 += 1) {
	  float v5[3];
	  for (int i1 = 0; i1 < 3; i1 += 1) {
		v5[i1] = v0[i1] * v1[i1];
	  }
	  {
		float x1;
		x1 = 0;
		for (int i1 = 0; i1 < 3; i1 += 1) {
		  x1 = v5[i1] + x1;
		}
		v4[i0] = x1 * v1[i0];
	  }
	}
	{
	  float v5[3];
	  {
		float v6[3];
		{
		  float v7[3];
		  for (int i0 = 0; i0 < 3; i0 += 1) {
			float v8[3];
			for (int i1 = 0; i1 < 3; i1 += 1) {
			  v8[i1] = v0[i1] * v1[i1];
			}
			{
			  float x1;
			  x1 = 0;
			  for (int i1 = 0; i1 < 3; i1 += 1) {
				x1 = v8[i1] + x1;
			  }
			  v7[i0] = x1 * v1[i0];
			}
		  }
#pragma omp parallel for
		  for (int i0 = 0; i0 < 3; i0 += 1) {
			v6[i0] = v0[i0] - v7[i0];
		  }
		}
#pragma omp parallel for
		for (int i0 = 0; i0 < 3; i0 += 1) {
		  v5[i0] = cos(x0) * v6[i0];
		}
	  }
#pragma omp parallel for
	  for (int i0 = 0; i0 < 3; i0 += 1) {
		v3[i0] = v4[i0] + v5[i0];
	  }
	}
  }
  {
	float v4[3];
	for (int i0 = 0; i0 < 3; i0 += 1) {
	  v4[i0] = sin(x0) * v1[i0];
	}
#pragma omp parallel for
	for (int i0 = 0; i0 < 3; i0 += 1) {
	  v2[i0] = v3[i0] + v4[i0];
	}
  }
}

float f() {
  for (int i0 = 0; i0 < r; i0 += 1) {
	for (int i1 = 0; i1 < c; i1 += 1) {
	  {
		float m3[r][c];
		for (int i2 = 0; i2 < r; i2 += 1) {
		  for (int i3 = 0; i3 < c; i3 += 1) {
			m3[i2][i3] = (m0[i2][i3] + m1[i2][i3]);
		  }
		}
		{
		  float m4[r][c];
		  for (int i2 = 0; i2 < r; i2 += 1) {
			for (int i3 = 0; i3 < c; i3 += 1) {
			  m4[i2][i3] = (m0[i2][i3] + m1[i2][i3]);
			}
		  }
		  m2[i0][i1] = (m3[i0][i1] + m1[i0][i1]);
		}
	  }
	}
  }
}

void g() {
  for (int i0 = 0; i0 < n; i0 += 1) {
	{
	  float v3[n];
	  for (int i1 = 0; i1 < n; i1 += 1) {
		v3[i1] = (v0[i1] + v1[i1]);
	  }
	  {
		float v4[n];
		for (int i1 = 0; i1 < n; i1 += 1) {
		  v4[i1] = (v0[i1] + v1[i1]);
		}
		v2[i0] = (v3[i0] + v1[i0]);
	  }
	}
  }
}

int main() {
  printf("%.f\n", f());
  return 0;
}
