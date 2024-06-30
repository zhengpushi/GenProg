/*
  2023.09.13
  由DPIA.v生成的C代码。

  B123_mat_equiv
*/

#include <stdio.h>
#include <stdbool.h>
#include <stdlib.h>
#include <time.h>				/* time() */
#include <sys/time.h>			/* gettimeofday() */

void f () {
  {
	float v1[3][3];

	/* 矩阵乘法 */
	for (int i0 = 0; i0 < 3; i0 += 1) {
	  for (int i1 = 0; i1 < 3; i1 += 1) {
		{
		  float v2[3];
		  for (int i2 = 0; i2 < 3; i2 += 1) {
			v2[i2] = err_CGexp_mkm_must_none<[i0][i2]> * err_CGexp_mkm_must_none<[i2][i1]>;
		  }
		  {
			float x3;
			x3 = 0;
			for (int i2 = 0; i2 < 3; i2 += 1) {
		}
	  }
	}

	/* 矩阵乘法 */
	for (int i0 = 0; i0 < 3; i0 += 1) {
	  for (int i1 = 0; i1 < 3; i1 += 1) {
		{
		  float v2[3];
		  for (int i2 = 0; i2 < 3; i2 += 1) {
			v2[i2] = err_CGexp_map_must_none * err_CGexp_mkm_must_none<[i2][i1]>;
		  }
		  {
			/* reduce */
			float x3;
			x3 = 0;
			for (int i2 = 0; i2 < 3; i2 += 1) {
			  x3 = v2[i2] + x3;
			}
			m0[i0][i1] = x3;
		  }
		}
	  }
	}

	
  }
}

void rotaa () {
  {
	float v3[3];
	{
	  float v4[3];
	  for (int i0 = 0; i0 < 3; i0 += 1) {
		{
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
	  }
	  {
		float v5[3];
		{
		  float v6[3];
		  {
			float v7[3];
			for (int i0 = 0; i0 < 3; i0 += 1) {
			  {
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
			}
			for (int i0 = 0; i0 < 3; i0 += 1) {
			  v6[i0] = v0[i0] - v7[i0];
			}
		  }
		  for (int i0 = 0; i0 < 3; i0 += 1) {
			v5[i0] = cos(x0) * v6[i0];
		  }
		}
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
	  for (int i0 = 0; i0 < 3; i0 += 1) {
		v2[i0] = v3[i0] + v4[i0];
	  }
	}
  }
}

/* 矩阵大小设定 */

/* 用于正确性测试 */
/* const int R = 2; */
/* const int C = 3; */
/* const int S = 4; */

/* 用于小规模性能测试 */
const int R = 1000;
const int C = 1000;
const int S = 1000;

/* 用于大规模性能测试 */
/* const int R = 250; */
/* const int C = 3000; */
/* const int S = 4000; */

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

/* 申请矩阵存储空间 */
float ** matrix_alloc(int m, int n) {
  float **A = (float **)malloc(m * sizeof(float *));
  for (int i = 0; i < m; i++) {
	A[i] = (float *)malloc(n * sizeof(float));
  }
  return A;
}

/* 释放动态分配的内存 */
void matrix_free(int m, float **A) {
  for (int i = 0; i < R; i++) {
	free(A[i]);
  }
  free(A);
}

/* 设置矩阵内容为随机数 */
void matrix_rand(int m, int n, float **A) {
  srand(time(NULL)); // 设置随机数种子  
  for (int i = 0; i < m; i++) {
	for (int j = 0; j < n; j++) {
	  /* A[i][j] = 1.0 * rand() / RAND_MAX * 100; */
	  /* A[i][j] = (float)rand() / RAND_MAX * 2 - 1; // 生成-1到1之间的随机数  	   */
	  A[i][j] = i * n + j + 1;	/* 生成 1,2,3, ... */
	}
  }
}

/* 打印矩阵 */
void matrix_print (int m, int n, float **A) {
  for (int i = 0; i < m; i++) {
	for (int j = 0; j < n; j++) {
	  printf("%.1f ", A[i][j]);
	}
	printf("\n");
  }
  printf("\n");
}

/* 矩阵乘法 - 顺序版本 */
void matrix_mul(int m, int n, int p, float **A, float **B, float **out) {
  time_measure(true, NULL);
  for (int i0 = 0; i0 < m; i0 += 1) {
	for (int i1 = 0; i1 < p; i1 += 1) {
	  float v2[n];
	  for (int i3 = 0; i3 < n; i3 += 1) {
		v2[i3] = (A[i0][i3] * B[i1][i3]);
	  }
	  float v4;
	  v4 = 0;
	  for (int i5 = 0; i5 < n; i5 += 1) {
		v4 = (v2[i5] + v4);
	  }
	  out[i0][i1] = v4;
	}
  }
  time_measure(false, "mul");
}

/* 矩阵乘法 - omp版本（由ZXL提供） */
void matrix_mul_omp(int m, int n, int p, float **A, float **B, float **out) {
  time_measure(true, NULL);
  
#pragma omp parallel for
  for (int i0 = 0; i0 < m; i0 += 1) {
	for (int i1 = 0; i1 < p; i1 += 1) {
	  float v2[n];
	  for (int i3 = 0; i3 < n; i3 += 1) {
		v2[i3] = (A[i0][i3] * B[i1][i3]);
	  }
	  float v4;
	  v4 = 0;
	  for (int i5 = 0; i5 < n; i5 += 1) {
		v4 = (v2[i5] + v4);
	  }
	  out[i0][i1] = v4;
	}
  }
  
  time_measure(false, "mul_omp");
}

/* 矩阵乘法 - omp版本（由SZP提供） */
void matrix_mul_omp_szp(int R, int S, int C, float **m0, float **m1, float **m2) {
  time_measure(true, NULL);

  // 以下内容由DPIA生成
#pragma omp parallel for
  for (int i0 = 0; i0 < R; i0 += 1) {
#pragma omp parallel for
	for (int i1 = 0; i1 < C; i1 += 1) {
	  {
		float v3[S];
#pragma omp parallel for
		for (int i2 = 0; i2 < S; i2 += 1) {
		  v3[i2] = (m0[i0][i2] * m1[i2][i1]);
		}
		{
		  float x0;
		  x0 = 0;
		  for (int i2 = 0; i2 < S; i2 += 1) {
			x0 = (v3[i2] + x0);
		  }
		  m2[i0][i1] = x0;
		}
	  }
	}
  }
  // 以上内容由DPIA生成
  
  time_measure(false, "mul_omp_szp");
}

/* 矩阵乘法 - omp版本（由SZP提供，并手动优化） */
void matrix_mul_omp_szp2(int R, int S, int C, float **m0, float **m1, float **m2) {
  time_measure(true, NULL);

  // 以下内容由DPIA生成

#pragma omp parallel for
  for (int i0 = 0; i0 < R; i0 += 1) {
/* #pragma omp parallel for */
	for (int i1 = 0; i1 < C; i1 += 1) {
	  {
		float x0;
		x0 = 0;
/* #pragma omp parallel for */
		for (int i2 = 0; i2 < S; i2 += 1) {
		  x0 = (m0[i0][i2] * m1[i2][i1]) + x0;
		}
		m2[i0][i1] = x0;
	  }
	}
  }
  // 以上内容由DPIA生成
  
  time_measure(false, "mul_omp_szp2");
}

/* m2[R][C] = m0[R][S] * m1[S][C] */
int main() {
  float **m0 = matrix_alloc(R,S);
  float **m1 = matrix_alloc(S,C);
  float **m2 = matrix_alloc(R,C);

  matrix_rand(R,S,m0);
  matrix_rand(S,C,m1);
  matrix_rand(R,C,m2);

  matrix_mul(R,S,C,m0,m1,m2);
  matrix_mul_omp(R,S,C,m0,m1,m2);
  matrix_mul_omp_szp(R,S,C,m0,m1,m2);
  matrix_mul_omp_szp2(R,S,C,m0,m1,m2);
	
  /* printf("m0：\n"); */
  /* matrix_print(R,S,m0); */

  /* printf("m1：\n"); */
  /* matrix_print(S,C,m1); */

  /* printf("m2：\n"); */
  /* matrix_print(R,C,m2); */

  matrix_free(R,m0);
  matrix_free(S,m1);
  matrix_free(R,m2);
  
  return 0;
}
