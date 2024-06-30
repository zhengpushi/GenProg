/*
  2023.09.13
  由DPIA.v生成的C代码。

  mmul

  一组测试结果：
  在 1000*100*1000 的矩阵乘法时，
  mul time :     3.759028
  mul_omp time :     0.853035
  mul_omp_szp time :     0.985621
  mul_omp_szp2 time :     0.593678

  结果分析：
  1. 自动生成的矩阵乘法代码，仍然有优化空间。
  (1) 如果是先申请临时数组来保存点积结果，然后加总，这种方式较慢；
  如果是直接用一个数来求和，这种方式较快。
  (2) 有3个for循环，可以开三处并行指示，结果是不同的。
  只开最内层，3.05
  只开中间层，0.65
  只开最外层，0.60
  其他组合都较慢。
  (3) 如果拿掉最内层的 float x0; 的声明，则由 0.60 秒变为 2.0 秒
  (4) 如果开启 -O3，则由 0.60 秒变为 0.22 秒。
  (5) 如果开启 -O3，则四个矩阵乘法中，_opm 最快，结果如下
mul time :     0.949753
mul_omp time :     0.148446
mul_omp_szp time :     0.324748
mul_omp_szp2 time :     0.218124
  这说明，_szp 程序总是会慢。原因是_szp程序执行了转置，而_omp 没有。
  在C代码看来，只是访问下标的交换，_opm 是 B[i][j]，而_szp 是 B[j][i]，
  这导致的结果是破坏了数据的局部性，从而降低了cache命中率，因为cache换页会
  更加频繁。
*/

#include <stdio.h>
#include <stdbool.h>
#include <stdlib.h>
#include <time.h>				/* time() */
#include <sys/time.h>			/* gettimeofday() */


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
