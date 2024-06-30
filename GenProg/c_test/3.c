/*
  2023.09.10
  这里是我写的DPIA算法所直接生成的C代码。

  dotproduct
*/

#include <stdio.h>

int main () {
  float x0 = 0;
  float v0[5] = {1,2,3,4,5};
  float v1[5] = {2,3,4,5,6};
  // v0.v1 = 2+6+12+20+30=70

  // 以下内容由DPIA生成
  {
	float v2[5];
#pragma omp parallel for
	for (int i0 = 0; i0 < 5; i0 += 1) {
	  v2[i0] = (v0[i0] * v1[i0]);
	}
	{
	  float x1;
	  x1 = x0;
	  for (int i0 = 0; i0 < 5; i0 += 1) {
		x1 = (v2[i0] + x1);
	  }
	  x0 = x1;
	}
  }
  // 以上内容由DPIA生成

  printf("x1 = v0.v1 = %f\n", x0);
}
