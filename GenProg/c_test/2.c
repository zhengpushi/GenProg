/*
  2023.09.10
  这里是我写的DPIA算法所直接生成的C代码。
*/

#include <stdio.h>

struct s0 {
  float x1;
  float x2;
};

struct s0 v1[3];
  
int main () {
  float x0 = 0;
  float x1 = 0;
  float v0[5] = {1,2,3,4,5};

  // 以下内容由DPIA生成
  {
	float x2;
	x2 = x0;
	for (int i0 = 0; i0 < 5; i0 += 1) {
	  x2 = (v0[i0] + x2);
	}
	x1 = x2;
  }
  // 以上内容由DPIA生成

  printf("x1 = %f\n", x1);
  
}
