/*
  2023.09.09
  这里是我写的DPIA算法所直接生成的C代码。
*/

#include <stdio.h>

int main () {
  float x0 = 0;
  float x1 = 0;
  float v0[5] = {1,2,3,4,5};

  // 以下内容由DPIA生成
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
			  x1 = (v5[i1] + x1);
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
					x1 = (v8[i1] + x1);
				  }
				  v7[i0] = x1 * v1[i0];
				}
			  }
			}
			for (int i0 = 0; i0 < 3; i0 += 1) {
			  v6[i0] = (v0[i0] - v7[i0]);
			}
		  }
		  for (int i0 = 0; i0 < 3; i0 += 1) {
			v5[i0] = cos(x0) * v6[i0];
		  }
		}
		for (int i0 = 0; i0 < 3; i0 += 1) {
		  v3[i0] = (v4[i0] + v5[i0]);
		}
	  }
	}
	{
	  float v4[3];
	  for (int i0 = 0; i0 < 3; i0 += 1) {
		v4[i0] = sin(x0) * v1[i0];
	  }
	  for (int i0 = 0; i0 < 3; i0 += 1) {
		v2[i0] = (v3[i0] + v4[i0]);
	  }
	}
  }
  // 以上内容由DPIA生成

  printf("x1 = %f\n", x1);
  
}
