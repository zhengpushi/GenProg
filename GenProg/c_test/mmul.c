/* 
   由 DPIAv3_4.v 生成
 */

/* m3 = (m0 * m1) * m2  */
void mmul1 () {

  /* 手动添加头部：
	 1. 这里只是满足了C的语法要求，没有考虑实际情形。
	 2. 数组维数是由函数传入，而不是固定的；同理数组内容也应该是指针的方式
  */
  const int r = 10;
  const int c = 10;
  const int s = 10;
  int t = 10;
  float m0[r][c];
  float m1[c][s];
  float m2[s][t];
  float m3[r][t];
  
  /* m4 = m0 * m1 */
  float m4[r][s];
  for (int i0 = 0; i0 < r; i0 += 1) {
	for (int i1 = 0; i1 < s; i1 += 1) {
	  float v5[c];
	  for (int i2 = 0; i2 < c; i2 += 1) {
		v5[i2] = m0[i0][i2] * m1[i2][i1];
	  }
	  {
		float x0;
		x0 = 0;
		for (int i2 = 0; i2 < c; i2 += 1) {
		  x0 = v5[i2] + x0;
		}
		m4[i0][i1] = x0;
	  }
	}
  }
  
  /* m3 = m4 * m2 = (m0 * m1) * m2 */
  for (int i0 = 0; i0 < r; i0 += 1) {
	for (int i1 = 0; i1 < t; i1 += 1) {
	  float v5[s];
	  for (int i2 = 0; i2 < s; i2 += 1) {
		v5[i2] = m4[i0][i2] * m2[i2][i1];
	  }
	  {
		float x0;
		x0 = 0;
		for (int i2 = 0; i2 < s; i2 += 1) {
		  x0 = v5[i2] + x0;
		}
		m3[i0][i1] = x0;
	  }
	}
  }
}


void main () {
  int r,c,s,t;
  mmul1(r);
}
