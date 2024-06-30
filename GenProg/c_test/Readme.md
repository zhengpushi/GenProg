# 关于 openmp
* 编译选项
  $ gcc -fopenmp
* 常见的for并行
  #pragma omp parallel for
  结果是：以下的for循环会交给多个线程并行执行
  简单的测试：可以打印如下内容 printf("i = %d\n", i);

# 程序清单
* new1.c   测试由多次reduce操作生成的一个sum程序
