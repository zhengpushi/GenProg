all : mmul.out

%.out : %.c
	gcc -fopenmp -O3 -o $@ $<

clean:
	rm *.out

