#include <stdio.h>
#include <stdlib.h>

int test(){
	int size = 5;
	int a[25];

	int x,y;
	int z;

	x = 2;
	y = 2*x+1;
	z = 1*x + 1;
	int b[y];
	//a[y] = 3;
	//y = z;
	printf("Before");
	b[z] = 10;
	printf("After");
	printf("Before");
	b[4] = 10;
	printf("After");
	printf("Before");
	a[5] = 10;
	printf("After");
	printf("Before");
	a[28] = 10;
	printf("After");
	x = a[30];	
	return 1;
}

int main() {

	int z = test();
	printf("%d",z);
	
	return 0;
}

