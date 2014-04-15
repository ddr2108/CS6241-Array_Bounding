#include <stdio.h>
#include <stdlib.h>

int main(){

	int i=0;
	int j=0;
	int k = 0;
	int t = 0;
	int r = 0;
	int v = 0;
	int w = 0;
	int x = 0;
	int y = 0;
	int z = 5;

	int sum=0;
	const int bsize=50;

	int a[100];
	int b[bsize];

	int c1=1,c2=2,c5=5,c10=10,c15=15,c20=20;

	y = z + 5;		//Shows GVN

	//Show array stuff
	a[20]=i;

	//Show restructuring
	if(i>5){
		i+=c10;
		w=c5-c1;
	}else{
		i=c2;
	}

	k=c5-c1;	//Show GVN after restructure	

	//Shows GVN used and deleted
	r = z+5;		
	z = 8;
	v = z + 5;

	//Show GVN with arrays
	y = j;	
	b[y]= c2;
	y = y + 1;
	b[y]= c1;
	b[j]=i;

	y = i;			//Cause Restructiring

	if(y>5){
		a[i]=i+j;
		b[i+j]=c10;
		i=i-c1;
	}else{
		a[i+y]=i+j;
		b[i+j]=c20;
	}

	//Array Stuff
	a[i]=c5;
	t=i-k;
	sum=a[t];
	sum+=a[k];

	//Show GVN with if then
	x = y;
	if(x>5){
		sum+=b[j-k];
	}else{
		sum-=b[j-t];
	}

}

