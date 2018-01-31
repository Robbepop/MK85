#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <stdarg.h>
#include <assert.h>

#include <stdint.h>

#include <list>
#include <string>
#include <iterator>
#include <iostream>
#include <sstream>

// Boehm garbage collector:
//#include <gc.h>

void die(const char* fmt, ...)
{
	va_list va;
	va_start (va, fmt);

	vprintf (fmt, va);
	exit(0);
};

void* xmalloc(size_t size)
{
	void* rt=malloc(size);
	if (rt==NULL)
		die ("Can't allocate %d bytes\n", size);
	memset(rt, 0, size);
	return rt;
};

void xfree (void* p)
{
	free(p);
};

char* xstrdup(const char *s)
{
	char* rt=(char*)xmalloc(strlen(s)+1);
	strcpy (rt, s);
	return rt;
};


// "1 2 3 4 5 -6" -> array of (signed) ints
// destroys input string
// allocates space for array
int* list_of_numbers_to_array (char *s, size_t array_size, size_t *parsed)
{
	int *rt=(int*)xmalloc(array_size*sizeof(int));
	assert(rt);
	int i=0;
	char *t=strtok(s, " \r\n");
	while (t!=NULL)
	{
		int v;
		assert (sscanf (t, "%d", &v)==1);
		rt[i++]=v;
		t=strtok(NULL, " \r\n");
	}
	*parsed=i;
	return rt;
};

char* create_string_of_numbers_in_range(int begin, size_t size)
{
	size_t buflen=size*10;
	char* buf=(char*)xmalloc(buflen);
	buf[0]=0;
	for (size_t i=0; i<size; i++)
	{
		char buf2[16];
		snprintf (buf2, sizeof(buf2), "%d ", begin+i);
		strncat(buf, buf2, buflen);
	};
	buf[strlen(buf)-1]=0;
	return buf;
};

void set_bit(uint32_t *v, int bit)
{
	(*v)|=1<<bit;
}

void clear_bit(uint32_t *v, int bit)
{
	(*v)&=~(1<<bit);
};

void negate_all_elements_in_int_array(int *a)
{
	for (int i=0; a[i]; i++)
		a[i]=-a[i];
};

size_t count_ints_in_array(int *a)
{
	int rt=0;
	for (int i=0; a[i]; i++)
		rt++;
	return rt;
};

char *list_of_ints_to_str(int *a)
{
	char* rt=(char*)malloc(count_ints_in_array(a)*10);
	rt[0]=0;
	char tmp[32];
	for (int i=0; a[i]; i++)
	{
		sprintf (tmp, "%d ", a[i]);
		strcat (rt, tmp);
	}
	rt[strlen(rt)-1]=0;
	//printf ("%s\n", rt);
	return rt;	
};

// https://stackoverflow.com/questions/994593/how-to-do-an-integer-log2-in-c
uint32_t mylog2(const uint32_t x)
{
	return (31 - __builtin_clz (x));
}

// https://en.wikipedia.org/wiki/Hamming_weight
//types and constants used in the functions below
//uint64_t is an unsigned 64-bit integer variable type (defined in C99 version of C language)
const uint64_t m1  = 0x5555555555555555; //binary: 0101...
const uint64_t m2  = 0x3333333333333333; //binary: 00110011..
const uint64_t m4  = 0x0f0f0f0f0f0f0f0f; //binary:  4 zeros,  4 ones ...
const uint64_t m8  = 0x00ff00ff00ff00ff; //binary:  8 zeros,  8 ones ...
const uint64_t m16 = 0x0000ffff0000ffff; //binary: 16 zeros, 16 ones ...
const uint64_t m32 = 0x00000000ffffffff; //binary: 32 zeros, 32 ones
const uint64_t hff = 0xffffffffffffffff; //binary: all ones
const uint64_t h01 = 0x0101010101010101; //the sum of 256 to the power of 0,1,2,3...
int popcount64c(uint64_t x)
{
    x -= (x >> 1) & m1;             //put count of each 2 bits into those 2 bits
    x = (x & m2) + ((x >> 2) & m2); //put count of each 4 bits into those 4 bits 
    x = (x + (x >> 4)) & m4;        //put count of each 8 bits into those 8 bits 
    return (x * h01) >> 56;  //returns left 8 bits of x + (x<<8) + (x<<16) + (x<<24) + ... 
}

std::string remove_trailing_space (std::string s)
{
	if (s.back()==' ')
		return remove_trailing_space(s.substr(0, s.length()-1));
	return s;
};

std::string cxx_list_of_ints_to_string (std::list<int> l)
{
	// https://stackoverflow.com/questions/2518979/how-to-transform-a-vectorint-into-a-string
	std::stringstream result;
	std::copy(l.begin(), l.end(), std::ostream_iterator<int>(result, " "));
	return remove_trailing_space(result.str());
};

