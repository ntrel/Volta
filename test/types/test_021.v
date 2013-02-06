//T compiles:yes
//T retval:0
//T has-passed:no
// null to pointer test.
module test_021;


alias voidPtr = void*;

class Clazz
{
	this() { return; }

	int i;
}

struct Struct
{
	int i;
}

void* f1(void*) { return null; }
char* f2(char*) { return null; }
int* f3(int*) { return null; }
Struct* f4(Struct*) { return null; }
Clazz f5(Clazz) { return null; }
voidPtr f6(voidPtr) { return null; }

class Main
{
public:
	void* p1;
	char* p2;
	int* p3;
	Struct* p4;
	Clazz p5;
	voidPtr p6;

public:
	this(void*, char*, int*, Struct*, Clazz, voidPtr)
	{
		p1 = null;
		p2 = null;
		p3 = null;
		p4 = null;
		p5 = null;
		p6 = null;
		return;
	}

	void func()
	{
		p1 = null;
		p2 = null;
		p3 = null;
		p4 = null;
		p5 = null;
		p6 = null;
		return;
	}
}

int main()
{
	void* p1 = null;
	char* p2 = null;
	int* p3 = null;
	Struct* p4 = null;
	Clazz p5 = null;

	f1(null);
	f2(null);
	f3(null);
	f4(null);
	f5(null);
	f6(null);

	auto c = new Main(null, null, null, null, null, null);
	c.func();

	return 0;
}