//T compiles:yes
//T retval:0
//T has-passed:no
// Auto bug
module test_001;

void* funcReturnsPointer() { void* ptr; return ptr; }

int main()
{
	auto ptr = funcReturnsPointer();

	return 42;
}
