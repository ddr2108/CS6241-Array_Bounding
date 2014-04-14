clang++ -c CSE6142.cpp `llvm-config --cxxflags`;
clang++ -shared -o pass.so CSE6142.o `llvm-config --ldflags`
opt -load ./pass.so -CSE6142 -dot-cfg <../../Test/hello.bc> result.bc
#llc result.bc
#clang++ result.s
#rm result.bc
#rm -f *~ pass.so *.o *.s
