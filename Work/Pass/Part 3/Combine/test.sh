clang++ -c p11.cpp `llvm-config --cxxflags`;
clang++ -shared -o pass.so p11.o `llvm-config --ldflags`
opt -load ./pass.so -p11 -dot-cfg <../../../Test/hello.bc> result.bc
lli result.bc
rm result.bc
#rm -f *~ pass.so *.o
