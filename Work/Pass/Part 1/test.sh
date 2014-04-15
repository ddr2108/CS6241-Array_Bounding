clang++ -c CreateBounds.cpp `llvm-config --cxxflags`;
clang++ -shared -o pass.so CreateBounds.o `llvm-config --ldflags`
opt -load ./pass.so -CreateBounds <../../Test/benchmark.bc> result.bc
#lli result.bc
#rm result.bc
#rm -f *~ pass.so *.o

