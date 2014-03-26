clang++ -c CSE6142.cpp `llvm-config --cxxflags`;
clang++ -shared -o pass.so CSE6142.o `llvm-config --ldflags`
opt -load ./pass.so -CSE6142 <../../Test/hello.bc> result.bc
lli result.bc
