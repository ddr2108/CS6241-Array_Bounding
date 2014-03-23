rm pass.so
clang++ -c arrayBound.cpp `llvm-config --cxxflags`;
clang++ -shared -o pass.so arrayBound.o `llvm-config --ldflags`
opt -load ./pass.so -arrayBound <../../Test/hello.bc> result.bc
lli result.bc

