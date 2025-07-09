all:
	g++ -g -O3 -L../z3/build -o guidedsampler guidedsampler.cpp -lz3
