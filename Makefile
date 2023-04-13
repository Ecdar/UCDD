build: FORCE
	unset CMAKE_TOOLCHAIN_FILE # If it was set before
	./getlibs.sh # If UUtils and UDBM are not installed system-wide
	cmake -B build -DTESTING=ON
	cmake --build build

test: build
	(cd build ; ctest --output-on-failure)

FORCE: ;