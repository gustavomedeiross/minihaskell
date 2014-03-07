EXECUTABLE=joujou

SRC=src/

$(EXECUTABLE): ./$(SRC)$(EXECUTABLE)
	cp src/joujou .

./$(SRC)$(EXECUTABLE):
	make -C $(SRC) -j

test: ./$(SRC)$(EXECUTABLE)
	cd test/ && ./test

clean:
	rm -f joujou
	make -C $(SRC) clean
