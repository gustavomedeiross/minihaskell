EXECUTABLE=joujou

SRC=src/
TEST=test/

$(EXECUTABLE): ./$(SRC)$(EXECUTABLE)
	cp src/joujou .

./$(SRC)$(EXECUTABLE):
	make -j -C $(SRC)

test: ./$(SRC)$(EXECUTABLE) FORCE
	make -C $(TEST) test

FORCE:

clean:
	rm -f joujou
	make -C $(SRC) cleanall
