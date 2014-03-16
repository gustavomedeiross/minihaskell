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
	make -C $(TEST) clean

ARCHDIR=bourgeat-xia

archive: $(ARCHDIR).tar.gz

$(ARCHDIR).tar.gz: clean
	rm -rf $(ARCHDIR)
	mkdir -p $(ARCHDIR)
	cp -r Makefile LICENSE README.md src/ test/ $(ARCHDIR)
	tar zcf $@ $(ARCHDIR)
