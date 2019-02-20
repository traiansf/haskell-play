all: recursive-types-for-free.pdf README.md

README.md: recursive-types-for-free.lhs
	pandoc $<  -o $@

%.pdf: %.lhs
	pandoc -t beamer $<  -o $@

clean:
	rm -f *.pdf *.md

