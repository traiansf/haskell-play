all: recursion.pdf README.md

README.md: recursion.lhs
	pandoc $<  -o $@

%.pdf: %.lhs
	pandoc -t beamer $<  -o $@

clean:
	rm -f *.pdf *.md

