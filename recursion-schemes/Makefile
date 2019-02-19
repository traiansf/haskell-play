all: recursion.pdf recursion.md

%.md: %.lhs
	pandoc $<  -o $@

%.pdf: %.lhs
	pandoc -t beamer $<  -o $@

clean:
	rm -f *.pdf *.md

