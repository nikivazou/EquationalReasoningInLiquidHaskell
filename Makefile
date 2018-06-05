MATHJAX=http://cdn.mathjax.org/mathjax/latest
LIQUIDCLIENT=../liquid-client
SLIDES=dist/_slides
SITE=dist/_site
DIST=dist/_build
TEMPLATES=assets/templates
FILTERS=assets/filters
JS=assets/js
CSS=assets/css
IMG=assets/img

##############################################
PANDOC=pandoc
INDEXER=$(FILTERS)/Toc.hs
METATEMPLATE=$(TEMPLATES)/pagemeta.template
INDEXTEMPLATE=$(TEMPLATES)/index.template
PREAMBLE=$(TEMPLATES)/preamble.lhs
BIB=$(TEMPLATES)/bib.lhs

# generated
PAGETEMPLATE=$(DIST)/page.template
LINKS=$(DIST)/links.txt
INDEX=$(DIST)/index.lhs

##############################################

PANDOCHTML=$(PANDOC)\
     --from=markdown+lhs \
	 --to=html5 \
     -s --mathjax \
	 --standalone \
     --parse-raw \
	 --mathjax \
	 --toc \
	 --section-divs \
	 --filter $(LIQUIDCLIENT)/templates/codeblock.hs \
	 --filter $(FILTERS)/Figures.hs \
	 --filter $(FILTERS)/Html.hs \
	 --variable=notitle \
	 --highlight-style=tango

REVEAL=$(PANDOC)\
	   --from=markdown\
	   --to=html5                           \
	   --standalone                         \
	   --mathjax \
	   --section-divs                       \
	 --filter $(FILTERS)/Slides.hs \
	   --template=$(TEMPLATES)/template.reveal  \
	   --variable reveal=js/reveal.js \
	   --variable mathjax=$(MATHJAX)

# LIQUID=liquid --short-names

####################################################################

lhsObjects   := $(wildcard src/*.lhs)
texObjects   := $(patsubst %.lhs,%.tex,$(wildcard src/*.lhs))
htmlObjects  := $(patsubst %.lhs,%.html,$(wildcard src/*.lhs))
mdObjects    := $(patsubst %.lhs,%.lhs.markdown,$(wildcard src/*.lhs))
slideObjects := $(patsubst %.lhs,%.lhs.slide.html,$(wildcard src/*.lhs))

####################################################################

all: html

################ rust style html ###################################

html: indexhtml $(htmlObjects)
	cp src/*.html               $(SITE)/
	cp -r $(IMG)                $(SITE)/
	cp -r $(CSS)                $(SITE)/
	cp -r $(LIQUIDCLIENT)/fonts $(SITE)/
	cp -r $(LIQUIDCLIENT)/css   $(SITE)/
	cp -r $(LIQUIDCLIENT)/js    $(SITE)/

indexhtml: $(INDEX)
	$(PANDOC) --from=markdown+lhs --to=html5 --template=$(INDEX) $(PREAMBLE) -o $(SITE)/index.html

$(INDEX):
	$(INDEXER) src/ $(METATEMPLATE) $(INDEXTEMPLATE) $(PAGETEMPLATE) $(INDEX) $(LINKS)

src/%.html: src/%.lhs
	PANDOC_TARGET=$@ PANDOC_CODETEMPLATE=$(LIQUIDCLIENT)/templates/code.template $(PANDOCHTML) --template=$(PAGETEMPLATE) $(PREAMBLE) $? $(TEMPLATES)/bib.lhs -o $@

################ reveal slides html ###################################

slides: $(slideObjects)
	mv src/*.html $(SLIDES)/
	cp -r $(IMG)  $(SLIDES)/
	cp -r $(JS)   $(SLIDES)/
	cp -r $(CSS)  $(SLIDES)/


src/.liquid/%.lhs.markdown: src/%.lhs
	-$(LIQUID) $?

src/%.lhs.slide.html: src/.liquid/%.lhs.markdown
	$(REVEAL) $? -o $@

################ CLEAN and SYNC #######################################

clean:
	rm -rf $(DIST)/* && rm -rf $(SITE)/* && rm -rf src/*.tex && rm -rf src/.liquid && rm -rf src/*.html

#clean:
#	cd lhs/ && ../cleanup && cd ../
#	cd html/ && rm -rf * && cd ../
#	cp index.html html/
