
all:
	swipl --goal=verify --stand_alone=true -o zad3 -c cb406099.pl

clean:
	rm zad3
