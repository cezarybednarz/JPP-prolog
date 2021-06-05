
all:
	swipl --goal=verify --stand_alone=true -o exec -c cb406099.pl

clean:
	rm exec
