# Make html listing
# Andreas, 2018-07-23

agda-html  =agda --html Everything.agda
docker     =docker run -v $(shell pwd):/home -w /home
docker-agda=$(docker) jlimperg/agda-stdlib

html : *.agda
	$(agda-html)

# Use docker-agda for running on travis.ci
deploy :
	$(docker-agda) $(agda-html)

# EOF
