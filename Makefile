EAOP_HOME = .
EBIN = ${EAOP_HOME}/ebin
SRC = ${EAOP_HOME}/src

MODS = eaop eaopcore eaoputil eaopweaver

all: compile erl

erl:
	erl -pa ${EBIN}

ebin:
	mkdir ${EBIN}

compile: ebin ${MODS:%=${EBIN}/%.beam}

${EBIN}/eaop.beam: ${SRC}/eaop.erl
	erlc -o ${EBIN} ${SRC}/eaop.erl

${EBIN}/eaopcore.beam: ${SRC}/eaopcore.erl
	erlc -o ${EBIN} ${SRC}/eaopcore.erl

${EBIN}/eaoputil.beam: ${SRC}/eaoputil.erl
	erlc -o ${EBIN} ${SRC}/eaoputil.erl

${EBIN}/eaopweaver.beam: ${SRC}/eaopweaver.erl
	erlc -o ${EBIN} ${SRC}/eaopweaver.erl
clean:
	rm -rf ${EBIN}/*.beam ${EBIN}/erl_crash.dump
	rmdir ${EBIN}
