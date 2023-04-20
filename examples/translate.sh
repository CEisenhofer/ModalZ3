#/bin/bash

for file in $1/*.ksp
do
	echo "${file%.*}.ksp"
  cat "${file%.*}.ksp" | ../balsiger/balsiger "$2" > "${file%.*}.smt2"
done
