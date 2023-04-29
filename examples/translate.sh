#/bin/bash

shopt -s nullglob # ignore if nothing was found in the directory

for file in $1/*.ksp
do
	echo "${file%.*}.ksp"
  cat "${file%.*}.ksp" | ../balsiger/balsiger "$2" > "${file%.*}.smt2"
done

for file in $1/*.intohylo
do
	echo "${file%.*}.intohylo"
  cat "${file%.*}.intohylo" | ../balsiger/balsiger "$2" > "${file%.*}.smt2"
done
