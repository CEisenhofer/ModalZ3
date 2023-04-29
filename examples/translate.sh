#/bin/bash

shopt -s nullglob # ignore if nothing was found in the directory

for file in $(find $1 -name '*.ksp' -or -name '*.intohylo');
do
  echo "${file}"
  cat "${file}" | ../balsiger/balsiger "$2" > "${file}.smt2"
done

#for file in $1/*.intohylo
#do
#  echo "${file%.*}.intohylo"
#  cat "${file%.*}.intohylo" | ../balsiger/balsiger "$2" > "${file%.*}.smt2"
#done
