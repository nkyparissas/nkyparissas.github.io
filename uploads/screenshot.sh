#!/bin/bash
for i in 1 2 3 4 5 6 7 8 9 10
do
	if [ ${#i} -lt 2 ] ; then
		inputNo="00${i}"
		inputNo="${inputNo: -2}"
	else
		inputNo=$i
	fi
	now=$(date +"%T")
	if [ $i -lt 10 ] ; then
		echo $now": Saving screenshot" $inputNo"/10"
		sleep 1s
		scrot -q 50 ./Screenshots/screenshot${inputNo}_%b%d_%H%M%S.jpg
		echo "The next screenshot will be taken in 30m"
		sleep 30m
	else
		echo "This screenshot is the last one ("$inputNo"/10)"
		shutdown -P +270
		echo "Removing the screenshots in 4h hours"
		sleep 1s
		scrot -q 50 ./Screenshots/screenshot${inputNo}_%b%d_%H%M%S.jpg
		sleep 4h
		rm ./Screenshots/*
	fi
done
