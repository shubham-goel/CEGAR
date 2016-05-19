#!/bin/bash

mkdir temp
mv results/* temp/
mkdir results/old/
mkdir results/interesting/
mkdir results/not_interesting/
mv temp/* results/old/
rm -r temp

k=1
for nodes in `seq 10 20`;
do
	start_edges=$((2*$nodes))
	end_edges=$((3*$nodes))
	for edges in `seq $start_edges $end_edges`;
	do
		for messages in `seq 10 15`;
		do
			start_timeout=$((2*$messages-5))
			end_timeout=$((2*$messages+5))
			for timeout in `seq $end_timeout -1 $start_timeout`;
			do
				l1=$(($messages/2))
				l=$( printf "%.0f" $l1 )

				directory="$nodes-$messages-$edges-$timeout-$k-$l"
				echo "Progress : $directory::(10-20)-(10-15)-($start_edges-$end_edges)-($end_timeout-$start_timeout)-$k-$l"
				python ScheduleTwoPathsCEGAR.py $nodes $messages $edges $timeout $k $l --quiet -d > "$directory.curr"
				if [ $? -ne 0 ]; then
					prefix="results/not_interesting"
				else
					prefix="results/interesting"
				fi
				mkdir "$prefix/$directory"
				cp -r schedules "$prefix/$directory/"
				mv "$directory.output" "$prefix/$directory/"
				mv "$directory.setting" "$prefix/$directory/"

				target="schedules/"
				if ! find "$target" -mindepth 1 -print -quit | grep -q .; then
				    break
				fi
			done
		done
	done
done
