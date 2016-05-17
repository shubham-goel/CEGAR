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
			for timeout in `seq $start_timeout $end_timeout`;
			do
				start_l1=$(($messages/2))
				start_l=$( printf "%.0f" $start_l1 )
				end_l=$(($messages-3))
				for l in `seq $start_l $end_l`;
				do
					directory="$nodes-$messages-$edges-$timeout-$k-$l"
					echo "Progress : $directory::(10-20)-(10-15)-($start_edges-$end_edges)-($start_timeout-$end_timeout)-$k-($start_l-$end_l)"
					python ScheduleTwoPathsCEGAR.py $nodes $messages $edges $timeout $k $l --quiet -d > output.curr
					if [ $? -ne 0 ]; then
						prefix="results/not_interesting"
					else
						prefix="results/interesting"
					fi
					mkdir "$prefix/$directory"
					cp -r schedules "$prefix/$directory/"
					touch "$prefix/$directory/output"
					touch "$prefix/$directory/setting"
					cat output.curr > "$prefix/$directory/output"
					cat setting.curr > "$prefix/$directory/setting"
				done
			done
		done
	done
done
