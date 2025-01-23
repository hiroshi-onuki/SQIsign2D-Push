#!/bin/bash

for i in {1..10}
do
    nohup julia find_response.jl 4 1 100 >> response_fail_l1new_${i}.txt &
done

echo "All tasks have been started."
