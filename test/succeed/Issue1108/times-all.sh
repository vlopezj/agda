#!/bin/bash

for i in `seq 1 13`; do
    for file in Issue1108 'Issue1108-2'; do
        count=$((2**$i))
        php ${file}.php.agda $count > ${file}.agda
        time agda ${file}.agda -vprofile:7 | tee times/${file}.${count}.time
    done
done

