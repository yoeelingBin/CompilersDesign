#!/bin/bash

cd test
for filename in *.seal; do
    echo "--------Test using" $filename "--------"
    ../parser  $filename > tempfile 
    diff tempfile ../test-answer/$filename.out > /dev/null
    if [ $? -eq 0 ]; then
        echo passed
    else 
        echo NOT passed
    fi
done
rm -f tempfile
cd ..