#!/usr/bin/env bash

./doit $1 > parse.out

if [[  $(head -1 ./parse.out) != ";;SUCCESS" ]]; then
    cat ./parse.out #Error text written to out
    exit
fi

csi -s ./parse.out
