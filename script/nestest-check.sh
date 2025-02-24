#! /bin/bash

cd `dirname $0`

cd ../
cargo run > script/mynes.log
cd script

vimdiff mynes.log nestest_no_cycle.log
