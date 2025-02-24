#! /bin/bash

cd "$(dirname "$0")" || exit 1

cd ../
cargo run > script/mynes.log
cd script || exit 1

vimdiff mynes.log nestest_no_cycle.log
