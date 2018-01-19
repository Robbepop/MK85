#!/usr/bin/env bash

./MK85 tests/alloc_two_vars.smt > tmp && diff tmp tests/alloc_two_vars.correct
./MK85 tests/bool1.smt > tmp && diff tmp tests/bool1.correct
./MK85 tests/bool2.smt > tmp && diff tmp tests/bool2.correct
./MK85 tests/bvadd_test.smt > tmp && diff tmp tests/bvadd_test.correct
./MK85 tests/bvadd_test2.smt > tmp && diff tmp tests/bvadd_test2.correct
./MK85 tests/bvneg_fixpoints.smt > tmp && diff tmp tests/bvneg_fixpoints.correct
./MK85 tests/bvnot_test.smt > tmp && diff tmp tests/bvnot_test.correct
./MK85 tests/DeMorgan1.smt > tmp && diff tmp tests/DeMorgan1.correct
./MK85 tests/DeMorgan2.smt > tmp && diff tmp tests/DeMorgan2.correct
./MK85 tests/bvsub_test.smt > tmp && diff tmp tests/bvsub_test.correct
./MK85 tests/bvsub_3_args.smt > tmp && diff tmp tests/bvsub_3_args.correct
./MK85 tests/bvugt_bvult_test.smt > tmp && diff tmp tests/bvugt_bvult_test.correct
./MK85 tests/bvugt_bvult_test2.smt > tmp && diff tmp tests/bvugt_bvult_test2.correct
./MK85 tests/bvuge_bvule_test.smt > tmp && diff tmp tests/bvuge_bvule_test.correct
./MK85 tests/bvsub_1_arg.smt > tmp && diff tmp tests/bvsub_1_arg.correct

./MK85 tests/distinct1.smt > tmp
a=$(cat tmp | grep bv | cut -d ';' -f 2 | sort | uniq | wc -l)
	
if [[ $a != "4" ]];
then
	echo "distinct1 failed"
	echo "got" $a
fi

./MK85 tests/distinct2.smt > tmp && diff tmp tests/distinct2.correct
./MK85 tests/distinct3.smt > tmp && diff tmp tests/distinct3.correct
./MK85 tests/zero_extend_test.smt > tmp && diff tmp tests/zero_extend_test.correct
./MK85 tests/extract_test.smt > tmp && diff tmp tests/extract_test.correct
./MK85 tests/ite_test1.smt > tmp && diff tmp tests/ite_test1.correct
./MK85 tests/bvmul_test.smt > tmp && diff tmp tests/bvmul_test.correct
./MK85 tests/bvmul_test3.smt > tmp && diff tmp tests/bvmul_test3.correct
./MK85 tests/factorize.smt > tmp && diff tmp tests/factorize.correct
./MK85 tests/bvsubge.smt > tmp && diff tmp tests/bvsubge.correct
./MK85 tests/bvudiv_test.smt > tmp && diff tmp tests/bvudiv_test.correct
./MK85 tests/bvudiv_test2.smt > tmp && diff tmp tests/bvudiv_test2.correct
./MK85 tests/bvneg_test.smt > tmp && diff tmp tests/bvneg_test.correct
./MK85 tests/t1.smt > tmp && diff tmp tests/t1.correct
./MK85 tests/XOR_alter.smt > tmp && diff tmp tests/XOR_alter.correct
./MK85 tests/modinv.smt > tmp && diff tmp tests/modinv.correct
./MK85 tests/bvneg_count_fixpoints.smt > tmp && diff tmp tests/bvneg_count_fixpoints.correct

./MK85 examples/mc.smt > tmp && diff tmp examples/mc.correct
./MK85 examples/fred.smt > tmp && diff tmp examples/fred.correct

./MK85 tests/bvshl2_test.smt > tmp && diff tmp tests/bvshl2_test.correct
./MK85 tests/bvlshr2_test.smt > tmp && diff tmp tests/bvlshr2_test.correct
./MK85 tests/bvlshr_10.smt > tmp && diff tmp tests/bvlshr_10.correct


