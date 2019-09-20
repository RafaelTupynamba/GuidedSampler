# GuidedSampler
GuidedSampler: Coverage-guided Sampling of SMT Solutions

[Paper](https://people.eecs.berkeley.edu/~rtd/papers/GuidedSampler.pdf)

# Building

Install dependencies

```
sudo apt install git python g++ make
```

Clone repos

```
git clone https://github.com/RafaelTupynamba/GuidedSampler.git
git clone https://github.com/Z3Prover/z3.git
```

Build z3 (with a patch to collect coverage information from the formula)

```
cd z3
git checkout bb7ad4e938ec3ade23282142119e77c838b1f7d1
cp ../GuidedSampler/z3-patch/mk_util.py scripts/mk_util.py
cp ../GuidedSampler/z3-patch/rewriter_def.h src/ast/rewriter/rewriter_def.h
cp ../GuidedSampler/z3-patch/model.cpp src/model/model.cpp
cp ../GuidedSampler/z3-patch/permutation_matrix.h src/util/lp/permutation_matrix.h
python scripts/mk_make.py
cd build
make
sudo make install
cd ../..
```

Build GuidedSampler

```
cd GuidedSampler
make
```

# Running

Example runs:

```
#  Collect a set of internal predicates to be used as coverage predicates
./guidedsampler -n 1000000 -t 1800.0 --get-internal-predicates formula.smt2

# Sample solutions to the formula, guided by the internal predicates, using the default GuidedSampler strategy (--random-soft-preds)
./guidedsampler -n 1000000 -t 1800.0 --use-internal-predicates --random-soft-preds formula.smt2

#  Generate a set of random predicates to be used as coverage predicates
./guidedsampler -n 1000000 -t 1800.0 --get-random-predicates formula.smt2

# Sample solutions to the formula, guided by the random predicates, using the default GuidedSampler strategy (--random-soft-preds)
./guidedsampler -n 1000000 -t 1800.0 --use-random-predicates --random-soft-preds formula.smt2
```

GuidedSampler will create a file `formula.smt2.samples` with the samples generated and print statistics to standard output. The file `formula.smt2.samples` has two lines for each produced sample. The first number represents the number of atomic mutations which were used to generate this sample. Then, the sample is displayed in a compact format. The next line starting with "P:" displays the coverage class of the sample.

The option -n can be used to specify the maximum number of samples produced and the option -t can be used to specify the maximum time allowed for sampling.

The option `--get-internal-predicates` can be used to collect an interesting set of internal predicates from the formula itself. The predicates are chosen by sampling solutions to the formula using the SMTSampler algorithm and then collecting coverage statistics from the internal nodes of the formula. We identify a subset of the nodes that exhibit diverse coverage behavior and save the subformulas corresponding to those nodes as the coverage predicates.

The option `--use-internal-predicates` can be used to sample solutions to the formula guided by the set of internal predicates. The set of internal predicates must have already been collected in a previous run using the option `--get-internal-predicates`.

The option `--get-random-predicates` can be used to generate a set of random predicates over the variables of the formula.

The option `--use-random-predicates` can be used to sample solutions to the formula guided by the set of random predicates. The set of random predicates must have already been collected in a previous run using the option `--get-random-predicates`.

Six different approaches can be used for sampling, as described in the GuidedSampler paper.

`--pred-hard`: baseline approach with hard constraints (BH)

`--pred-soft`: baseline approach with soft constraints (BS)

no option: SMTSampler approach (S0)

`--flip-preds`: approach S1, includes flipping coverage predicates to generate neighboring solutions

`--remove-repeated`: approach S2, includes S1 and also discards solutions from repeated coverage classes

`--random-soft-preds`: the GuidedSampler approach S3, includes S2 and also randomizes the coverage class of the initial base solution


All the samples that GuidedSampler outputs are valid solutions to the formula.

# Benchmarks

The benchmarks used come from SMT-LIB. They can be obtained from the following repositories.

[QF_AUFBV](https://clc-gitlab.cs.uiowa.edu:2443/SMT-LIB-benchmarks/QF_AUFBV)
[QF_ABV](https://clc-gitlab.cs.uiowa.edu:2443/SMT-LIB-benchmarks/QF_ABV)
[QF_BV](https://clc-gitlab.cs.uiowa.edu:2443/SMT-LIB-benchmarks/QF_BV)

# Paper

[FMCAD 2019 paper](https://people.eecs.berkeley.edu/~rtd/papers/GuidedSampler.pdf)

GuidedSampler: Coverage-guided Sampling of SMT Solutions

Rafael Dutra, Jonathan Bachrach, Koushik Sen
