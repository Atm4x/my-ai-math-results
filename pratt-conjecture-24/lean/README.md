# Pratt Conjecture 24 — Lean 4 counterexample

This standalone formalization refutes Conjecture 24 in Kevin Pratt, *On Generalized Corners and Matrix Multiplication*, ITCS 2024, DOI: 10.4230/LIPIcs.ITCS.2024.89.

Original source: https://drops.dagstuhl.de/storage/00lipics/lipics-vol287-itcs2024/LIPIcs.ITCS.2024.89/LIPIcs.ITCS.2024.89.pdf

The eight-edge radix-seven construction is taken from the v68 counterexample. This formalization changes the counting argument: rather than fixing all digit histograms and invoking Stirling's formula, it groups words by their six marginal sums (digit masses and separating weights), using an elementary finite pigeonhole argument. No prior speculative VAL-CYCLIC results are imported.

## Verify

Requires Lean 4.34.0, including its standard library. No Mathlib, Lake downloads, Python, external solvers, or extra project axioms are required.

```sh
lean --trust=0 --error=warning -o Pratt.olean Pratt.lean
```

Alternatively run `./verify.sh /absolute/path/to/lean` (the executable argument defaults to `lean`). The script checks the source in a temporary output directory and checks the reported dependencies of the final theorem.

The recorded verification used Lean 4.34.0 (commit 293d5d0c0c3f3dded4688b3ccd6a33939ac5102b), trust level 0, and warnings treated as errors. See `verification.log`. The source contains no `sorry`, `admit`, `axiom`, `unsafe`, or `native_decide` declarations/calls. The final theorem depends only on `propext`, `Classical.choice`, and `Quot.sound`.

## Definitions and theorem correspondence

- `ETF`: all three anchored uniqueness conditions of Pratt's Definition 17, expressed in terms of an induced target relation.
- `FinEdge`: membership in three subsets of `Fin N` and zero sum under addition modulo N. `fin_zero_equiv` proves the latter is precisely the equation `a+b+c=0` when N is positive.
- `targetList_mem`, `targetList_nodup`: the target list enumerates the induced zero-sum triples exactly once.
- `val`: the finite maximum of the number of such triples over all ETF triples of subsets. It is defined by enumerating the powerset and taking the maximum. `val_le_iff` proves its characterization as the least upper bound over all such triples; this is the maximum in Definition 17.
- `digitETF`, `digitFilter`, `word_filter`, `wordETF`, `targetETF`: the eight-edge certificate, exact separating weights, all-length exclusion of carries and extra targets, and all three ETF conditions.
- `val_lower`: for every natural n,

  `8^n <= (6*n+1)^6 * val (3*(7^n-1)+1)`.

  This gives the same exponential growth exponent log_7(8) as v68, with a different polynomial loss. It does not assert v68's sharper multinomial factor.
- `explicit_violation` and `fin_explicit_violation`: for every natural K and threshold N0, a modulus N >= N0 and an ETF target list with no duplicates exist such that `K*N^101 < ts.length^100`.
- `not_ValPrattConjecture24`: negates the natural-power form of Conjecture 24 for the actual `val` function, using q=100.

## Bridge to the published real-exponent statement

The published conjecture says that for every epsilon > 0, val(Z_N) = O(N^(1+epsilon)). Choose epsilon = 1/100. If the published conjecture held, there would be a real constant C >= 0 and a threshold N0 such that val(Z_N) <= C*N^(101/100) for all N >= N0. Raising to the 100th power and taking an integer K >= C^100 gives val(N)^100 <= K*N^101 eventually. The final Lean theorem rules out even that single necessary consequence. This elementary real-to-natural implication is stated here in prose; the Lean file deliberately avoids a real-analysis library and formalizes the natural-power statement and the exact finite maximum.

No independent external review or claim of scientific priority is made.
