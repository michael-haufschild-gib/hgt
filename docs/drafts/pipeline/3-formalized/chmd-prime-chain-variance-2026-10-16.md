# CHMD: complete arithmetic prime-chain variance factorization

Status: dependency-closed paper proof and Lean formalization kernel-audited. RH remains unproved; the goal remains active.

## Structural result

The complete positive origin-crossing source has an exact nonlocal variance factorization. Every original theta index, prime, prime power and arithmetic weight is retained. The result resolves the finite arithmetic reindexing and infinite-family convergence needed for this factorization. It does not resolve the original cosh subtraction.

For a positive product index N, prime p dividing N, divisor b of N, and real logarithmic cut u, define

- L = {m in divisors(N): ordCompl[p] m = b and log m < u};
- R = {k in divisors(N): ordCompl[p] k = b and u < log k};
- l = |L|, r = |R|;
- A and B = arithmetic means of a on L and R;
- V_L = sum over L of (a_m-A)^2, and V_R analogously.

Empty means are zero; empty sides contribute zero. The exact identity is

E(L,R;a) = sum over m in L, k in R of (a_m-a_k)^2
          = r V_L + l V_R + lr(A-B)^2.

The original finite Mangoldt divisor-cut energy equals

sum over p in primeFactors(N), b in divisors(N) of log(p) E(L,R;a).

Thus each prime chain splits into two internal variance sectors and one scalar mean-difference square. Isolated vertices and disconnected cuts are retained; no connectivity assumption is inserted.

## Dependency-closed paper proof

1. **Exact edge classification.** Write m=p^i b and k=p^j b using their p-primary factors and common p-free complement. If 0<m<k, then i<j, so k/m=p^(j-i), and its Mangoldt weight is log p. Conversely, an active Mangoldt divisor edge has a prime-power ratio and hence equal p-free complements. Its prime is unique: it is the least prime factor of the ratio. The base b divides m and therefore N. This proves the exhaustive, multiplicity-one prime-chain partition.

2. **Finite reindexing.** Extend the inner divisor sum from divisors(k) to divisors(N) using the indicator m divides k. Replace its Mangoldt coefficient by the exact prime-chain coefficient from step 1. Sum over the unique base b=ordCompl[p] m and exchange only finite sums. The strict inequalities at cut endpoints are identical on both sides.

3. **Variance identity.** Expanding the bipartite energy gives r sum_L(a_m^2)+l sum_R(a_k^2)-2(sum_L a_m)(sum_R a_k). Expanding the centered sums and substituting sum_L a_m=lA and sum_R a_k=rB gives the displayed three-sector identity. If either set is empty, both sides are zero. Its nullspace is exactly equality of a_m and a_k on every cross-side pair. Applying this to every prime chain gives the complete finite-fibre nullspace classification, including empty chains.

4. **Original theta fibre.** Substitute a_m=v(u-log m) and multiply by the unchanged fibre

   F_N(u)=cuspTerm(riemannCuspPoly,1,u) cuspTerm(riemannCuspPoly,N,-u).

   Every contributing chain satisfies 0<u<log N, where F_N(u)>0. Outside that interval one side of each chain is empty. Since log p>0, every individual chain density is nonnegative on the full real line.

5. **Analytic closure.** The finite indicator expansion proves measurability of each chain density. It is bounded above by the complete nonnegative cut density, whose integrability follows from the existing finite theta-edge expansion. Hence every chain is integrable. Index all components by the countable dependent family (N,p,b), where N is positive, p divides N and b divides N. Its finite N-fibre sum is the original cut integral. The earlier complete cut HasSum theorem and nonnegative sigma-summation therefore prove summability of the entire family, including the integrals of absolute values. The integral and complete sum may be exchanged. No truncation, numerical experiment, or prime-distribution premise occurs.

6. **Actual source and reflection.** The resulting sum equals the original prime-crossing source. Substitution into the already-proved Doob identity gives

   markovEnergy(Theta v) = archJump(v) + sameSide(v) + sameSide(v composed with negation)
                         + complete prime-chain variance sum - coshMass(v^2).

   For odd v, the same complete chain sum equals the original collar killing term minus twice the reflected-prime difference energy, summed over all original prime powers. Thus the previously isolated negative singular reflection component is retained through its exact compensation. The new sum vanishes exactly when a continuous compactly supported v is zero; this supplies no uniform comparison with coshMass.

## Lean artifacts

- `formal/GaloisForLFunctions/RHTower/CHMDPrimeChainVariance.lean`: 350 lines, 30 declarations. Namespace `RHTower.CHMDPrimeChain`. Main results: `mangoldt_edge_eq_chain_sum`, `divisor_cut_eq_chainVariance` (line 240), `chainVariance_zero_iff` (line 289), and individual-chain support lemmas.
- `formal/GaloisForLFunctions/RHTower/CHMDPrimeChainSourceFactorization.lean`: 220 lines, 21 declarations. Namespace `RHTower.CHMDPrimeChainSource`. Main results: `complete_chain_hasSum` (line 154), `complete_chain_norm_summable` (line 171), `doob_source_eq_chain_variances_sub_cosh` (line 185), `integral_complete_chain` (line 194), and `reflected_compensation_hasSum_chains` (line 211).
- Both leaves wired once in `formal/GaloisForLFunctions/RHTower.lean`. Existing mathematical leaves unchanged.

## Verification

Arithmetic and source scratch proofs passed. Mathlib-name and finite-subtype reindexing probes passed. Both `lake --old build` leaf commands exited 0. Final plain `lake env lean` audits of both tree leaves exited 0 with empty output. All 51 declarations were audited with `#print axioms` in `/tmp`: exactly the standard `propext`, `Classical.choice`, and `Quot.sound` were reported; no missing declarations or extra axioms. New leaves emit no warnings. The source leaf build replays existing dependency warnings.

Hashes at final direct audit:

- Arithmetic: `c2646ccc128aae1a8f0ba0e6198798709155f4e4147dda94cfcc4cd6fc96dbb2`.
- Source: `a0f96631b1c0ce47f9f17ace59b16a9cfdac54823dc5a175cf20a711d4c1577e`.

Corpus checks: three deep searches completed with full inventory coverage; existing compiler metadata included stale/uncompiled entries. Candidate applicability was checked against actual Lean sources and this toolchain. No external search, novelty claim, old research Markdown, heartbeat override, umbrella build, subagent, commit or push.

Index exited 0: five changed sources, including concurrent work. Global lint exited 1 solely because three unrelated, untracked modules were unreachable from the umbrella: `DeningerMeyerGaussianStripRegularization`, `DeningerMeyerMellinReconstruction`, and `DeningerMeyerMellinStripControl`. Those modules were left untouched. Both new CHMD leaves are reachable and have no lint errors. Scoped diff and new-artifact whitespace checks passed. All owned process handles are terminal. All 18 owned scratch/search/audit/log files were removed and their absence verified; audited source hashes remain unchanged.

## Remaining obstruction

The exact factorization concerns the retained positive crossing source. Neither its strict positivity nor its variance decomposition proves domination of the negative cosh mass. The next conjecture must address that mass jointly with the original archimedean and same-side terms, using the explicit chain-mean and internal-variance sectors. No positive factorization of the full Weil form, original CHMD defect elimination, or unconditional RH proof is claimed.
