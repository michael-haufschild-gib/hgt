# RH and twin primes as observations of one arithmetic pair kernel

- **ID:** twin-prime-rh-pair-kernel-bridge
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) / BRIDGE
- **Lean:** `formal/GaloisForLFunctions/twin-prime/RHPairKernelBridge.lean`
- **Source:** user-requested RH--twin-prime bridges; corpus `RHTower/Sieve/SquareWindowEnergyUnderRH.lean`
- **Statement:** Express an existing RH-equivalent correlation energy and exact twin-prime tail detection using the same von Mangoldt pair kernel, with prime-power removal explicit.

## Exact object and certified bridge

For natural `n`, set `w(n)=Lambda(n)/sqrt(n)` and `K(k,l)=w(k)w(l)`; division at zero is the real-field convention and `Lambda(0)=0`. Let `K_sf(k,l)=mu(k)^2 mu(l)^2 K(k,l)`.

The unconditional finite theorem is

`K_sf(k,l)>0 iff k and l are prime`.

Consequently the exact twin-prime target is equivalent to

`for every N, some M has sum_(N<n<=M) K_sf(n,n+2)>0`.

This asks for arbitrarily late positive gap-two mass. It does not replace infinitude by divergence of a weighted sum, which would be stronger without a density theorem.

The corpus's square-window RH criterion uses `T_M={0,...,M^2}`, the overlap kernel `O_M(k,l)` counting square windows `(m^2/2,m^2]` containing both indices, the first-moment kernel `F_M(k)` summing the window indices containing `k`, and `c=2(1-1/sqrt(2))`. Its energy is exactly

`C(M)=sum_(k,l in T_M) K(k,l) O_M(k,l)
      -2c sum_(k in T_M) sqrt(K(k,k)) F_M(k)
      +c^2 sum_(1<=m<=M) m^2`.

The diagonal square root equals `w(k)` because von Mangoldt is nonnegative. Existing theorem `RHTower.Sieve.riemannHypothesis_iff_squarePrimeWindowCorrelationEnergySubpower` identifies RH with `C(M)=O_delta(M^(1+delta))` for every positive `delta`.

A further exact partition of the first double sum isolates the two orientations of the prime gap-two pairs, leaving all other pairs as a nonnegative remainder. This shows where twin-prime data occurs inside the RH correlation expression without asserting that its aggregate bound determines this one slice.

## Sharper bridge: deletion of one lag preserves the RH criterion

Let `S_h(M)` be the prime-projected part of the pair sum with `l=k+h`, for any natural lag `h`. There is an unconditional bound, uniform in `h`,

`S_h(M) <<_epsilon M^(1+epsilon)` for every `epsilon>0`.

Indeed, `0<=O_M(k,l)<=M`, the prime projection is between zero and `K`, and `2w(k)w(l)<=w(k)^2+w(l)^2`. In a fixed-lag slice every index occurs at most once in each coordinate, so

`S_h(M)<=M sum_(0<=n<=M^2) w(n)^2`.

For `0<d<=1` and `M>=1`,

`sum_(1<=n<=M^2) Lambda(n)^2/n
 <=M^(4d) sum_(1<=n<=M^2) Lambda(n)^2 n^(-1-2d)
 <=(5/d^2) M^(4d)`.

The last bound is the existing unconditional theorem `RHTower.sum_vonMangoldt_sq_rpow_le`; its actual source was read. It follows from Chebyshev's bound and an elementary logarithm/power estimate, with no RH premise. Take `d=min(epsilon,1)/4`.

Thus the sharper exact equivalence, now formalized, is

`RH iff C(M)-2S_2(M)=O_epsilon(M^(1+epsilon)) for every epsilon>0`.

Proof: `2S_2` already satisfies every one of these bounds unconditionally, and big-O is closed under addition and subtraction. This does not assert logical independence of RH and twin primes. It identifies a concrete limitation of this shared representation: the RH growth class is unchanged when its explicit twin-prime slice is removed. A proof relating the conjectures must supply more than this aggregate growth criterion.

**Verdict: BRIDGE.** This is a closed deduction from the existing energy criterion and elementary coefficient bounds. No scientific priority is claimed. It makes the relationship more informative than merely placing both statements in one definition.

## Dependency-closed paper proof

1. `Lambda(n)>0` exactly at prime powers. Such an integer is squarefree exactly when it is prime. The Möbius square is one on squarefree integers and zero elsewhere. Since square roots are positive at primes, this gives the exact support of `K_sf`.
2. Every term of the tail sum is nonnegative. A finite sum is positive exactly when at least one term is positive. This proves both directions of the tail criterion, preserving the requested `p>N` quantifier.
3. Substitute `K(k,l)=w(k)w(l)` and `sqrt(K(k,k))=w(k)` into `C(M)`. The result is literally the existing square-window correlation energy. Transfer the already proved RH equivalence; audit its actual axiom closure.
4. Partition ordered pairs into prime gap-two pairs and their complement. Swapping indices preserves the carrier, kernel, and window overlap, so the two orientations contribute equally. This is an exact finite equality, with no estimate assumed for the complement.

All analytic input on the RH side must come from the existing unconditional equivalence. No RH assumption, prime-pair estimate, or new analytic interface is allowed as a premise of the bridge capstones. Kernel equivalences do not assert either conjecture.

The prime-power support facts were checked in mathlib source after the corpus search: `vonMangoldt_pos_iff`, `vonMangoldt_eq_zero_iff`, `moebius_apply_prime`, and `moebius_apply_isPrimePow_not_prime`. They close step 1 directly, including zero and one. The existing RH equivalence's statement and finite correlation definition were inspected in Lean. The full mathematical proof, new Lean implementation, and dependency axiom audit are complete.

## Frontier and attack

Corpus search first located the exact RH correlation criterion and the separately formalized Möbius--Mertens RH criteria. Their actual Lean statements were inspected. The square-window formulation supplies the closest shared arithmetic object; no need to replace RH by an unverified heuristic.

[Tao's correlation lectures](https://terrytao.wordpress.com/wp-content/uploads/2024/03/correlations-jan-5.pdf), pages 3--12, discuss the shared multiplicative-sign viewpoint, RH-scale one-point cancellation, and the parity obstruction for prime pairs. The 2024 claims about the then-open two-point Chowla problem are superseded by later sources; they are not used as a current-status assertion.

The current [ordinary two-point correlation manuscript](https://github.com/openai/math/blob/main/preprints/Ordinary-two-point-correlations-of-multiplicative-functions-September-24-2026/final.pdf), Theorems 1.1--1.2 and Corollary 1.3, supplies fixed-form statements. Its introduction explicitly excludes uniformity for growing affine coefficients. No quantitative determinant estimate is inferred from it.

The classical connection between zero pair correlation and short-interval prime variance is adjacent, not identical, to this bridge. [Languasco--Perelli--Zaccagnini (2012)](https://doi.org/10.1016/j.jmaa.2012.04.058) gives a quantitative Goldston--Montgomery transfer under RH. Its introduction was inspected; that theorem concerns an additional zero-correlation conjecture and averaged prime variance. It is not an implication from RH alone to fixed-gap prime positivity, and it is not used as an input to the new Lean proof.

**Verdict: BRIDGE.** The shared-kernel representation is a structural connection, not an RH--twin-prime equivalence or a scientific novelty claim. The sharper unification conjecture would require a new theorem controlling fixed-gap prime mass from the RH-type aggregate information, or a stronger common arithmetic law implying both. That theorem is not available here.

## Gates

- [x] Exact objects, source statements, and complete algebraic proof plan.
- [x] Check prime-power support lemmas in source and close paper dependencies.
- [x] Formalize exact kernel, RH readout, and twin-prime tail criterion.
- [x] Formalize the gap-two/complement partition.
- [x] Formalize the uniform fixed-lag bound and RH criterion after deleting the twin slice.
- [x] Leaf compile and capstone axiom audit.
- [x] Record the precise common structure and remaining distinction for the user.

## Lean surface and verification

- `TwinPrime.riemannHypothesis_iff_pairKernel_energy`: RH through the common pair kernel.
- `TwinPrime.twinPrimes_iff_pairKernel_tail_positive`: exact twin-prime infinitude criterion.
- `TwinPrime.rhPairMass_eq_twins_add_complement`: two twin orientations plus nonnegative complement.
- `TwinPrime.rhPrimeLagSlice_uniform_bound`: one subpower constant for every lag.
- `TwinPrime.riemannHypothesis_iff_pairKernel_energy_without_twins`: deletion preserves the RH growth criterion.

The leaf command `lake --old env lean GaloisForLFunctions/twin-prime/RHPairKernelBridge.lean` passed without warnings. All five capstones returned only `[propext, Classical.choice, Quot.sound]`. No analytic assumption, new axiom, placeholder, computation certificate, or raised elaboration option was introduced. The leaf is imported by the twin-prime umbrella; no umbrella build was run.

Indexes were regenerated and the deletion capstone is returned by the corpus search. All 21 owned source/card files passed whitespace and relative-link checks. Global lint still reports unreachable modules, research leaves at package root, and stale generated summaries during concurrent work; no global lint pass is claimed.

The first implementation had a recursive simplification in the pair partition. Explicit disjoint cases fixed it without increasing options. Later finite-selector and coercion issues were resolved against the actual mathlib declarations. Only failed or materially changed proofs were rechecked.

This is requested structural bridge work, not new scientific knowledge or a proof of either conjecture. The broader twin-prime programme still needs actual signed cancellation or another source of fixed-gap positivity.

## Log

- 2026-10-23 — Added in response to the user's request. The unconditional twin-prime goal remains active; this bridge work is a supporting task, not a replacement completion criterion.
- 2026-10-23 — Completed all five bridge capstones and their standard-axiom audits. The stronger uniform-lag estimate identifies a precise limitation of the shared RH energy representation.
