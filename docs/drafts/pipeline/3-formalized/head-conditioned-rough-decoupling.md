# Head-conditioned decoupling of rough Dirichlet polynomials on the height line

- **ID:** head-rough-decoupling
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `formal/GaloisForLFunctions/SquareRootThreshold/README.md` §5 research topic 7
  ("Every height"); `formal/GaloisForLFunctions/RHTower/PrimeTorusPhaseSecondMomentAndBlockIndependence.lean`
  (block independence on the torus) and `.../FiniteEulerProductKroneckerWeylLimitLaw.lean`
  (return-set density on heights).
- **Statement:** Weighting the heights by the return kernel of any finite set of primes below `y`
  leaves the mean square of every `y`-rough Dirichlet polynomial unchanged, with an effective
  error: `|∫_0^T K_P(τ)|D(τ)|² dτ − T·2^{|P|}Σ_m|α_m|²| ≤ 4N(1+log N)·2^{|P|}Σ_m|α_m|²`.

## Goal
The orbit lane of the Square-Root Threshold programme (SRT research topic 7, with the Bagchi
modules of `RHTower`) stops at one named error: *the tail conditioned on the return set of the
finite Euler head, which no bound on the tail averaged over all heights controls.* The corpus owns
block independence of the prime phases only on the **prime torus with Haar measure**
(`torusHaar_inter_eq_mul_of_disjoint_blocks`) and the positive density of the return set on
heights (`eventually_ofReal_mul_le_volume_eulerTargetReturnSet`); the transfer of a **conditional
second moment** from the torus model to the actual height line was missing, and weak convergence
of the orbit to the torus model does not supply it, because the conditioning set is defined by the
head.

This card supplies that transfer, with an explicit error and no hypothesis. The consequence is
that the head-conditioning is **free**: the exceptional heights of the typical-height lane cannot
be confined to the return set of any finite Euler head, and a tail estimate averaged over all
heights now does control the tail on the return set.

## Gates
- [x] 0 → 1  in-progress
- [x] 1 → 2  fully-proven (two elementary arithmetic inputs; see Approach)
- [x] 2 → 3  formalized: `formal/GaloisForLFunctions/RHTower/HeadConditionedRoughDecoupling.lean`,
  wired into `GaloisForLFunctions.RHTower`; all capstones depend only on
  `propext, Classical.choice, Quot.sound`.
- [ ] 3 → 4  publication-ready

## Approach
Two arithmetic facts carry the statement, and both are specific to `ℕ`.

1. **Exact vanishing of the diagonal.** A cross term of `|P|²|D|²` carries the frequency
   `log(s'n) − log(sm)`, which vanishes iff `s'n = sm`; since a product of a `y`-smooth and a
   `y`-rough integer determines both factors (`RHTower.smooth_rough_pair_unique`), this forces
   `s = s'` and `m = n`. So the smooth block and the rough block are *exactly* orthogonal — the
   height-line form of block independence.
2. **Effective separation off the diagonal.** When it does not vanish the frequency is
   `log(A/B)` for distinct positive integers, hence at least `1/max(A,B)` in modulus. This is the
   integrality of the frequencies, and it is what makes the error effective.

Mechanically: the probe times the rough polynomial is a Dirichlet polynomial at the *product*
frequencies, which are distinct by (1); the general mean value theorem at distinct integer
frequencies (`norm_integral_normSq_familyHeightPoly_sub_diag_le`, proved here by fibring an
arbitrary finite family of distinct integers over the consecutive range and invoking the corpus
theorem `RHTower.Sieve.dirichlet_meanValue_theorem`) then gives the bracket, and the diagonal
factorises as `(Σ_s|w_s|²)(Σ_m|α_m|²)`.

The concrete probe is the Euler head itself: with `S` the squarefree products of a finite set `P`
of primes and unit coefficients, `|P(τ)|² = Π_{p∈P}(2 + 2cos(τ log p))`, the return kernel of `P`,
maximal exactly where every `p ∈ P` returns to phase one.

## Lean (unconditional, standard axioms only)
- `RHTower.norm_integral_normSq_familyHeightPoly_sub_diag_le` — the mean value theorem at
  arbitrary distinct integer frequencies: `|∫_0^T |Σ_q f_q (k_q)^{iτ}|² − T Σ_q |f_q|²| ≤
  4N(1+log N) Σ_q |f_q|²`. (The corpus owned only the consecutive range `1, …, N`.)
- `RHTower.norm_integral_normSq_smooth_mul_rough_sub_diag_le` — the decoupling with its effective
  error.
- `RHTower.norm_integral_normSq_head_sub_diag_le` — the probe's own mean square, from the same
  theorem with `M = {1}`.
- `RHTower.tendsto_headWeighted_roughMeanSquare` — the probe-weighted rough mean square converges
  to the unweighted one.
- `RHTower.primeReturnKernel`, `RHTower.normSq_integerHeightPoly_squarefreeProducts`,
  `RHTower.tendsto_primeReturnKernel_weighted_roughMeanSquare` — the instance at the return kernel
  of a finite set of primes.
- `RHTower.norm_integral_primeReturnKernel_mul_rough_sub_diag_le` — the same bracket written at the
  return kernel, with the explicit cutoff `returnKernelCutoff P M`.
- `RHTower.mul_setIntegral_primeReturnKernel_badHeights_le` — Chebyshev in the return kernel: at
  most the fraction `1/λ` of the kernel's mass, up to the horizon-free error, lies at heights where
  the rough polynomial exceeds `λ` times its mean square.  This is the form the orbit lane needs:
  the budget `δ < η(y)` of a pigeonhole between the tail-bad density `δ` and the return density
  `η(y)` is no longer required, because the bad set has small density **relative to the kernel**.
- `RHTower.abs_integral_primeReturnKernel_sub_diag_le`,
  `RHTower.le_setIntegral_primeReturnKernel_goodHeights` — **return and smallness at once**: the
  heights where the primes below `y` return *and* the rough polynomial stays below `λ` times its
  mean square carry at least
  `(T − C)2^{|P|} − (T + C)2^{|P|}/λ` of the kernel's mass, positive for `λ > 1` once `T > C`.
  There is no relation imposed between the cutoff `y` and the budget, which is exactly what the
  density pigeonhole cannot provide.  Any probe carried by `y`-smooth integers is admissible, so
  the Fejér kernels of every order (products of prime powers below a bound) are covered and the
  concentration on the exact return set can be made as sharp as wanted.

## Selectivity
The first input survives for a Beurling system (generators still factor uniquely); the second does
not — products of Beurling generators are not integers, and the off-diagonal frequencies can be
arbitrarily small, so no effective error exists there. The theorem is therefore carried by the
integrality of the frequencies, not by their independence, and it fails for a general Beurling
system at the quantitative level. It is blind to the shifted pair `ζ(s−a)ζ(s+a)` and to the
Liouville twist, which do not change the frequencies: like every mean-value statement it is
infrastructure, not a selective estimate, and it is recorded as a tool, not as progress in the
width unit.

## Where it lands in the orbit lane
`RHTower.ZetaDiscRecurrenceOnEveryClosedDiscOfTheStrip` reduces RH to `HeadTargetUniformlyDense`
(the Dirichlet heads approximate `ζ` on every closed disc of the strip at cutoff-uniform positive
density) and proves the zero-free case unconditionally
(`zetaDiscStronglyRecurrentOn_of_zeroFree_of_lt`); the tail laws
`eventually_eventually_volume_eulerDiscTailBadSet_le_of_lt` give the bad-set density `δ` only for
`y` large *after* `δ` is fixed, while the return density `η(y)` decays in `y`, so the pigeonhole
`δ < η(y)` is a genuine budget constraint there.  The Chebyshev form above removes that constraint.
What it does not remove is the cutoff-uniformity of the head target itself, which is the remaining
(RH-equivalent) half.

## What it does not prove
The rough mean square is unchanged by the conditioning; it is *not* made small. The Bagchi route
needs the tail to **return**, not to be small, and the value of the tail at the fixed point is
still uncontrolled (`log ζ(s) − Σ_{p≤y}p^{−s}` at a single `s` in the strip). This card removes the
conditioning error from that route and leaves the fixed-point error.

## Log
- 2026-10-22 — created at stage 3; module written and compiled; wired into `RHTower`.
