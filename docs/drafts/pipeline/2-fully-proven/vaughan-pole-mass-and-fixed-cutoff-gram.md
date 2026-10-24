# Pole mass and the fixed-cutoff Vaughan Gram

- **ID:** vaughan-pole-mass-and-fixed-cutoff-gram
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Source:** ../1-in-progress/q-i-selective-square-root-band.md
- **Statement:** The pole row has cutoff-independent negative linear mixed density; the fixed-cutoff normalized Vaughan Gram converges to an explicit rank-one matrix.

## Goal

Identify the forced leading terms before seeking a selective bound on the residual energy.
This is a structural result within Q-I, not a fixed zero-free strip.

## Gates

- [x] Dependency-closed paper proof.
- [x] Pole calibration and uniform negative-entry witness checked in Lean.
- [ ] Fixed-cutoff classification and reciprocal-rate equivalence checked in Lean.
- [ ] Transitive-axiom audit and final leaf checks.
- [ ] Umbrella imports and corpus integration complete.

## Paper proof

Write `ρ = Re(1/ζ(1+ε)) > 0`, with `ε>0`. Let `p_i(n)` be the five pieces defined in
`CompletePronicVaughanCalibration`, `I(n)=Σ_i p_i(n)`, and
`G_ij(T)=Σ_(1≤n≤T) p_i(n)p_j(n)/(n(n+1))`. The divisor mean theorem gives `I(n)/n→0`.
The active correction `a(n)` has absolute value at most `1/2`, and the last piece is
`p_4(n)=-ρn-a(n)`, independently of both cutoffs.

For any two sequences with `f(n)/n→a` and `g(n)/n→b`, the summand
`f(n)g(n)/(n(n+1))` tends to `ab`. Cesàro averaging yields its mean `ab`.
Consequently `E_int(T)/T→0`, `G_44(T)/T→ρ²`, and
`(Σ_(j≠4)G_4j(T))/T→-ρ²`. The last sum equals the pronic pairing of `p_4` with
`I-p_4`; it is exactly cutoff-independent. The inequalities
`(ρn+a(n))²≥ρ²n²/2-1/4`, `n/(n+1)≥1/2`, and `Σ1/(n(n+1))≤1` give
`D_T≥G_44(T)≥ρ²T/4-1/4`, uniformly over all cutoffs. Since `D_T+R_mix(T)=E_int(T)`,
the ratio `R_mix(T)/D_T` tends to `-1` uniformly, even for moving cutoffs.
Eventually the four pole cross entries sum to at most `-ρ²T/2`, so at least one is
at most `-ρ²T/8`, uniformly over cutoffs.

For fixed `U,V`, put

`A_U=Σ_(1≤d≤U) μ(d)d^(-ε)/d`, `Z=Σ_(k≥1) k^(-ε)/k`, and

`c=(A_U,A_V,-Z A_U A_V,ρ-A_U-A_V+Z A_U A_V,-ρ)`.

The first two pieces divided by `n` tend to `A_U,A_V`, by the finite floor limits.
For fixed `m=ab>0`, the inner small-small sum is exactly
`m^(-ε) Σ_(k≤floor(n/m)) k^(-ε) floor(floor(n/m)/k)`.
The unsigned divisor mean theorem and `floor(n/m)/n→1/m` give its limit after division
by `n` as `m^(-ε)Z/m`. Finite summation over `a,b` factors into `ZA_UA_V`.
The exact five-piece identity determines the fourth mean. The preceding Cesàro lemma
then gives `G_ij(T)/T→c_i c_j`. In particular `D_T/T→d=Σ_i c_i²>0`, since `c_4=-ρ`.
Every fixed linear superposition has energy divided by `T` tending to the square of
its coefficient pairing with `c`.

The exact relative error is `|1+R_mix/D|=E_int/D` whenever `D>0`. At fixed cutoffs,
`D/T→d>0`, so bounded `E_int` is equivalent to an eventual bound
`|1+R_mix/D|≤C/T`. Extending an eventual energy bound to every horizon uses monotonicity
of the nonnegative pronic partial sums. This equivalence does not prove either side.

## Exact obstruction and positive survivor

- **Refuted estimate:** All four uncentered pole cross entries can be `o(T)` along some
  cutoff schedule. Their sum has strictly negative linear density for every schedule.
- **Positive survivor:** Exact cutoff-independent pole row, uniform finite negative-entry
  witness, explicit fixed-cutoff leading matrix, and the precise reciprocal rate needed
  for bounded residual energy.
- **New insight:** Near-total relative cancellation is already forced by the pole density.
  Only a quantitative bound on its unnormalized error can supply admission information.
- **Scope:** No full-energy divergence, impossibility of Class III estimates in general,
  or negative answer to Q-I is claimed. The broader Q-I card stays in progress.

## Lean status

`TheVaughanDiagonalContainsLinearPoleMass.lean` passed the direct leaf check; its extension
with the uniform negative-entry witness passed the olean-producing check, needed solely by
`TheFixedVaughanGramHasRankOneLeadingTerm.lean`. The latter is written but not checked yet.
The first module's transitive-axiom audit is running. No full or umbrella build was used.

## Log

- 2026-10-25 — Recorded the exact obstruction and dependency-closed positive classification.
