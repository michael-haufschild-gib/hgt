# Nine-field research programme: 250 significant contributions

- **ID:** nine-fields-250-20261023
- **Stage:** 1-in-progress
- **Type:** PROGRAMME LEDGER
- **Source:** user goal of 2026-10-23 (APT, BiScale, THIM, BVI, ACT, SRT, AIP, ACCE, SSIC).
- **Statement:** 250 significant, unconditional, Lean-audited contributions to the nine programmes.

## Rules in force

All nine READMEs read in full; they are read-only. No hgtl7 skill. Corpus search tool before
Mathlib and before rg/grep. Unconditional Lean only; one foreground `lake --old env lean` at a time;
no full or umbrella builds; wire finished leaves into their umbrella; no heartbeat raises; no
computations. Not counted: constant improvements, no-gos alone, renamings, proof lemmas.
Missing dependency oleans are built one at a time with `lake --old env lean -o` (CLAUDE.md rule 4).

## Accepted contributions: 1 / 250

1. THIM — the horizon limit commutes with the receiver exactly from half damping (candidate 1).

## Candidate 1 (THIM): the horizon limit commutes with the receiver exactly from half damping

**Open problem (THIM README §5, the parity pair):** whether signed rows can be uniformly bounded
while their pointwise limit is unpaid, or conversely.

**Theorem (paper proof complete).** On `𝒞(1, ε)`, `ε ≥ 0`: "rows uniformly paid ⇔ weight paid" holds
for every weight iff `ε ≥ 1/2`.
1. Every weight: uniformly bounded dyadic rows ⇒ paid (Fatou in the weight at fixed cutoff).
2. `ε > 1/2`: weight and all rows paid by one constant. `ε = 1/2`: row energy `≤ 2E + 17K²`
   (drift `Nτ_N² ≤ 4K²`, sawtooth `≤ 3K√N`).
3. `0 ≤ ε < 1/2`: explicit paid `c ∈ 𝒞(1, ε)` with unbounded row receivers (lacunary windowed
   dipoles `N = 2^{Lt}`, `w = 2^{Mt}`, cutoff `2^{Qt}`).

**Lean:** `TransHorizonIncidenceMechanics/TheHorizonLimitCommutesWithTheReceiverExactlyFromHalfDamping.lean`
(`horizonLimit_commutes_with_receiver_iff`). Status: compiled, axioms `propext`, `Classical.choice`,
`Quot.sound`; wired into the THIM umbrella.

## Candidate 2 (THIM): a paid receiver continues the Dirichlet series across its abscissa

**Theorem (paper proof complete).** If `Σ|c(d)|d^{-θ} < ∞` for `θ > a` and the receiver of `c` is
paid, then `Φ(s) = Σ_n A(n)(n^{-s} − (n+1)^{-s})` is holomorphic on `Re s > 1/2` and equals
`ζ(s)(C(s) − m)` on `(a, 1)`. For `1/2 < a < 1`: `C` is Lipschitz at `a`, and any exact power order
`|C(a+u) − L| ≍ u^α`, `α > 0`, is a positive integer.

**Application (quantization).** Below half damping a completely multiplicative `±1` pattern whose
flipped primes have Dirichlet density `ρ` is unpaid unless `ρ ∈ {1/2, 1}` (`Σ f(n)n^{-w} ≍
(w−1)^{2ρ−1}`). Not covered by the pole law, which gives only boundedness (`ρ ≥ 1/2`).

**Lean:** `TransHorizonIncidenceMechanics/APaidReceiverContinuesTheDirichletSeriesAcrossItsAbscissa.lean`
(`exists_holomorphic_continuation`, `exists_abs_dirichletSeries_sub_le_mul`,
`exists_nat_eq_of_rpow_bounds_at_abscissa`, `not_receiverBounded_of_flippedDensity`). Status:
written, not yet compiled.

## Candidate 3 (THIM): the universal hyperplane on the whole critical Wiener algebra

**Theorem (paper proof complete).** `0 < ε < 1/2`, `Σ_j |k(j)| j^{-1/2} < ∞`: `k ⋆ d^{-ε}` is paid
iff `K(1 − ε) = 0`. Finite kernels were known (`receiverBounded_dirichletConv_unit_iff`).
Sufficiency: `k = Σ_j k(j)(δ_j − j^{-(1−ε)}δ_1)`; each pole-free dilation `b_j` has `E(b_j) ≤ C/j`
(below `j` by the convolution law and `|A_q(n)| ≤ Cn^{1−ε}`; beyond `j` by the sharp hyperbola bound
`|A_c(n)| ≤ Σ_{d≤D}|c(d)| + 4BnD^{-1-ε}` at `D = ⌊√(jn)⌋`); Minkowski over truncations and continuity
of the energy at fixed cutoff. No divisor-problem asymptotic is needed.

**Lean:** `TransHorizonIncidenceMechanics/CriticalWienerPerturbationsOfTheSmoothPowerAreDecidedAtThePole.lean`
(`receiverBounded_dirichletConv_unit_iff_critical`). Status: written, compile pending (dependency
oleans being rebuilt by other agents).

## Candidate 4 (THIM): the hyperplane law on the algebra stops exactly at half damping

**Claim (paper proof sketched).** At `ε = 1/2`: (i) if `Σ_j |k(j)| j^{-1/2} (1 + log j)^{1/2} < ∞`,
then `k ⋆ d^{-1/2}` is paid iff `K(1/2) = 0` (`E(b_j) = O((1 + log j)/j)`); (ii) the kernel
`k = Σ_r c_r(δ_{j_r} − j_r^{-1/2}δ_1)`, `j_r = 4^{2^r}`, `c_r = j_r^{1/2}/r²`, lies in the critical
Wiener algebra with `K(1/2) = 0`, yet `k ⋆ d^{-1/2}` is unpaid: on `[j_R, j_{R+1})` the prefix carries
`−A_q(n) Σ_{r>R} r^{-2} ≥ c√n/R` (drift lower bound for `A_q`), of energy `≍ 2^R/R²`, while the
dilations `r ≤ R` are paid uniformly and the mean term is `O(Σ_R R^{-2})`.
So the hyperplane law on the full algebra holds for every `ε < 1/2` and fails at `ε = 1/2`.

## Checked and not pursued

- Pole law for kernels absolutely convergent at the abscissa: done by another agent
  (`APaidReceiverBoundsTheDirichletSeriesUpToItsAbscissa.lean`).
- Exact Plancherel law `E(c) = lim (1/2π)∫|ζ(σ+it)(C(σ+it)−m)|²/|σ+it|² dt`: the Báez-Duarte
  transform in receiver language; kept only as motivation.
