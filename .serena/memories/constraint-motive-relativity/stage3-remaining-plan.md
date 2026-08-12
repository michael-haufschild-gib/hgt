# CMR stage-3: plan for the 4 remaining cards (14/18 promoted)

Promoted: 14 — see `mem:constraint-motive-relativity/stage3-progress-2026-08-11` plus
`gauge-collapse-stratified-observation-density-reconstruction`
(`ConstraintMotiveRelativity/GaugeCollapseObservationDensity.lean`, 10 decls, axiom-clean).

## marked-mellin-normalization-exchange-response — TWO ITEMS LEFT

`ConstraintMotiveRelativity/MarkedMellinExchange.lean`: compiles clean, wired into the umbrella,
every declaration axiom-clean.

PROVED: `mellinWeight`, `totalMass`, `normWeight`; `coeff_of_normWeight` `(MER.7)`;
`totalMass_smul`, `normWeight_smul`; `exchangeSeed` `(MER.10)`; `hasDerivAt_normWeight` (the seed
IS the coordinatewise derivative along `c + εh`); `tsum_normWeight`, `tsum_exchangeSeed` (mass
zero); `exchangeSeed_eq_zero_iff` `(MER.11)`; `logAtom`, `atomChar`, `phaseCorr`, `phaseResponse`
`(MER.6)`/`(MER.13)`; `phaseCorr_smul` `(MER.19)`, `phaseResponse_smul` `(MER.20)`,
`phaseResponse_atom` `(MER.15)` — i.e. all of Countertheorem 6.1; `atomic_density` and
`coeff_eq_sSup` — Theorem 1.1; `expect`, `expect_const`, `phaseCorr_eq_expect`;
`phaseResponse_covariance` `(MER.14)`; `variance`, `hermVarianceChar`, `atomChar_mul_conj`,
`hermVarianceChar_eq` (`Var^H(χ) = 1 − |C|²`).

REMAINING (then promote):
1. `(MER.17)` `|DC_c[cr](t)|² ≤ Var_{P_c}(r) · (1 − |C_c(t)|²)`.  This is Cauchy–Schwarz for the
   `P_c`-weighted inner product on the *centered* vectors `r − E r` and `χ_t − C_c(t)`.
   Cheapest route in this tree: mimic `WeightedPortCapacity.portValue_normSq_le` — bound the
   partial sums with `Finset.sum_mul_sq_le_sq_mul_sq`, then pass to the tsum supremum.
2. `(MER.18)`/`(MER.18a)` time jets `∂_t^k C_c(t) = (−i)^k E_{P_c}(x^k χ_t)`: differentiate under
   the tsum.  The same uniform-truncation technique as
   `PortRecurrenceJets.hasDerivAt_portOrbit` applies verbatim (`tendstoUniformly` on `Finset ℕ`
   plus `hasDerivAt_of_tendstoUniformlyOn`); the dominating summable bound is `(MER.2)`'s log
   moments.
§7 is a specialization remark with no new theorem.

## helson-coefficient-fredholm-crossing-response

Corpus assets: `HTGeometry/SchattenOneBanach.lean` (`SchattenOneOperator`, `rankOneSchattenOne`,
`norm_rankOneSchattenOne`, `memSchattenClass_one_and_traceNorm_le_of_tendsto`).
Finite-matrix eigenbranch layer: `ParametricSpectralBranch.lean`, `SimpleSpectrumAnalyticBranch.lean`,
`AffineEigenbranchSecondOrderLaw.lean`, `AffineSimpleZeroMotion.lean`, `Bottcher/AlgebraicBranch.lean`.

Provable now: `d n = n.divisors.card`; `ℓ¹_d`; `∑_{j,k}|a_{jk}| = ∑_n d n |a_n|`; `K_a` as an
absolutely convergent rank-one series in `SchattenOneOperator` with `(HFR.3)`; `(HFR.4)`;
self-adjointness for real `a`; Lemma 3.1 `|W_u(n)| ≤ ‖u‖²`; `W_u(m²) = |u_m|² > 0` for `m` least
with `u_m ≠ 0`; `(HFR.9a)` continuity; `(HFR.11)`; `p(λc) = p(c)`; §6 countermodel 1.

NEW infrastructure for §4: Riesz projection of a trace-class-continuous family and its `C¹`
rank-one dependence; `(HFR.7)`/`(HFR.9)`; the Banach implicit-function-theorem hypersurface; the
Fredholm determinant `det_F(I − τ⁻¹K_a)` with `Δ_τ(a)=0 ↔ τ ∈ spec K_a`.  mathlib has only
`Analysis/Normed/Operator/Compact/FredholmAlternative.lean`.

## finite-reporter-admission-hyperbolic-reduction-composition, marked-euler-shell-…-normalization-wall

Not started.  Read the cards first; both are long (412 / 423 lines) with §-level theorem headers
listed by `grep -n "^### \|^## \|boxed"`.

## Practical notes

- `lake build <module>` for the audit; `lake env lean <file>` while iterating; `pkill -f "lake env
  lean"` to clean up (exit 137 = OOM from too many parallel leans).
- Long builds exceed the 600 s Bash cap — use `run_in_background` and poll the output file.
- The `HTGeometry` umbrella builds only after the repair in `HTGeometry/UniformIteratedDerivLimit.lean`.
- Recurring trap: a trailing `ring` after `field_simp` usually errors with "No goals"; drop it.
