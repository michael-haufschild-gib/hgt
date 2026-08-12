# CMR stage-3: plan for the 4 remaining cards (14/18 promoted)

Promoted: 14 cards — see `mem:constraint-motive-relativity/stage3-progress-2026-08-11`
plus `gauge-collapse-stratified-observation-density-reconstruction`
(`ConstraintMotiveRelativity/GaugeCollapseObservationDensity.lean`, 10 decls, axiom-clean).

Remaining (4): marked-mellin-normalization-exchange-response (NEARLY DONE),
finite-reporter-admission-hyperbolic-reduction-composition,
marked-euler-shell-mellin-gns-ht-recurrence-normalization-wall,
helson-coefficient-fredholm-crossing-response.

## marked-mellin-normalization-exchange-response — ONE SECTION LEFT

`ConstraintMotiveRelativity/MarkedMellinExchange.lean` compiles clean, is wired into the umbrella,
and all 10 listed declarations are axiom-clean (`propext, Classical.choice, Quot.sound`).

ALREADY PROVED:
- `mellinWeight`, `totalMass`, `normWeight`; `coeff_of_normWeight` — `(MER.7)`.
- `totalMass_smul`, `normWeight_smul` — unmarked probability is radial-scale invariant.
- `exchangeSeed` — `(MER.10)`; `hasDerivAt_normWeight` — it IS the coordinatewise derivative of
  normalization along `c + ε h` (linearity of `totalMass` along the path is the explicit
  hypothesis `hlin`, which absolute convergence supplies).
- `tsum_normWeight` (mass one), `tsum_exchangeSeed` (mass zero), `exchangeSeed_eq_zero_iff` —
  `(MER.11)` kernel is exactly the radial line.
- `logAtom`, `atomChar`, `phaseCorr`, `phaseResponse` — `(MER.6)`, `(MER.13)`.
- `phaseCorr_smul` — `(MER.19)`; `phaseResponse_smul` — `(MER.20)` (`λ⁻¹` scaling);
  `phaseResponse_atom` — `(MER.15)`.  Together these are Countertheorem 6.1's content.
- `atomic_density` — Theorem 1.1 (hom exists ↔ coordinatewise domination; hom-sets are
  subsingletons in a poset so uniqueness is automatic); `coeff_eq_sSup` — the coordinate is the
  supremum of the rational atomic probes below it.

STILL TO DO (only §5, then the card can be promoted):
- `(MER.14)` covariance form: with `h n = c n * r n` for a bounded real score `r`,
  `phaseResponse σ c h t = E_{P_c}(r · χ_t) − E_{P_c}(r) · E_{P_c}(χ_t)`.  Pure algebra on the
  tsum once `E_{P_c}(f) = ∑' n, normWeight σ c n * f n` is defined.
- `(MER.17)` Fisher bound `|DC_c[cr](t)|² ≤ Var_{P_c}(r)(1 − |C_c(t)|²) ≤ Var_{P_c}(r)`:
  Cauchy–Schwarz for the `P_c`-inner product on tsums (`inner_mul_le_norm_mul_norm` on the
  weighted `ℓ²`, or `Finset.inner_mul_le_norm_mul_norm` plus a limit).  Also
  `Var^H_{P_c}(χ_t) = 1 − |C_c(t)|²`, which is one expansion of `E|χ|² = 1`.
- `(MER.18)`/`(MER.18a)` time jets: `∂_t^k C_c(t) = (−i)^k E_{P_c}(x^k χ_t)` by differentiating
  under the tsum (dominated by the `(MER.2)` log moments).
- §7 is a specialization remark, no new theorem.

## gauge-collapse — DONE.  Trick worth remembering

`haveI : (φd.functor ⋙ Fu).IsEquivalence := Functor.isEquivalence_of_iso η.symm` then
`Functor.isEquivalence_of_comp_left φd.functor Fu` — avoids all whiskering/naturality.
Theorem 4.1 is literally `Functor.isDense_iff_fullyFaithful_restrictedULiftYoneda` with
`Presheaf.restrictedULiftYoneda` (`Mathlib/CategoryTheory/Limits/Presheaf.lean`).

## helson-coefficient-fredholm-crossing-response — scoped plan

Corpus assets: `HTGeometry/SchattenOneBanach.lean` (`SchattenOneOperator`, `rankOneSchattenOne`,
`norm_rankOneSchattenOne`, `memSchattenClass_one_and_traceNorm_le_of_tendsto`).
Finite-matrix eigenbranch layer: `ParametricSpectralBranch.lean`, `SimpleSpectrumAnalyticBranch.lean`,
`AffineEigenbranchSecondOrderLaw.lean`, `AffineSimpleZeroMotion.lean`, `Bottcher/AlgebraicBranch.lean`.

Write first (all provable now): `d n = n.divisors.card`; `ℓ¹_d`; `∑_{j,k}|a_{jk}| = ∑_n d n |a_n|`;
`K_a` as an absolutely convergent rank-one series in `SchattenOneOperator` with `(HFR.3)`;
`(HFR.4)`; self-adjointness for real `a`; Lemma 3.1 `|W_u(n)| ≤ ‖u‖²`; `W_u(m²) = |u_m|² > 0` for
`m` least with `u_m ≠ 0`; `(HFR.9a)` continuity; `(HFR.11)`; `p(λc) = p(c)`; §6 countermodel 1
(`a₁=0, a₂=1` ⇒ `[[0,1],[1,0]]`, eigenvalues `±1`).

NEW infrastructure for §4: Riesz projection of a trace-class-continuous family, its `C¹` rank-one
dependence, `(HFR.7)`/`(HFR.9)`, the Banach implicit-function-theorem hypersurface, and the
Fredholm determinant `det_F(I − τ⁻¹K_a)` with `Δ_τ(a)=0 ↔ τ ∈ spec K_a`.  mathlib has only
`Analysis/Normed/Operator/Compact/FredholmAlternative.lean`.

## Practical notes

- `lake build <module>` for the audit; `lake env lean <file>` while iterating; kill leftovers with
  `pkill -f "lake env lean"` (exit 137 = OOM from too many parallel leans).
- Long builds exceed the 600 s Bash cap — use `run_in_background` and poll the output file.
- The `HTGeometry` umbrella builds only after the repair in `HTGeometry/UniformIteratedDerivLimit.lean`.
