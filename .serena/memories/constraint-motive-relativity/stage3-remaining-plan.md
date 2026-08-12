# CMR stage-3: 17/18 promoted; the Helson card is partially built

## State

17 of the 18 `constraint-motive-relativity` cards are formalized unconditionally and promoted to
`docs/drafts/pipeline/3-formalized/constraint-motive-relativity/`, each with a
`<id>-formalized.md` companion.  Only `helson-coefficient-fredholm-crossing-response-law` remains in
`2-fully-proven`.

## What is already Lean-proved for the Helson card

`formal/GaloisForLFunctions/HTGeometry/ConstraintMotiveRelativity/HelsonDivisorResponse.lean`
(compiles clean, wired into `GaloisForLFunctions.HTGeometry`):

- `divisorWeight`, `divisorWeight_eq_card_divisors` — `(HFR.1)`'s weight `d(n)`;
- `HelsonSummable` — the space `ℓ¹_d`;
- `helsonEntry`, `helsonEntry_one_left` (`(HFR.4)` at entry level),
  `helsonEntry_conj_symm` (Theorem 2.1 (3)), `sum_norm_helsonEntry_fibre` (`(HFR.5)`'s fibre sum);
- `divisorConv` (`(HFR.6)`), `tsum_normSq_lpTwo`, `summable_normSq_lpTwo`,
  `sum_divisors_normSq_le`, **`norm_divisorConv_le`** (Lemma 3.1),
  **`divisorConv_least_sq`** (Theorem 4.1 (4): `W_u(m²) = |u_m|² ≠ 0` at the least active index);
- `mellinWeightedNorm`, `mellinMass`, `mellinWeightedNorm_eq`, `norm_mellinMass_le` (`(HFR.10a)`),
  `mellinNormalized`, `mellinNormalized_smul` (Corollary 5.1's projective invariance),
  `mellinExchangeSeed`, **`hasDerivAt_mellinNormalized`** (`(HFR.11)`);
- `helson_block_not_posSemidef` — §6 countermodel 1.

## What is still missing

1. **§2's trace-class realization.**  Assemble `K_a` as an absolutely trace-norm convergent series
   of rank ones and prove `(HFR.3)` `‖K_a‖₁ ≤ ∑ d(n)|a_n|`.  Reuse
   `HTGeometry/SchattenOneBanach.lean` (`SchattenOneOperator`, `rankOneSchattenOne`,
   `norm_rankOneSchattenOne`, `memSchattenClass_one_and_traceNorm_le_of_tendsto`).  The reindexing
   `∑_{j,k} |a_{jk}| = ∑_n d(n)|a_n|` should go through `Nat.divisorsAntidiagonal` and
   `Equiv.sigmaFiberEquiv` (the fibre identity `sum_norm_helsonEntry_fibre` is already proved).
2. **§3 Theorem 3.2 and §4 Theorem 4.1.**  These need genuinely new analytic infrastructure that
   neither mathlib nor the corpus has:
   - the Riesz projection `P(b) = (2πi)⁻¹ ∮ (z - K_b)⁻¹ dz` of a trace-class-continuous family,
     its rank-one-ness near a simple isolated eigenvalue, and its `C¹` dependence;
   - `μ(b) = tr(K_b P(b))` and `Dμ_a[h] = ⟨u, K_h u⟩` — this is `(HFR.7)`/`(HFR.9)`;
   - the Banach implicit-function theorem giving the `C¹` codimension-one wall hypersurface;
   - the Fredholm determinant `det_F(I − τ⁻¹K_a)` and `Δ_τ(a) = 0 ↔ τ ∈ spec K_a`.
     Mathlib has only `Analysis/Normed/Operator/Compact/FredholmAlternative.lean`.
   The card's own §9 suggests isolating finite-rank truncations of `(HFR.2)`–`(HFR.9)` first; the
   corpus finite-matrix eigenbranch layer (`HTGeometry/ParametricSpectralBranch.lean`,
   `SimpleSpectrumAnalyticBranch.lean`, `AffineEigenbranchSecondOrderLaw.lean`,
   `SimpleSpectrumEigenline.lean`) is the natural base for the truncated statements.
3. Corollary 5.1's `(HFR.12)` then follows by composing `hasDerivAt_mellinNormalized` with the
   eigenvalue derivative.

Do NOT promote the card until §§2–4 are complete; the companion file has not been written yet.

## Practical notes

- `lake build <module>` for the audit; `lake env lean <file>` while iterating; `pkill -f "lake env
  lean"` afterwards.  Full-umbrella builds exceed the 600 s Bash cap — run in background.
- Namespace collisions are real (`hyperbolicForm` already existed in `PrimeAugmentationSymplectic`).
- `↥S ⧸ T` needs `T : Submodule R ↥S` (`Submodule.comap S.subtype T`).
- `Module.evalEquiv`/`Module.IsReflexive` can fail instance search on `↥(Submodule …)` of a
  `→L[ℂ]` space; route through `Submodule.quotDualCoannihilatorToDual` and `Module.Finite.equiv`.
- `convert` on `HasDerivAt` hits a `Complex.addCommGroup` vs `instCommCStarAlgebraComplex` diamond;
  use `HasDerivAt.congr_deriv` instead, with `Pi.inv_apply` in the simp set.
- Recurrence/compact-orbit statements come free from
  `ConstraintMotiveRelativity/PortRecurrenceJets.lean`.
