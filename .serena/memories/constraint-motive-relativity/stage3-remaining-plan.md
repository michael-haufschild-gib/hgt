# CMR stage-3: plan for the 5 remaining cards (as of 13/18 done)

Done: see `mem:constraint-motive-relativity/stage3-progress-2026-08-11` (13 cards, all promoted).
Remaining: finite-reporter-admission-hyperbolic-reduction-composition,
gauge-collapse-stratified-observation-density-reconstruction,
helson-coefficient-fredholm-crossing-response,
marked-euler-shell-mellin-gns-ht-recurrence-normalization-wall,
marked-mellin-normalization-exchange-response.

## gauge-collapse-stratified-observation-density-reconstruction — START HERE, nearly done

Pure category theory; mathlib has everything.  A draft module was written and then removed because
one naturality square was still open; rewrite it as
`ConstraintMotiveRelativity/GaugeCollapseObservationDensity.lean` with:

- **Thm 2.1** `isEquivalence_of_gauge (φd : C ≌ Fd) (φe : C ≌ Fe) (Fu : Fd ⥤ Fe)`
  `(η : φd.functor ⋙ Fu ≅ φe.functor) : Fu.IsEquivalence`.
  Route: build `hiso : (φd.symm.trans φe).functor ≅ Fu` by
  `NatIso.ofComponents (fun X => (η.app (φd.inverse.obj X)).symm ≪≫ Fu.mapIso (φd.counitIso.app X))`
  then `Functor.isEquivalence_of_iso hiso`.
  THE ONLY OPEN STEP is that `NatIso.ofComponents` naturality square.  What failed: `dsimp`/
  `simp only [Equivalence.trans_functor, Equivalence.symm_functor, Functor.comp_map, Iso.trans_hom,
  Iso.symm_hom, Functor.mapIso_hom]` did not unfold `(φd.symm.trans φe).functor.map f`.
  Next things to try: `aesop_cat` (omit the naturality argument entirely and let the autoParam
  fire); or `Equivalence.trans_functor`/`Equivalence.symm_functor` via `erw`; or avoid `symm.trans`
  and state `hiso : φd.inverse ⋙ φe.functor ≅ Fu` directly, then
  `Functor.isEquivalence_of_iso hiso` with `inferInstance` for `(φd.inverse ⋙ φe.functor)`.
- **Thm 2.1 (2),(3)** `obj_iso_of_gauge` (must be a `noncomputable def`, it returns an `Iso`) via
  `Functor.FullyFaithful.ofFullyFaithful Fu |>.preimageIso`, and `isIso_of_gauge` via
  `Functor.ReflectsIsomorphisms.reflects`.  `no_gauge_of_not_isEquivalence` is the contrapositive.
- **Cor 2.2 `(GOD.7)`** `localization_identifies (L) (f : a ⟶ b) (g : d ⟶ c) (hf hg : IsIso …)`
  `(h : L.obj b ≅ L.obj c) : L.obj a ≅ L.obj d := (asIso (L.map f)).trans (h.trans (asIso (L.map g)).symm)`.
  (Compiles.)
- **Thm 4.1** is literally
  `CategoryTheory.Functor.isDense_iff_fullyFaithful_restrictedULiftYoneda`
  (`Mathlib/CategoryTheory/Functor/KanExtension/Dense.lean:159`, needs `[J.Full]`), with
  `Presheaf.restrictedULiftYoneda` from `Mathlib/CategoryTheory/Limits/Presheaf.lean:78`.
- **Thm 4.2** from `hdesc : N ≅ L ⋙ B` and full faithfulness of `N`:
  `faithful_of_nerve_descends`, `reflectsIso_of_nerve_descends`
  (rewrite `N.map f = hdesc.hom.app X ≫ (L ⋙ B).map f ≫ hdesc.inv.app Y` using
  `hdesc.hom.naturality f` and `hdesc.hom_inv_id_app`, then `infer_instance`),
  `objIso_of_nerve_descends` (a `noncomputable def`), and
  `nerveDescendsSerial : (N ≅ (L ⋙ M) ⋙ B) → N ≅ L ⋙ (M ⋙ B) := (·.trans (Functor.associator …))`.
  All of these compiled except the ones blocked by Thm 2.1's naturality.

## helson-coefficient-fredholm-crossing-response — scoped plan

Reusable corpus assets:
- `HTGeometry/SchattenOneBanach.lean` — `SchattenOneOperator H`, `rankOneSchattenOne x y`,
  `norm_rankOneSchattenOne`, `memSchattenClass_one_and_traceNorm_le_of_tendsto`,
  `schattenOneCoeCLM`.  Carrier for `K_a = ∑_{j,k} a_{jk} E_{jk}`.
- Finite-matrix simple-eigenvalue branch layer: `ParametricSpectralBranch.lean`,
  `SimpleSpectrumAnalyticBranch.lean`, `AffineEigenbranchSecondOrderLaw.lean`,
  `AffineSimpleZeroMotion.lean`, `Bottcher/AlgebraicBranch.lean`.
  All FINITE-DIMENSIONAL; the trace-class Riesz-projection version is in neither the tree nor
  mathlib (no Schatten class, no Fredholm determinant, no analytic perturbation of compact
  self-adjoint operators).

Immediately provable, write first:
1. `d n = n.divisors.card`; `ℓ¹_d`; identity `∑_{j,k} |a_{jk}| = ∑_n d n |a_n|`.
2. `K_a` in `SchattenOneOperator (lp (fun _ : ℕ+ => ℂ) 2)` as an absolutely convergent rank-one
   series; `(HFR.3)` `‖K_a‖₁ ≤ ∑ d n |a_n|`.
3. `(HFR.4)` `a_n = ⟪e_1, K_a e_n⟫`; self-adjointness for real `a`.
4. Lemma 3.1 `|W_u(n)| ≤ ‖u‖²`; `W_u(m²) = |u_m|² > 0` for `m` least with `u_m ≠ 0`
   ⇒ `(HFR.9a)` covector nonzero; continuity `|Γ(h)| ≤ ∑|h_n| ≤ ‖h‖_{1,d}`.
5. `(HFR.11)` derivative of the Mellin normalization; `p(λc) = p(c)`.
6. §6 countermodel 1: `a₁ = 0, a₂ = 1` gives `[[0,1],[1,0]]`, eigenvalues `±1`.

Needs NEW analytic infrastructure: Riesz projection for a trace-class-continuous family and its
`C¹` rank-one dependence, `(HFR.7)`/`(HFR.9)`, the Banach implicit-function theorem hypersurface,
and the Fredholm determinant `det_F(I − τ⁻¹K_a)` with `Δ_τ(a) = 0 ↔ τ ∈ spec K_a`.
mathlib has only `Analysis/Normed/Operator/Compact/FredholmAlternative.lean`.

## Practical notes

- `lake build <module>` for the audit; `lake env lean <file>` while iterating; kill leftovers with
  `pkill -f "lake env lean"` (exit 137 = OOM from too many parallel leans).
- `field_simp` sometimes emits a bare "Try this: ring_nf …" note with no source position; it is
  informational, not a warning, and `lake build` still succeeds.
- The `HTGeometry` umbrella builds only after the repair in `HTGeometry/UniformIteratedDerivLimit.lean`.
