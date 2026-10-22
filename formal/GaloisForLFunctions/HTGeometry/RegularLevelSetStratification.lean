import GaloisForLFunctions.HTGeometry.ClassicalStratifiedParametricAvoidance
import Mathlib.Data.Fintype.Pi

/-!
# Regular zero sets and finite regular stratifications

The set of surjective continuous linear maps `X → Y` is open when `Y` is finite-dimensional
(a right inverse stays invertible after composition under small perturbation, by continuity of the
determinant). Consequently the zero set of a smooth map `g : Y → ℝᵐ` (or into any
finite-dimensional `Z`) whose derivative is surjective at every zero is locally a smooth regular
level set of codimension at least `c ≤ m`, also after intersecting with an open set. The module
then provides constructors for `FiniteRegularStratification`: from finitely many pairwise disjoint
regular strata, from one regular set, and by adjoining a disjoint regular stratum.

## Main results

- `isOpen_surjectiveContinuousLinearMapLocus`: surjectivity is an open condition on
  `X →L[ℝ] Y` for finite-dimensional `Y`.
- `isLocalRegularLevelSetOfCodimAtLeast_zeroSet`: the zero set of a smooth `g : Y → ℝᵐ` that is a
  submersion along its zeros is a local regular level set of codimension at least `c ≤ m`.
- `isLocalRegularLevelSetOfCodimAtLeast_zeroSet_finiteDimensional`: the same for targets any
  finite-dimensional `Z`, with `c ≤ dim Z`; `_inter_isOpen` variants restrict to an open set.
- `IsLocalRegularLevelSetOfCodimAtLeast.inter_isOpen`: local regularity is preserved by
  intersecting with an open set.
- `finiteRegularStratification_of_pairwise`, `finiteRegularStratification_of_regular`,
  `FiniteRegularStratification.cons`: constructors for finite regular stratifications.

## Hypotheses

Unconditional. The zero-set theorems assume `g` is `C^∞` and that its Fréchet derivative is
surjective at each zero (in `O` for the open variants), with `c` at most the target dimension.
The stratification constructors take the regularity predicate `IsLocalRegularLevelSetOfCodimAtLeast`
of each stratum and the disjointness of strata as inputs.
-/

namespace GaloisForLFunctions.HTGeometry

open Set Filter Topology

noncomputable section

/-- For finite-dimensional `Y`, the surjective continuous linear maps `X → Y` form an open set. -/
theorem isOpen_surjectiveContinuousLinearMapLocus
    {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y] :
    IsOpen {L : X →L[ℝ] Y | Function.Surjective L} := by
  rw [isOpen_iff_mem_nhds]
  intro L hL
  have hrange : L.toLinearMap.range = ⊤ := LinearMap.range_eq_top.mpr hL
  obtain ⟨s, hs⟩ := L.toLinearMap.exists_rightInverse_of_surjective hrange
  let sc : Y →L[ℝ] X := LinearMap.toContinuousLinearMap s
  let g : (X →L[ℝ] Y) → (Y →L[ℝ] Y) := fun L' => L'.comp sc
  have hg : Continuous g := continuous_id.clm_comp continuous_const
  have hgL : g L = ContinuousLinearMap.id ℝ Y := by
    apply ContinuousLinearMap.ext
    intro y
    exact LinearMap.congr_fun hs y
  have hdet : (g L).det ≠ 0 := by
    rw [hgL]
    simp [ContinuousLinearMap.det, LinearMap.det_id]
  have hevent : ∀ᶠ L' in 𝓝 L, (g L').det ≠ 0 :=
    (ContinuousLinearMap.continuous_det.comp hg).continuousAt.eventually_ne hdet
  filter_upwards [hevent] with L' hdet'
  intro y
  let e : Y ≃L[ℝ] Y := (g L').toContinuousLinearEquivOfDetNeZero hdet'
  refine ⟨sc (e.symm y), ?_⟩
  change g L' (e.symm y) = y
  exact e.apply_symm_apply y

/-- If `g : Y → ℝᵐ` is `C^∞` with surjective derivative at every zero and `c ≤ m`, then the zero
set of `g` is locally a regular level set of codimension at least `c`. -/
theorem isLocalRegularLevelSetOfCodimAtLeast_zeroSet
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {m c : ℕ} (g : Y → (Fin m → ℝ)) (hcm : c ≤ m)
    (hg : ContDiff ℝ ⊤ g)
    (hsurj : ∀ x, g x = 0 → Function.Surjective (fderiv ℝ g x)) :
    IsLocalRegularLevelSetOfCodimAtLeast {x | g x = 0} c := by
  intro y hy
  let U : Set Y := {x | Function.Surjective (fderiv ℝ g x)}
  have hU : IsOpen U :=
    isOpen_surjectiveContinuousLinearMapLocus.preimage
      (hg.continuous_fderiv (by simp))
  have hyU : y ∈ U := hsurj y hy
  refine ⟨m, hcm, U, hU, hyU, g, hg.contDiffOn.mono (subset_univ U), ?_, ?_⟩
  · intro x _
    rfl
  · intro x hx
    simpa only [fderivWithin_of_isOpen hU hx] using! hx

/-- If `g : Y → ℝᵐ` is `C^∞` with surjective derivative at every zero in the open set `O` and
`c ≤ m`, then `{g = 0} ∩ O` is locally a regular level set of codimension at least `c`. -/
theorem isLocalRegularLevelSetOfCodimAtLeast_zeroSet_inter_isOpen
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {m c : ℕ} (g : Y → (Fin m → ℝ)) (hcm : c ≤ m)
    (hg : ContDiff ℝ ⊤ g) {O : Set Y} (hO : IsOpen O)
    (hsurj : ∀ x, g x = 0 → x ∈ O → Function.Surjective (fderiv ℝ g x)) :
    IsLocalRegularLevelSetOfCodimAtLeast ({x | g x = 0} ∩ O) c := by
  intro y hy
  let U : Set Y := O ∩ {x | Function.Surjective (fderiv ℝ g x)}
  have hU : IsOpen U := hO.inter
    (isOpen_surjectiveContinuousLinearMapLocus.preimage
      (hg.continuous_fderiv (by simp)))
  have hyU : y ∈ U := ⟨hy.2, hsurj y hy.1 hy.2⟩
  refine ⟨m, hcm, U, hU, hyU, g, hg.contDiffOn.mono (subset_univ U), ?_, ?_⟩
  · intro x hx
    exact and_iff_left hx.1
  · intro x hx
    simpa only [fderivWithin_of_isOpen hU hx] using! hx.2

/-- Finite-dimensional target version: for `C^∞` `g : Y → Z` submersive along its zeros and
`c ≤ dim Z`, the zero set is a local regular level set of codimension at least `c`. -/
theorem isLocalRegularLevelSetOfCodimAtLeast_zeroSet_finiteDimensional
    {Y Z : Type*}
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
    {c : ℕ} (g : Y → Z) (hc : c ≤ Module.finrank ℝ Z)
    (hg : ContDiff ℝ ⊤ g)
    (hsurj : ∀ x, g x = 0 → Function.Surjective (fderiv ℝ g x)) :
    IsLocalRegularLevelSetOfCodimAtLeast {x | g x = 0} c := by
  let e : Z ≃L[ℝ] (Fin (Module.finrank ℝ Z) → ℝ) :=
    ContinuousLinearEquiv.ofFinrankEq (Module.finrank_fin_fun ℝ).symm
  let phi : Y → (Fin (Module.finrank ℝ Z) → ℝ) := fun x => e (g x)
  have hphi : ContDiff ℝ ⊤ phi := e.contDiff.comp hg
  have hphiSurj : ∀ x, phi x = 0 → Function.Surjective (fderiv ℝ phi x) := by
    intro x hx
    have hgzero : g x = 0 := e.injective (by simpa [phi] using hx)
    have hgSurj := hsurj x hgzero
    have hderiv : fderiv ℝ phi x =
        e.toContinuousLinearMap.comp (fderiv ℝ g x) := by
      change fderiv ℝ (fun y => e (g y)) x = _
      rw [fderiv_fun_comp x e.differentiableAt
        (hg.differentiable (by simp)).differentiableAt]
      have he : fderiv ℝ (e : Z → (Fin (Module.finrank ℝ Z) → ℝ)) (g x) =
          e.toContinuousLinearMap := e.hasFDerivAt.fderiv
      rw [he]
    rw [hderiv]
    exact e.surjective.comp hgSurj
  have hreg := isLocalRegularLevelSetOfCodimAtLeast_zeroSet phi hc hphi hphiSurj
  convert hreg using 1
  ext x
  simp [phi]

/-- Finite-dimensional target version on an open set `O`: `{g = 0} ∩ O` is a local regular level
set of codimension at least `c ≤ dim Z` when `g` is submersive at zeros in `O`. -/
theorem isLocalRegularLevelSetOfCodimAtLeast_zeroSet_inter_isOpen_finiteDimensional
    {Y Z : Type*}
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
    {c : ℕ} (g : Y → Z) (hc : c ≤ Module.finrank ℝ Z)
    (hg : ContDiff ℝ ⊤ g) {O : Set Y} (hO : IsOpen O)
    (hsurj : ∀ x, g x = 0 → x ∈ O → Function.Surjective (fderiv ℝ g x)) :
    IsLocalRegularLevelSetOfCodimAtLeast ({x | g x = 0} ∩ O) c := by
  let e : Z ≃L[ℝ] (Fin (Module.finrank ℝ Z) → ℝ) :=
    ContinuousLinearEquiv.ofFinrankEq (Module.finrank_fin_fun ℝ).symm
  let phi : Y → (Fin (Module.finrank ℝ Z) → ℝ) := fun x => e (g x)
  have hphi : ContDiff ℝ ⊤ phi := e.contDiff.comp hg
  have hphiSurj : ∀ x, phi x = 0 → x ∈ O →
      Function.Surjective (fderiv ℝ phi x) := by
    intro x hx hxO
    have hgzero : g x = 0 := e.injective (by simpa [phi] using hx)
    have hgSurj := hsurj x hgzero hxO
    have hderiv : fderiv ℝ phi x =
        e.toContinuousLinearMap.comp (fderiv ℝ g x) := by
      change fderiv ℝ (fun y => e (g y)) x = _
      rw [fderiv_fun_comp x e.differentiableAt
        (hg.differentiable (by simp)).differentiableAt]
      have he : fderiv ℝ (e : Z → (Fin (Module.finrank ℝ Z) → ℝ)) (g x) =
          e.toContinuousLinearMap := e.hasFDerivAt.fderiv
      rw [he]
    rw [hderiv]
    exact e.surjective.comp hgSurj
  have hreg := isLocalRegularLevelSetOfCodimAtLeast_zeroSet_inter_isOpen
    phi hc hphi hO hphiSurj
  convert hreg using 1
  ext x
  simp [phi]

/-- A local regular level set of codimension at least `c` stays one after intersecting with an
open set. -/
theorem IsLocalRegularLevelSetOfCodimAtLeast.inter_isOpen
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {S O : Set Y} {c : ℕ}
    (hS : IsLocalRegularLevelSetOfCodimAtLeast S c) (hO : IsOpen O) :
    IsLocalRegularLevelSetOfCodimAtLeast (S ∩ O) c := by
  intro y hy
  obtain ⟨m, hcm, U, hU, hyU, g, hg, hzero, hsurj⟩ := hS y hy.1
  refine ⟨m, hcm, U ∩ O, hU.inter hO, ⟨hyU, hy.2⟩, g,
    hg.mono inter_subset_left, ?_, ?_⟩
  · intro x hx
    constructor
    · intro hxS
      exact (hzero x hx.1).mp hxS.1
    · intro hxzero
      exact ⟨(hzero x hx.1).mpr hxzero, hx.2⟩
  · intro x hx
    simpa only [fderivWithin_of_isOpen (hU.inter hO) hx,
      fderivWithin_of_isOpen hU hx.1] using hsurj x hx.1

/-- Finitely many pairwise disjoint local regular level sets of codimension at least `c` form a
finite regular stratification of their union. -/
def finiteRegularStratification_of_pairwise
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {n c : ℕ} (stratum : Fin n → Set Y)
    (hpair : Set.PairwiseDisjoint Set.univ stratum)
    (hregular : ∀ i, IsLocalRegularLevelSetOfCodimAtLeast (stratum i) c) :
    FiniteRegularStratification (⋃ i, stratum i) c where
  numberOfStrata := n
  stratum := stratum
  pairwise_disjoint := hpair
  cover := rfl
  regular := hregular

/-- A single local regular level set is a one-stratum finite regular stratification. -/
def finiteRegularStratification_of_regular
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {S : Set Y} {c : ℕ}
    (hregular : IsLocalRegularLevelSetOfCodimAtLeast S c) :
    FiniteRegularStratification S c := by
  let stratum : Fin 1 → Set Y := fun _ => S
  have hpair : Set.PairwiseDisjoint Set.univ stratum := by
    intro i _ j _ hij
    exact (hij (Subsingleton.elim i j)).elim
  have h := finiteRegularStratification_of_pairwise stratum hpair (fun _ => hregular)
  simpa only [stratum, iUnion_const] using h

/-- Adjoin a regular stratum `R`, disjoint from `T`, to a finite regular stratification of `T` to
stratify `S = R ∪ T`. -/
def FiniteRegularStratification.cons
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {S R T : Set Y} {c : ℕ}
    (tail : FiniteRegularStratification T c)
    (hR : IsLocalRegularLevelSetOfCodimAtLeast R c)
    (hRT : Disjoint R T) (hS : S = R ∪ T) :
    FiniteRegularStratification S c where
  numberOfStrata := tail.numberOfStrata + 1
  stratum := Fin.cases R tail.stratum
  pairwise_disjoint := by
    rw [Set.PairwiseDisjoint, Set.pairwise_univ, pairwise_fin_succ_iff]
    have hsubset : ∀ j, tail.stratum j ⊆ T := by
      intro j x hx
      have hx' : x ∈ ⋃ i, tail.stratum i := mem_iUnion.mpr ⟨j, hx⟩
      exact tail.cover.symm ▸ hx'
    refine ⟨?_, ?_, ?_⟩
    · intro i
      exact hRT.symm.mono_left (hsubset i)
    · intro j
      exact hRT.mono_right (hsubset j)
    · intro i j hij
      exact tail.pairwise_disjoint (mem_univ i) (mem_univ j) hij
  cover := by
    rw [iUnion_fin_add_one_eq_iUnion_succ]
    simpa only [tail.cover] using! hS
  regular := by
    intro i
    refine Fin.cases hR (fun j => tail.regular j) i

end

end GaloisForLFunctions.HTGeometry
