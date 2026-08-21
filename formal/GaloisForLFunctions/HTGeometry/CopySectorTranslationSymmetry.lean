/-
# The copy sector is a translation-invariant feature sector

A measure-preserving bijection that maps a finite orthonormal family into its own span does so by an
orthogonal coefficient matrix, because it preserves the Gram matrix of the family.  So a
measure-preserving symmetry group is automatically a group of feature symmetries, and if it acts
transitively the leverage of the sector is exactly its centred dimension.

The copy sector of a unitary register is the matrix-coefficient space of the representation
`U ↦ U^{⊗k} ⊗ \bar U^{⊗k}`, whose complex dimension is `D^{2k}`; left translation carries every
matrix coefficient of a representation into the span of the matrix coefficients, so the sector is
translation invariant and its leverage is at most `2D^{4k}`.

Main results:
* `isFeatureSymmetry_of_measureInvariant` — **orthogonality of the coefficient matrix**.
* `featureKernel_diag_eq_card_of_transitive_measure` — `(8c)` over a probability measure.
* `copyRep`, `copyRep_mul`, `card_copyIndex` — the copy representation.
* `matrixCoefficientFamily_translate` — **the sector is translation invariant**.
* `abs_spectralResolventKernel_le_copySector` — **`(8e)`**.
-/
import GaloisForLFunctions.HTGeometry.SpectralResolventKernel
import Mathlib.MeasureTheory.Integral.Bochner.Basic

open Finset MeasureTheory

noncomputable section

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

section MeasureSymmetry

variable {iota X : Type*} [Fintype iota] [DecidableEq iota] [MeasurableSpace X]

/-- Invariance of the integral under a self-map. -/
def IsIntegralInvariant (pi : Measure X) (g : X → X) : Prop :=
  ∀ f : X → ℝ, Integrable f pi → ∫ x, f (g x) ∂pi = ∫ x, f x ∂pi

theorem isIntegralInvariant_of_measurePreserving {pi : Measure X} {g : X → X}
    (hg : MeasurePreserving g pi pi) (hemb : MeasurableEmbedding g) :
    IsIntegralInvariant pi g :=
  fun f _ => hg.integral_comp hemb f

/-- Orthonormality of a finite family against a measure. -/
def IsOrthonormalFamily (pi : Measure X) (phi : iota → X → ℝ) : Prop :=
  ∀ i j, ∫ x, phi i x * phi j x ∂pi = if i = j then 1 else 0

/-- **A measure-preserving symmetry acts on an orthonormal family by an orthogonal matrix.**  The
Gram matrix of the transformed family is `O Oᵀ`, and it is preserved, so `O Oᵀ = 1`. -/
theorem isFeatureSymmetry_of_measureInvariant {pi : Measure X} {phi : iota → X → ℝ}
    (hphi : IsOrthonormalFamily pi phi)
    (hint : ∀ i j, Integrable (fun x => phi i x * phi j x) pi)
    {g : X → X} (hg : IsIntegralInvariant pi g)
    {O : Matrix iota iota ℝ} (hcomp : ∀ j x, phi j (g x) = ∑ i, O j i * phi i x) :
    IsFeatureSymmetry phi g O := by
  classical
  have hgram : ∀ j k : iota, (O * O.transpose) j k = (if j = k then (1 : ℝ) else 0) := by
    intro j k
    have hleft : ∫ x, phi j (g x) * phi k (g x) ∂pi = (if j = k then (1 : ℝ) else 0) := by
      rw [hg (fun x => phi j x * phi k x) (hint j k)]
      exact hphi j k
    have hexpand : ∀ x : X, phi j (g x) * phi k (g x)
        = ∑ i, ∑ l, (O j i * O k l) * (phi i x * phi l x) := by
      intro x
      rw [hcomp j x, hcomp k x, Finset.sum_mul_sum]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => by ring
    have hright : ∫ x, phi j (g x) * phi k (g x) ∂pi = ∑ i, O j i * O k i := by
      rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hexpand)]
      rw [MeasureTheory.integral_finsetSum _
        (fun i _ => by
          refine MeasureTheory.integrable_finsetSum _ fun l _ => ?_
          exact ((hint i l).const_mul (O j i * O k l)))]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [MeasureTheory.integral_finsetSum _
        (fun l _ => ((hint i l).const_mul (O j i * O k l)))]
      rw [Finset.sum_congr rfl fun l _ => MeasureTheory.integral_const_mul (O j i * O k l)
        (fun x => phi i x * phi l x)]
      rw [Finset.sum_congr rfl fun l _ => by rw [hphi i l]]
      simp
    have hOO : (O * O.transpose) j k = ∑ i, O j i * O k i := by
      simp [Matrix.mul_apply, Matrix.transpose_apply]
    rw [hOO, ← hright, hleft]
  refine ⟨?_, hcomp⟩
  refine (mul_eq_one_comm (M := Matrix iota iota ℝ)).mp ?_
  ext j k
  rw [hgram j k, Matrix.one_apply]

/-- **`(8c)` over a probability measure.**  A constant kernel diagonal equals the number of
centred modes. -/
theorem featureKernel_diag_eq_card_of_const_measure {pi : Measure X} [IsProbabilityMeasure pi]
    {phi : iota → X → ℝ} (hphi : ∀ j, ∫ x, phi j x ^ 2 ∂pi = 1)
    (hint : ∀ j, Integrable (fun x => phi j x ^ 2) pi)
    {c : ℝ} (hconst : ∀ x, featureKernel phi x x = c) :
    c = (Fintype.card iota : ℝ) := by
  classical
  have hkey : ∫ x, featureKernel phi x x ∂pi = (Fintype.card iota : ℝ) := by
    have hrw : ∀ x : X, featureKernel phi x x = ∑ j, phi j x ^ 2 :=
      fun x => Finset.sum_congr rfl fun j _ => by ring
    rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hrw)]
    rw [MeasureTheory.integral_finsetSum _ (fun j _ => hint j)]
    rw [Finset.sum_congr rfl fun j _ => hphi j]
    simp
  have hcst : ∫ x, featureKernel phi x x ∂pi = c := by
    rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hconst)]
    simp
  rw [← hcst, hkey]

/-- **`(8c)`.**  A transitive measure-preserving symmetry makes the leverage exactly the number of
centred modes. -/
theorem featureKernel_diag_eq_card_of_transitive_measure {pi : Measure X} [IsProbabilityMeasure pi]
    {phi : iota → X → ℝ} (hphi : IsOrthonormalFamily pi phi)
    (hint : ∀ i j, Integrable (fun x => phi i x * phi j x) pi)
    (hsym : ∀ x y : X, ∃ (g : X → X) (O : Matrix iota iota ℝ),
      IsIntegralInvariant pi g ∧ (∀ j z, phi j (g z) = ∑ i, O j i * phi i z) ∧ g x = y)
    (x : X) :
    featureKernel phi x x = (Fintype.card iota : ℝ) := by
  classical
  have hsym' : ∀ u v : X, ∃ (g : X → X) (O : Matrix iota iota ℝ),
      IsFeatureSymmetry phi g O ∧ g u = v := by
    intro u v
    obtain ⟨g, O, hg, hcomp, hguv⟩ := hsym u v
    exact ⟨g, O, isFeatureSymmetry_of_measureInvariant hphi hint hg hcomp, hguv⟩
  refine featureKernel_diag_eq_card_of_const_measure
    (fun j => by
      have := hphi j j
      rw [if_pos rfl] at this
      rw [← this]
      exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun z => by ring))
    (fun j => by
      have := hint j j
      refine this.congr (Filter.Eventually.of_forall fun z => by ring))
    (fun y => featureKernel_diag_const_of_transitive hsym' y x)

end MeasureSymmetry


section CopyRepresentation

variable {D : ℕ}

/-- The index set of the `k`-fold copy sector. -/
abbrev copyIndex (k D : ℕ) : Type := (Fin k → Fin D) × (Fin k → Fin D)

/-- The copy representation `U ↦ U^{⊗k} ⊗ \bar U^{⊗k}`. -/
def copyRep (k : ℕ) (U : Matrix (Fin D) (Fin D) ℂ) :
    Matrix (copyIndex k D) (copyIndex k D) ℂ :=
  fun p q => (∏ s, U (p.1 s) (q.1 s)) * (∏ s, (starRingEnd ℂ) (U (p.2 s) (q.2 s)))

theorem card_copyIndex (k D : ℕ) : Fintype.card (copyIndex k D) = D ^ k * D ^ k := by
  simp [Fintype.card_prod]

theorem copyRep_mul (k : ℕ) (U V : Matrix (Fin D) (Fin D) ℂ) :
    copyRep k (U * V) = copyRep k U * copyRep k V := by
  classical
  ext p q
  have hfst : (∏ s, (U * V) (p.1 s) (q.1 s))
      = ∑ e : Fin k → Fin D, ∏ s, (U (p.1 s) (e s) * V (e s) (q.1 s)) := by
    have hstep : ∀ s : Fin k, (U * V) (p.1 s) (q.1 s)
        = ∑ y : Fin D, U (p.1 s) y * V y (q.1 s) := fun s => by
      rw [Matrix.mul_apply]
    rw [Finset.prod_congr rfl fun s _ => hstep s]
    rw [Finset.prod_univ_sum (fun _ : Fin k => (Finset.univ : Finset (Fin D)))
      (fun s y => U (p.1 s) y * V y (q.1 s))]
    rw [Fintype.piFinset_univ]
  have hsnd : (∏ s, (starRingEnd ℂ) ((U * V) (p.2 s) (q.2 s)))
      = ∑ f : Fin k → Fin D, ∏ s,
        ((starRingEnd ℂ) (U (p.2 s) (f s)) * (starRingEnd ℂ) (V (f s) (q.2 s))) := by
    have hstep : ∀ s : Fin k, (starRingEnd ℂ) ((U * V) (p.2 s) (q.2 s))
        = ∑ y : Fin D, (starRingEnd ℂ) (U (p.2 s) y) * (starRingEnd ℂ) (V y (q.2 s)) := by
      intro s
      rw [Matrix.mul_apply, map_sum]
      exact Finset.sum_congr rfl fun y _ => by rw [map_mul]
    rw [Finset.prod_congr rfl fun s _ => hstep s]
    rw [Finset.prod_univ_sum (fun _ : Fin k => (Finset.univ : Finset (Fin D)))
      (fun s y => (starRingEnd ℂ) (U (p.2 s) y) * (starRingEnd ℂ) (V y (q.2 s)))]
    rw [Fintype.piFinset_univ]
  show (∏ s, (U * V) (p.1 s) (q.1 s)) * (∏ s, (starRingEnd ℂ) ((U * V) (p.2 s) (q.2 s)))
      = ∑ r : copyIndex k D, copyRep k U p r * copyRep k V r q
  rw [hfst, hsnd, Finset.sum_mul_sum, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun f _ => ?_
  rw [copyRep, copyRep, Finset.prod_mul_distrib, Finset.prod_mul_distrib]
  ring

/-- The real observables of a matrix-coefficient sector at an arbitrary index type. -/
def coeffFamily {n X : Type*} (rho : X → Matrix n n ℂ) : Option (Bool × (n × n)) → (X → ℝ)
  | none => fun _ => 1
  | some (false, p) => fun x => (rho x p.1 p.2).re
  | some (true, p) => fun x => (rho x p.1 p.2).im

/-- **The matrix-coefficient sector is translation invariant.**  Left translation carries every
matrix coefficient of a representation into the span of the matrix coefficients. -/
theorem coeffFamily_translate_mem_span {G n : Type*} [Fintype n] [Mul G]
    (rho : G → Matrix n n ℂ) (hmul : ∀ g x, rho (g * x) = rho g * rho x) (g : G)
    (b : Option (Bool × (n × n))) :
    (fun x => coeffFamily rho b (g * x)) ∈ Submodule.span ℝ (Set.range (coeffFamily rho)) := by
  classical
  match b with
  | none =>
      have : (fun x : G => coeffFamily rho none (g * x)) = coeffFamily rho none := rfl
      rw [this]
      exact Submodule.subset_span ⟨none, rfl⟩
  | some (beta, p) =>
      have hentry : ∀ x : G, rho (g * x) p.1 p.2
          = ∑ r : n, rho g p.1 r * rho x r p.2 := by
        intro x
        rw [hmul, Matrix.mul_apply]
      have hre : ∀ x : G, (rho (g * x) p.1 p.2).re
          = ∑ r : n, ((rho g p.1 r).re * (rho x r p.2).re
              - (rho g p.1 r).im * (rho x r p.2).im) := by
        intro x
        rw [hentry x, Complex.re_sum]
        exact Finset.sum_congr rfl fun r _ => by rw [Complex.mul_re]
      have him : ∀ x : G, (rho (g * x) p.1 p.2).im
          = ∑ r : n, ((rho g p.1 r).re * (rho x r p.2).im
              + (rho g p.1 r).im * (rho x r p.2).re) := by
        intro x
        rw [hentry x, Complex.im_sum]
        exact Finset.sum_congr rfl fun r _ => by rw [Complex.mul_im]
      have hbasisRe : ∀ r : n, (fun x : G => (rho x r p.2).re)
          ∈ Submodule.span ℝ (Set.range (coeffFamily rho)) := fun r =>
        Submodule.subset_span ⟨some (false, (r, p.2)), rfl⟩
      have hbasisIm : ∀ r : n, (fun x : G => (rho x r p.2).im)
          ∈ Submodule.span ℝ (Set.range (coeffFamily rho)) := fun r =>
        Submodule.subset_span ⟨some (true, (r, p.2)), rfl⟩
      cases beta with
      | false =>
          have hfun : (fun x : G => coeffFamily rho (some (false, p)) (g * x))
              = ∑ r : n, ((rho g p.1 r).re • (fun x : G => (rho x r p.2).re)
                  + (-(rho g p.1 r).im) • (fun x : G => (rho x r p.2).im)) := by
            funext x
            show (rho (g * x) p.1 p.2).re = _
            rw [hre x]
            simp only [Finset.sum_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
            exact Finset.sum_congr rfl fun r _ => by ring
          rw [hfun]
          refine Submodule.sum_mem _ fun r _ => Submodule.add_mem _ ?_ ?_
          · exact Submodule.smul_mem _ _ (hbasisRe r)
          · exact Submodule.smul_mem _ _ (hbasisIm r)
      | true =>
          have hfun : (fun x : G => coeffFamily rho (some (true, p)) (g * x))
              = ∑ r : n, ((rho g p.1 r).re • (fun x : G => (rho x r p.2).im)
                  + ((rho g p.1 r).im) • (fun x : G => (rho x r p.2).re)) := by
            funext x
            show (rho (g * x) p.1 p.2).im = _
            rw [him x]
            simp only [Finset.sum_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
          rw [hfun]
          refine Submodule.sum_mem _ fun r _ => Submodule.add_mem _ ?_ ?_
          · exact Submodule.smul_mem _ _ (hbasisIm r)
          · exact Submodule.smul_mem _ _ (hbasisRe r)

end CopyRepresentation


section Counting

variable {kappa X : Type*} [Fintype kappa] [DecidableEq kappa] [MeasurableSpace X]

/-- An orthonormal family is linearly independent. -/
theorem linearIndependent_of_orthonormalFamily {pi : Measure X} {psi : kappa → X → ℝ}
    (hpsi : IsOrthonormalFamily pi psi)
    (hint : ∀ i j, Integrable (fun x => psi i x * psi j x) pi) :
    LinearIndependent ℝ psi := by
  classical
  refine Fintype.linearIndependent_iff.mpr fun c hc k => ?_
  have hvanish : ∀ x : X, (∑ j, c j * psi j x) = 0 := by
    intro x
    have h := congrFun hc x
    simpa [Finset.sum_apply] using h
  have hzero : ∫ x, (∑ j, c j * psi j x) * psi k x ∂pi = 0 := by
    simp [hvanish]
  have hexp : ∫ x, (∑ j, c j * psi j x) * psi k x ∂pi = c k := by
    have hrw : ∀ x : X, (∑ j, c j * psi j x) * psi k x
        = ∑ j, c j * (psi j x * psi k x) := by
      intro x
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hrw)]
    rw [MeasureTheory.integral_finsetSum _ (fun j _ => (hint j k).const_mul (c j))]
    rw [Finset.sum_congr rfl fun j _ =>
      MeasureTheory.integral_const_mul (c j) (fun x => psi j x * psi k x)]
    rw [Finset.sum_congr rfl fun j _ => by rw [hpsi j k]]
    simp
  rw [← hexp, hzero]

/-- A centred orthonormal family together with the constant. -/
def augmentedFamily (psi : kappa → X → ℝ) : Option kappa → (X → ℝ)
  | none => fun _ => 1
  | some j => psi j

theorem isOrthonormalFamily_augmented {pi : Measure X} [IsProbabilityMeasure pi]
    {psi : kappa → X → ℝ} (hpsi : IsOrthonormalFamily pi psi)
    (hcent : ∀ j, ∫ x, psi j x ∂pi = 0) :
    IsOrthonormalFamily pi (augmentedFamily psi) := by
  classical
  intro i j
  match i, j with
  | none, none =>
      show ∫ _ : X, (1 : ℝ) * 1 ∂pi = _
      simp
  | none, some j =>
      show ∫ x : X, (1 : ℝ) * psi j x ∂pi = _
      rw [if_neg (by simp)]
      simpa using hcent j
  | some i, none =>
      show ∫ x : X, psi i x * (1 : ℝ) ∂pi = _
      rw [if_neg (by simp)]
      simpa using hcent i
  | some i, some j =>
      show ∫ x : X, psi i x * psi j x ∂pi = _
      rw [hpsi i j]
      by_cases h : i = j
      · rw [if_pos h, if_pos (by rw [h])]
      · rw [if_neg h, if_neg (by simpa using h)]

theorem integrable_augmented {pi : Measure X} [IsProbabilityMeasure pi]
    {psi : kappa → X → ℝ} (hint : ∀ i j, Integrable (fun x => psi i x * psi j x) pi)
    (hint1 : ∀ j, Integrable (psi j) pi) (i j : Option kappa) :
    Integrable (fun x => augmentedFamily psi i x * augmentedFamily psi j x) pi := by
  rcases i with _ | i <;> rcases j with _ | j
  · exact (MeasureTheory.integrable_const (1 : ℝ)).congr
      (Filter.Eventually.of_forall fun _ => by simp [augmentedFamily])
  · exact (hint1 j).congr
      (Filter.Eventually.of_forall fun _ => by simp [augmentedFamily])
  · exact (hint1 i).congr
      (Filter.Eventually.of_forall fun _ => by simp [augmentedFamily])
  · exact hint i j

/-- **The copy-sector dimension count.**  A centred orthonormal family inside the real
matrix-coefficient sector of a representation with index type `n` has at most `2·card n ^ 2`
members: the constant occupies one of the `2·card n ^ 2 + 1` available dimensions. -/
theorem card_le_of_centred_orthonormal_in_span {n : Type*} [Fintype n]
    {pi : Measure X} [IsProbabilityMeasure pi] {psi : kappa → X → ℝ}
    (hpsi : IsOrthonormalFamily pi psi) (hcent : ∀ j, ∫ x, psi j x ∂pi = 0)
    (hint : ∀ i j, Integrable (fun x => psi i x * psi j x) pi)
    (hint1 : ∀ j, Integrable (psi j) pi)
    (rho : X → Matrix n n ℂ)
    (hmem : ∀ j, psi j ∈ Submodule.span ℝ (Set.range (coeffFamily rho))) :
    Fintype.card kappa ≤ 2 * Fintype.card n ^ 2 := by
  classical
  have hli : LinearIndependent ℝ (augmentedFamily psi) :=
    linearIndependent_of_orthonormalFamily (isOrthonormalFamily_augmented hpsi hcent)
      (integrable_augmented hint hint1)
  have hsub : Submodule.span ℝ (Set.range (augmentedFamily psi))
      ≤ Submodule.span ℝ (Set.range (coeffFamily rho)) := by
    refine Submodule.span_le.mpr ?_
    rintro f ⟨b, rfl⟩
    match b with
    | none => exact Submodule.subset_span ⟨none, rfl⟩
    | some j => exact hmem j
  have hfin : Module.Finite ℝ (Submodule.span ℝ (Set.range (coeffFamily rho))) :=
    Module.Finite.span_of_finite ℝ (Set.finite_range _)
  have hmono := Submodule.finrank_mono (R := ℝ) hsub
  rw [finrank_span_eq_card hli] at hmono
  have hcount : Module.finrank ℝ (Submodule.span ℝ (Set.range (coeffFamily rho)))
      ≤ Fintype.card (Option (Bool × (n × n))) := finrank_range_le_card (coeffFamily rho)
  have hcard : Fintype.card (Option (Bool × (n × n))) = 2 * Fintype.card n ^ 2 + 1 := by
    simp [Fintype.card_option, Fintype.card_prod]
    ring
  rw [hcard] at hcount
  have : Fintype.card (Option kappa) ≤ 2 * Fintype.card n ^ 2 + 1 := le_trans hmono hcount
  rw [Fintype.card_option] at this
  omega

end Counting


section CopySectorBound

variable {kappa : Type*} [Fintype kappa] [DecidableEq kappa]

/-- **`(8e)`.**  On a group carrying a left-invariant probability measure, a centred orthonormal
family spanning a translation-invariant sector inside the real matrix coefficients of a
representation has resolvent bound `2·card n ^ 2 / (1 - a)`.  For the copy representation
`U ↦ U^{⊗k} ⊗ \bar U^{⊗k}` of a `D`-level register this is `2D^{4k}/(1-a)`. -/
theorem abs_spectralResolventKernel_le_copySector
    {G : Type*} [Group G] [MeasurableSpace G] {pi : Measure G} [IsProbabilityMeasure pi]
    (hinv : ∀ g : G, IsIntegralInvariant pi (fun x => g * x))
    {psi : kappa → G → ℝ} (hpsi : IsOrthonormalFamily pi psi)
    (hcent : ∀ j, ∫ x, psi j x ∂pi = 0)
    (hint : ∀ i j, Integrable (fun x => psi i x * psi j x) pi)
    (hint1 : ∀ j, Integrable (psi j) pi)
    (hspan : ∀ (g : G) (j : kappa),
      (fun x => psi j (g * x)) ∈ Submodule.span ℝ (Set.range psi))
    {n : Type*} [Fintype n] (rho : G → Matrix n n ℂ)
    (hmem : ∀ j, psi j ∈ Submodule.span ℝ (Set.range (coeffFamily rho)))
    {lam : kappa → ℝ} (hlam : ∀ j, |lam j| ≤ 1) {a : ℝ} (ha : 0 ≤ a) (ha1 : a < 1)
    (x y : G) :
    |spectralResolventKernel psi lam a x y| ≤ (2 * (Fintype.card n : ℝ) ^ 2) / (1 - a) := by
  classical
  have hsym : ∀ u v : G, ∃ (g : G → G) (O : Matrix kappa kappa ℝ),
      IsIntegralInvariant pi g ∧ (∀ j z, psi j (g z) = ∑ i, O j i * psi i z) ∧ g u = v := by
    intro u v
    choose Ofun hO using fun j : kappa =>
      (Submodule.mem_span_range_iff_exists_fun ℝ).mp (hspan (v * u⁻¹) j)
    refine ⟨fun z => (v * u⁻¹) * z, Matrix.of (fun j i => Ofun j i), hinv (v * u⁻¹), ?_, ?_⟩
    · intro j z
      have h := congrFun (hO j) z
      simpa [Finset.sum_apply] using h.symm
    · group
  have hdiag : ∀ z : G, featureKernel psi z z = (Fintype.card kappa : ℝ) :=
    fun z => featureKernel_diag_eq_card_of_transitive_measure hpsi hint hsym z
  have hbound := abs_spectralResolventKernel_le (phi := psi) (lam := lam) ha ha1 hlam
    (fun z => le_of_eq (hdiag z)) x y
  refine le_trans hbound ?_
  have hcard : (Fintype.card kappa : ℝ) ≤ 2 * (Fintype.card n : ℝ) ^ 2 := by
    have h := card_le_of_centred_orthonormal_in_span hpsi hcent hint hint1 rho hmem
    have : ((Fintype.card kappa : ℕ) : ℝ) ≤ ((2 * Fintype.card n ^ 2 : ℕ) : ℝ) := by
      exact_mod_cast h
    push_cast at this
    exact this
  have hpos : (0 : ℝ) < 1 - a := by linarith
  gcongr

end CopySectorBound


section UnitaryCopySector

variable {D : ℕ}

/-- The copy representation of the unitary group is multiplicative. -/
theorem copyRep_unitaryGroup_mul (k : ℕ) (U V : Matrix.unitaryGroup (Fin D) ℂ) :
    copyRep k ((U * V : Matrix.unitaryGroup (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ)
      = copyRep k (U : Matrix (Fin D) (Fin D) ℂ) * copyRep k (V : Matrix (Fin D) (Fin D) ℂ) := by
  rw [show ((U * V : Matrix.unitaryGroup (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ)
      = (U : Matrix (Fin D) (Fin D) ℂ) * (V : Matrix (Fin D) (Fin D) ℂ) from rfl]
  exact copyRep_mul k _ _

/-- **The copy-sector dimension.**  The `k`-fold copy representation of a `D`-level register has
complex dimension `D^{2k}`, so its real matrix-coefficient sector has leverage at most `2D^{4k}`. -/
theorem two_mul_card_copyIndex_sq (k D : ℕ) :
    2 * (Fintype.card (copyIndex k D) : ℝ) ^ 2 = 2 * (D : ℝ) ^ (4 * k) := by
  rw [card_copyIndex]
  push_cast
  ring

end UnitaryCopySector

end GaloisForLFunctions.HTGeometry

end
