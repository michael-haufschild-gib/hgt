import Mathlib
import GaloisForLFunctions.HTGeometry.ParametricRootCovering
import GaloisForLFunctions.Bottcher.BranchContinuation
import GaloisForLFunctions.Bottcher.ProperLocalHomeoCovering

/-!
# The root locus of a two-variable polynomial with everywhere-separable fibres is a covering
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial Topology Set
open scoped ContDiff

noncomputable section

/-- Two-variable evaluation: substitute the first coordinate in the coefficients of `f` and
evaluate the resulting one-variable polynomial at the second coordinate. -/
noncomputable def biEval (f : ℂ[X][X]) (p : ℂ × ℂ) : ℂ :=
  Polynomial.eval₂ (Polynomial.evalRingHom p.1) p.2 f

/-- The specialised one-variable polynomial: substitute `s` in the coefficients of `f`. -/
noncomputable def biFibre {R : Type*} [CommRing R] (f : R[X][X]) (s : R) : R[X] :=
  f.map (Polynomial.evalRingHom s)

theorem biEval_eq_eval_biFibre (f : ℂ[X][X]) (p : ℂ × ℂ) :
    biEval f p = (biFibre f p.1).eval p.2 := by
  simp [biEval, biFibre, Polynomial.eval_map]

theorem analyticAt_biEval (f : ℂ[X][X]) (q : ℂ × ℂ) : AnalyticAt ℂ (biEval f) q := by
  have h : biEval f = fun p : ℂ × ℂ => ∑ i ∈ Finset.range (f.natDegree + 1),
      (Polynomial.aeval p.1 (f.coeff i)) * p.2 ^ i := by
    funext p
    simp [biEval, Polynomial.eval₂_eq_sum_range]
  rw [h]
  apply Finset.analyticAt_fun_sum
  intro i _
  exact (analyticAt_fst.aeval_polynomial (f.coeff i)).mul (analyticAt_snd.pow i)

theorem continuous_biEval (f : ℂ[X][X]) : Continuous (biEval f) := by
  rw [continuous_iff_continuousAt]
  exact fun q => (analyticAt_biEval f q).continuousAt

/-- The partial derivative in the root variable is the derivative of the specialised fibre. -/
theorem biEval_partial_snd (f : ℂ[X][X]) (p : ℂ × ℂ) :
    (fderiv ℂ (biEval f) p) (0, 1) = (derivative (biFibre f p.1)).eval p.2 := by
  have hfdiff : HasFDerivAt (biEval f) (fderiv ℂ (biEval f) p) p :=
    (analyticAt_biEval f p).differentiableAt.hasFDerivAt
  have hι : HasFDerivAt (fun z : ℂ => (p.1, z))
      ((0 : ℂ →L[ℂ] ℂ).prod (ContinuousLinearMap.id ℂ ℂ)) p.2 :=
    (hasFDerivAt_const p.1 p.2).prodMk (hasFDerivAt_id p.2)
  have hcomp : HasFDerivAt (fun z => biEval f (p.1, z))
      ((fderiv ℂ (biEval f) p).comp
        ((0 : ℂ →L[ℂ] ℂ).prod (ContinuousLinearMap.id ℂ ℂ))) p.2 := by
    have h := hfdiff.comp p.2 hι
    simpa [Function.comp_def] using h
  have hpoly : HasDerivAt (fun z => biEval f (p.1, z))
      ((derivative (biFibre f p.1)).eval p.2) p.2 := by
    have heq : (fun z => biEval f (p.1, z)) = fun z => (biFibre f p.1).eval z := by
      funext z
      exact biEval_eq_eval_biFibre f (p.1, z)
    rw [heq]
    exact Polynomial.hasDerivAt _ p.2
  have huniq := hcomp.unique hpoly.hasFDerivAt
  have hev := ContinuousLinearMap.ext_iff.mp huniq 1
  simpa using hev

/-- The root locus of `f`. -/
def BiRootLocus (f : ℂ[X][X]) : Set (ℂ × ℂ) := {p | biEval f p = 0}

/-- Projection of the root locus to the parameter. -/
def biRootProj {f : ℂ[X][X]} (q : BiRootLocus f) : ℂ := q.1.1

theorem biRootLocus_eval (f : ℂ[X][X]) (q : BiRootLocus f) :
    (biFibre f q.1.1).eval q.1.2 = 0 := by
  have h : biEval f q.1 = 0 := q.2
  rw [biEval_eq_eval_biFibre] at h
  exact h

theorem biRootLocus_partial_ne {f : ℂ[X][X]} (q : BiRootLocus f)
    (hsep : (biFibre f q.1.1).Separable) :
    (fderiv ℂ (biEval f) (q.1.1, q.1.2)) (0, 1) ≠ 0 := by
  rw [biEval_partial_snd]
  exact hsep.eval₂_derivative_ne_zero (RingHom.id ℂ) (biRootLocus_eval f q)

/-! ### The implicit-function chart -/

/-- Implicit-function data at a point of the root locus. -/
noncomputable def biIFTData {f : ℂ[X][X]} (q : BiRootLocus f)
    (hsep : (biFibre f q.1.1).Separable) :
    ImplicitFunctionData ℂ (ℂ × ℂ) ℂ ℂ :=
  parametricRootIFTData q (analyticAt_biEval f q.1) (biRootLocus_partial_ne q hsep)

theorem biIFTData_apply {f : ℂ[X][X]} (q : BiRootLocus f)
    (hsep : (biFibre f q.1.1).Separable) (v : ℂ × ℂ) :
    (biIFTData q hsep).toOpenPartialHomeomorph v = (biEval f v, v.1) := rfl

theorem biIFTData_mem_source {f : ℂ[X][X]} (q : BiRootLocus f)
    (hsep : (biFibre f q.1.1).Separable) :
    (q : ℂ × ℂ) ∈ (biIFTData q hsep).toOpenPartialHomeomorph.source :=
  ImplicitFunctionData.pt_mem_toOpenPartialHomeomorph_source _

/-- **A chart of the root projection at a point where the fibre is separable.** -/
theorem exists_chart_biRootProj {f : ℂ[X][X]} (e : BiRootLocus f)
    (hsepe : (biFibre f e.1.1).Separable) :
    ∃ φ : OpenPartialHomeomorph (BiRootLocus f) ℂ,
      e ∈ φ.source ∧ biRootProj (f := f) = φ :=
  exists_chart_parametricRootProj e (analyticAt_biEval f e.1)
    (biRootLocus_partial_ne e hsepe)

/-- **The root projection is a local homeomorphism** as soon as every fibre is separable. -/
theorem isLocalHomeomorph_biRootProj {f : ℂ[X][X]}
    (hsep : ∀ s : ℂ, (biFibre f s).Separable) :
    IsLocalHomeomorph (biRootProj (f := f)) :=
  isLocalHomeomorph_parametricRootProj
    (fun q => analyticAt_biEval f q.1)
    (fun q => biRootLocus_partial_ne q (hsep q.1.1))

/-! ### Properness and the covering property -/

theorem biFibre_monic {R : Type*} [CommRing R] {f : R[X][X]} (hf : f.Monic) (s : R) :
    (biFibre f s).Monic :=
  hf.map _

theorem biFibre_natDegree {R : Type*} [CommRing R] [Nontrivial R] {f : R[X][X]} (hf : f.Monic)
    (s : R) : (biFibre f s).natDegree = f.natDegree :=
  hf.natDegree_map _

theorem biFibre_coeff {R : Type*} [CommRing R] (f : R[X][X]) (s : R) (i : ℕ) :
    (biFibre f s).coeff i = (f.coeff i).eval s := by
  simp [biFibre, Polynomial.coeff_map]

theorem biFibre_mul {R : Type*} [CommRing R] (f g : R[X][X]) (s : R) :
    biFibre (f * g) s = biFibre f s * biFibre g s := by
  simp [biFibre, Polynomial.map_mul]

theorem biFibre_X_sub_C {R : Type*} [CommRing R] (Q : R[X]) (s : R) :
    biFibre (X - Polynomial.C Q) s = X - Polynomial.C (Q.eval s) := by
  simp [biFibre, Polynomial.map_sub]

/-- Cauchy bound for the root locus, uniform on compacta of the parameter. -/
theorem biRootLocus_norm_le {f : ℂ[X][X]} (hf : f.Monic) (hdeg : 0 < f.natDegree)
    (q : BiRootLocus f) :
    ‖q.1.2‖ ≤ max 1 (∑ i ∈ Finset.range f.natDegree, ‖(f.coeff i).eval q.1.1‖) := by
  have h := Bottcher.norm_root_le_of_monic (biFibre_monic hf q.1.1) (biRootLocus_eval f q)
    (by rw [biFibre_natDegree hf]; exact hdeg)
  rw [biFibre_natDegree hf] at h
  simpa [biFibre_coeff] using h

/-- **The root projection is a proper map.** -/
theorem isProperMap_biRootProj {f : ℂ[X][X]} (hf : f.Monic) (hdeg : 0 < f.natDegree) :
    IsProperMap (biRootProj (f := f)) := by
  classical
  rw [isProperMap_iff_isCompact_preimage]
  refine ⟨continuous_fst.comp continuous_subtype_val, ?_⟩
  intro K hK
  set C : ℂ → ℝ := fun s => ∑ i ∈ Finset.range f.natDegree, ‖(f.coeff i).eval s‖ with hC
  have hCcont : Continuous C := by
    apply continuous_finsetSum
    intro i _
    exact ((f.coeff i).continuous_aeval).norm
  rcases K.eq_empty_or_nonempty with hKe | hKne
  · simp [hKe]
  obtain ⟨smax, _, hmax⟩ := hK.exists_isMaxOn hKne hCcont.continuousOn
  have hsub : (fun q : BiRootLocus f => (q : ℂ × ℂ)) '' (biRootProj (f := f) ⁻¹' K) ⊆
      K ×ˢ Metric.closedBall (0 : ℂ) (max 1 (C smax)) := by
    rintro _ ⟨q, hq, rfl⟩
    refine ⟨hq, ?_⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    exact (biRootLocus_norm_le hf hdeg q).trans (max_le_max_left 1 (hmax hq))
  have hclosed : IsClosed ((fun q : BiRootLocus f => (q : ℂ × ℂ)) ''
      (biRootProj (f := f) ⁻¹' K)) := by
    have himg : (fun q : BiRootLocus f => (q : ℂ × ℂ)) '' (biRootProj (f := f) ⁻¹' K) =
        BiRootLocus f ∩ (Prod.fst ⁻¹' K) := by
      ext p
      constructor
      · rintro ⟨q, hq, rfl⟩
        exact ⟨q.2, hq⟩
      · rintro ⟨hp, hpK⟩
        exact ⟨⟨p, hp⟩, hpK, rfl⟩
    rw [himg]
    exact (isClosed_eq (continuous_biEval f) continuous_const).inter (hK.isClosed.preimage continuous_fst)
  have hcomp : IsCompact ((fun q : BiRootLocus f => (q : ℂ × ℂ)) ''
      (biRootProj (f := f) ⁻¹' K)) :=
    (hK.prod (isCompact_closedBall (0 : ℂ) _)).of_isClosed_subset hclosed hsub
  exact (Topology.IsEmbedding.subtypeVal.isInducing.isCompact_iff).mpr hcomp

/-- **The root locus of an everywhere-separable monic family is a covering of the parameter
plane.** -/
theorem isCoveringMap_biRootProj {f : ℂ[X][X]} (hf : f.Monic) (hdeg : 0 < f.natDegree)
    (hsep : ∀ s : ℂ, (biFibre f s).Separable) :
    IsCoveringMap (biRootProj (f := f)) :=
  isCoveringMap_of_isProperMap_of_isLocalHomeomorph
    (isLocalHomeomorph_biRootProj hsep) (isProperMap_biRootProj hf hdeg)

end

end GaloisForLFunctions.HTGeometry
