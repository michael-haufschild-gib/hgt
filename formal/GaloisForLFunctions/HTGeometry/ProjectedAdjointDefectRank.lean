import GaloisForLFunctions.HTGeometry.FiniteBlaschkeGeneralizedSchurInertia

/-!
# Exact rank of a projected adjoint defect

The negative index of a contraction defect minus a finite-dimensional orthogonal projection is
the rank of the contraction adjoint restricted to the projection range.  This sharpens the
faithful/injective case: a kernel in the restricted adjoint records exactly the directions removed
by common-factor cancellation.
-/

open Complex
open scoped InnerProductSpace ComplexOrder

noncomputable section

namespace GaloisForLFunctions.HTGeometry

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Exact negative index of a projected adjoint defect, including rank loss from a nontrivial
kernel of the restricted adjoint. -/
theorem projectedAdjointDefectForm_hasExactNegativeIndex_rank
    (K : Submodule ℂ H) [K.HasOrthogonalProjection] [FiniteDimensional ℂ K]
    (C : H →L[ℂ] H) (hC : ‖C‖ ≤ 1) :
    HasExactNegativeIndex (projectedAdjointDefectForm K C)
      (Module.finrank ℂ (LinearMap.range
        ((ContinuousLinearMap.adjoint C).toLinearMap.domRestrict K))) := by
  let A : K →ₗ[ℂ] H :=
    (ContinuousLinearMap.adjoint C).toLinearMap.domRestrict K
  obtain ⟨L, hcompl⟩ := (LinearMap.ker A).exists_isCompl
  let incl : L →ₗ[ℂ] H := K.subtype.comp L.subtype
  let W : Submodule ℂ H := LinearMap.range incl
  have hincl : Function.Injective incl := by
    intro x y hxy
    exact Subtype.ext (Subtype.ext hxy)
  have hfinrankW : Module.finrank ℂ W = Module.finrank ℂ L := by
    exact (LinearEquiv.ofInjective incl hincl).finrank_eq.symm
  have hfinrankL : Module.finrank ℂ L = Module.finrank ℂ (LinearMap.range A) := by
    have hcompdim := Submodule.finrank_add_eq_of_isCompl hcompl
    have hranknull := LinearMap.finrank_range_add_finrank_ker A
    omega
  constructor
  · refine ⟨W, hfinrankW.trans hfinrankL, ?_⟩
    intro x hxW hx0
    obtain ⟨y, rfl⟩ := hxW
    have hy0 : (y : K) ≠ 0 := by
      intro hy
      apply hx0
      have hy' : y = 0 := Subtype.ext hy
      rw [hy', map_zero]
    have hAnz : A (y : K) ≠ 0 := by
      intro hAy
      have hyker : (y : K) ∈ LinearMap.ker A := hAy
      have hyL : (y : K) ∈ L := y.property
      have hybot : (y : K) ∈ (⊥ : Submodule ℂ K) := by
        rw [← hcompl.inf_eq_bot]
        exact ⟨hyker, hyL⟩
      exact hy0 hybot
    have hmemK : incl y ∈ K := (y : K).property
    have hstar : K.starProjection (incl y) = incl y :=
      Submodule.starProjection_eq_self_iff.mpr hmemK
    rw [projectedAdjointDefectForm, hstar]
    change ‖incl y‖ ^ (2 : ℕ) - ‖A (y : K)‖ ^ (2 : ℕ) - ‖incl y‖ ^ (2 : ℕ) < 0
    nlinarith [norm_pos_iff.mpr hAnz]
  · intro V hV
    let P : V →ₗ[ℂ] LinearMap.range A :=
      A.rangeRestrict.comp
        (K.orthogonalProjectionOnto.toLinearMap.comp V.subtype)
    have hPinj : Function.Injective P := by
      intro x y hxy
      have hPsub : P (x - y) = 0 := by rw [map_sub, hxy, sub_self]
      let d : H := ((x - y : V) : H)
      let u : H := K.starProjection d
      let v : H := d - u
      have huK : u ∈ K := K.starProjection_apply_mem d
      have hAu : ContinuousLinearMap.adjoint C u = 0 := by
        have hPA : A (K.orthogonalProjectionOnto d) = 0 := by
          exact Subtype.ext_iff.mp hPsub
        change ContinuousLinearMap.adjoint C (K.starProjection d) = 0
        rw [Submodule.starProjection_apply]
        exact hPA
      have hvKperp : v ∈ Kᗮ := K.sub_starProjection_mem_orthogonal d
      have hperp : (inner ℂ u v : ℂ) = 0 :=
        ((K.mem_orthogonal v).1 hvKperp u huK)
      have hsplit : d = u + v := by
        change d = u + (d - u)
        abel
      have hpyth : ‖d‖ ^ (2 : ℕ) = ‖u‖ ^ (2 : ℕ) + ‖v‖ ^ (2 : ℕ) := by
        rw [hsplit]
        simpa [sq] using norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero u v hperp
      have hadj : ContinuousLinearMap.adjoint C d =
          ContinuousLinearMap.adjoint C v := by
        rw [hsplit, map_add, hAu, zero_add]
      have hstar : K.starProjection d = u := rfl
      have hnonneg : 0 ≤ projectedAdjointDefectForm K C d := by
        rw [projectedAdjointDefectForm, hstar, hadj, hpyth]
        have hbound := adjoint_norm_le_self_of_opNorm_le_one C hC v
        nlinarith [norm_nonneg v,
          norm_nonneg (ContinuousLinearMap.adjoint C v)]
      have hd0 : d = 0 := by
        by_contra hd0
        have hneg := hV d (x - y).property hd0
        exact (not_lt_of_ge hnonneg) hneg
      have hsub : x - y = 0 := by
        apply Subtype.ext
        exact hd0
      exact sub_eq_zero.mp hsub
    exact LinearMap.finrank_le_finrank_of_injective hPinj

/-- Exact generalized-Schur index without a coprimality assumption: common inner factors appear
as the rank defect of the numerator adjoint on the denominator model space. -/
theorem finiteBlaschkeGeneralizedSchurForm_hasExactNegativeIndex_rank
    (F : DiskMultiplier) (B : FiniteBlaschke) (hF : F.bd ≤ 1) :
    HasExactNegativeIndex (finiteBlaschkeGeneralizedSchurForm F B)
      (Module.finrank ℂ (LinearMap.range
        ((ContinuousLinearMap.adjoint (hardyMul F)).toLinearMap.domRestrict
          (finiteBlaschkeModelSpace B)))) := by
  exact projectedAdjointDefectForm_hasExactNegativeIndex_rank
    (finiteBlaschkeModelSpace B) (hardyMul F) ((norm_hardyMul_le F).trans hF)

end GaloisForLFunctions.HTGeometry
