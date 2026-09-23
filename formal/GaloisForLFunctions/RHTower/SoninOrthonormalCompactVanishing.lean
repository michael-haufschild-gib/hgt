import GaloisForLFunctions.RHTower.SoninEulerQuadraticCorner
import GaloisForLFunctions.RHTower.SoninEvenCarrier
import GaloisForLFunctions.RHTower.SoninPrincipalRelativeIdeal

/-!
# Compact operators die on orthonormal sequences

Bessel's inequality makes the coefficients of an orthonormal sequence against a fixed vector square
summable, so they vanish; Fréchet--Riesz turns that into weak nullity, and a compact operator sends
a bounded weakly null sequence to a norm null one.

In particular the modes of a fixed shell are killed by every compact operator — the exact
correction included — so a mode estimate never has to carry the correction term.
-/

noncomputable section

set_option maxHeartbeats 1000000

namespace RHTower

open Filter
open scoped Topology InnerProduct InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

omit [CompleteSpace E] in
/-- **Orthonormal sequences are weakly null.**  Bessel makes the coefficients square summable. -/
theorem tendsto_inner_orthonormal_atTop_zero {v : ℕ → E} (hv : Orthonormal ℂ v) (y : E) :
    Tendsto (fun n => ⟪v n, y⟫_ℂ) atTop (𝓝 0) := by
  have hsummable : Summable fun n => ‖⟪v n, y⟫_ℂ‖ ^ (2 : ℕ) :=
    Orthonormal.inner_products_summable y hv
  have hzero : Tendsto (fun n => ‖⟪v n, y⟫_ℂ‖ ^ (2 : ℕ)) atTop (𝓝 0) := hsummable.tendsto_atTop_zero
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hsq : Tendsto (fun n => Real.sqrt (‖⟪v n, y⟫_ℂ‖ ^ (2 : ℕ))) atTop (𝓝 0) := by
    have h := (Real.continuous_sqrt.tendsto (0 : ℝ)).comp hzero
    simpa [Function.comp_def] using h
  refine hsq.congr fun n => ?_
  rw [Real.sqrt_sq (norm_nonneg _)]

/-- Every continuous functional vanishes on an orthonormal sequence in the limit. -/
theorem tendsto_apply_orthonormal_atTop_zero {v : ℕ → E} (hv : Orthonormal ℂ v)
    (ℓ : E →L[ℂ] ℂ) : Tendsto (fun n => ℓ (v n)) atTop (𝓝 0) := by
  obtain ⟨z, hz⟩ : ∃ z : E, ∀ x : E, ℓ x = ⟪z, x⟫_ℂ :=
    ⟨(InnerProductSpace.toDual ℂ E).symm ℓ, fun x =>
      (InnerProductSpace.toDual_symm_apply (𝕜 := ℂ) (E := E)).symm⟩
  have hconj : Tendsto (fun n => (starRingEnd ℂ) ⟪v n, z⟫_ℂ) atTop (𝓝 0) := by
    have h := (tendsto_inner_orthonormal_atTop_zero hv z).star
    simpa using h
  refine hconj.congr fun n => ?_
  rw [hz (v n), ← inner_conj_symm]
  simp

/-- **A compact operator dies on an orthonormal sequence.** -/
theorem tendsto_norm_compactOperator_apply_orthonormal
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    {T : E →L[ℂ] F} (hT : IsCompactOperator T) {v : ℕ → E} (hv : Orthonormal ℂ v) :
    Tendsto (fun n => ‖T (v n)‖) atTop (𝓝 0) :=
  IsCompactOperator.norm_apply_tendsto_zero_of_bounded_weakly_null T hT v 1
    (fun n => le_of_eq (hv.1 n)) (fun ℓ => tendsto_apply_orthonormal_atTop_zero hv ℓ)

/-- The modes of a fixed shell are killed by every compact operator. -/
theorem tendsto_norm_compactOperator_apply_evenShellVectorEven
    {T : evenSubspace →L[ℂ] evenSubspace} (hT : IsCompactOperator T)
    (s t : ℝ) (hs : 0 < s) (hst : s < t) :
    Tendsto (fun n => ‖T (evenShellVectorEven s t hst n)‖) atTop (𝓝 0) :=
  tendsto_norm_compactOperator_apply_orthonormal hT
    (evenShellVectorEven_orthonormal s t hs hst)

/-- In particular the exact projection correction dies on the shell modes. -/
theorem tendsto_norm_evenSoninProjectionCorrection_apply_evenShellVectorEven
    (u : ℝ) (hu : 0 < u) (s t : ℝ) (hs : 0 < s) (hst : s < t) :
    Tendsto (fun n => ‖evenSoninProjectionCorrection u (evenShellVectorEven s t hst n)‖)
      atTop (𝓝 0) :=
  tendsto_norm_compactOperator_apply_evenShellVectorEven
    (IsSoninPrincipalRelativeIdeal.isCompactOperator
      (IsSoninPrincipalRelativeIdeal.projectionCorrection u hu)) s t hs hst

end RHTower
