import GaloisForLFunctions.RHTower.FieldOneFiniteStageClassSonin
import Mathlib.Analysis.InnerProductSpace.Projection.Basic

/-!
# §VIII: Connes' band `B_Λ` and the projection `Q_Λ` on `L²(X_S)`

§VIII, Corollary 2 and Theorem 5 of

  A. Connes, *Trace formula in noncommutative geometry and the zeros of the Riemann zeta
  function*, arXiv:math/9811068:

  "Let `Q_Λ` be the orthogonal projection on the subspace of `L²(X_S)` spanned by the
  `f ∈ 𝒮(A_S)` which vanish as well as their Fourier transform for `|x| > Λ`."

The corpus already owns the adelic carrier for `k = ℚ` at a finite stage `S`: the class space
`X_S`, its `L²`, the sharp source cut-off `P_Λ` (multiplication by the indicator of the aperture
`{|x|_S ≤ Λ}`) and the semilocal Fourier unitary.  This module assembles Connes' band out of them:

* `connesAdelicBand` - `B_Λ = Range P_Λ ∩ Range P̂_Λ`, as the intersection of two kernels;
* `connes_mem_adelicBand_iff` - the fixed-point description `P_Λ f = f ∧ P_Λ (F f) = F f`;
* `connes_mem_adelicBand_iff_ae` - Connes' literal description: `f` and `F f` both vanish
  almost everywhere for `|x|_S > Λ`;
* `connesAdelicBand_isClosed` and `connesAdelicProjection` - the projection `Q_Λ`.

This is brick 1 of the Theorem 4 / Theorem 5 assembly.
-/

open MeasureTheory Set IsDedekindDomain

namespace GaloisForLFunctions.RHTower

noncomputable section

variable (S : Finset (HeightOneSpectrum ℤ)) (lam : ℝ)

/-- The sharp cut-off `P_Λ` fixes exactly the vectors supported in the aperture. -/
theorem connes_supportCutoff_eq_self_iff (f : FieldOneFiniteStageClassL2 S) :
    fieldOneFiniteStageClassSupportCutoff S lam f = f
      ↔ (fun x => f x)
          =ᵐ[fieldOneFiniteStageClassAdditiveMeasure S]
            (fieldOneFiniteStageClassAperture S lam).indicator fun x => f x := by
  constructor
  · intro h
    have hae := fieldOneFiniteStageClassSupportCutoff_ae S lam f
    rw [h] at hae
    exact hae
  · intro hae
    apply Lp.ext
    filter_upwards [fieldOneFiniteStageClassSupportCutoff_ae S lam f, hae] with x h1 h3
    rw [h1, ← h3]

/-- **§VIII.**  Connes' band `B_Λ ⊆ L²(X_S)`: the vectors that vanish, together with their
Fourier transform, beyond the cut-off. -/
def connesAdelicBand : Submodule ℂ (FieldOneFiniteStageClassL2 S) :=
  LinearMap.ker
      (ContinuousLinearMap.id ℂ (FieldOneFiniteStageClassL2 S)
        - fieldOneFiniteStageClassSupportCutoff S lam).toLinearMap
    ⊓ LinearMap.ker
      ((ContinuousLinearMap.id ℂ (FieldOneFiniteStageClassL2 S)
          - fieldOneFiniteStageClassSupportCutoff S lam)
        ∘L (fieldOneFiniteStageClassFourierUnitary S).toLinearIsometry.toContinuousLinearMap
        ).toLinearMap

/-- **§VIII, the fixed-point description of `B_Λ`.** -/
theorem connes_mem_adelicBand_iff (f : FieldOneFiniteStageClassL2 S) :
    f ∈ connesAdelicBand S lam
      ↔ fieldOneFiniteStageClassSupportCutoff S lam f = f
        ∧ fieldOneFiniteStageClassSupportCutoff S lam
            (fieldOneFiniteStageClassFourierUnitary S f)
          = fieldOneFiniteStageClassFourierUnitary S f := by
  constructor
  · rintro ⟨h1, h2⟩
    have e1 : f - fieldOneFiniteStageClassSupportCutoff S lam f = 0 := h1
    have e2 : fieldOneFiniteStageClassFourierUnitary S f
        - fieldOneFiniteStageClassSupportCutoff S lam
            (fieldOneFiniteStageClassFourierUnitary S f) = 0 := h2
    exact ⟨(sub_eq_zero.mp e1).symm, (sub_eq_zero.mp e2).symm⟩
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · show f - fieldOneFiniteStageClassSupportCutoff S lam f = 0
      rw [h1, sub_self]
    · show fieldOneFiniteStageClassFourierUnitary S f
        - fieldOneFiniteStageClassSupportCutoff S lam
            (fieldOneFiniteStageClassFourierUnitary S f) = 0
      rw [h2, sub_self]

/-- **§VIII, Connes' literal description of `B_Λ`.**  `f` and `F f` both vanish almost everywhere
for `|x|_S > Λ`. -/
theorem connes_mem_adelicBand_iff_ae (f : FieldOneFiniteStageClassL2 S) :
    f ∈ connesAdelicBand S lam
      ↔ ((fun x => f x)
            =ᵐ[fieldOneFiniteStageClassAdditiveMeasure S]
              (fieldOneFiniteStageClassAperture S lam).indicator fun x => f x)
        ∧ ((fun x => (fieldOneFiniteStageClassFourierUnitary S f) x)
            =ᵐ[fieldOneFiniteStageClassAdditiveMeasure S]
              (fieldOneFiniteStageClassAperture S lam).indicator
                fun x => (fieldOneFiniteStageClassFourierUnitary S f) x) := by
  rw [connes_mem_adelicBand_iff, connes_supportCutoff_eq_self_iff,
    connes_supportCutoff_eq_self_iff]

theorem connesAdelicBand_isClosed :
    IsClosed (SetLike.coe (connesAdelicBand S lam)) := by
  have h1 : IsClosed (SetLike.coe (LinearMap.ker
      (ContinuousLinearMap.id ℂ (FieldOneFiniteStageClassL2 S)
        - fieldOneFiniteStageClassSupportCutoff S lam).toLinearMap)) :=
    (ContinuousLinearMap.id ℂ (FieldOneFiniteStageClassL2 S)
      - fieldOneFiniteStageClassSupportCutoff S lam).isClosed_ker
  have h2 : IsClosed (SetLike.coe (LinearMap.ker
      ((ContinuousLinearMap.id ℂ (FieldOneFiniteStageClassL2 S)
          - fieldOneFiniteStageClassSupportCutoff S lam)
        ∘L (fieldOneFiniteStageClassFourierUnitary S).toLinearIsometry.toContinuousLinearMap
        ).toLinearMap)) :=
    ((ContinuousLinearMap.id ℂ (FieldOneFiniteStageClassL2 S)
        - fieldOneFiniteStageClassSupportCutoff S lam)
      ∘L (fieldOneFiniteStageClassFourierUnitary S).toLinearIsometry.toContinuousLinearMap
      ).isClosed_ker
  exact h1.inter h2

theorem connesAdelicBand_completeSpace : CompleteSpace (connesAdelicBand S lam) :=
  (connesAdelicBand_isClosed S lam).completeSpace_coe

/-- **§VIII, `Q_Λ`.**  The orthogonal projection of `L²(X_S)` onto Connes' band. -/
def connesAdelicProjection :
    FieldOneFiniteStageClassL2 S →L[ℂ] FieldOneFiniteStageClassL2 S :=
  haveI : CompleteSpace (connesAdelicBand S lam) := connesAdelicBand_completeSpace S lam
  Submodule.starProjection (connesAdelicBand S lam)

end

end GaloisForLFunctions.RHTower
