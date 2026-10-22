import GaloisForLFunctions.RHTower.InfiniteMobiusCausalShift

/-!
# Isometric Möbius shift analysis map `L²(ℝ) → ℓ²(ℕ, L²(ℝ))`

For `σ > 1`, this module defines the analysis map sending `f ∈ L²(ℝ)` to the sequence
`n ↦ μ(n) √π_σ(n) · f(· - log n)`, where `π_σ(n) = n^{-σ} / ∑_{m squarefree} m^{-σ}` is the
squarefree probability weight. Since each shift is unitary and `∑ₙ |μ(n)|² π_σ(n) = 1`, the
sequence lies in `ℓ²` and the map is a linear isometry.

## Main results

- `norm_infiniteMobiusShiftAnalysisValue_sq`: `‖(μ(n) √π_σ(n) f(· - log n))ₙ‖² = ‖f‖²`.
- `infiniteMobiusShiftAnalysis`: the analysis map as a `ℂ`-linear isometry
  `L²(ℝ) →ₗᵢ ℓ²(ℕ, L²(ℝ))`.

## Hypotheses

Unconditional apart from the range hypothesis `hsigma : 1 < σ`, which makes the squarefree
weights summable.
-/

open Complex MeasureTheory
open scoped BigOperators

noncomputable section
namespace RHTower

/-- The channel space `ℓ²(ℕ, L²(ℝ))` of square-summable sequences of `L²(ℝ)` functions. -/
abbrev InfiniteMobiusShiftChannel :=
  lp (fun _ : ℕ => Lp ℂ 2 (volume : Measure ℝ)) 2

/-- For `σ > 1`, the channel sequence `n ↦ μ(n) √π_σ(n) · f(· - log n)` in `ℓ²(ℕ, L²(ℝ))`. -/
def infiniteMobiusShiftAnalysisValue
    (sigma : ℝ) (hsigma : 1 < sigma)
    (f : Lp ℂ 2 (volume : Measure ℝ)) : InfiniteMobiusShiftChannel :=
  ⟨fun n => infiniteMobiusSignedWeight sigma n •
      MellinL2.additiveTranslationUnitary (-Real.log n) f,
    (memℓp_gen_iff (by norm_num : 0 < (2 : ENNReal).toReal)).2 (by
      simpa only [ENNReal.toReal_ofNat, Real.rpow_two, norm_smul,
        LinearIsometryEquiv.norm_map, mul_pow,
        norm_infiniteMobiusSignedWeight_sq hsigma] using
        (summable_squarefreeMobiusProbability hsigma).mul_right (‖f‖ ^ 2))⟩

theorem infiniteMobiusShiftAnalysisValue_apply
    (sigma : ℝ) (hsigma : 1 < sigma)
    (f : Lp ℂ 2 (volume : Measure ℝ)) (n : ℕ) :
    infiniteMobiusShiftAnalysisValue sigma hsigma f n =
      infiniteMobiusSignedWeight sigma n •
        MellinL2.additiveTranslationUnitary (-Real.log n) f := rfl

/-- For `σ > 1`, the channel sequence has squared norm `‖f‖²`, because the weights
`|μ(n)|² π_σ(n)` sum to `1`. -/
theorem norm_infiniteMobiusShiftAnalysisValue_sq
    (sigma : ℝ) (hsigma : 1 < sigma)
    (f : Lp ℂ 2 (volume : Measure ℝ)) :
    ‖infiniteMobiusShiftAnalysisValue sigma hsigma f‖ ^ 2 = ‖f‖ ^ 2 := by
  have hnorm := lp.norm_rpow_eq_tsum
    (p := (2 : ENNReal)) (by norm_num : 0 < (2 : ENNReal).toReal)
    (infiniteMobiusShiftAnalysisValue sigma hsigma f)
  simp only [ENNReal.toReal_ofNat, Real.rpow_two] at hnorm
  rw [hnorm]
  simp only [infiniteMobiusShiftAnalysisValue_apply, norm_smul,
    LinearIsometryEquiv.norm_map, mul_pow,
    norm_infiniteMobiusSignedWeight_sq hsigma]
  rw [tsum_mul_right, tsum_squarefreeMobiusProbability hsigma, one_mul]

/-- For `σ > 1`, the channel sequence has norm `‖f‖`. -/
theorem norm_infiniteMobiusShiftAnalysisValue
    (sigma : ℝ) (hsigma : 1 < sigma)
    (f : Lp ℂ 2 (volume : Measure ℝ)) :
    ‖infiniteMobiusShiftAnalysisValue sigma hsigma f‖ = ‖f‖ := by
  nlinarith [norm_infiniteMobiusShiftAnalysisValue_sq sigma hsigma f,
    norm_nonneg (infiniteMobiusShiftAnalysisValue sigma hsigma f), norm_nonneg f]

/-- For `σ > 1`, the Möbius shift analysis map `L²(ℝ) →ₗᵢ ℓ²(ℕ, L²(ℝ))`,
`f ↦ (μ(n) √π_σ(n) f(· - log n))ₙ`, as a linear isometry. -/
def infiniteMobiusShiftAnalysis
    (sigma : ℝ) (hsigma : 1 < sigma) :
    Lp ℂ 2 (volume : Measure ℝ) →ₗᵢ[ℂ] InfiniteMobiusShiftChannel where
  toFun := infiniteMobiusShiftAnalysisValue sigma hsigma
  map_add' f g := by
    apply lp.ext
    funext n
    simp only [infiniteMobiusShiftAnalysisValue_apply, map_add, smul_add,
      lp.coeFn_add, Pi.add_apply]
  map_smul' c f := by
    apply lp.ext
    funext n
    simp only [infiniteMobiusShiftAnalysisValue_apply, map_smul,
      lp.coeFn_smul, Pi.smul_apply, RingHom.id_apply]
    rw [smul_smul, mul_comm, ← smul_smul]
  norm_map' := norm_infiniteMobiusShiftAnalysisValue sigma hsigma

theorem infiniteMobiusShiftAnalysis_apply
    (sigma : ℝ) (hsigma : 1 < sigma)
    (f : Lp ℂ 2 (volume : Measure ℝ)) (n : ℕ) :
    infiniteMobiusShiftAnalysis sigma hsigma f n =
      infiniteMobiusSignedWeight sigma n •
        MellinL2.additiveTranslationUnitary (-Real.log n) f := rfl

end RHTower
