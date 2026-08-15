import GaloisForLFunctions.RHTower.GammaJumpMultiplierBounds
import GaloisForLFunctions.HTGeometry.VectorL2FourierMultiplier

/-!
# The Gamma jump operator as a first-order Fourier multiplier

The Gamma jump symbol is real, nonnegative, continuous and at most affine:

`0 ≤ r(η) ≤ S(1 + |η|)`,   `S = Σ_{n≥1} n^{-2}`.

Dividing by the first-order weight therefore leaves a bounded symbol, so the jump operator is the
composition of the first-order weight with a bounded Fourier multiplier of norm at most `S`.  On
Hilbert-space-valued `L²` this is the exact domain statement

`R : H¹(ℝ;X) → L²(ℝ;X)`,

and, because the symbol is nonnegative, the normalized multiplier is accretive: the real part of its
`L²` inner product against any function is nonnegative.
-/

noncomputable section

namespace GaloisForLFunctions.RHTower

open MeasureTheory Complex

open scoped ENNReal

/-- The constant `Σ_{n≥1} n^{-2}` bounding the jump symbol. -/
def gammaJumpConst : ℝ := ∑' n : ℕ, (1 : ℝ) / (((n : ℝ) + 1) ^ 2)

theorem gammaJumpConst_nonneg : 0 ≤ gammaJumpConst :=
  tsum_nonneg fun n => by positivity

/-- The jump symbol is continuous, being differentiable everywhere. -/
theorem continuous_gammaJumpMultiplier : Continuous gammaJumpMultiplier :=
  continuous_iff_continuousAt.mpr fun η => (hasDerivAt_gammaJumpMultiplier η).continuousAt

/-- The jump symbol divided by the first-order weight. -/
def gammaJumpNormalizedSymbol (ξ : ℝ) : ℂ :=
  ((gammaJumpMultiplier ξ / (1 + |ξ|) : ℝ) : ℂ)

theorem continuous_gammaJumpNormalizedSymbol : Continuous gammaJumpNormalizedSymbol := by
  refine Complex.continuous_ofReal.comp (Continuous.div continuous_gammaJumpMultiplier ?_ ?_)
  · exact continuous_const.add continuous_abs
  · intro ξ
    positivity

theorem measurable_gammaJumpNormalizedSymbol : Measurable gammaJumpNormalizedSymbol :=
  continuous_gammaJumpNormalizedSymbol.measurable

/-- **The normalized jump symbol is bounded by `S`.** -/
theorem norm_gammaJumpNormalizedSymbol_le (ξ : ℝ) :
    ‖gammaJumpNormalizedSymbol ξ‖ ≤ gammaJumpConst := by
  have hden : (0 : ℝ) < 1 + |ξ| := by positivity
  have hbound : |gammaJumpMultiplier ξ| ≤ gammaJumpConst * (1 + |ξ|) :=
    abs_gammaJumpMultiplier_le ξ
  rw [gammaJumpNormalizedSymbol, Complex.norm_real, Real.norm_eq_abs, abs_div,
    abs_of_pos hden, div_le_iff₀ hden]
  exact hbound

/-- The normalized jump symbol is a nonnegative real number at every frequency. -/
theorem gammaJumpNormalizedSymbol_nonneg (ξ : ℝ) :
    ∃ v : ℝ, 0 ≤ v ∧ gammaJumpNormalizedSymbol ξ = (v : ℂ) := by
  refine ⟨gammaJumpMultiplier ξ / (1 + |ξ|), ?_, rfl⟩
  have hden : (0 : ℝ) < 1 + |ξ| := by positivity
  exact div_nonneg (gammaJumpMultiplier_nonneg ξ) hden.le

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]

omit [CompleteSpace X] in
/-- **`(19)`: the jump operator factors through the first-order weight.**  The `L²` seminorm of the
jump multiple is bounded by `S` times the `L²` seminorm of the first-order multiple; this is the
quantitative form of `R : H¹(ℝ;X) → L²(ℝ;X)`. -/
theorem eLpNorm_gammaJumpMultiplier_smul_le (u : ℝ → X) :
    eLpNorm (fun ξ => ((gammaJumpMultiplier ξ : ℝ) : ℂ) • u ξ) 2 volume
      ≤ ENNReal.ofReal gammaJumpConst *
          eLpNorm (fun ξ => (((1 + |ξ| : ℝ)) : ℂ) • u ξ) 2 volume := by
  have hfac : ∀ ξ : ℝ, ((gammaJumpMultiplier ξ : ℝ) : ℂ) • u ξ
      = gammaJumpNormalizedSymbol ξ • ((((1 + |ξ| : ℝ)) : ℂ) • u ξ) := by
    intro ξ
    have hden : (0 : ℝ) < 1 + |ξ| := by positivity
    rw [gammaJumpNormalizedSymbol, smul_smul, ← Complex.ofReal_mul,
      div_mul_cancel₀ _ hden.ne']
  have hcongr : eLpNorm (fun ξ => ((gammaJumpMultiplier ξ : ℝ) : ℂ) • u ξ) 2 volume
      = eLpNorm (fun ξ => gammaJumpNormalizedSymbol ξ • ((((1 + |ξ| : ℝ)) : ℂ) • u ξ))
          2 volume := by
    congr 1
    funext ξ
    exact hfac ξ
  rw [hcongr]
  exact eLpNorm_smul_le_of_bound (p := 2) (μ := (volume : Measure ℝ))
    gammaJumpConst_nonneg norm_gammaJumpNormalizedSymbol_le _

/-- The bounded Fourier multiplier of the normalized jump symbol on `L²(ℝ;X)`. -/
def gammaJumpNormalizedMulCLM :
    Lp (α := ℝ) X 2 →L[ℂ] Lp (α := ℝ) X 2 :=
  HTGeometry.vectorFourierMulCLM (F := X) measurable_gammaJumpNormalizedSymbol
    gammaJumpConst_nonneg norm_gammaJumpNormalizedSymbol_le

/-- **The normalized jump multiplier has operator norm at most `S`.** -/
theorem norm_gammaJumpNormalizedMulCLM_le :
    ‖(gammaJumpNormalizedMulCLM : Lp (α := ℝ) X 2 →L[ℂ] Lp (α := ℝ) X 2)‖ ≤ gammaJumpConst :=
  HTGeometry.norm_vectorFourierMulCLM_le (F := X) measurable_gammaJumpNormalizedSymbol
    gammaJumpConst_nonneg norm_gammaJumpNormalizedSymbol_le

/-- **`(21)`: the jump operator is accretive.**  Because the symbol is nonnegative, the real part of
the `L²` inner product of a function with its normalized jump multiple is nonnegative. -/
theorem re_inner_gammaJumpNormalizedMulCLM_nonneg (f : Lp (α := ℝ) X 2) :
    0 ≤ (inner ℂ (gammaJumpNormalizedMulCLM (X := X) f) f : ℂ).re := by
  have hunit : (inner ℂ (gammaJumpNormalizedMulCLM (X := X) f) f : ℂ)
      = inner ℂ (lpBoundedSmulCLM (p := 2) (μ := (volume : Measure ℝ)) (H := X)
            measurable_gammaJumpNormalizedSymbol gammaJumpConst_nonneg
            norm_gammaJumpNormalizedSymbol_le
            (HTGeometry.vectorFourierL2 ℝ X f))
          (HTGeometry.vectorFourierL2 ℝ X f) := by
    have hmap := (Lp.fourierTransformₗᵢ ℝ X).inner_map_map
      (HTGeometry.vectorFourierL2inv ℝ X
        (lpBoundedSmulCLM (p := 2) (μ := (volume : Measure ℝ)) (H := X)
          measurable_gammaJumpNormalizedSymbol gammaJumpConst_nonneg
          norm_gammaJumpNormalizedSymbol_le (HTGeometry.vectorFourierL2 ℝ X f))) f
    rw [gammaJumpNormalizedMulCLM, HTGeometry.vectorFourierMulCLM_apply]
    rw [← hmap]
    congr 1
    exact HTGeometry.vectorFourierL2_vectorFourierL2inv _
  rw [hunit]
  exact HTGeometry.re_inner_lpBoundedSmulCLM_nonneg (F := X)
    measurable_gammaJumpNormalizedSymbol gammaJumpConst_nonneg
    norm_gammaJumpNormalizedSymbol_le gammaJumpNormalizedSymbol_nonneg _

end GaloisForLFunctions.RHTower
