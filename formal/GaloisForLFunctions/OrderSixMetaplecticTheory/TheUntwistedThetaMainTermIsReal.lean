import GaloisForLFunctions.OrderSixMetaplecticTheory.ComplexConjugationActsOnTheCubicSymbols
import GaloisForLFunctions.SpectralTheoryOfTheCubicCover.TheUntwistedThetaSeriesHasASmoothedMainTerm

/-!
# The main term of the untwisted theta series is real

Complex conjugation `A ↦ Ā` preserves norms and squarefreeness and conjugates the theta-square weight
(`thetaSquareWeight_conj`). So the Gaussian-smoothed untwisted sum
`G(X) = Σ_A a(A) φ(log(N A / X))` is real for every `X` (`star_gaussianSmoothedUntwistedTheta`), and the
coefficient `κ` of its main term `X^{2/3} κ` (remainder `O(X^{13/20})`) is real
(`thetaGaussianMainCoefficient_im`). Hence the residue `R = e^{−4/9} κ` of `S₁` at `2/3` is real
(`untwistedThetaResidue_im`).

The Mellin factor `M(4/3) = ∫₀^∞ t^{1/3} K_{1/3}(t)² dt` of the residue is real
(`star_besselSqMellin_four_thirds`).
-/

noncomputable section

open Filter Topology MeasureTheory

namespace GaloisForLFunctions.OrderSixMetaplecticTheory

open MetaplecticMobiusDescent MetaplecticMobiusDescent.Eisenstein MetaplecticMobiusDescent.CubicEisenstein
  SpectralTheoryOfTheCubicCover FamilyContinuationTheory.EisensteinNorm

theorem untwistedSquarefreeCoefficient_conj (A : Ideal O) :
    untwistedSquarefreeCoefficient (conjIdeal A) =
      star (untwistedSquarefreeCoefficient A) := by
  have hiff : (Squarefree (conjIdeal A) ∧ primaryIdealGenerator (conjIdeal A) ≠ 0) ↔
      (Squarefree A ∧ primaryIdealGenerator A ≠ 0) := by
    rw [squarefree_conjIdeal_iff, primaryIdealGenerator_conj]
    exact and_congr_right' (not_congr (map_eq_zero_iff _ conjO.injective))
  unfold untwistedSquarefreeCoefficient
  by_cases h : Squarefree A ∧ primaryIdealGenerator A ≠ 0
  · rw [if_pos (hiff.mpr h), if_pos h, thetaSquareWeight_conj]
  · rw [if_neg (mt hiff.mp h), if_neg h, star_zero]


/-! ### The smoothed sum and its main term are real -/

/-- **The smoothed untwisted theta sum is real.** Conjugate ideals carry conjugate weights. -/
theorem star_gaussianSmoothedUntwistedTheta (X : ℝ) :
    star (gaussianSmoothedUntwistedTheta X) = gaussianSmoothedUntwistedTheta X := by
  let f : Ideal O → ℂ := fun A => untwistedSquarefreeCoefficient A *
    (RHTower.smoothAFELogGaussian (Real.log ((Ideal.absNorm A : ℝ) / X)) : ℂ)
  change star (∑' A, f A) = ∑' A, f A
  calc star (∑' A, f A) = ∑' A, star (f A) := tsum_star
    _ = ∑' A, f (conjIdealEquiv.toEquiv A) := by
        congr 1
        funext A
        change _ = untwistedSquarefreeCoefficient (conjIdeal A) *
          (RHTower.smoothAFELogGaussian (Real.log ((Ideal.absNorm (conjIdeal A) : ℝ) / X)) : ℂ)
        rw [untwistedSquarefreeCoefficient_conj, absNorm_conjIdeal, star_mul', Complex.star_def,
          Complex.conj_ofReal]
    _ = ∑' A, f A := conjIdealEquiv.toEquiv.tsum_eq f

/-- **The main coefficient of the smoothed untwisted sum is real.** -/
theorem thetaGaussianMainCoefficient_im : thetaGaussianMainCoefficient.im = 0 := by
  obtain ⟨C, -, hbound⟩ := gaussianSmoothedUntwistedTheta_main_term (13 / 20) (by norm_num) (by norm_num)
  have key : ∀ X : ℝ, 1 ≤ X → |thetaGaussianMainCoefficient.im| ≤ C * X ^ (-(1 / 60 : ℝ)) := by
    intro X hX
    have hX0 : 0 < X := lt_of_lt_of_le zero_lt_one hX
    have hG : (gaussianSmoothedUntwistedTheta X).im = 0 := by
      have h := congrArg Complex.im (star_gaussianSmoothedUntwistedTheta X)
      rw [Complex.star_def, Complex.conj_im] at h
      linarith
    have hpow : (X : ℂ) ^ (2 / 3 : ℂ) = ((X ^ (2 / 3 : ℝ) : ℝ) : ℂ) := by
      rw [Complex.ofReal_cpow hX0.le]
      norm_num
    have hp : 0 < X ^ (2 / 3 : ℝ) := Real.rpow_pos_of_pos hX0 _
    have him : X ^ (2 / 3 : ℝ) * |thetaGaussianMainCoefficient.im| ≤ C * X ^ (13 / 20 : ℝ) := by
      calc X ^ (2 / 3 : ℝ) * |thetaGaussianMainCoefficient.im|
          = |(gaussianSmoothedUntwistedTheta X - (X : ℂ) ^ (2 / 3 : ℂ) * thetaGaussianMainCoefficient).im| := by
            rw [Complex.sub_im, hG, hpow, Complex.im_ofReal_mul, zero_sub, abs_neg, abs_mul, abs_of_pos hp]
        _ ≤ ‖gaussianSmoothedUntwistedTheta X - (X : ℂ) ^ (2 / 3 : ℂ) * thetaGaussianMainCoefficient‖ :=
            Complex.abs_im_le_norm _
        _ ≤ C * X ^ (13 / 20 : ℝ) := hbound X hX
    have hsplit : X ^ (13 / 20 : ℝ) = X ^ (2 / 3 : ℝ) * X ^ (-(1 / 60 : ℝ)) := by
      rw [← Real.rpow_add hX0]
      norm_num
    rw [hsplit, mul_left_comm] at him
    exact le_of_mul_le_mul_left him hp
  have hlim : Tendsto (fun X : ℝ => C * X ^ (-(1 / 60 : ℝ))) atTop (𝓝 0) := by
    simpa using (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 60)).const_mul C
  exact abs_nonpos_iff.mp (ge_of_tendsto hlim (eventually_atTop.mpr ⟨1, key⟩))

/-- **The residue of `S₁` at `2/3` is real.** -/
theorem untwistedThetaResidue_im : untwistedThetaResidue.im = 0 := by
  have h := thetaGaussianMainCoefficient_im
  have he : Complex.exp ((2 / 3 : ℂ) ^ 2) = ((Real.exp (4 / 9) : ℝ) : ℂ) := by
    rw [Complex.ofReal_exp]
    norm_num
  rw [thetaGaussianMainCoefficient, he, Complex.im_ofReal_mul] at h
  exact (mul_eq_zero.mp h).resolve_left (Real.exp_pos _).ne'


/-- `M(4/3) = ∫₀^∞ t^{1/3} K_{1/3}(t)² dt` is real. -/
theorem star_besselSqMellin_four_thirds : star (besselSqMellin (4 / 3)) = besselSqMellin (4 / 3) := by
  unfold besselSqMellin mellin
  rw [Complex.star_def, ← integral_conj]
  refine setIntegral_congr_fun measurableSet_Ioi fun t (ht : 0 < t) => ?_
  have hK : (starRingEnd ℂ) (schlafliBesselK (1 / 3) t) = schlafliBesselK (1 / 3) t :=
    star_schlafliBesselK_cubic t ht
  simp only [besselSq, smul_eq_mul, map_mul, map_pow, hK]
  rw [show (4 / 3 : ℂ) - 1 = ((1 / 3 : ℝ) : ℂ) by push_cast; ring, ← Complex.ofReal_cpow ht.le,
    Complex.conj_ofReal]

end GaloisForLFunctions.OrderSixMetaplecticTheory
