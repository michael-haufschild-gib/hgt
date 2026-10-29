import GaloisForLFunctions.ArithmeticIndexDescent.TheSquarePrimeBoundaryIsLowerOrder
import Mathlib.Analysis.Calculus.DSlope

/-!
# A Gamma and mass bound for the centred square-prime multiplier

The first Gauss-series term gives a quadratic Gamma floor near zero.
The square multiplier's continuous divided difference controls its centred
value on compact intervals. Combined with its sub-Gamma growth at infinity,
Young's inequality charges arbitrarily little Gamma to either factor and
ordinary square mass to only the second factor.
-/

noncomputable section
open Complex Real Filter Set
open RHTower

namespace GaloisForLFunctions.ArithmeticIndexDescent

theorem differentiable_squarePrimeRegularSymbol : Differentiable ℝ squarePrimeRegularSymbol := by
  intro t
  have hreg : DifferentiableAt ℂ Sieve.zetaLogDerivReg
      ((1 : ℂ) + 2 * (t : ℂ) * I) := by
    by_cases hs : (1 : ℂ) + 2 * (t : ℂ) * I = 1
    · rw [hs]
      exact Sieve.differentiableAt_zetaLogDerivReg_one
    · exact Sieve.differentiableAt_zetaLogDerivReg
        ((Sieve.zetaResidueUnit_ne_zero_iff hs).mpr
          (riemannZeta_ne_zero_of_one_le_re (by simp)))
  have hpath : DifferentiableAt ℝ (fun x : ℝ => (1 : ℂ) + 2 * (x : ℂ) * I) t := by
    fun_prop
  have hcomp := (hreg.restrictScalars ℝ).comp t hpath
  have hre := Complex.reCLM.differentiableAt.comp t hcomp
  exact hre.const_mul 2

theorem continuous_squarePrimeRegularSymbol : Continuous squarePrimeRegularSymbol :=
  differentiable_squarePrimeRegularSymbol.continuous

/-- The first positive term of the digamma difference controls the quadratic behaviour at zero. -/
theorem sixteen_mul_sq_div_le_gammaIncrementSymbol (t : ℝ) :
    16 * t ^ 2 / (1 + 4 * t ^ 2) ≤ gammaIncrementSymbol t := by
  have hs := Complex.hasSum_digammaRealDifferenceTerm
    (show (0 : ℝ) < 1 / 4 by norm_num) (t / 2)
  have hterm := hs.summable.sum_le_tsum ({0} : Finset ℕ)
    (fun j _ => Complex.digammaRealDifferenceTerm_nonneg (by norm_num) (t / 2) j)
  rw [Finset.sum_singleton, hs.tsum_eq] at hterm
  have harg : (((1 / 4 : ℝ) : ℂ) + ((t / 2 : ℝ) : ℂ) * I) =
      (1 / 4 : ℂ) + I * (t : ℂ) / 2 := by push_cast; ring
  have hquarter : ((1 / 4 : ℝ) : ℂ) = (1 / 4 : ℂ) := by norm_num
  rw [harg, hquarter] at hterm
  rw [gammaIncrementSymbol_eq_digamma]
  refine le_trans ?_ hterm
  apply le_of_eq
  unfold Complex.digammaRealDifferenceTerm
  norm_num only [Nat.cast_zero, add_zero]
  have hd : 1 + 4 * t ^ 2 ≠ 0 := ne_of_gt (by positivity)
  have hd' : (1 / 4 : ℝ) ^ 2 + (t / 2) ^ 2 ≠ 0 := ne_of_gt (by positivity)
  field_simp
  ring

/-- A centred regular square multiplier is bounded by a square root of Gamma on every compact interval. -/
theorem exists_centeredSquare_sq_le_gamma_on_compact {R : ℝ} (hR : 0 ≤ R) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ t : ℝ, |t| ≤ R →
      (squarePrimeRegularSymbol t - squarePrimeRegularSymbol 0) ^ 2 ≤
        K * gammaIncrementSymbol t := by
  have hc : Continuous (dslope squarePrimeRegularSymbol 0) := by
    rw [continuous_iff_continuousAt]
    intro t
    by_cases ht : t = 0
    · subst t
      exact continuousAt_dslope_same.mpr (differentiable_squarePrimeRegularSymbol 0)
    · exact (continuousAt_dslope_of_ne ht).mpr continuous_squarePrimeRegularSymbol.continuousAt
  obtain ⟨z, _, hmax⟩ := (isCompact_Icc (a := -R) (b := R)).exists_isMaxOn
    ⟨0, by constructor <;> linarith only [hR]⟩ hc.abs.continuousOn
  refine ⟨|dslope squarePrimeRegularSymbol 0 z| ^ 2 * ((1 + 4 * R ^ 2) / 16),
    by positivity, ?_⟩
  intro t ht
  have hb : |dslope squarePrimeRegularSymbol 0 t| ≤ |dslope squarePrimeRegularSymbol 0 z| :=
    hmax (abs_le.mp ht)
  have hb2 := (sq_le_sq₀ (abs_nonneg _) (abs_nonneg _)).mpr hb
  rw [sq_abs, sq_abs] at hb2
  have htR2 := (sq_le_sq₀ (abs_nonneg t) hR).mpr ht
  rw [sq_abs] at htR2
  have hquad := (div_le_iff₀ (by positivity : 0 < 1 + 4 * t ^ 2)).mp
    (sixteen_mul_sq_div_le_gammaIncrementSymbol t)
  have hmono := mul_le_mul_of_nonneg_left
    (show 1 + 4 * t ^ 2 ≤ 1 + 4 * R ^ 2 by linarith only [htR2])
    (gammaIncrementSymbol_nonneg t)
  have htpay : t ^ 2 ≤ ((1 + 4 * R ^ 2) / 16) * gammaIncrementSymbol t := by
    nlinarith only [hquad, hmono]
  have heq : squarePrimeRegularSymbol t - squarePrimeRegularSymbol 0 =
      t * dslope squarePrimeRegularSymbol 0 t := by
    simpa only [sub_zero, smul_eq_mul] using (sub_smul_dslope squarePrimeRegularSymbol 0 t).symm
  rw [heq, mul_pow]
  calc t ^ 2 * dslope squarePrimeRegularSymbol 0 t ^ 2
      ≤ t ^ 2 * dslope squarePrimeRegularSymbol 0 z ^ 2 :=
        mul_le_mul_of_nonneg_left hb2 (sq_nonneg t)
    _ ≤ (((1 + 4 * R ^ 2) / 16) * gammaIncrementSymbol t) *
        dslope squarePrimeRegularSymbol 0 z ^ 2 :=
          mul_le_mul_of_nonneg_right htpay (sq_nonneg _)
    _ = _ := by rw [sq_abs]; ring

/-- Subtracting the value at zero preserves the arbitrarily small Gamma bound at infinity. -/
theorem exists_centeredSquare_abs_le_epsilon_gamma {ε : ℝ} (hε : 0 < ε) :
    ∃ T : ℝ, 2 ≤ T ∧ ∀ t : ℝ, T ≤ |t| →
      |squarePrimeRegularSymbol t - squarePrimeRegularSymbol 0| ≤
        ε * gammaIncrementSymbol t := by
  obtain ⟨TM, hTM, hm⟩ := exists_squarePrime_regular_abs_le_epsilon_gamma
    (show 0 < ε / 2 by positivity)
  obtain ⟨TG, hTG, hg⟩ := exists_half_log_le_gammaIncrement
  refine ⟨max (max TM TG) (Real.exp (4 * |squarePrimeRegularSymbol 0| / ε)),
    hTM.trans ((le_max_left _ _).trans (le_max_left _ _)), ?_⟩
  intro t ht
  have htMG : max TM TG ≤ |t| := (le_max_left _ _).trans ht
  have htM : TM ≤ |t| := (le_max_left _ _).trans htMG
  have htG : TG ≤ |t| := (le_max_right _ _).trans htMG
  have hte : Real.exp (4 * |squarePrimeRegularSymbol 0| / ε) ≤ |t| :=
    (le_max_right _ _).trans ht
  have hlog : 4 * |squarePrimeRegularSymbol 0| ≤ ε * Real.log |t| := by
    have hh := Real.log_le_log (Real.exp_pos _) hte
    rw [Real.log_exp] at hh
    have hp := (div_le_iff₀ hε).mp hh
    linarith only [hp]
  have hgpay := mul_le_mul_of_nonneg_left (hg t htG) hε.le
  have hconst : |squarePrimeRegularSymbol 0| ≤ ε / 2 * gammaIncrementSymbol t := by
    linarith only [hlog, hgpay]
  have htri : |squarePrimeRegularSymbol t - squarePrimeRegularSymbol 0| ≤
      |squarePrimeRegularSymbol t| + |squarePrimeRegularSymbol 0| := by
    simpa only [sub_eq_add_neg, abs_neg] using
      abs_add_le (squarePrimeRegularSymbol t) (-squarePrimeRegularSymbol 0)
  linarith only [htri, hm t htM, hconst]

private theorem two_mul_le_add_of_square {x A B : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hx : x ^ 2 ≤ A * B) : 2 * x ≤ A + B := by
  by_contra hh
  have hlt : A + B < 2 * x := lt_of_not_ge hh
  have hsq := (sq_lt_sq₀ (add_nonneg hA hB)
    (show 0 ≤ 2 * x by linarith only [hlt, hA, hB])).mpr hlt
  nlinarith only [hsq, hx, sq_nonneg (A - B)]

private theorem low_square_young {ε K G D : ℝ} (hε : 0 < ε) (hK : 0 ≤ K) (hG : 0 ≤ G)
    (hD : D ^ 2 ≤ K * G) (a b : ℝ) :
    2 * |D| * |a| * |b| ≤ ε * G * a ^ 2 + (K / ε) * b ^ 2 := by
  have hsq : (|D| * |a| * |b|) ^ 2 ≤
      (ε * G * a ^ 2) * ((K / ε) * b ^ 2) := by
    calc (|D| * |a| * |b|) ^ 2 = D ^ 2 * (a ^ 2 * b ^ 2) := by
          simp only [mul_pow, sq_abs]
          ring
      _ ≤ (K * G) * (a ^ 2 * b ^ 2) :=
        mul_le_mul_of_nonneg_right hD (mul_nonneg (sq_nonneg a) (sq_nonneg b))
      _ = _ := by field_simp [hε.ne']
  have hh := two_mul_le_add_of_square (by positivity : 0 ≤ ε * G * a ^ 2)
    (by positivity : 0 ≤ (K / ε) * b ^ 2) hsq
  linarith only [hh]

/-- The centred mixed square multiplier charges arbitrarily little Gamma and mass to only
the second factor. The bound is uniform over all frequencies and scalar amplitudes. -/
theorem exists_centeredSquare_gamma_mass_bound {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t a b : ℝ,
      2 * |squarePrimeRegularSymbol t - squarePrimeRegularSymbol 0| * |a| * |b| ≤
        ε * gammaIncrementSymbol t * (a ^ 2 + b ^ 2) + C * b ^ 2 := by
  obtain ⟨T, hT, hhigh⟩ := exists_centeredSquare_abs_le_epsilon_gamma hε
  obtain ⟨K, hK, hlow⟩ := exists_centeredSquare_sq_le_gamma_on_compact
    (show 0 ≤ T by linarith only [hT])
  refine ⟨K / ε, by positivity, ?_⟩
  intro t a b
  have hG := gammaIncrementSymbol_nonneg t
  rcases le_or_gt T |t| with ht | ht
  · have hm := hhigh t ht
    have hab : 2 * |a| * |b| ≤ a ^ 2 + b ^ 2 := by
      nlinarith only [sq_nonneg (|a| - |b|), sq_abs a, sq_abs b]
    calc 2 * |squarePrimeRegularSymbol t - squarePrimeRegularSymbol 0| * |a| * |b|
        ≤ 2 * (ε * gammaIncrementSymbol t) * |a| * |b| := by gcongr
      _ = (ε * gammaIncrementSymbol t) * (2 * |a| * |b|) := by ring
      _ ≤ (ε * gammaIncrementSymbol t) * (a ^ 2 + b ^ 2) :=
        mul_le_mul_of_nonneg_left hab (mul_nonneg hε.le hG)
      _ ≤ _ := le_add_of_nonneg_right (by positivity)
  · have hh := low_square_young hε hK hG (hlow t ht.le) a b
    have hpay : 0 ≤ ε * gammaIncrementSymbol t * b ^ 2 := by positivity
    linarith only [hh, hpay]

end GaloisForLFunctions.ArithmeticIndexDescent
