import GaloisForLFunctions.HTGeometry.LogarithmicLaplaceScoreTwelve
import GaloisForLFunctions.RHTower.ThetaCuspFactoredReflectionBound

/-!
# Complete signed likelihood and reflected bounds through twelve at scale eight

The full higher-likelihood measure has support at least three. At q >= 8,
the existing order-twelve scalar score bound applies throughout that support.
The leading-moment comparison gives the factor-six derivative ceiling and
an exact-first-atom convolution majorant for every reflected jet through twelve.
These error bounds alone do not assert compensated source positivity.
-/

open MeasureTheory Filter Topology
namespace RHTower
noncomputable section

/-- Signed finite cooling preserves positivity and is bounded by the leading spectral moment. -/
theorem thetaCuspCoolingJet_signed_le_leadingMoment_twelve {n : ℕ} (hn : n ≤ 12) {x : ℝ}
    (hq : 8 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    0 ≤ (-1 : ℝ)^n*thetaCuspCoolingJet n 0 x ∧
    (-1 : ℝ)^n*thetaCuspCoolingJet n 0 x ≤
      (2*thetaCuspSingleAtomReflectionScale 1 x)^n *
        thetaCuspHigherLikelihoodSpectralMoment (thetaCuspLikelihoodCoordinate x) n := by
  have hx := regimeOne_pos_of_six_le (by linarith)
  have hB := thetaCuspLikelihoodCoordinate_pos hx.le
  let q := thetaCuspSingleAtomReflectionScale 1 x
  have hq0 : 0 ≤ q := by dsimp [q]; linarith
  have hs := integrable_laplaceCoolingJet_mul_exp_higher n 0 hB
  rw [thetaCuspCoolingJet_eq_integral_score n 0 hB, ← integral_const_mul]
  constructor
  · apply integral_nonneg_of_ae
    filter_upwards [ae_three_le_thetaCuspHigherLikelihoodSpectralMeasure] with t ht
    have hqt : 24 ≤ q*t := by nlinarith
    have hb := (HTGeometry.laplaceCoolingJet_signed_bounds_twelve hn hqt).1
    have hm := mul_nonneg hb (Real.exp_pos (-thetaCuspLikelihoodCoordinate x*t)).le
    change 0 ≤ (-1 : ℝ)^n*(HTGeometry.laplaceCoolingJet n 0 (q*t)*
      Real.exp (-thetaCuspLikelihoodCoordinate x*t))
    nlinarith only [hm]
  · rw [thetaCuspHigherLikelihoodSpectralMoment_eq_integral, ← integral_const_mul]
    apply integral_mono_ae (hs.const_mul _)
      ((integrable_pow_mul_exp_neg_thetaCuspHigherLikelihoodSpectralMeasure n hB).const_mul _)
    filter_upwards [ae_three_le_thetaCuspHigherLikelihoodSpectralMeasure] with t ht
    have hqt : 24 ≤ q*t := by nlinarith
    have hb := (HTGeometry.laplaceCoolingJet_signed_bounds_twelve hn hqt).2
    have hm := mul_le_mul_of_nonneg_right hb (Real.exp_pos (-thetaCuspLikelihoodCoordinate x*t)).le
    change (-1 : ℝ)^n*(HTGeometry.laplaceCoolingJet n 0 (q*t)*
      Real.exp (-thetaCuspLikelihoodCoordinate x*t)) ≤
      (2*q)^n*(t^n*Real.exp (-thetaCuspLikelihoodCoordinate x*t))
    calc
      _ ≤ (2*(q*t))^n*Real.exp (-thetaCuspLikelihoodCoordinate x*t) := by nlinarith only [hm]
      _ = _ := by simp only [mul_pow]; ring

/-- Every required higher-likelihood derivative has its sharp leading-scale ceiling. -/
theorem thetaCuspLikelihoodSourceRemainder_signed_bounds_of_eight_le
    {n : ℕ} (hn : n ≤ 12) {x : ℝ}
    (hq : 8 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    0 ≤ (-1 : ℝ)^n*iteratedDeriv n thetaCuspLikelihoodSourceRemainder x ∧
    (-1 : ℝ)^n*iteratedDeriv n thetaCuspLikelihoodSourceRemainder x ≤
      (6*thetaCuspSingleAtomReflectionScale 1 x)^n*regimeOneLikelihoodScale x := by
  have hx := regimeOne_pos_of_six_le (x := x) (by linarith)
  rw [iteratedDeriv_thetaCuspLikelihoodSourceRemainder n hx]
  have h := thetaCuspCoolingJet_signed_le_leadingMoment_twelve hn (x := x) (by linarith)
  refine ⟨h.1, h.2.trans ?_⟩
  have hnr : (n : ℝ) ≤ 12 := by exact_mod_cast hn
  have hδ : (n : ℝ)/3 ≤ thetaCuspSingleAtomReflectionScale 1 x-Real.pi := by
    linarith [Real.pi_lt_d2]
  have hb := thetaCuspHigherLikelihoodSpectralMoment_le_explicitScale n hδ
  have hqp : 0 ≤ thetaCuspSingleAtomReflectionScale 1 x := by linarith
  calc
    (2*thetaCuspSingleAtomReflectionScale 1 x)^n*
        thetaCuspHigherLikelihoodSpectralMoment (thetaCuspLikelihoodCoordinate x) n ≤
      (2*thetaCuspSingleAtomReflectionScale 1 x)^n*(3^n*regimeOneLikelihoodScale x) :=
        mul_le_mul_of_nonneg_left hb (by positivity)
    _ = (6*thetaCuspSingleAtomReflectionScale 1 x)^n*regimeOneLikelihoodScale x := by
      rw [← mul_assoc, ← mul_pow]
      congr 2
      ring

/-- Absolute finite derivative errors retain factor six on the full scale-eight ray. -/
theorem abs_iteratedDeriv_thetaCuspLikelihoodSourceRemainder_le_six_scale_twelve
    {n : ℕ} (hn : n ≤ 12) {x : ℝ}
    (hq : 8 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    |iteratedDeriv n thetaCuspLikelihoodSourceRemainder x| ≤
      (6*thetaCuspSingleAtomReflectionScale 1 x)^n*regimeOneLikelihoodScale x := by
  have h := thetaCuspLikelihoodSourceRemainder_signed_bounds_of_eight_le hn hq
  have heq : |iteratedDeriv n thetaCuspLikelihoodSourceRemainder x| =
      (-1 : ℝ)^n*iteratedDeriv n thetaCuspLikelihoodSourceRemainder x := by
    rw [← abs_of_nonneg h.1, abs_mul, abs_pow]
    norm_num
  rw [heq]
  exact h.2

/-- The reflected relative error costs two linear tails and one quadratic tail. -/
theorem abs_thetaCuspLikelihoodReflectionErrorJet_le_twelve {n : ℕ} (hn : n ≤ 12) {x : ℝ}
    (hq : 8 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    |thetaCuspLikelihoodReflectionErrorJet n x| ≤
      2*(6*thetaCuspSingleAtomReflectionScale 1 x)^n*regimeOneLikelihoodScale x +
        (12*thetaCuspSingleAtomReflectionScale 1 x)^n*regimeOneLikelihoodScale x^(2 : ℕ) := by
  let q := thetaCuspSingleAtomReflectionScale 1 x
  let ε := regimeOneLikelihoodScale x
  let R := thetaCuspLikelihoodSourceRemainder
  have hqp : 0 ≤ q := by dsimp [q]; linarith
  have he : 0 ≤ ε := (regimeOneLikelihoodScale_pos x).le
  have hx := regimeOne_pos_of_six_le (x := x) (by linarith)
  have hb := abs_iteratedDeriv_thetaCuspLikelihoodSourceRemainder_le_six_scale_twelve hn hq
  have hp : |1+(-1 : ℝ)^n| ≤ 2 := by
    have h := abs_add_le (1 : ℝ) ((-1 : ℝ)^n)
    norm_num [abs_pow] at h ⊢
    exact h
  have hlin : |(1+(-1 : ℝ)^n)*iteratedDeriv n R x| ≤ 2*(6*q)^n*ε := by
    rw [abs_mul]
    have hm := mul_le_mul hp hb (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)
    change |1+(-1 : ℝ)^n| * |iteratedDeriv n R x| ≤ 2*((6*q)^n*ε) at hm
    nlinarith only [hm]
  have hs : |∑ i ∈ Finset.range (n+1), (n.choose i : ℝ)*iteratedDeriv i R x *
      ((-1 : ℝ)^(n-i)*iteratedDeriv (n-i) R x)| ≤ (12*q)^n*ε^(2 : ℕ) := by
    calc
      _ ≤ ∑ i ∈ Finset.range (n+1), |(n.choose i : ℝ)*iteratedDeriv i R x *
          ((-1 : ℝ)^(n-i)*iteratedDeriv (n-i) R x)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ Finset.range (n+1), (n.choose i : ℝ)*((6*q)^i*ε)*((6*q)^(n-i)*ε) := by
        apply Finset.sum_le_sum
        intro i hi
        have hi' : i ≤ n := by have := Finset.mem_range.mp hi; omega
        have h1 := abs_iteratedDeriv_thetaCuspLikelihoodSourceRemainder_le_six_scale_twelve (hi'.trans hn) hq
        have h2 := abs_iteratedDeriv_thetaCuspLikelihoodSourceRemainder_le_six_scale_twelve
          ((Nat.sub_le n i).trans hn) hq
        simp only [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
          abs_of_nonneg (show (0 : ℝ) ≤ (n.choose i : ℝ) from Nat.cast_nonneg _)]
        exact mul_le_mul (mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg _)) h2
          (abs_nonneg _) (by positivity)
      _ = (12*q)^n*ε^(2 : ℕ) := by
        rw [show 12*q = 6*q+6*q by ring, add_pow, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i hi
        ring
  rw [thetaCuspLikelihoodReflectionErrorJet_eq n hx]
  have ht := abs_add_le ((1+(-1 : ℝ)^n)*iteratedDeriv n R x)
    (∑ i ∈ Finset.range (n+1), (n.choose i : ℝ)*iteratedDeriv i R x *
      ((-1 : ℝ)^(n-i)*iteratedDeriv (n-i) R x))
  change |(1+(-1 : ℝ)^n)*iteratedDeriv n R x +
    ∑ i ∈ Finset.range (n+1), (n.choose i : ℝ)*iteratedDeriv i R x *
      ((-1 : ℝ)^(n-i)*iteratedDeriv (n-i) R x)| ≤ 2*(6*q)^n*ε+(12*q)^n*ε^(2 : ℕ)
  linarith only [ht, hlin, hs]

/-- The complete finite reflection error retains the exact first-atom reflected jets in its majorant. -/
theorem abs_thetaCuspNativeReflectionJet_sub_first_le_factored_twelve
    {n : ℕ} (hn : n ≤ 12) {x : ℝ}
    (hq : 8 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    |thetaCuspNativeReflectionJet n x-thetaCuspFirstAtomReflectionJet n x| ≤
      ∑ i ∈ Finset.range (n+1), (n.choose i : ℝ)*|thetaCuspFirstAtomReflectionJet i x| *
        (2*(6*thetaCuspSingleAtomReflectionScale 1 x)^(n-i)*regimeOneLikelihoodScale x +
          (12*thetaCuspSingleAtomReflectionScale 1 x)^(n-i)*regimeOneLikelihoodScale x^(2 : ℕ)) := by
  have hx := regimeOne_pos_of_six_le (x := x) (by linarith)
  rw [thetaCuspNativeReflectionJet_sub_first_eq_factored n hx]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro i hi
  have hb := abs_thetaCuspLikelihoodReflectionErrorJet_le_twelve ((Nat.sub_le n i).trans hn) hq
  simp only [abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ (n.choose i : ℝ) from Nat.cast_nonneg _)]
  exact mul_le_mul_of_nonneg_left hb (mul_nonneg (Nat.cast_nonneg _) (abs_nonneg _))

end
end RHTower

