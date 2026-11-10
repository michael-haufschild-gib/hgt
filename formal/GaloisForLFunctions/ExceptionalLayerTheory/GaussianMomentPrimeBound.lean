import GaloisForLFunctions.ExceptionalLayerTheory.GaussianMomentTypeI
import GaloisForLFunctions.ExceptionalLayerTheory.GaussianMomentsReadTheDivisor
import GaloisForLFunctions.RHTower.Sieve.VaughanTypeIRestricted

/-!
# Arithmetic bounds for complete first Gaussian prime moments

The two type-I terms retain their truncated arithmetic coefficients.
Their total mass is paid by the damping scale, while reciprocal mass
costs only logarithms. The finite von Mangoldt head and the infinite
type-II estimate complete Vaughan's identity.
-/

open Complex Finset Filter Topology RHTower RHTower.Sieve ArithmeticFunction

noncomputable section
namespace GaloisForLFunctions.ExceptionalLayerTheory


private theorem sum_gaussianMoment_divisor_cost (α t : ℝ) (K : ℕ) :
    (∑ b ∈ Icc 1 K, (Real.sqrt (α * t) + 1 / ((b : ℝ) * Real.sqrt t))) =
      Real.sqrt (α * t) * K + invSum K / Real.sqrt t := by
  rw [sum_add_distrib]
  have hi : (∑ b ∈ Icc 1 K, 1 / ((b : ℝ) * Real.sqrt t)) = invSum K / Real.sqrt t := by
    unfold invSum
    rw [sum_div]
    apply sum_congr rfl
    intro b _
    ring
  rw [hi]
  simp only [sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
  ring

/-- The first actual type-I convolution is bounded independently of both endpoints. -/
theorem norm_sum_gaussianMoment_zeta_trunc_conv_le {σ α ξ t X : ℝ}
    (hσ : 0 ≤ σ) (hσ1 : σ < 1) (hα : 0 ≤ α) (hαξ : α ≤ ξ) (ht : 0 < t)
    (hsector : ξ ≤ 2 * α * t) (hscale : 2 ≤ α * X ^ 2)
    {A B U V : ℕ} (hA : 1 ≤ A) (hB : 1 ≤ B)
    (hUV : 1 ≤ U * V) (hUVX : ((U * V : ℕ) : ℝ) ≤ X) :
    ‖∑ n ∈ Ico A B,
        ((((zeta : ArithmeticFunction ℝ) * (truncAF vonMangoldt U *
          truncAF (moebius : ArithmeticFunction ℝ) V)) n : ℝ) : ℂ) *
            gaussianPrimeMomentWeight σ α ξ t n‖ ≤
      64000 * (1 / ((2 : ℝ) ^ (1 - σ) - 1) + 12) *
        X ^ (1 - σ) * (2 + Real.log X / Real.log 2) ^ 4 * Real.log ((U * V : ℕ) : ℝ) *
          (Real.sqrt (α * t) * ((U * V : ℕ) : ℝ) + invSum (U * V) / Real.sqrt t) := by
  let c := truncAF vonMangoldt U * truncAF (moebius : ArithmeticFunction ℝ) V
  have hsupp : ∀ b, U * V < b → ((c b : ℝ) : ℂ) = 0 := by
    intro b hb
    simp only [c, truncAF_conv_apply_of_gt hb, Complex.ofReal_zero]
  change ‖∑ n ∈ Ico A B, ((((zeta : ArithmeticFunction ℝ) * c) n : ℝ) : ℂ) * _‖ ≤ _
  simp_rw [coe_zeta_mul_apply']
  rw [sum_conv_mul_Ico_eq hA hB (le_max_left (B - 1) (U * V)) (fun _ => (1 : ℂ))
    (fun b => ((c b : ℝ) : ℂ)) (gaussianPrimeMomentWeight σ α ξ t),
    sum_Icc_restrict_of_support (le_max_right (B - 1) (U * V)) _ _ hsupp]
  simp only [one_mul]
  have hq : 1 < (2 : ℝ) ^ (1 - σ) := Real.one_lt_rpow (by norm_num) (by linarith only [hσ1])
  have hlog : 0 ≤ Real.log ((U * V : ℕ) : ℝ) := Real.log_nonneg (by exact_mod_cast hUV)
  calc
    _ ≤ ∑ b ∈ Icc 1 (U * V),
        64000 * (1 / ((2 : ℝ) ^ (1 - σ) - 1) + 12) *
          X ^ (1 - σ) * (2 + Real.log X / Real.log 2) ^ 4 * Real.log ((U * V : ℕ) : ℝ) *
            (Real.sqrt (α * t) + 1 / ((b : ℝ) * Real.sqrt t)) := by
      apply (norm_sum_le _ _).trans
      apply sum_le_sum
      intro b hb
      have hb1 := (mem_Icc.mp hb).1
      have hbX : (b : ℝ) ≤ X := (by exact_mod_cast (mem_Icc.mp hb).2 : (b : ℝ) ≤ ((U * V : ℕ) : ℝ)).trans hUVX
      have hc : ‖((c b : ℝ) : ℂ)‖ ≤ Real.log ((U * V : ℕ) : ℝ) := by
        rw [Complex.norm_real, Real.norm_eq_abs]
        exact (abs_truncAF_conv_le_log U V b).trans
          (Real.log_le_log (by exact_mod_cast (show 0 < b by omega)) (by exact_mod_cast (mem_Icc.mp hb).2))
      rw [norm_mul]
      have hh := mul_le_mul hc
        (norm_sum_gaussianPrimeMomentWeight_dilate_le hσ hσ1 hα hαξ ht hsector hscale
          (Nat.le_add_left 1 ((A - 1) / b)) (Nat.le_add_left 1 ((B - 1) / b)) hb1 hbX)
        (norm_nonneg _) hlog
      convert hh using 1
      ring
    _ = _ := by rw [← mul_sum, sum_gaussianMoment_divisor_cost]

/-- The second actual type-I convolution has only a harmonic divisor cost. -/
theorem norm_sum_gaussianMoment_log_trunc_moebius_le {σ α ξ t X : ℝ}
    (hσ : 0 ≤ σ) (hσ1 : σ < 1) (hα : 0 ≤ α) (hαξ : α ≤ ξ) (ht : 0 < t)
    (hsector : ξ ≤ 2 * α * t) (hscale : 2 ≤ α * X ^ 2)
    {A B V : ℕ} (hA : 1 ≤ A) (hB : 1 ≤ B) (hVX : (V : ℝ) ≤ X) :
    ‖∑ n ∈ Ico A B,
        (((ArithmeticFunction.log * truncAF (moebius : ArithmeticFunction ℝ) V) n : ℝ) : ℂ) *
            gaussianPrimeMomentWeight σ α ξ t n‖ ≤
      128000 * (1 / ((2 : ℝ) ^ (1 - σ) - 1) + 12) *
        X ^ (1 - σ) * (2 + Real.log X / Real.log 2) ^ 4 *
          (Real.sqrt (α * t) * V + invSum V / Real.sqrt t) := by
  let c := truncAF (moebius : ArithmeticFunction ℝ) V
  have hsupp : ∀ b, V < b → ((c b : ℝ) : ℂ) = 0 := by
    intro b hb
    simp only [c, truncAF_apply_of_gt hb, Complex.ofReal_zero]
  simp_rw [coe_log_mul_apply']
  rw [sum_conv_mul_Ico_eq hA hB (le_max_left (B - 1) V) (fun a => (Real.log a : ℂ))
    (fun b => ((c b : ℝ) : ℂ)) (gaussianPrimeMomentWeight σ α ξ t),
    sum_Icc_restrict_of_support (le_max_right (B - 1) V) _ _ hsupp]
  have hq : 1 < (2 : ℝ) ^ (1 - σ) := Real.one_lt_rpow (by norm_num) (by linarith only [hσ1])
  calc
    _ ≤ ∑ b ∈ Icc 1 V,
        128000 * (1 / ((2 : ℝ) ^ (1 - σ) - 1) + 12) *
          X ^ (1 - σ) * (2 + Real.log X / Real.log 2) ^ 4 *
            (Real.sqrt (α * t) + 1 / ((b : ℝ) * Real.sqrt t)) := by
      apply (norm_sum_le _ _).trans
      apply sum_le_sum
      intro b hb
      have hb1 := (mem_Icc.mp hb).1
      have hbX : (b : ℝ) ≤ X := (by exact_mod_cast (mem_Icc.mp hb).2 : (b : ℝ) ≤ V).trans hVX
      have hc : ‖((c b : ℝ) : ℂ)‖ ≤ 1 := by
        rw [Complex.norm_real, Real.norm_eq_abs]
        exact abs_truncAF_moebius_le_one V b
      rw [norm_mul]
      have hh := mul_le_mul hc
        (norm_sum_log_gaussianPrimeMomentWeight_dilate_le hσ hσ1 hα hαξ ht hsector hscale
          (Nat.le_add_left 1 ((A - 1) / b)) (Nat.le_add_left 1 ((B - 1) / b)) hb1 hbX)
        (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
      convert hh using 1
      ring
    _ = _ := by rw [← mul_sum, sum_gaussianMoment_divisor_cost]

/-- The finite Vaughan head keeps its exact abscissa decay. -/
theorem norm_sum_gaussianPrimeMoment_vonMangoldt_head_le {σ α ξ t : ℝ}
    (hσ1 : σ < 1) (hα : 0 ≤ α) (hαξ : α ≤ ξ) (ht : 0 < t)
    (hsector : ξ ≤ 2 * α * t) {U : ℕ} (hU : 1 ≤ U) :
    ‖∑ n ∈ Ico 1 (U + 1), ((vonMangoldt n : ℝ) : ℂ) * gaussianPrimeMomentWeight σ α ξ t n‖ ≤
      4 * α * (U : ℝ) ^ 2 * (U : ℝ) ^ (1 - σ) * Real.log U := by
  have hU0 : (0 : ℝ) < U := by exact_mod_cast (show 0 < U by omega)
  have hlog : 0 ≤ Real.log U := Real.log_nonneg (by exact_mod_cast hU)
  calc
    _ ≤ ∑ n ∈ Ico 1 (U + 1), 4 * α * (U : ℝ) ^ (2 - σ) * Real.log U := by
      apply (norm_sum_le _ _).trans
      apply sum_le_sum
      intro n hn
      have hn1 : 1 ≤ n := (mem_Ico.mp hn).1
      have hnU : n ≤ U := by have := (mem_Ico.mp hn).2; omega
      have hΛ : ‖((vonMangoldt n : ℝ) : ℂ)‖ ≤ Real.log U := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg vonMangoldt_nonneg]
        exact vonMangoldt_le_log.trans (Real.log_le_log (by exact_mod_cast (show 0 < n by omega)) (by exact_mod_cast hnU))
      have he : Real.exp (-α * (n : ℝ) ^ 2) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith only [mul_nonneg hα (sq_nonneg (n : ℝ))])
      have hp : (n : ℝ) ^ (2 - σ) ≤ (U : ℝ) ^ (2 - σ) :=
        Real.rpow_le_rpow (Nat.cast_nonneg n) (by exact_mod_cast hnU) (by linarith only [hσ1])
      have hw := (norm_gaussianPrimeMomentWeight_le σ hα hαξ ht hsector hn1).trans
        (mul_le_mul (mul_le_mul_of_nonneg_left hp (by positivity : 0 ≤ 4 * α)) he (by positivity) (by positivity))
      rw [norm_mul]
      have hh := mul_le_mul hΛ hw (norm_nonneg _) hlog
      convert hh using 1
      ring
    _ = _ := by
      simp only [sum_const, Nat.card_Ico, Nat.add_sub_cancel, nsmul_eq_mul]
      have hp : (U : ℝ) ^ (2 - σ) = (U : ℝ) * (U : ℝ) ^ (1 - σ) := by
        rw [show 2 - σ = 1 + (1 - σ) by ring, Real.rpow_add hU0, Real.rpow_one]
      rw [hp]
      ring

/-- The complete first von Mangoldt moment is absolutely convergent at positive damping. -/
theorem summable_gaussianPrimeMoment_vonMangoldt {σ α : ℝ}
    (hσ : 0 ≤ σ) (hα : 0 < α) (ξ t : ℝ) :
    Summable (fun n : ℕ => ((vonMangoldt n : ℝ) : ℂ) * gaussianPrimeMomentWeight σ α ξ t n) := by
  apply ((RHTower.summable_pow_mul_exp_neg_nat_sq 3 hα).mul_left ‖((α : ℂ) - ξ * I) / t‖).of_norm_bounded
  intro n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [gaussianPrimeMomentWeight]
  · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hΛ : ‖((vonMangoldt n : ℝ) : ℂ)‖ ≤ (n : ℝ) := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg vonMangoldt_nonneg]
      have hh := Real.log_le_sub_one_of_pos (by exact_mod_cast hn : (0 : ℝ) < n)
      exact vonMangoldt_le_log.trans (by linarith only [hh])
    have hp : (n : ℝ) ^ (-(σ - 2)) ≤ (n : ℝ) ^ 2 := by
      simpa only [Real.rpow_two] using Real.rpow_le_rpow_of_exponent_le hn1
        (by linarith only [hσ] : -(σ - 2) ≤ 2)
    rw [norm_mul, gaussianPrimeMomentWeight_eq_shift σ α ξ t hn, norm_mul, norm_gaussianPrimeWeight_exact]
    calc
      _ ≤ (n : ℝ) * (‖((α : ℂ) - ξ * I) / t‖ *
          ((n : ℝ) ^ 2 * Real.exp (-α * (n : ℝ) ^ 2))) := by gcongr
      _ = _ := by ring

private theorem gaussianMoment_log_scale_ge_two {X : ℝ} (hX : 1 ≤ X) :
    2 ≤ 2 + Real.log X / Real.log 2 := by
  have hh := Real.log_nonneg hX
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  exact le_add_of_nonneg_right (div_nonneg hh h2.le)

private theorem gaussianMoment_log_le_scale {X : ℝ} (hX : 1 ≤ X) :
    Real.log X ≤ Real.log X / Real.log 2 := by
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h2' : Real.log 2 ≤ 1 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at hh
    exact hh
  apply (le_div_iff₀ h2).mpr
  simpa only [mul_one] using mul_le_mul_of_nonneg_left h2' (Real.log_nonneg hX)

private theorem gaussianMoment_divisor_cost_le {α t X : ℝ}
    (hα : 0 ≤ α) (ht : 1 ≤ t) (hscale : α * X ^ 2 = 2)
    {K : ℕ} (hK : 1 ≤ K) (hKX : t * (K : ℝ) ≤ X) :
    Real.sqrt (α * t) * K + invSum K / Real.sqrt t ≤
      2 * (2 + Real.log X / Real.log 2) / Real.sqrt t := by
  have ht0 : 0 < t := zero_lt_one.trans_le ht
  have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  have hKX' : (K : ℝ) ≤ X := (by nlinarith only [ht, hK0] : (K : ℝ) ≤ t * K).trans hKX
  have hX : 1 ≤ X := hK1.trans hKX'
  have hs : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht0
  have hroot : Real.sqrt (α * t) * K ≤ 2 / Real.sqrt t := by
    apply (le_div_iff₀ hs).mpr
    have hp := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity : 0 ≤ t * (K : ℝ)) hKX 2) hα
    have he : (Real.sqrt (α * t) * K * Real.sqrt t) ^ 2 = α * (t * K) ^ 2 := by
      rw [mul_pow, mul_pow, Real.sq_sqrt (mul_nonneg hα ht0.le), Real.sq_sqrt ht0.le]
      ring
    rw [hscale] at hp
    have hnon : 0 ≤ Real.sqrt (α * t) * K * Real.sqrt t := by positivity
    nlinarith only [hp, he, hnon]
  have hlog : 1 + Real.log K ≤ 2 + Real.log X / Real.log 2 := by
    have hh := Real.log_le_log (by exact_mod_cast (show 0 < K by omega)) hKX'
    have hx := gaussianMoment_log_le_scale hX
    linarith only [hh, hx]
  have hL := gaussianMoment_log_scale_ge_two hX
  have hi := div_le_div_of_nonneg_right ((invSum_le_one_add_log hK).trans hlog) hs.le
  have hsum := add_le_add hroot hi
  apply hsum.trans
  rw [← add_div]
  exact div_le_div_of_nonneg_right (by linarith only [hL]) hs.le

private theorem gaussianMoment_head_physical_le {σ α ξ t X : ℝ}
    (hσ1 : σ < 1) (hα : 0 ≤ α) (hαξ : α ≤ ξ) (ht : 1 ≤ t)
    (hsector : ξ ≤ 2 * α * t) (hscale : α * X ^ 2 = 2)
    {U : ℕ} (hU : 1 ≤ U) (hUX : t * (U : ℝ) ≤ X) :
    ‖∑ n ∈ Ico 1 (U + 1), ((vonMangoldt n : ℝ) : ℂ) * gaussianPrimeMomentWeight σ α ξ t n‖ ≤
      8 * X ^ (1 - σ) * (2 + Real.log X / Real.log 2) / Real.sqrt t := by
  have ht0 : 0 < t := zero_lt_one.trans_le ht
  have hU1 : (1 : ℝ) ≤ U := by exact_mod_cast hU
  have hUX' : (U : ℝ) ≤ X := (by nlinarith only [ht, hU1] : (U : ℝ) ≤ t * U).trans hUX
  have hX : 1 ≤ X := hU1.trans hUX'
  have hlogU : 0 ≤ Real.log U := Real.log_nonneg hU1
  have hlog : Real.log U ≤ 2 + Real.log X / Real.log 2 := by
    have hh := Real.log_le_log (by exact_mod_cast (show 0 < U by omega)) hUX'
    have hx := gaussianMoment_log_le_scale hX
    linarith only [hh, hx]
  have hp := Real.rpow_le_rpow (Nat.cast_nonneg U) hUX' (by linarith only [hσ1] : 0 ≤ 1 - σ)
  have hs : Real.sqrt t ≤ t ^ 2 := by
    apply (Real.sqrt_le_left (sq_nonneg t)).mpr
    nlinarith only [ht, sq_nonneg (t - 1), sq_nonneg (t ^ 2 - 1)]
  have hprod := mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (by positivity : 0 ≤ t * (U : ℝ)) hUX 2) hα
  rw [hscale] at hprod
  apply (norm_sum_gaussianPrimeMoment_vonMangoldt_head_le hσ1 hα hαξ ht0 hsector hU).trans
  apply (le_div_iff₀ (Real.sqrt_pos.mpr ht0)).mpr
  have hfirst := mul_le_mul hp hlog hlogU (Real.rpow_nonneg (by linarith only [hX]) _)
  have hcoef : 4 * α * (U : ℝ) ^ 2 * Real.sqrt t ≤ 8 := by
    have hh := mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ 4 * α * (U : ℝ) ^ 2)
    nlinarith only [hh, hprod]
  have hh := mul_le_mul hcoef hfirst (by positivity : 0 ≤ (U : ℝ) ^ (1 - σ) * Real.log U) (by norm_num : (0 : ℝ) ≤ 8)
  convert hh using 1 <;> (first | rfl | ring)


/-- The pole-scale arithmetic envelope, with its abscissa-dependent constant explicit. -/
def gaussianPrimeMomentScale (σ X : ℝ) : ℝ :=
  (1 / ((2 : ℝ) ^ (1 - σ) - 1) + 12) * X ^ (1 - σ) *
    (2 + Real.log X / Real.log 2) ^ 6

private theorem gaussianPrimeMomentScale_nonneg {σ X : ℝ} (hσ1 : σ < 1) (hX : 1 ≤ X) :
    0 ≤ gaussianPrimeMomentScale σ X := by
  have hq : 1 < (2 : ℝ) ^ (1 - σ) := Real.one_lt_rpow (by norm_num) (by linarith only [hσ1])
  unfold gaussianPrimeMomentScale
  positivity

private theorem gaussianMoment_lower_log_power_le {σ X : ℝ}
    (hσ1 : σ < 1) (hX : 1 ≤ X) (k : ℕ) (hk : k ≤ 6) :
    (1 / ((2 : ℝ) ^ (1 - σ) - 1) + 12) * X ^ (1 - σ) *
      (2 + Real.log X / Real.log 2) ^ k ≤ gaussianPrimeMomentScale σ X := by
  have hq : 1 < (2 : ℝ) ^ (1 - σ) := Real.one_lt_rpow (by norm_num) (by linarith only [hσ1])
  have hL : 1 ≤ 2 + Real.log X / Real.log 2 := (by norm_num : (1 : ℝ) ≤ 2).trans (gaussianMoment_log_scale_ge_two hX)
  have hp : (2 + Real.log X / Real.log 2) ^ k ≤ (2 + Real.log X / Real.log 2) ^ 6 := by
    have hh := mul_le_mul_of_nonneg_left (one_le_pow₀ (n := 6 - k) hL)
      (by positivity : 0 ≤ (2 + Real.log X / Real.log 2) ^ k)
    rw [mul_one, ← pow_add, Nat.add_sub_of_le hk] at hh
    exact hh
  exact mul_le_mul_of_nonneg_left hp (by positivity)

private theorem gaussianMoment_head_scale_le {σ X : ℝ} (hσ1 : σ < 1) (hX : 1 ≤ X) :
    X ^ (1 - σ) * (2 + Real.log X / Real.log 2) ≤ gaussianPrimeMomentScale σ X := by
  have hq : 1 < (2 : ℝ) ^ (1 - σ) := Real.one_lt_rpow (by norm_num) (by linarith only [hσ1])
  have hf : 1 ≤ 1 / ((2 : ℝ) ^ (1 - σ) - 1) + 12 := by
    have hh : 0 ≤ 1 / ((2 : ℝ) ^ (1 - σ) - 1) := by positivity
    linarith only [hh]
  have hL := gaussianMoment_log_scale_ge_two hX
  have hh := mul_le_mul_of_nonneg_right hf
    (by positivity : 0 ≤ X ^ (1 - σ) * (2 + Real.log X / Real.log 2))
  calc
    _ ≤ (1 / ((2 : ℝ) ^ (1 - σ) - 1) + 12) * X ^ (1 - σ) *
        (2 + Real.log X / Real.log 2) ^ 1 := by convert hh using 1 <;> (first | rfl | ring)
    _ ≤ _ := gaussianMoment_lower_log_power_le hσ1 hX 1 (by norm_num)

private theorem gaussianMoment_typeI_physical_cost {σ α t X : ℝ}
    (hσ1 : σ < 1) (hα : 0 ≤ α) (ht : 1 ≤ t) (hscale : α * X ^ 2 = 2)
    {K : ℕ} (hK : 1 ≤ K) (hKX : t * (K : ℝ) ≤ X) :
    (1 / ((2 : ℝ) ^ (1 - σ) - 1) + 12) * X ^ (1 - σ) *
      (2 + Real.log X / Real.log 2) ^ 4 * Real.log K *
        (Real.sqrt (α * t) * K + invSum K / Real.sqrt t) ≤
      2 * gaussianPrimeMomentScale σ X / Real.sqrt t := by
  have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hKX' : (K : ℝ) ≤ X := (by nlinarith only [ht, hK1] : (K : ℝ) ≤ t * K).trans hKX
  have hX : 1 ≤ X := hK1.trans hKX'
  have hq : 1 < (2 : ℝ) ^ (1 - σ) := Real.one_lt_rpow (by norm_num) (by linarith only [hσ1])
  have hlogK : 0 ≤ Real.log K := Real.log_nonneg hK1
  have hlog : Real.log K ≤ 2 + Real.log X / Real.log 2 := by
    have hh := Real.log_le_log (by exact_mod_cast (show 0 < K by omega)) hKX'
    have hx := gaussianMoment_log_le_scale hX
    linarith only [hh, hx]
  have hcost := gaussianMoment_divisor_cost_le hα ht hscale hK hKX
  have hi : 0 ≤ invSum K := by unfold invSum; exact sum_nonneg fun n _ => by positivity
  have hh := mul_le_mul hlog hcost (by positivity : 0 ≤ Real.sqrt (α * t) * K + invSum K / Real.sqrt t)
    (by have := gaussianMoment_log_scale_ge_two hX; positivity)
  have hm := mul_le_mul_of_nonneg_left hh
    (by positivity : 0 ≤ (1 / ((2 : ℝ) ^ (1 - σ) - 1) + 12) * X ^ (1 - σ) * (2 + Real.log X / Real.log 2) ^ 4)
  unfold gaussianPrimeMomentScale
  convert hm using 1 <;> (first | rfl | ring)

private theorem gaussianMoment_log_typeI_physical_cost {σ α t X : ℝ}
    (hσ1 : σ < 1) (hα : 0 ≤ α) (ht : 1 ≤ t) (hscale : α * X ^ 2 = 2)
    {K : ℕ} (hK : 1 ≤ K) (hKX : t * (K : ℝ) ≤ X) :
    (1 / ((2 : ℝ) ^ (1 - σ) - 1) + 12) * X ^ (1 - σ) *
      (2 + Real.log X / Real.log 2) ^ 4 *
        (Real.sqrt (α * t) * K + invSum K / Real.sqrt t) ≤
      2 * gaussianPrimeMomentScale σ X / Real.sqrt t := by
  have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hKX' : (K : ℝ) ≤ X := (by nlinarith only [ht, hK1] : (K : ℝ) ≤ t * K).trans hKX
  have hX : 1 ≤ X := hK1.trans hKX'
  have hq : 1 < (2 : ℝ) ^ (1 - σ) := Real.one_lt_rpow (by norm_num) (by linarith only [hσ1])
  have hcost := gaussianMoment_divisor_cost_le hα ht hscale hK hKX
  have hm := mul_le_mul_of_nonneg_left hcost
    (by positivity : 0 ≤ (1 / ((2 : ℝ) ^ (1 - σ) - 1) + 12) * X ^ (1 - σ) * (2 + Real.log X / Real.log 2) ^ 4)
  have hp := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left (gaussianMoment_lower_log_power_le hσ1 hX 5 (by norm_num))
      (by norm_num : (0 : ℝ) ≤ 2)) (Real.sqrt_nonneg t)
  calc
    _ ≤ 2 * ((1 / ((2 : ℝ) ^ (1 - σ) - 1) + 12) * X ^ (1 - σ) *
        (2 + Real.log X / Real.log 2) ^ 5) / Real.sqrt t := by convert hm using 1 <;> (first | rfl | ring)
    _ ≤ _ := hp

/-- The complete first von Mangoldt moment has an independent arithmetic bound
with square-root saving in height. The damping scale pays both type-I masses. -/
theorem exists_gaussianPrimeMoment_vonMangoldt_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (σ α ξ t X : ℝ) (U V : ℕ),
      0 ≤ σ → σ < 1 → 0 < ξ → 2 ≤ t → ξ / (2 * t) ≤ α → α ≤ ξ →
      α * X ^ 2 = 2 → 128 * t * Real.log t ≤ Real.pi * U → 2 * t ≤ V →
      t * ((U * V : ℕ) : ℝ) ≤ X →
      ‖∑' n : ℕ, ((vonMangoldt n : ℝ) : ℂ) * gaussianPrimeMomentWeight σ α ξ t n‖ ≤
        C * gaussianPrimeMomentScale σ X / Real.sqrt t := by
  obtain ⟨C, hC, hII⟩ := exists_gaussianVaughan_moment_uniform_typeII_bound
  refine ⟨400000 + 16 * Real.sqrt C, by positivity, ?_⟩
  intro σ α ξ t X U V hσ hσ1 hξ ht hlower hupper hscale hUcut hVcut hUVX
  have ht0 : 0 < t := by linarith only [ht]
  have ht1 : 1 ≤ t := by linarith only [ht]
  have hα : 0 < α := (by positivity : 0 < ξ / (2 * t)).trans_le hlower
  have hsector : ξ ≤ 2 * α * t := by
    have hh := (div_le_iff₀ (by positivity : 0 < 2 * t)).mp hlower
    nlinarith only [hh]
  have hU : 1 ≤ U := by
    by_contra h
    have hz : U = 0 := by omega
    rw [hz, Nat.cast_zero, mul_zero] at hUcut
    have hlog : 0 < Real.log t := Real.log_pos (by linarith only [ht])
    have hp : 0 < 128 * t * Real.log t := by positivity
    linarith only [hp, hUcut]
  have hV : 1 ≤ V := by
    have hh : (1 : ℝ) ≤ V := by linarith only [hVcut, ht]
    exact_mod_cast hh
  have hUV : 1 ≤ U * V := by nlinarith only [hU, hV]
  have hUUV : U ≤ U * V := by nlinarith only [hU, hV]
  have hVUV : V ≤ U * V := by nlinarith only [hU, hV]
  have hUX : t * (U : ℝ) ≤ X :=
    (mul_le_mul_of_nonneg_left (by exact_mod_cast hUUV) ht0.le).trans hUVX
  have hVX : t * (V : ℝ) ≤ X :=
    (mul_le_mul_of_nonneg_left (by exact_mod_cast hVUV) ht0.le).trans hUVX
  have hUV1 : (1 : ℝ) ≤ ((U * V : ℕ) : ℝ) := by exact_mod_cast hUV
  have hUVX' : ((U * V : ℕ) : ℝ) ≤ X :=
    (by nlinarith only [ht1, hUV1] : ((U * V : ℕ) : ℝ) ≤ t * ((U * V : ℕ) : ℝ)).trans hUVX
  have hVX' : (V : ℝ) ≤ X := (by exact_mod_cast hVUV : (V : ℝ) ≤ ((U * V : ℕ) : ℝ)).trans hUVX'
  have hX : 1 ≤ X := hUV1.trans hUVX'
  have hq : 1 < (2 : ℝ) ^ (1 - σ) := Real.one_lt_rpow (by norm_num) (by linarith only [hσ1])
  have hG := gaussianPrimeMomentScale_nonneg hσ1 hX
  have hst : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht0
  obtain ⟨R, hR, hphysical⟩ := exists_gaussianMoment_physical_scale hσ hσ1 hα.le hX hscale.ge
  have hfinite (B : ℕ) (hB : U + 1 ≤ B) :
      ‖∑ n ∈ Ico 1 B, ((vonMangoldt n : ℝ) : ℂ) * gaussianPrimeMomentWeight σ α ξ t n‖ ≤
        (400000 + 16 * Real.sqrt C) * gaussianPrimeMomentScale σ X / Real.sqrt t := by
    have hB1 : 1 ≤ B := by omega
    have hh := gaussianMoment_head_physical_le hσ1 hα.le hupper ht1 hsector hscale hU hUX
    have hhead : ‖∑ n ∈ Ico 1 (U + 1), ((vonMangoldt n : ℝ) : ℂ) * gaussianPrimeMomentWeight σ α ξ t n‖ ≤
        8 * gaussianPrimeMomentScale σ X / Real.sqrt t := by
      apply hh.trans
      have hh' := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (gaussianMoment_head_scale_le hσ1 hX) (by norm_num : (0 : ℝ) ≤ 8)) hst.le
      convert hh' using 1
      ring
    have hz0 := norm_sum_gaussianMoment_zeta_trunc_conv_le hσ hσ1 hα.le hupper ht0 hsector hscale.ge
      (by omega : 1 ≤ U + 1) hB1 hUV hUVX'
    have hz : ‖∑ n ∈ Ico (U + 1) B,
        ((((zeta : ArithmeticFunction ℝ) * truncAF vonMangoldt U *
          truncAF (moebius : ArithmeticFunction ℝ) V) n : ℝ) : ℂ) * gaussianPrimeMomentWeight σ α ξ t n‖ ≤
        128000 * gaussianPrimeMomentScale σ X / Real.sqrt t := by
      rw [mul_assoc]
      apply hz0.trans
      have hh' := mul_le_mul_of_nonneg_left
        (gaussianMoment_typeI_physical_cost hσ1 hα.le ht1 hscale hUV hUVX) (by norm_num : (0 : ℝ) ≤ 64000)
      convert hh' using 1 <;> (first | rfl | ring)
    have hl0 := norm_sum_gaussianMoment_log_trunc_moebius_le hσ hσ1 hα.le hupper ht0 hsector hscale.ge
      (by omega : 1 ≤ U + 1) hB1 hVX'
    have hl : ‖∑ n ∈ Ico (U + 1) B,
        (((ArithmeticFunction.log * truncAF (moebius : ArithmeticFunction ℝ) V) n : ℝ) : ℂ) * gaussianPrimeMomentWeight σ α ξ t n‖ ≤
        256000 * gaussianPrimeMomentScale σ X / Real.sqrt t := by
      apply hl0.trans
      have hh' := mul_le_mul_of_nonneg_left
        (gaussianMoment_log_typeI_physical_cost hσ1 hα.le ht1 hscale hV hVX) (by norm_num : (0 : ℝ) ≤ 128000)
      convert hh' using 1 <;> (first | rfl | ring)
    have hII0 := hII σ α ξ t (U + 1) B R U V hσ hσ1 hξ ht1 hlower hupper
      (by omega) hB1 hR hUcut hVcut
    have hII1 : ‖(((α : ℂ) - ξ * I) / t) *
        (∑ n ∈ Ico (U + 1) B, (((typeIILong U * typeIIShort V) n : ℝ) : ℂ) *
          gaussianPrimeWeight (σ - 2) α ξ t n)‖ ≤
        16 * Real.sqrt (C / t) * (1 / ((2 : ℝ) ^ (1 - σ) - 1) + 12) *
          X ^ (1 - σ) * (2 + Real.log X / Real.log 2) ^ 4 := by
      apply hII0.trans
      have hh' := mul_le_mul_of_nonneg_left hphysical
        (by positivity : 0 ≤ 8 * Real.sqrt (C / t) * (1 / ((2 : ℝ) ^ (1 - σ) - 1) + 12))
      convert hh' using 1 <;> (first | rfl | ring)
    have htypeII : ‖∑ n ∈ Ico (U + 1) B,
        (((typeIILong U * typeIIShort V) n : ℝ) : ℂ) * gaussianPrimeMomentWeight σ α ξ t n‖ ≤
        16 * Real.sqrt C * gaussianPrimeMomentScale σ X / Real.sqrt t := by
      have he : (∑ n ∈ Ico (U + 1) B,
          (((typeIILong U * typeIIShort V) n : ℝ) : ℂ) * gaussianPrimeMomentWeight σ α ξ t n) =
          (((α : ℂ) - ξ * I) / t) *
            (∑ n ∈ Ico (U + 1) B, (((typeIILong U * typeIIShort V) n : ℝ) : ℂ) *
              gaussianPrimeWeight (σ - 2) α ξ t n) := by
        rw [mul_sum]
        apply sum_congr rfl
        intro n hn
        rw [gaussianPrimeMomentWeight_eq_shift σ α ξ t (by have := (mem_Ico.mp hn).1; omega)]
        ring
      rw [he]
      apply hII1.trans
      have hh' := mul_le_mul_of_nonneg_left (gaussianMoment_lower_log_power_le hσ1 hX 4 (by norm_num))
        (by positivity : 0 ≤ 16 * Real.sqrt (C / t))
      have hr : Real.sqrt (C / t) * Real.sqrt t = Real.sqrt C := by
        rw [← Real.sqrt_mul (div_nonneg hC.le ht0.le), div_mul_cancel₀ _ ht0.ne']
      calc
        _ ≤ 16 * Real.sqrt (C / t) * gaussianPrimeMomentScale σ X := by convert hh' using 1 <;> (first | rfl | ring)
        _ = _ := by
          apply (eq_div_iff hst.ne').mpr
          calc
            _ = 16 * (Real.sqrt (C / t) * Real.sqrt t) * gaussianPrimeMomentScale σ X := by ring
            _ = _ := by rw [hr]
    rw [← sum_Ico_consecutive (fun n => ((vonMangoldt n : ℝ) : ℂ) * gaussianPrimeMomentWeight σ α ξ t n)
      (by omega : 1 ≤ U + 1) hB,
      sum_vonMangoldt_block_decomp (V := V) (by omega : U < U + 1)]
    apply (norm_add_le _ _).trans
    have hblock := (norm_add_le
      (-∑ n ∈ Ico (U + 1) B, ((((zeta : ArithmeticFunction ℝ) * truncAF vonMangoldt U *
        truncAF (moebius : ArithmeticFunction ℝ) V) n : ℝ) : ℂ) * gaussianPrimeMomentWeight σ α ξ t n)
      (∑ n ∈ Ico (U + 1) B, (((ArithmeticFunction.log * truncAF (moebius : ArithmeticFunction ℝ) V) n : ℝ) : ℂ) *
        gaussianPrimeMomentWeight σ α ξ t n))
    rw [norm_neg] at hblock
    have hthree := (norm_add_le (_ : ℂ)
      (∑ n ∈ Ico (U + 1) B, (((typeIILong U * typeIIShort V) n : ℝ) : ℂ) *
        gaussianPrimeMomentWeight σ α ξ t n)).trans (_root_.add_le_add hblock le_rfl)
    have hb' := hthree.trans (_root_.add_le_add (_root_.add_le_add hz hl) htypeII)
    have htotal := _root_.add_le_add hhead hb'
    apply htotal.trans
    have hnon : 0 ≤ gaussianPrimeMomentScale σ X / Real.sqrt t := by positivity
    simp only [div_eq_mul_inv] at hnon ⊢
    nlinarith only [hnon]
  have hs := summable_gaussianPrimeMoment_vonMangoldt hσ hα ξ t
  apply le_of_tendsto hs.tendsto_sum_tsum_nat.norm
  filter_upwards [eventually_ge_atTop (U + 1)] with B hB
  have hh := hfinite B hB
  have hz : ((vonMangoldt 0 : ℝ) : ℂ) * gaussianPrimeMomentWeight σ α ξ t 0 = 0 := by simp
  have he : (∑ n ∈ Ico 1 B, ((vonMangoldt n : ℝ) : ℂ) * gaussianPrimeMomentWeight σ α ξ t n) =
      ∑ n ∈ range B, ((vonMangoldt n : ℝ) : ℂ) * gaussianPrimeMomentWeight σ α ξ t n := by
    rw [sum_Ico_eq_sub _ (by omega : 1 ≤ B), sum_range_one, hz, sub_zero]
  rwa [he] at hh

/-- The arithmetic first moment is the literal rotated prime observable. -/
theorem rotatedGaussianMomentPrimeSum_eq_arithmetic (σ y φ t : ℝ) :
    rotatedGaussianMomentPrimeSum ((σ : ℂ) + t * I) y φ t =
      ∑' n : ℕ, ((vonMangoldt n : ℝ) : ℂ) * gaussianPrimeMomentWeight σ
        (complexGaussianDamping y φ).re (-(complexGaussianDamping y φ).im) t n := by
  let ε := complexGaussianDamping y φ
  have hε : (ε.re : ℂ) - (-ε.im : ℝ) * I = ε := by apply Complex.ext <;> simp
  unfold rotatedGaussianMomentPrimeSum
  apply tsum_congr
  intro n
  by_cases hn : n = 0
  · subst n
    simp [LSeries.term_def, gaussianPrimeMomentWeight]
  · have hn1 : 1 ≤ n := by omega
    change LSeries.term (fun n => (vonMangoldt n : ℂ)) ((σ : ℂ) + t * I) n *
      (ε / t * (n : ℂ) ^ 2) * Complex.exp (-(ε * (n : ℂ) ^ 2)) =
      ((vonMangoldt n : ℝ) : ℂ) * gaussianPrimeMomentWeight σ ε.re (-ε.im) t n
    rw [LSeries.term_of_ne_zero hn, gaussianPrimeMomentWeight,
      gaussianPrimeWeight_eq σ ε.re (-ε.im) t hn1, hε, Complex.cpow_neg]
    ring


/-- The independent arithmetic estimate applies to the literal rotated prime
observable used by the exceptional-divisor filters. -/
theorem exists_rotatedGaussianMomentPrimeSum_arithmetic_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (σ y φ t X : ℝ) (U V : ℕ),
      let ε := complexGaussianDamping y φ
      0 ≤ σ → σ < 1 → 0 < -ε.im → 2 ≤ t → (-ε.im) / (2 * t) ≤ ε.re → ε.re ≤ -ε.im →
      ε.re * X ^ 2 = 2 → 128 * t * Real.log t ≤ Real.pi * U → 2 * t ≤ V →
      t * ((U * V : ℕ) : ℝ) ≤ X →
      ‖rotatedGaussianMomentPrimeSum ((σ : ℂ) + t * I) y φ t‖ ≤
        C * gaussianPrimeMomentScale σ X / Real.sqrt t := by
  obtain ⟨C, hC, hb⟩ := exists_gaussianPrimeMoment_vonMangoldt_bound
  refine ⟨C, hC, ?_⟩
  intro σ y φ t X U V
  dsimp only
  intro hσ hσ1 hξ ht hlower hupper hscale hU hV hUVX
  rw [rotatedGaussianMomentPrimeSum_eq_arithmetic]
  exact hb σ (complexGaussianDamping y φ).re (-(complexGaussianDamping y φ).im) t X U V
    hσ hσ1 hξ ht hlower hupper hscale hU hV hUVX

#print axioms norm_sum_gaussianMoment_zeta_trunc_conv_le
#print axioms norm_sum_gaussianMoment_log_trunc_moebius_le
#print axioms norm_sum_gaussianPrimeMoment_vonMangoldt_head_le
#print axioms summable_gaussianPrimeMoment_vonMangoldt
#print axioms exists_gaussianPrimeMoment_vonMangoldt_bound
#print axioms rotatedGaussianMomentPrimeSum_eq_arithmetic
#print axioms exists_rotatedGaussianMomentPrimeSum_arithmetic_bound
end GaloisForLFunctions.ExceptionalLayerTheory
