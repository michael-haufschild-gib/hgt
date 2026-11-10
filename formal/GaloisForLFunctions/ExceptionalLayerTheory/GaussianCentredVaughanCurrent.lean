import GaloisForLFunctions.ExceptionalLayerTheory.GaussianSecondMomentTypeIPole
import GaloisForLFunctions.ExceptionalLayerTheory.GaussianLogSecondMomentTypeIPole
import GaloisForLFunctions.ExceptionalLayerTheory.GaussianMomentPrimeBound

/-!
# The centred Gaussian Vaughan current

The logarithmic and constant continuum terms centre the actual type-II
convolution. Second-order lattice cancellation controls its difference
from the pole-subtracted prime current, uniformly in the two cutoffs.
-/

open Complex Finset Filter Topology RHTower RHTower.Sieve ArithmeticFunction

noncomputable section
namespace GaloisForLFunctions.ExceptionalLayerTheory

/-- The two signed continuum terms belonging to the actual type-II sum. -/
def gaussianCentredVaughanCurrent (σ α ξ t : ℝ) (U V : ℕ) : ℂ :=
  (∑' n : ℕ, (((typeIILong U * typeIIShort V) n : ℝ) : ℂ) *
    gaussianPrimeMomentWeight σ α ξ t n) +
  (∑ b ∈ Icc 1 V, ((truncAF (moebius : ArithmeticFunction ℝ) V b : ℝ) : ℂ) / (b : ℂ)) *
    gaussianFirstMomentLogPole ((σ : ℂ) + t * I) ((α : ℂ) - ξ * I) t -
  (1 + (∑ b ∈ Icc 1 (U * V),
      (((truncAF vonMangoldt U * truncAF (moebius : ArithmeticFunction ℝ) V) b : ℝ) : ℂ) / (b : ℂ)) +
    ∑ b ∈ Icc 1 V, ((truncAF (moebius : ArithmeticFunction ℝ) V b : ℝ) : ℂ) *
      (Real.log (b : ℝ) : ℂ) / (b : ℂ)) *
    gaussianFirstMomentPole ((σ : ℂ) + t * I) ((α : ℂ) - ξ * I) t

private theorem summable_gaussianMoment_convolution {σ α : ℝ}
    (hσ : 0 ≤ σ) (hα : 0 < α) (ξ t : ℝ) (f g : ArithmeticFunction ℝ)
    (hf : ∀ n, 1 ≤ n → |f n| ≤ (n : ℝ)) (hg : ∀ n, |g n| ≤ 1) :
    Summable (fun n : ℕ => (((f * g) n : ℝ) : ℂ) * gaussianPrimeMomentWeight σ α ξ t n) := by
  apply ((RHTower.summable_pow_mul_exp_neg_nat_sq 4 hα).mul_left
    ‖((α : ℂ) - ξ * I) / t‖).of_norm_bounded
  intro n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hc : ‖(((f * g) n : ℝ) : ℂ)‖ ≤ (n : ℝ) ^ 2 := by
    rw [coe_mul_apply]
    calc
      _ ≤ ∑ p ∈ n.divisorsAntidiagonal, ‖(f p.1 : ℂ) * (g p.2 : ℂ)‖ := norm_sum_le _ _
      _ ≤ ∑ p ∈ n.divisorsAntidiagonal, (n : ℝ) := by
        apply sum_le_sum
        intro p hp
        have hp' := Nat.mem_divisorsAntidiagonal.mp hp
        have hp1 : 1 ≤ p.1 := by
          by_contra h
          have hz : p.1 = 0 := by omega
          rw [hz, zero_mul] at hp'
          exact hp'.2 hp'.1.symm
        have hpn : p.1 ≤ n := Nat.le_of_dvd hn ⟨p.2, hp'.1.symm⟩
        rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
        calc
          _ ≤ (p.1 : ℝ) * 1 := mul_le_mul (hf p.1 hp1) (hg p.2) (abs_nonneg _) (by positivity)
          _ ≤ (n : ℝ) := by simpa using (show (p.1 : ℝ) ≤ n by exact_mod_cast hpn)
      _ = (n.divisors.card : ℝ) * n := by simp [card_divisorsAntidiagonal]
      _ ≤ (n : ℝ) * n := by
        apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg n)
        exact_mod_cast Nat.card_divisors_le_self n
      _ = _ := by ring
  have hp : (n : ℝ) ^ (-(σ - 2)) ≤ (n : ℝ) ^ 2 := by
    simpa only [Real.rpow_two] using Real.rpow_le_rpow_of_exponent_le
      (by exact_mod_cast hn : (1 : ℝ) ≤ n) (by linarith only [hσ] : -(σ - 2) ≤ 2)
  rw [norm_mul, gaussianPrimeMomentWeight_eq_shift σ α ξ t hn, norm_mul, norm_gaussianPrimeWeight_exact]
  calc
    _ ≤ (n : ℝ) ^ 2 * (‖((α : ℂ) - ξ * I) / t‖ *
        ((n : ℝ) ^ 2 * Real.exp (-α * (n : ℝ) ^ 2))) := by gcongr
    _ = _ := by ring

private theorem summable_gaussianMoment_first_typeI {σ α : ℝ}
    (hσ : 0 ≤ σ) (hα : 0 < α) (ξ t : ℝ) (U V : ℕ) :
    Summable (fun n : ℕ =>
      ((((zeta : ArithmeticFunction ℝ) * (truncAF vonMangoldt U *
        truncAF (moebius : ArithmeticFunction ℝ) V)) n : ℝ) : ℂ) *
          gaussianPrimeMomentWeight σ α ξ t n) := by
  rw [mul_comm (zeta : ArithmeticFunction ℝ)]
  apply summable_gaussianMoment_convolution hσ hα
  · intro n hn
    have hh := Real.log_le_sub_one_of_pos (by exact_mod_cast hn : (0 : ℝ) < n)
    exact (abs_truncAF_conv_le_log U V n).trans (by linarith only [hh])
  · intro n
    by_cases hn : n = 0 <;> simp [hn]

private theorem summable_gaussianMoment_log_typeI {σ α : ℝ}
    (hσ : 0 ≤ σ) (hα : 0 < α) (ξ t : ℝ) (V : ℕ) :
    Summable (fun n : ℕ =>
      (((ArithmeticFunction.log * truncAF (moebius : ArithmeticFunction ℝ) V) n : ℝ) : ℂ) *
        gaussianPrimeMomentWeight σ α ξ t n) := by
  apply summable_gaussianMoment_convolution hσ hα
  · intro n hn
    change |Real.log (n : ℝ)| ≤ (n : ℝ)
    rw [abs_of_nonneg (Real.log_nonneg (by exact_mod_cast hn))]
    have hh := Real.log_le_sub_one_of_pos (by exact_mod_cast hn : (0 : ℝ) < n)
    linarith only [hh]
  · exact abs_truncAF_moebius_le_one V

/-- Vaughan's identity holds for the complete absolutely convergent first moment. -/
theorem tsum_gaussianMoment_vaughan {σ α : ℝ} (hσ : 0 ≤ σ) (hα : 0 < α)
    (ξ t : ℝ) (U V : ℕ) :
    (∑' n : ℕ, ((vonMangoldt n : ℝ) : ℂ) * gaussianPrimeMomentWeight σ α ξ t n) =
    (∑ n ∈ Ico 1 (U + 1), ((vonMangoldt n : ℝ) : ℂ) * gaussianPrimeMomentWeight σ α ξ t n) -
    (∑' n : ℕ, ((((zeta : ArithmeticFunction ℝ) * (truncAF vonMangoldt U *
      truncAF (moebius : ArithmeticFunction ℝ) V)) n : ℝ) : ℂ) * gaussianPrimeMomentWeight σ α ξ t n) +
    (∑' n : ℕ, (((ArithmeticFunction.log * truncAF (moebius : ArithmeticFunction ℝ) V) n : ℝ) : ℂ) *
      gaussianPrimeMomentWeight σ α ξ t n) +
    ∑' n : ℕ, (((typeIILong U * typeIIShort V) n : ℝ) : ℂ) * gaussianPrimeMomentWeight σ α ξ t n := by
  let W := gaussianPrimeMomentWeight σ α ξ t
  have hh : Summable (fun n : ℕ => ((truncAF vonMangoldt U n : ℝ) : ℂ) * W n) :=
    summable_of_ne_finset_zero (s := Ico 1 (U + 1)) fun n hn => by
      by_cases h0 : n = 0
      · simp [h0]
      · rw [truncAF_apply_of_gt (by simp only [mem_Ico] at hn; omega), Complex.ofReal_zero, zero_mul]
  have hz := summable_gaussianMoment_first_typeI hσ hα ξ t U V
  have hl := summable_gaussianMoment_log_typeI hσ hα ξ t V
  have hII : Summable (fun n : ℕ => (((typeIILong U * typeIIShort V) n : ℝ) : ℂ) * W n) := by
    have hs := (summable_gaussianVaughan_moment_typeII hσ hα ξ t U V).mul_left
      (((α : ℂ) - ξ * I) / t)
    apply hs.congr
    intro n
    by_cases hn : n = 0
    · simp [hn]
    · dsimp only [W]
      rw [gaussianPrimeMomentWeight_eq_shift σ α ξ t (by omega)]
      ring
  have he (n : ℕ) : ((vonMangoldt n : ℝ) : ℂ) * W n =
      ((truncAF vonMangoldt U n : ℝ) : ℂ) * W n -
      ((((zeta : ArithmeticFunction ℝ) * (truncAF vonMangoldt U *
        truncAF (moebius : ArithmeticFunction ℝ) V)) n : ℝ) : ℂ) * W n +
      (((ArithmeticFunction.log * truncAF (moebius : ArithmeticFunction ℝ) V) n : ℝ) : ℂ) * W n +
      (((typeIILong U * typeIIShort V) n : ℝ) : ℂ) * W n := by
    have hv := congrArg (fun f : ArithmeticFunction ℝ => f n) (vaughan_identity U V)
    simp only [ArithmeticFunction.add_apply, mul_assoc] at hv
    change vonMangoldt n = truncAF vonMangoldt U n - _ + _ + (typeIILong U * typeIIShort V) n at hv
    rw [hv]
    push_cast
    ring
  have hhead : (∑' n : ℕ, ((truncAF vonMangoldt U n : ℝ) : ℂ) * W n) =
      ∑ n ∈ Ico 1 (U + 1), ((vonMangoldt n : ℝ) : ℂ) * W n := by
    rw [tsum_eq_sum (s := Ico 1 (U + 1)) (fun n hn => by
      by_cases h0 : n = 0
      · simp [h0]
      · rw [truncAF_apply_of_gt (by simp only [mem_Ico] at hn; omega), Complex.ofReal_zero, zero_mul])]
    apply sum_congr rfl
    intro n hn
    rw [truncAF_apply, if_pos (by have := (mem_Ico.mp hn).2; omega)]
  rw [tsum_congr he, ((hh.sub hz).add hl).tsum_add hII,
    (hh.sub hz).tsum_add hl, hh.tsum_sub hz, hhead]

/-- Only the finite head and the two lattice errors separate the centred
arithmetic convolution from the pole-subtracted complete prime current. -/
theorem norm_gaussianPrimeMoment_sub_centredVaughan_le {σ α ξ t X : ℝ}
    (hσ : 0 ≤ σ) (hσ1 : σ < 1) (hα : 0 < α) (hαξ : α ≤ ξ)
    (ht : 2 ≤ t) (hξ : ξ ≤ 2 * α * t) (hX : 0 < X) (hscale : α * X ^ 2 = 2)
    {U V : ℕ} (hU : 1 ≤ U) (hV : 1 ≤ V) (hVX : (V : ℝ) ≤ X) :
    ‖((∑' n : ℕ, ((vonMangoldt n : ℝ) : ℂ) * gaussianPrimeMomentWeight σ α ξ t n) -
      gaussianFirstMomentPole ((σ : ℂ) + t * I) ((α : ℂ) - ξ * I) t) -
      gaussianCentredVaughanCurrent σ α ξ t U V‖ ≤
    4 * α * (U : ℝ) ^ 2 * (U : ℝ) ^ (1 - σ) * Real.log U +
    2 * gaussianSecondMomentLatticeConstant σ * t ^ 2 * X ^ (-1 - σ) *
      ((U * V : ℕ) : ℝ) ^ 2 * Real.log ((U * V : ℕ) : ℝ) +
    gaussianLogSecondMomentConstant σ * t ^ 2 * X ^ (-1 - σ) * (1 + Real.log X) * (V : ℝ) ^ 2 := by
  have hH := norm_sum_gaussianPrimeMoment_vonMangoldt_head_le hσ1 hα.le hαξ
    (by linarith only [ht]) hξ hU
  have hZ := norm_tsum_gaussianMoment_zeta_trunc_conv_sub_pole_second_physical_le
    hσ hσ1 hα hαξ ht hξ hX hscale (Nat.mul_pos hU hV)
  have hL := norm_tsum_gaussianMoment_log_trunc_moebius_sub_poles_second_le
    hσ hσ1 hα hαξ ht hξ hX hscale hVX
  rw [tsum_gaussianMoment_vaughan hσ hα ξ t U V]
  unfold gaussianCentredVaughanCurrent
  have he : ∀ H Z L T A B D P Q : ℂ,
      (H - Z + L + T - P) - (T + B * Q - (1 + A + D) * P) =
        (H - (Z - A * P)) + (L - (B * Q - D * P)) := by intros; ring
  rw [he]
  exact (norm_add_le _ _).trans (_root_.add_le_add
    ((norm_sub_le _ _).trans (_root_.add_le_add hH hZ)) hL)

private theorem centred_current_scale_budgets {σ α t X : ℝ}
    (hσ : 1 / 2 ≤ σ) (hα : 0 < α) (ht : 2 ≤ t)
    (hscale : α * X ^ 2 = 2) (hTX : t ^ 8 ≤ X)
    {U V : ℕ} (hU : 1 ≤ U) (hV : 1 ≤ V)
    (hUt : (U : ℝ) ≤ t ^ 2) (hVt : (V : ℝ) ≤ t ^ 2) :
    4 * α * (U : ℝ) ^ 2 * (U : ℝ) ^ (1 - σ) * Real.log U ≤ 8 * t ^ 7 / X ∧
    t ^ 2 * X ^ (-1 - σ) * ((U * V : ℕ) : ℝ) ^ 2 * Real.log ((U * V : ℕ) : ℝ) ≤ 4 * t ^ 7 / X ∧
    t ^ 2 * X ^ (-1 - σ) * (1 + Real.log X) * (V : ℝ) ^ 2 ≤ 3 * t ^ 7 / X := by
  have ht0 : 0 < t := by linarith only [ht]
  have ht1 : 1 ≤ t := by linarith only [ht]
  have hX1 : 1 ≤ X := (one_le_pow₀ ht1).trans hTX
  have hX : 0 < X := zero_lt_one.trans_le hX1
  have hrt : 0 < Real.sqrt X := Real.sqrt_pos.mpr hX
  have hrt2 := Real.sq_sqrt hX.le
  have hU1 : (1 : ℝ) ≤ U := by exact_mod_cast hU
  have hK1 : (1 : ℝ) ≤ ((U * V : ℕ) : ℝ) := by exact_mod_cast Nat.mul_pos hU hV
  have hKt : ((U * V : ℕ) : ℝ) ≤ t ^ 4 := by
    push_cast
    calc
      _ ≤ t ^ 2 * t ^ 2 := mul_le_mul hUt hVt (Nat.cast_nonneg V) (by positivity)
      _ = _ := by ring
  have hroot : t ^ 4 ≤ Real.sqrt X := by
    have he : (t ^ 4) ^ 2 = t ^ 8 := by ring
    nlinarith only [he, hrt2, hTX, hrt.le, sq_nonneg (t ^ 4 - Real.sqrt X)]
  have ht8 : t ≤ t ^ 8 := by simpa only [pow_one] using pow_le_pow_right₀ ht1 (show 1 ≤ 8 by omega)
  have hXt : t ≤ X := ht8.trans hTX
  have ht7 : t ^ 7 ≤ X := (pow_le_pow_right₀ ht1 (by omega : 7 ≤ 8)).trans hTX
  have hq : X ^ (-1 - σ) * (X * Real.sqrt X) ≤ 1 := by
    have hp := Real.rpow_le_rpow_of_exponent_le hX1
      (by linarith only [hσ] : -1 - σ ≤ -(1 + 1 / (2 : ℝ)))
    have he : X ^ (-(1 + 1 / (2 : ℝ))) * (X * Real.sqrt X) = 1 := by
      rw [Real.rpow_neg hX.le, Real.rpow_add hX, Real.rpow_one, ← Real.sqrt_eq_rpow]
      field_simp [hX.ne', hrt.ne']
    exact (mul_le_mul_of_nonneg_right hp (by positivity)).trans_eq he
  have hq0 : 0 ≤ X ^ (-1 - σ) := Real.rpow_nonneg hX.le _
  have hlogK : Real.log ((U * V : ℕ) : ℝ) ≤ 4 * t := by
    have hh := Real.log_le_log (zero_lt_one.trans_le hK1) hKt
    rw [Real.log_pow] at hh
    have hl := Real.log_le_sub_one_of_pos ht0
    norm_num only [Nat.cast_ofNat] at hh
    linarith only [hh, hl]
  have hlogX : 1 + Real.log X ≤ 3 * Real.sqrt X := by
    have he : Real.log X = 2 * Real.log (Real.sqrt X) := by
      conv_lhs => rw [← hrt2]
      rw [Real.log_pow]
      norm_num
    have hh := Real.log_le_sub_one_of_pos hrt
    rw [he]
    linarith only [hh, hrt.le]
  have hlogU : Real.log U ≤ (U : ℝ) := by
    have hh := Real.log_le_sub_one_of_pos (zero_lt_one.trans_le hU1)
    linarith only [hh]
  have hup : (U : ℝ) ^ (1 - σ) ≤ (U : ℝ) := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hU1
      (by linarith only [hσ] : 1 - σ ≤ 1)
  have hU4 : (U : ℝ) ^ 4 ≤ t ^ 7 * X := by
    calc
      _ ≤ (t ^ 2) ^ 4 := pow_le_pow_left₀ (Nat.cast_nonneg U) hUt 4
      _ = t ^ 7 * t := by ring
      _ ≤ t ^ 7 * X := mul_le_mul_of_nonneg_left hXt (by positivity)
  refine ⟨?_, ?_, ?_⟩
  · apply (le_div_iff₀ hX).mpr
    calc
      _ ≤ 4 * α * (U : ℝ) ^ 2 * (U : ℝ) * (U : ℝ) * X := by gcongr
      _ = 4 * α * (U : ℝ) ^ 4 * X := by ring
      _ ≤ 4 * α * (t ^ 7 * X) * X := by gcongr
      _ = 8 * t ^ 7 := by linear_combination 4 * t ^ 7 * hscale
  · apply (le_div_iff₀ hX).mpr
    calc
      _ ≤ t ^ 2 * X ^ (-1 - σ) * (t ^ 4) ^ 2 * (4 * t) * X := by gcongr
      _ = 4 * t ^ 7 * (X ^ (-1 - σ) * X * t ^ 4) := by ring
      _ ≤ 4 * t ^ 7 * (X ^ (-1 - σ) * X * Real.sqrt X) := by gcongr
      _ ≤ 4 * t ^ 7 * 1 := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        simpa only [mul_assoc] using hq
      _ = _ := by ring
  · apply (le_div_iff₀ hX).mpr
    calc
      _ ≤ t ^ 2 * X ^ (-1 - σ) * (3 * Real.sqrt X) * (t ^ 2) ^ 2 * X := by gcongr
      _ = 3 * t ^ 6 * (X ^ (-1 - σ) * (X * Real.sqrt X)) := by ring
      _ ≤ 3 * t ^ 6 * 1 := mul_le_mul_of_nonneg_left hq (by positivity)
      _ ≤ 3 * t ^ 7 := by
        rw [mul_one]
        exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ ht1 (by omega : 6 ≤ 7)) (by norm_num)

/-- The full prime-current reduction retains inverse observation length,
uniformly over quadratic Vaughan cutoffs. -/
theorem norm_gaussianPrimeMoment_sub_centredVaughan_le_scale {σ α ξ t X : ℝ}
    (hσ : 1 / 2 ≤ σ) (hσ1 : σ < 1) (hα : 0 < α) (hαξ : α ≤ ξ)
    (ht : 2 ≤ t) (hξ : ξ ≤ 2 * α * t) (hscale : α * X ^ 2 = 2) (hTX : t ^ 8 ≤ X)
    {U V : ℕ} (hU : 1 ≤ U) (hV : 1 ≤ V)
    (hUt : (U : ℝ) ≤ t ^ 2) (hVt : (V : ℝ) ≤ t ^ 2) :
    ‖((∑' n : ℕ, ((vonMangoldt n : ℝ) : ℂ) * gaussianPrimeMomentWeight σ α ξ t n) -
      gaussianFirstMomentPole ((σ : ℂ) + t * I) ((α : ℂ) - ξ * I) t) -
      gaussianCentredVaughanCurrent σ α ξ t U V‖ ≤
    (8 * gaussianSecondMomentLatticeConstant σ + 3 * gaussianLogSecondMomentConstant σ + 8) * t ^ 7 / X := by
  have ht1 : 1 ≤ t := by linarith only [ht]
  have hX : 0 < X := (by positivity : 0 < t ^ 8).trans_le hTX
  have hVX : (V : ℝ) ≤ X := hVt.trans
    ((pow_le_pow_right₀ ht1 (by omega : 2 ≤ 8)).trans hTX)
  have hh := norm_gaussianPrimeMoment_sub_centredVaughan_le
    (by linarith only [hσ]) hσ1 hα hαξ ht hξ hX hscale hU hV hVX
  obtain ⟨hH, hZ, hL⟩ := centred_current_scale_budgets hσ hα ht hscale hTX hU hV hUt hVt
  have hD := gaussianSecondMomentLatticeConstant_nonneg hσ1
  have hC := gaussianLogSecondMomentConstant_nonneg hσ1
  have hZ' := mul_le_mul_of_nonneg_left hZ (by positivity : 0 ≤ 2 * gaussianSecondMomentLatticeConstant σ)
  have hL' := mul_le_mul_of_nonneg_left hL hC
  have hsum := _root_.add_le_add (_root_.add_le_add hH hZ') hL'
  apply hh.trans
  convert hsum using 1 <;> ring

/-- Above the eighth-power observation scale, the full prime current and
centred type II differ by a vanishing error, uniformly in quadratic cutoffs. -/
theorem norm_gaussianPrimeMoment_sub_centredVaughan_le_inv {σ α ξ t X : ℝ}
    (hσ : 1 / 2 ≤ σ) (hσ1 : σ < 1) (hα : 0 < α) (hαξ : α ≤ ξ)
    (ht : 2 ≤ t) (hξ : ξ ≤ 2 * α * t) (hscale : α * X ^ 2 = 2) (hTX : t ^ 8 ≤ X)
    {U V : ℕ} (hU : 1 ≤ U) (hV : 1 ≤ V)
    (hUt : (U : ℝ) ≤ t ^ 2) (hVt : (V : ℝ) ≤ t ^ 2) :
    ‖((∑' n : ℕ, ((vonMangoldt n : ℝ) : ℂ) * gaussianPrimeMomentWeight σ α ξ t n) -
      gaussianFirstMomentPole ((σ : ℂ) + t * I) ((α : ℂ) - ξ * I) t) -
      gaussianCentredVaughanCurrent σ α ξ t U V‖ ≤
    (8 * gaussianSecondMomentLatticeConstant σ + 3 * gaussianLogSecondMomentConstant σ + 8) / t := by
  have ht0 : 0 < t := by linarith only [ht]
  have hX : 0 < X := (by positivity : 0 < t ^ 8).trans_le hTX
  have hK : 0 ≤ 8 * gaussianSecondMomentLatticeConstant σ +
      3 * gaussianLogSecondMomentConstant σ + 8 := by
    have hD := gaussianSecondMomentLatticeConstant_nonneg hσ1
    have hC := gaussianLogSecondMomentConstant_nonneg hσ1
    positivity
  apply (norm_gaussianPrimeMoment_sub_centredVaughan_le_scale
    hσ hσ1 hα hαξ ht hξ hscale hTX hU hV hUt hVt).trans
  apply (div_le_div_iff₀ hX ht0).mpr
  calc
    _ = (8 * gaussianSecondMomentLatticeConstant σ +
        3 * gaussianLogSecondMomentConstant σ + 8) * t ^ 8 := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hTX hK

/-- The centred current is independent of the Vaughan cutoffs up to an
explicit inverse-height error throughout the long-observation regime. -/
theorem norm_gaussianCentredVaughan_cutoff_sub_le {σ α ξ t X : ℝ}
    (hσ : 1 / 2 ≤ σ) (hσ1 : σ < 1) (hα : 0 < α) (hαξ : α ≤ ξ)
    (ht : 2 ≤ t) (hξ : ξ ≤ 2 * α * t) (hscale : α * X ^ 2 = 2) (hTX : t ^ 8 ≤ X)
    {U₁ V₁ U₂ V₂ : ℕ} (hU₁ : 1 ≤ U₁) (hV₁ : 1 ≤ V₁) (hU₂ : 1 ≤ U₂) (hV₂ : 1 ≤ V₂)
    (hU₁t : (U₁ : ℝ) ≤ t ^ 2) (hV₁t : (V₁ : ℝ) ≤ t ^ 2)
    (hU₂t : (U₂ : ℝ) ≤ t ^ 2) (hV₂t : (V₂ : ℝ) ≤ t ^ 2) :
    ‖gaussianCentredVaughanCurrent σ α ξ t U₁ V₁ - gaussianCentredVaughanCurrent σ α ξ t U₂ V₂‖ ≤
      2 * (8 * gaussianSecondMomentLatticeConstant σ + 3 * gaussianLogSecondMomentConstant σ + 8) / t := by
  have h₁ := norm_gaussianPrimeMoment_sub_centredVaughan_le_inv
    hσ hσ1 hα hαξ ht hξ hscale hTX hU₁ hV₁ hU₁t hV₁t
  have h₂ := norm_gaussianPrimeMoment_sub_centredVaughan_le_inv
    hσ hσ1 hα hαξ ht hξ hscale hTX hU₂ hV₂ hU₂t hV₂t
  have htri (M C D : ℂ) : ‖C - D‖ ≤ ‖M - D‖ + ‖M - C‖ := by
    calc
      _ = ‖(M - D) - (M - C)‖ := by congr 1; ring
      _ ≤ _ := norm_sub_le _ _
  let M := (∑' n : ℕ, ((vonMangoldt n : ℝ) : ℂ) * gaussianPrimeMomentWeight σ α ξ t n) -
    gaussianFirstMomentPole ((σ : ℂ) + t * I) ((α : ℂ) - ξ * I) t
  let K := 8 * gaussianSecondMomentLatticeConstant σ + 3 * gaussianLogSecondMomentConstant σ + 8
  calc
    _ ≤ ‖M - gaussianCentredVaughanCurrent σ α ξ t U₂ V₂‖ +
        ‖M - gaussianCentredVaughanCurrent σ α ξ t U₁ V₁‖ := htri M _ _
    _ ≤ K / t + K / t := _root_.add_le_add h₂ h₁
    _ = _ := by dsimp only [K]; ring

#print axioms tsum_gaussianMoment_vaughan
#print axioms norm_gaussianPrimeMoment_sub_centredVaughan_le
#print axioms norm_gaussianPrimeMoment_sub_centredVaughan_le_scale
#print axioms norm_gaussianPrimeMoment_sub_centredVaughan_le_inv
#print axioms norm_gaussianCentredVaughan_cutoff_sub_le

end GaloisForLFunctions.ExceptionalLayerTheory
