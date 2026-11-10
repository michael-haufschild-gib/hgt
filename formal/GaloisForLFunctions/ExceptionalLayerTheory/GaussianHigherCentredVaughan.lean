import GaloisForLFunctions.ExceptionalLayerTheory.GaussianHigherLogTypeIPole

/-!
# Higher-moment centred Vaughan reduction

Every positive Gaussian moment admits the exact centred arithmetic current.
The first type-I remainder gains `2r` powers of the lattice spacing; the
logarithmic remainder needs only first variation when its cutoff is small.
-/

open Complex Finset Filter Topology RHTower RHTower.Sieve ArithmeticFunction
noncomputable section
namespace GaloisForLFunctions.ExceptionalLayerTheory

/-- The two signed continuum terms belonging to the actual type-II sum. -/
def gaussianHigherCentredVaughanCurrent (r : ℕ) (σ t : ℝ) (ε : ℂ) (U V : ℕ) : ℂ :=
  (∑' n : ℕ, (((typeIILong U * typeIIShort V) n : ℝ) : ℂ) *
    gaussianHigherPrimeMomentWeight r σ t ε n) +
  (∑ b ∈ Icc 1 V, ((truncAF (moebius : ArithmeticFunction ℝ) V b : ℝ) : ℂ) / (b : ℂ)) *
    gaussianHigherMomentLogPole r ((σ : ℂ) + t * I) ε t -
  (1 + (∑ b ∈ Icc 1 (U * V),
      (((truncAF vonMangoldt U * truncAF (moebius : ArithmeticFunction ℝ) V) b : ℝ) : ℂ) / (b : ℂ)) +
    ∑ b ∈ Icc 1 V, ((truncAF (moebius : ArithmeticFunction ℝ) V b : ℝ) : ℂ) *
      (Real.log (b : ℝ) : ℂ) / (b : ℂ)) *
    gaussianHigherMomentPole r ((σ : ℂ) + t * I) ε t

private theorem summable_higherMoment_convolution (r : ℕ) {σ : ℝ} {ε : ℂ}
    (hσ : 0 ≤ σ) (hε : 0 < ε.re) (t : ℝ) (f g : ArithmeticFunction ℝ)
    (hf : ∀ n, 1 ≤ n → |f n| ≤ (n : ℝ)) (hg : ∀ n, |g n| ≤ 1) :
    Summable (fun n : ℕ => (((f * g) n : ℝ) : ℂ) * gaussianHigherPrimeMomentWeight r σ t ε n) := by
  apply ((RHTower.summable_pow_mul_exp_neg_nat_sq (2 * r + 2) hε).mul_left
    ‖(ε / (t : ℂ)) ^ r‖).of_norm_bounded
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
  rw [norm_mul]
  calc
    _ ≤ (n : ℝ) ^ 2 * (‖(ε / (t : ℂ)) ^ r‖ *
        (n : ℝ) ^ (2 * r) * Real.exp (-ε.re * (n : ℝ) ^ 2)) :=
      mul_le_mul hc (norm_gaussianHigherPrimeMomentWeight_le r hσ t ε hn)
        (norm_nonneg _) (by positivity)
    _ = _ := by rw [pow_add]; ring

private theorem summable_higherMoment_first_typeI (r : ℕ) {σ : ℝ} {ε : ℂ}
    (hσ : 0 ≤ σ) (hε : 0 < ε.re) (t : ℝ) (U V : ℕ) :
    Summable (fun n : ℕ =>
      ((((zeta : ArithmeticFunction ℝ) * (truncAF vonMangoldt U *
        truncAF (moebius : ArithmeticFunction ℝ) V)) n : ℝ) : ℂ) *
          gaussianHigherPrimeMomentWeight r σ t ε n) := by
  rw [mul_comm (zeta : ArithmeticFunction ℝ)]
  apply summable_higherMoment_convolution r hσ hε
  · intro n hn
    have hh := Real.log_le_sub_one_of_pos (by exact_mod_cast hn : (0 : ℝ) < n)
    exact (abs_truncAF_conv_le_log U V n).trans (by linarith only [hh])
  · intro n
    by_cases hn : n = 0 <;> simp [hn]

private theorem summable_higherMoment_log_typeI (r : ℕ) {σ : ℝ} {ε : ℂ}
    (hσ : 0 ≤ σ) (hε : 0 < ε.re) (t : ℝ) (V : ℕ) :
    Summable (fun n : ℕ =>
      (((ArithmeticFunction.log * truncAF (moebius : ArithmeticFunction ℝ) V) n : ℝ) : ℂ) *
        gaussianHigherPrimeMomentWeight r σ t ε n) := by
  apply summable_higherMoment_convolution r hσ hε
  · intro n hn
    change |Real.log (n : ℝ)| ≤ (n : ℝ)
    rw [abs_of_nonneg (Real.log_nonneg (by exact_mod_cast hn))]
    have hh := Real.log_le_sub_one_of_pos (by exact_mod_cast hn : (0 : ℝ) < n)
    linarith only [hh]
  · exact abs_truncAF_moebius_le_one V

/-- Absolute convergence of the actual prime current at every positive damping. -/
theorem summable_gaussianHigherMoment_vonMangoldt (r : ℕ) {σ : ℝ} {ε : ℂ}
    (hσ : 0 ≤ σ) (hε : 0 < ε.re) (t : ℝ) :
    Summable (fun n : ℕ => ((vonMangoldt n : ℝ) : ℂ) *
      gaussianHigherPrimeMomentWeight r σ t ε n) := by
  apply ((RHTower.summable_pow_mul_exp_neg_nat_sq (2 * r + 1) hε).mul_left
    ‖(ε / (t : ℂ)) ^ r‖).of_norm_bounded
  intro n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hc : ‖((vonMangoldt n : ℝ) : ℂ)‖ ≤ (n : ℝ) := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg vonMangoldt_nonneg]
    have hh := Real.log_le_sub_one_of_pos (by exact_mod_cast hn : (0 : ℝ) < n)
    exact vonMangoldt_le_log.trans (by linarith only [hh])
  rw [norm_mul]
  calc
    _ ≤ (n : ℝ) * (‖(ε / (t : ℂ)) ^ r‖ *
        (n : ℝ) ^ (2 * r) * Real.exp (-ε.re * (n : ℝ) ^ 2)) :=
      mul_le_mul hc (norm_gaussianHigherPrimeMomentWeight_le r hσ t ε hn)
        (norm_nonneg _) (Nat.cast_nonneg n)
    _ = _ := by rw [pow_succ]; ring

/-- Vaughan's identity holds for the complete absolutely convergent higher moment. -/
theorem tsum_gaussianHigherMoment_vaughan (r : ℕ) {σ : ℝ} {ε : ℂ}
    (hσ : 0 ≤ σ) (hε : 0 < ε.re) (t : ℝ) (U V : ℕ) :
    (∑' n : ℕ, ((vonMangoldt n : ℝ) : ℂ) * gaussianHigherPrimeMomentWeight r σ t ε n) =
    (∑ n ∈ Ico 1 (U + 1), ((vonMangoldt n : ℝ) : ℂ) * gaussianHigherPrimeMomentWeight r σ t ε n) -
    (∑' n : ℕ, ((((zeta : ArithmeticFunction ℝ) * (truncAF vonMangoldt U *
      truncAF (moebius : ArithmeticFunction ℝ) V)) n : ℝ) : ℂ) * gaussianHigherPrimeMomentWeight r σ t ε n) +
    (∑' n : ℕ, (((ArithmeticFunction.log * truncAF (moebius : ArithmeticFunction ℝ) V) n : ℝ) : ℂ) *
      gaussianHigherPrimeMomentWeight r σ t ε n) +
    ∑' n : ℕ, (((typeIILong U * typeIIShort V) n : ℝ) : ℂ) * gaussianHigherPrimeMomentWeight r σ t ε n := by
  let W := gaussianHigherPrimeMomentWeight r σ t ε
  have hh : Summable (fun n : ℕ => ((truncAF vonMangoldt U n : ℝ) : ℂ) * W n) :=
    summable_of_ne_finset_zero (s := Ico 1 (U + 1)) fun n hn => by
      by_cases h0 : n = 0
      · simp [h0]
      · rw [truncAF_apply_of_gt (by simp only [mem_Ico] at hn; omega), Complex.ofReal_zero, zero_mul]
  have hz := summable_higherMoment_first_typeI r hσ hε t U V
  have hl := summable_higherMoment_log_typeI r hσ hε t V
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
  have hII : Summable (fun n : ℕ => (((typeIILong U * typeIIShort V) n : ℝ) : ℂ) * W n) := by
    have hs := (((summable_gaussianHigherMoment_vonMangoldt r hσ hε t).sub hh).add hz).sub hl
    apply hs.congr
    intro n
    dsimp only
    linear_combination he n
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

/-- The finite head keeps the exact abscissa power at every positive moment. -/
theorem norm_sum_gaussianHigherMoment_head_le (r : ℕ) (hr : r ≠ 0)
    {σ t : ℝ} {ε : ℂ} (hσ1 : σ < 1) (ht : 1 ≤ t) (hε : 0 < ε.re)
    (hsector : ‖ε‖ ≤ 4 * ε.re * t) {U : ℕ} (hU : 1 ≤ U) :
    ‖∑ n ∈ Ico 1 (U + 1), ((vonMangoldt n : ℝ) : ℂ) *
      gaussianHigherPrimeMomentWeight r σ t ε n‖ ≤
      (4 * ε.re) ^ r * (U : ℝ) ^ (2 * r) * (U : ℝ) ^ (1 - σ) * Real.log U := by
  have hU0 : (0 : ℝ) < U := by exact_mod_cast (show 0 < U by omega)
  have hlog : 0 ≤ Real.log U := Real.log_nonneg (by exact_mod_cast hU)
  have ht0 : 0 < t := zero_lt_one.trans_le ht
  have hr' : (2 : ℝ) ≤ ((2 * r : ℕ) : ℝ) := by exact_mod_cast (show 2 ≤ 2 * r by omega)
  have hpref : ‖(ε / (t : ℂ)) ^ r‖ ≤ (4 * ε.re) ^ r := by
    rw [norm_pow]
    apply pow_le_pow_left₀ (norm_nonneg _)
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht0]
    exact (div_le_iff₀ ht0).mpr hsector
  calc
    _ ≤ ∑ n ∈ Ico 1 (U + 1),
        (4 * ε.re) ^ r * (U : ℝ) ^ (((2 * r : ℕ) : ℝ) - σ) * Real.log U := by
      apply (norm_sum_le _ _).trans
      apply sum_le_sum
      intro n hn
      have hn1 : 1 ≤ n := (mem_Ico.mp hn).1
      have hnU : n ≤ U := by have := (mem_Ico.mp hn).2; omega
      have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
      have hΛ : ‖((vonMangoldt n : ℝ) : ℂ)‖ ≤ Real.log U := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg vonMangoldt_nonneg]
        exact vonMangoldt_le_log.trans
          (Real.log_le_log hn0 (by exact_mod_cast hnU))
      have hexp : Real.exp (-ε.re * (n : ℝ) ^ 2) ≤ 1 :=
        Real.exp_le_one_iff.mpr (by nlinarith only [mul_nonneg hε.le (sq_nonneg (n : ℝ))])
      have hpow : (n : ℝ) ^ (((2 * r : ℕ) : ℝ) - σ) ≤
          (U : ℝ) ^ (((2 * r : ℕ) : ℝ) - σ) :=
        Real.rpow_le_rpow hn0.le (by exact_mod_cast hnU) (by linarith only [hr', hσ1])
      have hw : ‖gaussianHigherPrimeMomentWeight r σ t ε n‖ ≤
          (4 * ε.re) ^ r * (U : ℝ) ^ (((2 * r : ℕ) : ℝ) - σ) := by
        unfold gaussianHigherPrimeMomentWeight gaussianMellinWeight
        rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hn0, Complex.norm_exp]
        have hre : (((2 * r : ℕ) : ℂ) - ((σ : ℂ) + t * I)).re =
            ((2 * r : ℕ) : ℝ) - σ := by simp
        have he : (-(ε * (n : ℂ) ^ 2)).re = -ε.re * (n : ℝ) ^ 2 := by simp [pow_two]
        simp only [Complex.ofReal_natCast]
        rw [hre, he]
        calc
          _ ≤ (4 * ε.re) ^ r *
              ((U : ℝ) ^ (((2 * r : ℕ) : ℝ) - σ) * 1) := by gcongr
          _ = _ := by ring
      rw [norm_mul]
      exact (mul_le_mul hΛ hw (norm_nonneg _) hlog).trans_eq (by ring)
    _ = _ := by
      simp only [sum_const, Nat.card_Ico, Nat.add_sub_cancel, nsmul_eq_mul]
      have hp : (U : ℝ) * (U : ℝ) ^ (((2 * r : ℕ) : ℝ) - σ) =
          (U : ℝ) ^ (2 * r) * (U : ℝ) ^ (1 - σ) := by
        calc
          _ = (U : ℝ) ^ (1 + (((2 * r : ℕ) : ℝ) - σ)) := by
            rw [Real.rpow_add hU0, Real.rpow_one]
          _ = _ := by
            rw [← Real.rpow_natCast U (2 * r), ← Real.rpow_add hU0]
            congr 1
            ring
      calc
        _ = (4 * ε.re) ^ r *
            ((U : ℝ) * (U : ℝ) ^ (((2 * r : ℕ) : ℝ) - σ)) * Real.log U := by ring
        _ = _ := by rw [hp]; ring

/-- At `Re ε X²=2`, the head gains the same length power as the first type-I error. -/
theorem norm_sum_gaussianHigherMoment_head_physical_le (r : ℕ) (hr : r ≠ 0)
    {σ t X : ℝ} {ε : ℂ} (hσ1 : σ < 1) (ht : 1 ≤ t) (hε : 0 < ε.re)
    (hsector : ‖ε‖ ≤ 4 * ε.re * t) (hX : 0 < X) (hscale : ε.re * X ^ 2 = 2)
    {U : ℕ} (hU : 1 ≤ U) (hUX : (U : ℝ) ≤ X) :
    ‖∑ n ∈ Ico 1 (U + 1), ((vonMangoldt n : ℝ) : ℂ) *
      gaussianHigherPrimeMomentWeight r σ t ε n‖ ≤
      8 ^ r * (U : ℝ) ^ (2 * r) * X ^ (1 - σ - (2 * r : ℕ)) * Real.log U := by
  have hp : (4 * ε.re) ^ r * X ^ (1 - σ) =
      8 ^ r * X ^ (1 - σ - (2 * r : ℕ)) := by
    have hx : X ^ (1 - σ) = X ^ (1 - σ - (2 * r : ℕ)) * (X ^ 2) ^ r := by
      rw [← pow_mul, ← Real.rpow_natCast X (2 * r), ← Real.rpow_add hX]
      congr 1
      ring
    rw [hx]
    calc
      _ = ((4 * ε.re) * X ^ 2) ^ r * X ^ (1 - σ - (2 * r : ℕ)) := by rw [mul_pow]; ring
      _ = _ := by rw [show 4 * ε.re * X ^ 2 = 8 by nlinarith only [hscale]]
  apply (norm_sum_gaussianHigherMoment_head_le r hr hσ1 ht hε hsector hU).trans
  calc
    _ ≤ (4 * ε.re) ^ r * (U : ℝ) ^ (2 * r) * X ^ (1 - σ) * Real.log U := by
      have hlog := Real.log_nonneg (by exact_mod_cast hU : (1 : ℝ) ≤ U)
      gcongr
      exact Real.rpow_le_rpow (Nat.cast_nonneg U) hUX (by linarith only [hσ1])
    _ = _ := by
      calc
        _ = ((4 * ε.re) ^ r * X ^ (1 - σ)) * (U : ℝ) ^ (2 * r) * Real.log U := by ring
        _ = _ := by rw [hp]; ring

/-- Exact signed Vaughan centring leaves only the finite head and the two
independently proved lattice errors. -/
theorem norm_gaussianHigherMoment_sub_centredVaughan_le (r : ℕ) (hr : r ≠ 0)
    {σ t X : ℝ} {ε : ℂ} (hσ : 0 ≤ σ) (hσ1 : σ < 1) (ht : 1 ≤ t)
    (hε : 0 < ε.re) (hsector : ‖ε‖ ≤ 4 * ε.re * t)
    (hX : 0 < X) (hscale : ε.re * X ^ 2 = 2) {U V : ℕ}
    (hU : 1 ≤ U) (hV : 1 ≤ V) (hUX : (U : ℝ) ≤ X) (hVX : (V : ℝ) ≤ X) :
    ‖((∑' n : ℕ, ((vonMangoldt n : ℝ) : ℂ) * gaussianHigherPrimeMomentWeight r σ t ε n) -
      gaussianHigherMomentPole r ((σ : ℂ) + t * I) ε t) -
      gaussianHigherCentredVaughanCurrent r σ t ε U V‖ ≤
      8 ^ r * (U : ℝ) ^ (2 * r) * X ^ (1 - σ - (2 * r : ℕ)) * Real.log U +
      (gaussianHigherMomentLatticeConstant r σ * (2 : ℝ) ^ (((2 * r : ℕ) + σ - 1) / 2)) *
        t ^ (2 * r) * X ^ (1 - σ - (2 * r : ℕ)) *
        ((U * V : ℕ) : ℝ) ^ (2 * r) * Real.log ((U * V : ℕ) : ℝ) +
      gaussianHigherLogMomentConstant r σ * t * X ^ (-σ) * (1 + Real.log X) * V := by
  have hH := norm_sum_gaussianHigherMoment_head_physical_le r hr hσ1 ht hε hsector hX hscale hU hUX
  have hZ := norm_tsum_gaussianHigherMoment_zeta_trunc_conv_sub_pole_le
    r hr hσ hσ1 ht hε hsector hX hscale (Nat.mul_pos hU hV)
  have hL := norm_tsum_gaussianHigherMoment_log_trunc_moebius_sub_poles_le
    r hr hσ hσ1 ht hε hsector hX hscale hVX
  rw [tsum_gaussianHigherMoment_vaughan r hσ hε t U V]
  unfold gaussianHigherCentredVaughanCurrent
  have he : ∀ H Z L T A B D P Q : ℂ,
      (H - Z + L + T - P) - (T + B * Q - (1 + A + D) * P) =
        (H - (Z - A * P)) + (L - (B * Q - D * P)) := by intros; ring
  rw [he]
  exact (norm_add_le _ _).trans (_root_.add_le_add
    ((norm_sub_le _ _).trans (_root_.add_le_add hH hZ)) hL)

/-- The all-order cutoff bound for the complete centred Vaughan reduction. -/
theorem norm_gaussianHigherMoment_sub_centredVaughan_product_le (r : ℕ) (hr : r ≠ 0)
    {σ t X : ℝ} {ε : ℂ} (hσ : 0 ≤ σ) (hσ1 : σ < 1) (ht : 1 ≤ t)
    (hε : 0 < ε.re) (hsector : ‖ε‖ ≤ 4 * ε.re * t)
    (hX : 0 < X) (hscale : ε.re * X ^ 2 = 2) {U V : ℕ}
    (hU : 1 ≤ U) (hV : 1 ≤ V) (hUVX : ((U * V : ℕ) : ℝ) ≤ X) :
    ‖((∑' n : ℕ, ((vonMangoldt n : ℝ) : ℂ) * gaussianHigherPrimeMomentWeight r σ t ε n) -
      gaussianHigherMomentPole r ((σ : ℂ) + t * I) ε t) -
      gaussianHigherCentredVaughanCurrent r σ t ε U V‖ ≤
      ((8 ^ r + gaussianHigherMomentLatticeConstant r σ *
          (2 : ℝ) ^ (((2 * r : ℕ) + σ - 1) / 2)) *
        t ^ (2 * r) * ((U * V : ℕ) : ℝ) ^ (2 * r) * X ^ (1 - σ - (2 * r : ℕ)) +
       gaussianHigherLogMomentConstant r σ * V * t * X ^ (-σ)) * (1 + Real.log X) := by
  have hU1 : (1 : ℝ) ≤ U := by exact_mod_cast hU
  have hV1 : (1 : ℝ) ≤ V := by exact_mod_cast hV
  have hUK : (U : ℝ) ≤ ((U * V : ℕ) : ℝ) := by
    push_cast
    nlinarith only [hU1, hV1]
  have hVK : (V : ℝ) ≤ ((U * V : ℕ) : ℝ) := by
    push_cast
    nlinarith only [hU1, hV1]
  have hUX := hUK.trans hUVX
  have hVX := hVK.trans hUVX
  have hU0 : (0 : ℝ) < U := by exact_mod_cast (show 0 < U by omega)
  have hK0 : (0 : ℝ) < ((U * V : ℕ) : ℝ) := by exact_mod_cast Nat.mul_pos hU hV
  have hX1 : 1 ≤ X := (by exact_mod_cast hU : (1 : ℝ) ≤ U).trans hUX
  have hlogX : 0 ≤ Real.log X := Real.log_nonneg hX1
  have hlogU : 0 ≤ Real.log U := Real.log_nonneg (by exact_mod_cast hU)
  have hlogK : 0 ≤ Real.log ((U * V : ℕ) : ℝ) :=
    Real.log_nonneg (by exact_mod_cast Nat.mul_pos hU hV)
  have hUlog : Real.log U ≤ 1 + Real.log X := by
    linarith only [Real.log_le_log hU0 hUX]
  have hKlog : Real.log ((U * V : ℕ) : ℝ) ≤ 1 + Real.log X := by
    linarith only [Real.log_le_log hK0 hUVX]
  have hC := gaussianHigherMomentLatticeConstant_nonneg r hσ1
  have htp : 1 ≤ t ^ (2 * r) := one_le_pow₀ ht
  have hH : 8 ^ r * (U : ℝ) ^ (2 * r) * X ^ (1 - σ - (2 * r : ℕ)) * Real.log U ≤
      8 ^ r * t ^ (2 * r) * ((U * V : ℕ) : ℝ) ^ (2 * r) *
        X ^ (1 - σ - (2 * r : ℕ)) * (1 + Real.log X) := by
    calc
      _ = 8 ^ r * 1 * (U : ℝ) ^ (2 * r) * X ^ (1 - σ - (2 * r : ℕ)) * Real.log U := by ring
      _ ≤ _ := by gcongr
  have hZ : (gaussianHigherMomentLatticeConstant r σ *
        (2 : ℝ) ^ (((2 * r : ℕ) + σ - 1) / 2)) *
      t ^ (2 * r) * X ^ (1 - σ - (2 * r : ℕ)) *
      ((U * V : ℕ) : ℝ) ^ (2 * r) * Real.log ((U * V : ℕ) : ℝ) ≤
      (gaussianHigherMomentLatticeConstant r σ *
        (2 : ℝ) ^ (((2 * r : ℕ) + σ - 1) / 2)) *
      t ^ (2 * r) * X ^ (1 - σ - (2 * r : ℕ)) *
      ((U * V : ℕ) : ℝ) ^ (2 * r) * (1 + Real.log X) := by gcongr
  apply (norm_gaussianHigherMoment_sub_centredVaughan_le
    r hr hσ hσ1 ht hε hsector hX hscale hU hV hUX hVX).trans
  exact (_root_.add_le_add_right (_root_.add_le_add hH hZ) _).trans_eq (by ring)

/-- Positive power slack absorbs the logarithm. The two explicit cutoff
budgets give an inverse-height error for the actual centred reduction. -/
theorem norm_gaussianHigherMoment_sub_centredVaughan_cutoff_le (r : ℕ) (hr : r ≠ 0)
    {σ t X η : ℝ} {ε : ℂ} (hσ : 0 ≤ σ) (hσ1 : σ < 1) (ht : 1 ≤ t)
    (hε : 0 < ε.re) (hsector : ‖ε‖ ≤ 4 * ε.re * t)
    (hX : 0 < X) (hscale : ε.re * X ^ 2 = 2) {U V : ℕ}
    (hU : 1 ≤ U) (hV : 1 ≤ V) (hUVX : ((U * V : ℕ) : ℝ) ≤ X) (hη : 0 < η)
    (hfirst : t ^ (2 * r + 1) * ((U * V : ℕ) : ℝ) ^ (2 * r) ≤
      X ^ ((2 * r : ℕ) + σ - 1 - η))
    (hlog : (V : ℝ) * t ^ 2 ≤ X ^ (σ - η)) :
    ‖((∑' n : ℕ, ((vonMangoldt n : ℝ) : ℂ) * gaussianHigherPrimeMomentWeight r σ t ε n) -
      gaussianHigherMomentPole r ((σ : ℂ) + t * I) ε t) -
      gaussianHigherCentredVaughanCurrent r σ t ε U V‖ ≤
      (8 ^ r + gaussianHigherMomentLatticeConstant r σ *
          (2 : ℝ) ^ (((2 * r : ℕ) + σ - 1) / 2) + gaussianHigherLogMomentConstant r σ) *
        (1 + 1 / η) / t := by
  have ht0 : 0 < t := zero_lt_one.trans_le ht
  have hX1 : 1 ≤ X :=
    (by exact_mod_cast Nat.mul_pos hU hV : (1 : ℝ) ≤ ((U * V : ℕ) : ℝ)).trans hUVX
  have hL : 1 + Real.log X ≤ (1 + 1 / η) * X ^ η := by
    have hp : 1 ≤ X ^ η := Real.one_le_rpow hX1 hη.le
    have hl := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hX η)
    rw [Real.log_rpow hX] at hl
    have hd : Real.log X ≤ X ^ η / η := (le_div_iff₀ hη).mpr (by linarith only [hl])
    exact (_root_.add_le_add hp hd).trans_eq (by ring)
  have hA : t ^ (2 * r) * ((U * V : ℕ) : ℝ) ^ (2 * r) *
      X ^ (1 - σ - (2 * r : ℕ)) ≤ X ^ (-η) / t := by
    apply (le_div_iff₀ ht0).mpr
    calc
      _ = (t ^ (2 * r + 1) * ((U * V : ℕ) : ℝ) ^ (2 * r)) *
          X ^ (1 - σ - (2 * r : ℕ)) := by rw [pow_succ]; ring
      _ ≤ X ^ ((2 * r : ℕ) + σ - 1 - η) * X ^ (1 - σ - (2 * r : ℕ)) :=
        mul_le_mul_of_nonneg_right hfirst (Real.rpow_nonneg hX.le _)
      _ = X ^ (-η) := by rw [← Real.rpow_add hX]; congr 1; ring
  have hB : (V : ℝ) * t * X ^ (-σ) ≤ X ^ (-η) / t := by
    apply (le_div_iff₀ ht0).mpr
    calc
      _ = ((V : ℝ) * t ^ 2) * X ^ (-σ) := by ring
      _ ≤ X ^ (σ - η) * X ^ (-σ) :=
        mul_le_mul_of_nonneg_right hlog (Real.rpow_nonneg hX.le _)
      _ = X ^ (-η) := by rw [← Real.rpow_add hX]; congr 1; ring
  let A : ℝ := 8 ^ r + gaussianHigherMomentLatticeConstant r σ *
    (2 : ℝ) ^ (((2 * r : ℕ) + σ - 1) / 2)
  let B : ℝ := gaussianHigherLogMomentConstant r σ
  have hC := gaussianHigherMomentLatticeConstant_nonneg r hσ1
  have hA0 : 0 ≤ A := by dsimp [A]; positivity
  have hB0 : 0 ≤ B := gaussianHigherLogMomentConstant_nonneg hr hσ1
  apply (norm_gaussianHigherMoment_sub_centredVaughan_product_le
    r hr hσ hσ1 ht hε hsector hX hscale hU hV hUVX).trans
  calc
    _ = (A * (t ^ (2 * r) * ((U * V : ℕ) : ℝ) ^ (2 * r) *
          X ^ (1 - σ - (2 * r : ℕ))) + B * ((V : ℝ) * t * X ^ (-σ))) *
          (1 + Real.log X) := by dsimp [A, B]; ring
    _ ≤ (A * (X ^ (-η) / t) + B * (X ^ (-η) / t)) *
          ((1 + 1 / η) * X ^ η) := by
      apply mul_le_mul
      · exact _root_.add_le_add (mul_le_mul_of_nonneg_left hA hA0)
          (mul_le_mul_of_nonneg_left hB hB0)
      · exact hL
      · exact add_nonneg zero_le_one (Real.log_nonneg hX1)
      · positivity
    _ = _ := by
      have hp : X ^ (-η) * X ^ η = 1 := by rw [← Real.rpow_add hX]; simp
      calc
        _ = (A + B) * (1 + 1 / η) / t * (X ^ (-η) * X ^ η) := by ring
        _ = _ := by rw [hp, mul_one]; rfl

#print axioms summable_gaussianHigherMoment_vonMangoldt
#print axioms tsum_gaussianHigherMoment_vaughan
#print axioms norm_sum_gaussianHigherMoment_head_physical_le
#print axioms norm_gaussianHigherMoment_sub_centredVaughan_product_le
#print axioms norm_gaussianHigherMoment_sub_centredVaughan_cutoff_le

end GaloisForLFunctions.ExceptionalLayerTheory
