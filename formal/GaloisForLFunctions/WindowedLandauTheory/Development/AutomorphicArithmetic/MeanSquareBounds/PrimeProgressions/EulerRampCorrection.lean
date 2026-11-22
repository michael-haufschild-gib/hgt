import GaloisForLFunctions.RHTower.DirichletLThreeFourOne
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.MeanSquareBounds.SmoothedIdentity

/-! The finite Euler-factor correction to a normalized character ramp. -/

open Complex Finset WindowedLandauTheory.HC
open ArithmeticFunction (vonMangoldt vonMangoldt_nonneg)
open GaloisForLFunctions.ShortIntervalPrimesInProgressions

noncomputable section

namespace QH.PrimeProgressions

private def deletedWeight (M n : ℕ) : ℝ :=
  if n.Coprime M then 0 else vonMangoldt n / Real.sqrt n

private theorem deletedWeight_nonneg (M n : ℕ) : 0 ≤ deletedWeight M n := by
  unfold deletedWeight
  split_ifs
  · exact le_rfl
  · exact div_nonneg vonMangoldt_nonneg (Real.sqrt_nonneg _)

private theorem half_prime_power_mass {p : ℕ} (hp : p.Prime) :
    Summable (RHTower.primePowerWeight (1 / 2) p) ∧
      ∑' n, RHTower.primePowerWeight (1 / 2) p n ≤ 3 * Real.log p := by
  let f := RHTower.primePowerWeight (1 / 2) p
  let r := (Real.sqrt (p : ℝ))⁻¹
  have hp₂ : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp₀ : (0 : ℝ) < p := by linarith only [hp₂]
  have hr₀ : 0 ≤ r := by dsimp only [r]; positivity
  have hp_low : (4 / 3 : ℝ) ≤ Real.sqrt p := by
    apply Real.le_sqrt_of_sq_le
    linarith only [hp₂]
  have hr : r ≤ 3 / 4 := by
    dsimp only [r]
    rw [← one_div, div_le_iff₀ (Real.sqrt_pos.mpr hp₀)]
    linarith only [hp_low]
  have hr₁ : r < 1 := hr.trans_lt (by norm_num)
  have h_inj : Function.Injective fun k : ℕ => p ^ (k + 1) := fun a b h =>
    by simpa using Nat.pow_right_injective hp.two_le h
  have h_supp : ∀ n ∉ Set.range (fun k : ℕ => p ^ (k + 1)), f n = 0 := fun n hn =>
    Set.indicator_of_notMem hn _
  have h_value (k : ℕ) : f (p ^ (k + 1)) = Real.log p * r * r ^ k := by
    dsimp only [f, RHTower.primePowerWeight]
    rw [Set.indicator_of_mem (Set.mem_range_self k), ← Real.sqrt_eq_rpow]
    push_cast
    have hpow (j : ℕ) : Real.sqrt ((p : ℝ) ^ j) = Real.sqrt (p : ℝ) ^ j := by
      induction j with
      | zero => simp
      | succ j hj => rw [pow_succ (p : ℝ) j, Real.sqrt_mul (pow_nonneg hp₀.le j), hj, pow_succ]
    change Real.log p / Real.sqrt ((p : ℝ) ^ (k + 1)) = _
    rw [hpow, div_eq_mul_inv, inv_pow, pow_succ]
    dsimp only [r]
    ring
  have h_geo := summable_geometric_of_lt_one hr₀ hr₁
  have h_fun : (f ∘ fun k : ℕ => p ^ (k + 1)) = fun k => Real.log p * r * r ^ k := funext h_value
  have hs : Summable f := by
    rw [← h_inj.summable_iff h_supp, h_fun]
    exact h_geo.mul_left _
  refine ⟨hs, ?_⟩
  change ∑' n, f n ≤ _
  rw [← h_inj.tsum_eq (fun n hn => by_contra fun h => hn (h_supp n h)), tsum_congr h_value,
    tsum_mul_left, tsum_geometric_of_lt_one hr₀ hr₁]
  have h_ratio : r * (1 - r)⁻¹ ≤ 3 := by
    rw [mul_inv_le_iff₀ (sub_pos.mpr hr₁)]
    linarith only [hr]
  rw [mul_assoc, mul_comm 3]
  exact mul_le_mul_of_nonneg_left h_ratio (Real.log_nonneg (by linarith only [hp₂]))

/-- The deleted prime powers have bounded absolute mass at the square-root weight. -/
private theorem deletedWeight_sum (M : ℕ) [NeZero M] :
    Summable (deletedWeight M) ∧
      ∑' n, deletedWeight M n ≤ 8 * (M : ℝ) ^ 2 := by
  have hp (p : ℕ) (hp : p ∈ M.primeFactors) : p.Prime := Nat.prime_of_mem_primeFactors hp
  let w := RHTower.primePowerWeight (1 / 2)
  have hdom (n : ℕ) : deletedWeight M n ≤ ∑ p ∈ M.primeFactors, w p n := by
    have hnonneg : 0 ≤ ∑ p ∈ M.primeFactors, w p n :=
      sum_nonneg fun p h => RHTower.primePowerWeight_nonneg (hp p h) n
    unfold deletedWeight
    split_ifs with hn
    · exact hnonneg
    by_cases hΛ : vonMangoldt n = 0
    · simpa only [hΛ, zero_div] using hnonneg
    obtain ⟨p, k, hp', hk, rfl⟩ := (isPrimePow_nat_iff _).mp
      (ArithmeticFunction.vonMangoldt_ne_zero_iff.mp hΛ)
    have hpM : p ∈ M.primeFactors := Nat.mem_primeFactors.mpr
      ⟨hp', by
        by_contra h
        exact hn (((Nat.Prime.coprime_iff_not_dvd hp').mpr h).pow_left k), NeZero.ne M⟩
    have he : vonMangoldt (p ^ k) / Real.sqrt ((p ^ k : ℕ) : ℝ) = w p (p ^ k) := by
      change _ = RHTower.primePowerWeight (1 / 2) p (p ^ k)
      unfold RHTower.primePowerWeight
      rw [Set.indicator_of_mem (Set.mem_range.mpr ⟨k - 1, by rw [Nat.sub_add_cancel hk]⟩),
        ArithmeticFunction.vonMangoldt_apply_pow hk.ne', ArithmeticFunction.vonMangoldt_apply_prime hp',
        Real.sqrt_eq_rpow]
    exact he.le.trans (single_le_sum (fun l hl => RHTower.primePowerWeight_nonneg (hp l hl) _) hpM)
  have hs : Summable (fun n => ∑ p ∈ M.primeFactors, w p n) :=
    summable_sum fun p hm => (half_prime_power_mass (hp p hm)).1
  have hd := Summable.of_nonneg_of_le (deletedWeight_nonneg M) hdom hs
  have hM : (1 : ℝ) ≤ M := by exact_mod_cast NeZero.pos M
  refine ⟨hd, (hd.tsum_le_tsum hdom hs).trans ?_⟩
  calc
    _ = ∑ p ∈ M.primeFactors, ∑' n, w p n :=
      Summable.tsum_finsetSum fun p hm => (half_prime_power_mass (hp p hm)).1
    _ ≤ ∑ p ∈ M.primeFactors, 3 * Real.log (p : ℝ) :=
      sum_le_sum fun p hm => (half_prime_power_mass (hp p hm)).2
    _ = 3 * Real.log (∏ p ∈ M.primeFactors, (p : ℝ)) := by
      rw [← mul_sum, Real.log_prod fun p hm => by exact_mod_cast (hp p hm).ne_zero]
    _ ≤ 3 * Real.log M := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      refine Real.log_le_log (Finset.prod_pos fun p hm => by exact_mod_cast (hp p hm).pos) ?_
      rw [← Nat.cast_prod]
      exact_mod_cast Nat.le_of_dvd (NeZero.pos M) (Nat.prod_primeFactors_dvd M)
    _ ≤ _ := by
      have hm := Real.log_le_sub_one_of_pos (show (0 : ℝ) < M by linarith only [hM])
      nlinarith only [hm, hM, mul_nonneg (show 0 ≤ (M : ℝ) - 1 by linarith only [hM])
        (Nat.cast_nonneg (α := ℝ) M)]

/-- Passing from the inducing character to the larger modulus changes the ramp by a constant
and an error bounded by a conductor-polynomial multiple of `1 / √y`. -/
theorem normalized_ramp_changeLevel {N M : ℕ} [NeZero M] (hNM : N ∣ M) (ψ : DirichletCharacter ℂ N) :
    ∃ K : ℂ, ∀ y : ℝ, 2 ≤ y →
      ‖An.sumLamChi (ψ.changeLevel hNM) y / (y : ℂ) - An.sumLamChi ψ y / (y : ℂ) - K‖ ≤
        8 * (M : ℝ) ^ 2 / Real.sqrt y := by
  let χ := ψ.changeLevel hNM
  let d (n : ℕ) := twistedVM χ n - twistedVM ψ n
  let z (n : ℕ) := d n / (n : ℂ)
  have hd (n : ℕ) : ‖d n‖ ≤ if n.Coprime M then 0 else vonMangoldt n := by
    split_ifs with hn
    · have he := ψ.changeLevel_eq_cast_of_dvd' hNM (a := (n : ℤ)) (Nat.isCoprime_iff_coprime.mpr hn)
      rw [Int.cast_natCast, Int.cast_natCast] at he
      simp only [d, χ, twistedVM, he, sub_self, norm_zero, le_refl]
    · have hzero : χ n = 0 := MulChar.map_nonunit χ (by rwa [ZMod.isUnit_iff_coprime])
      simp only [d, twistedVM, hzero, zero_mul, zero_sub, norm_neg, norm_mul, norm_real,
        Real.norm_of_nonneg vonMangoldt_nonneg]
      exact mul_le_of_le_one_left vonMangoldt_nonneg (DirichletCharacter.norm_le_one ψ _)
  have hd0 : d 0 = 0 := by simp [d, twistedVM]
  have hd' (n : ℕ) : ‖d n‖ ≤ Real.sqrt n * deletedWeight M n := by
    rcases n.eq_zero_or_pos with rfl | hn
    · simp [hd0]
    have hn₀ : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hn)
    unfold deletedWeight
    split_ifs with h
    · simpa only [mul_zero, if_pos h] using hd n
    · rw [mul_div_cancel₀ _ hn₀.ne']
      simpa only [if_neg h] using hd n
  obtain ⟨hb, hbnd⟩ := deletedWeight_sum M
  have hz (n : ℕ) : ‖z n‖ ≤ deletedWeight M n := by
    rcases n.eq_zero_or_pos with rfl | hn
    · simp only [z, hd0, zero_div, norm_zero, deletedWeight_nonneg]
    have hn₁ : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hr : 1 ≤ Real.sqrt (n : ℝ) := Real.one_le_sqrt.mpr hn₁
    have hrn : Real.sqrt (n : ℝ) ≤ n := by
      simpa only [Real.mul_self_sqrt (Nat.cast_nonneg (α := ℝ) n)] using
        le_mul_of_one_le_right (Real.sqrt_nonneg (n : ℝ)) hr
    dsimp only [z]
    rw [norm_div, Complex.norm_natCast, div_le_iff₀ (by linarith : 0 < (n : ℝ))]
    exact (hd' n).trans (by simpa only [mul_comm] using mul_le_mul_of_nonneg_right hrn (deletedWeight_nonneg M n))
  have hsz : Summable z := Summable.of_norm_bounded hb hz
  refine ⟨∑' n, z n, fun y hy => ?_⟩
  have hy₀ : 0 < y := by linarith
  have hs₀ : 0 < Real.sqrt y := Real.sqrt_pos.mpr hy₀
  have hsq := Real.sq_sqrt hy₀.le
  let F := Icc 1 ⌊y⌋₊
  let u (n : ℕ) := if n ∈ F then z n - d n / (y : ℂ) else 0
  have huf : ∀ n ∉ F, u n = 0 := fun n hn => if_neg hn
  have hsu : Summable u := summable_of_ne_finset_zero (s := F) huf
  have he : An.sumLamChi χ y / (y : ℂ) - An.sumLamChi ψ y / (y : ℂ) = ∑' n, u n := by
    rw [QH.sumLamChi_eq_ramp χ (by linarith), QH.sumLamChi_eq_ramp ψ (by linarith),
      tsum_eq_sum (s := F) huf, Finset.sum_div, Finset.sum_div, ← sum_sub_distrib]
    refine sum_congr rfl fun n hn => ?_
    dsimp only [u, z, d]
    rw [if_pos hn]
    have hyc : (y : ℂ) ≠ 0 := ofReal_ne_zero.mpr hy₀.ne'
    have hnc : (n : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (mem_Icc.mp hn).1)
    field_simp [hyc, hnc]
  change ‖An.sumLamChi χ y / (y : ℂ) - An.sumLamChi ψ y / (y : ℂ) - ∑' n, z n‖ ≤ _
  rw [he, ← hsu.tsum_sub hsz]
  have hterm (n : ℕ) : ‖u n - z n‖ ≤ deletedWeight M n / Real.sqrt y := by
    have hnw := deletedWeight_nonneg M n
    by_cases hn : n ∈ F
    · have hny : (n : ℝ) ≤ y :=
        (Nat.cast_le.mpr (mem_Icc.mp hn).2).trans (Nat.floor_le hy₀.le)
      simp only [u, if_pos hn, sub_sub_cancel_left, norm_neg, norm_div, norm_real,
        Real.norm_of_nonneg hy₀.le]
      calc ‖d n‖ / y ≤ (Real.sqrt y * deletedWeight M n) / y :=
            div_le_div_of_nonneg_right ((hd' n).trans
              (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hny) hnw)) hy₀.le
        _ = _ := by
          field_simp [hy₀.ne', hs₀.ne']
          nlinarith only [congrArg (fun v => v * deletedWeight M n) hsq]
    · rcases n.eq_zero_or_pos with rfl | hn₀
      · simp [u, hn, z, hd0, div_nonneg hnw hs₀.le]
      · have hny : y ≤ n := (Nat.lt_of_floor_lt (by
          by_contra! hfloor
          exact hn (mem_Icc.mpr ⟨hn₀, hfloor⟩))).le
        have hsn : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hn₀)
        simp only [u, if_neg hn, zero_sub, norm_neg, z, norm_div, Complex.norm_natCast]
        calc ‖d n‖ / (n : ℝ) ≤ (Real.sqrt (n : ℝ) * deletedWeight M n) / n :=
              div_le_div_of_nonneg_right (hd' n) (Nat.cast_nonneg n)
          _ = deletedWeight M n / Real.sqrt n := by
              have hnR : (0 : ℝ) < n := by exact_mod_cast hn₀
              field_simp [hnR.ne', hsn.ne']
              nlinarith only [congrArg (fun v => v * deletedWeight M n) (Real.sq_sqrt hnR.le)]
          _ ≤ _ := div_le_div_of_nonneg_left hnw hs₀ (Real.sqrt_le_sqrt hny)
  have hbs := hb.div_const (Real.sqrt y)
  have hnrm : Summable (fun n => ‖u n - z n‖) :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg (u n - z n)) hterm hbs
  refine (norm_tsum_le_tsum_norm hnrm).trans ((hnrm.tsum_le_tsum hterm hbs).trans ?_)
  rw [tsum_div_const]
  exact div_le_div_of_nonneg_right hbnd hs₀.le

end QH.PrimeProgressions
