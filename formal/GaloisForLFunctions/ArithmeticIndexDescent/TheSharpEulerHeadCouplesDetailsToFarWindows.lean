import GaloisForLFunctions.ArithmeticIndexDescent.TheGammaReservePaysEulerHeadsUpToTheSquareOfTheDepth
import GaloisForLFunctions.ArithmeticIndexDescent.TheCoarseDetailPrimePairIsTheLiteralSource
import GaloisForLFunctions.RHTower.FreeLagSymbolBoundaryLayer
import GaloisForLFunctions.RHTower.FreeLagTraceCertificateObstruction
import GaloisForLFunctions.RHTower.SelbergPrimePolynomialHighMoments
import GaloisForLFunctions.RHTower.CCM.CCMFirstClockPrimePowerTowerCollapse

/-!
# The sharp Euler head couples each detail to a far window

The head `p ≤ Y` of the complete mixed Euler source weights the lags `log m` by `2Λ(m)/√m` for every
`m ≤ Y` and drops to the proper prime powers beyond `Y`. Its edge at `m = Y` is visible at scale
`√Y`: a balanced detail on the pair `a` is coupled to the coarse window
`log Y + [log 2b, log(2b + 2))` with strength

`B_Y[a, b] / √Y → L[a, b] = ∫ h_a(u) s_b(u) du`, `s_b(u) = 4(√min(β, 1) − √min(α, 1))`,

`α = 2b e^{−u}`, `β = (2b + 2) e^{−u}` (`tendsto_headCoupling`). This is the prime number theorem in
the form `Σ_{m ≤ x} Λ(m)/√m ~ 2√x`, read on windows (`tendsto_headWindowMass`), after the head is
reindexed by its prime powers; the proper prime powers above `Y` cost `O(Y^{1/4})`
(`abs_eulerHead_tsum_sub_le`). The limit coupling is lower triangular with diagonal
`−4√(2a) J_a`, `J_a = ∫ h_a e^{−u/2} > 0` by strict convexity (`headCouplingLimit_eq_zero_of_lt`,
`headCouplingLimit_self_ne_zero`).
-/

noncomputable section

open MeasureTheory Finset Filter Topology
open RHTower

namespace GaloisForLFunctions.ArithmeticIndexDescent

open ArithmeticCastelnuovoSeveri.LogCells BiarithmeticGaugeGeometry HTGeometry

local notation "Λ" => ArithmeticFunction.vonMangoldt

/-! ### The prime number theorem on windows -/

/-- `A(x) = Σ_{n ≤ x} Λ(n)/√n`. -/
def sqrtChebyshev (x : ℝ) : ℝ := ∑ n ∈ Icc 0 ⌊x⌋₊, Λ n / Real.sqrt n

theorem sqrtChebyshev_mono : Monotone sqrtChebyshev := fun x y hxy =>
  sum_le_sum_of_subset_of_nonneg (Icc_subset_Icc_right (Nat.floor_mono hxy)) fun n _ _ =>
    div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _)

theorem tendsto_sqrtChebyshev :
    Tendsto (fun x => sqrtChebyshev x / Real.sqrt x) atTop (𝓝 2) :=
  RHTower.FreeLagTrace.tendsto_sum_vonMangoldt_div_sqrt

/-- `Σ_{1 ≤ m ≤ Y, m < γY} Λ(m)/√m`: the part of a window seen by the head `m ≤ Y`. -/
def headWindowMass (Y : ℕ) (γ : ℝ) : ℝ :=
  ∑ m ∈ (Icc 1 Y).filter (fun m => (m : ℝ) < γ * Y), Λ m / Real.sqrt m

theorem headWindowMass_nonneg (Y : ℕ) (γ : ℝ) : 0 ≤ headWindowMass Y γ :=
  sum_nonneg fun _ _ => div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _)

theorem headWindowMass_le (Y : ℕ) {γ : ℝ} (hγ : 0 < γ) :
    headWindowMass Y γ ≤ sqrtChebyshev (min γ 1 * Y) := by
  refine sum_le_sum_of_subset_of_nonneg (fun m hm => ?_) fun n _ _ =>
    div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _)
  obtain ⟨hmY, hmγ⟩ := mem_filter.mp hm
  have hmY' : (m : ℝ) ≤ Y := by exact_mod_cast (mem_Icc.mp hmY).2
  refine mem_Icc.mpr ⟨Nat.zero_le _, Nat.le_floor ?_⟩
  rcases le_total γ 1 with h | h
  · rw [min_eq_left h]; exact hmγ.le
  · rw [min_eq_right h, one_mul]; exact hmY'

theorem sqrtChebyshev_sub_one_le_headWindowMass (Y : ℕ) {γ : ℝ} (hγ : 0 < γ) :
    sqrtChebyshev (min γ 1 * Y - 1) ≤ headWindowMass Y γ := by
  have h0 : ∑ n ∈ Icc 0 ⌊min γ 1 * Y - 1⌋₊, Λ n / Real.sqrt n =
      ∑ n ∈ Icc 1 ⌊min γ 1 * Y - 1⌋₊, Λ n / Real.sqrt n := by
    refine (sum_subset (Icc_subset_Icc_left (Nat.zero_le 1)) fun n hn hn' => ?_).symm
    have : n = 0 := by
      by_contra h
      exact hn' (mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr h, (mem_Icc.mp hn).2⟩)
    subst this
    simp
  rw [sqrtChebyshev, h0]
  refine sum_le_sum_of_subset_of_nonneg (fun n hn => ?_) fun n _ _ =>
    div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _)
  obtain ⟨hn1, hn2⟩ := mem_Icc.mp hn
  have hpos : 0 < min γ 1 * Y - 1 := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn1
    have h2 : (n : ℝ) ≤ min γ 1 * Y - 1 :=
      (Nat.le_floor_iff' (by omega)).mp hn2
    linarith
  have hn' : (n : ℝ) ≤ min γ 1 * Y - 1 := Nat.floor_le hpos.le |>.trans' (by exact_mod_cast hn2)
  have hc1 : min γ 1 * (Y : ℝ) ≤ Y := by
    have := min_le_right γ 1
    nlinarith [(Nat.cast_nonneg Y : (0 : ℝ) ≤ Y)]
  have hcγ : min γ 1 * (Y : ℝ) ≤ γ * Y :=
    mul_le_mul_of_nonneg_right (min_le_left γ 1) (Nat.cast_nonneg Y)
  refine mem_filter.mpr ⟨mem_Icc.mpr ⟨hn1, ?_⟩, by linarith⟩
  exact_mod_cast (show (n : ℝ) ≤ Y by linarith)

/-- **The window law.** `(1/√Y) Σ_{1 ≤ m ≤ Y, m < γY} Λ(m)/√m → 2√min(γ, 1)`. -/
theorem tendsto_headWindowMass {γ : ℝ} (hγ : 0 < γ) :
    Tendsto (fun Y : ℕ => headWindowMass Y γ / Real.sqrt Y) atTop
      (𝓝 (2 * Real.sqrt (min γ 1))) := by
  set c := min γ 1 with hc
  have hc0 : 0 < c := lt_min hγ one_pos
  have hY : Tendsto (fun Y : ℕ => (Y : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  -- upper bound
  have hup : Tendsto (fun Y : ℕ => sqrtChebyshev (c * Y) / Real.sqrt Y) atTop
      (𝓝 (2 * Real.sqrt c)) := by
    have h1 := tendsto_sqrtChebyshev.comp (hY.const_mul_atTop hc0)
    refine (h1.mul_const (Real.sqrt c)).congr' ?_
    filter_upwards [eventually_gt_atTop 0] with Y hY0
    have hY0' : (0 : ℝ) < Y := by exact_mod_cast hY0
    simp only [Function.comp_apply]
    rw [Real.sqrt_mul hc0.le, div_mul_eq_mul_div, mul_div_mul_comm, div_self
      (Real.sqrt_pos.mpr hc0).ne', one_mul]
  -- lower bound
  have hlo : Tendsto (fun Y : ℕ => sqrtChebyshev (c * Y - 1) / Real.sqrt Y) atTop
      (𝓝 (2 * Real.sqrt c)) := by
    have hlin : Tendsto (fun Y : ℕ => c * (Y : ℝ) - 1) atTop atTop :=
      tendsto_atTop_add_const_right _ _ (hY.const_mul_atTop hc0)
    have h1 := tendsto_sqrtChebyshev.comp hlin
    have h2 : Tendsto (fun Y : ℕ => Real.sqrt ((c * Y - 1) / Y)) atTop (𝓝 (Real.sqrt c)) := by
      have : Tendsto (fun Y : ℕ => c - 1 / (Y : ℝ)) atTop (𝓝 (c - 0)) :=
        tendsto_const_nhds.sub (tendsto_const_nhds.div_atTop hY)
      rw [sub_zero] at this
      refine (Real.continuous_sqrt.tendsto c).comp (this.congr' ?_)
      filter_upwards [eventually_gt_atTop 0] with Y hY0
      have hY0' : (0 : ℝ) < Y := by exact_mod_cast hY0
      field_simp
    refine (h1.mul h2).congr' ?_
    filter_upwards [hlin.eventually_gt_atTop 0, eventually_gt_atTop 0] with Y hpos hY0
    have hY0' : (0 : ℝ) < Y := by exact_mod_cast hY0
    simp only [Function.comp_apply]
    rw [Real.sqrt_div hpos.le, div_mul_div_comm, mul_comm (Real.sqrt (c * Y - 1)),
      mul_div_mul_right _ _ (Real.sqrt_pos.mpr hpos).ne']
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlo hup (fun Y => ?_) fun Y => ?_
  · exact div_le_div_of_nonneg_right (sqrtChebyshev_sub_one_le_headWindowMass Y hγ)
      (Real.sqrt_nonneg _)
  · exact div_le_div_of_nonneg_right (headWindowMass_le Y hγ) (Real.sqrt_nonneg _)

/-- **Chebyshev on windows.** `Σ_{1 ≤ m ≤ Y, m < γY} Λ(m)/√m ≤ 2C √Y`. -/
theorem headWindowMass_le_sqrt (Y : ℕ) (hY : 1 ≤ Y) (γ : ℝ) :
    headWindowMass Y γ ≤ 2 * RHTower.FreeLagTrace.chebyshevConst * Real.sqrt Y := by
  have hY' : (1 : ℝ) ≤ Y := by exact_mod_cast hY
  refine le_trans ?_ (RHTower.FreeLagTrace.sum_vonMangoldt_div_sqrt_le hY')
  refine le_trans (sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun n _ _ =>
    div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _)) ?_
  rw [Nat.floor_natCast]
  have hsplit : Icc 1 Y = insert 1 (Icc 2 Y) := by
    ext n; simp only [mem_insert, mem_Icc]; omega
  rw [hsplit, sum_insert (by simp)]
  simp

/-! ### The proper prime powers -/

/-- `Σ_{n ≤ M, n not prime} Λ(n)/√n ≤ 144 M^{1/4}`. -/
theorem sum_nonprime_vonMangoldt_div_sqrt_le (M : ℕ) :
    ∑ n ∈ (Icc 1 M).filter (fun n => ¬ n.Prime), Λ n / Real.sqrt n ≤
      144 * (M : ℝ) ^ (1 / 4 : ℝ) := by
  have h := RHTower.sum_nonprime_vonMangoldt_rpow_le (δ := 1 / 4) (by norm_num) (by norm_num) M
  have hterm : ∀ n ∈ (Icc 1 M).filter (fun n => ¬ n.Prime), Λ n / Real.sqrt n ≤
      (M : ℝ) ^ (1 / 4 : ℝ) * (Λ n * (n : ℝ) ^ (-(1 / 2 + 1 / 4 : ℝ))) := by
    intro n hn
    have hn1 : 1 ≤ n := (mem_Icc.mp (mem_filter.mp hn).1).1
    have hnM : n ≤ M := (mem_Icc.mp (mem_filter.mp hn).1).2
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
    have hpow : (n : ℝ) ^ (1 / 4 : ℝ) ≤ (M : ℝ) ^ (1 / 4 : ℝ) :=
      Real.rpow_le_rpow hn0.le (by exact_mod_cast hnM) (by norm_num)
    have hsq : Real.sqrt n = (n : ℝ) ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow _
    have hid : (n : ℝ) ^ (1 / 4 : ℝ) * (n : ℝ) ^ (-(1 / 2 + 1 / 4 : ℝ)) = (Real.sqrt n)⁻¹ := by
      rw [← Real.rpow_add hn0, hsq, ← Real.rpow_neg hn0.le]
      norm_num
    calc Λ n / Real.sqrt n = Λ n * ((n : ℝ) ^ (1 / 4 : ℝ) * (n : ℝ) ^ (-(1 / 2 + 1 / 4 : ℝ))) := by
          rw [hid, div_eq_mul_inv]
      _ ≤ Λ n * ((M : ℝ) ^ (1 / 4 : ℝ) * (n : ℝ) ^ (-(1 / 2 + 1 / 4 : ℝ))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hpow (by positivity))
            ArithmeticFunction.vonMangoldt_nonneg
      _ = _ := by ring
  calc _ ≤ ∑ n ∈ (Icc 1 M).filter (fun n => ¬ n.Prime),
        (M : ℝ) ^ (1 / 4 : ℝ) * (Λ n * (n : ℝ) ^ (-(1 / 2 + 1 / 4 : ℝ))) := sum_le_sum hterm
    _ = (M : ℝ) ^ (1 / 4 : ℝ) * ∑ n ∈ (Icc 1 M).filter (fun n => ¬ n.Prime),
        Λ n * (n : ℝ) ^ (-(1 / 2 + 1 / 4 : ℝ)) := by rw [mul_sum]
    _ ≤ (M : ℝ) ^ (1 / 4 : ℝ) * (36 / (1 / 4)) :=
        mul_le_mul_of_nonneg_left h (by positivity)
    _ = _ := by ring

/-! ### Reindexing the head by its prime powers -/

theorem tsum_primePow_eq_sum {F : ℕ → ℝ} {M : ℕ} (hF0 : ∀ m, M < m → F m = 0) (p : ℕ)
    (hp : p.Prime) :
    ∑' k : ℕ, F (p ^ (k + 1)) = ∑ e ∈ Icc 1 (p.log M), F (p ^ e) := by
  rw [tsum_eq_sum (s := range (p.log M)) fun k hk => hF0 _ ?_]
  · rw [range_eq_Ico, ← Nat.Ico_succ_right, sum_Ico_add' (fun e => F (p ^ e)) 0 (p.log M) 1]
  · have hk' : p.log M + 1 ≤ k + 1 := by simpa using hk
    exact (Nat.lt_pow_succ_log_self hp.one_lt M).trans_le
      (Nat.pow_le_pow_right hp.pos hk')

/-- **The head is the prime powers up to `Y` plus proper powers beyond.** If `F` vanishes beyond
`M < (Y + 1)²` and is dominated by `B · 2Λ(m)/√m`, the head sum differs from `Σ_{m ≤ Y} F m` by at
most `288 B M^{1/4}`. -/
theorem abs_eulerHead_tsum_sub_le {Y M : ℕ} (hYM : Y ≤ M) (hMY : M < (Y + 1) ^ 2)
    {F : ℕ → ℝ} {B : ℝ} (hB : 0 ≤ B) (hF0 : ∀ m, M < m → F m = 0)
    (hFB : ∀ m, |F m| ≤ B * (2 * Λ m / Real.sqrt m)) :
    |∑ p ∈ eulerHead Y, ∑' k : ℕ, F ((p : ℕ) ^ (k + 1)) - ∑ m ∈ Icc 1 Y, F m| ≤
      288 * B * (M : ℝ) ^ (1 / 4 : ℝ) := by
  classical
  have hΛ : ∀ m, Λ m = 0 → F m = 0 := fun m hm => by
    have := hFB m
    rw [hm, mul_zero, zero_div, mul_zero] at this
    exact abs_nonpos_iff.mp this
  set G : ℕ → ℝ := fun p => ∑ e ∈ Icc 1 (p.log M), F (p ^ e)
  -- the head as a sum over `primesLE Y`
  have hhead : ∑ p ∈ eulerHead Y, ∑' k : ℕ, F ((p : ℕ) ^ (k + 1)) = ∑ p ∈ Nat.primesLE Y, G p := by
    rw [eulerHead, sum_subtype_eq_sum_filter (f := fun p : ℕ => ∑' k : ℕ, F (p ^ (k + 1)))]
    refine sum_congr rfl fun p hp => tsum_primePow_eq_sum hF0 p (mem_filter.mp hp).2
  -- all prime powers up to `M`
  have hall : ∑ m ∈ Icc 1 M, F m = ∑ p ∈ Nat.primesLE M, G p := by
    rw [← RHTower.sum_primePow_Icc_eq_sum_primesLE, sum_filter]
    refine sum_congr rfl fun m _ => ?_
    split_ifs with h
    · rfl
    · exact (hΛ m (ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr h)).symm
  -- primes beyond `Y` carry only their first power
  have hbig : ∀ p ∈ (Nat.primesLE M).filter (fun p => Y < p), G p = F p := by
    intro p hp
    obtain ⟨hpM, hpY⟩ := mem_filter.mp hp
    obtain ⟨hpM, hpr⟩ := Nat.mem_primesLE.mp hpM
    have hlog : p.log M = 1 := by
      rw [Nat.log_eq_iff (by norm_num)]
      refine ⟨by simpa using hpM, ?_⟩
      calc M < (Y + 1) ^ 2 := hMY
        _ ≤ p ^ 2 := Nat.pow_le_pow_left hpY 2
        _ = p ^ (1 + 1) := rfl
    simp [G, hlog]
  have hsplitP : ∑ p ∈ Nat.primesLE M, G p =
      ∑ p ∈ Nat.primesLE Y, G p + ∑ p ∈ (Nat.primesLE M).filter (fun p => Y < p), F p := by
    rw [← sum_filter_add_sum_filter_not (Nat.primesLE M) (fun p => p ≤ Y)]
    congr 1
    · refine sum_congr ?_ fun _ _ => rfl
      ext p
      simp only [mem_filter, Nat.mem_primesLE]
      constructor
      · rintro ⟨⟨_, hp⟩, hpY⟩; exact ⟨hpY, hp⟩
      · rintro ⟨hpY, hp⟩; exact ⟨⟨hpY.trans hYM, hp⟩, hpY⟩
    · rw [← sum_congr rfl hbig]
      refine sum_congr ?_ fun _ _ => rfl
      ext p
      simp only [mem_filter, not_le]
  -- the integers between `Y` and `M`
  have hsplitM : ∑ m ∈ Icc 1 M, F m = ∑ m ∈ Icc 1 Y, F m +
      (∑ p ∈ (Nat.primesLE M).filter (fun p => Y < p), F p +
        ∑ m ∈ (Ioc Y M).filter (fun m => ¬ m.Prime), F m) := by
    have hIcc : Icc 1 M = Icc 1 Y ∪ Ioc Y M := by
      ext m; simp only [mem_union, mem_Icc, mem_Ioc]; omega
    rw [hIcc, sum_union (by
      rw [disjoint_left]; intro m h1 h2; simp only [mem_Icc, mem_Ioc] at h1 h2; omega)]
    congr 1
    rw [← sum_filter_add_sum_filter_not (Ioc Y M) Nat.Prime]
    congr 1
    refine sum_congr ?_ fun _ _ => rfl
    ext m
    simp only [mem_filter, mem_Ioc, Nat.mem_primesLE]
    tauto
  have hdiff : ∑ p ∈ eulerHead Y, ∑' k : ℕ, F ((p : ℕ) ^ (k + 1)) - ∑ m ∈ Icc 1 Y, F m =
      ∑ m ∈ (Ioc Y M).filter (fun m => ¬ m.Prime), F m := by
    rw [hhead]
    linarith [hall, hsplitP, hsplitM]
  rw [hdiff]
  calc |∑ m ∈ (Ioc Y M).filter (fun m => ¬ m.Prime), F m|
      ≤ ∑ m ∈ (Ioc Y M).filter (fun m => ¬ m.Prime), |F m| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ m ∈ (Icc 1 M).filter (fun m => ¬ m.Prime), B * (2 * Λ m / Real.sqrt m) := by
        refine (sum_le_sum fun m _ => hFB m).trans (sum_le_sum_of_subset_of_nonneg ?_ fun m _ _ =>
          mul_nonneg hB (div_nonneg (mul_nonneg (by norm_num)
            ArithmeticFunction.vonMangoldt_nonneg) (Real.sqrt_nonneg _)))
        intro m hm
        simp only [mem_filter, mem_Ioc, mem_Icc] at hm ⊢
        exact ⟨⟨by omega, hm.1.2⟩, hm.2⟩
    _ = 2 * B * ∑ m ∈ (Icc 1 M).filter (fun m => ¬ m.Prime), Λ m / Real.sqrt m := by
        rw [mul_sum]; refine sum_congr rfl fun m _ => ?_; ring
    _ ≤ 2 * B * (144 * (M : ℝ) ^ (1 / 4 : ℝ)) :=
        mul_le_mul_of_nonneg_left (sum_nonprime_vonMangoldt_div_sqrt_le M) (by positivity)
    _ = _ := by ring

end GaloisForLFunctions.ArithmeticIndexDescent
