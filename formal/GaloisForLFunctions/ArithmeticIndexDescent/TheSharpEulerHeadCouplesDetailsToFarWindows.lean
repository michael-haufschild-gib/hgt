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

theorem sqrtChebyshev_mono : Monotone sqrtChebyshev := fun _ _ hxy =>
  sum_le_sum_of_subset_of_nonneg (Icc_subset_Icc_right (Nat.floor_mono hxy)) fun _ _ _ =>
    div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _)

theorem tendsto_sqrtChebyshev :
    Tendsto (fun x => sqrtChebyshev x / Real.sqrt x) atTop (𝓝 2) :=
  RHTower.FreeLagTrace.tendsto_sum_vonMangoldt_div_sqrt

/-- `Σ_{1 ≤ m ≤ Y, m < γY} Λ(m)/√m`: the part of a window seen by the head `m ≤ Y`. -/
def headWindowMass (Y : ℕ) (γ : ℝ) : ℝ :=
  ∑ m ∈ (Icc 1 Y).filter (fun m : ℕ => (m : ℝ) < γ * (Y : ℝ)), Λ m / Real.sqrt (m : ℝ)

theorem headWindowMass_nonneg (Y : ℕ) (γ : ℝ) : 0 ≤ headWindowMass Y γ :=
  sum_nonneg fun _ _ => div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _)

theorem headWindowMass_le (Y : ℕ) (γ : ℝ) :
    headWindowMass Y γ ≤ sqrtChebyshev (min γ 1 * Y) := by
  refine sum_le_sum_of_subset_of_nonneg (fun m hm => ?_) fun _ _ _ =>
    div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _)
  obtain ⟨hmY, hmγ⟩ := mem_filter.mp hm
  have hmY' : (m : ℝ) ≤ Y := by exact_mod_cast (mem_Icc.mp hmY).2
  refine mem_Icc.mpr ⟨Nat.zero_le _, Nat.le_floor ?_⟩
  rcases le_total γ 1 with h | h
  · rw [min_eq_left h]; exact hmγ.le
  · rw [min_eq_right h, one_mul]; exact hmY'

theorem sqrtChebyshev_sub_one_le_headWindowMass (Y : ℕ) (γ : ℝ) :
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
  refine sum_le_sum_of_subset_of_nonneg (fun n hn => ?_) fun _ _ _ =>
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
    have hsc := Real.sqrt_pos.mpr hc0
    have hsY := Real.sqrt_pos.mpr hY0'
    simp only [Function.comp_apply]
    rw [Real.sqrt_mul hc0.le]
    field_simp
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
    have hsp := Real.sqrt_pos.mpr hpos
    have hsY := Real.sqrt_pos.mpr hY0'
    simp only [Function.comp_apply]
    rw [Real.sqrt_div hpos.le]
    field_simp
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlo hup (fun Y => ?_) fun Y => ?_
  · exact div_le_div_of_nonneg_right (sqrtChebyshev_sub_one_le_headWindowMass Y γ)
      (Real.sqrt_nonneg _)
  · exact div_le_div_of_nonneg_right (headWindowMass_le Y γ) (Real.sqrt_nonneg _)

/-- **Chebyshev on windows.** `Σ_{1 ≤ m ≤ Y, m < γY} Λ(m)/√m ≤ 2C √Y`. -/
theorem headWindowMass_le_sqrt (Y : ℕ) (hY : 1 ≤ Y) (γ : ℝ) :
    headWindowMass Y γ ≤ 2 * RHTower.FreeLagTrace.chebyshevConst * Real.sqrt Y := by
  have hY' : (1 : ℝ) ≤ Y := by exact_mod_cast hY
  refine le_trans ?_ (RHTower.FreeLagTrace.sum_vonMangoldt_div_sqrt_le hY')
  refine le_trans (sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun _ _ _ =>
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
  · rw [range_eq_Ico, sum_Ico_add' (fun e => F (p ^ e)) 0 (p.log M) 1]
    refine sum_congr ?_ fun _ _ => rfl
    ext e; simp only [mem_Ico, mem_Icc]; omega
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
    have hbij : ∑ p ∈ eulerHead Y, ∑' k : ℕ, F ((p : ℕ) ^ (k + 1)) =
        ∑ n ∈ Nat.primesLE Y, ∑' k : ℕ, F (n ^ (k + 1)) :=
      Finset.sum_bij (fun (p : Nat.Primes) _ => (p : ℕ))
        (fun p hp => Nat.mem_primesLE.mpr ⟨mem_eulerHead.mp hp, p.property⟩)
        (fun p _ q _ h => Subtype.ext h)
        (fun n hn => ⟨⟨n, (Nat.mem_primesLE.mp hn).2⟩,
          mem_eulerHead.mpr (Nat.mem_primesLE.mp hn).1, rfl⟩) (fun _ _ => rfl)
    rw [hbij]
    exact sum_congr rfl fun p hp => tsum_primePow_eq_sum hF0 p (Nat.mem_primesLE.mp hp).2
  -- all prime powers up to `M`
  have hall : ∑ m ∈ Icc 1 M, F m = ∑ p ∈ Nat.primesLE M, G p := by
    rw [← RHTower.sum_primePow_Icc_eq_sum_primesLE, sum_filter]
    refine sum_congr rfl fun m _ => ?_
    split_ifs with h
    · rfl
    · exact hΛ m (ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr h)
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

/-! ### A single detail and a far window -/

/-- The unit detail on the pair `a`. -/
def detailUnit (a : ℕ) : ℕ → ℝ := fun n => if n = a then 1 else 0

/-- The coarse window of the pairs `Yb ≤ n < Y(b + 1)`, i.e. of `[log 2Yb, log 2Y(b + 1))`. -/
def coarseWindow (Y b : ℕ) : ℕ → ℝ := fun n => if Y * b ≤ n ∧ n < Y * (b + 1) then 1 else 0

theorem haarSectionProfile_detailUnit {a X : ℕ} (ha : 1 ≤ a) (haX : a ≤ X) (x : ℝ) :
    haarSectionProfile (detailUnit a) X x = haarProfile a x := by
  rw [haarSectionProfile, sum_eq_single a (fun n _ hn => by simp [detailUnit, hn])
    (fun h => absurd (mem_Icc.mpr ⟨ha, haX⟩) h)]
  simp [detailUnit]

/-- Consecutive cells tile an interval: `Σ_{A ≤ k < B} 1_{[log k, log(k+1))} = 1_{[log A, log B)}`. -/
theorem sum_Ico_rawCell {A B : ℕ} (hA : 1 ≤ A) (hAB : A ≤ B) (x : ℝ) :
    ∑ k ∈ Ico A B, rawCell k x =
      (Set.Ico (Real.log A) (Real.log B)).indicator (fun _ => (1 : ℝ)) x := by
  induction B, hAB using Nat.le_induction with
  | base => simp
  | succ B hAB ih =>
    have hA0 : (0 : ℝ) < A := by exact_mod_cast hA
    have hB0 : (0 : ℝ) < B := by exact_mod_cast hA.trans hAB
    have h1 : Real.log A ≤ Real.log B := Real.log_le_log hA0 (by exact_mod_cast hAB)
    have h2 : Real.log (B : ℝ) ≤ Real.log ((B + 1 : ℕ) : ℝ) :=
      Real.log_le_log hB0 (by push_cast; linarith)
    have hu := congrFun (Set.indicator_union_of_disjoint (Set.Ico_disjoint_Ico_same
      (a := Real.log A) (b := Real.log B) (c := Real.log ((B + 1 : ℕ) : ℝ))) (fun _ => (1 : ℝ))) x
    rw [Set.Ico_union_Ico_eq_Ico h1 h2] at hu
    rw [sum_Ico_succ_top hAB, ih, rawCell, hu]

theorem coarseProfile_eq_indicator {b : ℕ} (hb : 1 ≤ b) (x : ℝ) :
    coarseProfile b x =
      (Set.Ico (Real.log ((2 * b : ℕ) : ℝ)) (Real.log ((2 * b + 2 : ℕ) : ℝ))).indicator
        (fun _ => (1 : ℝ)) x := by
  rw [← sum_Ico_rawCell (by omega) (by omega), coarseProfile,
    show Ico (2 * b) (2 * b + 2) = {2 * b, 2 * b + 1} by ext n; simp; omega,
    sum_pair (by omega)]

private theorem sum_Ico_pairs (f : ℕ → ℝ) {A B : ℕ} (hAB : A ≤ B) :
    ∑ n ∈ Ico A B, (f (2 * n) + f (2 * n + 1)) = ∑ k ∈ Ico (2 * A) (2 * B), f k := by
  induction B, hAB using Nat.le_induction with
  | base => simp
  | succ B hAB ih =>
    rw [sum_Ico_succ_top hAB, ih, show 2 * (B + 1) = 2 * B + 1 + 1 by ring,
      sum_Ico_succ_top (by omega), sum_Ico_succ_top (by omega), add_assoc]

/-- **The window is a translated coarse pair.** -/
theorem averageSectionProfile_coarseWindow {Y b X : ℕ} (hY : 1 ≤ Y) (hb : 1 ≤ b)
    (hX : Y * (b + 1) ≤ X + 1) (x : ℝ) :
    averageSectionProfile (coarseWindow Y b) X x = coarseProfile b (x - Real.log Y) := by
  have hYb : 1 ≤ Y * b := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hsum : averageSectionProfile (coarseWindow Y b) X x =
      ∑ n ∈ Ico (Y * b) (Y * (b + 1)), coarseProfile n x := by
    rw [averageSectionProfile]
    simp only [coarseWindow, ite_mul, one_mul, zero_mul]
    rw [← sum_filter]
    refine sum_congr ?_ fun _ _ => rfl
    ext n
    simp only [mem_filter, mem_Icc, mem_Ico]
    constructor
    · rintro ⟨_, h⟩; exact h
    · rintro ⟨h1, h2⟩; exact ⟨⟨hYb.trans h1, by omega⟩, h1, h2⟩
  rw [hsum, sum_congr rfl fun n _ =>
    (show coarseProfile n x = rawCell (2 * n) x + rawCell (2 * n + 1) x from rfl), sum_Ico_pairs (fun k => rawCell k x) (Nat.mul_le_mul_left Y (Nat.le_succ b)),
    sum_Ico_rawCell (by omega) (by nlinarith), coarseProfile_eq_indicator hb]
  have hY0 : (0 : ℝ) < Y := by exact_mod_cast hY
  have hb0 : (0 : ℝ) < b := by exact_mod_cast hb
  simp only [Set.indicator_apply, Set.mem_Ico]
  push_cast
  rw [show (2 : ℝ) * (Y * b) = Y * (2 * b) by ring, show (2 : ℝ) * (Y * (b + 1)) = Y * (2 * b + 2) by
    ring, Real.log_mul hY0.ne' (by positivity), Real.log_mul hY0.ne' (by positivity)]
  congr 1
  apply propext
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

/-- The coupling kernel of the detail `a` and the window `b` at relative lag `t`. -/
def headCouplingKernel (a b : ℕ) (t : ℝ) : ℝ := ∫ u, haarProfile a u * coarseProfile b (u + t)

theorem measurable_coarseProfile (b : ℕ) : Measurable (coarseProfile b) :=
  (measurable_rawCell _).add (measurable_rawCell _)

theorem abs_coarseProfile_le {b : ℕ} (hb : 1 ≤ b) (x : ℝ) : |coarseProfile b x| ≤ 1 := by
  rw [coarseProfile_eq_indicator hb]
  simp only [Set.indicator_apply]
  split_ifs <;> norm_num

theorem integrable_haarProfile_mul_coarseProfile (a : ℕ) {b : ℕ} (hb : 1 ≤ b) (t : ℝ) :
    Integrable (fun u => haarProfile a u * coarseProfile b (u + t)) :=
  (integrable_haarProfile a).mul_bdd ((measurable_coarseProfile b).comp
    (measurable_add_const t)).aestronglyMeasurable
    (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact abs_coarseProfile_le hb _)

theorem rawCell_nonneg (k : ℕ) (x : ℝ) : 0 ≤ rawCell k x :=
  Set.indicator_nonneg (fun _ _ => zero_le_one) x

theorem abs_haarProfile_le {a : ℕ} (ha : 1 ≤ a) (x : ℝ) :
    |haarProfile a x| ≤ rawCell (2 * a) x + rawCell (2 * a + 1) x := by
  have hl := logCellWidth_pos (show 1 ≤ 2 * a by omega)
  have hr := logCellWidth_pos (show 1 ≤ 2 * a + 1 by omega)
  have hL0 : 0 ≤ haarLeftCoeff a := div_nonneg hr.le (add_pos hl hr).le
  have hR0 : 0 ≤ haarRightCoeff a := div_nonneg hl.le (add_pos hl hr).le
  have hs := haarCoeff_sum ha
  have r0 := rawCell_nonneg (2 * a) x
  have r1 := rawCell_nonneg (2 * a + 1) x
  rw [haarProfile]
  exact abs_le.mpr ⟨by nlinarith, by nlinarith⟩

/-- `|k_{ab}(t)| ≤ 2`. -/
theorem abs_headCouplingKernel_le {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) (t : ℝ) :
    |headCouplingKernel a b t| ≤ 2 := by
  have hint : Integrable (fun u => rawCell (2 * a) u + rawCell (2 * a + 1) u) :=
    (integrable_rawCell _).add (integrable_rawCell _)
  calc |headCouplingKernel a b t| ≤ ∫ u, |haarProfile a u * coarseProfile b (u + t)| :=
        abs_integral_le_integral_abs
    _ ≤ ∫ u, (rawCell (2 * a) u + rawCell (2 * a + 1) u) := by
        refine integral_mono (integrable_haarProfile_mul_coarseProfile a hb t).abs hint fun u => ?_
        rw [abs_mul]
        exact (mul_le_of_le_one_right (abs_nonneg _) (abs_coarseProfile_le hb _)).trans
          (abs_haarProfile_le ha u)
    _ = logCellWidth (2 * a) + logCellWidth (2 * a + 1) := by
        rw [integral_add (integrable_rawCell _) (integrable_rawCell _),
          integral_rawCell (by omega), integral_rawCell (by omega)]
    _ ≤ 1 + 1 := by
        have h1 := logCellWidth_le_inv (show 1 ≤ 2 * a by omega)
        have h2 := logCellWidth_le_inv (show 1 ≤ 2 * a + 1 by omega)
        have h3 : 1 / ((2 * a : ℕ) : ℝ) ≤ 1 := by
          rw [div_le_one (by positivity)]; exact_mod_cast (show 1 ≤ 2 * a by omega)
        have h4 : 1 / ((2 * a + 1 : ℕ) : ℝ) ≤ 1 := by
          rw [div_le_one (by positivity)]; exact_mod_cast (show 1 ≤ 2 * a + 1 by omega)
        linarith
    _ = 2 := by norm_num

theorem haarProfile_eq_zero_of_lt {a : ℕ} {u : ℝ} (hu : u < Real.log ((2 * a : ℕ) : ℝ)) :
    haarProfile a u = 0 := by
  have h0 : rawCell (2 * a) u = 0 := by
    rw [rawCell, Set.indicator_of_notMem]; exact fun h => absurd h.1 (not_le.mpr hu)
  have h1 : rawCell (2 * a + 1) u = 0 := by
    rcases Nat.eq_zero_or_pos a with rfl | ha
    · rw [rawCell, Set.indicator_of_notMem]
      intro h
      have := h.1
      simp only [mul_zero, Nat.cast_zero, Real.log_zero] at hu
      simp at this
      linarith
    · rw [rawCell, Set.indicator_of_notMem]
      intro h
      have hle : Real.log ((2 * a : ℕ) : ℝ) ≤ Real.log ((2 * a + 1 : ℕ) : ℝ) :=
        Real.log_le_log (by positivity) (by push_cast; linarith)
      exact absurd (hle.trans h.1) (not_le.mpr hu)
  rw [haarProfile, h0, h1]; ring

/-- The kernel vanishes once the window lies beyond the translated pair. -/
theorem headCouplingKernel_eq_zero {a b : ℕ} (hb : 1 ≤ b) {t : ℝ}
    (ht : Real.log ((2 * b + 2 : ℕ) : ℝ) - Real.log ((2 * a : ℕ) : ℝ) ≤ t) :
    headCouplingKernel a b t = 0 := by
  unfold headCouplingKernel
  refine integral_eq_zero_of_ae (Eventually.of_forall fun u => ?_)
  by_cases hu : u < Real.log ((2 * a : ℕ) : ℝ)
  · simp [haarProfile_eq_zero_of_lt hu]
  · show haarProfile a u * coarseProfile b (u + t) = 0
    rw [coarseProfile_eq_indicator hb, Set.indicator_of_notMem, mul_zero]
    intro h; linarith [h.2]

/-- **The source of a single detail against a far window.** -/
theorem integerMixedSource_detailUnit_coarseWindow {a b Y X : ℕ} (ha : 1 ≤ a) (haX : a ≤ X)
    (hY : 1 ≤ Y) (hb : 1 ≤ b) (hX : Y * (b + 1) ≤ X + 1) (m : ℕ) :
    integerMixedSource m (detailUnit a) (coarseWindow Y b) X X =
      2 * Λ m / Real.sqrt m * headCouplingKernel a b (Real.log m - Real.log Y) := by
  by_cases hm : 2 ≤ m
  · rw [integerMixedSource, inner_shift_coarseSection_haarSection _ _ _ _ hm, add_zero,
      inner_shift_haar_coarse_profiles]
    congr 1
    unfold headCouplingKernel
    congr 1
    funext u
    rw [haarSectionProfile_detailUnit ha haX, averageSectionProfile_coarseWindow hY hb hX]
    congr 2
    ring
  · have hΛ : Λ m = 0 := by interval_cases m <;> simp
    simp [integerMixedSource, hΛ]

/-- The weighted term of the head at `m`. -/
def headTerm (Y a b m : ℕ) : ℝ :=
  2 * Λ m / Real.sqrt m * headCouplingKernel a b (Real.log m - Real.log Y)

/-- **The head coupling** `B_Y[a, b]`: the complete mixed Euler source of the head `p ≤ Y` on the
detail `a` and the window `b`. -/
def headCoupling (Y a b : ℕ) : ℝ :=
  ∑ p ∈ eulerHead Y, ∑' k : ℕ, headTerm Y a b ((p : ℕ) ^ (k + 1))

theorem finiteEulerMixedSource_detailUnit_coarseWindow {a b Y X : ℕ} (ha : 1 ≤ a) (haX : a ≤ X)
    (hY : 1 ≤ Y) (hb : 1 ≤ b) (hX : Y * (b + 1) ≤ X + 1) :
    finiteEulerMixedSource (eulerHead Y) (detailUnit a) (coarseWindow Y b) X = headCoupling Y a b := by
  unfold finiteEulerMixedSource primeEulerMixedSource headCoupling
  refine sum_congr rfl fun p _ => tsum_congr fun k => ?_
  rw [integerMixedSource_detailUnit_coarseWindow ha haX hY hb hX]
  rfl

/-- **The head is the integers up to `Y`**, up to `O(Y^{1/4})`. -/
theorem abs_headCoupling_sub_le {Y a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) (hbY : b ≤ Y) :
    |headCoupling Y a b - ∑ m ∈ Icc 1 Y, headTerm Y a b m| ≤
      576 * ((Y * (b + 1) : ℕ) : ℝ) ^ (1 / 4 : ℝ) := by
  have h := abs_eulerHead_tsum_sub_le (Y := Y) (M := Y * (b + 1)) (F := headTerm Y a b) (B := 2)
    (Nat.le_mul_of_pos_right Y (by omega)) (by nlinarith) (by norm_num) (fun m hm => ?_)
    (fun m => ?_)
  · rw [headCoupling]; linarith
  · have hY1 : 1 ≤ Y := hb.trans hbY
    have hY0 : (0 : ℝ) < Y := by exact_mod_cast hY1
    have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
    rw [headTerm, headCouplingKernel_eq_zero hb, mul_zero]
    have hmY : ((Y * (b + 1) : ℕ) : ℝ) ≤ m := by exact_mod_cast hm.le
    have hlog : Real.log Y + Real.log ((b : ℝ) + 1) ≤ Real.log m := by
      rw [← Real.log_mul hY0.ne' (by positivity)]
      exact Real.log_le_log (by positivity) (by push_cast at hmY; linarith)
    have ha0 : 0 ≤ Real.log (a : ℝ) := Real.log_nonneg (by exact_mod_cast ha)
    have h2b : Real.log ((2 * b + 2 : ℕ) : ℝ) = Real.log 2 + Real.log ((b : ℝ) + 1) := by
      rw [← Real.log_mul (by norm_num) (by positivity)]; push_cast; ring_nf
    have h2a : Real.log ((2 * a : ℕ) : ℝ) = Real.log 2 + Real.log (a : ℝ) := by
      rw [← Real.log_mul (by norm_num) (by positivity)]; push_cast; ring_nf
    rw [h2b, h2a]
    linarith
  · rw [headTerm, abs_mul]
    have hw : 0 ≤ 2 * Λ m / Real.sqrt m :=
      div_nonneg (mul_nonneg (by norm_num) ArithmeticFunction.vonMangoldt_nonneg) (Real.sqrt_nonneg _)
    rw [abs_of_nonneg hw, mul_comm 2 (2 * Λ m / Real.sqrt m)]
    exact mul_le_mul_of_nonneg_left (abs_headCouplingKernel_le ha hb _) hw

end GaloisForLFunctions.ArithmeticIndexDescent
