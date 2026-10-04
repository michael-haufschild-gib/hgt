import GaloisForLFunctions.RHTower.ThetaChronologicalPositiveTransfer

/-!
# The causal Möbius–theta frame retains the arithmetic jump record

In logarithmic time `b(x) = B(e^x)`, the causal tail is right-continuous, continuous off the sites
`log m`, and jumps at `log m` by exactly `−k(0) μ(m)/√m`.  Hence `μ(m)` is read off from the jump.
For `0 < t < 1` the tail is the Gaussian seed `h(−log t)`.  The decomposition `b = J + c` into the
pure jump function `J(x) = −k(0) Σ_{1 ≤ m ≤ e^x} μ(m)/√m` and a locally Lipschitz regular part `c`
identifies the singular part of `db/dx` as `−k(0) Σ μ(m)/√m δ_{log m}`.  Every regular observation
`∫ P(∂)C(y+a) dν(a)` of the cutoff current is continuous, so none of them — and in particular no
positive finite-measure transfer `T` with finite-order derivatives — reproduces `b`.
-/

open MeasureTheory Set Filter Topology

namespace RHTower

noncomputable section

/-! ## Logarithmic time -/

/-- `b(x) = B(e^x)`. -/
def causalLogTail (x : ℝ) : ℝ := causalMobiusThetaTail (Real.exp x)

theorem causalLogTail_eq (x : ℝ) : causalLogTail x = ∑' n : ℕ, causalLogTerm x n := by
  rw [causalLogTail, causalMobiusThetaTail]
  exact tsum_congr fun n => causalMobiusThetaTerm_exp x n

theorem causalLogTail_fun : causalLogTail = fun x => ∑' n : ℕ, causalLogTerm x n :=
  funext causalLogTail_eq

/-- The weights `μ(n) n^{−1/2}`. -/
def moebiusInvSqrtWeight (n : ℕ) : ℝ := (ArithmeticFunction.moebius n : ℝ) * (n : ℝ) ^ (-(1 / 2 : ℝ))

theorem moebiusInvSqrtWeight_zero : moebiusInvSqrtWeight 0 = 0 := by simp [moebiusInvSqrtWeight]

theorem abs_moebiusInvSqrtWeight_le (n : ℕ) : |moebiusInvSqrtWeight n| ≤ (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
  rw [moebiusInvSqrtWeight, abs_mul, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)]
  have hμ : |(ArithmeticFunction.moebius n : ℝ)| ≤ 1 := by
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one
  calc |(ArithmeticFunction.moebius n : ℝ)| * (n : ℝ) ^ (-(1 / 2 : ℝ))
      ≤ 1 * (n : ℝ) ^ (-(1 / 2 : ℝ)) :=
        mul_le_mul_of_nonneg_right hμ (Real.rpow_nonneg (Nat.cast_nonneg n) _)
    _ = _ := one_mul _

theorem natCast_rpow_neg_half_le_one (n : ℕ) : (n : ℝ) ^ (-(1 / 2 : ℝ)) ≤ 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [Nat.cast_zero, Real.zero_rpow (by norm_num)]; norm_num
  · exact Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hn) (by norm_num)

theorem polyBoundedWeight_moebiusInvSqrtWeight : PolyBoundedWeight 0 moebiusInvSqrtWeight := fun n => by
  rw [pow_zero]; exact (abs_moebiusInvSqrtWeight_le n).trans (natCast_rpow_neg_half_le_one n)

/-- The smooth profile of one term: `μ(n) n^{−1/2} k(log n − y)`. -/
def causalLogProfile (n : ℕ) (y : ℝ) : ℝ := moebiusInvSqrtWeight n * thetaCuspFullSource (Real.log n - y)

theorem causalLogTerm_eq_indicator (x : ℝ) (n : ℕ) :
    causalLogTerm x n = Set.indicator (Iio (Real.log n)) (causalLogProfile n) x := by
  rfl

theorem continuous_causalLogProfile (n : ℕ) : Continuous (causalLogProfile n) :=
  continuous_const.mul (continuous_thetaCuspFullSource.comp (continuous_const.sub continuous_id))

theorem exists_abs_causalLogTerm_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (x : ℝ) (n : ℕ), |causalLogTerm x n| ≤ C * Real.exp (2 * x) * (n : ℝ) ^ (-(5 / 2 : ℝ)) := by
  obtain ⟨C, hC0, hC⟩ := exists_abs_causalMobiusThetaTerm_le
  refine ⟨C, hC0, fun x n => ?_⟩
  have h := hC (Real.exp x) n (Real.exp_pos x)
  rw [causalMobiusThetaTerm_exp, ← Real.exp_nat_mul] at h
  convert h using 3; push_cast; ring_nf

/-- Domination on `(−∞, X]`. -/
theorem exists_abs_causalLogTerm_le_of_le (X : ℝ) :
    ∃ u : ℕ → ℝ, Summable u ∧ ∀ (x : ℝ) (n : ℕ), x ≤ X → ‖causalLogTerm x n‖ ≤ u n := by
  obtain ⟨C, hC0, hC⟩ := exists_abs_causalLogTerm_le
  refine ⟨fun n => C * Real.exp (2 * X) * (n : ℝ) ^ (-(5 / 2 : ℝ)),
    summable_natCast_rpow_neg_five_halves.mul_left _, fun x n hx => ?_⟩
  rw [Real.norm_eq_abs]
  exact (hC x n).trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.2 (by linarith)) hC0) (Real.rpow_nonneg (Nat.cast_nonneg _) _))

theorem continuousWithinAt_causalLogTerm_Ici (x : ℝ) (n : ℕ) :
    ContinuousWithinAt (fun y => causalLogTerm y n) (Ici x) x := by
  simp_rw [causalLogTerm_eq_indicator]
  rcases lt_or_ge x (Real.log n) with hx | hx
  · refine ((continuous_causalLogProfile n).continuousAt.congr ?_).continuousWithinAt
    filter_upwards [Iio_mem_nhds hx] with y hy
    rw [Set.indicator_of_mem hy]
  · have h0 : ∀ y ∈ Ici x, Set.indicator (Iio (Real.log n)) (causalLogProfile n) y = 0 :=
      fun y hy => Set.indicator_of_notMem (show y ∉ Iio (Real.log n) from fun h =>
        absurd (lt_of_lt_of_le (show y < Real.log n from h) hx) (not_lt.2 (hy : x ≤ y))) _
    exact (continuousWithinAt_const (b := (0 : ℝ)) (s := Ici x) (x := x)).congr h0
      (h0 x Set.self_mem_Ici)

theorem continuousAt_causalLogTerm {x : ℝ} {n : ℕ} (hx : x ≠ Real.log n) :
    ContinuousAt (fun y => causalLogTerm y n) x := by
  simp_rw [causalLogTerm_eq_indicator]
  rcases lt_or_gt_of_ne hx with hx | hx
  · refine (continuous_causalLogProfile n).continuousAt.congr ?_
    filter_upwards [Iio_mem_nhds hx] with y hy
    rw [Set.indicator_of_mem hy]
  · refine (continuousAt_const (y := (0 : ℝ))).congr ?_
    filter_upwards [Ioi_mem_nhds hx] with y hy
    exact (Set.indicator_of_notMem (show y ∉ Iio (Real.log n) from fun h =>
      lt_irrefl y (lt_trans (show y < Real.log n from h) (show Real.log n < y from hy))) _).symm

theorem tendsto_causalLogTerm_left (n : ℕ) :
    Tendsto (fun y => causalLogTerm y n) (𝓝[<] Real.log n)
      (𝓝 (moebiusInvSqrtWeight n * thetaCuspFullSource 0)) := by
  have h := ((continuous_causalLogProfile n).tendsto (Real.log n)).mono_left
    (nhdsWithin_le_nhds (s := Iio (Real.log n)))
  simp only [causalLogProfile, sub_self] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with y hy
  rw [causalLogTerm_eq_indicator, Set.indicator_of_mem hy, causalLogProfile]

theorem causalLogTerm_log_self (n : ℕ) : causalLogTerm (Real.log n) n = 0 := by
  rw [causalLogTerm_eq_indicator]
  exact Set.indicator_of_notMem (show Real.log n ∉ Iio (Real.log n) from Set.self_notMem_Iio) _

/-! ## Right-continuity, continuity off the sites, and the jumps (10) -/

/-- **`b` is right-continuous everywhere.** -/
theorem continuousWithinAt_causalLogTail_Ici (x : ℝ) : ContinuousWithinAt causalLogTail (Ici x) x := by
  obtain ⟨u, hu, hbound⟩ := exists_abs_causalLogTerm_le_of_le (x + 1)
  have hlim : ∀ n : ℕ, Tendsto (fun y => causalLogTerm y n) (𝓝[≥] x) (𝓝 (causalLogTerm x n)) :=
    fun n => continuousWithinAt_causalLogTerm_Ici x n
  have hb : ∀ᶠ y in 𝓝[≥] x, ∀ n, ‖causalLogTerm y n‖ ≤ u n := by
    filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds (show x < x + 1 by linarith))] with y hy n
    exact hbound y n (le_of_lt hy)
  have h := tendsto_tsum_of_dominated_convergence hu hlim hb
  rw [ContinuousWithinAt, causalLogTail_fun]
  exact h

/-- **`b` is continuous off the logarithmic sites.** -/
theorem continuousAt_causalLogTail {x : ℝ} (hx : ∀ n : ℕ, x ≠ Real.log n) :
    ContinuousAt causalLogTail x := by
  obtain ⟨u, hu, hbound⟩ := exists_abs_causalLogTerm_le_of_le (x + 1)
  have hlim : ∀ n : ℕ, Tendsto (fun y => causalLogTerm y n) (𝓝 x) (𝓝 (causalLogTerm x n)) :=
    fun n => continuousAt_causalLogTerm (hx n)
  have hb : ∀ᶠ y in 𝓝 x, ∀ n, ‖causalLogTerm y n‖ ≤ u n := by
    filter_upwards [Iio_mem_nhds (show x < x + 1 by linarith)] with y hy n
    exact hbound y n (le_of_lt hy)
  have h := tendsto_tsum_of_dominated_convergence hu hlim hb
  rw [ContinuousAt, causalLogTail_fun]
  exact h

theorem log_natCast_injOn {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (h : Real.log m = Real.log n) : m = n := by
  have := Real.log_injOn_pos (Set.mem_Ioi.2 (by exact_mod_cast hm : (0 : ℝ) < m))
    (Set.mem_Ioi.2 (by exact_mod_cast hn : (0 : ℝ) < n)) h
  exact_mod_cast this

/-- **The left limit at `log m`.** -/
theorem tendsto_causalLogTail_left {m : ℕ} (hm : 0 < m) :
    Tendsto causalLogTail (𝓝[<] Real.log m)
      (𝓝 (causalLogTail (Real.log m) + moebiusInvSqrtWeight m * thetaCuspFullSource 0)) := by
  obtain ⟨u, hu, hbound⟩ := exists_abs_causalLogTerm_le_of_le (Real.log m)
  set g : ℕ → ℝ := fun n => if n = m then moebiusInvSqrtWeight m * thetaCuspFullSource 0
    else causalLogTerm (Real.log m) n
  have hlim : ∀ n, Tendsto (fun y => causalLogTerm y n) (𝓝[<] Real.log m) (𝓝 (g n)) := by
    intro n
    by_cases hnm : n = m
    · subst hnm; simp only [g, if_true]; exact tendsto_causalLogTerm_left n
    · simp only [g, hnm, if_false]
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · have h0 : ∀ y, causalLogTerm y 0 = 0 := fun y => by
          rw [causalLogTerm_eq_indicator]; simp [causalLogProfile, moebiusInvSqrtWeight]
        simp only [h0]; exact tendsto_const_nhds
      · exact ((continuousAt_causalLogTerm fun h =>
          hnm (log_natCast_injOn hn hm h.symm)).tendsto).mono_left
          (nhdsWithin_le_nhds (s := Iio (Real.log m)))
  have hb : ∀ᶠ y in 𝓝[<] Real.log m, ∀ n, ‖causalLogTerm y n‖ ≤ u n := by
    filter_upwards [self_mem_nhdsWithin] with y hy n
    exact hbound y n (le_of_lt hy)
  have h := tendsto_tsum_of_dominated_convergence hu hlim hb
  rw [causalLogTail_fun]
  convert h using 2
  · have hsum : Summable fun n => causalLogTerm (Real.log m) n :=
      Summable.of_norm_bounded hu fun n => hbound _ n le_rfl
    have hg : g = (fun n => causalLogTerm (Real.log m) n) +
        Pi.single m (moebiusInvSqrtWeight m * thetaCuspFullSource 0) := by
      funext n
      simp only [g, Pi.add_apply, Pi.single_apply]
      by_cases hnm : n = m
      · subst hnm; simp [causalLogTerm_log_self]
      · simp [hnm]
    have hsingle : Summable (Pi.single m (moebiusInvSqrtWeight m * thetaCuspFullSource 0) : ℕ → ℝ) :=
      (hasSum_pi_single m _).summable
    show (∑' n, causalLogTerm (Real.log m) n) + _ = _
    rw [hg]
    simp only [Pi.add_apply]
    rw [Summable.tsum_add hsum hsingle, tsum_pi_single]

/-- The jump `b(log m+) − b(log m−)`. -/
def causalLogJump (m : ℕ) : ℝ :=
  causalLogTail (Real.log m) - limUnder (𝓝[<] Real.log m) causalLogTail

theorem natCast_rpow_neg_half_eq_inv_sqrt (m : ℕ) : (m : ℝ) ^ (-(1 / 2 : ℝ)) = (Real.sqrt m)⁻¹ := by
  rw [Real.sqrt_eq_rpow, Real.rpow_neg (Nat.cast_nonneg m)]

/-- **(10) The exact jump.**  `b(log m+) − b(log m−) = −k(0) μ(m)/√m`, `b(log m+) = b(log m)`. -/
theorem causalLogJump_eq {m : ℕ} (hm : 0 < m) :
    causalLogJump m = -(thetaCuspFullSource 0 * ArithmeticFunction.moebius m / Real.sqrt m) := by
  rw [causalLogJump, (tendsto_causalLogTail_left hm).limUnder_eq, moebiusInvSqrtWeight,
    natCast_rpow_neg_half_eq_inv_sqrt]
  ring

/-- **(11) Coefficient recovery.**  `μ(m) = −√m [b(log m+) − b(log m−)]/k(0)`. -/
theorem moebius_eq_of_causalLogJump {m : ℕ} (hm : 0 < m) :
    (ArithmeticFunction.moebius m : ℝ) = -(Real.sqrt m * causalLogJump m) / thetaCuspFullSource 0 := by
  have hk := HedenmalmThetaSource.thetaCuspFullSource_pos 0
  have hs : 0 < Real.sqrt m := Real.sqrt_pos.2 (by exact_mod_cast hm)
  rw [causalLogJump_eq hm]
  field_simp

/-- **The jump is nonzero exactly at squarefree sites.** -/
theorem causalLogJump_ne_zero_iff {m : ℕ} (hm : 0 < m) : causalLogJump m ≠ 0 ↔ Squarefree m := by
  have hk := HedenmalmThetaSource.thetaCuspFullSource_pos 0
  have hs : 0 < Real.sqrt m := Real.sqrt_pos.2 (by exact_mod_cast hm)
  rw [causalLogJump_eq hm, ← ArithmeticFunction.moebius_ne_zero_iff_squarefree, Ne, Ne, neg_eq_zero,
    div_eq_zero_iff, mul_eq_zero, Int.cast_eq_zero]
  simp [hk.ne', hs.ne']

/-- **`b` is discontinuous at every squarefree site.** -/
theorem not_continuousAt_causalLogTail {m : ℕ} (hm : 0 < m) (hsq : Squarefree m) :
    ¬ ContinuousAt causalLogTail (Real.log m) := by
  intro hc
  have h1 := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Iio (Real.log m)))
  have h2 := tendsto_causalLogTail_left hm
  have := tendsto_nhds_unique h2 h1
  have hj : causalLogJump m = 0 := by
    rw [causalLogJump, h1.limUnder_eq, sub_self]
  exact (causalLogJump_ne_zero_iff hm).2 hsq hj

/-! ## (12) The exterior initial value -/

theorem mulConvWeight_moebiusInvSqrt_invSqrt (m : ℕ) :
    mulConvWeight moebiusInvSqrtWeight invSqrtWeight m = if m = 1 then 1 else 0 := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [mulConvWeight]
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have h1 : mulConvWeight moebiusInvSqrtWeight invSqrtWeight m =
      (m : ℝ) ^ (-(1 / 2 : ℝ)) * (ArithmeticFunction.moebius * ArithmeticFunction.zeta :
        ArithmeticFunction ℝ) m := by
    rw [mulConvWeight, ArithmeticFunction.mul_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p hp => ?_
    have hp' := Nat.mem_divisorsAntidiagonal.1 hp
    have h2 : p.2 ≠ 0 := fun h => by rw [h, mul_zero] at hp'; exact hm.ne' hp'.1.symm
    have hmul : (m : ℝ) = (p.1 : ℝ) * (p.2 : ℝ) := by rw [← hp'.1]; push_cast; ring
    rw [moebiusInvSqrtWeight, invSqrtWeight, hmul, Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
    simp [ArithmeticFunction.natCoe_apply, ArithmeticFunction.zeta_apply, h2]
    ring
  rw [h1, ArithmeticFunction.coe_moebius_mul_coe_zeta, ArithmeticFunction.one_apply]
  split_ifs with h
  · subst h; simp
  · simp

/-- **(12)** For `0 < t < 1` the causal tail is the Gaussian seed: `B(t) = h(−log t)`. -/
theorem causalMobiusThetaTail_eq_seed {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    causalMobiusThetaTail t = thetaSeedAtom (-Real.log t) := by
  have hterm : ∀ n : ℕ, causalMobiusThetaTerm t n =
      moebiusInvSqrtWeight n * thetaCuspFullSource (-Real.log t + Real.log n) := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [causalMobiusThetaTerm, moebiusInvSqrtWeight]
    have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
    rw [causalMobiusThetaTerm, Set.indicator_of_mem (show t ∈ Ioo 0 (n : ℝ) from ⟨ht0, by linarith⟩),
      moebiusInvSqrtWeight, Real.log_div (by positivity) ht0.ne']
    ring_nf
  rw [causalMobiusThetaTail, tsum_congr hterm]
  have h := GaussianLogTail.logShiftSeries_logShiftSeries gaussianLogTail_thetaSeedAtom
    polyBoundedWeight_moebiusInvSqrtWeight polyBoundedWeight_invSqrtWeight moebiusInvSqrtWeight_zero
    invSqrtWeight_zero (-Real.log t)
  rw [← thetaCuspFullSource_eq_logShiftSeries] at h
  rw [logShiftSeries] at h
  rw [h, logShiftSeries]
  simp_rw [mulConvWeight_moebiusInvSqrt_invSqrt, ite_mul, one_mul, zero_mul]
  rw [tsum_ite_eq]
  simp

/-! ## (13) Jump part and regular part -/

/-- The pure jump function `J(x) = −k(0) Σ_{1 ≤ m ≤ e^x} μ(m)/√m`. -/
def causalJumpPart (x : ℝ) : ℝ :=
  -(thetaCuspFullSource 0) * ∑ m ∈ Finset.Icc 1 ⌊Real.exp x⌋₊, moebiusInvSqrtWeight m

/-- One term `μ(n) n^{−1/2} k((log n − x)⁺)` of the regular part. -/
def causalRegularTerm (n : ℕ) (x : ℝ) : ℝ :=
  moebiusInvSqrtWeight n * thetaCuspFullSource (max (Real.log n - x) 0)

/-- The regular part `c(x) = Σ_n μ(n) n^{−1/2} k((log n − x)⁺)`. -/
def causalRegularPart (x : ℝ) : ℝ := ∑' n : ℕ, causalRegularTerm n x

theorem natCast_rpow_neg_two_eq {n : ℕ} (hn : 0 < n) :
    (n : ℝ) ^ (-(2 : ℝ)) = Real.exp (-(2 * Real.log n)) := by
  rw [Real.rpow_def_of_pos (by exact_mod_cast hn)]; ring_nf

theorem mem_Icc_floor_exp_iff {x : ℝ} {n : ℕ} :
    n ∈ Finset.Icc 1 ⌊Real.exp x⌋₊ ↔ 0 < n ∧ Real.log n ≤ x := by
  rw [Finset.mem_Icc, Nat.le_floor_iff (Real.exp_pos x).le]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    rw [Real.log_le_iff_le_exp (by exact_mod_cast h1)]; exact h2
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    rwa [← Real.log_le_iff_le_exp (by exact_mod_cast h1)]

theorem exists_abs_causalRegularTerm_le (X : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (x : ℝ) (n : ℕ), x ≤ X →
      |causalRegularTerm n x| ≤ C * (n : ℝ) ^ (-(5 / 2 : ℝ)) := by
  obtain ⟨C, hC0, hC⟩ := exists_abs_thetaCuspFullSource_le 2
  refine ⟨C * Real.exp (2 * X), by positivity, fun x n hx => ?_⟩
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [causalRegularTerm, moebiusInvSqrtWeight]
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  rw [causalRegularTerm, abs_mul]
  have h1 := abs_moebiusInvSqrtWeight_le n
  have h2 := hC (max (Real.log n - x) 0)
  have hmax : Real.log n - X ≤ |max (Real.log n - x) 0| := by
    rw [abs_of_nonneg (le_max_right _ _)]; exact le_trans (by linarith) (le_max_left _ _)
  have h3 : Real.exp (-(2 * |max (Real.log n - x) 0|)) ≤ Real.exp (2 * X) * (n : ℝ) ^ (-(2 : ℝ)) := by
    rw [natCast_rpow_neg_two_eq hn, ← Real.exp_add]
    exact Real.exp_le_exp.2 (by linarith)
  have hsplit : (n : ℝ) ^ (-(5 / 2 : ℝ)) = (n : ℝ) ^ (-(1 / 2 : ℝ)) * (n : ℝ) ^ (-(2 : ℝ)) := by
    rw [← Real.rpow_add hnR]; norm_num
  rw [hsplit]
  calc |moebiusInvSqrtWeight n| * |thetaCuspFullSource (max (Real.log n - x) 0)|
      ≤ (n : ℝ) ^ (-(1 / 2 : ℝ)) * (C * (Real.exp (2 * X) * (n : ℝ) ^ (-(2 : ℝ)))) :=
        mul_le_mul h1 (h2.trans (mul_le_mul_of_nonneg_left h3 hC0)) (abs_nonneg _)
          (Real.rpow_nonneg hnR.le _)
    _ = _ := by ring

theorem summable_causalRegularTerm (x : ℝ) : Summable fun n : ℕ => causalRegularTerm n x := by
  obtain ⟨C, _, hC⟩ := exists_abs_causalRegularTerm_le x
  exact Summable.of_norm_bounded (summable_natCast_rpow_neg_five_halves.mul_left C)
    fun n => (hC x n le_rfl)

/-- **(13) The decomposition `b = J + c`.** -/
theorem causalLogTail_eq_jump_add_regular (x : ℝ) :
    causalLogTail x = causalJumpPart x + causalRegularPart x := by
  have hterm : ∀ n : ℕ, causalRegularTerm n x =
      causalLogTerm x n + if n ∈ Finset.Icc 1 ⌊Real.exp x⌋₊ then
        thetaCuspFullSource 0 * moebiusInvSqrtWeight n else 0 := by
    intro n
    rw [causalLogTerm_eq_indicator, causalRegularTerm]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · have h0 : causalLogProfile 0 = 0 := funext fun y => by
        simp [causalLogProfile, moebiusInvSqrtWeight]
      simp [h0, moebiusInvSqrtWeight]
    by_cases hx : x < Real.log n
    · have hnot : n ∉ Finset.Icc 1 ⌊Real.exp x⌋₊ := fun h =>
        absurd (mem_Icc_floor_exp_iff.1 h).2 (not_le.2 hx)
      rw [Set.indicator_of_mem (show x ∈ Iio (Real.log n) from hx), if_neg hnot,
        max_eq_left (by linarith), causalLogProfile]
      ring
    · have hmem : n ∈ Finset.Icc 1 ⌊Real.exp x⌋₊ := mem_Icc_floor_exp_iff.2 ⟨hn, not_lt.1 hx⟩
      rw [Set.indicator_of_notMem (show x ∉ Iio (Real.log n) from hx), if_pos hmem,
        max_eq_right (by linarith)]
      ring
  have hs1 : Summable fun n => causalLogTerm x n := by
    obtain ⟨u, hu, hb⟩ := exists_abs_causalLogTerm_le_of_le x
    exact Summable.of_norm_bounded hu fun n => hb x n le_rfl
  have hs2 : Summable fun n : ℕ => if n ∈ Finset.Icc 1 ⌊Real.exp x⌋₊ then
      thetaCuspFullSource 0 * moebiusInvSqrtWeight n else 0 :=
    summable_of_ne_finset_zero (s := Finset.Icc 1 ⌊Real.exp x⌋₊) fun n hn => if_neg hn
  rw [causalRegularPart, tsum_congr hterm, Summable.tsum_add hs1 hs2,
    tsum_eq_sum (s := Finset.Icc 1 ⌊Real.exp x⌋₊) fun n hn => if_neg hn, causalLogTail_eq,
    causalJumpPart, Finset.sum_ite_of_true fun n hn => hn, ← Finset.mul_sum]
  ring

/-- `|k(a) − k(b)| ≤ C e^{2X} n^{−2} |a − b|` on `[max(log n − X, 0), ∞)`. -/
theorem abs_thetaCuspFullSource_sub_le {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ x : ℝ, |deriv thetaCuspFullSource x| ≤ C * Real.exp (-(2 * |x|))) (X : ℝ) {n : ℕ} (hn : 0 < n)
    {a b : ℝ} (ha : max (Real.log n - X) 0 ≤ a) (hb : max (Real.log n - X) 0 ≤ b) :
    |thetaCuspFullSource a - thetaCuspFullSource b| ≤
      C * Real.exp (2 * X) * (n : ℝ) ^ (-(2 : ℝ)) * |a - b| := by
  set K : ℝ := C * Real.exp (2 * X) * (n : ℝ) ^ (-(2 : ℝ))
  have hK : 0 ≤ K := by positivity
  have hlip : LipschitzOnWith (Real.toNNReal K) thetaCuspFullSource (Ici (max (Real.log n - X) 0)) := by
    refine Convex.lipschitzOnWith_of_nnnorm_deriv_le (fun u _ => differentiable_thetaCuspFullSource u)
      (fun u hu => ?_) (convex_Ici _)
    rw [← NNReal.coe_le_coe, coe_nnnorm, Real.norm_eq_abs, Real.coe_toNNReal _ hK]
    have hu' : max (Real.log n - X) 0 ≤ u := hu
    have hu0 : 0 ≤ u := le_trans (le_max_right _ _) hu'
    have hu1 : Real.log n - X ≤ u := le_trans (le_max_left _ _) hu'
    refine (hC u).trans ?_
    rw [abs_of_nonneg hu0]
    have : Real.exp (-(2 * u)) ≤ Real.exp (2 * X) * (n : ℝ) ^ (-(2 : ℝ)) := by
      rw [natCast_rpow_neg_two_eq hn, ← Real.exp_add]
      exact Real.exp_le_exp.2 (by linarith)
    calc C * Real.exp (-(2 * u)) ≤ C * (Real.exp (2 * X) * (n : ℝ) ^ (-(2 : ℝ))) :=
          mul_le_mul_of_nonneg_left this hC0
      _ = K := by ring
  have h := hlip.dist_le_mul a ha b hb
  rwa [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ hK] at h

/-- **The regular part is Lipschitz on every half-line `(−∞, X]`.** -/
theorem exists_lipschitzOnWith_causalRegularPart (X : ℝ) :
    ∃ L : NNReal, LipschitzOnWith L causalRegularPart (Iic X) := by
  obtain ⟨C, hC0, hC⟩ := exists_abs_deriv_thetaCuspFullSource_le 2
  set S : ℝ := ∑' n : ℕ, (n : ℝ) ^ (-(5 / 2 : ℝ))
  have hS : 0 ≤ S := tsum_nonneg fun n => Real.rpow_nonneg (Nat.cast_nonneg n) _
  set L : ℝ := C * Real.exp (2 * X) * S
  have hL : 0 ≤ L := by positivity
  refine ⟨Real.toNNReal L, LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_⟩
  have hx' : x ≤ X := hx
  have hy' : y ≤ X := hy
  set bnd : ℕ → ℝ := fun n => C * Real.exp (2 * X) * (n : ℝ) ^ (-(5 / 2 : ℝ)) * |x - y|
  have hterm : ∀ n : ℕ, |causalRegularTerm n x - causalRegularTerm n y| ≤ bnd n := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp only [causalRegularTerm, moebiusInvSqrtWeight, ArithmeticFunction.map_zero, Int.cast_zero,
        zero_mul, sub_self, abs_zero, bnd]
      positivity
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have hxm : max (Real.log n - X) 0 ≤ max (Real.log n - x) 0 := max_le_max (by linarith) le_rfl
    have hym : max (Real.log n - X) 0 ≤ max (Real.log n - y) 0 := max_le_max (by linarith) le_rfl
    have h1 := abs_thetaCuspFullSource_sub_le hC0 hC X hn hxm hym
    have h2 : |max (Real.log n - x) 0 - max (Real.log n - y) 0| ≤ |x - y| := by
      refine (abs_max_sub_max_le_abs _ _ _).trans (le_of_eq ?_)
      rw [show Real.log n - x - (Real.log n - y) = -(x - y) by ring, abs_neg]
    have h3 := abs_moebiusInvSqrtWeight_le n
    have hsplit : (n : ℝ) ^ (-(5 / 2 : ℝ)) = (n : ℝ) ^ (-(1 / 2 : ℝ)) * (n : ℝ) ^ (-(2 : ℝ)) := by
      rw [← Real.rpow_add hnR]; norm_num
    rw [causalRegularTerm, causalRegularTerm, ← mul_sub, abs_mul]
    calc |moebiusInvSqrtWeight n| * |thetaCuspFullSource (max (Real.log n - x) 0) -
          thetaCuspFullSource (max (Real.log n - y) 0)|
        ≤ (n : ℝ) ^ (-(1 / 2 : ℝ)) * (C * Real.exp (2 * X) * (n : ℝ) ^ (-(2 : ℝ)) * |x - y|) :=
          mul_le_mul h3 (h1.trans (mul_le_mul_of_nonneg_left h2 (by positivity))) (abs_nonneg _)
            (Real.rpow_nonneg hnR.le _)
      _ = bnd n := by simp only [bnd]; rw [hsplit]; ring
  have hsb : Summable bnd := (summable_natCast_rpow_neg_five_halves.mul_left _).mul_right _
  have hs1 : Summable fun n : ℕ => |causalRegularTerm n x - causalRegularTerm n y| :=
    Summable.of_nonneg_of_le (fun _ => abs_nonneg _) hterm hsb
  rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ hL, causalRegularPart, causalRegularPart,
    ← (summable_causalRegularTerm x).tsum_sub (summable_causalRegularTerm y)]
  calc |∑' n : ℕ, (causalRegularTerm n x - causalRegularTerm n y)|
      ≤ ∑' n : ℕ, |causalRegularTerm n x - causalRegularTerm n y| := by
        rw [← Real.norm_eq_abs]
        exact (norm_tsum_le_tsum_norm (by simpa only [Real.norm_eq_abs] using hs1)).trans_eq
          (tsum_congr fun n => Real.norm_eq_abs _)
    _ ≤ ∑' n : ℕ, bnd n := Summable.tsum_le_tsum hterm hs1 hsb
    _ = L * |x - y| := by
        simp only [bnd, L, S]
        rw [tsum_mul_right, tsum_mul_left]

theorem continuous_causalRegularPart : Continuous causalRegularPart := by
  refine continuous_iff_continuousAt.2 fun x => ?_
  obtain ⟨L, hL⟩ := exists_lipschitzOnWith_causalRegularPart (x + 1)
  exact (hL.continuousOn.continuousAt (Iic_mem_nhds (by linarith)))

/-- The jump part is locally constant off the sites: on `[log m, log (m+1))` it equals
`−k(0) Σ_{n=1}^{m} μ(n)/√n`, and it vanishes on `(−∞, 0)`. -/
theorem causalJumpPart_eq_of_mem {m : ℕ} (hm : 0 < m) {x : ℝ} (h1 : Real.log m ≤ x)
    (h2 : x < Real.log (m + 1)) :
    causalJumpPart x = -(thetaCuspFullSource 0) * ∑ n ∈ Finset.Icc 1 m, moebiusInvSqrtWeight n := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hfl : ⌊Real.exp x⌋₊ = m := by
    rw [Nat.floor_eq_iff (Real.exp_pos x).le]
    exact ⟨(Real.log_le_iff_le_exp hmR).1 h1, (Real.lt_log_iff_exp_lt (by positivity)).1 h2⟩
  rw [causalJumpPart, hfl]

theorem causalJumpPart_eq_zero_of_neg {x : ℝ} (hx : x < 0) : causalJumpPart x = 0 := by
  have hfl : ⌊Real.exp x⌋₊ = 0 := Nat.floor_eq_zero.2 (by rw [← Real.exp_zero]; exact Real.exp_lt_exp.2 hx)
  rw [causalJumpPart, hfl]
  simp

/-! ## The regular-transport obstruction -/

/-- A regular observation `y ↦ ∫ Σ_{i ≤ N} p_i C^{(i)}(y + a) dν(a)` of the cutoff current. -/
def regularCutoffObservation (p : ℕ → ℂ) (N : ℕ) (ν : Measure ℝ) (y : ℝ) : ℂ :=
  ∫ a, ∑ i ∈ Finset.range (N + 1), p i * ((iteratedDeriv i cofinalBoundaryProfile (y + a) : ℝ) : ℂ) ∂ν

/-- **Regular observations are continuous** (dominated convergence). -/
theorem continuous_regularCutoffObservation (p : ℕ → ℂ) (N : ℕ) (ν : Measure ℝ) [IsFiniteMeasure ν] :
    Continuous (regularCutoffObservation p N ν) := by
  choose M _ hM using exists_abs_iteratedDeriv_cofinalBoundaryProfile_le
  set B : ℝ := ∑ i ∈ Finset.range (N + 1), ‖p i‖ * M i
  have hcont := continuous_iteratedDeriv_cofinalBoundaryProfile
  refine continuous_of_dominated (bound := fun _ => B) (fun y => ?_)
    (fun y => Eventually.of_forall fun a => ?_) (integrable_const B) (Eventually.of_forall fun a => ?_)
  · exact (continuous_finsetSum _ fun i _ => continuous_const.mul (Complex.continuous_ofReal.comp
      ((hcont i).comp (continuous_const.add continuous_id)))).aestronglyMeasurable
  · refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hM i _) (norm_nonneg _)
  · exact continuous_finsetSum _ fun i _ => continuous_const.mul (Complex.continuous_ofReal.comp
      ((hcont i).comp (continuous_id.add continuous_const)))

/-- **Regular-transport obstruction.**  For every finite complex combination `Σ_j c_j ν_j` of finite
Borel measures — every finite complex Borel measure has this form — and every fixed finite-order
constant-coefficient operator `P(∂)`, the regular observation `y ↦ ∫ P(∂)C(y+a) dν(a)` is continuous,
hence never equals the causal source `b`, which jumps at `0 = log 1`. -/
theorem regularCutoffObservation_sum_ne_causalLogTail {ι : Type*} [Fintype ι] (c : ι → ℂ)
    (p : ι → ℕ → ℂ) (N : ι → ℕ) (ν : ι → Measure ℝ) [∀ j, IsFiniteMeasure (ν j)] :
    (fun y => ∑ j, c j * regularCutoffObservation (p j) (N j) (ν j) y) ≠
      fun y => (causalLogTail y : ℂ) := by
  intro h
  have hc : Continuous fun y => (causalLogTail y : ℂ) :=
    h ▸ continuous_finsetSum _ fun j _ => continuous_const.mul (continuous_regularCutoffObservation _ _ _)
  have hb : Continuous causalLogTail := by
    have := Complex.continuous_re.comp hc
    simpa only [Function.comp_def, Complex.ofReal_re] using this
  exact not_continuousAt_causalLogTail (m := 1) one_pos squarefree_one hb.continuousAt

/-- **The positive transfer cannot construct the causal source.**  `T` applied to any fixed
finite-order derivative combination of `C` (in particular `T(DC)`) is continuous, so differs from `b`. -/
theorem positiveTransfer_derivatives_ne_causalLogTail (p : ℕ → ℝ) (N : ℕ) :
    positiveTransfer (fun y => ∑ i ∈ Finset.range (N + 1), p i * iteratedDeriv i cofinalBoundaryProfile y) ≠
      causalLogTail := by
  intro h
  choose M _ hM using exists_abs_iteratedDeriv_cofinalBoundaryProfile_le
  have hf : Continuous fun y => ∑ i ∈ Finset.range (N + 1), p i * iteratedDeriv i cofinalBoundaryProfile y :=
    continuous_finsetSum _ fun i _ => continuous_const.mul (continuous_iteratedDeriv_cofinalBoundaryProfile i)
  have hfM : ∀ y, |∑ i ∈ Finset.range (N + 1), p i * iteratedDeriv i cofinalBoundaryProfile y| ≤
      ∑ i ∈ Finset.range (N + 1), |p i| * M i := fun y => by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hM i y) (abs_nonneg _)
  have hc := continuous_positiveTransfer hf hfM
  rw [h] at hc
  exact not_continuousAt_causalLogTail (m := 1) one_pos squarefree_one hc.continuousAt

end

end RHTower
