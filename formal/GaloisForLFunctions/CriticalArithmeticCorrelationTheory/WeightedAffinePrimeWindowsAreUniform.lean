import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.ActualAffinePrimeWindowsAreUniformInTheirParameters
import GaloisForLFunctions.RHTower.MertensFirst

/-!
# Weighted affine prime windows are uniform in their parameters

For a Lipschitz weight `F` on `[0,1]` vanishing on `[0,a]`, `a > 0`, the weighted affine prime
reading of a Ramanujan coefficient converges to its unit-average value,

`Σ_{k ≤ X} Λ(k)/k · c_q(kn+h) · F(k/X) → (c_q(n) c_q(h)/φ(q)) ∫_a^1 F(t) dt/t`,

uniformly in both affine parameters `n, h` and over real horizons `X`. A grid of `D` multiplicative
windows `(iY,(i+1)Y]`, `Y = ⌊X/D⌋`, reduces the weight to finitely many unweighted affine windows;
Mertens' bound pays the Lipschitz oscillation of the weight inside each window, the leftover
terms above `DY`, and the Riemann-sum error of `∫ F(t) dt/t`.
-/

noncomputable section

open MeasureTheory Finset Filter Topology

namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory

open BezoutValuationIncidence

local notation "Λ" => ArithmeticFunction.vonMangoldt

/-- The Mertens constant of `RHTower.Mertens.mertens_first`. -/
def mertensWindowConstant : ℝ := 2 * (Real.log 4 + 4)

theorem mertensWindowConstant_nonneg : 0 ≤ mertensWindowConstant := by
  unfold mertensWindowConstant
  have := Real.log_nonneg (show (1 : ℝ) ≤ 4 by norm_num)
  positivity

/-- A multiplicative window of prime powers costs its logarithmic length plus a constant. -/
theorem sum_Ioc_vonMangoldt_div_le {U V : ℕ} (hU : 1 ≤ U) (hUV : U ≤ V) :
    ∑ k ∈ Ioc U V, (Λ k : ℝ) / k ≤ Real.log V - Real.log U + mertensWindowConstant := by
  have hsplit : (∑ k ∈ Ioc 0 V, (Λ k : ℝ) / k) =
      (∑ k ∈ Ioc 0 U, (Λ k : ℝ) / k) + ∑ k ∈ Ioc U V, (Λ k : ℝ) / k :=
    (sum_Ioc_consecutive _ (Nat.zero_le U) hUV).symm
  have hV := (abs_le.mp (RHTower.Mertens.mertens_first V (hU.trans hUV))).2
  have hUm := (abs_le.mp (RHTower.Mertens.mertens_first U hU)).1
  have hIcc (n : ℕ) : Icc 1 n = Ioc 0 n := rfl
  rw [hIcc] at hV hUm
  unfold mertensWindowConstant
  linarith

theorem sum_vonMangoldt_div_nonneg (s : Finset ℕ) : 0 ≤ ∑ k ∈ s, (Λ k : ℝ) / k :=
  sum_nonneg fun k _ => div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg k)

/-- A prime-power reciprocal is at most `log k / k`. -/
theorem vonMangoldt_div_le_log_div (k : ℕ) : (Λ k : ℝ) / k ≤ Real.log k / k :=
  div_le_div_of_nonneg_right ArithmeticFunction.vonMangoldt_le_log (Nat.cast_nonneg k)

/-- Splitting an initial segment into `D` consecutive windows of length `Y`. -/
theorem sum_Ioc_zero_mul_eq_sum_windows (f : ℕ → ℝ) (D Y : ℕ) :
    ∑ k ∈ Ioc 0 (D * Y), f k = ∑ i ∈ range D, ∑ k ∈ Ioc (i * Y) ((i + 1) * Y), f k := by
  induction D with
  | zero => simp
  | succ D ih =>
    rw [Finset.sum_range_succ, ← ih, sum_Ioc_consecutive _ (Nat.zero_le _)
      (Nat.mul_le_mul_right Y (Nat.le_succ D))]

/-- Riemann sum of `∫ F(t) dt/t` on the grid `i/D` for a Lipschitz weight vanishing near zero. -/
theorem abs_sum_grid_sub_integral_le {a ℓ : ℝ} (ha1 : a ≤ 1) {F : ℝ → ℝ}
    (hF0 : ∀ t, t ≤ a → F t = 0)
    (hFlip : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) 1, |F s - F t| ≤ ℓ * |s - t|)
    {D : ℕ} (hD : 1 ≤ D) (hDa : 1 / (D : ℝ) ≤ a) :
    |∑ i ∈ range D, F (i / D) * (Real.log (i + 1) - Real.log i) - ∫ t in a..1, F t / t| ≤
      ℓ * Real.log D / D := by
  have hD0 : (0 : ℝ) < D := by exact_mod_cast hD
  set g : ℕ → ℝ := fun i => (i : ℝ) / D with hg
  have hcont : ContinuousOn F (Set.Icc 0 1) := by
    intro t ht
    refine Metric.continuousWithinAt_iff.mpr fun e he => ?_
    refine ⟨e / (|ℓ| + 1), by positivity, fun s hs hst => ?_⟩
    rw [Real.dist_eq] at hst ⊢
    calc |F s - F t| ≤ ℓ * |s - t| := hFlip s hs t ht
      _ ≤ |ℓ| * |s - t| := mul_le_mul_of_nonneg_right (le_abs_self ℓ) (abs_nonneg _)
      _ ≤ (|ℓ| + 1) * |s - t| := by nlinarith [abs_nonneg (s - t)]
      _ < (|ℓ| + 1) * (e / (|ℓ| + 1)) := mul_lt_mul_of_pos_left hst (by positivity)
      _ = e := by field_simp
  have hint (u v : ℝ) (hu : 0 < u) (huv : u ≤ v) (hv : v ≤ 1) :
      IntervalIntegrable (fun t => F t / t) MeasureTheory.volume u v := by
    refine (ContinuousOn.intervalIntegrable ?_)
    rw [Set.uIcc_of_le huv]
    refine (hcont.mono fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩).div
      continuousOn_id fun t ht => by linarith [ht.1]
  have hint0 (κ u v : ℝ) (hu : 0 < u) (huv : u ≤ v) :
      IntervalIntegrable (fun t => κ / t) MeasureTheory.volume u v := by
    refine (ContinuousOn.intervalIntegrable ?_)
    rw [Set.uIcc_of_le huv]
    exact continuousOn_const.div continuousOn_id fun t ht => by linarith [ht.1]
  -- `∫_a^1 = ∫_{1/D}^1`, since `F` vanishes on `[1/D, a]`.
  have hlow : (∫ t in a..1, F t / t) = ∫ t in (1 / (D : ℝ))..1, F t / t := by
    have hz : (∫ t in (1 / (D : ℝ))..a, F t / t) = 0 := by
      have hcongr : Set.EqOn (fun t => F t / t) (fun _ => (0 : ℝ)) (Set.uIcc (1 / (D : ℝ)) a) :=
        fun t ht => by
          rw [Set.uIcc_of_le hDa] at ht
          simp [hF0 t ht.2]
      rw [intervalIntegral.integral_congr hcongr, intervalIntegral.integral_zero]
    rw [← intervalIntegral.integral_add_adjacent_intervals
      (hint (1 / D) a (by positivity) hDa ha1) (hint a 1 ((by positivity : (0:ℝ) < 1 / D).trans_le hDa) ha1 le_rfl),
      hz, zero_add]
  -- adjacent grid intervals
  have hsumint : (∫ t in (1 / (D : ℝ))..1, F t / t) =
      ∑ i ∈ Ico 1 D, ∫ t in g i..g (i + 1), F t / t := by
    rw [intervalIntegral.sum_integral_adjacent_intervals_Ico hD]
    · simp only [hg, Nat.cast_one]
      rw [div_self hD0.ne']
    · intro i hi
      have hi1 : (1 : ℝ) ≤ i := by exact_mod_cast (Set.mem_Ico.mp hi).1
      have hiD : (i : ℝ) + 1 ≤ D := by exact_mod_cast (Set.mem_Ico.mp hi).2
      refine hint _ _ (by simp only [hg]; positivity) ?_ ?_
      · simp only [hg]; push_cast; gcongr; linarith
      · simp only [hg]; push_cast; rw [div_le_one hD0]; exact hiD
  have hcell (i : ℕ) (hi : i ∈ Ico 1 D) :
      |F (i / D) * (Real.log (i + 1) - Real.log i) - ∫ t in g i..g (i + 1), F t / t| ≤
        ℓ / D * (Real.log (i + 1) - Real.log i) := by
    have hi1 : (1 : ℝ) ≤ i := by exact_mod_cast (mem_Ico.mp hi).1
    have hiD : (i : ℝ) + 1 ≤ D := by exact_mod_cast (mem_Ico.mp hi).2
    have hgi : 0 < g i := by simp only [hg]; positivity
    have hgle : g i ≤ g (i + 1) := by simp only [hg]; push_cast; gcongr; linarith
    have hg1 : g (i + 1) ≤ 1 := by simp only [hg]; push_cast; rw [div_le_one hD0]; exact hiD
    have hlog : (∫ t in g i..g (i + 1), (1 : ℝ) / t) = Real.log (i + 1) - Real.log i := by
      rw [integral_one_div_of_pos hgi (hgi.trans_le hgle)]
      simp only [hg]; push_cast
      rw [div_div_div_cancel_right₀ hD0.ne', Real.log_div (by positivity) (by positivity)]
    have hconst : F (i / D) * (Real.log (i + 1) - Real.log i) =
        ∫ t in g i..g (i + 1), F (g i) / t := by
      rw [← hlog, ← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr fun t _ => ?_
      simp only [hg]; ring
    rw [hconst, ← intervalIntegral.integral_sub (hint0 (F (g i)) _ _ hgi hgle)
      (hint _ _ hgi hgle hg1)]
    · rw [← hlog, ← intervalIntegral.integral_const_mul]
      refine intervalIntegral.abs_integral_le_integral_abs hgle |>.trans
        (intervalIntegral.integral_mono_on hgle ?_ ?_ fun t ht => ?_)
      · exact ((hint0 (F (g i)) _ _ hgi hgle).sub (hint _ _ hgi hgle hg1)).abs
      · refine (ContinuousOn.intervalIntegrable ?_)
        rw [Set.uIcc_of_le hgle]
        exact continuousOn_const.mul (continuousOn_const.div continuousOn_id
          fun t ht => by linarith [ht.1])
      · have ht0 : 0 < t := hgi.trans_le ht.1
        have hgiI : g i ∈ Set.Icc (0 : ℝ) 1 := ⟨hgi.le, hgle.trans hg1⟩
        have htI : t ∈ Set.Icc (0 : ℝ) 1 := ⟨ht0.le, ht.2.trans hg1⟩
        have hdist : |g i - t| ≤ 1 / D := by
          rw [abs_sub_comm, abs_of_nonneg (by linarith [ht.1])]
          have : g (i + 1) - g i = 1 / D := by simp only [hg]; push_cast; ring
          linarith [ht.2]
        rw [← sub_div, abs_div, abs_of_pos ht0]
        have hℓ : 0 ≤ ℓ := by
          have := hFlip 0 ⟨le_rfl, zero_le_one⟩ 1 ⟨zero_le_one, le_rfl⟩
          have h2 := abs_nonneg (F 0 - F 1)
          norm_num at this
          linarith
        calc |F (g i) - F t| / t ≤ (ℓ * (1 / D)) / t :=
              div_le_div_of_nonneg_right ((hFlip _ hgiI _ htI).trans
                (mul_le_mul_of_nonneg_left hdist hℓ)) ht0.le
          _ = ℓ / D * (1 / t) := by ring
  -- the `i = 0` grid term vanishes
  have hzero : (∑ i ∈ range D, F (i / D) * (Real.log (i + 1) - Real.log i)) =
      ∑ i ∈ Ico 1 D, F (i / D) * (Real.log (i + 1) - Real.log i) := by
    rw [range_eq_Ico, ← sum_Ico_consecutive _ (Nat.zero_le 1) hD]
    simp [hF0 0 (by linarith [show (0 : ℝ) < 1 / D by positivity])]
  rw [hzero, hlow, hsumint, ← sum_sub_distrib]
  calc |∑ i ∈ Ico 1 D, (F (i / D) * (Real.log (i + 1) - Real.log i) -
        ∫ t in g i..g (i + 1), F t / t)|
      ≤ ∑ i ∈ Ico 1 D, ℓ / D * (Real.log (i + 1) - Real.log i) :=
        (abs_sum_le_sum_abs _ _).trans (sum_le_sum hcell)
    _ = ℓ / D * Real.log D := by
        rw [← mul_sum, sum_Ico_eq_sum_range]
        congr 1
        have h := sum_range_sub (fun i : ℕ => Real.log ((1 + i : ℕ) : ℝ)) (D - 1)
        have hD1 : 1 + (D - 1) = D := by omega
        simp only [hD1, Nat.cast_add, Nat.cast_one, add_zero, Real.log_one, sub_zero] at h
        rw [← h]
        refine sum_congr rfl fun i _ => ?_
        push_cast
        ring_nf
    _ = ℓ * Real.log D / D := by ring

/-- Window geometry: a grid window sits within `1/D + D/X` of its left node. -/
theorem grid_window_position {X : ℝ} (hX : 0 < X) {D : ℕ} (hD : 1 ≤ D) {i k : ℕ} (hi : i < D)
    (hk : k ∈ Ioc (i * ⌊X / D⌋₊) ((i + 1) * ⌊X / D⌋₊)) :
    (k : ℝ) / X ∈ Set.Icc (0 : ℝ) 1 ∧ |(k : ℝ) / X - i / D| ≤ 1 / D + D / X := by
  have hD0 : (0 : ℝ) < D := by exact_mod_cast hD
  set Y := ⌊X / D⌋₊ with hY
  have hYle : (Y : ℝ) ≤ X / D := Nat.floor_le (by positivity)
  have hYgt : X / D - 1 < Y := Nat.sub_one_lt_floor _
  obtain ⟨hk1, hk2⟩ := mem_Ioc.mp hk
  have hk1R : (i : ℝ) * Y < k := by exact_mod_cast hk1
  have hk2R : (k : ℝ) ≤ (i + 1) * Y := by exact_mod_cast hk2
  have hiD : (i : ℝ) + 1 ≤ D := by exact_mod_cast hi
  have hi0 : (0 : ℝ) ≤ i := Nat.cast_nonneg i
  have hup : (k : ℝ) / X ≤ (i + 1) / D := by
    rw [div_le_div_iff₀ hX hD0]
    calc (k : ℝ) * D ≤ (i + 1) * Y * D := mul_le_mul_of_nonneg_right hk2R hD0.le
      _ ≤ (i + 1) * (X / D) * D := by gcongr
      _ = (i + 1) * X := by field_simp
  have hlow : (i : ℝ) / D - D / X ≤ (k : ℝ) / X := by
    have h1 : (i : ℝ) * (X / D - 1) ≤ k := by nlinarith
    rw [sub_le_iff_le_add, div_le_iff₀ hD0]
    have h2 : (i : ℝ) ≤ D := by linarith
    calc (i : ℝ) = i * (X / D - 1) * D / X + i * D / X := by field_simp; ring
      _ ≤ k * D / X + D * D / X := by
          gcongr
      _ = ((k : ℝ) / X + D / X) * D := by ring
  have h1D : 0 ≤ 1 / (D : ℝ) := by positivity
  refine ⟨⟨by positivity, hup.trans ((div_le_one hD0).mpr hiD)⟩, abs_le.mpr ⟨?_, ?_⟩⟩
  · linarith
  · have : (i + 1 : ℝ) / D = i / D + 1 / D := by ring
    have hDX : 0 ≤ (D : ℝ) / X := by positivity
    linarith

/-- The windows above the first one carry the Mertens mass `log D + C`. -/
theorem sum_windows_above_first_le {D Y : ℕ} (hD : 1 ≤ D) (hY : 1 ≤ Y) :
    (∑ i ∈ Ico 1 D, ∑ k ∈ Ioc (i * Y) ((i + 1) * Y), (Λ k : ℝ) / k) ≤
      Real.log D + mertensWindowConstant := by
  have hw := sum_Ioc_zero_mul_eq_sum_windows (fun k => (Λ k : ℝ) / k) D Y
  rw [range_eq_Ico, ← sum_Ico_consecutive _ (Nat.zero_le 1) hD, Nat.Ico_succ_singleton,
    sum_singleton, zero_mul, zero_add, one_mul,
    ← sum_Ioc_consecutive _ (Nat.zero_le Y) (Nat.le_mul_of_pos_left Y (by omega))] at hw
  have hb := sum_Ioc_vonMangoldt_div_le hY (Nat.le_mul_of_pos_left Y (by omega : 0 < D))
  have hlog : Real.log ((D * Y : ℕ) : ℝ) - Real.log Y = Real.log D := by
    push_cast
    rw [Real.log_mul (by positivity) (by exact_mod_cast (by omega : Y ≠ 0))]
    ring
  linarith

/-- Oscillation of a Lipschitz weight inside the grid windows. -/
theorem abs_sum_window_oscillation_le {q : ℕ} {a ℓ X : ℝ} (ha : 0 < a) {F : ℝ → ℝ}
    (hF0 : ∀ t, t ≤ a → F t = 0)
    (hFlip : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) 1, |F s - F t| ≤ ℓ * |s - t|)
    (hℓ : 0 ≤ ℓ) (hX : 0 < X) {D : ℕ} (hD : 1 ≤ D) (hDa : 1 / (D : ℝ) ≤ a)
    (hY : 1 ≤ ⌊X / D⌋₊) (n h : ℕ) :
    |∑ i ∈ range D, ∑ k ∈ Ioc (i * ⌊X / D⌋₊) ((i + 1) * ⌊X / D⌋₊), (Λ k : ℝ) / k *
        ramanujanLagCoefficient q (k * n + h) * (F (k / X) - F (i / D))| ≤
      q.totient * ℓ * (1 / D + D / X) * (Real.log D + mertensWindowConstant) := by
  set Y := ⌊X / D⌋₊ with hYdef
  have hD0 : (0 : ℝ) < D := by exact_mod_cast hD
  have hYle : (Y : ℝ) ≤ X / D := Nat.floor_le (by positivity)
  set B : ℝ := q.totient * ℓ * (1 / D + D / X) with hB
  have hB0 : 0 ≤ B := by positivity
  -- the first window vanishes identically
  have h0 : (∑ k ∈ Ioc (0 * Y) ((0 + 1) * Y), (Λ k : ℝ) / k *
      ramanujanLagCoefficient q (k * n + h) * (F (k / X) - F ((0 : ℕ) / D))) = 0 := by
    refine sum_eq_zero fun k hk => ?_
    have hk2 : (k : ℝ) ≤ Y := by
      have := (mem_Ioc.mp hk).2
      simp only [zero_add, one_mul] at this
      exact_mod_cast this
    have hkX : (k : ℝ) / X ≤ a := by
      calc (k : ℝ) / X ≤ (X / D) / X := by gcongr; exact hk2.trans hYle
        _ = 1 / D := by field_simp
        _ ≤ a := hDa
    simp [hF0 _ hkX, hF0 0 ha.le]
  have hcell (i : ℕ) (hi : i ∈ Ico 1 D) :
      |∑ k ∈ Ioc (i * Y) ((i + 1) * Y), (Λ k : ℝ) / k *
        ramanujanLagCoefficient q (k * n + h) * (F (k / X) - F (i / D))| ≤
        B * ∑ k ∈ Ioc (i * Y) ((i + 1) * Y), (Λ k : ℝ) / k := by
    rw [mul_sum]
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun k hk => ?_)
    have hiD : i < D := (mem_Ico.mp hi).2
    have hpos := grid_window_position hX hD hiD hk
    have hiI : (i : ℝ) / D ∈ Set.Icc (0 : ℝ) 1 :=
      ⟨by positivity, (div_le_one hD0).mpr (by exact_mod_cast hiD.le)⟩
    have hosc := (hFlip _ hpos.1 _ hiI).trans (mul_le_mul_of_nonneg_left hpos.2 hℓ)
    have hΛ : 0 ≤ (Λ k : ℝ) / k :=
      div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg k)
    have hc := BiScaleUncertainty.SieveMoments.abs_ramanujanLagCoefficient_le_totient q
      (k * n + h)
    rw [abs_mul, abs_mul, abs_of_nonneg hΛ]
    calc (Λ k : ℝ) / k * |ramanujanLagCoefficient q (k * n + h)| * |F (k / X) - F (i / D)|
        ≤ (Λ k : ℝ) / k * q.totient * (ℓ * (1 / D + D / X)) := by gcongr
      _ = B * ((Λ k : ℝ) / k) := by rw [hB]; ring
  rw [range_eq_Ico, ← sum_Ico_consecutive _ (Nat.zero_le 1) hD, Nat.Ico_succ_singleton,
    sum_singleton]
  have h0' : (∑ k ∈ Ioc (0 * Y) ((0 + 1) * Y), (Λ k : ℝ) / k *
      ramanujanLagCoefficient q (k * n + h) * (F (k / X) - F (((0 : ℕ) : ℝ) / D))) = 0 := h0
  rw [h0', zero_add]
  calc _ ≤ ∑ i ∈ Ico 1 D, B * ∑ k ∈ Ioc (i * Y) ((i + 1) * Y), (Λ k : ℝ) / k :=
        (abs_sum_le_sum_abs _ _).trans (sum_le_sum hcell)
    _ = B * ∑ i ∈ Ico 1 D, ∑ k ∈ Ioc (i * Y) ((i + 1) * Y), (Λ k : ℝ) / k := by rw [mul_sum]
    _ ≤ B * (Real.log D + mertensWindowConstant) :=
        mul_le_mul_of_nonneg_left (sum_windows_above_first_le hD hY) hB0

/-- The leftover terms above the last full window. -/
theorem abs_sum_leftover_le {q : ℕ} {ℓ X : ℝ} {F : ℝ → ℝ}
    (hFb : ∀ t ∈ Set.Icc (0 : ℝ) 1, |F t| ≤ ℓ) (hℓ : 0 ≤ ℓ) {D : ℕ} (hD : 1 ≤ D)
    (hX2D : 2 * (D : ℝ) ≤ X) (n h : ℕ) :
    |∑ k ∈ Ioc (D * ⌊X / D⌋₊) ⌊X⌋₊, (Λ k : ℝ) / k *
        ramanujanLagCoefficient q (k * n + h) * F (k / X)| ≤
      D * (q.totient * ℓ * (2 * (Real.log X / X))) := by
  have hD0 : (0 : ℝ) < D := by exact_mod_cast hD
  have hD1R : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hXpos : 0 < X := by linarith
  set Y := ⌊X / D⌋₊ with hYdef
  have hYgt : X / D - 1 < Y := Nat.sub_one_lt_floor _
  have h2 : X - D < D * Y := by
    have := hYgt
    rw [div_sub_one hD0.ne', div_lt_iff₀ hD0] at this
    linarith
  have hcard : ((Ioc (D * Y) ⌊X⌋₊).card : ℝ) ≤ D := by
    rw [Nat.card_Ioc]
    have h1 : (⌊X⌋₊ : ℝ) ≤ X := Nat.floor_le hXpos.le
    have h3 : ⌊X⌋₊ < D * Y + D := by
      have : (⌊X⌋₊ : ℝ) < D * Y + D := by linarith
      exact_mod_cast this
    exact_mod_cast (show ⌊X⌋₊ - D * Y ≤ D by omega)
  have hk (k : ℕ) (hk : k ∈ Ioc (D * Y) ⌊X⌋₊) :
      |(Λ k : ℝ) / k * ramanujanLagCoefficient q (k * n + h) * F (k / X)| ≤
        q.totient * ℓ * (2 * (Real.log X / X)) := by
    obtain ⟨hk1, hk2⟩ := mem_Ioc.mp hk
    have hkX : (k : ℝ) ≤ X := (Nat.cast_le.mpr hk2).trans (Nat.floor_le hXpos.le)
    have hk1R : (D : ℝ) * Y < k := by exact_mod_cast hk1
    have hkX2 : X / 2 ≤ k := by linarith
    have hk0 : (0 : ℝ) < k := by linarith
    have hkI : (k : ℝ) / X ∈ Set.Icc (0 : ℝ) 1 := ⟨by positivity, (div_le_one hXpos).mpr hkX⟩
    have hΛ : (Λ k : ℝ) / k ≤ 2 * (Real.log X / X) := by
      calc (Λ k : ℝ) / k ≤ Real.log k / k := vonMangoldt_div_le_log_div k
        _ ≤ Real.log X / (X / 2) :=
            div_le_div₀ (Real.log_nonneg (by linarith)) (Real.log_le_log hk0 hkX)
              (by positivity) hkX2
        _ = 2 * (Real.log X / X) := by field_simp
    have hc := BiScaleUncertainty.SieveMoments.abs_ramanujanLagCoefficient_le_totient q
      (k * n + h)
    rw [abs_mul, abs_mul, abs_of_nonneg (div_nonneg ArithmeticFunction.vonMangoldt_nonneg
      (Nat.cast_nonneg k))]
    have hlX : 0 ≤ 2 * (Real.log X / X) :=
      mul_nonneg zero_le_two (div_nonneg (Real.log_nonneg (by linarith)) hXpos.le)
    calc (Λ k : ℝ) / k * |ramanujanLagCoefficient q (k * n + h)| * |F (k / X)|
        ≤ 2 * (Real.log X / X) * q.totient * ℓ :=
          mul_le_mul (mul_le_mul hΛ hc (abs_nonneg _) hlX) (hFb _ hkI) (abs_nonneg _)
            (mul_nonneg hlX (Nat.cast_nonneg _))
      _ = q.totient * ℓ * (2 * (Real.log X / X)) := by ring
  have hlog0 : 0 ≤ Real.log X / X := div_nonneg (Real.log_nonneg (by linarith)) hXpos.le
  calc _ ≤ ∑ k ∈ Ioc (D * Y) ⌊X⌋₊, |(Λ k : ℝ) / k *
        ramanujanLagCoefficient q (k * n + h) * F (k / X)| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ Ioc (D * Y) ⌊X⌋₊, (q.totient * ℓ * (2 * (Real.log X / X)) : ℝ) := sum_le_sum hk
    _ = (Ioc (D * Y) ⌊X⌋₊).card * (q.totient * ℓ * (2 * (Real.log X / X))) := by
        rw [sum_const, nsmul_eq_mul]
    _ ≤ D * (q.totient * ℓ * (2 * (Real.log X / X))) :=
        mul_le_mul_of_nonneg_right hcard (by positivity)

/-- The exact grid decomposition of a weighted reading. -/
theorem weighted_reading_eq_grid {q : ℕ} {X : ℝ} (hX : 0 < X) {F : ℝ → ℝ} {D : ℕ} (hD : 1 ≤ D)
    (n h : ℕ) :
    (∑ k ∈ Icc 1 ⌊X⌋₊, (Λ k : ℝ) / k * ramanujanLagCoefficient q (k * n + h) * F (k / X)) =
      (∑ i ∈ range D, F (i / D) * affineRamanujanPrimeWindow q n h i (i + 1) ⌊X / D⌋₊) +
      (∑ i ∈ range D, ∑ k ∈ Ioc (i * ⌊X / D⌋₊) ((i + 1) * ⌊X / D⌋₊), (Λ k : ℝ) / k *
        ramanujanLagCoefficient q (k * n + h) * (F (k / X) - F (i / D))) +
      ∑ k ∈ Ioc (D * ⌊X / D⌋₊) ⌊X⌋₊, (Λ k : ℝ) / k *
        ramanujanLagCoefficient q (k * n + h) * F (k / X) := by
  have hD0 : (0 : ℝ) < D := by exact_mod_cast hD
  have hDYX : D * ⌊X / D⌋₊ ≤ ⌊X⌋₊ := Nat.le_floor (by
    push_cast
    calc (D : ℝ) * ⌊X / D⌋₊ ≤ D * (X / D) := by gcongr; exact Nat.floor_le (by positivity)
      _ = X := by field_simp)
  rw [show Icc 1 ⌊X⌋₊ = Ioc 0 ⌊X⌋₊ from rfl, ← sum_Ioc_consecutive _ (Nat.zero_le _) hDYX,
    sum_Ioc_zero_mul_eq_sum_windows, ← sum_add_distrib]
  congr 1
  refine sum_congr rfl fun i _ => ?_
  unfold affineRamanujanPrimeWindow
  rw [mul_sum, ← sum_add_distrib]
  refine sum_congr rfl fun k _ => ?_
  ring

/-- Arithmetic of the leftover budget. -/
private theorem leftover_budget_eq {D K ε : ℝ} (hD : 0 < D) (hK : 0 < K) :
    D * (K * (2 * (ε / (16 * D * K)))) = ε / 8 := by
  field_simp
  ring

/-- Arithmetic of the window budget. -/
private theorem window_budget_eq {D ℓ ε : ℝ} (hD : 0 < D) (hℓ : 0 ≤ ℓ) :
    D * (ℓ * (ε / (8 * D * (ℓ + 1)))) = ε / 8 * (ℓ / (ℓ + 1)) := by
  have : ℓ + 1 ≠ 0 := by linarith
  field_simp

/-- Budget for the `D/X` oscillation term. -/
private theorem dx_budget_le {P L K x ε : ℝ} (_hP : 0 ≤ P) (hPK : P ≤ K) (hL : 0 ≤ L)
    (hK : 0 < K) (hε : 0 < ε) (hx : x ≤ ε / (8 * K * (L + 1))) (hx0 : 0 ≤ x) :
    P * x * L ≤ ε / 8 := by
  have h1 : P * x * L ≤ K * (ε / (8 * K * (L + 1))) * L := by gcongr
  have h2 : K * (ε / (8 * K * (L + 1))) * L = ε / 8 * (L / (L + 1)) := by
    field_simp
  have h3 : L / (L + 1) ≤ 1 := (div_le_one (by linarith)).mpr (by linarith)
  rw [h2] at h1
  nlinarith

/-- **Weighted affine prime windows.** Lipschitz weights vanishing near zero preserve the
unit-average Ramanujan law, uniformly in both affine parameters and over real horizons. -/
theorem exists_weightedAffineRamanujanWindow_uniform {q : ℕ} (hq : 0 < q) {a ℓ : ℝ}
    (ha : 0 < a) (ha1 : a ≤ 1) {F : ℝ → ℝ} (hF0 : ∀ t, t ≤ a → F t = 0)
    (hFlip : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) 1, |F s - F t| ≤ ℓ * |s - t|)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X → ∀ n h : ℕ,
      |∑ k ∈ Icc 1 ⌊X⌋₊, (Λ k : ℝ) / k * ramanujanLagCoefficient q (k * n + h) * F (k / X) -
        ramanujanLagCoefficient q n * ramanujanLagCoefficient q h / q.totient *
          ∫ t in a..1, F t / t| ≤ ε := by
  have hA : (0 : ℝ) < q.totient := Nat.cast_pos.mpr (Nat.totient_pos.mpr hq)
  have hℓ : 0 ≤ ℓ := by
    have := hFlip 0 ⟨le_rfl, zero_le_one⟩ 1 ⟨zero_le_one, le_rfl⟩
    have h2 := abs_nonneg (F 0 - F 1)
    norm_num at this
    linarith
  have hFb (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) : |F t| ≤ ℓ := by
    have h := hFlip t ht a ⟨ha.le, ha1⟩
    rw [hF0 a le_rfl, sub_zero] at h
    have hd : |t - a| ≤ 1 := abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
    exact h.trans (by nlinarith)
  obtain ⟨C, hCdef⟩ : ∃ C : ℝ, C = mertensWindowConstant := ⟨_, rfl⟩
  have hC : 0 ≤ C := hCdef ▸ mertensWindowConstant_nonneg
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = (q.totient : ℝ) * ℓ + 1 := ⟨_, rfl⟩
  have hK0 : 0 < K := by rw [hK]; positivity
  have hPK : (q.totient : ℝ) * ℓ ≤ K := by rw [hK]; linarith
  have hP0 : 0 ≤ (q.totient : ℝ) * ℓ := mul_nonneg hA.le hℓ
  -- the grid size
  have hlogdiv : Tendsto (fun D : ℕ => (Real.log D + C) / D) atTop (𝓝 0) := by
    have h1 : Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝 0) := by
      simpa using Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
    have h2 : Tendsto (fun x : ℝ => C / x) atTop (𝓝 0) := by
      simpa [div_eq_mul_inv] using tendsto_inv_atTop_zero.const_mul C
    have h3 := (h1.add h2).comp tendsto_natCast_atTop_atTop
    rw [add_zero] at h3
    refine h3.congr' (Eventually.of_forall fun D => ?_)
    simp only [Function.comp, add_div]
  obtain ⟨D, hDev⟩ := eventually_atTop.mp
    ((hlogdiv.eventually (gt_mem_nhds (show (0 : ℝ) < ε / (8 * K) by positivity))).and
      (eventually_ge_atTop (⌈1 / a⌉₊ + 1)))
  obtain ⟨hDsmall, hDbig⟩ := hDev D le_rfl
  have hD1 : 1 ≤ D := by omega
  have hD0 : (0 : ℝ) < D := by exact_mod_cast hD1
  have hDa : 1 / (D : ℝ) ≤ a := by
    rw [div_le_iff₀ hD0]
    have h1 : 1 / a ≤ (⌈1 / a⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : (⌈1 / a⌉₊ : ℝ) ≤ D := by exact_mod_cast (by omega : ⌈1 / a⌉₊ ≤ D)
    have := h1.trans h2
    rw [div_le_iff₀ ha] at this
    linarith
  have hlogD0 : 0 ≤ Real.log D := Real.log_nonneg (by exact_mod_cast hD1)
  have hLD : K * ((Real.log D + C) / D) ≤ ε / 8 := by
    have := hDsmall.le
    rw [lt_div_iff₀ (by positivity)] at hDsmall
    linarith
  -- the unweighted windows
  obtain ⟨ε', hε'⟩ : ∃ ε' : ℝ, ε' = ε / (8 * D * (ℓ + 1)) := ⟨_, rfl⟩
  have hε'0 : 0 < ε' := by rw [hε']; positivity
  have hwin : ∀ᶠ Y : ℕ in atTop, ∀ i ∈ Ico 1 D, ∀ n h : ℕ,
      |affineRamanujanPrimeWindow q n h i (i + 1) Y -
        (Real.log ((i + 1 : ℕ) : ℝ) - Real.log i) * ramanujanLagCoefficient q n *
          ramanujanLagCoefficient q h / q.totient| ≤ ε' :=
    (Finset.eventually_all (Ico 1 D)).mpr fun i hi =>
      eventually_affineRamanujanPrimeWindow_uniform hq (mem_Ico.mp hi).1 (Nat.le_succ i) hε'0
  obtain ⟨Y₀, hY₀⟩ := eventually_atTop.mp hwin
  -- the horizon
  have hlogX : Tendsto (fun X : ℝ => Real.log X / X) atTop (𝓝 0) := by
    simpa using Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  have hDX : Tendsto (fun X : ℝ => (D : ℝ) / X) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using tendsto_inv_atTop_zero.const_mul (D : ℝ)
  obtain ⟨X₁, hX₁⟩ := eventually_atTop.mp
    ((hlogX.eventually (gt_mem_nhds (show (0 : ℝ) < ε / (16 * D * K) by positivity))).and
      (hDX.eventually (gt_mem_nhds (show (0 : ℝ) < ε / (8 * K * (Real.log D + C + 1)) by
        positivity))))
  refine ⟨max (max (2 * D) (D * (Y₀ + 1))) (max X₁ 1), fun X hX n h => ?_⟩
  have hX2D : 2 * (D : ℝ) ≤ X := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hX)
  have hXY : (D : ℝ) * (Y₀ + 1) ≤ X := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hX)
  have hX1 : X₁ ≤ X := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hX)
  have hX1' : 1 ≤ X := le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hX)
  have hXpos : 0 < X := by linarith
  obtain ⟨hlogXs, hDXs⟩ := hX₁ X hX1
  have hYY₀ : Y₀ + 1 ≤ ⌊X / D⌋₊ := Nat.le_floor (by
    push_cast
    rw [le_div_iff₀ hD0]
    linarith)
  have hY1 : 1 ≤ ⌊X / D⌋₊ := by omega
  obtain ⟨κ, hκ⟩ : ∃ κ : ℝ,
      κ = ramanujanLagCoefficient q n * ramanujanLagCoefficient q h / q.totient := ⟨_, rfl⟩
  have hκb : |κ| ≤ q.totient := by
    rw [hκ, abs_div, abs_mul, abs_of_pos hA, div_le_iff₀ hA]
    exact mul_le_mul (BiScaleUncertainty.SieveMoments.abs_ramanujanLagCoefficient_le_totient q n)
      (BiScaleUncertainty.SieveMoments.abs_ramanujanLagCoefficient_le_totient q h)
      (abs_nonneg _) hA.le
  -- (1) unweighted windows
  have hpart1 : |(∑ i ∈ range D, F (i / D) * affineRamanujanPrimeWindow q n h i (i + 1)
      ⌊X / D⌋₊) - κ * ∑ i ∈ range D, F (i / D) * (Real.log (i + 1) - Real.log i)| ≤ ε / 8 := by
    rw [mul_sum, ← sum_sub_distrib]
    refine (abs_sum_le_sum_abs _ _).trans ?_
    calc _ ≤ ∑ i ∈ range D, ℓ * ε' := by
          refine sum_le_sum fun i hi => ?_
          rcases Nat.eq_zero_or_pos i with rfl | hi0
          · simp [hF0 0 ha.le, mul_nonneg hℓ hε'0.le]
          · have hiD := mem_range.mp hi
            have hb := hY₀ ⌊X / D⌋₊ (by omega) i (mem_Ico.mpr ⟨hi0, hiD⟩) n h
            have hFi : |F (i / D)| ≤ ℓ :=
              hFb _ ⟨by positivity, (div_le_one hD0).mpr (by exact_mod_cast hiD.le)⟩
            have heq : F (i / D) * affineRamanujanPrimeWindow q n h i (i + 1) ⌊X / D⌋₊ -
                κ * (F (i / D) * (Real.log (i + 1) - Real.log i)) =
                F (i / D) * (affineRamanujanPrimeWindow q n h i (i + 1) ⌊X / D⌋₊ -
                  (Real.log ((i + 1 : ℕ) : ℝ) - Real.log i) * ramanujanLagCoefficient q n *
                    ramanujanLagCoefficient q h / q.totient) := by
              rw [hκ]; push_cast; ring
            rw [heq, abs_mul]
            exact mul_le_mul hFi hb (abs_nonneg _) hℓ
      _ = D * (ℓ * ε') := by rw [sum_const, card_range, nsmul_eq_mul]
      _ ≤ ε / 8 := by
          have he : (D : ℝ) * (ℓ * ε') = ε / 8 * (ℓ / (ℓ + 1)) := by
            rw [hε']; exact window_budget_eq hD0 hℓ
          rw [he]
          have : ℓ / (ℓ + 1) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith)
          nlinarith
  -- (2) Riemann sum
  have hpart2 : |κ * ∑ i ∈ range D, F (i / D) * (Real.log (i + 1) - Real.log i) -
      κ * ∫ t in a..1, F t / t| ≤ ε / 8 := by
    rw [← mul_sub, abs_mul]
    have hR := abs_sum_grid_sub_integral_le ha1 hF0 hFlip hD1 hDa
    have h1 : Real.log D / D ≤ (Real.log D + C) / D :=
      div_le_div_of_nonneg_right (by linarith) hD0.le
    have h2 : 0 ≤ Real.log D / D := div_nonneg hlogD0 hD0.le
    calc _ ≤ (q.totient : ℝ) * (ℓ * Real.log D / D) := mul_le_mul hκb hR (abs_nonneg _) hA.le
      _ = ((q.totient : ℝ) * ℓ) * (Real.log D / D) := by ring
      _ ≤ K * ((Real.log D + C) / D) := mul_le_mul hPK h1 h2 hK0.le
      _ ≤ ε / 8 := hLD
  -- (3) oscillation
  have hpart3 := abs_sum_window_oscillation_le (q := q) ha hF0 hFlip hℓ hXpos hD1 hDa hY1 n h
  rw [← hCdef] at hpart3
  have hpart3' : (q.totient : ℝ) * ℓ * (1 / D + D / X) * (Real.log D + C) ≤ ε / 4 := by
    have hL0 : 0 ≤ Real.log D + C := by linarith
    have h1 : (q.totient : ℝ) * ℓ * (1 / D) * (Real.log D + C) ≤ ε / 8 := by
      have heq : (q.totient : ℝ) * ℓ * (1 / D) * (Real.log D + C) =
          ((q.totient : ℝ) * ℓ) * ((Real.log D + C) / D) := by ring
      rw [heq]
      exact (mul_le_mul_of_nonneg_right hPK (div_nonneg hL0 hD0.le)).trans hLD
    have h2 := dx_budget_le hP0 hPK hL0 hK0 hε hDXs.le (by positivity : (0 : ℝ) ≤ D / X)
    have heq : (q.totient : ℝ) * ℓ * (1 / D + D / X) * (Real.log D + C) =
        (q.totient : ℝ) * ℓ * (1 / D) * (Real.log D + C) +
          (q.totient : ℝ) * ℓ * (D / X) * (Real.log D + C) := by ring
    rw [heq]
    linarith
  -- (4) leftover
  have hpart4 := abs_sum_leftover_le (q := q) hFb hℓ hD1 hX2D n h
  have hpart4' : (D : ℝ) * ((q.totient : ℝ) * ℓ * (2 * (Real.log X / X))) ≤ ε / 8 := by
    have hl : Real.log X / X ≤ ε / (16 * D * K) := hlogXs.le
    have hl0 : 0 ≤ Real.log X / X := div_nonneg (Real.log_nonneg hX1') hXpos.le
    calc (D : ℝ) * ((q.totient : ℝ) * ℓ * (2 * (Real.log X / X)))
        ≤ D * (K * (2 * (ε / (16 * D * K)))) := by
          gcongr
      _ = ε / 8 := leftover_budget_eq hD0 hK0
  rw [weighted_reading_eq_grid hXpos hD1 n h, ← hκ]
  have hre : (∑ i ∈ range D, F (i / D) * affineRamanujanPrimeWindow q n h i (i + 1) ⌊X / D⌋₊) +
      (∑ i ∈ range D, ∑ k ∈ Ioc (i * ⌊X / D⌋₊) ((i + 1) * ⌊X / D⌋₊), (Λ k : ℝ) / k *
        ramanujanLagCoefficient q (k * n + h) * (F (k / X) - F (i / D))) +
      (∑ k ∈ Ioc (D * ⌊X / D⌋₊) ⌊X⌋₊, (Λ k : ℝ) / k *
        ramanujanLagCoefficient q (k * n + h) * F (k / X)) - κ * ∫ t in a..1, F t / t =
      ((∑ i ∈ range D, F (i / D) * affineRamanujanPrimeWindow q n h i (i + 1) ⌊X / D⌋₊) -
        κ * ∑ i ∈ range D, F (i / D) * (Real.log (i + 1) - Real.log i)) +
      (κ * ∑ i ∈ range D, F (i / D) * (Real.log (i + 1) - Real.log i) -
        κ * ∫ t in a..1, F t / t) +
      (∑ i ∈ range D, ∑ k ∈ Ioc (i * ⌊X / D⌋₊) ((i + 1) * ⌊X / D⌋₊), (Λ k : ℝ) / k *
        ramanujanLagCoefficient q (k * n + h) * (F (k / X) - F (i / D))) +
      (∑ k ∈ Ioc (D * ⌊X / D⌋₊) ⌊X⌋₊, (Λ k : ℝ) / k *
        ramanujanLagCoefficient q (k * n + h) * F (k / X)) := by ring
  rw [hre]
  generalize hT1 : (∑ i ∈ range D, F (i / D) * affineRamanujanPrimeWindow q n h i (i + 1)
    ⌊X / D⌋₊) - κ * ∑ i ∈ range D, F (i / D) * (Real.log (i + 1) - Real.log i) = T1 at hpart1 ⊢
  generalize hT2 : κ * ∑ i ∈ range D, F (i / D) * (Real.log (i + 1) - Real.log i) -
    κ * ∫ t in a..1, F t / t = T2 at hpart2 ⊢
  generalize hT3 : (∑ i ∈ range D, ∑ k ∈ Ioc (i * ⌊X / D⌋₊) ((i + 1) * ⌊X / D⌋₊), (Λ k : ℝ) / k *
    ramanujanLagCoefficient q (k * n + h) * (F (k / X) - F (i / D))) = T3 at hpart3 ⊢
  generalize hT4 : (∑ k ∈ Ioc (D * ⌊X / D⌋₊) ⌊X⌋₊, (Λ k : ℝ) / k *
    ramanujanLagCoefficient q (k * n + h) * F (k / X)) = T4 at hpart4 ⊢
  have h12 := abs_add_le T1 T2
  have h123 := abs_add_le (T1 + T2) T3
  have h1234 := abs_add_le (T1 + T2 + T3) T4
  linarith [hpart1, hpart2, hpart3, hpart3', hpart4, hpart4']

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory
