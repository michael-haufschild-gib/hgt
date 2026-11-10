import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.SumsOverTheDegreePointsAreRiemannSums

/-!
# The packets on the degree points carry Weil's archimedean form

A packet `f ∈ C²_c(ℝ)` in the logarithmic coordinate is sampled on the degree points at the scale
`N`: the degree point `n` carries `f(log(n/N))` and the mass `1/n`. In the unitary normalization
the jets pair `m ≠ n` by `½(1/|m − n| + 1/(m + n))/√(mn)`, and the counterterm at `n` is the mass
times `log(n/2π)`, the logarithm of the density of the degree points over `2π`.

For a packet supported in `[log 3, log K]`, on the window `N < n ≤ (1 + 3K)N`:

* **The rates out of the window** (`abs_highTail_sub_le`, `lowTail_bounds`): the rate of the
  jumps from `n` beyond `M` is `Ω(log(M/n))` up to `ω(log(M/n))/M`, and the rate of the jumps
  from `n` down to `[1, N]` is `Ω(log(n/N))` up to `Ω(log n)`; `Ω(y) = ∫_y^∞ ω`. Both are
  comparisons of a monotone sum with the increments of its primitive.
* **Lévy–Khintchine on the window** (`degreeForm_eq`): the pairing with its counterterm is the
  masses against `levyRow n − log(n/2π)`, minus the masses against the two rates out of the
  window, minus half the Dirichlet sum of the jets inside the window.
* **The limit** (`tendsto_degreeForm`): the first term tends to `−A(0)·∫f²` by the row theorem
  of the degree points; the other three are Riemann sums; their limits add up to the jump form
  of `f` by its splitting into a window and its tails. So the pairing of the jets with the
  counterterm of the degree points tends to minus the archimedean part of Weil's functional of
  `f` without the pole.

* **A counterterm of the scale alone** (`tendsto_degreePairing_sub_scale_counterterm`,
  `integral_sq_mul_translate`): with `log(N/2π)` at every point of the window, a counterterm that
  does not depend on the degree point, the limit is Weil's form plus `∫ f(u)² u du`, the first
  moment of the mass, which moves by `s·∫f²` when the packet is translated by `s`.
* **No counterterm** (`tendsto_degreePairing_div_log`): the pairing of the jets divided by
  `log N` tends to `∫ f²`. Leaving the diagonal out is not a finite part: it differs from Weil's
  form by the mass times `log N`.

No other counterterm enters, and nothing is assumed on the packet beyond `C²` and the position of
its support above the scale. Weil's functional is invariant under translation of the packet, so
the support condition fixes the scale and not the packet.
-/

open Finset Filter Topology MeasureTheory
open Zeta23

noncomputable section

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

local notation "ω" => _root_.RHTower.archLevyDensity
local notation "Ω" => _root_.RHTower.WeilLevyPoleGauss.archLevyAntideriv

/-! ### The primitive of the Lévy density -/

theorem archLevyAntideriv_anti {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) : Ω b ≤ Ω a := by
  rcases eq_or_lt_of_le hab with rfl | h
  · exact le_rfl
  · have hstep := (archLevyAntideriv_step ha (sub_pos.mpr h)).1
    rw [add_sub_cancel] at hstep
    have hω := _root_.RHTower.archLevyDensity_pos (ha.trans h)
    nlinarith [mul_pos hω (sub_pos.mpr h)]

theorem levyWeight_nonneg (m n : ℕ) : 0 ≤ levyWeight m n := by
  unfold levyWeight jetKernel
  positivity

/-- `1/(t + 1) ≤ log((t + 1)/t) ≤ 1/t`. -/
theorem log_succ_div_bounds {t : ℝ} (ht : 0 < t) :
    1 / (t + 1) ≤ Real.log ((t + 1) / t) ∧ Real.log ((t + 1) / t) ≤ 1 / t := by
  have hpos : 0 < (t + 1) / t := by positivity
  have e : t + 1 - t = 1 := by ring
  constructor
  · have h := Real.one_sub_inv_le_log_of_pos hpos
    rw [inv_div, one_sub_div (by positivity), e] at h
    exact h
  · have h := Real.log_le_sub_one_of_pos hpos
    rw [div_sub_one ht.ne', e] at h
    exact h

/-- One step of the primitive above `n`, against the rate at either end. -/
theorem archLevyAntideriv_log_step {n t : ℝ} (hn : 0 < n) (hnt : n < t) :
    ω (Real.log ((t + 1) / n)) / (t + 1) ≤
        Ω (Real.log (t / n)) - Ω (Real.log ((t + 1) / n)) ∧
      Ω (Real.log (t / n)) - Ω (Real.log ((t + 1) / n)) ≤ ω (Real.log (t / n)) / t := by
  have ht : 0 < t := hn.trans hnt
  have ha : 0 < Real.log (t / n) := Real.log_pos ((one_lt_div hn).mpr hnt)
  have ha1 : 0 < Real.log ((t + 1) / n) := Real.log_pos ((one_lt_div hn).mpr (by linarith))
  obtain ⟨hδ1, hδ2⟩ := log_succ_div_bounds ht
  have hδ : 0 < Real.log ((t + 1) / t) := lt_of_lt_of_le (by positivity) hδ1
  have hadd : Real.log (t / n) + Real.log ((t + 1) / t) = Real.log ((t + 1) / n) := by
    rw [← Real.log_mul (by positivity) (by positivity)]
    congr 1
    field_simp
  obtain ⟨h1, h2⟩ := archLevyAntideriv_step ha hδ
  rw [hadd] at h1 h2
  have hω1 := (_root_.RHTower.archLevyDensity_pos ha1).le
  have hω0 := (_root_.RHTower.archLevyDensity_pos ha).le
  constructor
  · calc ω (Real.log ((t + 1) / n)) / (t + 1)
        = ω (Real.log ((t + 1) / n)) * (1 / (t + 1)) := by ring
      _ ≤ ω (Real.log ((t + 1) / n)) * Real.log ((t + 1) / t) :=
          mul_le_mul_of_nonneg_left hδ1 hω1
      _ ≤ Ω (Real.log (t / n)) - Ω (Real.log ((t + 1) / n)) := h1
  · calc Ω (Real.log (t / n)) - Ω (Real.log ((t + 1) / n))
        ≤ ω (Real.log (t / n)) * Real.log ((t + 1) / t) := h2
      _ ≤ ω (Real.log (t / n)) * (1 / t) := mul_le_mul_of_nonneg_left hδ2 hω0
      _ = ω (Real.log (t / n)) / t := by ring

/-! ### The rate beyond the window -/

/-- The rate of the jumps from `n` to the degree points beyond `M`. -/
def highTail (M n : ℕ) : ℝ := ∑' j : ℕ, levyWeight (M + j + 1) n

/-- `Ω(log((M + j)/n))`, the rate of the jumps from `n` beyond `M + j` in the continuum. -/
def highPot (M n j : ℕ) : ℝ := Ω (Real.log (((M + j : ℕ) : ℝ) / n))

theorem levyWeight_of_gt' {m n : ℕ} (hn : 1 ≤ n) (h : n < m) :
    levyWeight m n = ω (Real.log ((m : ℝ) / n)) / m := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have h' : (n : ℝ) < m := by exact_mod_cast h
  rw [levyWeight_eq_archLevyDensity (by omega) hn (by omega),
    abs_of_pos (Real.log_pos ((one_lt_div hn').mpr h'))]

section HighTail

variable {n M : ℕ}

theorem highPot_pos (hn : 1 ≤ n) (hnM : n < M) (j : ℕ) : 0 < highPot M n j := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have h1 : (n : ℝ) < ((M + j : ℕ) : ℝ) := by exact_mod_cast (by omega : n < M + j)
  exact _root_.RHTower.WeilLevyPoleGauss.archLevyAntideriv_pos
    (Real.log_pos ((one_lt_div hn').mpr h1))

theorem highTail_term (hn : 1 ≤ n) (hnM : n < M) (j : ℕ) :
    highPot M n (j + 1) - highPot M n (j + 1 + 1) ≤ levyWeight (M + j + 1) n ∧
      levyWeight (M + j + 1) n ≤ highPot M n j - highPot M n (j + 1) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have h1 : (n : ℝ) < ((M + j : ℕ) : ℝ) := by exact_mod_cast (by omega : n < M + j)
  have h2 : (n : ℝ) < ((M + (j + 1) : ℕ) : ℝ) := by
    exact_mod_cast (by omega : n < M + (j + 1))
  have e1 : ((M + (j + 1) : ℕ) : ℝ) = ((M + j : ℕ) : ℝ) + 1 := by
    push_cast
    ring
  have e2 : ((M + (j + 1 + 1) : ℕ) : ℝ) = ((M + (j + 1) : ℕ) : ℝ) + 1 := by
    push_cast
    ring
  have e3 : ((M + j + 1 : ℕ) : ℝ) = ((M + (j + 1) : ℕ) : ℝ) := by
    push_cast
    ring
  rw [levyWeight_of_gt' hn (by omega : n < M + j + 1), e3]
  unfold highPot
  constructor
  · have h := (archLevyAntideriv_log_step hn' h2).2
    rw [← e2] at h
    exact h
  · have h := (archLevyAntideriv_log_step hn' h1).1
    rw [← e1] at h
    exact h

theorem sum_highTail_le (hn : 1 ≤ n) (hnM : n < M) (J : ℕ) :
    ∑ j ∈ range J, levyWeight (M + j + 1) n ≤ highPot M n 0 := by
  have hsum := Finset.sum_range_sub' (fun j => highPot M n j) J
  have hle := Finset.sum_le_sum fun j (_ : j ∈ range J) => (highTail_term hn hnM j).2
  rw [hsum] at hle
  linarith [highPot_pos hn hnM J]

theorem summable_highTail (hn : 1 ≤ n) (hnM : n < M) :
    Summable fun j : ℕ => levyWeight (M + j + 1) n :=
  summable_of_sum_range_le (fun _ => levyWeight_nonneg _ _) (sum_highTail_le hn hnM)

theorem highTail_le (hn : 1 ≤ n) (hnM : n < M) : highTail M n ≤ highPot M n 0 :=
  Real.tsum_le_of_sum_range_le (fun _ => levyWeight_nonneg _ _) (sum_highTail_le hn hnM)

theorem le_highTail (hn : 1 ≤ n) (hnM : n < M) : highPot M n 1 ≤ highTail M n := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have h0 : Tendsto (fun J : ℕ => highPot M n (J + 1)) atTop (𝓝 0) := by
    have hJ : Tendsto (fun J : ℕ => Real.log (((M + (J + 1) : ℕ) : ℝ) / n)) atTop atTop :=
      Real.tendsto_log_atTop.comp ((tendsto_natCast_atTop_atTop.comp
        (tendsto_atTop_mono (fun J => (by omega : J ≤ M + (J + 1))) tendsto_id)).atTop_div_const
          hn')
    exact _root_.RHTower.WeilLevyCoshCrossover.tendsto_archLevyAntideriv_atTop.comp hJ
  have hlim : Tendsto (fun J : ℕ => highPot M n 1 - highPot M n (J + 1)) atTop
      (𝓝 (highPot M n 1)) := by
    have h := (tendsto_const_nhds (x := highPot M n 1) (f := (atTop : Filter ℕ))).sub h0
    rwa [sub_zero] at h
  refine le_of_tendsto' hlim fun J => ?_
  have hsum := Finset.sum_range_sub' (fun j => highPot M n (j + 1)) J
  have hle := Finset.sum_le_sum fun j (_ : j ∈ range J) => (highTail_term hn hnM j).1
  rw [hsum] at hle
  exact hle.trans ((summable_highTail hn hnM).sum_le_tsum _ fun j _ => levyWeight_nonneg _ _)

/-- **The rate beyond the window** is `Ω(log(M/n))` up to `ω(log(M/n))/M`. -/
theorem abs_highTail_sub_le (hn : 1 ≤ n) (hnM : n < M) :
    |highTail M n - Ω (Real.log ((M : ℝ) / n))| ≤ ω (Real.log ((M : ℝ) / n)) / M := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hM : (n : ℝ) < M := by exact_mod_cast hnM
  have h0 : highPot M n 0 = Ω (Real.log ((M : ℝ) / n)) := by
    unfold highPot
    rw [Nat.add_zero]
  have h1 : highPot M n 1 = Ω (Real.log (((M : ℝ) + 1) / n)) := by
    unfold highPot
    push_cast
    rfl
  have hstep := (archLevyAntideriv_log_step hn' hM).2
  have hup := highTail_le hn hnM
  have hlo := le_highTail hn hnM
  rw [h0] at hup
  rw [h1] at hlo
  have hω : 0 ≤ ω (Real.log ((M : ℝ) / n)) / M :=
    div_nonneg (_root_.RHTower.archLevyDensity_pos
      (Real.log_pos ((one_lt_div hn').mpr hM))).le (by positivity)
  rw [abs_le]
  constructor <;> linarith

end HighTail

/-! ### The rate below the window -/

theorem mul_one_sub_pow_four_le {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ^ 2 ≤ 1 / 3) :
    a * (1 - a ^ 4) ≤ b * (1 - b ^ 4) := by
  have hb0 : 0 ≤ b := ha.trans hab
  have hb4 : b ^ 4 ≤ 1 / 9 := by
    calc b ^ 4 = (b ^ 2) ^ 2 := by ring
      _ ≤ (1 / 3) ^ 2 := pow_le_pow_left₀ (sq_nonneg b) hb 2
      _ = 1 / 9 := by norm_num
  have h1 : a ^ 4 ≤ b ^ 4 := pow_le_pow_left₀ ha hab 4
  have h2 : b * a ^ 3 ≤ b ^ 4 := by
    calc b * a ^ 3 ≤ b * b ^ 3 := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ha hab 3) hb0
      _ = b ^ 4 := by ring
  have h3 : b ^ 2 * a ^ 2 ≤ b ^ 4 := by
    calc b ^ 2 * a ^ 2 ≤ b ^ 2 * b ^ 2 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ha hab 2) (sq_nonneg b)
      _ = b ^ 4 := by ring
  have h4 : b ^ 3 * a ≤ b ^ 4 := by
    calc b ^ 3 * a ≤ b ^ 3 * b := mul_le_mul_of_nonneg_left hab (pow_nonneg hb0 3)
      _ = b ^ 4 := by ring
  have key : b * (1 - b ^ 4) - a * (1 - a ^ 4) =
      (b - a) * (1 - (b ^ 4 + b ^ 3 * a + b ^ 2 * a ^ 2 + b * a ^ 3 + a ^ 4)) := by ring
  have hnn : 0 ≤ (b - a) * (1 - (b ^ 4 + b ^ 3 * a + b ^ 2 * a ^ 2 + b * a ^ 3 + a ^ 4)) :=
    mul_nonneg (by linarith) (by linarith)
  linarith

/-- The rate of the jumps from `n` down to `r`, per unit of `r`, in the variable
`c = √(r/n)`: `1/(c(1 − c⁴)n)`. -/
theorem lowRate_eq {n r c : ℝ} (hn : 0 < n) (hr : 0 < r) (hc : 0 < c) (hrc : r / n = c ^ 2)
    (hc4 : c ^ 4 < 1) :
    ω (Real.log n - Real.log r) / r = 1 / (c * (1 - c ^ 4) * n) := by
  have hsq : Real.sqrt (r / n) = c := by
    rw [hrc]
    exact Real.sqrt_sq hc.le
  have hr' : r = c ^ 2 * n := (div_eq_iff hn.ne').mp hrc
  have h2 : (1 : ℝ) - c ^ 4 ≠ 0 := (sub_pos.mpr hc4).ne'
  have e : (c ^ 2) ^ 2 = c ^ 4 := by ring
  rw [← Real.log_div hn.ne' hr.ne', archLevyDensity_log (by positivity), inv_div, hsq, hrc, e,
    hr']
  field_simp

/-- **Below a third of `n` the rate per unit is decreasing.** -/
theorem lowRate_anti {n s t : ℝ} (hn : 0 < n) (hs : 0 < s) (hst : s ≤ t) (ht : 3 * t ≤ n) :
    ω (Real.log n - Real.log t) / t ≤ ω (Real.log n - Real.log s) / s := by
  have ht0 : 0 < t := hs.trans_le hst
  obtain ⟨a, ha, has⟩ : ∃ a : ℝ, 0 < a ∧ s / n = a ^ 2 :=
    ⟨Real.sqrt (s / n), Real.sqrt_pos.mpr (by positivity), (Real.sq_sqrt (by positivity)).symm⟩
  obtain ⟨b, hb, hbt⟩ : ∃ b : ℝ, 0 < b ∧ t / n = b ^ 2 :=
    ⟨Real.sqrt (t / n), Real.sqrt_pos.mpr (by positivity), (Real.sq_sqrt (by positivity)).symm⟩
  have hsq : a ^ 2 ≤ b ^ 2 := by
    rw [← has, ← hbt]
    exact div_le_div_of_nonneg_right hst hn.le
  have hab : a ≤ b := by
    by_contra h
    have := pow_lt_pow_left₀ (not_le.mp h) hb.le two_ne_zero
    linarith
  have hb2 : b ^ 2 ≤ 1 / 3 := by
    rw [← hbt, div_le_div_iff₀ hn (by norm_num : (0 : ℝ) < 3)]
    linarith
  have hb4 : b ^ 4 < 1 := by
    have h9 : b ^ 4 ≤ 1 / 9 := by
      calc b ^ 4 = (b ^ 2) ^ 2 := by ring
        _ ≤ (1 / 3) ^ 2 := pow_le_pow_left₀ (sq_nonneg b) hb2 2
        _ = 1 / 9 := by norm_num
    linarith
  have ha4 : a ^ 4 < 1 := lt_of_le_of_lt (pow_le_pow_left₀ ha.le hab 4) hb4
  have key := mul_one_sub_pow_four_le ha.le hab hb2
  rw [lowRate_eq hn ht0 hb hbt hb4, lowRate_eq hn hs ha has ha4]
  exact one_div_le_one_div_of_le (mul_pos (mul_pos ha (sub_pos.mpr ha4)) hn)
    (mul_le_mul_of_nonneg_right key hn.le)

theorem hasDerivAt_lowPot {n x : ℝ} (hx : 0 < x) (hxn : x < n) :
    HasDerivAt (fun t => Ω (Real.log n - Real.log t)) (ω (Real.log n - Real.log x) / x) x := by
  have hy : 0 < Real.log n - Real.log x := sub_pos.mpr (Real.log_lt_log hx hxn)
  have hin : HasDerivAt (fun t => Real.log n - Real.log t) (0 - x⁻¹) x :=
    (hasDerivAt_const x (Real.log n)).sub (Real.hasDerivAt_log hx.ne')
  have h := (_root_.RHTower.WeilLevyPoleGauss.hasDerivAt_archLevyAntideriv hy).comp x hin
  refine h.congr_deriv ?_
  rw [div_eq_mul_inv]
  ring

/-- One step of the primitive below a third of `n`, against the rate at either end. -/
theorem lowStep {n t : ℝ} (ht : 0 < t) (htn : 3 * (t + 1) ≤ n) :
    ω (Real.log n - Real.log (t + 1)) / (t + 1) ≤
        Ω (Real.log n - Real.log (t + 1)) - Ω (Real.log n - Real.log t) ∧
      Ω (Real.log n - Real.log (t + 1)) - Ω (Real.log n - Real.log t) ≤
        ω (Real.log n - Real.log t) / t := by
  have hn : 0 < n := by linarith
  have hlt : t < t + 1 := by linarith
  have hd : ∀ x ∈ Set.Icc t (t + 1), HasDerivAt (fun y => Ω (Real.log n - Real.log y))
      (ω (Real.log n - Real.log x) / x) x := fun x hx =>
    hasDerivAt_lowPot (ht.trans_le hx.1) (by linarith [hx.2])
  have hF : ContinuousOn (fun y => Ω (Real.log n - Real.log y)) (Set.Icc t (t + 1)) :=
    fun x hx => (hd x hx).continuousAt.continuousWithinAt
  have h1 := mul_le_sub_of_hasDerivAt (F := fun y => Ω (Real.log n - Real.log y))
    (f := fun x => ω (Real.log n - Real.log x) / x) hlt hF
    (fun x hx => hd x ⟨hx.1.le, hx.2.le⟩)
    (fun x hx => lowRate_anti hn (ht.trans hx.1) hx.2.le htn)
  have h2 := sub_le_mul_of_hasDerivAt (F := fun y => Ω (Real.log n - Real.log y))
    (f := fun x => ω (Real.log n - Real.log x) / x) hlt hF
    (fun x hx => hd x ⟨hx.1.le, hx.2.le⟩)
    (fun x hx => lowRate_anti hn ht hx.1.le (by linarith [hx.2]))
  rw [add_sub_cancel_left, mul_one] at h1 h2
  exact ⟨h1, h2⟩

/-- The rate of the jumps from `n` to the degree points up to `N`. -/
def lowTail (N n : ℕ) : ℝ := ∑ m ∈ Ioc 0 N, levyWeight m n

theorem levyWeight_of_lt' {m n : ℕ} (hm : 1 ≤ m) (h : m < n) :
    levyWeight m n = ω (Real.log n - Real.log m) / m := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hn' : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have h' : (m : ℝ) < n := by exact_mod_cast h
  rw [levyWeight_eq_archLevyDensity hm (by omega) (by omega), Real.log_div hm'.ne' hn'.ne',
    abs_of_neg (sub_neg.mpr (Real.log_lt_log hm' h')), neg_sub]

/-- **The rate below the window** is `Ω(log(n/N))` up to `Ω(log n)`. -/
theorem lowTail_bounds {N n : ℕ} (hN : 1 ≤ N) (hn : 3 * N ≤ n) :
    Ω (Real.log ((n : ℝ) / N)) - Ω (Real.log n) ≤ lowTail N n ∧
      lowTail N n ≤ Ω (Real.log ((n : ℝ) / N)) + Ω (Real.log n) := by
  obtain ⟨N', rfl⟩ : ∃ N', N = N' + 1 := ⟨N - 1, by omega⟩
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have h3 : (3 : ℝ) * ((N' : ℝ) + 1) ≤ n := by exact_mod_cast hn
  -- the potential and the rate at the integers
  obtain ⟨G, hG⟩ : ∃ G : ℕ → ℝ, ∀ k, G k = Ω (Real.log n - Real.log ((k : ℝ) + 1)) :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨φ, hφ⟩ : ∃ φ : ℕ → ℝ,
      ∀ k, φ k = ω (Real.log n - Real.log ((k : ℝ) + 1)) / ((k : ℝ) + 1) := ⟨_, fun _ => rfl⟩
  have hterm : ∀ k : ℕ, k < N' + 1 → levyWeight (k + 1) n = φ k := by
    intro k hk
    rw [levyWeight_of_lt' (by omega) (by omega), hφ]
    push_cast
    rfl
  have hstep : ∀ k : ℕ, k < N' → φ (k + 1) ≤ G (k + 1) - G k ∧ G (k + 1) - G k ≤ φ k := by
    intro k hk
    have hk' : (k : ℝ) + 1 ≤ N' := by exact_mod_cast hk
    have h := lowStep (n := n) (t := (k : ℝ) + 1) (by positivity) (by linarith)
    rw [hG, hG, hφ, hφ]
    push_cast
    exact h
  -- the two ends of the telescoping sum
  have hGN : G N' = Ω (Real.log ((n : ℝ) / ((N' + 1 : ℕ) : ℝ))) := by
    rw [hG, Real.log_div hn0.ne' (by positivity)]
    push_cast
    rfl
  have hG0 : G 0 = Ω (Real.log n) := by
    rw [hG, Nat.cast_zero, zero_add, Real.log_one, sub_zero]
  have hφ0 : φ 0 ≤ 2 * G 0 := by
    have hd : ∀ x ∈ Set.Icc (1 / 2 : ℝ) 1, HasDerivAt (fun y => Ω (Real.log n - Real.log y))
        (ω (Real.log n - Real.log x) / x) x := fun x hx =>
      hasDerivAt_lowPot (by linarith [hx.1]) (by linarith [hx.2])
    have h := mul_le_sub_of_hasDerivAt (F := fun y => Ω (Real.log n - Real.log y))
      (f := fun x => ω (Real.log n - Real.log x) / x) (by norm_num : (1 / 2 : ℝ) < 1)
      (fun x hx => (hd x hx).continuousAt.continuousWithinAt)
      (fun x hx => hd x ⟨hx.1.le, hx.2.le⟩)
      (fun x hx => lowRate_anti hn0 (by linarith [hx.1]) hx.2.le (by linarith))
    have hpos : 0 < Ω (Real.log n - Real.log (1 / 2)) :=
      _root_.RHTower.WeilLevyPoleGauss.archLevyAntideriv_pos
        (sub_pos.mpr (Real.log_lt_log (by norm_num) (by linarith)))
    rw [hφ, hG0, Nat.cast_zero, zero_add]
    simp only [Real.log_one, sub_zero, div_one] at h ⊢
    linarith
  have hsum := Finset.sum_range_sub G N'
  have hs := sum_Ioc_add_eq_sum_range (fun m => levyWeight m n) 0 (N' + 1)
  simp only [zero_add] at hs
  rw [lowTail, hs, Finset.sum_congr rfl fun k hk => hterm k (Finset.mem_range.mp hk)]
  constructor
  · rw [Finset.sum_range_succ]
    have hle := Finset.sum_le_sum fun k (hk : k ∈ range N') =>
      (hstep k (Finset.mem_range.mp hk)).2
    rw [hsum] at hle
    have hlast : 0 ≤ φ N' := by
      rw [← hterm N' (by omega)]
      exact levyWeight_nonneg _ _
    rw [← hGN, ← hG0]
    linarith
  · rw [Finset.sum_range_succ']
    have hle := Finset.sum_le_sum fun k (hk : k ∈ range N') =>
      (hstep k (Finset.mem_range.mp hk)).1
    rw [hsum] at hle
    rw [← hGN, ← hG0]
    linarith

/-! ### The rates inside a window -/

/-- **The rates inside a window** are the total rate minus the rates out of the window. -/
theorem sum_erase_window_levyWeight {N M n : ℕ} (hNn : N < n) (hnM : n ≤ M) :
    ∑ m ∈ (Ioc N M).erase n, levyWeight m n = levyRow n - lowTail N n - highTail M n := by
  have hn : 1 ≤ n := by omega
  have hs := (hasSum_levyWeight_above hn).summable
  have h1 := hs.sum_add_tsum_nat_add (M - n)
  have h2 : ∑' j : ℕ, levyWeight (n + (j + (M - n)) + 1) n = highTail M n :=
    tsum_congr fun j => by
      have e : n + (j + (M - n)) + 1 = M + j + 1 := by omega
      rw [e]
  have h3 := sum_Ioc_add_eq_sum_range (fun m => levyWeight m n) n (M - n)
  rw [Nat.add_sub_of_le hnM] at h3
  have hlow : Ico 1 n = Ioc 0 N ∪ Ioo N n := by
    ext k
    simp only [mem_Ico, mem_union, mem_Ioc, mem_Ioo]
    omega
  have hdl : Disjoint (Ioc 0 N) (Ioo N n) := by
    rw [Finset.disjoint_left]
    intro k hk hk'
    simp only [mem_Ioc, mem_Ioo] at hk hk'
    omega
  have hwin : (Ioc N M).erase n = Ioo N n ∪ Ioc n M := by
    ext k
    simp only [mem_erase, mem_Ioc, mem_union, mem_Ioo]
    omega
  have hdw : Disjoint (Ioo N n) (Ioc n M) := by
    rw [Finset.disjoint_left]
    intro k hk hk'
    simp only [mem_Ioc, mem_Ioo] at hk hk'
    omega
  rw [hwin, Finset.sum_union hdw, levyRow, hlow, Finset.sum_union hdl, lowTail, ← h1, h2, h3]
  ring

/-! ### Packets on the degree points -/

/-- The sample of the packet at the degree point `n`, at the scale `N`. -/
def degreeSample (f : ℝ → ℝ) (N n : ℕ) : ℝ := f (Real.log ((n : ℝ) / N))

/-- The pairing of the jets on the degree points of the window `N < n ≤ (1 + L)N`, in the unitary
normalization. -/
def degreePairing (f : ℝ → ℝ) (L N : ℕ) : ℝ :=
  ∑ n ∈ Ioc N (N + L * N), ∑ m ∈ (Ioc N (N + L * N)).erase n,
    degreeSample f N m * degreeSample f N n * levyKernel m n

/-- The pairing with the counterterm of the degree points: the mass at `n` times `log(n/2π)`. -/
def degreeForm (f : ℝ → ℝ) (L N : ℕ) : ℝ :=
  degreePairing f L N -
    ∑ n ∈ Ioc N (N + L * N), degreeSample f N n ^ 2 / n * Real.log ((n : ℝ) / (2 * Real.pi))

/-- A jump of the jets between two degree points, in the logarithmic coordinate. -/
theorem sq_sub_mul_levyKernel (f : ℝ → ℝ) {N m n : ℕ} (hN : 1 ≤ N) (hm : 1 ≤ m) (hn : 1 ≤ n)
    (hmn : m ≠ n) :
    (degreeSample f N m - degreeSample f N n) ^ 2 * levyKernel m n =
      boxKernel f (Real.log ((n : ℝ) / N)) (Real.log ((m : ℝ) / N)) / ((n : ℝ) * m) := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hlog : Real.log ((n : ℝ) / N) - Real.log ((m : ℝ) / N) = -Real.log ((m : ℝ) / n) := by
    rw [Real.log_div hn'.ne' hN'.ne', Real.log_div hm'.ne' hN'.ne', Real.log_div hm'.ne' hn'.ne']
    ring
  rw [levyKernel_eq_archLevyDensity hm hn hmn, boxKernel, hlog, abs_neg, degreeSample,
    degreeSample]
  ring

/-- **Lévy–Khintchine on the window.** -/
theorem degreeForm_eq (f : ℝ → ℝ) (L : ℕ) {N : ℕ} (hN : 1 ≤ N) :
    degreeForm f L N =
      ∑ n ∈ Ioc N (N + L * N), degreeSample f N n ^ 2 / n *
          (levyRow n - Real.log ((n : ℝ) / (2 * Real.pi))) -
        ∑ n ∈ Ioc N (N + L * N), degreeSample f N n ^ 2 / n * lowTail N n -
        ∑ n ∈ Ioc N (N + L * N), degreeSample f N n ^ 2 / n * highTail (N + L * N) n -
        (∑ n ∈ Ioc N (N + L * N), ∑ m ∈ Ioc N (N + L * N),
          boxKernel f (Real.log ((n : ℝ) / N)) (Real.log ((m : ℝ) / N)) / ((n : ℝ) * m)) / 2 := by
  have hS : ∀ n ∈ Ioc N (N + L * N), 0 < n := fun n hn => by
    have := (Finset.mem_Ioc.mp hn).1
    omega
  have hrow : ∑ n ∈ Ioc N (N + L * N), degreeSample f N n ^ 2 / n *
        ∑ m ∈ (Ioc N (N + L * N)).erase n, levyWeight m n =
      ∑ n ∈ Ioc N (N + L * N), degreeSample f N n ^ 2 / n *
        (levyRow n - lowTail N n - highTail (N + L * N) n) :=
    Finset.sum_congr rfl fun n hn => by
      rw [sum_erase_window_levyWeight (Finset.mem_Ioc.mp hn).1 (Finset.mem_Ioc.mp hn).2]
  have hdir : ∑ n ∈ Ioc N (N + L * N), ∑ m ∈ (Ioc N (N + L * N)).erase n,
        (degreeSample f N m - degreeSample f N n) ^ 2 * levyKernel m n =
      ∑ n ∈ Ioc N (N + L * N), ∑ m ∈ Ioc N (N + L * N),
        boxKernel f (Real.log ((n : ℝ) / N)) (Real.log ((m : ℝ) / N)) / ((n : ℝ) * m) :=
    Finset.sum_congr rfl fun n hn => by
      have hn1 : 1 ≤ n := hS n hn
      rw [← Finset.sum_erase (Ioc N (N + L * N)) (a := n)
        (f := fun m => boxKernel f (Real.log ((n : ℝ) / N)) (Real.log ((m : ℝ) / N)) /
          ((n : ℝ) * m)) (by simp [boxKernel_self])]
      refine Finset.sum_congr rfl fun m hm => ?_
      exact sq_sub_mul_levyKernel f hN (hS m (Finset.mem_of_mem_erase hm)) hn1
        (Finset.ne_of_mem_erase hm)
  have hcomb : ∑ n ∈ Ioc N (N + L * N), degreeSample f N n ^ 2 / n *
        (levyRow n - lowTail N n - highTail (N + L * N) n) -
      ∑ n ∈ Ioc N (N + L * N), degreeSample f N n ^ 2 / n *
        Real.log ((n : ℝ) / (2 * Real.pi)) =
      ∑ n ∈ Ioc N (N + L * N), degreeSample f N n ^ 2 / n *
          (levyRow n - Real.log ((n : ℝ) / (2 * Real.pi))) -
        ∑ n ∈ Ioc N (N + L * N), degreeSample f N n ^ 2 / n * lowTail N n -
        ∑ n ∈ Ioc N (N + L * N), degreeSample f N n ^ 2 / n * highTail (N + L * N) n := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    ring
  rw [degreeForm, degreePairing, sum_mul_mul_levyKernel _ hS (degreeSample f N), hrow, hdir]
  linarith

/-! ### The limit -/

/-- Masses against errors that are uniformly small on the support of the packet. -/
theorem tendsto_sum_mass_mul_error {f : ℝ → ℝ} {L : ℕ} {s : ℝ} {e : ℕ → ℕ → ℝ}
    (hS : Tendsto (fun N : ℕ => ∑ n ∈ Ioc N (N + L * N), degreeSample f N n ^ 2 / n) atTop
      (𝓝 s))
    (he : ∀ ε > 0, ∀ᶠ N : ℕ in atTop, ∀ n ∈ Ioc N (N + L * N),
      degreeSample f N n ≠ 0 → |e N n| ≤ ε) :
    Tendsto (fun N : ℕ => ∑ n ∈ Ioc N (N + L * N), degreeSample f N n ^ 2 / n * e N n) atTop
      (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hden : 0 < |s| + 2 := by positivity
  have hε1 : 0 < ε / (|s| + 2) := div_pos hε hden
  filter_upwards [he _ hε1, hS.eventually (Iio_mem_nhds (lt_add_one s))] with N h1 h2
  have h2' : ∑ n ∈ Ioc N (N + L * N), degreeSample f N n ^ 2 / n < s + 1 := h2
  rw [Real.dist_eq, sub_zero]
  have hterm : ∀ n ∈ Ioc N (N + L * N), |degreeSample f N n ^ 2 / n * e N n| ≤
      degreeSample f N n ^ 2 / n * (ε / (|s| + 2)) := by
    intro n hn
    have hw : 0 ≤ degreeSample f N n ^ 2 / n := by positivity
    rw [abs_mul, abs_of_nonneg hw]
    by_cases h0 : degreeSample f N n = 0
    · rw [h0]
      simp
    · exact mul_le_mul_of_nonneg_left (h1 n hn h0) hw
  calc |∑ n ∈ Ioc N (N + L * N), degreeSample f N n ^ 2 / n * e N n|
      ≤ ∑ n ∈ Ioc N (N + L * N), |degreeSample f N n ^ 2 / n * e N n| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ n ∈ Ioc N (N + L * N), degreeSample f N n ^ 2 / n * (ε / (|s| + 2)) :=
        Finset.sum_le_sum hterm
    _ = (∑ n ∈ Ioc N (N + L * N), degreeSample f N n ^ 2 / n) * (ε / (|s| + 2)) := by
        rw [Finset.sum_mul]
    _ ≤ (|s| + 1) * (ε / (|s| + 2)) :=
        mul_le_mul_of_nonneg_right (by linarith [le_abs_self s]) hε1.le
    _ < ε := by
        rw [mul_div_assoc', div_lt_iff₀ hden]
        nlinarith [abs_nonneg s]

/-- **The packets on the degree points carry Weil's archimedean form.** For a packet
`f ∈ C²_c(ℝ)` supported in `[log 3, log K]`, the pairing of the jets on the degree points of the
window `N < n ≤ (1 + 3K)N`, minus the masses times `log(n/2π)`, tends to minus the archimedean
part of Weil's functional of `f` without the pole. -/
theorem tendsto_degreeForm {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) {K : ℕ}
    (hK : 1 ≤ K) (hsupp : ∀ u, u ≤ Real.log 3 ∨ Real.log K ≤ u → f u = 0) :
    Tendsto (degreeForm f (3 * K)) atTop
      (𝓝 (-(_root_.RHTower.WeilOneSided.weilArchRe
            (EF.weilTest (packetTest f hf hfc).1 (packetTest f hf hfc).1) -
          (_root_.RHTower.weilPoleTerm
            (EF.weilTest (packetTest f hf hfc).1 (packetTest f hf hfc).1)).re))) := by
  have hcont := hf.continuous
  obtain ⟨B, hB⟩ := hcont.bounded_above_of_compact_support hfc
  obtain ⟨C, hC⟩ := hf.lipschitzWith_of_hasCompactSupport hfc (by norm_num)
  have hB' : ∀ u, |f u| ≤ B := fun u => by
    rw [← Real.norm_eq_abs]
    exact hB u
  have hL : ∀ u v, |f u - f v| ≤ (C : ℝ) * |u - v| := fun u v => by
    have h := hC.dist_le_mul u v
    rwa [Real.dist_eq, Real.dist_eq] at h
  -- the window in the logarithmic coordinate
  have hK' : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hδ : (0 : ℝ) < Real.log 3 := Real.log_pos (by norm_num)
  have h3K : ((3 * K : ℕ) : ℝ) = 3 * K := by
    push_cast
    ring
  have h1L : (0 : ℝ) < 1 + ((3 * K : ℕ) : ℝ) := by
    rw [h3K]
    linarith
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = Real.log (1 + ((3 * K : ℕ) : ℝ)) := ⟨_, rfl⟩
  have hδc : Real.log 3 ≤ c := by
    rw [hc, h3K]
    exact Real.log_le_log (by norm_num) (by linarith)
  have hcK : Real.log K ≤ c - Real.log 3 := by
    rw [hc, h3K, ← Real.log_div (by linarith) (by norm_num)]
    exact Real.log_le_log (by linarith) (by
      rw [le_div_iff₀ (by norm_num)]
      linarith)
  have hsuppW : ∀ u, u ≤ Real.log 3 ∨ c - Real.log 3 ≤ u → f u = 0 := fun u hu =>
    hsupp u (hu.imp id fun h => hcK.trans h)
  have hsuppR : ∀ u : ℝ, (K : ℝ) ≤ |u| → f u = 0 := fun u hu => by
    rcases le_abs.mp hu with h | h
    · exact hsupp u (Or.inr ((Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith)))
    · exact hsupp u (Or.inl (by linarith))
  have hL3 : 1 ≤ 3 * K := by omega
  have hMcast : ∀ N : ℕ, ((N + 3 * K * N : ℕ) : ℝ) = (1 + ((3 * K : ℕ) : ℝ)) * N := fun N => by
    push_cast
    ring
  -- where the samples do not vanish
  have hsam : ∀ {N n : ℕ}, 1 ≤ N → 1 ≤ n → degreeSample f N n ≠ 0 →
      Real.log 3 < Real.log ((n : ℝ) / N) ∧ 3 * N < n ∧ (n : ℝ) < K * N := by
    intro N n hN hn h0
    have hN' : (0 : ℝ) < N := by exact_mod_cast hN
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have h1 : Real.log 3 < Real.log ((n : ℝ) / N) := by
      by_contra h
      exact h0 (hsupp _ (Or.inl (not_lt.mp h)))
    have h2 : Real.log ((n : ℝ) / N) < Real.log K := by
      by_contra h
      exact h0 (hsupp _ (Or.inr (not_lt.mp h)))
    have h3 : (3 : ℝ) < (n : ℝ) / N := (Real.log_lt_log_iff (by norm_num) (by positivity)).mp h1
    have h4 : (n : ℝ) / N < K := (Real.log_lt_log_iff (by positivity) (by linarith)).mp h2
    rw [lt_div_iff₀ hN'] at h3
    rw [div_lt_iff₀ hN'] at h4
    exact ⟨h1, by exact_mod_cast h3, h4⟩
  -- the masses
  have hmass : Tendsto (fun N : ℕ => ∑ n ∈ Ioc N (N + 3 * K * N), degreeSample f N n ^ 2 / n)
      atTop (𝓝 (packetAutocorr f 0)) := by
    have h := tendsto_degreeSum (G := fun u => f u ^ 2) (hcont.pow 2) hL3
    rw [← hc] at h
    rw [packetAutocorr_zero_eq_integral_window hδ hsuppW]
    exact h
  -- the masses against the total rates
  have hrowlim : Tendsto (fun N : ℕ => ∑ n ∈ Ioc N (N + 3 * K * N),
      degreeSample f N n ^ 2 / n * (levyRow n - Real.log ((n : ℝ) / (2 * Real.pi)))) atTop
      (𝓝 (-EF.gammaBracket 0 * packetAutocorr f 0)) := by
    have herr := tendsto_sum_mass_mul_error
      (e := fun _ n => levyRow n - Real.log ((n : ℝ) / (2 * Real.pi)) + EF.gammaBracket 0) hmass
      (fun ε hε => by
        obtain ⟨n₀, hn₀⟩ := Filter.eventually_atTop.mp
          ((Metric.tendsto_nhds.mp tendsto_levyRow_sub_log) ε hε)
        filter_upwards [eventually_ge_atTop n₀] with N hN n hn _
        have hlt := hn₀ n (hN.trans (Finset.mem_Ioc.mp hn).1.le)
        rw [Real.dist_eq, sub_neg_eq_add] at hlt
        exact hlt.le)
    have h := (hmass.const_mul (-EF.gammaBracket 0)).add herr
    rw [add_zero] at h
    refine h.congr fun N => ?_
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    ring
  -- the masses against the rates beyond the window
  have hGhigh : Continuous fun u => f u ^ 2 * Ω (max (c - u) (Real.log 3)) :=
    (hcont.pow 2).mul (continuous_archLevyAntideriv_max (continuous_const.sub continuous_id) hδ)
  have hhigh : Tendsto (fun N : ℕ => ∑ n ∈ Ioc N (N + 3 * K * N),
      degreeSample f N n ^ 2 / n * highTail (N + 3 * K * N) n) atTop
      (𝓝 (∫ u in (0 : ℝ)..c, f u ^ 2 * Ω (max (c - u) (Real.log 3)))) := by
    have hmain := tendsto_degreeSum hGhigh hL3
    rw [← hc] at hmain
    have herr := tendsto_sum_mass_mul_error
      (e := fun N n => highTail (N + 3 * K * N) n -
        Ω (max (c - Real.log ((n : ℝ) / N)) (Real.log 3))) hmass
      (fun ε hε => by
        have hlim : Tendsto (fun N : ℕ => ω (Real.log 3) / (N : ℝ)) atTop (𝓝 0) :=
          tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
        filter_upwards [hlim.eventually (Iic_mem_nhds hε), eventually_ge_atTop 1]
          with N hNε hN n hn h0
        have hn1 : 1 ≤ n := by
          have := (Finset.mem_Ioc.mp hn).1
          omega
        obtain ⟨_, _, h4⟩ := hsam hN hn1 h0
        have hN' : (0 : ℝ) < N := by exact_mod_cast hN
        have hn' : (0 : ℝ) < n := by exact_mod_cast hn1
        have hKN : (0 : ℝ) < K * N := by positivity
        have hnM' : (n : ℝ) < ((N + 3 * K * N : ℕ) : ℝ) := by
          rw [hMcast, h3K]
          linarith
        have hnM : n < N + 3 * K * N := by exact_mod_cast hnM'
        have hcu : c - Real.log ((n : ℝ) / N) = Real.log (((N + 3 * K * N : ℕ) : ℝ) / n) := by
          rw [hc, hMcast, Real.log_div hn'.ne' hN'.ne',
            Real.log_div (mul_pos h1L hN').ne' hn'.ne', Real.log_mul h1L.ne' hN'.ne']
          ring
        have hratio : Real.log 3 ≤ Real.log (((N + 3 * K * N : ℕ) : ℝ) / n) := by
          apply Real.log_le_log (by norm_num)
          rw [le_div_iff₀ hn', hMcast, h3K]
          linarith
        have hω : ω (Real.log (((N + 3 * K * N : ℕ) : ℝ) / n)) ≤ ω (Real.log 3) :=
          archLevyDensity_antitoneOn hδ (hδ.trans_le hratio) hratio
        have hMN : (N : ℝ) ≤ ((N + 3 * K * N : ℕ) : ℝ) := by
          exact_mod_cast Nat.le_add_right N _
        have hNε' : ω (Real.log 3) / (N : ℝ) ≤ ε := hNε
        show |highTail (N + 3 * K * N) n - Ω (max (c - Real.log ((n : ℝ) / N)) (Real.log 3))| ≤ ε
        rw [hcu, max_eq_left hratio]
        exact ((abs_highTail_sub_le hn1 hnM).trans
          (div_le_div₀ (_root_.RHTower.archLevyDensity_pos hδ).le hω hN' hMN)).trans hNε')
    have h := hmain.add herr
    rw [add_zero] at h
    refine h.congr fun N => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    simp only [degreeSample]
    ring
  -- the masses against the rates below the window
  have hGlow : Continuous fun u => f u ^ 2 * Ω (max u (Real.log 3)) :=
    (hcont.pow 2).mul (continuous_archLevyAntideriv_max continuous_id hδ)
  have hlow : Tendsto (fun N : ℕ => ∑ n ∈ Ioc N (N + 3 * K * N),
      degreeSample f N n ^ 2 / n * lowTail N n) atTop
      (𝓝 (∫ u in (0 : ℝ)..c, f u ^ 2 * Ω (max u (Real.log 3)))) := by
    have hmain := tendsto_degreeSum hGlow hL3
    rw [← hc] at hmain
    have herr := tendsto_sum_mass_mul_error
      (e := fun N n => lowTail N n - Ω (max (Real.log ((n : ℝ) / N)) (Real.log 3))) hmass
      (fun ε hε => by
        have hlim : Tendsto (fun N : ℕ => Ω (Real.log (N : ℝ))) atTop (𝓝 0) :=
          _root_.RHTower.WeilLevyCoshCrossover.tendsto_archLevyAntideriv_atTop.comp
            (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
        filter_upwards [hlim.eventually (Iic_mem_nhds hε), eventually_ge_atTop 2]
          with N hNε hN n hn h0
        have hN1 : 1 ≤ N := by omega
        have hn1 : 1 ≤ n := by
          have := (Finset.mem_Ioc.mp hn).1
          omega
        obtain ⟨h1, h3, _⟩ := hsam hN1 hn1 h0
        have hN' : (1 : ℝ) < N := by exact_mod_cast hN
        have hNn : (N : ℝ) ≤ n := by exact_mod_cast (by omega : N ≤ n)
        have hb := lowTail_bounds hN1 h3.le
        have hanti : Ω (Real.log (n : ℝ)) ≤ Ω (Real.log (N : ℝ)) :=
          archLevyAntideriv_anti (Real.log_pos hN') (Real.log_le_log (by linarith) hNn)
        have hNε' : Ω (Real.log (N : ℝ)) ≤ ε := hNε
        show |lowTail N n - Ω (max (Real.log ((n : ℝ) / N)) (Real.log 3))| ≤ ε
        rw [max_eq_left h1.le, abs_le]
        constructor <;> linarith [hb.1, hb.2])
    have h := hmain.add herr
    rw [add_zero] at h
    refine h.congr fun N => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    simp only [degreeSample]
    ring
  -- the jumps inside the window
  have hdir := tendsto_degreePairSum (continuous_boxKernel hcont hL) (3 * K)
  rw [← hc] at hdir
  -- the jump form of the packet
  have hbox := integral_levyJump_eq_window hcont hsuppR hB' hL hδ hδc hsuppW
  have hweil := weilArchRe_sub_pole_packet hf hfc hsuppR hB' hL
  have hTp : ∫ u in (0 : ℝ)..c, f u ^ 2 * (Ω (max (c - u) (Real.log 3)) + Ω (max u (Real.log 3))) =
      (∫ u in (0 : ℝ)..c, f u ^ 2 * Ω (max (c - u) (Real.log 3))) +
        ∫ u in (0 : ℝ)..c, f u ^ 2 * Ω (max u (Real.log 3)) := by
    rw [← intervalIntegral.integral_add (hGhigh.intervalIntegrable _ _)
      (hGlow.intervalIntegrable _ _)]
    refine intervalIntegral.integral_congr fun u _ => ?_
    show f u ^ 2 * (Ω (max (c - u) (Real.log 3)) + Ω (max u (Real.log 3))) =
      f u ^ 2 * Ω (max (c - u) (Real.log 3)) + f u ^ 2 * Ω (max u (Real.log 3))
    ring
  have hlim := ((hrowlim.sub hlow).sub hhigh).sub (hdir.div_const 2)
  have e : -(EF.gammaBracket 0 * packetAutocorr f 0 +
        ((∫ u in (0 : ℝ)..c, ∫ v in (0 : ℝ)..c, boxKernel f u v) / 2 +
          ((∫ u in (0 : ℝ)..c, f u ^ 2 * Ω (max (c - u) (Real.log 3))) +
            ∫ u in (0 : ℝ)..c, f u ^ 2 * Ω (max u (Real.log 3))))) =
      -EF.gammaBracket 0 * packetAutocorr f 0 -
          (∫ u in (0 : ℝ)..c, f u ^ 2 * Ω (max u (Real.log 3))) -
          (∫ u in (0 : ℝ)..c, f u ^ 2 * Ω (max (c - u) (Real.log 3))) -
        (∫ u in (0 : ℝ)..c, ∫ v in (0 : ℝ)..c, boxKernel f u v) / 2 := by ring
  rw [hweil, hbox, hTp, e]
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  exact (degreeForm_eq f (3 * K) hN).symm

/-! ### Every packet, at the scales above its support -/

theorem packetAutocorr_translate (f : ℝ → ℝ) (s x : ℝ) :
    packetAutocorr (fun u => f (u - s)) x = packetAutocorr f x := by
  rw [packetAutocorr, packetAutocorr,
    ← integral_sub_right_eq_self (fun u => f u * f (u + x)) s]
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  show f (u - s) * f (u + x - s) = f (u - s) * f (u - s + x)
  rw [sub_add_eq_add_sub]

theorem levyJump_translate (f : ℝ → ℝ) (s : ℝ) :
    levyJump (fun u => f (u - s)) = levyJump f := by
  funext x
  rw [levyJump, levyJump, packetAutocorr_translate, packetAutocorr_translate]

/-- **Every packet, at the scales above its support.** A packet `f ∈ C²_c(ℝ)` supported in
`[−R, R]` is moved to `[log 3, log K]` by the translation by `R + log 3`; on the degree points
this is the sampling of `f` at the scale `3e^R N`. Weil's functional does not change, so the
pairing of the jets with the counterterm of the degree points tends to minus the archimedean part
of Weil's functional of `f` without the pole. -/
theorem tendsto_degreeForm_translate {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) {R K : ℕ} (hsuppR : ∀ u : ℝ, (R : ℝ) ≤ |u| → f u = 0)
    (hK : 2 * (R : ℝ) + Real.log 3 ≤ Real.log K) :
    Tendsto (degreeForm (fun u => f (u - ((R : ℝ) + Real.log 3))) (3 * K)) atTop
      (𝓝 (-(_root_.RHTower.WeilOneSided.weilArchRe
            (EF.weilTest (packetTest f hf hfc).1 (packetTest f hf hfc).1) -
          (_root_.RHTower.weilPoleTerm
            (EF.weilTest (packetTest f hf hfc).1 (packetTest f hf hfc).1)).re))) := by
  have hδ : (0 : ℝ) < Real.log 3 := Real.log_pos (by norm_num)
  have hlog3 : Real.log 3 ≤ 2 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)
    linarith
  have hR0 : (0 : ℝ) ≤ R := Nat.cast_nonneg R
  have hK1 : 1 ≤ K := by
    rcases Nat.eq_zero_or_pos K with rfl | h
    · rw [Nat.cast_zero, Real.log_zero] at hK
      linarith
    · exact h
  have hcont := hf.continuous
  obtain ⟨B, hB⟩ := hcont.bounded_above_of_compact_support hfc
  obtain ⟨C, hC⟩ := hf.lipschitzWith_of_hasCompactSupport hfc (by norm_num)
  have hB' : ∀ u, |f u| ≤ B := fun u => by
    rw [← Real.norm_eq_abs]
    exact hB u
  have hL : ∀ u v, |f u - f v| ≤ (C : ℝ) * |u - v| := fun u v => by
    have h := hC.dist_le_mul u v
    rwa [Real.dist_eq, Real.dist_eq] at h
  -- the translate
  have hg : ContDiff ℝ 2 fun u => f (u - ((R : ℝ) + Real.log 3)) :=
    hf.comp (contDiff_id.sub contDiff_const)
  have hgc : HasCompactSupport fun u => f (u - ((R : ℝ) + Real.log 3)) :=
    HasCompactSupport.intro
      (isCompact_Icc (a := Real.log 3) (b := 2 * (R : ℝ) + Real.log 3)) fun x hx => by
        refine hsuppR _ ?_
        rw [Set.mem_Icc, not_and_or, not_le, not_le] at hx
        rcases hx with h | h
        · exact le_abs.mpr (Or.inr (by linarith))
        · exact le_abs.mpr (Or.inl (by linarith))
  have hgsupp : ∀ u, u ≤ Real.log 3 ∨ Real.log K ≤ u →
      f (u - ((R : ℝ) + Real.log 3)) = 0 := by
    rintro u (hu | hu)
    · exact hsuppR _ (le_abs.mpr (Or.inr (by linarith)))
    · exact hsuppR _ (le_abs.mpr (Or.inl (by linarith)))
  have hgR : ∀ u : ℝ, ((2 * R + 2 : ℕ) : ℝ) ≤ |u| → f (u - ((R : ℝ) + Real.log 3)) = 0 := by
    intro u hu
    refine hsuppR _ ?_
    have h1 := abs_sub_abs_le_abs_sub u ((R : ℝ) + Real.log 3)
    rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ (R : ℝ) + Real.log 3)] at h1
    push_cast at hu
    linarith
  have hgB : ∀ u, |f (u - ((R : ℝ) + Real.log 3))| ≤ B := fun u => hB' _
  have hgL : ∀ u v, |f (u - ((R : ℝ) + Real.log 3)) - f (v - ((R : ℝ) + Real.log 3))| ≤
      (C : ℝ) * |u - v| := fun u v => by
    have h := hL (u - ((R : ℝ) + Real.log 3)) (v - ((R : ℝ) + Real.log 3))
    rwa [sub_sub_sub_cancel_right] at h
  have hmain := tendsto_degreeForm hg hgc hK1 hgsupp
  rw [weilArchRe_sub_pole_packet hg hgc hgR hgB hgL, levyJump_translate,
    packetAutocorr_translate] at hmain
  rw [weilArchRe_sub_pole_packet hf hfc hsuppR hB' hL]
  exact hmain

/-! ### A counterterm of the scale alone -/

/-- The first moment of the mass of a translated packet. -/
theorem integral_sq_mul_translate {f : ℝ → ℝ} (hcont : Continuous f) (hfc : HasCompactSupport f)
    (s : ℝ) : ∫ u, f (u - s) ^ 2 * u = (∫ u, f u ^ 2 * u) + s * ∫ u, f u ^ 2 := by
  have hsq : HasCompactSupport fun v => f v ^ 2 := hfc.comp_left (zero_pow two_ne_zero)
  have i1 : Integrable fun v => f v ^ 2 * v :=
    ((hcont.pow 2).mul continuous_id).integrable_of_hasCompactSupport hsq.mul_right
  have i2 : Integrable fun v => s * f v ^ 2 :=
    ((hcont.pow 2).integrable_of_hasCompactSupport hsq).const_mul s
  have h := integral_sub_right_eq_self (μ := volume) (fun v => f v ^ 2 * (v + s)) s
  have hl : ∫ u, f (u - s) ^ 2 * u = ∫ u, f (u - s) ^ 2 * (u - s + s) :=
    integral_congr_ae (Eventually.of_forall fun u => by
      show f (u - s) ^ 2 * u = f (u - s) ^ 2 * (u - s + s)
      rw [sub_add_cancel])
  have hr : ∫ v, f v ^ 2 * (v + s) = ∫ v, (f v ^ 2 * v + s * f v ^ 2) :=
    integral_congr_ae (Eventually.of_forall fun v => by
      show f v ^ 2 * (v + s) = f v ^ 2 * v + s * f v ^ 2
      ring)
  rw [hl, h, hr, integral_add i1 i2, integral_const_mul]

/-- **A counterterm of the scale alone leaves the first moment of the mass.** With the
counterterm `log(N/2π)` at every degree point of the window, a function of the scale and not of
the point, the pairing of the jets tends to minus the archimedean part of Weil's functional
without the pole plus `∫ f(u)² u du`. -/
theorem tendsto_degreePairing_sub_scale_counterterm {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) {K : ℕ} (hK : 1 ≤ K)
    (hsupp : ∀ u, u ≤ Real.log 3 ∨ Real.log K ≤ u → f u = 0) :
    Tendsto (fun N : ℕ => degreePairing f (3 * K) N -
        (∑ n ∈ Ioc N (N + 3 * K * N), degreeSample f N n ^ 2 / n) *
          Real.log ((N : ℝ) / (2 * Real.pi))) atTop
      (𝓝 (-(_root_.RHTower.WeilOneSided.weilArchRe
            (EF.weilTest (packetTest f hf hfc).1 (packetTest f hf hfc).1) -
          (_root_.RHTower.weilPoleTerm
            (EF.weilTest (packetTest f hf hfc).1 (packetTest f hf hfc).1)).re) +
        ∫ u in (0 : ℝ)..Real.log (1 + ((3 * K : ℕ) : ℝ)), f u ^ 2 * u)) := by
  have hG : Continuous fun u => f u ^ 2 * u := (hf.continuous.pow 2).mul continuous_id
  have h1 := tendsto_degreeForm hf hfc hK hsupp
  have h2 := tendsto_degreeSum hG (by omega : 1 ≤ 3 * K)
  refine (h1.add h2).congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have h2π : (2 * Real.pi) ≠ 0 := by positivity
  have hterm : ∀ n ∈ Ioc N (N + 3 * K * N),
      degreeSample f N n ^ 2 / n * Real.log ((n : ℝ) / (2 * Real.pi)) =
        (fun u => f u ^ 2 * u) (Real.log ((n : ℝ) / N)) / n +
          degreeSample f N n ^ 2 / n * Real.log ((N : ℝ) / (2 * Real.pi)) := by
    intro n hn
    have hn' : (0 : ℝ) < n := by
      have := (Finset.mem_Ioc.mp hn).1
      exact_mod_cast (by omega : 0 < n)
    show degreeSample f N n ^ 2 / n * Real.log ((n : ℝ) / (2 * Real.pi)) =
      f (Real.log ((n : ℝ) / N)) ^ 2 * Real.log ((n : ℝ) / N) / n +
        degreeSample f N n ^ 2 / n * Real.log ((N : ℝ) / (2 * Real.pi))
    rw [degreeSample, Real.log_div hn'.ne' h2π, Real.log_div hn'.ne' hN'.ne',
      Real.log_div hN'.ne' h2π]
    ring
  rw [degreeForm, Finset.sum_congr rfl hterm, Finset.sum_add_distrib, ← Finset.sum_mul]
  ring

/-- **Without a counterterm the pairing of the jets grows like the mass times `log N`.** The
pairing divided by `log N` tends to `∫ f²`. -/
theorem tendsto_degreePairing_div_log {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) {K : ℕ} (hK : 1 ≤ K)
    (hsupp : ∀ u, u ≤ Real.log 3 ∨ Real.log K ≤ u → f u = 0) :
    Tendsto (fun N : ℕ => degreePairing f (3 * K) N / Real.log N) atTop
      (𝓝 (∫ u in (0 : ℝ)..Real.log (1 + ((3 * K : ℕ) : ℝ)), f u ^ 2)) := by
  have h1 := tendsto_degreePairing_sub_scale_counterterm hf hfc hK hsupp
  have hS : Tendsto (fun N : ℕ => ∑ n ∈ Ioc N (N + 3 * K * N), degreeSample f N n ^ 2 / n) atTop
      (𝓝 (∫ u in (0 : ℝ)..Real.log (1 + ((3 * K : ℕ) : ℝ)), f u ^ 2)) :=
    tendsto_degreeSum (G := fun u => f u ^ 2) (hf.continuous.pow 2) (by omega : 1 ≤ 3 * K)
  have hlog : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have h0 := h1.div_atTop hlog
  have hr : Tendsto (fun N : ℕ => Real.log ((N : ℝ) / (2 * Real.pi)) / Real.log N) atTop
      (𝓝 1) := by
    have h := (tendsto_const_nhds (x := (1 : ℝ))).sub
      ((tendsto_const_nhds (x := Real.log (2 * Real.pi))).div_atTop hlog)
    rw [sub_zero] at h
    refine h.congr' ?_
    filter_upwards [eventually_ge_atTop 2] with N hN
    have hN1 : (1 : ℝ) < N := by exact_mod_cast hN
    have hl : Real.log (N : ℝ) ≠ 0 := (Real.log_pos hN1).ne'
    rw [Real.log_div (zero_lt_one.trans hN1).ne' (by positivity), sub_div, div_self hl]
  have h := h0.add (hS.mul hr)
  rw [zero_add, mul_one] at h
  refine h.congr fun N => ?_
  ring

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ
