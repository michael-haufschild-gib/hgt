import GaloisForLFunctions.BiScaleUncertainty.PrimeWindowCeilingPolarAsymptotics

/-!
# The floor of the prime side on long windows

The polar kernel `e^{|s−t|/2}` on `[0, L]` is nearly `e^{L/2}(u ⊗ v + v ⊗ u)` with `u = e^{−t/2}`,
`v = e^{−(L−t)/2}`: its spectrum carries the pair `± e^{L/2}`. The ceiling of the prime side is the
top (`PrimeWindowCeilingPolarAsymptotics`); this file proves that the floor is the bottom.

**Theorem** (`tendsto_windowFloor_div_exp`). The window floor `inf (A − W)/‖c‖²` over
nonnegative combinations of tests supported in intervals of length `L` satisfies
`floor(L)/e^{L/2} → −1`. With the ceiling: on windows of length `log X` the prime side ranges
exactly over `[−√X, √X](1 + o(1))`.

**Mechanism.** The antisymmetric polar test `(e^{−t/2} − e^{−(L−t)/2}) χ(t)` pairs its two ends with
the opposite sign: `k(y) ≤ 2L e^{−y/2} − e^{−(L−y)/2}(L − y − 2δ)` (`correlation_antiTest_le`), so its
prime side is at most `4L(2 + L)² − 2 e^{−L/2} Σ_{n≤Y} Λ(n) log(Y/n)` with `Y = e^{L−2δ}`, and the
Riesz mean is `≥ (1 − η)Y`. The self-correlations of `u` and `v` cost only `O(L³)`.
-/

open MeasureTheory Set Complex Finsupp Filter Topology
open Zeta23
open RHTower RHTower.WeilOneSided
open scoped ComplexConjugate Real

namespace GaloisForLFunctions.BiScaleUncertainty

noncomputable section

/-- The correlation of a real profile is real. -/
theorem weilTest_ofReal (F : ℝ → ℝ) (y : ℝ) :
    EF.weilTest (fun t => (F t : ℂ)) (fun t => (F t : ℂ)) y = ((∫ t, F t * F (t - y) : ℝ) : ℂ) := by
  rw [WeilSpectral.weilTest_apply, ← integral_complex_ofReal]
  congr 1; funext t
  simp only [Complex.conj_ofReal, Complex.ofReal_mul]

/-- The correlation of a real profile is even. -/
theorem integral_mul_sub_neg (F : ℝ → ℝ) (y : ℝ) :
    ∫ t, F t * F (t - -y) = ∫ t, F t * F (t - y) := by
  have := integral_add_right_eq_self (μ := volume) (fun t => F t * F (t + y)) (-y)
  simp only [sub_neg_eq_add]
  rw [← this]
  congr 1; funext t
  rw [show t + -y + y = t by ring, show t + -y = t - y by ring, mul_comm]

/-- The antisymmetric polar profile `e^{−t/2} − e^{−(L−t)/2}`. -/
def antiProfile (L t : ℝ) : ℝ := Real.exp (-t / 2) - Real.exp (-(L - t) / 2)

section AntiTest

variable {L δ : ℝ} (hδ : 0 < δ) (hLδ : 2 * δ < L)

/-- The antisymmetric polar test `(e^{−t/2} − e^{−(L−t)/2}) χ(t)`. -/
def antiTestReal (t : ℝ) : ℝ := antiProfile L t * polarCutoff hδ hLδ t

theorem mem_of_antiTestReal_ne_zero {t : ℝ} (ht : antiTestReal hδ hLδ t ≠ 0) : t ∈ Ioo 0 L :=
  mem_of_polarCutoff_ne_zero hδ hLδ (right_ne_zero_of_mul ht)

theorem antiTestReal_sq_le (t : ℝ) : antiTestReal hδ hLδ t ^ 2 ≤ polarTestReal hδ hLδ t ^ 2 := by
  have hu := Real.exp_pos (-t / 2)
  have hv := Real.exp_pos (-(L - t) / 2)
  rw [antiTestReal, polarTestReal, antiProfile, polarProfile, mul_pow, mul_pow]
  exact mul_le_mul_of_nonneg_right (by nlinarith) (sq_nonneg _)

theorem contDiff_antiTestReal : ContDiff ℝ 2 (antiTestReal hδ hLδ) :=
  ((Real.contDiff_exp.comp (contDiff_id.neg.div_const 2)).sub
    (Real.contDiff_exp.comp ((contDiff_const.sub contDiff_id).neg.div_const 2))).mul
      (polarCutoff hδ hLδ).contDiff

theorem hasCompactSupport_antiTestReal : HasCompactSupport (antiTestReal hδ hLδ) :=
  (polarCutoff hδ hLδ).hasCompactSupport.mul_left

/-- The antisymmetric polar test as a Weil test. -/
def antiTestFn : WeilTestFn :=
  ⟨fun t => (antiTestReal hδ hLδ t : ℂ), Complex.ofRealCLM.contDiff.comp (contDiff_antiTestReal hδ hLδ),
    (hasCompactSupport_antiTestReal hδ hLδ).comp_left (g := ((↑) : ℝ → ℂ)) Complex.ofReal_zero⟩

theorem antiTestFn_supp : ∀ u, (antiTestFn hδ hLδ).1 u ≠ 0 → u ∈ Ioo 0 (0 + L) := by
  intro u hu
  rw [zero_add]
  exact mem_of_antiTestReal_ne_zero hδ hLδ fun h => hu (by simp [antiTestFn, h])

theorem integrable_antiTestReal_mul (y : ℝ) :
    Integrable fun t => antiTestReal hδ hLδ t * antiTestReal hδ hLδ (t - y) :=
  ((contDiff_antiTestReal hδ hLδ).continuous.mul ((contDiff_antiTestReal hδ hLδ).continuous.comp
    (continuous_id.sub continuous_const))).integrable_of_hasCompactSupport
      (hasCompactSupport_antiTestReal hδ hLδ).mul_right

/-- The pointwise correlation bound: the self terms are at most `e^{−y/2}` each on the window, and
the cross term `−e^{−(L−t)/2} e^{−(t−y)/2} = −e^{−(L−y)/2}` is fully present where `χ = 1`. -/
theorem antiTestReal_mul_le {y t : ℝ} (hy : 0 ≤ y) :
    antiTestReal hδ hLδ t * antiTestReal hδ hLδ (t - y) ≤
      (Ioo 0 L).indicator (fun _ => 2 * Real.exp (-y / 2)) t -
        (Icc (y + δ) (L - δ)).indicator (fun _ => Real.exp (-(L - y) / 2)) t := by
  set χ := polarCutoff hδ hLδ
  have hχ0 : ∀ s, 0 ≤ χ s := fun s => χ.nonneg
  have hχ1 : ∀ s, χ s ≤ 1 := fun s => χ.le_one
  set c := χ t * χ (t - y) with hc
  have hc0 : 0 ≤ c := mul_nonneg (hχ0 _) (hχ0 _)
  have hc1 : c ≤ 1 := by nlinarith [hχ0 t, hχ0 (t - y), hχ1 t, hχ1 (t - y)]
  have hval : antiTestReal hδ hLδ t * antiTestReal hδ hLδ (t - y) =
      c * (Real.exp (-t / 2) * Real.exp (-(t - y) / 2) +
        Real.exp (-(L - t) / 2) * Real.exp (-(L - (t - y)) / 2) -
        Real.exp (-t / 2) * Real.exp (-(L - (t - y)) / 2) -
        Real.exp (-(L - t) / 2) * Real.exp (-(t - y) / 2)) := by
    simp only [antiTestReal, antiProfile, hc, χ]; ring
  have hcross : Real.exp (-(L - t) / 2) * Real.exp (-(t - y) / 2) = Real.exp (-(L - y) / 2) := by
    rw [← Real.exp_add]; congr 1; ring
  have hpos3 : 0 ≤ Real.exp (-t / 2) * Real.exp (-(L - (t - y)) / 2) := by positivity
  rw [hval, hcross]
  by_cases hc_pos : c = 0
  · rw [hc_pos, zero_mul]
    by_cases hI : t ∈ Icc (y + δ) (L - δ)
    · exfalso
      have h1 : χ t = 1 := polarCutoff_eq_one hδ hLδ ⟨by linarith [hI.1], hI.2⟩
      have h2 : χ (t - y) = 1 := polarCutoff_eq_one hδ hLδ ⟨by linarith [hI.1], by linarith [hI.2]⟩
      rw [hc, h1, h2] at hc_pos; norm_num at hc_pos
    · rw [Set.indicator_of_notMem hI, sub_zero]
      exact Set.indicator_nonneg (fun _ _ => by positivity) t
  -- `c > 0`: both `t` and `t − y` lie in the window
  have ht : t ∈ Ioo 0 L := mem_of_polarCutoff_ne_zero hδ hLδ fun h => hc_pos (by rw [hc, h, zero_mul])
  have hty : t - y ∈ Ioo 0 L :=
    mem_of_polarCutoff_ne_zero hδ hLδ fun h => hc_pos (by rw [hc, h, mul_zero])
  have hs1 : Real.exp (-t / 2) * Real.exp (-(t - y) / 2) ≤ Real.exp (-y / 2) := by
    rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (by linarith [hty.1])
  have hs2 : Real.exp (-(L - t) / 2) * Real.exp (-(L - (t - y)) / 2) ≤ Real.exp (-y / 2) := by
    rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (by linarith [ht.2])
  rw [Set.indicator_of_mem ht]
  have hE := Real.exp_pos (-(L - y) / 2)
  by_cases hI : t ∈ Icc (y + δ) (L - δ)
  · have h1 : χ t = 1 := polarCutoff_eq_one hδ hLδ ⟨by linarith [hI.1], hI.2⟩
    have h2 : χ (t - y) = 1 := polarCutoff_eq_one hδ hLδ ⟨by linarith [hI.1], by linarith [hI.2]⟩
    have hc1' : c = 1 := by rw [hc, h1, h2, one_mul]
    rw [Set.indicator_of_mem hI, hc1', one_mul]
    linarith
  · rw [Set.indicator_of_notMem hI, sub_zero]
    nlinarith [mul_le_mul_of_nonneg_left (by linarith : Real.exp (-t / 2) * Real.exp (-(t - y) / 2) +
        Real.exp (-(L - t) / 2) * Real.exp (-(L - (t - y)) / 2) -
        Real.exp (-t / 2) * Real.exp (-(L - (t - y)) / 2) - Real.exp (-(L - y) / 2) ≤
        2 * Real.exp (-y / 2)) hc0, mul_nonneg (sub_nonneg.mpr hc1) (Real.exp_pos (-y / 2)).le]

/-- **The antisymmetric correlation.** For `0 ≤ y ≤ L − 2δ`:
`k(y) ≤ 2L e^{−y/2} − e^{−(L−y)/2}(L − y − 2δ)`. -/
theorem correlation_antiTest_le {y : ℝ} (hy : 0 ≤ y) (hyL : y + 2 * δ ≤ L) :
    ∫ t, antiTestReal hδ hLδ t * antiTestReal hδ hLδ (t - y) ≤
      2 * L * Real.exp (-y / 2) - Real.exp (-(L - y) / 2) * (L - y - 2 * δ) := by
  have hL : 0 < L := by linarith
  have h1 : ∫ t, (Ioo 0 L).indicator (fun _ => 2 * Real.exp (-y / 2)) t = 2 * L * Real.exp (-y / 2) := by
    rw [integral_indicator_const _ measurableSet_Ioo, measureReal_def, Real.volume_Ioo,
      ENNReal.toReal_ofReal (by linarith), smul_eq_mul]
    ring
  have h2 : ∫ t, (Icc (y + δ) (L - δ)).indicator (fun _ => Real.exp (-(L - y) / 2)) t =
      Real.exp (-(L - y) / 2) * (L - y - 2 * δ) := by
    rw [integral_indicator_const _ measurableSet_Icc, measureReal_def, Real.volume_Icc,
      ENNReal.toReal_ofReal (by linarith), smul_eq_mul]
    ring
  have hi1 : Integrable fun t => (Ioo 0 L).indicator (fun _ => 2 * Real.exp (-y / 2)) t :=
    continuous_const.integrableOn_Icc.mono_set Ioo_subset_Icc_self |>.integrable_indicator
      measurableSet_Ioo
  have hi2 : Integrable fun t => (Icc (y + δ) (L - δ)).indicator (fun _ => Real.exp (-(L - y) / 2)) t :=
    continuous_const.integrableOn_Icc.integrable_indicator measurableSet_Icc
  rw [← h1, ← h2, ← integral_sub hi1 hi2]
  exact integral_mono (integrable_antiTestReal_mul hδ hLδ y) (hi1.sub hi2)
    fun t => antiTestReal_mul_le hδ hLδ hy

/-- Beyond `L − 2δ` only the self terms remain: `k(y) ≤ 2L e^{−y/2}` for `y ≥ 0`. -/
theorem correlation_antiTest_le_self {y : ℝ} (hy : 0 ≤ y) :
    ∫ t, antiTestReal hδ hLδ t * antiTestReal hδ hLδ (t - y) ≤ 2 * L * Real.exp (-y / 2) := by
  have hL : 0 < L := by linarith
  have h1 : ∫ t, (Ioo 0 L).indicator (fun _ => 2 * Real.exp (-y / 2)) t = 2 * L * Real.exp (-y / 2) := by
    rw [integral_indicator_const _ measurableSet_Ioo, measureReal_def, Real.volume_Ioo,
      ENNReal.toReal_ofReal (by linarith), smul_eq_mul]
    ring
  have hi1 : Integrable fun t => (Ioo 0 L).indicator (fun _ => 2 * Real.exp (-y / 2)) t :=
    continuous_const.integrableOn_Icc.mono_set Ioo_subset_Icc_self |>.integrable_indicator
      measurableSet_Ioo
  rw [← h1]
  refine integral_mono (integrable_antiTestReal_mul hδ hLδ y) hi1 fun t => ?_
  have := antiTestReal_mul_le hδ hLδ (t := t) hy
  have : 0 ≤ (Icc (y + δ) (L - δ)).indicator (fun _ => Real.exp (-(L - y) / 2)) t :=
    Set.indicator_nonneg (fun _ _ => (Real.exp_pos _).le) t
  linarith

theorem hasCompactSupport_antiTestReal_sq :
    HasCompactSupport fun u => antiTestReal hδ hLδ u ^ 2 :=
  HasCompactSupport.intro (isCompact_Icc (a := 0) (b := L)) fun u hu => by
    by_cases h : antiTestReal hδ hLδ u = 0
    · rw [h]; norm_num
    · exact absurd (Ioo_subset_Icc_self (mem_of_antiTestReal_ne_zero hδ hLδ h)) hu

/-- The mass of the antisymmetric test is at most that of the polar test. -/
theorem massOf_antiTest_le :
    massOf (Finsupp.single (antiTestFn hδ hLδ) 1) ≤ 2 + 2 * L * Real.exp (-L / 2) := by
  refine le_trans ?_ (massOf_polarTest_le hδ hLδ)
  rw [WeilOneSided.massOf, Finsupp.sum_single_index (by simp), one_mul,
    WeilOneSided.massOf, Finsupp.sum_single_index (by simp), one_mul]
  change ∫ u, ‖(antiTestReal hδ hLδ u : ℂ)‖ ^ 2 ≤ ∫ u, ‖(polarTestReal hδ hLδ u : ℂ)‖ ^ 2
  simp_rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  exact integral_mono
    (((contDiff_antiTestReal hδ hLδ).continuous.pow 2).integrable_of_hasCompactSupport
      (hasCompactSupport_antiTestReal_sq hδ hLδ))
    (((contDiff_polarTestReal hδ hLδ).continuous.pow 2).integrable_of_hasCompactSupport
      (hasCompactSupport_polarTestReal_sq hδ hLδ))
    fun u => antiTestReal_sq_le hδ hLδ u

end AntiTest

/-! ### The prime side of the antisymmetric test -/

section AntiTestDeviation

variable {L δ : ℝ} (hδ : 0 < δ) (hLδ : 2 * δ < L)

theorem logValue_antiTest_eq (n : ℕ) :
    logValue (antiTestFn hδ hLδ).1 n =
      2 * (∫ t, antiTestReal hδ hLδ t * antiTestReal hδ hLδ (t - Real.log n)) / Real.sqrt n := by
  change logValue (fun t => (antiTestReal hδ hLδ t : ℂ)) n = _
  rw [logValue, weilTest_ofReal, weilTest_ofReal, ← Complex.ofReal_add, Complex.ofReal_re,
    integral_mul_sub_neg]
  ring

/-- Every node carries at most the self term `4L/n`. -/
theorem logValue_antiTest_le_self {n : ℕ} (hn : 1 ≤ n) :
    logValue (antiTestFn hδ hLδ).1 n ≤ 4 * L / n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hs : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn0
  have hlog : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
  have hk := correlation_antiTest_le_self hδ hLδ hlog
  have e : Real.exp (-Real.log n / 2) = 1 / Real.sqrt n := by
    have := exp_sub_half_log (n := n) (by omega) 0
    rw [Real.exp_zero, zero_sub] at this
    rw [show -Real.log n / 2 = -(Real.log n / 2) by ring, this]
  rw [e] at hk
  rw [logValue_antiTest_eq, div_le_iff₀ hs]
  calc 2 * ∫ t, antiTestReal hδ hLδ t * antiTestReal hδ hLδ (t - Real.log n)
      ≤ 2 * (2 * L * (1 / Real.sqrt n)) := by linarith
    _ = 4 * L / n * Real.sqrt n := by field_simp; rw [Real.sq_sqrt hn0.le]; ring

/-- At a node with `log n ≤ L − 2δ` the far ends pair negatively:
`L_n ≤ 4L/n − 2e^{−L/2}(L − 2δ − log n)`. -/
theorem logValue_antiTest_le {n : ℕ} (hn : 1 ≤ n) (hnL : Real.log n + 2 * δ ≤ L) :
    logValue (antiTestFn hδ hLδ).1 n ≤
      4 * L / n - 2 * Real.exp (-L / 2) * (L - 2 * δ - Real.log n) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hs : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn0
  have hlog : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
  have hk := correlation_antiTest_le hδ hLδ hlog hnL
  have e1 : Real.exp (-Real.log n / 2) = 1 / Real.sqrt n := by
    have := exp_sub_half_log (n := n) (by omega) 0
    rw [Real.exp_zero, zero_sub] at this
    rw [show -Real.log n / 2 = -(Real.log n / 2) by ring, this]
  have e2 : Real.exp (-(L - Real.log n) / 2) = Real.exp (-L / 2) * Real.sqrt n := by
    rw [show -(L - Real.log n) / 2 = -L / 2 + Real.log n / 2 by ring, exp_add_half_log (by omega)]
  rw [e1, e2] at hk
  rw [logValue_antiTest_eq, div_le_iff₀ hs]
  have : (4 * L / n - 2 * Real.exp (-L / 2) * (L - 2 * δ - Real.log n)) * Real.sqrt n =
      2 * (2 * L * (1 / Real.sqrt n) -
        Real.exp (-L / 2) * Real.sqrt n * (L - Real.log n - 2 * δ)) := by
    field_simp; rw [Real.sq_sqrt hn0.le]; ring
  rw [this]
  linarith

/-- **The antisymmetric test sees the Riesz mean with the opposite sign.** -/
theorem primeSide_antiTest_le :
    linearCombination ℝ (fun j : LogIndex => (ArithmeticFunction.vonMangoldt (j : ℕ) : ℝ))
        (logVector (antiTestFn hδ hLδ)) ≤
      4 * L * (2 + L) ^ 2 - 2 * Real.exp (-L / 2) * ∑ n ∈ Finset.Icc 1 ⌊Real.exp (L - 2 * δ)⌋₊,
        (ArithmeticFunction.vonMangoldt n : ℝ) * Real.log (Real.exp (L - 2 * δ) / n) := by
  classical
  have hL : 0 < L := by linarith
  set Y := Real.exp (L - 2 * δ)
  set N := ⌈Real.exp L⌉₊
  have hN : L ≤ Real.log N :=
    calc L = Real.log (Real.exp L) := (Real.log_exp L).symm
      _ ≤ Real.log N := Real.log_le_log (Real.exp_pos L) (Nat.le_ceil _)
  rw [primeSide_eq_sum_of_window (antiTestFn_supp hδ hLδ) hN]
  have hYN : ⌊Y⌋₊ < N := by
    have h1 : (⌊Y⌋₊ : ℝ) ≤ Y := Nat.floor_le (Real.exp_pos _).le
    have h2 : Y < Real.exp L := Real.exp_lt_exp.mpr (by linarith)
    have h3 : Real.exp L ≤ (N : ℝ) := Nat.le_ceil _
    exact_mod_cast h1.trans_lt (h2.trans_le h3)
  -- termwise: the self term everywhere, the far pairing on `[2, Y]`
  have hterm : ∀ n ∈ Finset.Ico 2 N,
      (ArithmeticFunction.vonMangoldt n : ℝ) * logValue (antiTestFn hδ hLδ).1 n ≤
        4 * L * ((ArithmeticFunction.vonMangoldt n : ℝ) / n) -
          (if n ∈ Finset.Icc 2 ⌊Y⌋₊ then 2 * Real.exp (-L / 2) *
            ((ArithmeticFunction.vonMangoldt n : ℝ) * Real.log (Y / n)) else 0) := by
    intro n hn
    have hn2 := (Finset.mem_Ico.mp hn).1
    have hΛ : (0 : ℝ) ≤ ArithmeticFunction.vonMangoldt n := ArithmeticFunction.vonMangoldt_nonneg
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    split_ifs with hY
    · have hnY : (n : ℝ) ≤ Y := (Nat.cast_le.mpr (Finset.mem_Icc.mp hY).2).trans
        (Nat.floor_le (Real.exp_pos _).le)
      have hlogY : Real.log n ≤ L - 2 * δ :=
        calc Real.log n ≤ Real.log Y := Real.log_le_log hn0 hnY
          _ = L - 2 * δ := Real.log_exp _
      have h := mul_le_mul_of_nonneg_left (logValue_antiTest_le hδ hLδ (n := n) (by omega)
        (by linarith)) hΛ
      have hlogdiv : Real.log (Y / n) = L - 2 * δ - Real.log n := by
        rw [Real.log_div (Real.exp_pos _).ne' hn0.ne', Real.log_exp]
      rw [hlogdiv]
      calc (ArithmeticFunction.vonMangoldt n : ℝ) * logValue (antiTestFn hδ hLδ).1 n
          ≤ ArithmeticFunction.vonMangoldt n *
              (4 * L / n - 2 * Real.exp (-L / 2) * (L - 2 * δ - Real.log n)) := h
        _ = _ := by ring
    · rw [sub_zero]
      calc (ArithmeticFunction.vonMangoldt n : ℝ) * logValue (antiTestFn hδ hLδ).1 n
          ≤ ArithmeticFunction.vonMangoldt n * (4 * L / n) :=
            mul_le_mul_of_nonneg_left (logValue_antiTest_le_self hδ hLδ (by omega)) hΛ
        _ = _ := by ring
  have hM : ∑ n ∈ Finset.Ico 2 N, (ArithmeticFunction.vonMangoldt n : ℝ) / n ≤ (2 + L) ^ 2 := by
    have h := sum_vonMangoldt_div_le_of_lt_exp (S := Finset.Ico 2 N) (τ := L + 1) (by linarith)
      fun n hn => by
        have hn' := Finset.mem_Ico.mp hn
        refine ⟨by omega, ?_⟩
        have h1 : ((n + 1 : ℕ) : ℝ) ≤ N := by exact_mod_cast hn'.2
        have h2 : (N : ℝ) < Real.exp L + 1 := Nat.ceil_lt_add_one (Real.exp_pos L).le
        have h3 : Real.exp L < Real.exp (L + 1) := Real.exp_lt_exp.mpr (by linarith)
        push_cast at h1
        linarith
    calc _ ≤ (1 + (L + 1)) ^ 2 := h
      _ = (2 + L) ^ 2 := by ring
  have hsub : ∑ n ∈ Finset.Ico 2 N, (if n ∈ Finset.Icc 2 ⌊Y⌋₊ then 2 * Real.exp (-L / 2) *
      ((ArithmeticFunction.vonMangoldt n : ℝ) * Real.log (Y / n)) else 0) =
      2 * Real.exp (-L / 2) * ∑ n ∈ Finset.Icc 1 ⌊Y⌋₊,
        (ArithmeticFunction.vonMangoldt n : ℝ) * Real.log (Y / n) := by
    rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr (fun n hn => by
      rw [Finset.mem_Icc] at hn; rw [Finset.mem_Ico]; omega), ← Finset.mul_sum]
    congr 1
    refine Finset.sum_subset (fun n hn => ?_) fun n hn hn2 => ?_
    · rw [Finset.mem_Icc] at hn ⊢; omega
    · have : n = 1 := by rw [Finset.mem_Icc] at hn hn2; omega
      subst this; simp
  calc ∑ n ∈ Finset.Ico 2 N, (ArithmeticFunction.vonMangoldt n : ℝ) * logValue (antiTestFn hδ hLδ).1 n
      ≤ ∑ n ∈ Finset.Ico 2 N, (4 * L * ((ArithmeticFunction.vonMangoldt n : ℝ) / n) -
          (if n ∈ Finset.Icc 2 ⌊Y⌋₊ then 2 * Real.exp (-L / 2) *
            ((ArithmeticFunction.vonMangoldt n : ℝ) * Real.log (Y / n)) else 0)) :=
        Finset.sum_le_sum hterm
    _ = 4 * L * ∑ n ∈ Finset.Ico 2 N, (ArithmeticFunction.vonMangoldt n : ℝ) / n -
          2 * Real.exp (-L / 2) * ∑ n ∈ Finset.Icc 1 ⌊Y⌋₊,
            (ArithmeticFunction.vonMangoldt n : ℝ) * Real.log (Y / n) := by
        rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hsub]
    _ ≤ _ := by nlinarith

end AntiTestDeviation

/-- `L (2 + L)² e^{−L/2} → 0`. -/
theorem tendsto_mul_two_add_sq_mul_exp_neg_half :
    Tendsto (fun L : ℝ => L * (2 + L) ^ 2 * Real.exp (-(L / 2))) atTop (𝓝 0) := by
  have hc : Tendsto (fun L : ℝ => L / 2) atTop atTop := tendsto_id.atTop_div_const two_pos
  have h1 := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp hc
  have h2 := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 2).comp hc
  have h3 := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 3).comp hc
  have := ((h1.const_mul 8).add (h2.const_mul 16)).add (h3.const_mul 8)
  simp only [mul_zero, add_zero] at this
  refine this.congr fun L => ?_
  simp only [Function.comp_apply]
  ring

/-- **Lower half of the floor asymptotics.** For every `η ∈ (0, 1]`, eventually some window
deviation is at most `−(1 − η) e^{L/2}`: the antisymmetric polar test. -/
theorem eventually_exists_windowDeviation_le {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) :
    ∀ᶠ L in atTop, ∃ x ∈ windowDeviations L, x ≤ -((1 - η) * Real.exp (L / 2)) := by
  classical
  set δ := η / 8 with hδdef
  have hδ : 0 < δ := by positivity
  obtain ⟨Y₀, hY₀1, hY₀⟩ := exists_riesz_ge (η := η / 4) (by positivity) (by linarith)
  have hsmall := tendsto_mul_two_add_sq_mul_exp_neg_half.eventually
    (Iio_mem_nhds (by positivity : (0 : ℝ) < η / 8))
  filter_upwards [hsmall, eventually_ge_atTop (Real.log Y₀ + 2 * δ + 1)] with L hL hLY
  have hlogY₀ : 0 ≤ Real.log Y₀ := Real.log_nonneg hY₀1
  have hLδ : 2 * δ < L := by linarith
  have hL0 : 0 < L := by linarith
  set f := antiTestFn hδ hLδ
  set c : WeilTestFn →₀ ℝ := Finsupp.single f 1
  have hc : ∀ g, 0 ≤ c g := fun g => by
    simp only [c]; rw [Finsupp.single_apply]; split_ifs <;> norm_num
  have hsupp : ∀ g ∈ c.support, ∃ a, ∀ u, g.1 u ≠ 0 → u ∈ Ioo a (a + L) := fun g hg => by
    have : g = f := by
      by_contra h; exact (Finsupp.mem_support_iff.mp hg) (by simp [c, Ne.symm h])
    exact ⟨0, this ▸ antiTestFn_supp hδ hLδ⟩
  have hdev : nodeArchEnergy c - weilEnergy c =
      linearCombination ℝ (fun j : LogIndex => (ArithmeticFunction.vonMangoldt (j : ℕ) : ℝ))
        (logVector f) := by
    rw [nodeArchEnergy_eq_weilEnergy_add, add_sub_cancel_left, nodeVector_single_test]
  set Y := Real.exp (L - 2 * δ)
  have hYY₀ : Y₀ ≤ Y := by
    calc Y₀ = Real.exp (Real.log Y₀) := (Real.exp_log (by linarith)).symm
      _ ≤ Y := Real.exp_le_exp.mpr (by linarith)
  have hR := hY₀ Y hYY₀
  have hP := primeSide_antiTest_le hδ hLδ
  have hmass := massOf_antiTest_le hδ hLδ
  have he : 0 < Real.exp (-L / 2) := Real.exp_pos _
  have hEL := Real.exp_pos (L / 2)
  have hYe : Real.exp (-L / 2) * Y = Real.exp (-(2 * δ)) * Real.exp (L / 2) := by
    simp only [Y]; rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  have hδe : 1 - η / 4 ≤ Real.exp (-(2 * δ)) := by
    have := Real.one_sub_le_exp_neg (2 * δ); rw [hδdef] at this ⊢; linarith
  -- the polynomial self terms are small against `e^{L/2}`
  have hinv : Real.exp (-(L / 2)) * Real.exp (L / 2) = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  have hpoly : L * (2 + L) ^ 2 ≤ η / 8 * Real.exp (L / 2) := by
    have := mul_le_mul_of_nonneg_right hL.le hEL.le
    rwa [mul_assoc, hinv, mul_one] at this
  have hLsmall : L * Real.exp (-L / 2) ≤ η / 8 := by
    have h1 : L ≤ L * (2 + L) ^ 2 := le_mul_of_one_le_right hL0.le (by nlinarith [hL0])
    have h2 : L * Real.exp (-L / 2) ≤ L * (2 + L) ^ 2 * Real.exp (-(L / 2)) := by
      rw [show -L / 2 = -(L / 2) by ring]
      exact mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
    linarith
  -- the prime side is very negative
  have hPup : nodeArchEnergy c - weilEnergy c ≤
      4 * L * (2 + L) ^ 2 - 2 * (1 - η / 4) * ((1 - η / 4) * Real.exp (L / 2)) := by
    rw [hdev]
    refine hP.trans ?_
    have h1 : 2 * Real.exp (-L / 2) * ((1 - η / 4) * Y) ≤
        2 * Real.exp (-L / 2) * ∑ n ∈ Finset.Icc 1 ⌊Y⌋₊,
          (ArithmeticFunction.vonMangoldt n : ℝ) * Real.log (Y / n) :=
      mul_le_mul_of_nonneg_left hR (by positivity)
    have h2 : 2 * (1 - η / 4) * ((1 - η / 4) * Real.exp (L / 2)) ≤
        2 * Real.exp (-L / 2) * ((1 - η / 4) * Y) := by
      have : 2 * Real.exp (-L / 2) * ((1 - η / 4) * Y) =
          2 * (1 - η / 4) * (Real.exp (-(2 * δ)) * Real.exp (L / 2)) := by rw [← hYe]; ring
      rw [this]
      have : 0 ≤ 1 - η / 4 := by linarith
      have := mul_le_mul_of_nonneg_right hδe hEL.le
      nlinarith
    linarith
  set E := Real.exp (L / 2) with hEdef
  have hF2 : 2 * (1 - η / 4) * ((1 - η / 4) * E) = (2 - η + η ^ 2 / 8) * E := by ring
  have hL1 : L ≤ L * (2 + L) ^ 2 := le_mul_of_one_le_right hL0.le (by nlinarith [hL0])
  have hF3 : L ≤ η / 8 * E := hL1.trans hpoly
  have hηE : η * E ≤ E := by nlinarith
  have hη2E : 0 ≤ η ^ 2 * E := by positivity
  have hPneg : nodeArchEnergy c - weilEnergy c < 0 := by
    rw [hF2] at hPup; linarith
  have hm : 0 < massOf c := by
    have hcheb := abs_nodeArchEnergy_sub_weilEnergy_le_chebyshev hc hL0.le hsupp
    by_contra h0
    push Not at h0
    have hm0 : massOf c = 0 := le_antisymm h0 (by
      rw [WeilOneSided.massOf, Finsupp.sum_single_index (by simp), one_mul]
      exact integral_nonneg fun u => sq_nonneg _)
    rw [hm0, mul_zero] at hcheb
    linarith [neg_abs_le (nodeArchEnergy c - weilEnergy c)]
  refine ⟨(nodeArchEnergy c - weilEnergy c) / massOf c, ⟨c, hc, hsupp, hm, rfl⟩, ?_⟩
  rw [div_le_iff₀ hm]
  -- `P ≤ −(1 − η) e^{L/2} (2 + 2L e^{−L/2}) ≤ −(1 − η) e^{L/2} ‖f‖²`
  have hMpos : 0 ≤ (1 - η) * E := mul_nonneg (by linarith) hEL.le
  have h3 : -((1 - η) * E) * (2 + 2 * L * Real.exp (-L / 2)) ≤ -((1 - η) * E) * massOf c := by
    nlinarith
  have hexp1 : E * Real.exp (-L / 2) = 1 := by
    rw [hEdef, ← Real.exp_add]; ring_nf; exact Real.exp_zero
  have hexpand : -((1 - η) * E) * (2 + 2 * L * Real.exp (-L / 2)) =
      -(2 * (1 - η) * E) - 2 * (1 - η) * L * (E * Real.exp (-L / 2)) := by ring
  rw [hexp1, mul_one] at hexpand
  have hηL : 0 ≤ η * L := by positivity
  have h4 : nodeArchEnergy c - weilEnergy c ≤ -((1 - η) * E) * (2 + 2 * L * Real.exp (-L / 2)) := by
    rw [hexpand]; rw [hF2] at hPup; linarith
  linarith

/-- The window floor `inf (A − W)/‖c‖²` over windows of length `L`. -/
def windowFloor (L : ℝ) : ℝ := sInf (windowDeviations L)

/-- **The window floor is minus the polar ceiling:** `floor(L)/e^{L/2} → −1`. -/
theorem tendsto_windowFloor_div_exp :
    Tendsto (fun L => windowFloor L / Real.exp (L / 2)) atTop (𝓝 (-1)) := by
  rw [tendsto_order]
  constructor
  · intro a ha
    set η := (-1 - a) / 2
    have hη : 0 < η := by simp only [η]; linarith
    filter_upwards [eventually_abs_windowDeviations_le hη,
      eventually_exists_windowDeviation_le (η := 1) one_pos le_rfl] with L hle ⟨x, hx, _⟩
    have hinf : -((1 + η) * Real.exp (L / 2)) ≤ windowFloor L :=
      le_csInf ⟨x, hx⟩ fun y hy => by have := hle y hy; linarith [neg_abs_le y]
    rw [lt_div_iff₀ (Real.exp_pos _)]
    have hηa : a < -(1 + η) := by simp only [η]; linarith
    nlinarith [mul_lt_mul_of_pos_right hηa (Real.exp_pos (L / 2))]
  · intro b hb
    set η := min ((b + 1) / 2) 1
    have hη : 0 < η := lt_min (by linarith) one_pos
    have hη1 : η ≤ 1 := min_le_right _ _
    have hηb : -(1 - η) < b := by
      have : η ≤ (b + 1) / 2 := min_le_left _ _
      linarith
    filter_upwards [eventually_exists_windowDeviation_le hη hη1,
      eventually_ge_atTop (0 : ℝ)] with L ⟨x, hx, hxle⟩ hL0
    have hbdd : BddBelow (windowDeviations L) :=
      ⟨-((Real.log 4 + 4) * Real.exp (L / 2) + (1 + L) ^ 2), fun y ⟨c, hc, hs, hm, hy⟩ => by
        rw [hy, le_div_iff₀ hm]
        have := abs_nodeArchEnergy_sub_weilEnergy_le_chebyshev hc hL0 hs
        linarith [neg_abs_le (nodeArchEnergy c - weilEnergy c)]⟩
    have hinf := csInf_le hbdd hx
    rw [div_lt_iff₀ (Real.exp_pos _)]
    unfold windowFloor
    nlinarith [mul_lt_mul_of_pos_right hηb (Real.exp_pos (L / 2))]

end

end GaloisForLFunctions.BiScaleUncertainty
