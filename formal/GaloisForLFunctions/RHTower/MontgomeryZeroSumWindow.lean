import GaloisForLFunctions.RHTower.LorentzianZeroMass
import GaloisForLFunctions.RHTower.HorizontalSingletonFiberCharging
import GaloisForLFunctions.RHTower.CentralReciprocalMoments

/-!
# The Lorentzian zero sum: full sum, finite window, and tails

The zero side of Montgomery's lemma at height `t` is `−2√x · S(x,t)` with
`S(x,t) := Σ_ρ x^{ρ−1/2} / (1 + (t + i(ρ − ½))²)` over all zeros of `ξ` with multiplicity.
This module splits `S` into the finite window `0 < γ ≤ T` and its complement, and bounds
every piece by the Lorentzian zero-mass estimates:

* `‖x^{ρ−1/2} L_ρ(t)‖ ≤ 16 √x /(1 + (t − γ)²)` for `x ≥ 1`;
* the window sum is `≤ 16√x · M(t)`, hence `O(√x log t)`;
* the complement, for `0 ≤ t ≤ T`, is `≤ 256 √x (C + log(2T+5)) (1/(1+T−t) + 1/(1+t))`;
* the window seen from outside `[0,T]` decays like `1/(1 + dist(t,[0,T]))` up to a logarithm;
* `S(x,·)` is continuous on every compact interval.

The window is a genuine `Finset` of multiplicity copies, so the finite-family theorems
(`montgomeryForm_eq_integral_height`) apply to it verbatim.
-/

open Complex MeasureTheory Filter Topology Set

namespace RHTower

/-! ## The finite window of zero copies -/

/-- The copies with ordinate in `(0, T]`. -/
def zeroWindowSet (T : ℝ) : Set XiZeroCopy :=
  {q : XiZeroCopy | 0 < (q.1 : ℂ).im ∧ (q.1 : ℂ).im ≤ T}

/-- The fibre of copies over one divisor point is finite. -/
theorem fiber_finite (z : ℂ) : {q : XiZeroCopy | (q.1 : ℂ) = z}.Finite := by
  by_cases hz : z ∈ (MeromorphicOn.divisor xi Set.univ).support
  · let ρ : XiDivisorSupport := ⟨z, hz⟩
    refine (Set.finite_range (fun j => (xiZeroCopyFiberEquiv ρ j).1)).subset ?_
    intro q hq
    have h : q.1 = ρ := Subtype.ext hq
    refine ⟨(xiZeroCopyFiberEquiv ρ).symm ⟨q, h⟩, ?_⟩
    simp
  · have : {q : XiZeroCopy | (q.1 : ℂ) = z} = ∅ := by
      ext q
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      intro h
      exact hz (h ▸ q.1.2)
    rw [this]; exact Set.finite_empty

theorem zeroWindowSet_finite (T : ℝ) : (zeroWindowSet T).Finite := by
  refine ((stripFinsetPos T).finite_toSet.biUnion
    (fun z _ => fiber_finite z)).subset ?_
  intro q hq
  obtain ⟨h0, hT⟩ := hq
  have hβ0 := xiZeroCopy_re_pos q
  have hβ1 := xiZeroCopy_re_lt_one q
  have hxi : xi (q.1 : ℂ) = 0 := xi_eq_zero_of_mem_divisor_support q.1
  refine Set.mem_iUnion₂.mpr ⟨(q.1 : ℂ), ?_, rfl⟩
  rw [Finset.mem_coe, mem_stripFinsetPos]
  exact ⟨hβ0, hβ1, h0, hT, hxi⟩

/-- The finite window `0 < γ ≤ T` of zero copies. -/
noncomputable def zeroWindow (T : ℝ) : Finset XiZeroCopy := (zeroWindowSet_finite T).toFinset

theorem mem_zeroWindow {T : ℝ} {q : XiZeroCopy} :
    q ∈ zeroWindow T ↔ 0 < (q.1 : ℂ).im ∧ (q.1 : ℂ).im ≤ T := by
  rw [zeroWindow, Set.Finite.mem_toFinset]; rfl

theorem coe_zeroWindow (T : ℝ) : (zeroWindow T : Set XiZeroCopy) = zeroWindowSet T := by
  rw [zeroWindow, Set.Finite.coe_toFinset]

/-! ## The zero-sum term and the full sum -/

/-- The summand `x^{ρ−1/2} / (1 + (t + i(ρ−½))²)` of the Lorentzian zero sum. -/
noncomputable def zeroSumTerm (x t : ℝ) (q : XiZeroCopy) : ℂ :=
  (x : ℂ) ^ ((q.1 : ℂ) - 1 / 2) * lorentzShift (lorentzCentre (q.1 : ℂ)) t

/-- The full Lorentzian zero sum `S(x,t) = Σ_ρ x^{ρ−1/2} / (1 + (t + i(ρ−½))²)`. -/
noncomputable def lorentzZeroSumAll (x t : ℝ) : ℂ := ∑' q : XiZeroCopy, zeroSumTerm x t q

theorem lorentzZeroSum_zeroWindow (T x t : ℝ) :
    lorentzZeroSum (zeroWindow T) (fun q : XiZeroCopy => (q.1 : ℂ)) x t
      = ∑ q ∈ zeroWindow T, zeroSumTerm x t q := rfl

/-- The Montgomery zero summand is `−2√x` times the zero-sum term. -/
theorem montgomeryZeroTerm_eq_zeroSumTerm {x : ℝ} (hx : 0 < x) (t : ℝ) (q : XiZeroCopy) :
    montgomeryZeroTerm x t q = -2 * (x : ℂ) ^ ((1 / 2 : ℝ) : ℂ) * zeroSumTerm x t q := by
  rw [montgomeryZeroTerm_eq_lorentz, cpow_eq_sqrt_mul x hx, zeroSumTerm]; ring

theorem norm_cpow_sub_half_le {x : ℝ} (hx : 1 ≤ x) (q : XiZeroCopy) :
    ‖(x : ℂ) ^ ((q.1 : ℂ) - 1 / 2)‖ ≤ Real.sqrt x := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos (by linarith), Real.sqrt_eq_rpow]
  apply Real.rpow_le_rpow_of_exponent_le hx
  have := xiZeroCopy_re_lt_one q
  simp only [Complex.sub_re, Complex.div_re, Complex.one_re]
  norm_num
  linarith

/-- `‖L_{i(ρ−½)}(t)‖ ≤ 16 /(1 + (t − γ)²)` for a zero copy `ρ`. -/
theorem norm_lorentzShift_centre_le (t : ℝ) (q : XiZeroCopy) :
    ‖lorentzShift (lorentzCentre (q.1 : ℂ)) t‖ ≤ 16 * lorentzMassTerm t q := by
  have hβ0 := xiZeroCopy_re_pos q
  have hβ1 := xiZeroCopy_re_lt_one q
  have hmem : lorentzCentre (q.1 : ℂ) ∈ unitStrip := lorentzCentre_mem_unitStrip ⟨hβ0, hβ1⟩
  refine (norm_lorentzShift_le hmem t).trans ?_
  rw [lorentzCentre_re, lorentzCentre_im, lorentzMassTerm]
  have him : |(q.1 : ℂ).re - 1 / 2| ≤ 1 / 2 := by rw [abs_le]; constructor <;> linarith
  have h1 : 1 / 2 ≤ 1 - |(q.1 : ℂ).re - 1 / 2| := by linarith
  have h2 : 4 / (1 - |(q.1 : ℂ).re - 1 / 2|) ^ 2 ≤ 16 := by
    rw [div_le_iff₀ (by positivity)]; nlinarith
  rw [show t + -(q.1 : ℂ).im = t - (q.1 : ℂ).im by ring]
  exact mul_le_mul_of_nonneg_right h2 (by positivity)

/-- `‖x^{ρ−1/2} L_ρ(t)‖ ≤ 16 √x /(1 + (t − γ)²)` for `x ≥ 1`. -/
theorem norm_zeroSumTerm_le {x : ℝ} (hx : 1 ≤ x) (t : ℝ) (q : XiZeroCopy) :
    ‖zeroSumTerm x t q‖ ≤ 16 * Real.sqrt x * lorentzMassTerm t q := by
  rw [zeroSumTerm, norm_mul]
  calc ‖(x : ℂ) ^ ((q.1 : ℂ) - 1 / 2)‖ * ‖lorentzShift (lorentzCentre (q.1 : ℂ)) t‖
      ≤ Real.sqrt x * (16 * lorentzMassTerm t q) :=
        mul_le_mul (norm_cpow_sub_half_le hx q) (norm_lorentzShift_centre_le t q)
          (norm_nonneg _) (Real.sqrt_nonneg _)
    _ = 16 * Real.sqrt x * lorentzMassTerm t q := by ring

theorem summable_zeroSumTerm {x : ℝ} (hx : 1 ≤ x) (t : ℝ) : Summable (zeroSumTerm x t) :=
  Summable.of_norm_bounded ((summable_lorentzMassTerm t).mul_left (16 * Real.sqrt x))
    (norm_zeroSumTerm_le hx t)

theorem summable_norm_zeroSumTerm {x : ℝ} (hx : 1 ≤ x) (t : ℝ) :
    Summable (fun q => ‖zeroSumTerm x t q‖) :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (norm_zeroSumTerm_le hx t)
    ((summable_lorentzMassTerm t).mul_left (16 * Real.sqrt x))

/-- The zero side of Montgomery's lemma is `−2√x · S(x,t)`. -/
theorem tsum_montgomeryZeroTerm_eq {x : ℝ} (hx : 1 ≤ x) (t : ℝ) :
    ∑' q : XiZeroCopy, montgomeryZeroTerm x t q
      = -2 * (x : ℂ) ^ ((1 / 2 : ℝ) : ℂ) * lorentzZeroSumAll x t := by
  rw [lorentzZeroSumAll, ← tsum_mul_left]
  exact tsum_congr fun q => montgomeryZeroTerm_eq_zeroSumTerm (by linarith) t q

/-! ## The split into the window and its complement -/

/-- The complement sum `Σ_{γ ∉ (0,T]} x^{ρ−1/2} L_ρ(t)`. -/
noncomputable def zeroSumOut (T x t : ℝ) : ℂ :=
  ∑' q : XiZeroCopy, (zeroWindowSet T)ᶜ.indicator (zeroSumTerm x t) q

/-- A finite sum over the window is the series of the indicator. -/
theorem sum_zeroWindow_eq_tsum_indicator {E : Type*} [AddCommGroup E] [TopologicalSpace E]
    [T2Space E] (T : ℝ) (f : XiZeroCopy → E) :
    ∑ q ∈ zeroWindow T, f q = ∑' q : XiZeroCopy, (zeroWindowSet T).indicator f q := by
  classical
  rw [tsum_eq_sum (s := zeroWindow T) (fun q hq => Set.indicator_of_notMem
    (by rwa [← coe_zeroWindow, Finset.mem_coe]) f)]
  refine Finset.sum_congr rfl fun q hq => ?_
  rw [Set.indicator_of_mem (by rwa [← coe_zeroWindow, Finset.mem_coe])]

theorem lorentzZeroSumAll_eq_window_add_out {x : ℝ} (hx : 1 ≤ x) (T t : ℝ) :
    lorentzZeroSumAll x t = ∑ q ∈ zeroWindow T, zeroSumTerm x t q + zeroSumOut T x t := by
  have hs := summable_zeroSumTerm hx t
  rw [lorentzZeroSumAll, zeroSumOut, sum_zeroWindow_eq_tsum_indicator,
    ← (hs.indicator _).tsum_add (hs.indicator _)]
  exact tsum_congr fun q => (Set.indicator_self_add_compl_apply _ _ q).symm

theorem norm_tsum_indicator_le {x : ℝ} (hx : 1 ≤ x) (t : ℝ) (A : Set XiZeroCopy) :
    ‖∑' q : XiZeroCopy, A.indicator (zeroSumTerm x t) q‖
      ≤ 16 * Real.sqrt x * ∑' q : XiZeroCopy, A.indicator (lorentzMassTerm t) q := by
  classical
  have hsum : Summable (fun q => ‖A.indicator (zeroSumTerm x t) q‖) := by
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun q => ?_)
      (summable_norm_zeroSumTerm hx t)
    by_cases hq : q ∈ A
    · rw [Set.indicator_of_mem hq]
    · rw [Set.indicator_of_notMem hq]; simp
  refine (norm_tsum_le_tsum_norm hsum).trans ?_
  rw [← tsum_mul_left]
  refine Summable.tsum_le_tsum (fun q => ?_) hsum
    (((summable_lorentzMassTerm t).indicator A).mul_left _)
  unfold Set.indicator
  split_ifs with h
  · exact norm_zeroSumTerm_le hx t q
  · simp

theorem indicator_compl_le (t : ℝ) (T : ℝ) (q : XiZeroCopy) :
    (zeroWindowSet T)ᶜ.indicator (lorentzMassTerm t) q
      ≤ {q : XiZeroCopy | (q.1 : ℂ).im ≤ 0}.indicator (lorentzMassTerm t) q
        + {q : XiZeroCopy | T < (q.1 : ℂ).im}.indicator (lorentzMassTerm t) q := by
  classical
  have hA : 0 ≤ {q : XiZeroCopy | (q.1 : ℂ).im ≤ 0}.indicator (lorentzMassTerm t) q :=
    Set.indicator_nonneg (fun q _ => lorentzMassTerm_nonneg t q) q
  have hB : 0 ≤ {q : XiZeroCopy | T < (q.1 : ℂ).im}.indicator (lorentzMassTerm t) q :=
    Set.indicator_nonneg (fun q _ => lorentzMassTerm_nonneg t q) q
  by_cases hq : q ∈ (zeroWindowSet T)ᶜ
  · rw [Set.indicator_of_mem hq]
    have hcase : (q.1 : ℂ).im ≤ 0 ∨ T < (q.1 : ℂ).im := by
      by_contra hcon
      exact hq ⟨lt_of_not_ge (fun h => hcon (Or.inl h)), le_of_not_gt (fun h => hcon (Or.inr h))⟩
    rcases hcase with h | h
    · rw [Set.indicator_of_mem (show q ∈ {q : XiZeroCopy | (q.1 : ℂ).im ≤ 0} from h)]
      linarith
    · rw [Set.indicator_of_mem (show q ∈ {q : XiZeroCopy | T < (q.1 : ℂ).im} from h)]
      linarith
  · rw [Set.indicator_of_notMem hq]
    linarith

/-- **The complement is small inside the window of heights.** For `x ≥ 1`, `0 ≤ t ≤ T`,
`‖Σ_{γ∉(0,T]} x^{ρ−1/2} L_ρ(t)‖ ≤ 256 √x (C + log(2T+5)) (1/(1+(T−t)) + 1/(1+t))`. -/
theorem norm_zeroSumOut_le {x : ℝ} (hx : 1 ≤ x) {t T : ℝ} (ht : 0 ≤ t) (htT : t ≤ T) :
    ‖zeroSumOut T x t‖ ≤ 256 * Real.sqrt x * (xiLineTwoLogDerivConstant + Real.log (2 * T + 5))
      * (1 / (1 + (T - t)) + 1 / (1 + t)) := by
  refine (norm_tsum_indicator_le hx t _).trans ?_
  have hA := tsum_indicator_le_zero_le ht htT
  have hB := tsum_indicator_gt_le ht htT
  have hsplit : ∑' q : XiZeroCopy, (zeroWindowSet T)ᶜ.indicator (lorentzMassTerm t) q
      ≤ (∑' q : XiZeroCopy, {q : XiZeroCopy | (q.1 : ℂ).im ≤ 0}.indicator (lorentzMassTerm t) q)
        + ∑' q : XiZeroCopy, {q : XiZeroCopy | T < (q.1 : ℂ).im}.indicator (lorentzMassTerm t) q := by
    rw [← ((summable_lorentzMassTerm t).indicator _).tsum_add
      ((summable_lorentzMassTerm t).indicator _)]
    exact Summable.tsum_le_tsum (indicator_compl_le t T) ((summable_lorentzMassTerm t).indicator _)
      (((summable_lorentzMassTerm t).indicator _).add ((summable_lorentzMassTerm t).indicator _))
  have hC := xiLineTwoLogDerivConstant_nonneg
  have hL : 0 ≤ Real.log (2 * T + 5) := Real.log_nonneg (by linarith)
  calc 16 * Real.sqrt x * ∑' q : XiZeroCopy, (zeroWindowSet T)ᶜ.indicator (lorentzMassTerm t) q
      ≤ 16 * Real.sqrt x * (16 * (xiLineTwoLogDerivConstant + Real.log (2 * T + 5)) / (1 + t)
          + 16 * (xiLineTwoLogDerivConstant + Real.log (2 * T + 5)) / (1 + (T - t))) := by
        gcongr
        exact hsplit.trans (add_le_add hA hB)
    _ = 256 * Real.sqrt x * (xiLineTwoLogDerivConstant + Real.log (2 * T + 5))
      * (1 / (1 + (T - t)) + 1 / (1 + t)) := by ring

/-! ## Bounds on the window sum -/

theorem norm_sum_zeroWindow_le_tsum_indicator {x : ℝ} (hx : 1 ≤ x) (T t : ℝ) :
    ‖∑ q ∈ zeroWindow T, zeroSumTerm x t q‖
      ≤ 16 * Real.sqrt x * ∑' q : XiZeroCopy, (zeroWindowSet T).indicator (lorentzMassTerm t) q := by
  rw [sum_zeroWindow_eq_tsum_indicator]
  exact norm_tsum_indicator_le hx t (zeroWindowSet T)

/-- The window sum is at most `16 √x` times the full Lorentzian mass. -/
theorem norm_sum_zeroWindow_le_mass {x : ℝ} (hx : 1 ≤ x) (T t : ℝ) :
    ‖∑ q ∈ zeroWindow T, zeroSumTerm x t q‖ ≤ 16 * Real.sqrt x * lorentzMass t := by
  refine (norm_sum_zeroWindow_le_tsum_indicator hx T t).trans ?_
  gcongr
  exact Summable.tsum_le_tsum (fun q => Set.indicator_le_self' (fun q _ => lorentzMassTerm_nonneg t q) q)
    ((summable_lorentzMassTerm t).indicator _) (summable_lorentzMassTerm t)

/-- `‖Σ_{0<γ≤T} x^{ρ−1/2} L_ρ(t)‖ ≤ 128 √x (C + log(|t| + 4))`. -/
theorem norm_sum_zeroWindow_le_log {x : ℝ} (hx : 1 ≤ x) (T t : ℝ) :
    ‖∑ q ∈ zeroWindow T, zeroSumTerm x t q‖
      ≤ 128 * Real.sqrt x * (xiLineTwoLogDerivConstant + Real.log (|t| + 4)) := by
  refine (norm_sum_zeroWindow_le_mass hx T t).trans ?_
  have := lorentzMass_le_log t
  calc 16 * Real.sqrt x * lorentzMass t
      ≤ 16 * Real.sqrt x * (8 * (xiLineTwoLogDerivConstant + Real.log (|t| + 4))) := by
        gcongr
    _ = 128 * Real.sqrt x * (xiLineTwoLogDerivConstant + Real.log (|t| + 4)) := by ring

/-- The window seen from above: for `0 ≤ T ≤ t`,
`‖Σ_{0<γ≤T} x^{ρ−1/2} L_ρ(t)‖ ≤ 256 √x (C + log(t + 5)) / (1 + (t − T))`. -/
theorem norm_sum_zeroWindow_le_of_ge {x : ℝ} (hx : 1 ≤ x) {T t : ℝ} (hT : 0 ≤ T) (hTt : T ≤ t) :
    ‖∑ q ∈ zeroWindow T, zeroSumTerm x t q‖
      ≤ 256 * Real.sqrt x * (xiLineTwoLogDerivConstant + Real.log (t + 5)) / (1 + (t - T)) := by
  refine (norm_sum_zeroWindow_le_tsum_indicator hx T t).trans ?_
  have hmono : ∑' q : XiZeroCopy, (zeroWindowSet T).indicator (lorentzMassTerm t) q
      ≤ ∑' q : XiZeroCopy, {q : XiZeroCopy | (q.1 : ℂ).im ≤ T}.indicator (lorentzMassTerm t) q := by
    refine Summable.tsum_le_tsum (fun q => ?_) ((summable_lorentzMassTerm t).indicator _)
      ((summable_lorentzMassTerm t).indicator _)
    exact Set.indicator_le_indicator_of_subset (fun q hq => hq.2) (lorentzMassTerm_nonneg t) q
  have := tsum_indicator_le_le hT hTt
  calc 16 * Real.sqrt x * ∑' q : XiZeroCopy, (zeroWindowSet T).indicator (lorentzMassTerm t) q
      ≤ 16 * Real.sqrt x * (16 * (xiLineTwoLogDerivConstant + Real.log (t + 5)) / (1 + (t - T))) := by
        gcongr
        exact hmono.trans this
    _ = 256 * Real.sqrt x * (xiLineTwoLogDerivConstant + Real.log (t + 5)) / (1 + (t - T)) := by
        ring

/-- The window seen from below: for `t ≤ 0`,
`‖Σ_{0<γ≤T} x^{ρ−1/2} L_ρ(t)‖ ≤ 256 √x (C + log(|t| + 5)) / (1 + |t|)`. -/
theorem norm_sum_zeroWindow_le_of_le {x : ℝ} (hx : 1 ≤ x) {T t : ℝ} (ht : t ≤ 0) :
    ‖∑ q ∈ zeroWindow T, zeroSumTerm x t q‖
      ≤ 256 * Real.sqrt x * (xiLineTwoLogDerivConstant + Real.log (|t| + 5)) / (1 + |t|) := by
  refine (norm_sum_zeroWindow_le_tsum_indicator hx T t).trans ?_
  have hmono : ∑' q : XiZeroCopy, (zeroWindowSet T).indicator (lorentzMassTerm t) q
      ≤ ∑' q : XiZeroCopy, {q : XiZeroCopy | 0 < (q.1 : ℂ).im}.indicator (lorentzMassTerm t) q := by
    refine Summable.tsum_le_tsum (fun q => ?_) ((summable_lorentzMassTerm t).indicator _)
      ((summable_lorentzMassTerm t).indicator _)
    exact Set.indicator_le_indicator_of_subset (fun q hq => hq.1) (lorentzMassTerm_nonneg t) q
  have := tsum_indicator_gt_zero_le ht
  calc 16 * Real.sqrt x * ∑' q : XiZeroCopy, (zeroWindowSet T).indicator (lorentzMassTerm t) q
      ≤ 16 * Real.sqrt x * (16 * (xiLineTwoLogDerivConstant + Real.log (|t| + 5)) / (1 + |t|)) := by
        gcongr
        exact hmono.trans this
    _ = 256 * Real.sqrt x * (xiLineTwoLogDerivConstant + Real.log (|t| + 5)) / (1 + |t|) := by
        ring

/-! ## Continuity of the full sum on compact intervals -/

/-- On `t ∈ [k, k+1]`, `1/(1 + (t − γ)²) ≤ 3/(1 + (k − γ)²)`. -/
theorem lorentzMassTerm_le_of_mem_Icc {t : ℝ} {k : ℝ} (hk : k ≤ t) (hk1 : t ≤ k + 1)
    (q : XiZeroCopy) : lorentzMassTerm t q ≤ 3 * lorentzMassTerm k q := by
  unfold lorentzMassTerm
  rw [mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
  have hk1' : t - k ≤ 1 := by linarith
  nlinarith [sq_nonneg ((t - (q.1 : ℂ).im) + (t - k)),
    mul_nonneg (sub_nonneg.mpr hk) (sub_nonneg.mpr hk1')]

/-- A summable majorant of the zero-sum terms, uniform on `[0, T]`. -/
noncomputable def windowMajorant (x T : ℝ) (q : XiZeroCopy) : ℝ :=
  48 * Real.sqrt x * ∑ k ∈ Finset.range (⌊T⌋₊ + 1), lorentzMassTerm (k : ℝ) q

theorem summable_windowMajorant (x T : ℝ) : Summable (windowMajorant x T) := by
  have h : Summable (fun q : XiZeroCopy =>
      ∑ k ∈ Finset.range (⌊T⌋₊ + 1), lorentzMassTerm (k : ℝ) q) :=
    summable_sum (f := fun (k : ℕ) (q : XiZeroCopy) => lorentzMassTerm (k : ℝ) q)
      (fun k _ => summable_lorentzMassTerm (k : ℝ))
  exact h.mul_left (48 * Real.sqrt x)

theorem norm_zeroSumTerm_le_windowMajorant {x : ℝ} (hx : 1 ≤ x) {T t : ℝ} (ht : 0 ≤ t)
    (htT : t ≤ T) (q : XiZeroCopy) : ‖zeroSumTerm x t q‖ ≤ windowMajorant x T q := by
  refine (norm_zeroSumTerm_le hx t q).trans ?_
  unfold windowMajorant
  set k : ℕ := ⌊t⌋₊ with hk
  have hkt : (k : ℝ) ≤ t := Nat.floor_le ht
  have htk : t ≤ (k : ℝ) + 1 := (Nat.lt_floor_add_one t).le
  have hkmem : k ∈ Finset.range (⌊T⌋₊ + 1) := by
    rw [Finset.mem_range, Nat.lt_succ_iff]
    exact Nat.floor_le_floor htT
  have h3 := lorentzMassTerm_le_of_mem_Icc hkt htk q
  have hle : lorentzMassTerm (k : ℝ) q ≤ ∑ j ∈ Finset.range (⌊T⌋₊ + 1), lorentzMassTerm (j : ℝ) q :=
    Finset.single_le_sum (f := fun j : ℕ => lorentzMassTerm (j : ℝ) q)
      (fun j _ => lorentzMassTerm_nonneg (j : ℝ) q) hkmem
  have hsx : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
  nlinarith [mul_nonneg hsx (lorentzMassTerm_nonneg t q), mul_nonneg hsx (lorentzMassTerm_nonneg (k : ℝ) q)]


theorem continuousOn_lorentzZeroSumAll {x : ℝ} (hx : 1 ≤ x) (T : ℝ) :
    ContinuousOn (lorentzZeroSumAll x) (Set.Icc 0 T) := by
  refine continuousOn_tsum (fun q => ?_) (summable_windowMajorant x T)
    (fun q t ht => norm_zeroSumTerm_le_windowMajorant hx ht.1 ht.2 q)
  have hβ0 := xiZeroCopy_re_pos q
  have hβ1 := xiZeroCopy_re_lt_one q
  exact (continuous_const.mul (continuous_lorentzShift (lorentzCentre_mem_unitStrip ⟨hβ0, hβ1⟩))).continuousOn

end RHTower
