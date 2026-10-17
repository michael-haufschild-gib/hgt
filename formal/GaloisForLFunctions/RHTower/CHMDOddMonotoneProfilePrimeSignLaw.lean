import GaloisForLFunctions.RHTower.CHMDOddPrimeCrossSignBonusAndWindowPositivity

/-!
# The monotone prime-sign law on the one-signed odd cone

On the one-signed odd cone the prime `n` enters the Doob energy through the difference
`B_n(g) − C_n(g)` of the opposite-side convolution `2 (Λ(n)/√n) ∫_0^{log n} g(s) g(log n − s) ds`
and the same-side autocorrelation `4 (Λ(n)/√n) ∫_0^∞ g(s) g(s + log n) ds` of the profile
`g = Θ|v|`.  For a profile that vanishes beyond `a` and is nonincreasing on `[c, a]` (a unimodal
profile with mode at or before `c`; an odd test vanishes at the origin, so `c > 0` is the
natural case), the convolution dominates twice the autocorrelation at every lag
`u ≥ max(2a/3, (a + c)/2)`:

`∫_0^u g(s) g(u − s) ds ≥ 2 ∫_0^∞ g(s) g(s + u) ds`.

Hence every prime power with `log n` beyond that threshold helps, and only the primes below it can
hurt.  The constant `2/3` is sharp: for the indicator profile of `[0, a]` (`c = 0`) the difference
equals `3u − 2a`.  Consequences: on a support of half-width `a ≤ (3/2) log 2` with mode
`c ≤ 2 log 2 − a`, every prime term is nonnegative and the energy dominates the Lévy form plus the
cross-sign bonus, extending the unconditional window from `2 log 2` to `3 log 2` on the unimodal
sub-cone; in general the energy dominates the Lévy form, the bonus, and the finitely many prime
terms below the threshold.  Models of the hypotheses: `v(x) = sign(x) p(|x|)/Θ(x)` with `p`
any `C²` profile vanishing to second order at `0`, nonincreasing on `[c, a]` and zero beyond `a`.
-/

open MeasureTheory Set Filter Topology
open scoped InnerProductSpace

namespace RHTower.CHMDPolar
open CHMDDoobGraph

/-! ## The convolution–autocorrelation comparison for monotone profiles -/

/-- **Convolution dominates twice the autocorrelation beyond two thirds of the support and beyond
the midpoint of the mode and the edge.** -/
theorem two_mul_integral_autocorr_le_integral_conv {g : ℝ → ℝ} (hg : Continuous g)
    (hgc : HasCompactSupport g) (hg0 : ∀ s, 0 ≤ g s) {a c : ℝ} (ha : 0 < a)
    (hga : ∀ s, a ≤ s → g s = 0) (hmono : AntitoneOn g (Icc c a)) {u : ℝ}
    (hu : 2 * a / 3 ≤ u) (huc : (a + c) / 2 ≤ u) :
    2 * ∫ s in Ioi (0 : ℝ), g s * g (s + u) ≤ ∫ s in (0 : ℝ)..u, g s * g (u - s) := by
  have hu0 : 0 ≤ u := by linarith
  have hF : Continuous fun s => g s * g (u - s) := by fun_prop
  have hG : Continuous fun s => g s * g (s + u) := by fun_prop
  have hGc : HasCompactSupport fun s => g s * g (s + u) := by
    have h1 : HasCompactSupport fun s => g (s + u) := hgc.comp_homeomorph (Homeomorph.addRight u)
    exact h1.mul_left
  have hGi : Integrable fun s => g s * g (s + u) := hG.integrable_of_hasCompactSupport hGc
  rcases le_or_gt a u with hau | hau
  · -- beyond the support the autocorrelation vanishes
    have h0 : ∫ s in Ioi (0 : ℝ), g s * g (s + u) = 0 :=
      setIntegral_eq_zero_of_forall_eq_zero fun s hs => by
        rw [hga (s + u) (by linarith [mem_Ioi.mp hs]), mul_zero]
    rw [h0, mul_zero]
    exact intervalIntegral.integral_nonneg hu0 fun s _ => mul_nonneg (hg0 _) (hg0 _)
  · set b := a - u with hb
    have hb0 : 0 ≤ b := by linarith
    have hbu : b ≤ u - b := by linarith
    -- the autocorrelation lives on `[0, b]`
    have hauto : ∫ s in Ioi (0 : ℝ), g s * g (s + u) = ∫ s in (0 : ℝ)..b, g s * g (s + u) := by
      have h0 : ∫ s in Ioi b, g s * g (s + u) = 0 :=
        setIntegral_eq_zero_of_forall_eq_zero fun s hs => by
          rw [hga (s + u) (by linarith [mem_Ioi.mp hs]), mul_zero]
      rw [← Ioc_union_Ioi_eq_Ioi hb0, setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
        hGi.integrableOn hGi.integrableOn, intervalIntegral.integral_of_le hb0, h0, add_zero]
    -- split the convolution into `[0,b] ∪ [b, u−b] ∪ [u−b, u]`
    have hI : ∀ c d : ℝ, IntervalIntegrable (fun s => g s * g (u - s)) volume c d :=
      fun c d => hF.intervalIntegrable c d
    have hsplit : ∫ s in (0 : ℝ)..u, g s * g (u - s) =
        (∫ s in (0 : ℝ)..b, g s * g (u - s)) + (∫ s in b..(u - b), g s * g (u - s)) +
          ∫ s in (u - b)..u, g s * g (u - s) := by
      rw [intervalIntegral.integral_add_adjacent_intervals (hI 0 b) (hI b (u - b)),
        intervalIntegral.integral_add_adjacent_intervals (hI 0 (u - b)) (hI (u - b) u)]
    -- the far piece is the reflection of the near piece
    have hrefl : ∫ s in (u - b)..u, g s * g (u - s) = ∫ s in (0 : ℝ)..b, g s * g (u - s) := by
      have h := intervalIntegral.integral_comp_sub_left (a := u - b) (b := u)
        (fun s => g s * g (u - s)) u
      beta_reduce at h
      rw [sub_self, sub_sub_cancel] at h
      rw [← h]
      refine intervalIntegral.integral_congr fun s _ => ?_
      rw [sub_sub_cancel, mul_comm]
    -- the middle piece is nonnegative
    have hmid : 0 ≤ ∫ s in b..(u - b), g s * g (u - s) :=
      intervalIntegral.integral_nonneg hbu fun s _ => mul_nonneg (hg0 _) (hg0 _)
    -- on `[0, b]` monotonicity compares the two integrands
    have hcmp : ∫ s in (0 : ℝ)..b, g s * g (s + u) ≤ ∫ s in (0 : ℝ)..b, g s * g (u - s) := by
      refine intervalIntegral.integral_mono_on hb0 (hG.intervalIntegrable _ _) (hI 0 b)
        fun s hs => ?_
      refine mul_le_mul_of_nonneg_left ?_ (hg0 s)
      refine hmono ⟨by linarith [hs.1, hs.2], by linarith [hs.1, hs.2]⟩
        ⟨by linarith [hs.1, hs.2], by linarith [hs.1, hs.2]⟩ (by linarith [hs.1])
    rw [hauto, hsplit, hrefl]
    linarith

/-! ## The prime-sign law -/

/-- **Every prime power beyond the threshold helps**: `C_n(g) ≤ B_n(g)` whenever
`log n ≥ max(2a/3, (a + c)/2)` for a profile nonincreasing on `[c, a]` and vanishing beyond `a`. -/
theorem sameSideCross_le_oppositeSideBonus_of_antitoneOn {g : ℝ → ℝ} (hg : Continuous g)
    (hgc : HasCompactSupport g) (hg0 : ∀ s, 0 ≤ g s) {a c : ℝ} (ha : 0 < a)
    (hga : ∀ s, a ≤ s → g s = 0) (hmono : AntitoneOn g (Icc c a)) {n : ℕ}
    (hn : 2 * a / 3 ≤ Real.log n) (hnc : (a + c) / 2 ≤ Real.log n) :
    sameSideCross g n ≤ oppositeSideBonus g n := by
  unfold sameSideCross oppositeSideBonus
  have h := two_mul_integral_autocorr_le_integral_conv hg hgc hg0 ha hga hmono hn hnc
  have hw := vonMangoldtAtom_nonneg n
  have := mul_le_mul_of_nonneg_left h hw
  linarith

/-- The Doob profile of a one-signed odd test is a continuous nonnegative compactly supported
function vanishing beyond the half-width of the support. -/
theorem phiDoobTest_abs_vanish {v : ℝ → ℝ} {L : ℝ}
    (hsupp : ∀ x ∉ Ioo (-(L / 2)) (L / 2), v x = 0) {s : ℝ} (hs : L / 2 ≤ s) :
    phiDoobTest (fun y => |v y|) s = 0 := by
  show riemannKernelReal s * |v s| = 0
  rw [hsupp s (fun h => by linarith [h.2]), abs_zero, mul_zero]

/-- **The unimodal prime-sign law on the one-signed odd cone**: for a one-signed odd test of support
`(−L/2, L/2)` whose Doob profile `Θ|v|` is nonincreasing on `[c, L/2]`, every prime power with
`log n ≥ max(L/3, (L/2 + c)/2)` contributes nonnegatively, so the energy dominates the Lévy form,
the cross-sign bonus and the finitely many prime terms below the threshold:
`E(v) ≥ Λ_∞(Θ|v|) + 4·bonus(Θ|v|) + Σ_{n < N} (B_n − C_n)` for every `N` beyond the threshold. -/
theorem levy_abs_add_bonus_add_sum_le_sourceEnergy_of_antitoneOn (v : ℝ → ℝ)
    (hv : ContDiff ℝ 2 v) (hvc : HasCompactSupport v) (hodd : ∀ x, v (-x) = -v x)
    (hpos : ∀ x, 0 ≤ x → 0 ≤ v x) {L c : ℝ} (hL : 0 < L)
    (hsupp : ∀ x ∉ Ioo (-(L / 2)) (L / 2), v x = 0)
    (hmono : AntitoneOn (phiDoobTest fun y => |v y|) (Icc c (L / 2))) {N : ℕ}
    (hN : L / 3 ≤ Real.log N) (hNc : (L / 2 + c) / 2 ≤ Real.log N) :
    weilLevyForm (phiDoobTest fun y => |v y|) + 4 * crossSignBonus (phiDoobTest fun y => |v y|) +
        ∑ n ∈ Finset.range N, (oppositeSideBonus (phiDoobTest fun y => |v y|) n -
          sameSideCross (phiDoobTest fun y => |v y|) n) ≤
      sourceEnergy (compactLift v hv hvc) := by
  have hgc : Continuous (phiDoobTest fun y => |v y|) :=
    continuous_riemannKernelReal.mul hv.continuous.abs
  have hgcs : HasCompactSupport (phiDoobTest fun y => |v y|) :=
    hasCompactSupport_phiDoobTest (hvc.comp_left abs_zero)
  have hg0 : ∀ s, 0 ≤ phiDoobTest (fun y => |v y|) s :=
    fun s => mul_nonneg (riemannKernelReal_pos s).le (abs_nonneg _)
  have hsum : Summable fun n : ℕ => oppositeSideBonus (phiDoobTest fun y => |v y|) n -
      sameSideCross (phiDoobTest fun y => |v y|) n := by
    have h := (summable_integral_phiDoobPrimeCross hv.continuous hvc).neg
    refine h.congr fun n => ?_
    exact neg_integral_phiDoobPrimeCross_eq v hv.continuous hvc hodd hpos n
  rw [sourceEnergy_eq_levy_abs_add_bonus_add_tsum_split v hv hvc hodd hpos]
  refine add_le_add le_rfl (hsum.sum_le_tsum (Finset.range N) fun n hn => ?_)
  have hnN : N ≤ n := by simpa using hn
  have hNpos : 0 < N := by
    by_contra h0
    have : N = 0 := by omega
    rw [this] at hN
    simp at hN
    linarith
  have hlog : Real.log N ≤ Real.log n :=
    Real.log_le_log (by exact_mod_cast hNpos) (by exact_mod_cast hnN)
  refine sub_nonneg.mpr (sameSideCross_le_oppositeSideBonus_of_antitoneOn hgc hgcs hg0
    (by linarith : 0 < L / 2) (fun s hs => phiDoobTest_abs_vanish hsupp hs) hmono ?_ ?_)
  · linarith
  · linarith

/-- **The unimodal window `3 log 2`**: for a one-signed odd test of support `(−L/2, L/2)` with
`L ≤ 3 log 2` whose Doob profile is nonincreasing on `[c, L/2]` with `c ≤ 2 log 2 − L/2`, every
prime term is nonnegative and the energy dominates the Lévy form plus the cross-sign bonus. -/
theorem levy_abs_add_bonus_le_sourceEnergy_of_antitoneOn_three_log_two (v : ℝ → ℝ)
    (hv : ContDiff ℝ 2 v) (hvc : HasCompactSupport v) (hodd : ∀ x, v (-x) = -v x)
    (hpos : ∀ x, 0 ≤ x → 0 ≤ v x) {L c : ℝ} (hL : 0 < L)
    (hsupp : ∀ x ∉ Ioo (-(L / 2)) (L / 2), v x = 0)
    (hmono : AntitoneOn (phiDoobTest fun y => |v y|) (Icc c (L / 2)))
    (hL2 : L ≤ 3 * Real.log 2) (hc : (L / 2 + c) / 2 ≤ Real.log 2) :
    weilLevyForm (phiDoobTest fun y => |v y|) + 4 * crossSignBonus (phiDoobTest fun y => |v y|) ≤
      sourceEnergy (compactLift v hv hvc) := by
  have h := levy_abs_add_bonus_add_sum_le_sourceEnergy_of_antitoneOn v hv hvc hodd hpos hL hsupp
    hmono (N := 2) (by push_cast; linarith) (by push_cast; linarith)
  have h2 : ∑ n ∈ Finset.range 2, (oppositeSideBonus (phiDoobTest fun y => |v y|) n -
      sameSideCross (phiDoobTest fun y => |v y|) n) = 0 := by
    rw [Finset.sum_range_succ, Finset.sum_range_one]
    unfold oppositeSideBonus sameSideCross
    rw [vonMangoldtAtom_eq_zero_of_lt_two (n := 0) (by norm_num),
      vonMangoldtAtom_eq_zero_of_lt_two (n := 1) (by norm_num)]
    ring
  rw [h2, add_zero] at h
  exact h

/-! ## Sharpness of the threshold: the indicator profile -/

/-- For the indicator profile of `[0, a]` the convolution at lag `u ∈ [0, a]` equals `u`. -/
theorem integral_conv_indicator {a u : ℝ} (hu0 : 0 ≤ u) (hua : u ≤ a) :
    ∫ s in (0 : ℝ)..u, (Icc 0 a).indicator (fun _ => (1 : ℝ)) s *
      (Icc 0 a).indicator (fun _ => (1 : ℝ)) (u - s) = u := by
  have h : ∀ s ∈ uIcc (0 : ℝ) u, (Icc 0 a).indicator (fun _ => (1 : ℝ)) s *
      (Icc 0 a).indicator (fun _ => (1 : ℝ)) (u - s) = 1 := by
    intro s hs
    rw [uIcc_of_le hu0] at hs
    rw [indicator_of_mem (show s ∈ Icc 0 a from ⟨hs.1, by linarith [hs.2]⟩),
      indicator_of_mem (show u - s ∈ Icc 0 a from ⟨by linarith [hs.2], by linarith [hs.1]⟩),
      mul_one]
  rw [intervalIntegral.integral_congr h]
  simp

/-- For the indicator profile of `[0, a]` the autocorrelation at lag `u ∈ [0, a]` equals `a − u`. -/
theorem integral_autocorr_indicator {a u : ℝ} (hu0 : 0 ≤ u) (hua : u ≤ a) :
    ∫ s in Ioi (0 : ℝ), (Icc 0 a).indicator (fun _ => (1 : ℝ)) s *
      (Icc 0 a).indicator (fun _ => (1 : ℝ)) (s + u) = a - u := by
  have h : ∀ s ∈ Ioi (0 : ℝ), (Icc 0 a).indicator (fun _ => (1 : ℝ)) s *
      (Icc 0 a).indicator (fun _ => (1 : ℝ)) (s + u) =
        (Ioc 0 (a - u)).indicator (fun _ => (1 : ℝ)) s := by
    intro s hs
    have hs0 : 0 < s := hs
    by_cases hsb : s ≤ a - u
    · rw [indicator_of_mem (show s ∈ Icc 0 a from ⟨hs0.le, by linarith⟩),
        indicator_of_mem (show s + u ∈ Icc 0 a from ⟨by linarith, by linarith⟩),
        indicator_of_mem (show s ∈ Ioc 0 (a - u) from ⟨hs0, hsb⟩), mul_one]
    · rw [not_le] at hsb
      rw [indicator_of_notMem (fun h : s + u ∈ Icc 0 a => by linarith [h.2]), mul_zero,
        indicator_of_notMem (fun h : s ∈ Ioc 0 (a - u) => by linarith [h.2])]
  rw [setIntegral_congr_fun measurableSet_Ioi h, setIntegral_indicator measurableSet_Ioc]
  have hinter : Ioi (0 : ℝ) ∩ Ioc 0 (a - u) = Ioc 0 (a - u) := by
    ext s
    simp only [mem_inter_iff, mem_Ioi, mem_Ioc]
    tauto
  rw [hinter, setIntegral_const, Real.volume_real_Ioc, smul_eq_mul, mul_one, sub_zero,
    max_eq_left (by linarith)]

/-- **Sharpness**: for the indicator profile the convolution minus twice the autocorrelation at
lag `u ∈ [0, a]` is `3u − 2a`, negative exactly below the threshold `u = 2a/3`. -/
theorem conv_sub_two_mul_autocorr_indicator {a u : ℝ} (hu0 : 0 ≤ u) (hua : u ≤ a) :
    (∫ s in (0 : ℝ)..u, (Icc 0 a).indicator (fun _ => (1 : ℝ)) s *
        (Icc 0 a).indicator (fun _ => (1 : ℝ)) (u - s)) -
      2 * ∫ s in Ioi (0 : ℝ), (Icc 0 a).indicator (fun _ => (1 : ℝ)) s *
        (Icc 0 a).indicator (fun _ => (1 : ℝ)) (s + u) = 3 * u - 2 * a := by
  rw [integral_conv_indicator hu0 hua, integral_autocorr_indicator hu0 hua]
  ring


/-! ## Sharpness of the mode threshold: the two-step profile -/

/-- The two-step profile: `M` on `[0, 1)`, `1` on `[1, 2]`, zero elsewhere (mode `c = 1`, support
`a = 2`, so the two thresholds are `2a/3 = 4/3` and `(a + c)/2 = 3/2`). -/
noncomputable def twoStepProfile (M : ℝ) (s : ℝ) : ℝ :=
  M * (Ico (0 : ℝ) 1).indicator (fun _ => (1 : ℝ)) s + (Icc (1 : ℝ) 2).indicator (fun _ => (1 : ℝ)) s

theorem twoStepProfile_of_mem_Ico {M s : ℝ} (h : s ∈ Ico (0 : ℝ) 1) : twoStepProfile M s = M := by
  unfold twoStepProfile
  rw [indicator_of_mem h, indicator_of_notMem (fun h' : s ∈ Icc (1 : ℝ) 2 => by
    linarith [h.2, h'.1])]
  ring

theorem twoStepProfile_of_mem_Icc {M s : ℝ} (h : s ∈ Icc (1 : ℝ) 2) : twoStepProfile M s = 1 := by
  unfold twoStepProfile
  rw [indicator_of_mem h, indicator_of_notMem (fun h' : s ∈ Ico (0 : ℝ) 1 => by
    linarith [h.1, h'.2])]
  ring

theorem twoStepProfile_of_two_lt {M s : ℝ} (h : 2 < s) : twoStepProfile M s = 0 := by
  unfold twoStepProfile
  rw [indicator_of_notMem (fun h' : s ∈ Icc (1 : ℝ) 2 => by linarith [h'.2]),
    indicator_of_notMem (fun h' : s ∈ Ico (0 : ℝ) 1 => by linarith [h'.2])]
  ring

theorem measurable_twoStepProfile (M : ℝ) : Measurable (twoStepProfile M) := by
  unfold twoStepProfile
  exact (measurable_const.mul (measurable_const.indicator measurableSet_Ico)).add
    (measurable_const.indicator measurableSet_Icc)

theorem abs_twoStepProfile_le (M s : ℝ) : |twoStepProfile M s| ≤ |M| + 1 := by
  unfold twoStepProfile
  have h1 : |(Ico (0 : ℝ) 1).indicator (fun _ => (1 : ℝ)) s| ≤ 1 := by
    by_cases h : s ∈ Ico (0 : ℝ) 1 <;> simp [h]
  have h2 : |(Icc (1 : ℝ) 2).indicator (fun _ => (1 : ℝ)) s| ≤ 1 := by
    by_cases h : s ∈ Icc (1 : ℝ) 2 <;> simp [h]
  refine (abs_add_le _ _).trans (add_le_add ?_ h2)
  rw [abs_mul]
  exact mul_le_of_le_one_right (abs_nonneg _) h1

theorem intervalIntegrable_twoStepProfile_mul (M : ℝ) {φ : ℝ → ℝ} (hφ : Measurable φ)
    (c d : ℝ) :
    IntervalIntegrable (fun s => twoStepProfile M s * twoStepProfile M (φ s)) volume c d := by
  rw [intervalIntegrable_iff]
  refine Measure.integrableOn_of_bounded (M := (|M| + 1) ^ 2) measure_Ioc_lt_top.ne
    ((measurable_twoStepProfile M).mul
      ((measurable_twoStepProfile M).comp hφ)).aestronglyMeasurable (ae_of_all _ fun s => ?_)
  rw [Real.norm_eq_abs, abs_mul, sq]
  exact mul_le_mul (abs_twoStepProfile_le _ _) (abs_twoStepProfile_le _ _) (abs_nonneg _)
    (by positivity)

/-- The convolution of the two-step profile at a lag `u ∈ (1, 3/2)`. -/
theorem integral_conv_twoStepProfile {M u : ℝ} (hu1 : 1 < u) (hu2 : u < 3 / 2) :
    ∫ s in (0 : ℝ)..u, twoStepProfile M s * twoStepProfile M (u - s) =
      2 * M * (u - 1) + M ^ 2 * (2 - u) := by
  have hI : ∀ c d : ℝ, IntervalIntegrable
      (fun s => twoStepProfile M s * twoStepProfile M (u - s)) volume c d :=
    fun c d => intervalIntegrable_twoStepProfile_mul M (φ := fun s => u - s) (by fun_prop) c d
  rw [← intervalIntegral.integral_add_adjacent_intervals (hI 0 (u - 1)) (hI (u - 1) u),
    ← intervalIntegral.integral_add_adjacent_intervals (hI (u - 1) 1) (hI 1 u)]
  have h1 : ∫ s in (0 : ℝ)..(u - 1), twoStepProfile M s * twoStepProfile M (u - s) =
      (u - 1) * M := by
    have hpt : EqOn (fun s => twoStepProfile M s * twoStepProfile M (u - s)) (fun _ => M)
        (uIcc 0 (u - 1)) := by
      intro s hs
      rw [uIcc_of_le (by linarith)] at hs
      simp only
      rw [twoStepProfile_of_mem_Ico ⟨hs.1, by linarith [hs.2]⟩,
        twoStepProfile_of_mem_Icc ⟨by linarith [hs.2], by linarith [hs.1]⟩, mul_one]
    rw [intervalIntegral.integral_congr hpt, intervalIntegral.integral_const, smul_eq_mul, sub_zero]
  have h2 : ∫ s in (u - 1)..1, twoStepProfile M s * twoStepProfile M (u - s) =
      (2 - u) * M ^ 2 := by
    have hpt : ∀ᵐ x ∂(volume : Measure ℝ), x ∈ uIoc (u - 1) 1 →
        twoStepProfile M x * twoStepProfile M (u - x) = M ^ 2 := by
      filter_upwards [Measure.ae_ne volume (1 : ℝ)] with x hx1 hx
      rw [uIoc_of_le (by linarith)] at hx
      have hx1' : x < 1 := lt_of_le_of_ne hx.2 hx1
      rw [twoStepProfile_of_mem_Ico ⟨by linarith [hx.1], hx1'⟩,
        twoStepProfile_of_mem_Ico ⟨by linarith, by linarith [hx.1]⟩, sq]
    rw [intervalIntegral.integral_congr_ae hpt, intervalIntegral.integral_const, smul_eq_mul,
      show (1 : ℝ) - (u - 1) = 2 - u by ring]
  have h3 : ∫ s in (1 : ℝ)..u, twoStepProfile M s * twoStepProfile M (u - s) = (u - 1) * M := by
    have hpt : EqOn (fun s => twoStepProfile M s * twoStepProfile M (u - s)) (fun _ => M)
        (uIcc 1 u) := by
      intro s hs
      rw [uIcc_of_le hu1.le] at hs
      simp only
      rw [twoStepProfile_of_mem_Icc ⟨hs.1, by linarith [hs.2]⟩,
        twoStepProfile_of_mem_Ico ⟨by linarith [hs.2], by linarith [hs.1]⟩, one_mul]
    rw [intervalIntegral.integral_congr hpt, intervalIntegral.integral_const, smul_eq_mul]
  rw [h1, h2, h3]
  ring

/-- The autocorrelation of the two-step profile at a lag `u ∈ (1, 3/2)`. -/
theorem integral_autocorr_twoStepProfile {M u : ℝ} (hu1 : 1 < u) (hu2 : u < 3 / 2) :
    ∫ s in Ioi (0 : ℝ), twoStepProfile M s * twoStepProfile M (s + u) = M * (2 - u) := by
  have h : ∀ s ∈ Ioi (0 : ℝ), twoStepProfile M s * twoStepProfile M (s + u) =
      M * (Ioc 0 (2 - u)).indicator (fun _ => (1 : ℝ)) s := by
    intro s hs
    have hs0 : 0 < s := hs
    by_cases hsb : s ≤ 2 - u
    · rw [twoStepProfile_of_mem_Ico ⟨hs0.le, by linarith⟩,
        twoStepProfile_of_mem_Icc ⟨by linarith, by linarith⟩,
        indicator_of_mem (show s ∈ Ioc 0 (2 - u) from ⟨hs0, hsb⟩)]
    · rw [not_le] at hsb
      rw [twoStepProfile_of_two_lt (s := s + u) (by linarith), mul_zero,
        indicator_of_notMem (fun h : s ∈ Ioc 0 (2 - u) => by linarith [h.2]), mul_zero]
  rw [setIntegral_congr_fun measurableSet_Ioi h, integral_const_mul,
    setIntegral_indicator measurableSet_Ioc]
  have hinter : Ioi (0 : ℝ) ∩ Ioc 0 (2 - u) = Ioc 0 (2 - u) := by
    ext s
    simp only [mem_inter_iff, mem_Ioi, mem_Ioc]
    tauto
  rw [hinter, setIntegral_const, Real.volume_real_Ioc, smul_eq_mul, mul_one, sub_zero,
    max_eq_left (by linarith)]

/-- **Sharpness of the mode threshold**: for the two-step profile (`a = 2`, `c = 1`) and a lag
`u ∈ (1, 3/2)`, the convolution minus twice the autocorrelation equals
`−M (6 − 4u − M (2 − u))`. -/
theorem conv_sub_two_mul_autocorr_twoStepProfile {M u : ℝ} (hu1 : 1 < u) (hu2 : u < 3 / 2) :
    (∫ s in (0 : ℝ)..u, twoStepProfile M s * twoStepProfile M (u - s)) -
      2 * ∫ s in Ioi (0 : ℝ), twoStepProfile M s * twoStepProfile M (s + u) =
      -(M * (6 - 4 * u - M * (2 - u))) := by
  rw [integral_conv_twoStepProfile hu1 hu2, integral_autocorr_twoStepProfile hu1 hu2]
  ring

/-- For small positive `M` the comparison fails at every lag in `(4/3, 3/2)`: the threshold
`(a + c)/2` cannot be lowered to `2a/3` for profiles that are only monotone beyond the mode. -/
theorem conv_sub_two_mul_autocorr_twoStepProfile_neg {M u : ℝ} (hu1 : 1 < u) (hu2 : u < 3 / 2)
    (hM0 : 0 < M) (hM : M * (2 - u) < 6 - 4 * u) :
    (∫ s in (0 : ℝ)..u, twoStepProfile M s * twoStepProfile M (u - s)) -
      2 * ∫ s in Ioi (0 : ℝ), twoStepProfile M s * twoStepProfile M (s + u) < 0 := by
  rw [conv_sub_two_mul_autocorr_twoStepProfile hu1 hu2]
  exact neg_neg_of_pos (mul_pos hM0 (by linarith))

end RHTower.CHMDPolar
