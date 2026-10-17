import GaloisForLFunctions.RHTower.CHMDOddPrimeCrossSignBonusAndWindowPositivity

/-!
# The monotone prime-sign law on the one-signed odd cone

On the one-signed odd cone the prime `n` enters the Doob energy through the difference
`B_n(g) − C_n(g)` of the opposite-side convolution `2 (Λ(n)/√n) ∫_0^{log n} g(s) g(log n − s) ds`
and the same-side autocorrelation `4 (Λ(n)/√n) ∫_0^∞ g(s) g(s + log n) ds` of the profile
`g = Θ|v|`.  For a profile that is nonincreasing on `[0, a]` and vanishes beyond `a`, the
convolution dominates twice the autocorrelation at every lag `u ≥ 2a/3`:

`∫_0^u g(s) g(u − s) ds ≥ 2 ∫_0^∞ g(s) g(s + u) ds`.

Hence every prime power with `log n ≥ 2a/3` helps, and only the primes below `e^{2a/3}` can
hurt.  The constant `2/3` is sharp: for the indicator profile of `[0, a]` the difference equals
`3u − 2a`.  Consequences: on a support of half-width `a ≤ (3/2) log 2`, every prime term is
nonnegative and the energy dominates the Lévy form plus the cross-sign bonus, extending the
unconditional window from `2 log 2` to `3 log 2` on the monotone sub-cone; in general the energy
dominates the Lévy form, the bonus, and the finitely many prime terms below the threshold.
-/

open MeasureTheory Set Filter Topology
open scoped InnerProductSpace

namespace RHTower.CHMDPolar
open CHMDDoobGraph

/-! ## The convolution–autocorrelation comparison for monotone profiles -/

/-- **Convolution dominates twice the autocorrelation beyond two thirds of the support.** -/
theorem two_mul_integral_autocorr_le_integral_conv {g : ℝ → ℝ} (hg : Continuous g)
    (hgc : HasCompactSupport g) (hg0 : ∀ s, 0 ≤ g s) {a : ℝ} (ha : 0 < a)
    (hga : ∀ s, a ≤ s → g s = 0) (hmono : AntitoneOn g (Icc 0 a)) {u : ℝ}
    (hu : 2 * a / 3 ≤ u) :
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

/-- **Every prime power beyond two thirds of the support helps**: `C_n(g) ≤ B_n(g)` whenever
`log n ≥ 2a/3` for a profile nonincreasing on `[0, a]` and vanishing beyond `a`. -/
theorem sameSideCross_le_oppositeSideBonus_of_antitoneOn {g : ℝ → ℝ} (hg : Continuous g)
    (hgc : HasCompactSupport g) (hg0 : ∀ s, 0 ≤ g s) {a : ℝ} (ha : 0 < a)
    (hga : ∀ s, a ≤ s → g s = 0) (hmono : AntitoneOn g (Icc 0 a)) {n : ℕ}
    (hn : 2 * a / 3 ≤ Real.log n) :
    sameSideCross g n ≤ oppositeSideBonus g n := by
  unfold sameSideCross oppositeSideBonus
  have h := two_mul_integral_autocorr_le_integral_conv hg hgc hg0 ha hga hmono hn
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

/-- **The monotone prime-sign law on the one-signed odd cone**: for a one-signed odd test of support
`(−L/2, L/2)` whose Doob profile `Θ|v|` is nonincreasing on `[0, L/2]`, every prime power with
`log n ≥ L/3` contributes nonnegatively, so the energy dominates the Lévy form, the cross-sign
bonus and the finitely many prime terms below `e^{L/3}`:
`E(v) ≥ Λ_∞(Θ|v|) + 4·bonus(Θ|v|) + Σ_{n < N} (B_n − C_n)` for every `N` with `L/3 ≤ log N`. -/
theorem levy_abs_add_bonus_add_sum_le_sourceEnergy_of_antitoneOn (v : ℝ → ℝ)
    (hv : ContDiff ℝ 2 v) (hvc : HasCompactSupport v) (hodd : ∀ x, v (-x) = -v x)
    (hpos : ∀ x, 0 ≤ x → 0 ≤ v x) {L : ℝ} (hL : 0 < L)
    (hsupp : ∀ x ∉ Ioo (-(L / 2)) (L / 2), v x = 0)
    (hmono : AntitoneOn (phiDoobTest fun y => |v y|) (Icc 0 (L / 2))) {N : ℕ}
    (hN : L / 3 ≤ Real.log N) :
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
    (by linarith : 0 < L / 2) (fun s hs => phiDoobTest_abs_vanish hsupp hs) hmono ?_)
  linarith

/-- **The monotone window `3 log 2`**: for a one-signed odd test of support `(−L/2, L/2)` with
`L ≤ 3 log 2` whose Doob profile is nonincreasing on `[0, L/2]`, every prime term is nonnegative
and the energy dominates the Lévy form plus the cross-sign bonus. -/
theorem levy_abs_add_bonus_le_sourceEnergy_of_antitoneOn_three_log_two (v : ℝ → ℝ)
    (hv : ContDiff ℝ 2 v) (hvc : HasCompactSupport v) (hodd : ∀ x, v (-x) = -v x)
    (hpos : ∀ x, 0 ≤ x → 0 ≤ v x) {L : ℝ} (hL : 0 < L)
    (hsupp : ∀ x ∉ Ioo (-(L / 2)) (L / 2), v x = 0)
    (hmono : AntitoneOn (phiDoobTest fun y => |v y|) (Icc 0 (L / 2)))
    (hL2 : L ≤ 3 * Real.log 2) :
    weilLevyForm (phiDoobTest fun y => |v y|) + 4 * crossSignBonus (phiDoobTest fun y => |v y|) ≤
      sourceEnergy (compactLift v hv hvc) := by
  have h := levy_abs_add_bonus_add_sum_le_sourceEnergy_of_antitoneOn v hv hvc hodd hpos hL hsupp
    hmono (N := 2) (by push_cast; linarith)
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

end RHTower.CHMDPolar
