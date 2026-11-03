import GaloisForLFunctions.CanonicalSystemOfTheWindowTower.TheTrivialDivisorCouplesOrderedTests
import GaloisForLFunctions.WindowTowerOfSpecZ.TheTransferAcrossAStage

/-!
# The frozen form glues two windows

Fix a prime power `n = N + 1`, `ℓ = log n`, `w = Λ(n)/√n` and a collar width `0 < ε` with
`ε < log((n+1)/n)`; the window of length `A = ℓ + ε` splits into the **left collar**
`L = [−A, −ℓ]`, the **interior** `I = [−ℓ, −ε]` and the **right collar** `R = [−ε, 0]`. A test
`x_L + y + x_R` with pieces supported in `L`, `I`, `R` is a **stage test**. The new fold (translation
by `ℓ`) maps `L` onto `R`; on stage tests its correlation is `⟨x_L, J x_R⟩ = ∫ x_L(u) x_R(u + ℓ)`.

* **Chain law** (`weilQuad_chain_three`): for ordered pieces `f < g < h`,
  `Q(f + g + h) = Q(f + g) + Q(g + h) − Q(g) + 2Ξ(f, h)`, `Ξ` the ordered coupling
  (`TheTrivialDivisorCouplesOrderedTests`): the window is two windows of the previous length glued
  along the interior, plus the coupling of the far pieces.
* **The collar coupling of a stage** (`orderedCoupling_collars`): `Ξ(x_L, x_R) = ⟨μ(x_L), ν(x_R)⟩ − w⟨x_L, J x_R⟩`,
  where `⟨μ, ν⟩ = μ_{1}ν_{1} − Σ_{k≥1} μ_{−2k}ν_{−2k}` is the trivial-divisor pairing of the moments.
* **The two-collar identity** (`weilQuad_stageTest`): Weil's form on a stage test is the **frozen
  two-collar form** `F(x_L, y, x_R) = Q(x_L + y) + Q(y + x_R) − Q(y) + 2⟨μ(x_L), ν(x_R)⟩` minus the fold,
  `Q = F − 2w⟨x_L, J x_R⟩`; and `F` is the corpus stage datum `Q_N` (`stageForm_stageTest`). The impulse
  of the stage is exactly `−2w⟨x_L, J x_R⟩`; composite stages carry none.
* **The stage law** (`stage_nonneg_iff`): Weil positivity on stage tests ⟺ for all collar data
  `inf_y F(x_L, y, x_R) ≥ 2w⟨x_L, J x_R⟩` — the frozen two-collar complement must dominate the fold.
* **First stage** (`firstStage_frozen_eq`): at `n = 2` every coupling inside the window is prime-free,
  so `F = Q(x_L) + Q(y) + Q(x_R) + 2(⟨μ(x_L), ν(y)⟩ + ⟨μ(y), ν(x_R)⟩ + ⟨μ(x_L), ν(x_R)⟩)`: the frozen
  datum sees the collars only through `Q(x_L)`, `Q(x_R)` and their trivial-divisor moments
  (`firstStage_frozen_congr`).
* **Second stage** (`secondStage_frozen_eq`): at `n = 3` the earlier fold `T₂` adds its transports,
  `−2w₂(⟨τx_L, y⟩ + ⟨y, τ x_R⟩)` with `⟨τx_L, y⟩ = ∫ x_L(u) y(u + log 2)`: the collars are seen through
  their moments and through their images under the earlier fold.
-/

noncomputable section

open MeasureTheory Set Filter Topology RHTower
open scoped Real

namespace GaloisForLFunctions.CanonicalSystemOfTheWindowTower

open SpacingScaleHarmonicAnalysis CohomologyOfWindowsOfSpecZ RHTower.WeilMarkovPole

variable {a b : ℝ} {f g h : ℝ → ℝ}

/-! ### Supports -/

/-- A continuous function vanishing off `[p, q]` vanishes at both endpoints. -/
theorem eq_zero_of_vanish_off_Icc (hf : Continuous f) {p q : ℝ}
    (hv : ∀ u, u ∉ Icc p q → f u = 0) {u : ℝ} (hu : u ≤ p ∨ q ≤ u) : f u = 0 := by
  have hcl : IsClosed {u | f u = 0} := isClosed_eq hf continuous_const
  rcases hu with hu | hu
  · have hsub : Iio u ⊆ {u | f u = 0} := fun v hv' => hv v fun hm => by
      have := mem_Iio.mp hv'; linarith [hm.1]
    exact hcl.closure_subset_iff.mpr hsub (by rw [closure_Iio]; exact le_rfl)
  · have hsub : Ioi u ⊆ {u | f u = 0} := fun v hv' => hv v fun hm => by
      have := mem_Ioi.mp hv'; linarith [hm.2]
    exact hcl.closure_subset_iff.mpr hsub (by rw [closure_Ioi]; exact le_rfl)

theorem hasCompactSupport_of_vanish_off_Icc {p q : ℝ} (hv : ∀ u, u ∉ Icc p q → f u = 0) :
    HasCompactSupport f :=
  HasCompactSupport.intro isCompact_Icc hv

/-- Tests living in `(p, q)` and `(r, s)` correlate only at lags in `(r − q, s − p)`. -/
theorem crossCorr_eq_zero_of_lag (hf : Continuous f) (hg : Continuous g) {p q r s : ℝ}
    (hfv : ∀ u, u ∉ Icc p q → f u = 0) (hgv : ∀ u, u ∉ Icc r s → g u = 0) {x : ℝ}
    (hx : x ≤ r - q ∨ s - p ≤ x) : crossCorr f g x = 0 := by
  unfold crossCorr
  have e : ∀ u, f u * g (u + x) = 0 := fun u => by
    by_cases hu : p < u ∧ u < q
    · refine mul_eq_zero_of_right _ (eq_zero_of_vanish_off_Icc hg hgv ?_)
      rcases hx with hx | hx
      · left; linarith [hu.2]
      · right; linarith [hu.1]
    · refine mul_eq_zero_of_left (eq_zero_of_vanish_off_Icc hf hfv ?_) _
      by_contra hc
      push Not at hc
      exact hu ⟨hc.1, hc.2⟩
  simp only [e, integral_zero]

/-! ### Additivity of the ordered coupling -/

theorem crossCorr_add_right (hf : Continuous f) (hfc : HasCompactSupport f)
    (hg : Continuous g) (hh : Continuous h) (x : ℝ) :
    crossCorr f (fun u => g u + h u) x = crossCorr f g x + crossCorr f h x := by
  unfold crossCorr
  have i1 : Integrable fun u => f u * g (u + x) :=
    (hf.mul (hg.comp (continuous_add_const x))).integrable_of_hasCompactSupport hfc.mul_right
  have i2 : Integrable fun u => f u * h (u + x) :=
    (hf.mul (hh.comp (continuous_add_const x))).integrable_of_hasCompactSupport hfc.mul_right
  rw [← integral_add i1 i2]
  congr 1; funext u; ring

/-- The kernel term of an ordered pair is integrable on the half-line. -/
theorem OrderedAt.integrableOn_collarKernel_mul (hfg : OrderedAt a f g) (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) :
    IntegrableOn (fun x => collarKernel x * crossCorr f g x) (Ioi 0) := by
  have i1 := (integrable_crossCorr_mul_cosh hf.continuous hfc hg.continuous hgc).integrableOn
    (s := Ioi (0 : ℝ))
  have i2 := hfg.integrableOn_archLevyDensity_mul_crossCorr hf hfc hg hgc
  refine IntegrableOn.congr_fun (f := fun x => 2 * (crossCorr f g x * Real.cosh (x / 2)) -
    archLevyDensity x * crossCorr f g x) ((i1.const_mul 2).sub i2) (fun x hx => ?_) measurableSet_Ioi
  rw [← two_mul_cosh_sub_archLevyDensity hx]
  ring

/-- The prime part of the coupling is a finite sum over the lags meeting the supports. -/
theorem tsum_vonMangoldtAtom_mul_crossCorr_eq_sum {R : ℝ} (hfR : SupportedIn R f)
    (hgR : SupportedIn R g) :
    ∑' n : ℕ, vonMangoldtAtom n * crossCorr f g (Real.log n) =
      ∑ n ∈ Finset.range (lagRange R), vonMangoldtAtom n * crossCorr f g (Real.log n) := by
  refine tsum_eq_sum fun n hn => ?_
  have hn' : lagRange R ≤ n := by simpa using hn
  have hl := two_mul_lt_abs_log_of_lagRange_le hn'
  unfold crossCorr
  simp only [mul_shift_eq_zero_of_supportedIn hfR hgR hl, integral_zero, mul_zero]

/-- **The ordered coupling is additive** in the right test. -/
theorem orderedCoupling_add_right (h₁ : OrderedAt a f g) (h₂ : OrderedAt a f h)
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) (hg : ContDiff ℝ 2 g)
    (hgc : HasCompactSupport g) (hh : ContDiff ℝ 2 h) (hhc : HasCompactSupport h) :
    orderedCoupling f (fun u => g u + h u) = orderedCoupling f g + orderedCoupling f h := by
  unfold orderedCoupling
  have e1 : ∫ x in Ioi (0 : ℝ), collarKernel x * crossCorr f (fun u => g u + h u) x =
      (∫ x in Ioi (0 : ℝ), collarKernel x * crossCorr f g x) +
        ∫ x in Ioi (0 : ℝ), collarKernel x * crossCorr f h x := by
    rw [← integral_add (h₁.integrableOn_collarKernel_mul hf hfc hg hgc)
      (h₂.integrableOn_collarKernel_mul hf hfc hh hhc)]
    refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
    rw [crossCorr_add_right hf.continuous hfc hg.continuous hh.continuous]
    ring
  obtain ⟨R₁, -, hR₁⟩ := exists_supportedIn hfc
  obtain ⟨R₂, -, hR₂⟩ := exists_supportedIn hgc
  obtain ⟨R₃, -, hR₃⟩ := exists_supportedIn hhc
  set R := max R₁ (max R₂ R₃)
  have hfR := supportedIn_mono hR₁ (le_max_left _ _)
  have hgR := supportedIn_mono hR₂ ((le_max_left R₂ R₃).trans (le_max_right _ _))
  have hhR := supportedIn_mono hR₃ ((le_max_right R₂ R₃).trans (le_max_right _ _))
  rw [e1, tsum_vonMangoldtAtom_mul_crossCorr_eq_sum hfR (supportedIn_add hgR hhR),
    tsum_vonMangoldtAtom_mul_crossCorr_eq_sum hfR hgR,
    tsum_vonMangoldtAtom_mul_crossCorr_eq_sum hfR hhR]
  have e2 : ∑ n ∈ Finset.range (lagRange R),
      vonMangoldtAtom n * crossCorr f (fun u => g u + h u) (Real.log n) =
      ∑ n ∈ Finset.range (lagRange R), (vonMangoldtAtom n * crossCorr f g (Real.log n) +
        vonMangoldtAtom n * crossCorr f h (Real.log n)) := by
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [crossCorr_add_right hf.continuous hfc hg.continuous hh.continuous]
    ring
  rw [e2, Finset.sum_add_distrib]
  ring

/-! ### The chain law -/

/-- **Chain law**: for ordered pieces `f < g < h`,
`Q(f + g + h) = Q(f + g) + Q(g + h) − Q(g) + 2Ξ(f, h)`. -/
theorem weilQuad_chain_three (hfg : OrderedAt a f g) (hgh : OrderedAt b g h) (hab : a ≤ b)
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) (hg : ContDiff ℝ 2 g)
    (hgc : HasCompactSupport g) (hh : ContDiff ℝ 2 h) (hhc : HasCompactSupport h) :
    weilQuad (fun u => f u + g u + h u) =
      weilQuad (fun u => f u + g u) + weilQuad (fun u => g u + h u) - weilQuad g +
        2 * orderedCoupling f h := by
  have hfh : OrderedAt a f h := ⟨hfg.left, fun u hu => hgh.right u (lt_of_lt_of_le hu hab)⟩
  have hfgh : OrderedAt a f (fun u => g u + h u) :=
    ⟨hfg.left, fun u hu => by simp only [hfg.right u hu, hfh.right u hu, add_zero]⟩
  have e1 := weilQuad_add_of_ordered hfgh hf hfc (hg.add hh) (hgc.add hhc)
  have e2 := weilQuad_add_of_ordered hfg hf hfc hg hgc
  rw [orderedCoupling_add_right hfg hfh hf hfc hg hgc hh hhc] at e1
  have hfun : (fun u => f u + g u + h u) = fun u => f u + (g u + h u) := by
    funext u; ring
  rw [hfun, e1, e2]
  ring

/-! ### The moment pairing and the frozen two-collar form -/

/-- The **trivial-divisor pairing** of a left and a right test,
`⟨μ(f), ν(g)⟩ = μ_1(f) ν_1(g) − Σ_{k ≥ 1} μ_{−2k}(f) ν_{−2k}(g)`. -/
def momentPairing (f g : ℝ → ℝ) : ℝ :=
  leftMoment f (1 / 2) * rightMoment g (1 / 2) -
    ∑' k : ℕ, leftMoment f (trivialExponent k) * rightMoment g (trivialExponent k)

/-- The **frozen two-collar form** of a stage test:
`F(x_L, y, x_R) = Q(x_L + y) + Q(y + x_R) − Q(y) + 2⟨μ(x_L), ν(x_R)⟩`. -/
def frozenTwoCollar (xL y xR : ℝ → ℝ) : ℝ :=
  weilQuad (fun u => xL u + y u) + weilQuad (fun u => y u + xR u) - weilQuad y +
    2 * momentPairing xL xR

/-- Prime-free ordered tests couple through the moment pairing alone. -/
theorem orderedCoupling_eq_momentPairing (hfg : OrderedAt a f g) (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (hfree : ∀ n : ℕ, 2 ≤ n → crossCorr f g (Real.log n) = 0) :
    orderedCoupling f g = momentPairing f g := by
  rw [orderedCoupling, hfg.integral_collarKernel_mul_eq_moments hf hfc hg hgc, momentPairing]
  have : ∑' n : ℕ, vonMangoldtAtom n * crossCorr f g (Real.log n) = 0 := by
    refine (tsum_congr fun n => ?_).trans tsum_zero
    by_cases hn : 2 ≤ n
    · rw [hfree n hn, mul_zero]
    · rw [vonMangoldtAtom_eq_zero_of_lt_two (by omega), zero_mul]
  rw [this, sub_zero]

/-- An ordered pair whose only visible fold is `m` couples through the moments and that fold. -/
theorem orderedCoupling_eq_momentPairing_sub (hfg : OrderedAt a f g) (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) {m : ℕ}
    (honly : ∀ n : ℕ, 2 ≤ n → n ≠ m → crossCorr f g (Real.log n) = 0) :
    orderedCoupling f g =
      momentPairing f g - vonMangoldtAtom m * crossCorr f g (Real.log m) := by
  rw [orderedCoupling, hfg.integral_collarKernel_mul_eq_moments hf hfc hg hgc, momentPairing]
  congr 1
  refine tsum_eq_single m fun n hn => ?_
  by_cases h2 : 2 ≤ n
  · rw [honly n h2 hn, mul_zero]
  · rw [vonMangoldtAtom_eq_zero_of_lt_two (by omega), zero_mul]

/-! ### Stage tests -/

/-- On a stage the collar is shorter than the interior jump: `ε < log n`. -/
theorem stage_eps_lt_log {n : ℕ} (hn : 2 ≤ n) {ε : ℝ}
    (hεn : Real.log n + ε < Real.log (n + 1)) : ε < Real.log n := by
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have h1 : Real.log (n + 1) ≤ Real.log (2 * n) := Real.log_le_log (by linarith) (by linarith)
  rw [Real.log_mul (by norm_num) hn0.ne'] at h1
  have h2 : Real.log 2 ≤ Real.log n := Real.log_le_log (by norm_num) hn2
  linarith

/-- Concavity at the integers: `log(n+1) + log(n−1) ≤ 2 log n`. -/
theorem log_succ_add_log_pred_le {n : ℕ} (hn : 2 ≤ n) :
    Real.log (n + 1) + Real.log (n - 1) ≤ 2 * Real.log n := by
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have h : Real.log ((n + 1) * (n - 1)) ≤ Real.log (n * n) :=
    Real.log_le_log (by nlinarith) (by nlinarith)
  rw [Real.log_mul (by linarith) (by linarith), Real.log_mul (by linarith) (by linarith)] at h
  linarith

/-- The two collars of stage `n` see each other only at the lag `log n`. -/
theorem crossCorr_collars_log_eq_zero {n m : ℕ} (hn : 2 ≤ n) (hm : 2 ≤ m) (hmn : m ≠ n)
    {ε : ℝ} (hεn : Real.log n + ε < Real.log (n + 1)) {xL xR : ℝ → ℝ} (hxL : Continuous xL)
    (hxR : Continuous xR) (hL : ∀ u, u ∉ Icc (-Real.log n - ε) (-Real.log n) → xL u = 0)
    (hR : ∀ u, u ∉ Icc (-ε) 0 → xR u = 0) : crossCorr xL xR (Real.log m) = 0 := by
  refine crossCorr_eq_zero_of_lag hxL hxR hL hR ?_
  rcases lt_or_gt_of_ne hmn with hlt | hgt
  · left
    have hm' : (m : ℝ) ≤ n - 1 := by
      have : m + 1 ≤ n := hlt
      have : ((m + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast this
      push_cast at this; linarith
    have h1 : Real.log m ≤ Real.log (n - 1) :=
      Real.log_le_log (by have h2 : (2 : ℝ) ≤ m := (by exact_mod_cast hm); linarith) hm'
    have h2 := log_succ_add_log_pred_le hn
    linarith
  · right
    have hm' : (n : ℝ) + 1 ≤ m := by
      have : ((n + 1 : ℕ) : ℝ) ≤ m := by exact_mod_cast hgt
      push_cast at this; linarith
    have h1 : Real.log (n + 1) ≤ Real.log m := Real.log_le_log (by positivity) hm'
    linarith

/-- **The two-collar identity**: on a stage test, Weil's form is the frozen two-collar form minus
the new fold, `Q(x_L + y + x_R) = F(x_L, y, x_R) − 2w⟨x_L, J x_R⟩`. -/
theorem weilQuad_stageTest {n : ℕ} (hn : 2 ≤ n) {ε : ℝ} (hε : 0 < ε)
    (hεn : Real.log n + ε < Real.log (n + 1)) {xL y xR : ℝ → ℝ}
    (hxL : ContDiff ℝ 2 xL) (hy : ContDiff ℝ 2 y) (hxR : ContDiff ℝ 2 xR)
    (hL : ∀ u, u ∉ Icc (-Real.log n - ε) (-Real.log n) → xL u = 0)
    (hI : ∀ u, u ∉ Icc (-Real.log n) (-ε) → y u = 0)
    (hR : ∀ u, u ∉ Icc (-ε) 0 → xR u = 0) :
    weilQuad (fun u => xL u + y u + xR u) =
      frozenTwoCollar xL y xR - 2 * vonMangoldtAtom n * crossCorr xL xR (Real.log n) := by
  have hεl := stage_eps_lt_log hn hεn
  have oLI : OrderedAt (-Real.log n) xL y :=
    ⟨fun u hu => hL u fun hm => by linarith [hm.2], fun u hu => hI u fun hm => by linarith [hm.1]⟩
  have oIR : OrderedAt (-ε) y xR :=
    ⟨fun u hu => hI u fun hm => by linarith [hm.2], fun u hu => hR u fun hm => by linarith [hm.1]⟩
  have oLR : OrderedAt (-Real.log n) xL xR :=
    ⟨oLI.left, fun u hu => hR u fun hm => by linarith [hm.1]⟩
  rw [weilQuad_chain_three oLI oIR (by linarith) hxL (hasCompactSupport_of_vanish_off_Icc hL) hy
      (hasCompactSupport_of_vanish_off_Icc hI) hxR (hasCompactSupport_of_vanish_off_Icc hR),
    orderedCoupling_eq_momentPairing_sub oLR hxL (hasCompactSupport_of_vanish_off_Icc hL) hxR
      (hasCompactSupport_of_vanish_off_Icc hR) (m := n) fun m hm hmn =>
        crossCorr_collars_log_eq_zero hn hm hmn hεn hxL.continuous hxR.continuous hL hR]
  unfold frozenTwoCollar
  ring

/-- **The stage law**: Weil positivity on the stage tests of `n` is equivalent to the frozen
two-collar form dominating the new fold on every stage test. -/
theorem stage_nonneg_iff {n : ℕ} (hn : 2 ≤ n) {ε : ℝ} (hε : 0 < ε)
    (hεn : Real.log n + ε < Real.log (n + 1)) :
    (∀ xL y xR : ℝ → ℝ, ContDiff ℝ 2 xL → ContDiff ℝ 2 y → ContDiff ℝ 2 xR →
      (∀ u, u ∉ Icc (-Real.log n - ε) (-Real.log n) → xL u = 0) →
      (∀ u, u ∉ Icc (-Real.log n) (-ε) → y u = 0) → (∀ u, u ∉ Icc (-ε) 0 → xR u = 0) →
        0 ≤ weilQuad (fun u => xL u + y u + xR u)) ↔
    (∀ xL y xR : ℝ → ℝ, ContDiff ℝ 2 xL → ContDiff ℝ 2 y → ContDiff ℝ 2 xR →
      (∀ u, u ∉ Icc (-Real.log n - ε) (-Real.log n) → xL u = 0) →
      (∀ u, u ∉ Icc (-Real.log n) (-ε) → y u = 0) → (∀ u, u ∉ Icc (-ε) 0 → xR u = 0) →
        2 * vonMangoldtAtom n * crossCorr xL xR (Real.log n) ≤ frozenTwoCollar xL y xR) := by
  refine forall_congr' fun xL => forall_congr' fun y => forall_congr' fun xR => ?_
  refine forall_congr' fun hxL => forall_congr' fun hy => forall_congr' fun hxR => ?_
  refine forall_congr' fun hL => forall_congr' fun hI => forall_congr' fun hR => ?_
  rw [weilQuad_stageTest hn hε hεn hxL hy hxR hL hI hR, sub_nonneg]

/-! ### The frozen form is the stage datum -/

theorem windowLevel_stage {N : ℕ} {ε : ℝ} (hε : 0 ≤ ε)
    (hεn : Real.log (N + 1 : ℕ) + ε < Real.log (N + 2 : ℕ)) :
    windowLevel (Real.log (N + 1 : ℕ) + ε) = N + 1 := by
  unfold windowLevel
  have hN1 : (0 : ℝ) < (N + 1 : ℕ) := by positivity
  rw [Real.exp_add, Real.exp_log hN1, Nat.floor_eq_iff (by positivity)]
  constructor
  · have := Real.one_le_exp_iff.mpr hε
    push_cast
    nlinarith
  · have h := Real.exp_lt_exp.mpr hεn
    rw [Real.exp_add, Real.exp_log hN1, Real.exp_log (by positivity)] at h
    push_cast at h ⊢
    linarith

/-- On a stage test the fold correlates only the two collars: `∫ H(u)H(u + ℓ) = ⟨x_L, J x_R⟩`. -/
theorem integral_stageTest_mul_shift {n : ℕ} {ε : ℝ} (hε : 0 < ε) {xL y xR : ℝ → ℝ}
    (hy : Continuous y) (hεl : ε < Real.log n)
    (hL : ∀ u, u ∉ Icc (-Real.log n - ε) (-Real.log n) → xL u = 0)
    (hI : ∀ u, u ∉ Icc (-Real.log n) (-ε) → y u = 0)
    (hR : ∀ u, u ∉ Icc (-ε) 0 → xR u = 0) :
    ∫ u, (xL u + y u + xR u) * (xL (u + Real.log n) + y (u + Real.log n) + xR (u + Real.log n)) =
      crossCorr xL xR (Real.log n) := by
  unfold crossCorr
  congr 1
  funext u
  set ℓ := Real.log n
  by_cases h1 : u < -ℓ - ε
  · rw [hL u fun hm => by linarith [hm.1], hI u fun hm => by linarith [hm.1],
      hR u fun hm => by linarith [hm.1]]
    ring
  · by_cases h2 : -ℓ < u
    · rw [hL (u + ℓ) fun hm => by linarith [hm.2], hI (u + ℓ) fun hm => by linarith [hm.2],
        hR (u + ℓ) fun hm => by linarith [hm.2]]
      ring
    · push Not at h1 h2
      rw [eq_zero_of_vanish_off_Icc hy hI (Or.inl h2), hR u fun hm => by linarith [hm.1],
        eq_zero_of_vanish_off_Icc hy hI (Or.inr (by linarith)),
        hL (u + ℓ) fun hm => by linarith [hm.2]]
      ring

/-- **The frozen two-collar form is the stage datum** `Q_N` of the corpus on stage tests. -/
theorem stageForm_stageTest {N : ℕ} (hN : 1 ≤ N) {ε : ℝ} (hε : 0 < ε)
    (hεn : Real.log (N + 1 : ℕ) + ε < Real.log (N + 2 : ℕ)) {xL y xR : ℝ → ℝ}
    (hxL : ContDiff ℝ 2 xL) (hy : ContDiff ℝ 2 y) (hxR : ContDiff ℝ 2 xR)
    (hL : ∀ u, u ∉ Icc (-Real.log (N + 1 : ℕ) - ε) (-Real.log (N + 1 : ℕ)) → xL u = 0)
    (hI : ∀ u, u ∉ Icc (-Real.log (N + 1 : ℕ)) (-ε) → y u = 0)
    (hR : ∀ u, u ∉ Icc (-ε) 0 → xR u = 0) :
    WindowTowerOfSpecZ.stageForm N (fun u => xL u + y u + xR u) = frozenTwoCollar xL y xR := by
  set H := fun u => xL u + y u + xR u with hHdef
  have hn : 2 ≤ N + 1 := by omega
  have hεn' : Real.log ((N + 1 : ℕ) : ℝ) + ε < Real.log (((N + 1 : ℕ) : ℝ) + 1) := by
    have : (((N + 1 : ℕ) : ℝ) + 1) = ((N + 2 : ℕ) : ℝ) := by push_cast; ring
    rw [this]; exact hεn
  have hεl := stage_eps_lt_log hn hεn'
  have hwin : IsWindowTest (Real.log (N + 1 : ℕ) + ε) H := by
    refine ⟨(hxL.add hy).add hxR, fun u hu => ?_⟩
    have hu' : u < -(Real.log (N + 1 : ℕ) + ε) ∨ 0 < u := by
      by_contra hc; push Not at hc; exact hu ⟨hc.1, hc.2⟩
    simp only [H]
    rcases hu' with hu' | hu'
    · rw [hL u fun hm => by linarith [hm.1], hI u fun hm => by linarith [hm.1],
        hR u fun hm => by linarith [hm.1]]; ring
    · rw [hL u fun hm => by linarith [hm.2], hI u fun hm => by linarith [hm.2],
        hR u fun hm => by linarith [hm.2]]; ring
  have hQ := weilQuad_eq_markovForm_windowLevel hwin
  rw [windowLevel_stage hε.le hεn, markovForm_succ hwin.continuous hwin.hasCompactSupport hN] at hQ
  have hshift := integral_stageTest_mul_shift (n := N + 1) hε hy.continuous hεl hL hI hR
  have hstage := weilQuad_stageTest hn hε hεn' hxL hy hxR hL hI hR
  have hw : primeJumpWeight (N + 1) = vonMangoldtAtom (N + 1) := by
    unfold primeJumpWeight vonMangoldtAtom; rw [if_pos hn]
  rw [WindowTowerOfSpecZ.stageForm]
  simp only [H] at hQ hshift ⊢
  rw [hshift, hw] at hQ
  linarith

end GaloisForLFunctions.CanonicalSystemOfTheWindowTower
