import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheHorizonCriterion
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.ThePrimesOfAHorizonWindow
import GaloisForLFunctions.RHTower.WeilLevyPoleGaussModeCancellation

/-!
# The window datum

A **window** of `Spec ℤ` of length `A ≥ 0` is the interval `[−A, 0]` of the scaling line; a
**window test** is a real `C²` function supported there. The prime powers that act on a window by a
jump are the `n ≤ e^A`; the **level** of the window is `⌊e^A⌋`.

* **Locality** (`weilQuad_eq_markovForm_windowLevel`, `markovForm_eq_windowLevel`): on window tests
  Weil's form is the Markov form at the level of the window plus the pole plane,
  `Q(H) = M_{⌊e^A⌋}(H) + ½⟨c,H⟩² − ½⟨s,H⟩²`, and any higher level gives the same Markov form.
* **Locality in the Euler factors** (`weilFullFunctional_congr_window`): two weights that agree on
  `2 ≤ n ≤ ⌊e^A⌋` have the same Weil functional on every window test of length `A`.
* **Symmetries** (`weilQuad_comp_neg`, `weilQuad_windowInvolution`): reflection and the window
  involution `σ_A H(u) = H(−A − u)` are isometries; windows of equal length are isometric.
* **The window criterion** (`riemannHypothesis_iff_windowForm_nonneg`): RH holds iff Weil's form is
  nonnegative on every window test of every length.
* **The canonical degree** (`canonicalDegree`): `deg K_A = 2Σ_{n ≤ e^A} Λ(n)/√n − Ω(0)`, minus the
  creation potential of the window; it is positive and nondecreasing in `A`.
-/

noncomputable section

open MeasureTheory Set Filter Topology Zeta23

namespace GaloisForLFunctions.CohomologyOfWindowsOfSpecZ

open SpacingScaleHarmonicAnalysis RHTower.WeilMarkovPole

/-- A **window test** of length `A`: a real `C²` function supported in the window `[−A, 0]`. -/
structure IsWindowTest (A : ℝ) (H : ℝ → ℝ) : Prop where
  contDiff : ContDiff ℝ 2 H
  vanish : ∀ y, y ∉ Icc (-A) 0 → H y = 0

/-- The **level** of a window of length `A`: the prime powers acting on it are the `n ≤ ⌊e^A⌋`. -/
def windowLevel (A : ℝ) : ℕ := ⌊Real.exp A⌋₊

/-- The **canonical degree** of a window, `deg K_A = −V_{⌊e^A⌋} = 2Σ_{2≤n≤e^A} Λ(n)/√n − Ω(0)`. -/
def canonicalDegree (A : ℝ) : ℝ := -creationPotential (windowLevel A)

variable {A B : ℝ} {H : ℝ → ℝ}

namespace IsWindowTest

theorem continuous (hH : IsWindowTest A H) : Continuous H := hH.contDiff.continuous

theorem hasCompactSupport (hH : IsWindowTest A H) : HasCompactSupport H :=
  HasCompactSupport.intro (isCompact_Icc (a := -A) (b := 0)) hH.vanish

/-- Windows nest. -/
theorem mono (hH : IsWindowTest A H) (hAB : A ≤ B) : IsWindowTest B H :=
  ⟨hH.contDiff, fun y hy => hH.vanish y fun hm => hy ⟨by linarith [hm.1], hm.2⟩⟩

/-- A jump longer than the window leaves it. -/
theorem mul_translate_eq_zero (hH : IsWindowTest A H) {ℓ : ℝ} (hℓ : A < ℓ) (u : ℝ) :
    H u * H (u + ℓ) = 0 := by
  by_cases hu : u ∈ Icc (-A) 0
  · rw [hH.vanish (u + ℓ) fun hm => by linarith [hm.2, hu.1], mul_zero]
  · rw [hH.vanish u hu, zero_mul]

/-- The prime powers beyond the level leave the window. -/
theorem mul_translate_log_eq_zero (hH : IsWindowTest A H) {n : ℕ} (hn : windowLevel A < n)
    (u : ℝ) : H u * H (u + Real.log n) = 0 := by
  have hn' : Real.exp A < n := (Nat.floor_lt (Real.exp_pos A).le).mp hn
  have hn0 : (0 : ℝ) < n := (Real.exp_pos A).trans hn'
  exact hH.mul_translate_eq_zero ((Real.lt_log_iff_exp_lt hn0).mpr hn') u

/-- The autocorrelation of a window test vanishes at `±log n` beyond the level. -/
theorem weilTest_log_eq_zero (hH : IsWindowTest A H) {n : ℕ} (hn : windowLevel A < n) :
    EF.weilTest (fun u => (H u : ℂ)) (fun u => (H u : ℂ)) (Real.log n) = 0 ∧
      EF.weilTest (fun u => (H u : ℂ)) (fun u => (H u : ℂ)) (-Real.log n) = 0 := by
  obtain ⟨e1, e2⟩ := weilTest_ofReal_log H n
  have hz : (fun u => H u * H (u + Real.log n)) = fun _ => (0 : ℝ) :=
    funext (hH.mul_translate_log_eq_zero hn)
  rw [e1, e2, hz, integral_zero, Complex.ofReal_zero]
  exact ⟨rfl, rfl⟩

end IsWindowTest

/-! ### Locality -/

/-- **Locality**: on a window test of length `A`, `Q(H) = M_{⌊e^A⌋}(H) + ½⟨c,H⟩² − ½⟨s,H⟩²`. -/
theorem weilQuad_eq_markovForm_windowLevel (hH : IsWindowTest A H) :
    weilQuad H = markovForm (windowLevel A) H + coshPairing H ^ 2 / 2 - sinhPairing H ^ 2 / 2 :=
  ArithmeticHodgeTheoryOfDegenerations.weilQuad_eq_markovForm hH.contDiff hH.hasCompactSupport
    fun _ hn u => hH.mul_translate_log_eq_zero hn u

/-- **Level independence**: every level past `⌊e^A⌋` gives the same Markov form on the window. -/
theorem markovForm_eq_windowLevel (hH : IsWindowTest A H) {N : ℕ} (hN : windowLevel A ≤ N) :
    markovForm N H = markovForm (windowLevel A) H :=
  ArithmeticHodgeTheoryOfDegenerations.markovForm_eq_of_level hH.contDiff hH.hasCompactSupport
    (fun _ hn u => hH.mul_translate_log_eq_zero hn u) hN

/-- **Locality in the Euler factors**: weights agreeing on `2 ≤ n ≤ ⌊e^A⌋` give the same Weil
functional on every window test of length `A`. -/
theorem weilFullFunctional_congr_window (hH : IsWindowTest A H) {lam lam' : ℕ → ℝ}
    (h : ∀ n : ℕ, 2 ≤ n → n ≤ windowLevel A → lam n = lam' n) :
    RHTower.weilFullFunctional lam (EF.weilTest (fun u => (H u : ℂ)) (fun u => (H u : ℂ))) =
      RHTower.weilFullFunctional lam' (EF.weilTest (fun u => (H u : ℂ)) (fun u => (H u : ℂ))) := by
  set k := EF.weilTest (fun u => (H u : ℂ)) (fun u => (H u : ℂ)) with hk
  have hs : (∑' n : ℕ, ((if 2 ≤ n then lam n / Real.sqrt n else 0 : ℝ) : ℂ) *
      (k (Real.log n) + k (-Real.log n))) =
      ∑' n : ℕ, ((if 2 ≤ n then lam' n / Real.sqrt n else 0 : ℝ) : ℂ) *
        (k (Real.log n) + k (-Real.log n)) := by
    refine tsum_congr fun n => ?_
    by_cases hn : n ≤ windowLevel A
    · by_cases h2 : 2 ≤ n
      · rw [if_pos h2, if_pos h2, h n h2 hn]
      · rw [if_neg h2, if_neg h2]
    · obtain ⟨e1, e2⟩ := hH.weilTest_log_eq_zero (not_le.mp hn)
      rw [hk, e1, e2, add_zero, mul_zero, mul_zero]
  simp only [RHTower.weilFullFunctional, hs]

/-! ### Symmetries -/

/-- **Reflection invariance**: `Q(H(−·)) = Q(H)`; the autocorrelation does not change. -/
theorem weilQuad_comp_neg (H : ℝ → ℝ) : weilQuad (fun u => H (-u)) = weilQuad H := by
  unfold weilQuad
  have hk : EF.weilTest (fun u => (H (-u) : ℂ)) (fun u => (H (-u) : ℂ)) =
      EF.weilTest (fun u => (H u : ℂ)) (fun u => (H u : ℂ)) := by
    funext y
    rw [RHTower.weilTest_ofReal_eq, RHTower.weilTest_ofReal_eq]
    congr 1
    have h1 : (fun t => H (-t) * H (-(t - y))) = fun t => (fun s => H s * H (s + y)) (-t) := by
      funext t; simp only; ring_nf
    have h2 : (fun s => H s * H (s + y)) = fun s => (fun t => H t * H (t - y)) (s + y) := by
      funext s; simp only [add_sub_cancel_right]; ring
    rw [h1, integral_neg_eq_self (fun s => H s * H (s + y)), h2,
      integral_add_right_eq_self (fun t => H t * H (t - y)) y]
  rw [hk]

/-- The **window involution** `σ_A H(u) = H(−A − u)`: Serre duality of the window. -/
def windowInvolution (A : ℝ) (H : ℝ → ℝ) : ℝ → ℝ := fun u => H (-A - u)

theorem windowInvolution_windowInvolution (A : ℝ) (H : ℝ → ℝ) :
    windowInvolution A (windowInvolution A H) = H := by
  funext u; simp only [windowInvolution]; ring_nf

theorem IsWindowTest.windowInvolution (hH : IsWindowTest A H) :
    IsWindowTest A (windowInvolution A H) := by
  refine ⟨hH.contDiff.comp (contDiff_const.sub contDiff_id), fun y hy => hH.vanish _ fun hm => hy ?_⟩
  exact ⟨by linarith [hm.2], by linarith [hm.1]⟩

/-- **Window Serre duality**: the window involution is an isometry of Weil's form. -/
theorem weilQuad_windowInvolution (A : ℝ) (H : ℝ → ℝ) :
    weilQuad (windowInvolution A H) = weilQuad H := by
  have h : windowInvolution A H = fun u => (fun v => H (-v)) (u - -A) := by
    funext u; simp only [windowInvolution]; ring_nf
  rw [h, weilQuad_comp_sub (fun v => H (-v)) (-A), weilQuad_comp_neg]

/-- A translate of a window test of length `A` into `[c − A, c]` has the same Weil form. -/
theorem weilQuad_translate (H : ℝ → ℝ) (c : ℝ) : weilQuad (fun u => H (u - c)) = weilQuad H :=
  weilQuad_comp_sub H c

/-! ### The window criterion -/

/-- **The window criterion**: RH holds iff Weil's form is nonnegative on every window test of
every length. -/
theorem riemannHypothesis_iff_windowForm_nonneg :
    RiemannHypothesis ↔ ∀ A : ℝ, 0 ≤ A → ∀ H : ℝ → ℝ, IsWindowTest A H → 0 ≤ weilQuad H := by
  rw [ArithmeticHodgeTheoryOfDegenerations.riemannHypothesis_iff_weilQuad_nonneg]
  constructor
  · intro hW A _ H hH
    exact hW H hH.contDiff hH.hasCompactSupport
  · intro hW g hg hgc
    obtain ⟨R, hR⟩ := hgc.isCompact.isBounded.subset_closedBall 0
    set R' := max R 0 with hR'
    have hR0 : 0 ≤ R' := le_max_right _ _
    have hgR : ∀ u, R' < |u| → g u = 0 := fun u hu => by
      by_contra hne
      have := hR (subset_tsupport g hne)
      rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at this
      linarith [le_max_left R 0]
    have hwin : IsWindowTest (2 * R') (fun u => g (u - -R')) := by
      refine ⟨hg.comp (contDiff_id.sub contDiff_const), fun y hy => hgR _ ?_⟩
      simp only [mem_Icc, not_and_or, not_le] at hy
      rcases hy with hy | hy
      · rw [abs_of_neg (by linarith)]; linarith
      · rw [abs_of_pos (by linarith)]; linarith
    have := hW (2 * R') (by linarith) _ hwin
    rwa [weilQuad_comp_sub] at this

/-! ### The canonical degree -/

theorem canonicalDegree_eq (A : ℝ) :
    canonicalDegree A =
      2 * ∑ n ∈ Finset.Icc 2 (windowLevel A), primeJumpWeight n - EF.gammaBracket 0 := by
  rw [canonicalDegree, creationPotential]; ring

theorem windowLevel_mono : Monotone windowLevel := fun _ _ h =>
  Nat.floor_le_floor (Real.exp_le_exp.mpr h)

/-- The canonical degree is positive: `Ω(0) < 0`. -/
theorem canonicalDegree_pos (A : ℝ) : 0 < canonicalDegree A := by
  rw [canonicalDegree_eq]
  have := RHTower.WeilLevyPoleGauss.gammaBracket_zero_lt_zero
  have : 0 ≤ ∑ n ∈ Finset.Icc 2 (windowLevel A), primeJumpWeight n :=
    Finset.sum_nonneg fun n _ => primeJumpWeight_nonneg n
  linarith

/-- The canonical degree is nondecreasing in the window length. -/
theorem canonicalDegree_mono : Monotone canonicalDegree := fun A B hAB => by
  rw [canonicalDegree_eq, canonicalDegree_eq]
  have : ∑ n ∈ Finset.Icc 2 (windowLevel A), primeJumpWeight n ≤
      ∑ n ∈ Finset.Icc 2 (windowLevel B), primeJumpWeight n :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc le_rfl (windowLevel_mono hAB))
      fun n _ _ => primeJumpWeight_nonneg n
  linarith

end GaloisForLFunctions.CohomologyOfWindowsOfSpecZ
