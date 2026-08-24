import GaloisForLFunctions.RHTower.CCMArchimedeanInfiniteOrder
import GaloisForLFunctions.RHTower.HedenmalmThetaSourceUnconditional
import GaloisForLFunctions.RHTower.ThetaCuspFinitePrimeCofinalSelection

/-!
# Positive cofinal finite-prime theta screen

Uniform compact convergence to the everywhere-positive completed theta source provides a
transition-strip positivity threshold.  Combining that threshold with the all-derivative
diagonal selector gives strictly increasing source-defined cutoffs.  The canonical translated
smooth cutoff then produces a one-sided screened source whose FE reflection average is real,
even, and strictly positive at every point.
-/

open Filter Topology Set MeasureTheory

noncomputable section

namespace RHTower

theorem thetaCuspSourceTerm_pos_of_nonneg
    {x : ℝ} (hx : 0 ≤ x) {n : ℕ} (hn : 0 < n) :
    0 < thetaCuspSourceTerm x n := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hexp : (1 : ℝ) ≤ Real.exp x := by
    simpa using Real.exp_le_exp.mpr hx
  have hscale : (1 : ℝ) ≤ (n : ℝ) * Real.exp x := by nlinarith [Real.exp_pos x]
  have hseed : 0 < thetaCuspSeed ((n : ℝ) * Real.exp x) := by
    apply thetaCuspSeed_pos
    nlinarith [Real.pi_gt_three, sq_nonneg ((n : ℝ) * Real.exp x - 1)]
  unfold thetaCuspSourceTerm
  exact mul_pos (Real.exp_pos _) hseed

theorem finitePrimeThetaCuspSource_pos_of_nonneg (N : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    0 < finitePrimeThetaCuspSource N x := by
  let S : Set ℕ := (N + 1).smoothNumbers
  let f : S → ℝ := fun n ↦ thetaCuspSourceTerm x n
  have hf : Summable f := (summable_thetaCuspSourceTerm x).subtype S
  have hfnn : ∀ n : S, 0 ≤ f n := fun n ↦
    (thetaCuspSourceTerm_pos_of_nonneg hx
      (Nat.pos_of_ne_zero (Nat.ne_zero_of_mem_smoothNumbers n.property))).le
  let oneS : S := ⟨1, by
    rw [Nat.mem_smoothNumbers]
    simp⟩
  have hone : 0 < f oneS := thetaCuspSourceTerm_pos_of_nonneg hx one_pos
  have hle : f oneS ≤ ∑' n : S, f n := hf.le_tsum oneS (fun n _ ↦ hfnn n)
  rw [finitePrimeThetaCuspSource]
  exact hone.trans_le hle

/-- On the compact transition side, sufficiently large finite-prime sources are strictly
positive because they converge uniformly to the everywhere-positive completed theta source. -/
theorem exists_finitePrimeThetaCuspPositiveThreshold (j : ℕ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ x ∈
        Icc (-((j + 1 : ℕ) : ℝ)) 0,
      0 < finitePrimeThetaCuspSource N x := by
  let K : Set ℝ := Icc (-((j + 1 : ℕ) : ℝ)) 0
  have hK : IsCompact K := isCompact_Icc
  have hKne : K.Nonempty := nonempty_Icc.mpr (by
    have hj : (0 : ℝ) ≤ (j + 1 : ℕ) := by positivity
    linarith)
  have hcont : ContinuousOn thetaCuspFullSource K :=
    contDiff_thetaCuspFullSource.continuous.continuousOn
  obtain ⟨x₀, hx₀K, hx₀min⟩ := hK.exists_isMinOn hKne hcont
  have hx₀pos : 0 < thetaCuspFullSource x₀ :=
    HedenmalmThetaSource.thetaCuspFullSource_pos x₀
  let epsilon : ℝ := thetaCuspFullSource x₀ / 2
  have hepsilon : 0 < epsilon := half_pos hx₀pos
  have hconv := finitePrimeThetaCuspSource_tendstoUniformlyOn_Icc
    ((j + 1 : ℕ) : ℝ)
  have hev := (Metric.tendstoUniformlyOn_iff.mp hconv) epsilon hepsilon
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 hev
  refine ⟨N₀, fun N hN x hxK ↦ ?_⟩
  have hxBig : x ∈ Icc (-((j + 1 : ℕ) : ℝ)) ((j + 1 : ℕ) : ℝ) :=
    ⟨hxK.1, hxK.2.trans (by positivity)⟩
  have hclose := hN₀ N hN x hxBig
  have hmin : thetaCuspFullSource x₀ ≤ thetaCuspFullSource x := hx₀min hxK
  rw [Real.dist_eq] at hclose
  dsimp [epsilon] at hclose
  have hlower : thetaCuspFullSource x - thetaCuspFullSource x₀ / 2 <
      finitePrimeThetaCuspSource N x := by
    rw [abs_lt] at hclose
    linarith
  nlinarith

noncomputable def finitePrimeThetaCuspPositiveThreshold (j : ℕ) : ℕ :=
  Classical.choose (exists_finitePrimeThetaCuspPositiveThreshold j)

theorem finitePrimeThetaCuspPositiveThreshold_spec (j : ℕ) {N : ℕ}
    (hN : finitePrimeThetaCuspPositiveThreshold j ≤ N) :
    ∀ x ∈ Icc (-((j + 1 : ℕ) : ℝ)) 0,
      0 < finitePrimeThetaCuspSource N x :=
  (Classical.choose_spec (exists_finitePrimeThetaCuspPositiveThreshold j)) N hN

/-- Strictly increasing cutoffs satisfying both all-derivative accuracy and transition positivity. -/
noncomputable def finitePrimeThetaCuspPositiveScreenIndex : ℕ → ℕ
  | 0 => max (finitePrimeThetaCuspAccuracyThreshold 0)
      (finitePrimeThetaCuspPositiveThreshold 0)
  | j + 1 => max
      (max (finitePrimeThetaCuspAccuracyThreshold (j + 1))
        (finitePrimeThetaCuspPositiveThreshold (j + 1)))
      (finitePrimeThetaCuspPositiveScreenIndex j + 1)

theorem finitePrimeThetaCuspPositiveScreenIndex_strictMono :
    StrictMono finitePrimeThetaCuspPositiveScreenIndex := by
  apply strictMono_nat_of_lt_succ
  intro j
  rw [finitePrimeThetaCuspPositiveScreenIndex]
  exact (Nat.lt_succ_self _).trans_le (le_max_right _ _)

theorem finitePrimeThetaCuspAccuracyThreshold_le_positiveScreenIndex (j : ℕ) :
    finitePrimeThetaCuspAccuracyThreshold j ≤
      finitePrimeThetaCuspPositiveScreenIndex j := by
  cases j with
  | zero => exact le_max_left _ _
  | succ j =>
      rw [finitePrimeThetaCuspPositiveScreenIndex]
      exact (le_max_left _ _).trans (le_max_left _ _)

theorem finitePrimeThetaCuspPositiveThreshold_le_positiveScreenIndex (j : ℕ) :
    finitePrimeThetaCuspPositiveThreshold j ≤
      finitePrimeThetaCuspPositiveScreenIndex j := by
  cases j with
  | zero => exact le_max_right _ _
  | succ j =>
      rw [finitePrimeThetaCuspPositiveScreenIndex]
      exact (le_max_right _ _).trans (le_max_left _ _)

theorem finitePrimeThetaCuspPositiveScreenIndex_accuracy (j : ℕ) :
    finitePrimeThetaCuspScreenAccuracy j
      (finitePrimeThetaCuspPositiveScreenIndex j) :=
  finitePrimeThetaCuspAccuracyThreshold_spec j
    (finitePrimeThetaCuspAccuracyThreshold_le_positiveScreenIndex j)

theorem finitePrimeThetaCuspPositiveScreenIndex_pos (j : ℕ) (x : ℝ)
    (hx : -((j + 1 : ℕ) : ℝ) ≤ x) :
    0 < finitePrimeThetaCuspSource (finitePrimeThetaCuspPositiveScreenIndex j) x := by
  rcases le_total x 0 with hx0 | hx0
  · exact finitePrimeThetaCuspPositiveThreshold_spec j
      (finitePrimeThetaCuspPositiveThreshold_le_positiveScreenIndex j) x ⟨hx, hx0⟩
  · exact finitePrimeThetaCuspSource_pos_of_nonneg _ hx0

/-- Translated one-sided smooth cutoff at screen stage `j`. -/
def finitePrimeThetaCuspScreenCutoff (j : ℕ) (x : ℝ) : ℝ :=
  ccmSmoothHalflineCutoff (x + j)

theorem finitePrimeThetaCuspScreenCutoff_eq_zero (j : ℕ) {x : ℝ}
    (hx : x ≤ -((j + 1 : ℕ) : ℝ)) :
    finitePrimeThetaCuspScreenCutoff j x = 0 := by
  apply ccmSmoothHalflineCutoff_eq_zero
  push_cast at hx ⊢
  linarith

theorem finitePrimeThetaCuspScreenCutoff_eq_one (j : ℕ) {x : ℝ}
    (hx : -((j : ℕ) : ℝ) ≤ x) :
    finitePrimeThetaCuspScreenCutoff j x = 1 := by
  apply ccmSmoothHalflineCutoff_eq_one
  have hj : (0 : ℝ) ≤ (j : ℕ) := by positivity
  linarith

def finitePrimeThetaCuspRightScreen (j : ℕ) (x : ℝ) : ℝ :=
  finitePrimeThetaCuspScreenCutoff j x *
    finitePrimeThetaCuspSource (finitePrimeThetaCuspPositiveScreenIndex j) x

def finitePrimeThetaCuspEvenScreen (j : ℕ) (x : ℝ) : ℝ :=
  (finitePrimeThetaCuspRightScreen j x +
    finitePrimeThetaCuspRightScreen j (-x)) / 2

theorem finitePrimeThetaCuspEvenScreen_neg (j : ℕ) (x : ℝ) :
    finitePrimeThetaCuspEvenScreen j (-x) = finitePrimeThetaCuspEvenScreen j x := by
  unfold finitePrimeThetaCuspEvenScreen
  simp only [neg_neg]
  ring

theorem finitePrimeThetaCuspRightScreen_pos_of_ge_neg_nat
    (j : ℕ) {x : ℝ} (hx : -((j : ℕ) : ℝ) ≤ x) :
    0 < finitePrimeThetaCuspRightScreen j x := by
  rw [finitePrimeThetaCuspRightScreen,
    finitePrimeThetaCuspScreenCutoff_eq_one j hx, one_mul]
  exact finitePrimeThetaCuspPositiveScreenIndex_pos j x (by
    push_cast
    linarith)

theorem finitePrimeThetaCuspRightScreen_nonneg (j : ℕ) (x : ℝ) :
    0 ≤ finitePrimeThetaCuspRightScreen j x := by
  by_cases hx : x ≤ -((j + 1 : ℕ) : ℝ)
  · rw [finitePrimeThetaCuspRightScreen,
      finitePrimeThetaCuspScreenCutoff_eq_zero j hx, zero_mul]
  · unfold finitePrimeThetaCuspRightScreen
    exact mul_nonneg (ccmSmoothHalflineCutoff_nonneg _)
      (finitePrimeThetaCuspPositiveScreenIndex_pos j x (le_of_not_ge hx)).le

theorem finitePrimeThetaCuspEvenScreen_pos (j : ℕ) (x : ℝ) :
    0 < finitePrimeThetaCuspEvenScreen j x := by
  rcases le_total (-((j : ℕ) : ℝ)) x with hx | hx
  · have hr := finitePrimeThetaCuspRightScreen_pos_of_ge_neg_nat j hx
    have hrefNonneg := finitePrimeThetaCuspRightScreen_nonneg j (-x)
    unfold finitePrimeThetaCuspEvenScreen
    positivity
  · have hr := finitePrimeThetaCuspRightScreen_pos_of_ge_neg_nat j (x := -x) (by
      linarith)
    have hleftNonneg := finitePrimeThetaCuspRightScreen_nonneg j x
    unfold finitePrimeThetaCuspEvenScreen
    positivity

end RHTower
