import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic

/-!
# Route E right-to-left short-window transfer

An all-right short-interval supply theorem already contains a numerically downward supply theorem.
At height `y`, apply the right-window theorem at `y - 2 * h y`.  Monotonicity of `h` places that
entire window strictly below `y`, without changing its counted predicate.  This separates numerical
direction from Möbius-grade direction in cutoff-dependent factorization relations.
-/

namespace RHTower

open Finset

/-- Real-scale form used when the structured token centre is a quotient such as `n / t`. -/
theorem routeE_real_rightWindow_subset_leftWindow
    (h : ℝ → ℝ) (hmono : Monotone h) {y : ℝ}
    (hpos : 0 < h y) :
    Set.Ioc (y - 2 * h y) ((y - 2 * h y) + h (y - 2 * h y)) ⊆
      Set.Ioo (y - 2 * h y) y := by
  intro m hm
  refine ⟨hm.1, ?_⟩
  have hbase : y - 2 * h y ≤ y := by linarith
  have hwindow : h (y - 2 * h y) ≤ h y := hmono hbase
  linarith [hm.2]

/-- The right window based at `y - 2h(y)` lies inside the left window of radius `2h(y)` at `y`. -/
theorem routeE_rightWindow_subset_leftWindow
    (h : ℕ → ℕ) (hmono : Monotone h) {y : ℕ}
    (hfit : 2 * h y ≤ y) :
    Finset.Ioc (y - 2 * h y) ((y - 2 * h y) + h (y - 2 * h y)) ⊆
      Finset.Ioo (y - 2 * h y) y := by
  intro m hm
  rw [Finset.mem_Ioc] at hm
  rw [Finset.mem_Ioo]
  refine ⟨hm.1, ?_⟩
  have hbase : y - 2 * h y ≤ y := Nat.sub_le _ _
  have hwindow : h (y - 2 * h y) ≤ h y := hmono hbase
  omega

/-- Every counted right-window lower bound transfers unchanged to the corresponding left window. -/
theorem routeE_leftWindow_card_ge_rightWindow_card
    (h : ℕ → ℕ) (hmono : Monotone h) (A : ℕ → Prop) [DecidablePred A]
    {y D : ℕ} (hfit : 2 * h y ≤ y)
    (hsupply : D ≤
      ((Finset.Ioc (y - 2 * h y) ((y - 2 * h y) + h (y - 2 * h y))).filter A).card) :
    D ≤ ((Finset.Ioo (y - 2 * h y) y).filter A).card := by
  refine hsupply.trans (Finset.card_le_card ?_)
  exact Finset.filter_subset_filter _ (routeE_rightWindow_subset_leftWindow h hmono hfit)

/-- A nonempty all-right supply gives a predicate-preserving numerical predecessor within `2h(y)`. -/
theorem routeE_exists_leftWindow_of_rightWindow
    (h : ℕ → ℕ) (hmono : Monotone h) (A : ℕ → Prop) [DecidablePred A]
    {y : ℕ} (hfit : 2 * h y ≤ y)
    (hsupply : 0 <
      ((Finset.Ioc (y - 2 * h y) ((y - 2 * h y) + h (y - 2 * h y))).filter A).card) :
    ∃ m, A m ∧ y - 2 * h y < m ∧ m < y := by
  have hcard : 0 < ((Finset.Ioo (y - 2 * h y) y).filter A).card :=
    routeE_leftWindow_card_ge_rightWindow_card h hmono A hfit hsupply
  obtain ⟨m, hm⟩ := Finset.card_pos.mp hcard
  rw [Finset.mem_filter, Finset.mem_Ioo] at hm
  exact ⟨m, hm.2, hm.1.1, hm.1.2⟩

/-! ## Two-radius transpose-overlap boundary -/

/-- A token from the count-preserving two-radius shift can reverse an ordinary upward window edge
only at the single boundary point `y-h(y)`. -/
theorem routeE_twoShift_reverse_eq_singleBoundary
    (h : ℕ → ℕ) (hmono : Monotone h) {y m : ℕ}
    (hfit : 2 * h y ≤ y)
    (hm : m ∈ Finset.Ioc (y - 2 * h y)
      ((y - 2 * h y) + h (y - 2 * h y)))
    (hreverse : y ≤ m + h m) :
    m = y - h y := by
  rw [Finset.mem_Ioc] at hm
  have hbase : y - 2 * h y ≤ y := Nat.sub_le _ _
  have hxhy : h (y - 2 * h y) ≤ h y := hmono hbase
  have hmle : m ≤ y - h y := by omega
  have hmley : m ≤ y := hmle.trans (Nat.sub_le _ _)
  have hmhy : h m ≤ h y := hmono hmley
  omega

/-- Numerically reverse-compatible tokens in the two-radius shifted window. -/
def routeETwoShiftReverseOverlapWindow (h : ℕ → ℕ) (y : ℕ) : Finset ℕ :=
  (Finset.Ioc (y - 2 * h y)
    ((y - 2 * h y) + h (y - 2 * h y))).filter fun m => y ≤ m + h m

theorem routeE_twoShift_reverseOverlapWindow_subset_singleton
    (h : ℕ → ℕ) (hmono : Monotone h) {y : ℕ}
    (hfit : 2 * h y ≤ y) :
    routeETwoShiftReverseOverlapWindow h y ⊆ {y - h y} := by
  intro m hm
  rw [routeETwoShiftReverseOverlapWindow, Finset.mem_filter] at hm
  rw [Finset.mem_singleton]
  exact routeE_twoShift_reverse_eq_singleBoundary h hmono hfit hm.1 hm.2

/-- The two-radius shift has at most one numerically transpose-overlapping token. -/
theorem routeE_twoShift_reverseOverlapWindow_card_le_one
    (h : ℕ → ℕ) (hmono : Monotone h) {y : ℕ}
    (hfit : 2 * h y ≤ y) :
    (routeETwoShiftReverseOverlapWindow h y).card ≤ 1 := by
  calc
    (routeETwoShiftReverseOverlapWindow h y).card ≤ ({y - h y} : Finset ℕ).card :=
      Finset.card_le_card
        (routeE_twoShift_reverseOverlapWindow_subset_singleton h hmono hfit)
    _ = 1 := Finset.card_singleton _

/-! ## One-radius shift and transpose-overlap boundary -/

/-- Shifting by one radius places the right window in the corresponding closed left window. -/
theorem routeE_oneShift_rightWindow_subset_closedLeftWindow
    (h : ℕ → ℕ) (hmono : Monotone h) {y : ℕ}
    (hfit : h y ≤ y) :
    Finset.Ioc (y - h y) ((y - h y) + h (y - h y)) ⊆
      Finset.Ioc (y - h y) y := by
  intro m hm
  rw [Finset.mem_Ioc] at hm ⊢
  refine ⟨hm.1, ?_⟩
  have hbase : y - h y ≤ y := Nat.sub_le _ _
  have hwindow : h (y - h y) ≤ h y := hmono hbase
  omega

/-- If the counted predicate excludes `y`, the one-radius shift transfers every token strictly
below `y`, so the factor two in the unconditional transfer is unnecessary. -/
theorem routeE_oneShift_rightWindow_filter_subset_leftWindow_filter
    (h : ℕ → ℕ) (hmono : Monotone h) (A : ℕ → Prop) [DecidablePred A]
    {y : ℕ} (hfit : h y ≤ y) (hAy : ¬ A y) :
    (Finset.Ioc (y - h y) ((y - h y) + h (y - h y))).filter A ⊆
      (Finset.Ioo (y - h y) y).filter A := by
  intro m hm
  rw [Finset.mem_filter, Finset.mem_Ioc] at hm
  rw [Finset.mem_filter, Finset.mem_Ioo]
  refine ⟨⟨hm.1.1, ?_⟩, hm.2⟩
  have hclosed := routeE_oneShift_rightWindow_subset_closedLeftWindow h hmono hfit
    (by simpa only [Finset.mem_Ioc] using hm.1)
  rw [Finset.mem_Ioc] at hclosed
  exact lt_of_le_of_ne hclosed.2 (Ne.symm (fun hmy => hAy (hmy ▸ hm.2)))

/-- Predicate counts therefore transfer without loss at one-radius displacement whenever the
source point is excluded by the target predicate. -/
theorem routeE_oneShift_leftWindow_card_ge_rightWindow_card
    (h : ℕ → ℕ) (hmono : Monotone h) (A : ℕ → Prop) [DecidablePred A]
    {y D : ℕ} (hfit : h y ≤ y) (hAy : ¬ A y)
    (hsupply : D ≤
      ((Finset.Ioc (y - h y) ((y - h y) + h (y - h y))).filter A).card) :
    D ≤ ((Finset.Ioo (y - h y) y).filter A).card := by
  exact hsupply.trans (Finset.card_le_card
    (routeE_oneShift_rightWindow_filter_subset_leftWindow_filter h hmono A hfit hAy))

/-- A downward token from the one-radius shift which is not the reversal of an upward window edge
must lie in the initial strip whose width is the radius oscillation. -/
theorem routeE_oneShift_nonreverse_mem_oscillationBoundary
    (h : ℕ → ℕ) (hmono : Monotone h) {y m : ℕ}
    (hfit : h y ≤ y)
    (hm : m ∈ Finset.Ioc (y - h y) ((y - h y) + h (y - h y)))
    (hmy : m ≠ y) (hnotReverse : ¬y ≤ m + h m) :
    m ∈ Finset.Ioo (y - h y)
      ((y - h y) + (h y - h (y - h y))) := by
  rw [Finset.mem_Ioc] at hm
  rw [Finset.mem_Ioo]
  refine ⟨hm.1, ?_⟩
  have hbase : y - h y ≤ y := Nat.sub_le _ _
  have hxhy : h (y - h y) ≤ h y := hmono hbase
  have hmle : m ≤ y := by omega
  have hmlt : m < y := lt_of_le_of_ne hmle hmy
  have hxm : y - h y ≤ m := hm.1.le
  have hxmWindow : h (y - h y) ≤ h m := hmono hxm
  omega

/-- Downward one-shift edges which are neither diagonal nor reversals of upward window edges. -/
def routeEOneShiftNonreverseWindow (h : ℕ → ℕ) (y : ℕ) : Finset ℕ :=
  (Finset.Ioc (y - h y) ((y - h y) + h (y - h y))).filter fun m =>
    m ≠ y ∧ ¬y ≤ m + h m

theorem routeE_oneShift_nonreverseWindow_subset_oscillationBoundary
    (h : ℕ → ℕ) (hmono : Monotone h) {y : ℕ}
    (hfit : h y ≤ y) :
    routeEOneShiftNonreverseWindow h y ⊆
      Finset.Ioo (y - h y)
        ((y - h y) + (h y - h (y - h y))) := by
  intro m hm
  rw [routeEOneShiftNonreverseWindow, Finset.mem_filter] at hm
  exact routeE_oneShift_nonreverse_mem_oscillationBoundary h hmono hfit hm.1 hm.2.1 hm.2.2

/-- The number of non-reversible one-shift edges is at most the radius oscillation
`h(y)-h(y-h(y))`. -/
theorem routeE_oneShift_nonreverseWindow_card_le_radiusOscillation
    (h : ℕ → ℕ) (hmono : Monotone h) {y : ℕ}
    (hfit : h y ≤ y) :
    (routeEOneShiftNonreverseWindow h y).card ≤ h y - h (y - h y) := by
  calc
    (routeEOneShiftNonreverseWindow h y).card ≤
        (Finset.Ioo (y - h y)
          ((y - h y) + (h y - h (y - h y)))).card :=
      Finset.card_le_card
        (routeE_oneShift_nonreverseWindow_subset_oscillationBoundary h hmono hfit)
    _ ≤ h y - h (y - h y) := by
      simp only [Nat.card_Ioo]
      omega

/-- Tokens from the one-radius shifted supply which also pass the reverse-window test. -/
def routeEOneShiftReverseFilteredWindow
    (h : ℕ → ℕ) (A : ℕ → Prop) [DecidablePred A] (y : ℕ) : Finset ℕ :=
  (Finset.Ioc (y - h y) ((y - h y) + h (y - h y))).filter fun m =>
    A m ∧ y ≤ m + h m

/-- Imposing the symmetric reverse-window condition loses at most the exact radius oscillation.
This converts a one-sided token lower bound into a pair-stable token lower bound. -/
theorem routeE_oneShift_reverseFilteredWindow_card_ge_supply_sub_oscillation
    (h : ℕ → ℕ) (hmono : Monotone h) (A : ℕ → Prop) [DecidablePred A]
    {y D : ℕ} (hfit : h y ≤ y) (hAy : ¬A y)
    (hsupply : D ≤
      ((Finset.Ioc (y - h y) ((y - h y) + h (y - h y))).filter A).card) :
    D - (h y - h (y - h y)) ≤
      (routeEOneShiftReverseFilteredWindow h A y).card := by
  let base : Finset ℕ :=
    Finset.Ioc (y - h y) ((y - h y) + h (y - h y))
  let eligible : Finset ℕ := base.filter A
  have hbadSubset :
      eligible.filter (fun m => ¬y ≤ m + h m) ⊆ routeEOneShiftNonreverseWindow h y := by
    intro m hm
    simp only [eligible, base, Finset.mem_filter, Finset.mem_Ioc] at hm
    rw [routeEOneShiftNonreverseWindow, Finset.mem_filter]
    refine ⟨by simpa only [Finset.mem_Ioc] using hm.1.1, ?_⟩
    exact ⟨fun hmy => hAy (hmy ▸ hm.1.2), hm.2⟩
  have hbad : (eligible.filter (fun m => ¬y ≤ m + h m)).card ≤
      h y - h (y - h y) := by
    exact (Finset.card_le_card hbadSubset).trans
      (routeE_oneShift_nonreverseWindow_card_le_radiusOscillation h hmono hfit)
  have hpartition := eligible.card_filter_add_card_filter_not (fun m => y ≤ m + h m)
  have hgood :
      eligible.filter (fun m => y ≤ m + h m) =
        routeEOneShiftReverseFilteredWindow h A y := by
    ext m
    simp only [eligible, base, routeEOneShiftReverseFilteredWindow, Finset.mem_filter,
      Finset.mem_Ioc]
    tauto
  rw [hgood] at hpartition
  change D ≤ eligible.card at hsupply
  omega

/-- For the actual fixed-shell radius `h(y)=c*sqrt(y)`, one-shift radius oscillation is at most
`c²`.  At `c=(log X)^(1 : ℕ).55`, this is the subpower width `(log X)^(3 : ℕ).1`. -/
theorem routeE_sqrtRadius_sub_oneShift_le_sq
    (c y : ℝ) (hc : 0 ≤ c) (hy : c ^ (2 : ℕ) ≤ y) :
    c * Real.sqrt y - c * Real.sqrt (y - c * Real.sqrt y) ≤ c ^ (2 : ℕ) := by
  have hy0 : 0 ≤ y := le_trans (sq_nonneg c) hy
  have hsqrty : (Real.sqrt y) ^ (2 : ℕ) = y := Real.sq_sqrt hy0
  have hcsqrt : c ≤ Real.sqrt y := by
    apply (sq_le_sq₀ hc (Real.sqrt_nonneg y)).mp
    simpa [hsqrty] using hy
  have hshift0 : 0 ≤ y - c * Real.sqrt y := by
    have hmul := mul_le_mul_of_nonneg_right hcsqrt (Real.sqrt_nonneg y)
    nlinarith [hsqrty]
  have hlower0 : 0 ≤ Real.sqrt y - c := sub_nonneg.mpr hcsqrt
  have hlowerSq : (Real.sqrt y - c) ^ (2 : ℕ) ≤ y - c * Real.sqrt y := by
    nlinarith [hsqrty, mul_le_mul_of_nonneg_left hcsqrt hc]
  have hlower : Real.sqrt y - c ≤ Real.sqrt (y - c * Real.sqrt y) := by
    apply (sq_le_sq₀ hlower0 (Real.sqrt_nonneg _)).mp
    rw [Real.sq_sqrt hshift0]
    exact hlowerSq
  nlinarith [mul_le_mul_of_nonneg_left hlower hc]

end RHTower
