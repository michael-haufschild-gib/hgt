/-
# Böttcher tower — Brolin: finite singular-tail controls

This module is part of the split Brolin/Riesz-measure interface. Import
`GaloisForLFunctions.Bottcher.Brolin` for the full public surface.
-/
import GaloisForLFunctions.Bottcher.Brolin.BoundaryAtom

open Filter Topology MeasureTheory CompactlySupported Laplacian
open scoped Laplacian

namespace Bottcher

local instance singularTailLocalInst1 : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩

/-- Sum of pointwise differences over a finite multiset. -/
theorem multiset_sum_map_sub_real {α : Type*} (s : Multiset α)
    (f g : α → ℝ) :
    (s.map (fun x => f x - g x)).sum =
      (s.map f).sum - (s.map g).sum := by
  induction s using Multiset.induction_on with
  | empty =>
      simp
  | cons a s ih =>
      simp [ih]
      ring

/-- Compare finite sums over a multiset by a pointwise comparison on its
entries. -/
theorem multiset_sum_map_le_of_forall {α : Type*} (s : Multiset α)
    {f g : α → ℝ}
    (h : ∀ x ∈ s, f x ≤ g x) :
    (s.map f).sum ≤ (s.map g).sum := by
  induction s using Multiset.induction_on with
  | empty =>
      simp
  | cons a s ih =>
      have ha : f a ≤ g a := h a (by simp)
      have hs : ∀ x ∈ s, f x ≤ g x := by
        intro x hx
        exact h x (by simp [hx])
      simpa using add_le_add ha (ih hs)

/-- Equal pointwise data on a multiset have equal finite sums. -/
theorem multiset_sum_map_eq_of_forall {α : Type*} (s : Multiset α)
    {f g : α → ℝ}
    (h : ∀ x ∈ s, f x = g x) :
    (s.map f).sum = (s.map g).sum := by
  induction s using Multiset.induction_on with
  | empty =>
      simp
  | cons a s ih =>
      have ha : f a = g a := h a (by simp)
      have hs : ∀ x ∈ s, f x = g x := by
        intro x hx
        exact h x (by simp [hx])
      simpa [ha] using ih hs

/-- Sum of a constant over the entries selected by a decidable predicate. -/
theorem multiset_sum_map_if_const_eq_card_filter_mul {α : Type*}
    (s : Multiset α) (p : α → Prop) [DecidablePred p] (A : ℝ) :
    (s.map (fun x => if p x then A else 0)).sum =
      ((s.filter p).card : ℝ) * A := by
  induction s using Multiset.induction_on with
  | empty =>
      simp
  | cons a s ih =>
      by_cases ha : p a
      · simp [ha, ih, add_mul, add_comm]
      · simp [ha, ih]

/-- Exact pointwise singular-tail cost of truncating the logarithmic kernel. -/
theorem logKernel_sub_truncatedLogKernel_eq_if_norm_lt
    (z r : ℂ) (δ : ℝ) :
    logKernel z r - truncatedLogKernel z δ r =
      if ‖z - r‖ < δ then
        Real.log δ - Real.log ‖z - r‖
      else
        0 := by
  by_cases hclose : ‖z - r‖ < δ
  · unfold logKernel truncatedLogKernel
    rw [if_pos hclose, max_eq_left hclose.le]
    ring
  · unfold logKernel truncatedLogKernel
    rw [if_neg hclose, max_eq_right (le_of_not_gt hclose)]
    ring

/-- Pointwise singular-tail bound for one root.  If a root is outside the
truncation ball then the tail is zero; if it is inside, a lower separation
scale `η` bounds the tail by `-log η`. -/
theorem logKernel_sub_truncatedLogKernel_le_closeIndicator
    {z r : ℂ} {η δ : ℝ}
    (hηpos : 0 < η) (hδpos : 0 < δ) (hδle : δ ≤ 1)
    (hηsep : η ≤ ‖z - r‖) :
    logKernel z r - truncatedLogKernel z δ r ≤
      if ‖z - r‖ < δ then - Real.log η else 0 := by
  by_cases hclose : ‖z - r‖ < δ
  · have htrunc_nonneg : 0 ≤ truncatedLogKernel z δ r := by
      unfold truncatedLogKernel
      rw [max_eq_left hclose.le]
      exact neg_nonneg.mpr (Real.log_nonpos hδpos.le hδle)
    have hkernel_le : logKernel z r ≤ - Real.log η := by
      unfold logKernel
      exact neg_le_neg (Real.log_le_log hηpos hηsep)
    simp [hclose]
    linarith
  · have hδle_norm : δ ≤ ‖z - r‖ := le_of_not_gt hclose
    rw [truncatedLogKernel_eq_logKernel_of_le_norm hδle_norm]
    simp [hclose]

/-- Sharper pointwise singular-tail bound: on the truncation ball the cost is
bounded by the logarithmic width between the truncation scale `δ` and a lower
separation scale `η`. -/
theorem logKernel_sub_truncatedLogKernel_le_closeIndicator_logRange
    {z r : ℂ} {η δ : ℝ}
    (hηpos : 0 < η)
    (hηsep : η ≤ ‖z - r‖) :
    logKernel z r - truncatedLogKernel z δ r ≤
      if ‖z - r‖ < δ then
        Real.log δ - Real.log η
      else
        0 := by
  rw [logKernel_sub_truncatedLogKernel_eq_if_norm_lt]
  by_cases hclose : ‖z - r‖ < δ
  · simp [hclose]
    have hlog : Real.log η ≤ Real.log ‖z - r‖ :=
      Real.log_le_log hηpos hηsep
    linarith
  · simp [hclose]

/-- The finite singular tail at level `n`: the amount lost by replacing the
true finite logarithmic kernel with the `δ`-truncated kernel.  This is the
quantity that must be uniformly controlled to pass the zero finite boundary
potential to the limiting measure. -/
noncomputable def finiteBrolinSingularTail
    (c z : ℂ) (δ : ℝ) (n : ℕ) : ℝ :=
  logPotential (preBrolinMeasure c n) z -
    ∫ w, truncatedLogKernel z δ w ∂preBrolinMeasure c n

/-- Finite singular tail as a normalized root average.  This converts the
remaining hDisc analytic problem into a concrete estimate over the zero
pullback roots. -/
theorem finiteBrolinSingularTail_eq_root_average
    (c z : ℂ) (δ : ℝ) (n : ℕ) :
    finiteBrolinSingularTail c z δ n =
      (2 ^ n : ℝ)⁻¹ *
        ((quadraticPolyIterate c n).roots.map
          (fun r => logKernel z r - truncatedLogKernel z δ r)).sum := by
  unfold finiteBrolinSingularTail
  rw [logPotential_preBrolinMeasure_eq_scaled_rootLogKernelSum,
    integral_preBrolinMeasure_eq_root_average]
  rw [multiset_sum_map_sub_real]
  ring

/-- Exact finite singular tail as a normalized average of the true truncation
cost on close roots.  This is the annular-estimate entry point: only roots with
`‖z-r‖ < δ` contribute, and their contribution is exactly
`log δ - log ‖z-r‖`. -/
theorem finiteBrolinSingularTail_eq_root_average_truncationCost
    (c z : ℂ) (δ : ℝ) (n : ℕ) :
    finiteBrolinSingularTail c z δ n =
      (2 ^ n : ℝ)⁻¹ *
        ((quadraticPolyIterate c n).roots.map
          (fun r =>
            if ‖z - r‖ < δ then
              Real.log δ - Real.log ‖z - r‖
            else
              0)).sum := by
  rw [finiteBrolinSingularTail_eq_root_average]
  congr 1
  exact multiset_sum_map_eq_of_forall _ (fun r _hr =>
    logKernel_sub_truncatedLogKernel_eq_if_norm_lt z r δ)

/-- Finite singular-tail domination by any pointwise cost on the level roots.
This is the compiled interface for annular/cylinder estimates: once geometry
bounds the exact truncation cost root-by-root, the potential-theoretic finite
tail bound follows by summing. -/
theorem finiteBrolinSingularTail_le_rootAverageCost
    {c z : ℂ} {δ : ℝ} {n : ℕ} {cost : ℂ → ℝ}
    (hcost :
      ∀ r ∈ (quadraticPolyIterate c n).roots,
        (if ‖z - r‖ < δ then
          Real.log δ - Real.log ‖z - r‖
        else
          0) ≤ cost r) :
    finiteBrolinSingularTail c z δ n ≤
      (2 ^ n : ℝ)⁻¹ *
        ((quadraticPolyIterate c n).roots.map cost).sum := by
  rw [finiteBrolinSingularTail_eq_root_average_truncationCost]
  apply mul_le_mul_of_nonneg_left
  · exact multiset_sum_map_le_of_forall _ hcost
  · positivity

/-- The finite singular tail is nonnegative whenever the evaluation point is
not a level-`n` atom. -/
theorem finiteBrolinSingularTail_nonneg_of_iterate_ne_zero
    {c z : ℂ} {δ : ℝ} {n : ℕ} (hδ : 0 < δ)
    (hz : (quadratic c)^[n] z ≠ 0) :
    0 ≤ finiteBrolinSingularTail c z δ n := by
  unfold finiteBrolinSingularTail
  have hle :=
    integral_truncatedLogKernel_preBrolinMeasure_le_logPotential_of_iterate_ne_zero
      (c := c) (z := z) (δ := δ) (n := n) hδ hz
  linarith

/-- Finite singular tail bounded by the weighted count of roots in the
truncation ball, assuming a separation scale from the evaluation point to all
level-`n` roots.  This is the first root-counting form needed for the
disconnected cylinder estimate. -/
theorem finiteBrolinSingularTail_le_closeRootWeight
    {c z : ℂ} {η δ : ℝ} {n : ℕ}
    (hηpos : 0 < η) (hδpos : 0 < δ) (hδle : δ ≤ 1)
    (hηsep :
      ∀ r ∈ (quadraticPolyIterate c n).roots, η ≤ ‖z - r‖) :
    finiteBrolinSingularTail c z δ n ≤
      (2 ^ n : ℝ)⁻¹ *
        ((quadraticPolyIterate c n).roots.map
          (fun r => if ‖z - r‖ < δ then - Real.log η else 0)).sum := by
  rw [finiteBrolinSingularTail_eq_root_average]
  apply mul_le_mul_of_nonneg_left
  · exact multiset_sum_map_le_of_forall _ (fun r hr =>
      logKernel_sub_truncatedLogKernel_le_closeIndicator
        hηpos hδpos hδle (hηsep r hr))
  · positivity

/-- Finite singular tail bounded by the number of level-`n` roots in the
truncation ball.  This is the counting form of the tail estimate. -/
theorem finiteBrolinSingularTail_le_closeRootCount
    {c z : ℂ} {η δ : ℝ} {n : ℕ}
    (hηpos : 0 < η) (hδpos : 0 < δ) (hδle : δ ≤ 1)
    (hηsep :
      ∀ r ∈ (quadraticPolyIterate c n).roots, η ≤ ‖z - r‖) :
    finiteBrolinSingularTail c z δ n ≤
      (2 ^ n : ℝ)⁻¹ *
        (((quadraticPolyIterate c n).roots.filter
          (fun r => ‖z - r‖ < δ)).card : ℝ) *
          (- Real.log η) := by
  have h :=
    finiteBrolinSingularTail_le_closeRootWeight
      (c := c) (z := z) (η := η) (δ := δ) (n := n)
      hηpos hδpos hδle hηsep
  rw [multiset_sum_map_if_const_eq_card_filter_mul] at h
  simpa [mul_assoc] using h

/-- Finite singular tail bounded by the close-root count times the exact
logarithmic scale width `log δ - log η`. -/
theorem finiteBrolinSingularTail_le_closeRootLogRangeCount
    {c z : ℂ} {η δ : ℝ} {n : ℕ}
    (hηpos : 0 < η)
    (hηsep :
      ∀ r ∈ (quadraticPolyIterate c n).roots, η ≤ ‖z - r‖) :
    finiteBrolinSingularTail c z δ n ≤
      (2 ^ n : ℝ)⁻¹ *
        (((quadraticPolyIterate c n).roots.filter
          (fun r => ‖z - r‖ < δ)).card : ℝ) *
          (Real.log δ - Real.log η) := by
  rw [finiteBrolinSingularTail_eq_root_average]
  have hsum :
      ((quadraticPolyIterate c n).roots.map
        (fun r => logKernel z r - truncatedLogKernel z δ r)).sum ≤
        ((quadraticPolyIterate c n).roots.map
          (fun r => if ‖z - r‖ < δ then
            Real.log δ - Real.log η else 0)).sum :=
    multiset_sum_map_le_of_forall _ (fun r hr =>
      logKernel_sub_truncatedLogKernel_le_closeIndicator_logRange
        hηpos (hηsep r hr))
  have hsum' :
      ((quadraticPolyIterate c n).roots.map
        (fun r => logKernel z r - truncatedLogKernel z δ r)).sum ≤
        (((quadraticPolyIterate c n).roots.filter
          (fun r => ‖z - r‖ < δ)).card : ℝ) *
          (Real.log δ - Real.log η) := by
    rw [multiset_sum_map_if_const_eq_card_filter_mul] at hsum
    exact hsum
  have hmul := mul_le_mul_of_nonneg_left hsum'
    (by positivity : 0 ≤ (2 ^ n : ℝ)⁻¹)
  simpa [mul_assoc] using hmul

/-- Canonical finite singular-tail estimate.  At a disconnected boundary point,
the finite singular tail is controlled by the pre-Brolin mass of the
truncation ball, weighted by the logarithm of the actual finite separation
from that boundary point to the level roots. -/
theorem finiteBrolinSingularTail_le_canonicalSmallBallCost
    {c z : ℂ} {δ : ℝ} {n : ℕ}
    (hc : Disconnected c) (hzK : z ∈ filledJulia c)
    (hδpos : 0 < δ) (hδle : δ ≤ 1) :
    finiteBrolinSingularTail c z δ n ≤
      (preBrolinMeasure c n {w : ℂ | ‖z - w‖ < δ}).toReal *
        (- Real.log (finiteBrolinRootSeparation c z n)) := by
  have htail :=
    finiteBrolinSingularTail_le_closeRootCount
      (c := c) (z := z)
      (η := finiteBrolinRootSeparation c z n) (δ := δ) (n := n)
      (finiteBrolinRootSeparation_pos_of_mem_filledJulia_of_disconnected
        (c := c) (z := z) hc hzK n)
      hδpos hδle
      (fun r hr =>
        finiteBrolinRootSeparation_le_norm_sub_of_mem_filledJulia_of_disconnected
          (c := c) (z := z) (r := r) hc hzK hr)
  have hmass_eq :=
    preBrolinMeasure_ball_toReal_eq_scaled_closeRootCount
      (c := c) (z := z) (δ := δ) hδpos n
  simpa [hmass_eq, mul_assoc] using htail

/-- Sharpened canonical finite singular-tail estimate with the true logarithmic
width `log δ - log η_n`, where `η_n` is the finite separation from the
boundary point to the level-`n` zero-pullback roots. -/
theorem finiteBrolinSingularTail_le_canonicalSmallBallLogRangeCost
    {c z : ℂ} {δ : ℝ} {n : ℕ}
    (hc : Disconnected c) (hzK : z ∈ filledJulia c)
    (hδpos : 0 < δ) :
    finiteBrolinSingularTail c z δ n ≤
      (preBrolinMeasure c n {w : ℂ | ‖z - w‖ < δ}).toReal *
        (Real.log δ - Real.log (finiteBrolinRootSeparation c z n)) := by
  have htail :=
    finiteBrolinSingularTail_le_closeRootLogRangeCount
      (c := c) (z := z)
      (η := finiteBrolinRootSeparation c z n) (δ := δ) (n := n)
      (finiteBrolinRootSeparation_pos_of_mem_filledJulia_of_disconnected
        (c := c) (z := z) hc hzK n)
      (fun r hr =>
        finiteBrolinRootSeparation_le_norm_sub_of_mem_filledJulia_of_disconnected
          (c := c) (z := z) (r := r) hc hzK hr)
  have hmass_eq :=
    preBrolinMeasure_ball_toReal_eq_scaled_closeRootCount
      (c := c) (z := z) (δ := δ) hδpos n
  simpa [hmass_eq, mul_assoc] using htail

/-- Injective-ball finite singular-tail estimate.  If the truncation ball is a
single sheet for `f_c^[n]`, then the exact logarithmic loss is bounded by one
level-`n` atom times the logarithmic annulus width. -/
theorem finiteBrolinSingularTail_le_injectiveBallLogRangeCost
    {c z : ℂ} {η δ : ℝ} {n : ℕ}
    (hc : Disconnected c)
    (hηpos : 0 < η)
    (hηsep :
      ∀ r ∈ (quadraticPolyIterate c n).roots, η ≤ ‖z - r‖)
    (hηδ : η ≤ δ)
    (hinj : Set.InjOn ((quadratic c)^[n]) {w : ℂ | ‖z - w‖ < δ}) :
    finiteBrolinSingularTail c z δ n ≤
      (2 ^ n : ℝ)⁻¹ * (Real.log δ - Real.log η) := by
  have htail :=
    finiteBrolinSingularTail_le_closeRootLogRangeCount
      (c := c) (z := z) (η := η) (δ := δ) (n := n)
      hηpos hηsep
  have hcount :=
    closeRootCount_le_one_of_iterate_injOn_ball
      (c := c) (z := z) (δ := δ) (n := n) hc hinj
  have hcount_real :
      (((quadraticPolyIterate c n).roots.filter
        (fun r => ‖z - r‖ < δ)).card : ℝ) ≤ 1 := by
    exact_mod_cast hcount
  have hlog_nonneg : 0 ≤ Real.log δ - Real.log η :=
    sub_nonneg.mpr (Real.log_le_log hηpos hηδ)
  have hinner :
      (((quadraticPolyIterate c n).roots.filter
        (fun r => ‖z - r‖ < δ)).card : ℝ) *
          (Real.log δ - Real.log η) ≤
        1 * (Real.log δ - Real.log η) :=
    mul_le_mul_of_nonneg_right hcount_real hlog_nonneg
  have hscaled :
      (2 ^ n : ℝ)⁻¹ *
        ((((quadraticPolyIterate c n).roots.filter
          (fun r => ‖z - r‖ < δ)).card : ℝ) *
            (Real.log δ - Real.log η)) ≤
      (2 ^ n : ℝ)⁻¹ * (1 * (Real.log δ - Real.log η)) :=
    mul_le_mul_of_nonneg_left hinner (by positivity)
  calc
    finiteBrolinSingularTail c z δ n
        ≤ (2 ^ n : ℝ)⁻¹ *
            (((quadraticPolyIterate c n).roots.filter
              (fun r => ‖z - r‖ < δ)).card : ℝ) *
            (Real.log δ - Real.log η) := htail
    _ = (2 ^ n : ℝ)⁻¹ *
          ((((quadraticPolyIterate c n).roots.filter
            (fun r => ‖z - r‖ < δ)).card : ℝ) *
              (Real.log δ - Real.log η)) := by ring
    _ ≤ (2 ^ n : ℝ)⁻¹ * (1 * (Real.log δ - Real.log η)) := hscaled
    _ = (2 ^ n : ℝ)⁻¹ * (Real.log δ - Real.log η) := by ring

/-- Canonical disconnected-boundary version of the injective-ball singular
tail estimate, using the finite separation scale from the boundary point to
the level roots. -/
theorem finiteBrolinSingularTail_le_injectiveBallCanonicalLogRangeCost
    {c z : ℂ} {δ : ℝ} {n : ℕ}
    (hc : Disconnected c) (hzK : z ∈ filledJulia c)
    (hsepδ : finiteBrolinRootSeparation c z n ≤ δ)
    (hinj : Set.InjOn ((quadratic c)^[n]) {w : ℂ | ‖z - w‖ < δ}) :
    finiteBrolinSingularTail c z δ n ≤
      (2 ^ n : ℝ)⁻¹ *
        (Real.log δ - Real.log (finiteBrolinRootSeparation c z n)) :=
  finiteBrolinSingularTail_le_injectiveBallLogRangeCost
    (c := c) (z := z)
    (η := finiteBrolinRootSeparation c z n) (δ := δ) (n := n)
    hc
    (finiteBrolinRootSeparation_pos_of_mem_filledJulia_of_disconnected
      (c := c) (z := z) hc hzK n)
    (fun r hr =>
        finiteBrolinRootSeparation_le_norm_sub_of_mem_filledJulia_of_disconnected
        (c := c) (z := z) (r := r) hc hzK hr)
    hsepδ hinj

/-- If the truncation scale lies below a known root-separation scale, then no
level root contributes to the finite singular tail. -/
theorem finiteBrolinSingularTail_eq_zero_of_delta_le_separation
    {c z : ℂ} {η δ : ℝ} {n : ℕ}
    (hηsep :
      ∀ r ∈ (quadraticPolyIterate c n).roots, η ≤ ‖z - r‖)
    (hδη : δ ≤ η) :
    finiteBrolinSingularTail c z δ n = 0 := by
  rw [finiteBrolinSingularTail_eq_root_average_truncationCost]
  have hsum :
      ((quadraticPolyIterate c n).roots.map
        (fun r =>
          if ‖z - r‖ < δ then
            Real.log δ - Real.log ‖z - r‖
          else
            0)).sum =
        ((quadraticPolyIterate c n).roots.map (fun _r : ℂ => (0 : ℝ))).sum :=
    multiset_sum_map_eq_of_forall _ (fun r hr => by
      have hδdist : δ ≤ ‖z - r‖ := le_trans hδη (hηsep r hr)
      simp [not_lt_of_ge hδdist])
  rw [hsum]
  simp

/-- Injective-ball finite singular-tail estimate with the logarithmic width
clipped at zero.  This is the usable cylinder form: below the separation scale
the tail is zero, and above it injectivity leaves at most one contributing
atom. -/
theorem finiteBrolinSingularTail_le_injectiveBallCanonicalClippedLogRangeCost
    {c z : ℂ} {δ : ℝ} {n : ℕ}
    (hc : Disconnected c) (hzK : z ∈ filledJulia c)
    (hinj : Set.InjOn ((quadratic c)^[n]) {w : ℂ | ‖z - w‖ < δ}) :
    finiteBrolinSingularTail c z δ n ≤
      (2 ^ n : ℝ)⁻¹ *
        max 0 (Real.log δ - Real.log (finiteBrolinRootSeparation c z n)) := by
  by_cases hsepδ : finiteBrolinRootSeparation c z n ≤ δ
  · have htail :=
      finiteBrolinSingularTail_le_injectiveBallCanonicalLogRangeCost
        (c := c) (z := z) (δ := δ) (n := n) hc hzK hsepδ hinj
    have hlog_nonneg :
        0 ≤ Real.log δ - Real.log (finiteBrolinRootSeparation c z n) := by
      exact sub_nonneg.mpr
        (Real.log_le_log
          (finiteBrolinRootSeparation_pos_of_mem_filledJulia_of_disconnected
            (c := c) (z := z) hc hzK n)
          hsepδ)
    simpa [max_eq_right hlog_nonneg] using htail
  · have hδsep : δ ≤ finiteBrolinRootSeparation c z n :=
      le_of_lt (lt_of_not_ge hsepδ)
    have hzero :=
      finiteBrolinSingularTail_eq_zero_of_delta_le_separation
        (c := c) (z := z) (δ := δ) (n := n)
        (η := finiteBrolinRootSeparation c z n)
        (fun r hr =>
          finiteBrolinRootSeparation_le_norm_sub_of_mem_filledJulia_of_disconnected
            (c := c) (z := z) (r := r) hc hzK hr)
        hδsep
    rw [hzero]
    exact mul_nonneg (by positivity) (le_max_left _ _)

/-- Finite cylinder-cover singular-tail estimate.  The close zero-pullbacks
need not lie in one round injectivity ball; it is enough that they are covered
by finitely many injective cylinder charts. -/
theorem finiteBrolinSingularTail_le_cylinderCoverCanonicalClippedLogRangeCost
    {c z : ℂ} {δ : ℝ} {n : ℕ} {ι : Type*}
    {I : Finset ι} {S : ι → Set ℂ}
    (hc : Disconnected c) (hzK : z ∈ filledJulia c)
    (hinj : ∀ i, i ∈ I → Set.InjOn ((quadratic c)^[n]) (S i))
    (hcover :
      ∀ r ∈ (quadraticPolyIterate c n).roots, ‖z - r‖ < δ →
        ∃ i, i ∈ I ∧ r ∈ S i) :
    finiteBrolinSingularTail c z δ n ≤
      (2 ^ n : ℝ)⁻¹ * (I.card : ℝ) *
        max 0
          (Real.log δ - Real.log (finiteBrolinRootSeparation c z n)) := by
  by_cases hsepδ : finiteBrolinRootSeparation c z n ≤ δ
  · have htail :=
      finiteBrolinSingularTail_le_closeRootLogRangeCount
        (c := c) (z := z)
        (η := finiteBrolinRootSeparation c z n) (δ := δ) (n := n)
        (finiteBrolinRootSeparation_pos_of_mem_filledJulia_of_disconnected
          (c := c) (z := z) hc hzK n)
        (fun r hr =>
          finiteBrolinRootSeparation_le_norm_sub_of_mem_filledJulia_of_disconnected
            (c := c) (z := z) (r := r) hc hzK hr)
    have hcount :=
      closeRootCount_le_finset_card_of_iterate_injOn_cover
        (c := c) (z := z) (δ := δ) (n := n)
        (I := I) (S := S) hc hinj hcover
    have hcount_real :
        (((quadraticPolyIterate c n).roots.filter
          (fun r => ‖z - r‖ < δ)).card : ℝ) ≤
          (I.card : ℝ) := by
      exact_mod_cast hcount
    have hlog_nonneg :
        0 ≤ Real.log δ - Real.log (finiteBrolinRootSeparation c z n) := by
      exact sub_nonneg.mpr
        (Real.log_le_log
          (finiteBrolinRootSeparation_pos_of_mem_filledJulia_of_disconnected
            (c := c) (z := z) hc hzK n)
          hsepδ)
    have hinner :
        (((quadraticPolyIterate c n).roots.filter
          (fun r => ‖z - r‖ < δ)).card : ℝ) *
            (Real.log δ -
              Real.log (finiteBrolinRootSeparation c z n)) ≤
          (I.card : ℝ) *
            (Real.log δ -
              Real.log (finiteBrolinRootSeparation c z n)) :=
      mul_le_mul_of_nonneg_right hcount_real hlog_nonneg
    have hscaled :
        (2 ^ n : ℝ)⁻¹ *
          ((((quadraticPolyIterate c n).roots.filter
            (fun r => ‖z - r‖ < δ)).card : ℝ) *
              (Real.log δ -
                Real.log (finiteBrolinRootSeparation c z n))) ≤
        (2 ^ n : ℝ)⁻¹ *
          ((I.card : ℝ) *
            (Real.log δ -
              Real.log (finiteBrolinRootSeparation c z n))) :=
      mul_le_mul_of_nonneg_left hinner (by positivity)
    calc
      finiteBrolinSingularTail c z δ n
          ≤ (2 ^ n : ℝ)⁻¹ *
              (((quadraticPolyIterate c n).roots.filter
                (fun r => ‖z - r‖ < δ)).card : ℝ) *
              (Real.log δ -
                Real.log (finiteBrolinRootSeparation c z n)) := htail
      _ = (2 ^ n : ℝ)⁻¹ *
            ((((quadraticPolyIterate c n).roots.filter
              (fun r => ‖z - r‖ < δ)).card : ℝ) *
                (Real.log δ -
                  Real.log (finiteBrolinRootSeparation c z n))) := by ring
      _ ≤ (2 ^ n : ℝ)⁻¹ *
            ((I.card : ℝ) *
              (Real.log δ -
                Real.log (finiteBrolinRootSeparation c z n))) := hscaled
      _ = (2 ^ n : ℝ)⁻¹ * (I.card : ℝ) *
            (Real.log δ -
              Real.log (finiteBrolinRootSeparation c z n)) := by ring
      _ = (2 ^ n : ℝ)⁻¹ * (I.card : ℝ) *
            max 0
              (Real.log δ -
                Real.log (finiteBrolinRootSeparation c z n)) := by
          rw [max_eq_right hlog_nonneg]
  · have hδsep : δ ≤ finiteBrolinRootSeparation c z n :=
      le_of_lt (lt_of_not_ge hsepδ)
    have hzero :=
      finiteBrolinSingularTail_eq_zero_of_delta_le_separation
        (c := c) (z := z) (δ := δ) (n := n)
        (η := finiteBrolinRootSeparation c z n)
        (fun r hr =>
          finiteBrolinRootSeparation_le_norm_sub_of_mem_filledJulia_of_disconnected
            (c := c) (z := z) (r := r) hc hzK hr)
        hδsep
    rw [hzero]
    exact mul_nonneg
      (mul_nonneg (by positivity) (by positivity))
      (le_max_left _ _)

/-- Finite-level singular-tail control implies the missing canonical boundary
inequality at one integrable boundary point.  The tail is measured before
taking the compactness limit: the finite potential tends to zero on `K_c`, the
fixed truncation passes to `μ_c`, and a vanishing finite tail forces the
limiting truncated integral to be arbitrarily close to zero from below. -/
theorem gapAMu_boundary_nonnegative_of_preBrolin_singularTail_control
    {c z : ℂ} (hc : Disconnected c) (hzK : z ∈ filledJulia c)
    (hint : Integrable (fun w => logKernel z w) (gapAMu c))
    (htail :
      ∀ ε : ℝ, 0 < ε →
        ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧
          ∀ᶠ k in atTop,
            logPotential
                (preBrolinMeasure c (brolinLimitSubsequence c k)) z -
              ∫ w, truncatedLogKernel z δ w
                ∂preBrolinMeasure c (brolinLimitSubsequence c k) ≤ ε) :
    0 ≤ logPotential (gapAMu c) z := by
  by_contra hnot
  let U : ℝ := logPotential (gapAMu c) z
  have hUneg : U < 0 := by
    dsimp [U]
    exact lt_of_not_ge hnot
  let ε : ℝ := -U / 2
  have hεpos : 0 < ε := by
    dsimp [ε]
    linarith
  rcases htail ε hεpos with ⟨δ, hδpos, hδle, htail_event⟩
  let T : ℝ := ∫ w, truncatedLogKernel z δ w ∂gapAMu c
  have hfinitePotential :
      Tendsto
        (fun k : ℕ =>
          logPotential
            (preBrolinMeasure c (brolinLimitSubsequence c k)) z)
        atTop (𝓝 0) := by
    have hneg :=
      neg_logPotential_preBrolinMeasure_limitSubseq_tendsto_zero_filledJulia_of_disconnected
        (c := c) (z := z) hc hzK
    simpa using hneg.neg
  have htrunc :
      Tendsto
        (fun k : ℕ =>
          ∫ w, truncatedLogKernel z δ w
            ∂preBrolinMeasure c (brolinLimitSubsequence c k))
        atTop (𝓝 T) := by
    dsimp [T]
    simpa [gapAMu_eq_brolinMu, brolinMu] using
      truncatedLogKernel_preBrolinMeasure_subseq_integral_tendsto_limiting
        c z hδpos
  have hdiff :
      Tendsto
        (fun k : ℕ =>
          logPotential
              (preBrolinMeasure c (brolinLimitSubsequence c k)) z -
            ∫ w, truncatedLogKernel z δ w
              ∂preBrolinMeasure c (brolinLimitSubsequence c k))
        atTop (𝓝 (0 - T)) :=
    hfinitePotential.sub htrunc
  have hlim_le : 0 - T ≤ ε :=
    le_of_tendsto hdiff htail_event
  have hTlower : -ε ≤ T := by
    linarith
  have hTupper : T ≤ U := by
    dsimp [T, U]
    exact integral_truncatedLogKernel_gapAMu_le_logPotential_of_integrable
      (c := c) (z := z) hc hzK hδpos hδle hint
  have hU_lt_lower : U < -ε := by
    dsimp [ε]
    linarith
  linarith

/-- hDisc closure from finite-level singular-tail control at every finite
canonical boundary kernel.  This is the pre-Brolin uniform-integrability form
of the remaining analytic passage: no boundary value is assumed for `μ_c`;
it is forced by the finite zero-potential convergence plus tail control. -/
theorem gapAMu_hasGreenPotentialRepresentation_of_preBrolin_singularTail_control
    {c : ℂ} (hc : Disconnected c)
    (htail :
      ∀ z : ℂ, z ∈ filledJulia c →
        Integrable (fun w => logKernel z w) (gapAMu c) →
        ∀ ε : ℝ, 0 < ε →
          ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧
            ∀ᶠ k in atTop,
              logPotential
                  (preBrolinMeasure c (brolinLimitSubsequence c k)) z -
                ∫ w, truncatedLogKernel z δ w
                  ∂preBrolinMeasure c (brolinLimitSubsequence c k) ≤ ε) :
    HasGreenPotentialRepresentation c (gapAMu c) := by
  rw [gapAMu_hasGreenPotentialRepresentation_iff_boundary_integrable_nonnegative hc]
  intro z hzK hint
  exact gapAMu_boundary_nonnegative_of_preBrolin_singularTail_control
    (c := c) (z := z) hc hzK hint (htail z hzK hint)

/-- Same hDisc closure, stated with the named finite singular tail.  This is
the form intended for the next geometric estimate: prove that
`finiteBrolinSingularTail` is eventually small at every finite canonical
boundary kernel. -/
theorem gapAMu_hasGreenPotentialRepresentation_of_finiteBrolinSingularTail_control
    {c : ℂ} (hc : Disconnected c)
    (htail :
      ∀ z : ℂ, z ∈ filledJulia c →
        Integrable (fun w => logKernel z w) (gapAMu c) →
        ∀ ε : ℝ, 0 < ε →
          ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧
            ∀ᶠ k in atTop,
              finiteBrolinSingularTail c z δ
                (brolinLimitSubsequence c k) ≤ ε) :
    HasGreenPotentialRepresentation c (gapAMu c) := by
  exact gapAMu_hasGreenPotentialRepresentation_of_preBrolin_singularTail_control
    (c := c) hc
    (fun z hzK hint ε hε => by
      rcases htail z hzK hint ε hε with ⟨δ, hδpos, hδle, hevent⟩
      exact ⟨δ, hδpos, hδle, by
        simpa [finiteBrolinSingularTail] using hevent⟩)

/-- Root-count version of the GAP-A closure.  It is the hDisc-facing form of
the Brolin/Riesz boundary problem: for each finite canonical boundary kernel,
it is enough to bound the normalized number of level roots in a small
truncation ball, with the actual level-dependent separation scale retained in
the logarithmic weight. -/
theorem gapAMu_hasGreenPotentialRepresentation_of_closeRootCount_control
    {c : ℂ} (hc : Disconnected c)
    (hcount :
      ∀ z : ℂ, z ∈ filledJulia c →
        Integrable (fun w => logKernel z w) (gapAMu c) →
        ∀ ε : ℝ, 0 < ε →
          ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧
            ∀ᶠ k in atTop,
              ∃ η : ℝ, 0 < η ∧
                (∀ r ∈ (quadraticPolyIterate c
                    (brolinLimitSubsequence c k)).roots,
                  η ≤ ‖z - r‖) ∧
                (2 ^ (brolinLimitSubsequence c k) : ℝ)⁻¹ *
                  (((quadraticPolyIterate c
                    (brolinLimitSubsequence c k)).roots.filter
                      (fun r => ‖z - r‖ < δ)).card : ℝ) *
                    (- Real.log η) ≤ ε) :
    HasGreenPotentialRepresentation c (gapAMu c) := by
  apply gapAMu_hasGreenPotentialRepresentation_of_finiteBrolinSingularTail_control
    (c := c) hc
  intro z hzK hint ε hε
  rcases hcount z hzK hint ε hε with ⟨δ, hδpos, hδle, hcount_event⟩
  refine ⟨δ, hδpos, hδle, ?_⟩
  filter_upwards [hcount_event] with k hk
  rcases hk with ⟨η, hηpos, hηsep, hbound⟩
  have htail :=
    finiteBrolinSingularTail_le_closeRootCount
      (c := c) (z := z) (η := η) (δ := δ)
      (n := brolinLimitSubsequence c k)
      hηpos hδpos hδle hηsep
  exact le_trans htail hbound

/-- Small-ball-mass version of the GAP-A closure.  This is the same criterion
as `gapAMu_hasGreenPotentialRepresentation_of_closeRootCount_control`, but
expressed through the finite pre-Brolin measures themselves. -/
theorem gapAMu_hasGreenPotentialRepresentation_of_preBrolinSmallBallMass_control
    {c : ℂ} (hc : Disconnected c)
    (hmass :
      ∀ z : ℂ, z ∈ filledJulia c →
        Integrable (fun w => logKernel z w) (gapAMu c) →
        ∀ ε : ℝ, 0 < ε →
          ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧
            ∀ᶠ k in atTop,
              ∃ η : ℝ, 0 < η ∧
                (∀ r ∈ (quadraticPolyIterate c
                    (brolinLimitSubsequence c k)).roots,
                  η ≤ ‖z - r‖) ∧
                (preBrolinMeasure c (brolinLimitSubsequence c k)
                    {w : ℂ | ‖z - w‖ < δ}).toReal *
                    (- Real.log η) ≤ ε) :
    HasGreenPotentialRepresentation c (gapAMu c) := by
  apply gapAMu_hasGreenPotentialRepresentation_of_closeRootCount_control
    (c := c) hc
  intro z hzK hint ε hε
  rcases hmass z hzK hint ε hε with ⟨δ, hδpos, hδle, hmass_event⟩
  refine ⟨δ, hδpos, hδle, ?_⟩
  filter_upwards [hmass_event] with k hk
  rcases hk with ⟨η, hηpos, hηsep, hbound⟩
  refine ⟨η, hηpos, hηsep, ?_⟩
  have hmass_eq :=
    preBrolinMeasure_ball_toReal_eq_scaled_closeRootCount
      (c := c) (z := z) (δ := δ) hδpos
      (n := brolinLimitSubsequence c k)
  simpa [hmass_eq, mul_assoc] using hbound

/-- Canonical small-ball-mass closure for GAP-A.  The only remaining estimate
is now a finite statement: the pre-Brolin mass of the `δ`-ball around a
boundary point, weighted by the logarithm of the actual finite separation from
that boundary point to the level roots, is eventually arbitrarily small. -/
theorem gapAMu_hasGreenPotentialRepresentation_of_canonicalSmallBallMass_control
    {c : ℂ} (hc : Disconnected c)
    (hmass :
      ∀ z : ℂ, z ∈ filledJulia c →
        Integrable (fun w => logKernel z w) (gapAMu c) →
        ∀ ε : ℝ, 0 < ε →
          ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧
            ∀ᶠ k in atTop,
              (preBrolinMeasure c (brolinLimitSubsequence c k)
                  {w : ℂ | ‖z - w‖ < δ}).toReal *
                (- Real.log
                  (finiteBrolinRootSeparation c z
                    (brolinLimitSubsequence c k))) ≤ ε) :
    HasGreenPotentialRepresentation c (gapAMu c) := by
  apply gapAMu_hasGreenPotentialRepresentation_of_preBrolinSmallBallMass_control
    (c := c) hc
  intro z hzK hint ε hε
  rcases hmass z hzK hint ε hε with ⟨δ, hδpos, hδle, hmass_event⟩
  refine ⟨δ, hδpos, hδle, ?_⟩
  filter_upwards [hmass_event] with k hk
  refine
    ⟨finiteBrolinRootSeparation c z (brolinLimitSubsequence c k),
      finiteBrolinRootSeparation_pos_of_mem_filledJulia_of_disconnected
        (c := c) (z := z) hc hzK (brolinLimitSubsequence c k),
      ?_, hk⟩
  intro r hr
  exact
    finiteBrolinRootSeparation_le_norm_sub_of_mem_filledJulia_of_disconnected
      (c := c) (z := z) (r := r) hc hzK hr

/-- Sharpened canonical small-ball closure for GAP-A.  The finite estimate to
prove is the actual singular integral cost: pre-Brolin mass in the truncation
ball times the logarithmic width from `δ` down to the finite root-separation
scale. -/
theorem gapAMu_hasGreenPotentialRepresentation_of_canonicalSmallBallLogRange_control
    {c : ℂ} (hc : Disconnected c)
    (hmass :
      ∀ z : ℂ, z ∈ filledJulia c →
        Integrable (fun w => logKernel z w) (gapAMu c) →
        ∀ ε : ℝ, 0 < ε →
          ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧
            ∀ᶠ k in atTop,
              (preBrolinMeasure c (brolinLimitSubsequence c k)
                  {w : ℂ | ‖z - w‖ < δ}).toReal *
                (Real.log δ -
                  Real.log
                    (finiteBrolinRootSeparation c z
                      (brolinLimitSubsequence c k))) ≤ ε) :
    HasGreenPotentialRepresentation c (gapAMu c) := by
  apply gapAMu_hasGreenPotentialRepresentation_of_finiteBrolinSingularTail_control
    (c := c) hc
  intro z hzK hint ε hε
  rcases hmass z hzK hint ε hε with ⟨δ, hδpos, hδle, hmass_event⟩
  refine ⟨δ, hδpos, hδle, ?_⟩
  filter_upwards [hmass_event] with k hk
  exact le_trans
    (finiteBrolinSingularTail_le_canonicalSmallBallLogRangeCost
      (c := c) (z := z) (δ := δ)
      (n := brolinLimitSubsequence c k) hc hzK hδpos)
    hk

/-- hDisc-facing cylinder closure for GAP-A.  It is enough to find, at each
finite canonical boundary kernel, a fixed small truncation ball on which the
selected finite iterates are eventually injective, with the clipped finite
logarithmic width decaying at the `2⁻ⁿ` scale. -/
theorem gapAMu_hasGreenPotentialRepresentation_of_injectiveBallClippedLogRange_control
    {c : ℂ} (hc : Disconnected c)
    (hgeom :
      ∀ z : ℂ, z ∈ filledJulia c →
        Integrable (fun w => logKernel z w) (gapAMu c) →
        ∀ ε : ℝ, 0 < ε →
          ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧
            ∀ᶠ k in atTop,
              Set.InjOn
                ((quadratic c)^[brolinLimitSubsequence c k])
                {w : ℂ | ‖z - w‖ < δ} ∧
              (2 ^ (brolinLimitSubsequence c k) : ℝ)⁻¹ *
                max 0
                  (Real.log δ -
                    Real.log
                      (finiteBrolinRootSeparation c z
                        (brolinLimitSubsequence c k))) ≤ ε) :
    HasGreenPotentialRepresentation c (gapAMu c) := by
  apply gapAMu_hasGreenPotentialRepresentation_of_finiteBrolinSingularTail_control
    (c := c) hc
  intro z hzK hint ε hε
  rcases hgeom z hzK hint ε hε with ⟨δ, hδpos, hδle, hgeom_event⟩
  refine ⟨δ, hδpos, hδle, ?_⟩
  filter_upwards [hgeom_event] with k hk
  rcases hk with ⟨hinj, hbound⟩
  exact le_trans
    (finiteBrolinSingularTail_le_injectiveBallCanonicalClippedLogRangeCost
      (c := c) (z := z) (δ := δ)
      (n := brolinLimitSubsequence c k) hc hzK hinj)
    hbound

/-- hDisc-facing finite-cylinder-cover closure for GAP-A, with the exact
clipped count estimate left as the geometric input.  This is the round-ball
injectivity criterion with the false geometric bottleneck removed: hDisc may
cover the close zero-pullback atoms by finitely many injective cylinder charts
and prove the corresponding weighted count tends to zero. -/
theorem gapAMu_hasGreenPotentialRepresentation_of_cylinderCoverClippedLogRange_control
    {c : ℂ} {ι : Type*} (hc : Disconnected c)
    (hgeom :
      ∀ z : ℂ, z ∈ filledJulia c →
        Integrable (fun w => logKernel z w) (gapAMu c) →
        ∀ ε : ℝ, 0 < ε →
          ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧
            ∀ᶠ k in atTop,
              ∃ I : Finset ι, ∃ S : ι → Set ℂ,
                (∀ i, i ∈ I →
                  Set.InjOn
                    ((quadratic c)^[brolinLimitSubsequence c k])
                    (S i)) ∧
                (∀ r ∈ (quadraticPolyIterate c
                    (brolinLimitSubsequence c k)).roots,
                  ‖z - r‖ < δ →
                    ∃ i, i ∈ I ∧ r ∈ S i) ∧
                (2 ^ (brolinLimitSubsequence c k) : ℝ)⁻¹ *
                  (I.card : ℝ) *
                  max 0
                    (Real.log δ -
                      Real.log
                        (finiteBrolinRootSeparation c z
                          (brolinLimitSubsequence c k))) ≤ ε) :
    HasGreenPotentialRepresentation c (gapAMu c) := by
  apply gapAMu_hasGreenPotentialRepresentation_of_finiteBrolinSingularTail_control
    (c := c) hc
  intro z hzK hint ε hε
  rcases hgeom z hzK hint ε hε with ⟨δ, hδpos, hδle, hgeom_event⟩
  refine ⟨δ, hδpos, hδle, ?_⟩
  filter_upwards [hgeom_event] with k hk
  rcases hk with ⟨I, S, hinj, hcover, hbound⟩
  exact le_trans
    (finiteBrolinSingularTail_le_cylinderCoverCanonicalClippedLogRangeCost
      (c := c) (z := z) (δ := δ)
      (n := brolinLimitSubsequence c k)
      (I := I) (S := S) hc hzK hinj hcover)
    hbound

/-- The polynomial factor in `n` is still killed by the canonical `2⁻ⁿ`
weight. -/
theorem tendsto_nat_mul_inv_two_pow :
    Tendsto (fun n : ℕ => (n : ℝ) * (2 ^ n : ℝ)⁻¹) atTop (𝓝 0) := by
  have h :=
    tendsto_self_mul_const_pow_of_lt_one
      (r := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
  simpa [one_div, inv_pow, mul_comm] using h

/-- An exponential lower bound on the finite root separation leaves only a
linear logarithmic loss. -/
theorem clippedLogRange_le_linear_of_exp_sep
    {c z : ℂ} {δ A : ℝ} {n : ℕ}
    (hδpos : 0 < δ) (hδle : δ ≤ 1) (hApos : 0 < A)
    (hsep :
      Real.exp (-(A * (n : ℝ))) ≤ finiteBrolinRootSeparation c z n) :
    max 0
      (Real.log δ - Real.log (finiteBrolinRootSeparation c z n)) ≤
        A * (n : ℝ) := by
  have hlogsep_lower :
      -(A * (n : ℝ)) ≤
        Real.log (finiteBrolinRootSeparation c z n) := by
    calc
      -(A * (n : ℝ)) =
          Real.log (Real.exp (-(A * (n : ℝ)))) := by
            rw [Real.log_exp]
      _ ≤ Real.log (finiteBrolinRootSeparation c z n) :=
          Real.log_le_log (Real.exp_pos _) hsep
  have hlogδ : Real.log δ ≤ 0 :=
    Real.log_nonpos hδpos.le hδle
  have hlinear :
      Real.log δ - Real.log (finiteBrolinRootSeparation c z n) ≤
        A * (n : ℝ) := by
    linarith
  have hAnonneg : 0 ≤ A * (n : ℝ) :=
    mul_nonneg hApos.le (by positivity)
  exact max_le hAnonneg hlinear

/-- Scaled version of `clippedLogRange_le_linear_of_exp_sep`, in the exact
form needed by the injective-cylinder criterion. -/
theorem scaledClippedLogRange_le_linear_of_exp_sep
    {c z : ℂ} {δ A : ℝ} {n : ℕ}
    (hδpos : 0 < δ) (hδle : δ ≤ 1) (hApos : 0 < A)
    (hsep :
      Real.exp (-(A * (n : ℝ))) ≤ finiteBrolinRootSeparation c z n) :
    (2 ^ n : ℝ)⁻¹ *
      max 0
        (Real.log δ - Real.log (finiteBrolinRootSeparation c z n)) ≤
      A * ((n : ℝ) * (2 ^ n : ℝ)⁻¹) := by
  have hlog :=
    clippedLogRange_le_linear_of_exp_sep
      (c := c) (z := z) (δ := δ) (A := A) (n := n)
      hδpos hδle hApos hsep
  have hmul :=
    mul_le_mul_of_nonneg_left hlog (by positivity : 0 ≤ (2 ^ n : ℝ)⁻¹)
  calc
    (2 ^ n : ℝ)⁻¹ *
        max 0
          (Real.log δ -
            Real.log (finiteBrolinRootSeparation c z n))
        ≤ (2 ^ n : ℝ)⁻¹ * (A * (n : ℝ)) := hmul
    _ = A * ((n : ℝ) * (2 ^ n : ℝ)⁻¹) := by ring

/-- Cover-count version of the exponential-separation bound.  A uniformly
bounded number of injective cylinders still leaves a vanishing `n 2⁻ⁿ`
logarithmic cost. -/
theorem coverScaledClippedLogRange_le_linear_of_exp_sep
    {c z : ℂ} {δ A B : ℝ} {M n : ℕ}
    (hδpos : 0 < δ) (hδle : δ ≤ 1) (hApos : 0 < A)
    (hBnonneg : 0 ≤ B) (hM : (M : ℝ) ≤ B)
    (hsep :
      Real.exp (-(A * (n : ℝ))) ≤ finiteBrolinRootSeparation c z n) :
    (2 ^ n : ℝ)⁻¹ * (M : ℝ) *
      max 0
        (Real.log δ - Real.log (finiteBrolinRootSeparation c z n)) ≤
      (B * A) * ((n : ℝ) * (2 ^ n : ℝ)⁻¹) := by
  have hclip :=
    clippedLogRange_le_linear_of_exp_sep
      (c := c) (z := z) (δ := δ) (A := A) (n := n)
      hδpos hδle hApos hsep
  have hclip_nonneg :
      0 ≤
        max 0
          (Real.log δ - Real.log (finiteBrolinRootSeparation c z n)) :=
    le_max_left _ _
  have hMclip :
      (M : ℝ) *
          max 0
            (Real.log δ - Real.log (finiteBrolinRootSeparation c z n)) ≤
        B *
          max 0
            (Real.log δ - Real.log (finiteBrolinRootSeparation c z n)) :=
    mul_le_mul_of_nonneg_right hM hclip_nonneg
  have hBclip :
      B *
          max 0
            (Real.log δ - Real.log (finiteBrolinRootSeparation c z n)) ≤
        B * (A * (n : ℝ)) :=
    mul_le_mul_of_nonneg_left hclip hBnonneg
  have hinner :
      (M : ℝ) *
          max 0
            (Real.log δ - Real.log (finiteBrolinRootSeparation c z n)) ≤
        B * (A * (n : ℝ)) :=
    le_trans hMclip hBclip
  have hscaled :=
    mul_le_mul_of_nonneg_left hinner (by positivity : 0 ≤ (2 ^ n : ℝ)⁻¹)
  calc
    (2 ^ n : ℝ)⁻¹ * (M : ℝ) *
        max 0
          (Real.log δ - Real.log (finiteBrolinRootSeparation c z n))
        = (2 ^ n : ℝ)⁻¹ *
            ((M : ℝ) *
              max 0
                (Real.log δ -
                  Real.log (finiteBrolinRootSeparation c z n))) := by ring
    _ ≤ (2 ^ n : ℝ)⁻¹ * (B * (A * (n : ℝ))) := hscaled
    _ = (B * A) * ((n : ℝ) * (2 ^ n : ℝ)⁻¹) := by ring

/-- The `n qⁿ 2⁻ⁿ` factor tends to zero whenever the cylinder-cover growth
base is strictly smaller than the full degree `2`. -/
theorem tendsto_nat_mul_subtwo_ratio_pow {q : ℝ}
    (hqnonneg : 0 ≤ q) (hqlt : q < 2) :
    Tendsto (fun n : ℕ => (n : ℝ) * (q / 2) ^ n) atTop (𝓝 0) := by
  have hqratio_nonneg : 0 ≤ q / 2 := div_nonneg hqnonneg (by norm_num)
  have hqratio_lt : q / 2 < 1 := by nlinarith
  exact tendsto_self_mul_const_pow_of_lt_one
    (r := q / 2) hqratio_nonneg hqratio_lt

/-- Sub-full-degree cover-count version of the exponential-separation bound.
If the number of injective cylinder charts is `O(qⁿ)` with `q < 2`, the
weighted logarithmic cost still tends to zero. -/
theorem coverScaledClippedLogRange_le_geometric_of_exp_sep
    {c z : ℂ} {δ A C q : ℝ} {M n : ℕ}
    (hδpos : 0 < δ) (hδle : δ ≤ 1) (hApos : 0 < A)
    (hCnonneg : 0 ≤ C) (hqnonneg : 0 ≤ q)
    (hM : (M : ℝ) ≤ C * q ^ n)
    (hsep :
      Real.exp (-(A * (n : ℝ))) ≤ finiteBrolinRootSeparation c z n) :
    (2 ^ n : ℝ)⁻¹ * (M : ℝ) *
      max 0
        (Real.log δ - Real.log (finiteBrolinRootSeparation c z n)) ≤
      (C * A) * ((n : ℝ) * (q / 2) ^ n) := by
  have hclip :=
    clippedLogRange_le_linear_of_exp_sep
      (c := c) (z := z) (δ := δ) (A := A) (n := n)
      hδpos hδle hApos hsep
  have hclip_nonneg :
      0 ≤
        max 0
          (Real.log δ - Real.log (finiteBrolinRootSeparation c z n)) :=
    le_max_left _ _
  have hcover_nonneg : 0 ≤ C * q ^ n :=
    mul_nonneg hCnonneg (pow_nonneg hqnonneg n)
  have hMclip :
      (M : ℝ) *
          max 0
            (Real.log δ - Real.log (finiteBrolinRootSeparation c z n)) ≤
        (C * q ^ n) *
          max 0
            (Real.log δ - Real.log (finiteBrolinRootSeparation c z n)) :=
    mul_le_mul_of_nonneg_right hM hclip_nonneg
  have hcover_clip :
      (C * q ^ n) *
          max 0
            (Real.log δ - Real.log (finiteBrolinRootSeparation c z n)) ≤
        (C * q ^ n) * (A * (n : ℝ)) :=
    mul_le_mul_of_nonneg_left hclip hcover_nonneg
  have hinner :
      (M : ℝ) *
          max 0
            (Real.log δ - Real.log (finiteBrolinRootSeparation c z n)) ≤
        (C * q ^ n) * (A * (n : ℝ)) :=
    le_trans hMclip hcover_clip
  have hscaled :=
    mul_le_mul_of_nonneg_left hinner (by positivity : 0 ≤ (2 ^ n : ℝ)⁻¹)
  have hratio : q ^ n * (2 ^ n : ℝ)⁻¹ = (q / 2) ^ n := by
    rw [div_eq_mul_inv, mul_pow, inv_pow]
  calc
    (2 ^ n : ℝ)⁻¹ * (M : ℝ) *
        max 0
          (Real.log δ - Real.log (finiteBrolinRootSeparation c z n))
        = (2 ^ n : ℝ)⁻¹ *
            ((M : ℝ) *
              max 0
                (Real.log δ -
                  Real.log (finiteBrolinRootSeparation c z n))) := by ring
    _ ≤ (2 ^ n : ℝ)⁻¹ * ((C * q ^ n) * (A * (n : ℝ))) := hscaled
    _ = (C * A) * ((n : ℝ) * (q / 2) ^ n) := by
          rw [← hratio]
          ring

/-- Along the selected Brolin subsequence, an eventual exponential separation
bound forces the clipped logarithmic cost to vanish. -/
theorem clippedLogRange_subseq_tendsto_zero_of_eventually_exp_sep
    {c z : ℂ} {δ A : ℝ}
    (hδpos : 0 < δ) (hδle : δ ≤ 1) (hApos : 0 < A)
    (hsep :
      ∀ᶠ k in atTop,
        Real.exp (-(A * (brolinLimitSubsequence c k : ℝ))) ≤
          finiteBrolinRootSeparation c z
            (brolinLimitSubsequence c k)) :
    Tendsto
      (fun k : ℕ =>
        (2 ^ (brolinLimitSubsequence c k) : ℝ)⁻¹ *
          max 0
            (Real.log δ -
              Real.log
                (finiteBrolinRootSeparation c z
                  (brolinLimitSubsequence c k))))
      atTop (𝓝 0) := by
  have hbase :
      Tendsto
        (fun n : ℕ => A * ((n : ℝ) * (2 ^ n : ℝ)⁻¹))
        atTop (𝓝 0) :=
    by simpa using tendsto_nat_mul_inv_two_pow.const_mul A
  have hbound_tendsto :
      Tendsto
        (fun k : ℕ =>
          A * ((brolinLimitSubsequence c k : ℝ) *
            (2 ^ (brolinLimitSubsequence c k) : ℝ)⁻¹))
        atTop (𝓝 0) :=
    hbase.comp (brolinLimitSubsequence_tendsto_atTop c)
  refine squeeze_zero' ?hnonneg ?hupper hbound_tendsto
  · exact Eventually.of_forall fun k =>
      mul_nonneg (by positivity) (le_max_left _ _)
  · filter_upwards [hsep] with k hk
    exact
      scaledClippedLogRange_le_linear_of_exp_sep
        (c := c) (z := z) (δ := δ) (A := A)
        (n := brolinLimitSubsequence c k)
        hδpos hδle hApos hk

/-- hDisc-facing exponential-separation closure for GAP-A.  The remaining
geometric input is now explicit: a fixed local injectivity cylinder and an
eventual exponential lower bound for the finite zero-pullback separation. -/
theorem gapAMu_hasGreenPotentialRepresentation_of_injectiveBall_exponentialSeparation_control
    {c : ℂ} (hc : Disconnected c)
    (hgeom :
      ∀ z : ℂ, z ∈ filledJulia c →
        Integrable (fun w => logKernel z w) (gapAMu c) →
          ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧
            ∃ A : ℝ, 0 < A ∧
              ∀ᶠ k in atTop,
                Set.InjOn
                  ((quadratic c)^[brolinLimitSubsequence c k])
                  {w : ℂ | ‖z - w‖ < δ} ∧
                Real.exp
                  (-(A * (brolinLimitSubsequence c k : ℝ))) ≤
                  finiteBrolinRootSeparation c z
                    (brolinLimitSubsequence c k)) :
    HasGreenPotentialRepresentation c (gapAMu c) := by
  apply gapAMu_hasGreenPotentialRepresentation_of_injectiveBallClippedLogRange_control
    (c := c) hc
  intro z hzK hint ε hε
  rcases hgeom z hzK hint with
    ⟨δ, hδpos, hδle, A, hApos, hgeom_event⟩
  refine ⟨δ, hδpos, hδle, ?_⟩
  have hsep_event :
      ∀ᶠ k in atTop,
        Real.exp (-(A * (brolinLimitSubsequence c k : ℝ))) ≤
          finiteBrolinRootSeparation c z
            (brolinLimitSubsequence c k) := by
    filter_upwards [hgeom_event] with k hk
    exact hk.2
  have hlim :=
    clippedLogRange_subseq_tendsto_zero_of_eventually_exp_sep
      (c := c) (z := z) (δ := δ) (A := A)
      hδpos hδle hApos hsep_event
  have heps_nhds :
      {x : ℝ | x < ε} ∈ 𝓝 (0 : ℝ) :=
    Iio_mem_nhds hε
  have hsmall :=
    hlim.eventually heps_nhds
  filter_upwards [hgeom_event, hsmall] with k hk hlt
  exact ⟨hk.1, le_of_lt hlt⟩

/-- hDisc-facing finite-cylinder-cover closure for GAP-A.  Instead of forcing a
round ball to be one injectivity domain for `f_c^[n]`, it is enough to cover
the close zero-pullback atoms by uniformly boundedly many injective cylinder
charts, with an eventual exponential lower bound on the finite separation
from the boundary point. -/
theorem gapAMu_hasGreenPotentialRepresentation_of_cylinderCover_exponentialSeparation_control
    {c : ℂ} {ι : Type*} (hc : Disconnected c)
    (hgeom :
      ∀ z : ℂ, z ∈ filledJulia c →
        Integrable (fun w => logKernel z w) (gapAMu c) →
          ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧
            ∃ A : ℝ, 0 < A ∧
              ∃ B : ℝ, 0 ≤ B ∧
                ∀ᶠ k in atTop,
                  ∃ I : Finset ι, ∃ S : ι → Set ℂ,
                    (I.card : ℝ) ≤ B ∧
                    (∀ i, i ∈ I →
                      Set.InjOn
                        ((quadratic c)^[brolinLimitSubsequence c k])
                        (S i)) ∧
                    (∀ r ∈ (quadraticPolyIterate c
                        (brolinLimitSubsequence c k)).roots,
                      ‖z - r‖ < δ →
                        ∃ i, i ∈ I ∧ r ∈ S i) ∧
                    Real.exp
                      (-(A * (brolinLimitSubsequence c k : ℝ))) ≤
                      finiteBrolinRootSeparation c z
                        (brolinLimitSubsequence c k)) :
    HasGreenPotentialRepresentation c (gapAMu c) := by
  apply gapAMu_hasGreenPotentialRepresentation_of_finiteBrolinSingularTail_control
    (c := c) hc
  intro z hzK hint ε hε
  rcases hgeom z hzK hint with
    ⟨δ, hδpos, hδle, A, hApos, B, hBnonneg, hgeom_event⟩
  refine ⟨δ, hδpos, hδle, ?_⟩
  have hbase :
      Tendsto
        (fun n : ℕ => (B * A) * ((n : ℝ) * (2 ^ n : ℝ)⁻¹))
        atTop (𝓝 0) := by
    simpa using tendsto_nat_mul_inv_two_pow.const_mul (B * A)
  have hbound_tendsto :
      Tendsto
        (fun k : ℕ =>
          (B * A) * ((brolinLimitSubsequence c k : ℝ) *
            (2 ^ (brolinLimitSubsequence c k) : ℝ)⁻¹))
        atTop (𝓝 0) :=
    hbase.comp (brolinLimitSubsequence_tendsto_atTop c)
  have heps_nhds :
      {x : ℝ | x < ε} ∈ 𝓝 (0 : ℝ) :=
    Iio_mem_nhds hε
  have hsmall :=
    hbound_tendsto.eventually heps_nhds
  filter_upwards [hgeom_event, hsmall] with k hk hlt
  rcases hk with ⟨I, S, hIcard, hinj, hcover, hsep⟩
  have htail :=
    finiteBrolinSingularTail_le_cylinderCoverCanonicalClippedLogRangeCost
      (c := c) (z := z) (δ := δ)
      (n := brolinLimitSubsequence c k)
      (I := I) (S := S) hc hzK hinj hcover
  have hcost :=
    coverScaledClippedLogRange_le_linear_of_exp_sep
      (c := c) (z := z) (δ := δ) (A := A) (B := B)
      (M := I.card) (n := brolinLimitSubsequence c k)
      hδpos hδle hApos hBnonneg hIcard hsep
  exact le_trans htail (le_trans hcost (le_of_lt hlt))

/-- hDisc-facing sub-full-degree cylinder-cover closure for GAP-A.  The
close zero-pullback atoms may be covered by `O(qⁿ)` injective cylinder charts
for any fixed `q < 2`; the missing logarithmic separation may decay
exponentially, because the residual cost is `n (q/2)ⁿ`. -/
theorem gapAMu_hasGreenPotentialRepresentation_of_cylinderCover_subtwoExponentialSeparation_control
    {c : ℂ} {ι : Type*} (hc : Disconnected c)
    (hgeom :
      ∀ z : ℂ, z ∈ filledJulia c →
        Integrable (fun w => logKernel z w) (gapAMu c) →
          ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧
            ∃ A : ℝ, 0 < A ∧
              ∃ C : ℝ, 0 ≤ C ∧
                ∃ q : ℝ, 0 ≤ q ∧ q < 2 ∧
                  ∀ᶠ k in atTop,
                    ∃ I : Finset ι, ∃ S : ι → Set ℂ,
                      (I.card : ℝ) ≤
                        C * q ^ (brolinLimitSubsequence c k) ∧
                      (∀ i, i ∈ I →
                        Set.InjOn
                          ((quadratic c)^[brolinLimitSubsequence c k])
                          (S i)) ∧
                      (∀ r ∈ (quadraticPolyIterate c
                          (brolinLimitSubsequence c k)).roots,
                        ‖z - r‖ < δ →
                          ∃ i, i ∈ I ∧ r ∈ S i) ∧
                      Real.exp
                        (-(A * (brolinLimitSubsequence c k : ℝ))) ≤
                        finiteBrolinRootSeparation c z
                          (brolinLimitSubsequence c k)) :
    HasGreenPotentialRepresentation c (gapAMu c) := by
  apply gapAMu_hasGreenPotentialRepresentation_of_finiteBrolinSingularTail_control
    (c := c) hc
  intro z hzK hint ε hε
  rcases hgeom z hzK hint with
    ⟨δ, hδpos, hδle, A, hApos, C, hCnonneg, q,
      hqnonneg, hqlt, hgeom_event⟩
  refine ⟨δ, hδpos, hδle, ?_⟩
  have hbase :
      Tendsto
        (fun n : ℕ => (C * A) * ((n : ℝ) * (q / 2) ^ n))
        atTop (𝓝 0) := by
    simpa using
      (tendsto_nat_mul_subtwo_ratio_pow hqnonneg hqlt).const_mul (C * A)
  have hbound_tendsto :
      Tendsto
        (fun k : ℕ =>
          (C * A) *
            ((brolinLimitSubsequence c k : ℝ) *
              (q / 2) ^ (brolinLimitSubsequence c k)))
        atTop (𝓝 0) :=
    hbase.comp (brolinLimitSubsequence_tendsto_atTop c)
  have heps_nhds :
      {x : ℝ | x < ε} ∈ 𝓝 (0 : ℝ) :=
    Iio_mem_nhds hε
  have hsmall :=
    hbound_tendsto.eventually heps_nhds
  filter_upwards [hgeom_event, hsmall] with k hk hlt
  rcases hk with ⟨I, S, hIcard, hinj, hcover, hsep⟩
  have htail :=
    finiteBrolinSingularTail_le_cylinderCoverCanonicalClippedLogRangeCost
      (c := c) (z := z) (δ := δ)
      (n := brolinLimitSubsequence c k)
      (I := I) (S := S) hc hzK hinj hcover
  have hcost :=
    coverScaledClippedLogRange_le_geometric_of_exp_sep
      (c := c) (z := z) (δ := δ) (A := A) (C := C) (q := q)
      (M := I.card) (n := brolinLimitSubsequence c k)
      hδpos hδle hApos hCnonneg hqnonneg hIcard hsep
  exact le_trans htail (le_trans hcost (le_of_lt hlt))

end Bottcher
