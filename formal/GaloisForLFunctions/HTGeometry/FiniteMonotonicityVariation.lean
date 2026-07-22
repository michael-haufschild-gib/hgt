import Mathlib.Analysis.BoundedVariation
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Finite-monotonicity total-variation law

A uniformly bounded real function with at most `n` monotonicity intervals has total variation at
most `2 n` times its uniform bound.  This is the abstract last step in the one-turning-point Sturm
argument for the fixed CCM prolate modes: the differential equation supplies a number of
monotonicity intervals independent of aperture, while uniform prolate-to-Hermite convergence
supplies the uniform bound.

The theorem is independent of prolate functions and unconditional.  It uses the extended-real
variation from mathlib, so its finiteness corollary connects directly to the BV lattice-envelope
modules.
-/

open Set
open scoped ENNReal

namespace HTGeometry

/-! ## One-sign Sturm cells -/

/-- Weighted derivative (Sturm flux) of `f` with leading coefficient `p`. -/
noncomputable def sturmFlux (p f : ℝ → ℝ) (x : ℝ) : ℝ := p x * deriv f x

/-- A positive right-hand side in `(p f')' = q f` makes the Sturm flux strictly increasing on
the cell. -/
theorem sturmFlux_strictMonoOn_of_rhs_pos
    {a b : ℝ} (p q f : ℝ → ℝ)
    (hcontinuous : ContinuousOn (sturmFlux p f) (Icc a b))
    (hode : ∀ x ∈ Ioo a b, deriv (sturmFlux p f) x = q x * f x)
    (hpos : ∀ x ∈ Ioo a b, 0 < q x * f x) :
    StrictMonoOn (sturmFlux p f) (Icc a b) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc a b) hcontinuous
  intro x hx
  rw [interior_Icc] at hx
  rw [hode x hx]
  exact hpos x hx

/-- A negative right-hand side in `(p f')' = q f` makes the Sturm flux strictly decreasing on
the cell. -/
theorem sturmFlux_strictAntiOn_of_rhs_neg
    {a b : ℝ} (p q f : ℝ → ℝ)
    (hcontinuous : ContinuousOn (sturmFlux p f) (Icc a b))
    (hode : ∀ x ∈ Ioo a b, deriv (sturmFlux p f) x = q x * f x)
    (hneg : ∀ x ∈ Ioo a b, q x * f x < 0) :
    StrictAntiOn (sturmFlux p f) (Icc a b) := by
  apply strictAntiOn_of_deriv_neg (convex_Icc a b) hcontinuous
  intro x hx
  rw [interior_Icc] at hx
  rw [hode x hx]
  exact hneg x hx

/-- Injectivity of the Sturm flux allows at most one stationary point of `f` in a cell. -/
theorem criticalSet_subsingleton_of_injOn_sturmFlux
    (p f : ℝ → ℝ) (s : Set ℝ)
    (hinj : Set.InjOn (sturmFlux p f) s) :
    {x | x ∈ s ∧ deriv f x = 0}.Subsingleton := by
  intro x hx y hy
  apply hinj hx.1 hy.1
  simp [sturmFlux, hx.2, hy.2]

/-- **One-sign Sturm critical-point law, positive branch.** On a cell where the right-hand side
`q f` is positive, a Sturm solution has at most one stationary point. -/
theorem criticalSet_subsingleton_of_sturm_rhs_pos
    {a b : ℝ} (p q f : ℝ → ℝ)
    (hcontinuous : ContinuousOn (sturmFlux p f) (Icc a b))
    (hode : ∀ x ∈ Ioo a b, deriv (sturmFlux p f) x = q x * f x)
    (hpos : ∀ x ∈ Ioo a b, 0 < q x * f x) :
    {x | x ∈ Icc a b ∧ deriv f x = 0}.Subsingleton := by
  exact criticalSet_subsingleton_of_injOn_sturmFlux p f (Icc a b)
    (sturmFlux_strictMonoOn_of_rhs_pos p q f hcontinuous hode hpos).injOn

/-- **One-sign Sturm critical-point law, negative branch.** On a cell where the right-hand side
`q f` is negative, a Sturm solution has at most one stationary point. -/
theorem criticalSet_subsingleton_of_sturm_rhs_neg
    {a b : ℝ} (p q f : ℝ → ℝ)
    (hcontinuous : ContinuousOn (sturmFlux p f) (Icc a b))
    (hode : ∀ x ∈ Ioo a b, deriv (sturmFlux p f) x = q x * f x)
    (hneg : ∀ x ∈ Ioo a b, q x * f x < 0) :
    {x | x ∈ Icc a b ∧ deriv f x = 0}.Subsingleton := by
  exact criticalSet_subsingleton_of_injOn_sturmFlux p f (Icc a b)
    (sturmFlux_strictAntiOn_of_rhs_neg p q f hcontinuous hode hneg).injOn

/-- Variation of an antitone real function on an interval is bounded by its endpoint drop. -/
theorem AntitoneOn.eVariationOn_le {α : Type*} [LinearOrder α]
    {f : α → ℝ} {s : Set α} (hf : AntitoneOn f s) {a b : α}
    (ha : a ∈ s) (hb : b ∈ s) :
    eVariationOn f (s ∩ Icc a b) ≤ ENNReal.ofReal (f a - f b) := by
  apply iSup_le
  rintro ⟨n, ⟨u, hu, hus⟩⟩
  calc
    (∑ i ∈ Finset.range n, edist (f (u (i + 1))) (f (u i))) =
        ∑ i ∈ Finset.range n, ENNReal.ofReal (f (u i) - f (u (i + 1))) := by
      refine Finset.sum_congr rfl fun i hi => ?_
      simp only [Finset.mem_range] at hi
      rw [edist_dist, Real.dist_eq, abs_of_nonpos]
      · rw [neg_sub]
      · exact sub_nonpos.mpr (hf (hus i).1 (hus (i + 1)).1 (hu (Nat.le_succ _)))
    _ = ENNReal.ofReal (∑ i ∈ Finset.range n, (f (u i) - f (u (i + 1)))) := by
      rw [ENNReal.ofReal_sum_of_nonneg]
      intro i _
      exact sub_nonneg.mpr (hf (hus i).1 (hus (i + 1)).1 (hu (Nat.le_succ _)))
    _ = ENNReal.ofReal (f (u 0) - f (u n)) := by
      rw [Finset.sum_range_sub' fun i => f (u i)]
    _ ≤ ENNReal.ofReal (f a - f b) := by
      apply ENNReal.ofReal_le_ofReal
      exact sub_le_sub (hf ha (hus 0).1 (hus 0).2.1)
        (hf (hus n).1 hb (hus n).2.2)

/-- **Finite-monotonicity variation law.** If `I 0 ≤ ... ≤ I n` partitions an interval and `f`
is monotone in either direction on every cell, then a uniform bound `|f| ≤ B` makes its total
variation at most `2 n B`. -/
theorem eVariationOn_le_of_piecewise_monotone
    (f : ℝ → ℝ) (I : ℕ → ℝ) (n : ℕ) (hI : Monotone I)
    (hmono : ∀ i < n,
      MonotoneOn f (Icc (I i) (I (i + 1))) ∨
        AntitoneOn f (Icc (I i) (I (i + 1))))
    (B : ℝ) (hbound : ∀ x ∈ Icc (I 0) (I n), |f x| ≤ B) :
    eVariationOn f (Icc (I 0) (I n)) ≤ ENNReal.ofReal (2 * n * B) := by
  rw [← eVariationOn.sum' f hI]
  calc
    (∑ i ∈ Finset.range n,
        eVariationOn f (Icc (I i) (I (i + 1)))) ≤
        ∑ i ∈ Finset.range n, ENNReal.ofReal (2 * B) := by
      apply Finset.sum_le_sum
      intro i hi
      have hin : i < n := Finset.mem_range.mp hi
      have hleft : I i ∈ Icc (I 0) (I n) :=
        ⟨hI (Nat.zero_le i), hI (Nat.le_of_lt hin)⟩
      have hright : I (i + 1) ∈ Icc (I 0) (I n) :=
        ⟨hI (Nat.zero_le (i + 1)), hI (Nat.succ_le_iff.mpr hin)⟩
      have hlo : -B ≤ f (I i) := (abs_le.mp (hbound _ hleft)).1
      have hhi : f (I i) ≤ B := (abs_le.mp (hbound _ hleft)).2
      have hlo' : -B ≤ f (I (i + 1)) := (abs_le.mp (hbound _ hright)).1
      have hhi' : f (I (i + 1)) ≤ B := (abs_le.mp (hbound _ hright)).2
      rcases hmono i hin with hinc | hdec
      · have hv := MonotoneOn.eVariationOn_le hinc
          (left_mem_Icc.2 (hI (Nat.le_succ i)))
          (right_mem_Icc.2 (hI (Nat.le_succ i)))
        rw [inter_self] at hv
        refine hv.trans ?_
        apply ENNReal.ofReal_le_ofReal
        linarith
      · have hv := HTGeometry.AntitoneOn.eVariationOn_le hdec
          (left_mem_Icc.2 (hI (Nat.le_succ i)))
          (right_mem_Icc.2 (hI (Nat.le_succ i)))
        rw [inter_self] at hv
        refine hv.trans ?_
        apply ENNReal.ofReal_le_ofReal
        linarith
    _ = ENNReal.ofReal (2 * n * B) := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      rw [← ENNReal.ofReal_natCast n, ← ENNReal.ofReal_mul (Nat.cast_nonneg n)]
      congr 1
      ring

/-- A finite monotonicity partition automatically makes the function BV on the full interval. -/
theorem boundedVariationOn_of_piecewise_monotone
    (f : ℝ → ℝ) (I : ℕ → ℝ) (n : ℕ) (hI : Monotone I)
    (hmono : ∀ i < n,
      MonotoneOn f (Icc (I i) (I (i + 1))) ∨
        AntitoneOn f (Icc (I i) (I (i + 1))))
    (B : ℝ) (hbound : ∀ x ∈ Icc (I 0) (I n), |f x| ≤ B) :
    BoundedVariationOn f (Icc (I 0) (I n)) := by
  apply ne_of_lt
  exact (eVariationOn_le_of_piecewise_monotone f I n hI hmono B hbound).trans_lt
    ENNReal.ofReal_lt_top

end HTGeometry
