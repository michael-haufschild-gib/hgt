import GaloisForLFunctions.HTGeometry.ExponentialLatticeWeight
import GaloisForLFunctions.HTGeometry.HyperbolicDiagonalSummability

/-!
# BTZ image sums and periodic long-string completion

For conformal weight one, the opposite-boundary kernel is
`(cosh t + cosh x)⁻²`. A separated exponential majorant proves convergence of
both spatial and temporal image sums. Spatial images decay in time; adding
temporal images gives a positive periodic correlator with exact returns.

This is the mathematical image-sum mechanism in equations (2.6) and (3.1) of
Maldacena, *Eternal black holes in Anti-de-Sitter*, arXiv:hep-th/0106112.
All lattice spacings are exponentials, so positivity is constructed.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry.Thermofield

open Filter
open scoped Topology

/-- The scalar opposite-boundary kernel at conformal weight one. -/
def btzKernel (t x : ℝ) : ℝ := ((Real.cosh t + Real.cosh x) ^ 2)⁻¹

theorem btzKernel_pos (t x : ℝ) : 0 < btzKernel t x := by
  exact inv_pos.mpr (sq_pos_of_pos (add_pos (Real.cosh_pos t) (Real.cosh_pos x)))

theorem btzKernel_swap (t x : ℝ) : btzKernel t x = btzKernel x t := by
  simp only [btzKernel, add_comm]

theorem btzKernel_neg_time (t x : ℝ) : btzKernel (-t) x = btzKernel t x := by
  simp only [btzKernel, Real.cosh_neg]

private theorem exp_abs_le_two_cosh (t : ℝ) : Real.exp |t| ≤ 2 * Real.cosh t := by
  have hc : Real.cosh |t| = Real.cosh t := by
    by_cases ht : 0 ≤ t
    · rw [abs_of_nonneg ht]
    · rw [abs_of_neg (lt_of_not_ge ht), Real.cosh_neg]
  rw [← hc, Real.cosh_eq]
  linarith only [Real.exp_pos (-|t|)]

/-- A product majorant controls both infinite image directions at once. -/
theorem btzKernel_le_exp (t x : ℝ) :
    btzKernel t x ≤ Real.exp (-|t|) * Real.exp (-|x|) := by
  have ht := exp_abs_le_two_cosh t
  have hx := exp_abs_le_two_cosh x
  have hprod : Real.exp |t| * Real.exp |x| ≤ (Real.cosh t + Real.cosh x) ^ 2 := by
    calc
      _ ≤ (2 * Real.cosh t) * (2 * Real.cosh x) :=
        mul_le_mul ht hx (Real.exp_pos _).le (by positivity)
      _ ≤ _ := by nlinarith only [sq_nonneg (Real.cosh t - Real.cosh x)]
  calc
    btzKernel t x ≤ (Real.exp |t| * Real.exp |x|)⁻¹ :=
      inv_anti₀ (mul_pos (Real.exp_pos _) (Real.exp_pos _)) hprod
    _ = Real.exp (-|t|) * Real.exp (-|x|) := by
      rw [mul_inv_rev, Real.exp_neg, Real.exp_neg]
      ring

/-- Exponential tails remain summable after an arbitrary real lattice shift. -/
theorem summable_shifted_exp (a x : ℝ) :
    Summable (fun n : ℤ => Real.exp (-|x + Real.exp a * (n : ℝ)|)) := by
  have hs := (summable_exp_neg_abs_int (Real.exp_pos a)).mul_left (Real.exp |x|)
  apply hs.of_nonneg_of_le (fun _ => (Real.exp_pos _).le)
  intro n
  rw [← Real.exp_add, Real.exp_le_exp]
  have h := abs_sub_le (x + Real.exp a * (n : ℝ)) x
  rw [show x + Real.exp a * (n : ℝ) - x = Real.exp a * (n : ℝ) by ring,
    abs_mul, abs_of_pos (Real.exp_pos a)] at h
  linarith only [h]

/-- Spatial image sum of the BTZ kernel. -/
def btzSpatialImages (a t x : ℝ) : ℝ :=
  ∑' n : ℤ, btzKernel t (x + Real.exp a * (n : ℝ))

theorem summable_btzSpatialImages (a t x : ℝ) :
    Summable (fun n : ℤ => btzKernel t (x + Real.exp a * (n : ℝ))) :=
  ((summable_shifted_exp a x).mul_left (Real.exp (-|t|))).of_nonneg_of_le
    (fun _ => (btzKernel_pos _ _).le) (fun _ => btzKernel_le_exp _ _)

theorem btzSpatialImages_pos (a t x : ℝ) : 0 < btzSpatialImages a t x := by
  apply (btzKernel_pos t (x + Real.exp a * (0 : ℤ))).trans_le
  exact (summable_btzSpatialImages a t x).le_tsum 0 (fun _ _ => (btzKernel_pos _ _).le)

/-- The complete spatial image sum has a uniform exponential time envelope. -/
theorem btzSpatialImages_le (a t x : ℝ) :
    btzSpatialImages a t x ≤ Real.exp (-|t|) *
      ∑' n : ℤ, Real.exp (-|x + Real.exp a * (n : ℝ)|) := by
  rw [btzSpatialImages, ← tsum_mul_left]
  exact (summable_btzSpatialImages a t x).tsum_le_tsum
    (fun _ => btzKernel_le_exp _ _)
    ((summable_shifted_exp a x).mul_left _)

/-- The spatially quotiented correlator decays to zero at late times. -/
theorem btzSpatialImages_tendsto_zero (a x : ℝ) :
    Tendsto (fun t => btzSpatialImages a t x) atTop (𝓝 0) := by
  have he : Tendsto (fun t : ℝ => Real.exp (-|t|)) atTop (𝓝 0) := by
    apply (Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot).congr'
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    rw [abs_of_nonneg ht]
  have hb := he.mul_const (∑' n : ℤ, Real.exp (-|x + Real.exp a * (n : ℝ)|))
  rw [zero_mul] at hb
  exact squeeze_zero (fun t => (btzSpatialImages_pos a t x).le)
    (fun t => btzSpatialImages_le a t x) hb

/-- Adding a full spatial period just permutes the image labels. -/
theorem btzSpatialImages_periodic (a t : ℝ) :
    Function.Periodic (btzSpatialImages a t) (Real.exp a) := by
  intro x
  unfold btzSpatialImages
  have h := (Equiv.addRight (1 : ℤ)).tsum_eq
    (fun n : ℤ => btzKernel t (x + Real.exp a * (n : ℝ)))
  convert h using 1
  apply tsum_congr
  intro n
  congr 2
  simp only [Equiv.coe_addRight, Int.cast_add, Int.cast_one]
  ring

/-- Temporal images restore the periodicity of the long-string spectrum. -/
def longStringImages (b a t x : ℝ) : ℝ :=
  ∑' m : ℤ, btzSpatialImages a (t + Real.exp b * (m : ℝ)) x

theorem summable_longStringImages (b a t x : ℝ) :
    Summable (fun m : ℤ => btzSpatialImages a (t + Real.exp b * (m : ℝ)) x) :=
  ((summable_shifted_exp b t).mul_right
      (∑' n : ℤ, Real.exp (-|x + Real.exp a * (n : ℝ)|))).of_nonneg_of_le
    (fun _ => (btzSpatialImages_pos _ _ _).le) (fun _ => btzSpatialImages_le _ _ _)

/-- Both image directions converge absolutely, so their order can be exchanged. -/
theorem summable_btzDoubleImages (b a t x : ℝ) :
    Summable (fun p : ℤ × ℤ =>
      btzKernel (t + Real.exp b * (p.1 : ℝ)) (x + Real.exp a * (p.2 : ℝ))) := by
  rw [summable_prod_of_nonneg (fun _ => (btzKernel_pos _ _).le)]
  exact ⟨fun _ => summable_btzSpatialImages _ _ _, summable_longStringImages _ _ _ _⟩

theorem longStringImages_pos (b a t x : ℝ) : 0 < longStringImages b a t x := by
  apply (btzSpatialImages_pos a (t + Real.exp b * (0 : ℤ)) x).trans_le
  exact (summable_longStringImages b a t x).le_tsum 0
    (fun _ _ => (btzSpatialImages_pos _ _ _).le)

/-- Exact time periodicity follows from reindexing the temporal images. -/
theorem longStringImages_periodic (b a x : ℝ) :
    Function.Periodic (fun t => longStringImages b a t x) (Real.exp b) := by
  intro t
  unfold longStringImages
  have h := (Equiv.addRight (1 : ℤ)).tsum_eq
    (fun m : ℤ => btzSpatialImages a (t + Real.exp b * (m : ℝ)) x)
  convert h using 1
  apply tsum_congr
  intro m
  congr 2
  simp only [Equiv.coe_addRight, Int.cast_add, Int.cast_one]
  ring

/-- Every nonnegative integer multiple of the period is an exact return. -/
theorem longStringImages_returns (b a x : ℝ) (n : ℕ) :
    longStringImages b a ((n : ℝ) * Real.exp b) x = longStringImages b a 0 x := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul,
      longStringImages_periodic b a x, ih]

/-- The convergent temporal completion cannot share the spatial correlator's
late-time decay: positive exact returns occur arbitrarily late. -/
theorem longStringImages_not_tendsto_zero (b a x : ℝ) :
    ¬ Tendsto (fun t => longStringImages b a t x) atTop (𝓝 0) := by
  intro h
  have ht : Tendsto (fun n : ℕ => (n : ℝ) * Real.exp b) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_mul_const (Real.exp_pos b)
  have hzero : Tendsto (fun _ : ℕ => longStringImages b a 0 x) atTop (𝓝 0) := by
    simpa only [Function.comp_def, longStringImages_returns] using h.comp ht
  have heq : longStringImages b a 0 x = 0 := tendsto_nhds_unique tendsto_const_nhds hzero
  exact (longStringImages_pos b a 0 x).ne' heq

/-- At zero time, BTZ lattice entries are squares of the corpus hyperbolic
resolvent weights. -/
theorem btzKernel_zero_lattice (a : ℝ) (n : ℕ) :
    btzKernel 0 (2 * (n * a)) = (1 / 4 : ℝ) * hyperbolicResolventWeight a n ^ 2 := by
  have h : 1 + Real.cosh (2 * (n * a)) = 2 * Real.cosh (n * a) ^ 2 := by
    rw [Real.cosh_two_mul, Real.cosh_sq]
    ring
  rw [btzKernel, Real.cosh_zero, h, hyperbolicResolventWeight]
  field_simp [(Real.cosh_pos (n * a)).ne'] <;> ring

end GaloisForLFunctions.HTGeometry.Thermofield

#print axioms GaloisForLFunctions.HTGeometry.Thermofield.btzKernel_pos
#print axioms GaloisForLFunctions.HTGeometry.Thermofield.btzKernel_swap
#print axioms GaloisForLFunctions.HTGeometry.Thermofield.btzKernel_neg_time
#print axioms GaloisForLFunctions.HTGeometry.Thermofield.btzKernel_le_exp
#print axioms GaloisForLFunctions.HTGeometry.Thermofield.summable_shifted_exp
#print axioms GaloisForLFunctions.HTGeometry.Thermofield.summable_btzSpatialImages
#print axioms GaloisForLFunctions.HTGeometry.Thermofield.btzSpatialImages_pos
#print axioms GaloisForLFunctions.HTGeometry.Thermofield.btzSpatialImages_le
#print axioms GaloisForLFunctions.HTGeometry.Thermofield.btzSpatialImages_tendsto_zero
#print axioms GaloisForLFunctions.HTGeometry.Thermofield.btzSpatialImages_periodic
#print axioms GaloisForLFunctions.HTGeometry.Thermofield.summable_longStringImages
#print axioms GaloisForLFunctions.HTGeometry.Thermofield.summable_btzDoubleImages
#print axioms GaloisForLFunctions.HTGeometry.Thermofield.longStringImages_pos
#print axioms GaloisForLFunctions.HTGeometry.Thermofield.longStringImages_periodic
#print axioms GaloisForLFunctions.HTGeometry.Thermofield.longStringImages_returns
#print axioms GaloisForLFunctions.HTGeometry.Thermofield.longStringImages_not_tendsto_zero
#print axioms GaloisForLFunctions.HTGeometry.Thermofield.btzKernel_zero_lattice
