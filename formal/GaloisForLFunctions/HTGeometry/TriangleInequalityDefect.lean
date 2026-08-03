import Mathlib

/-!
# The defect in the triangle inequality is the total misalignment

For a summable family of complex numbers, the amount by which the sum of the moduli exceeds the
modulus of the sum is exactly the total loss from projecting each term onto the direction of the
sum:

`∑ ‖c i‖ − ‖∑ c i‖ = ∑ (‖c i‖ − Re(ū · c i))`,

where `u` is the unit in the direction of the sum.  Every summand on the right is nonnegative, so a
small defect forces almost every term to be almost aligned with the sum.

This is the mechanism that a bound by absolute values throws away.  In Wiman–Valiron theory the
normalised coefficients all lie in the closed unit disc and their sum is as large as it can be at a
maximum-modulus point; the identity below converts that maximality into alignment of the phases,
which is what makes the weighted sums cancel.
-/

namespace GaloisForLFunctions.HTGeometry

/-- Projecting onto a unit direction never increases the modulus. -/
theorem re_conj_mul_le_norm (c : ℂ) {u : ℂ} (hu : ‖u‖ = 1) :
    ((starRingEnd ℂ) u * c).re ≤ ‖c‖ := by
  have h := Complex.re_le_norm ((starRingEnd ℂ) u * c)
  rwa [norm_mul, RCLike.norm_conj, hu, one_mul] at h

/-- The per-term misalignment is nonnegative. -/
theorem alignment_defect_nonneg (c : ℂ) {u : ℂ} (hu : ‖u‖ = 1) :
    0 ≤ ‖c‖ - ((starRingEnd ℂ) u * c).re :=
  sub_nonneg.mpr (re_conj_mul_le_norm c hu)

/-- **The triangle-inequality defect is the total misalignment.**  If the sum points in the unit
direction `u` with modulus `A`, then the excess of the sum of the moduli over `A` is exactly the sum
of the per-term misalignments. -/
theorem tsum_alignment_defect {ι : Type*} (c : ι → ℂ) (hc : Summable c)
    (hn : Summable fun i => ‖c i‖) {u : ℂ} (hu : ‖u‖ = 1) {A : ℝ}
    (hsum : ∑' i, c i = (A : ℂ) * u) :
    ∑' i, (‖c i‖ - ((starRingEnd ℂ) u * c i).re) = (∑' i, ‖c i‖) - A := by
  have hmul : Summable fun i => (starRingEnd ℂ) u * c i := hc.mul_left _
  have hre : Summable fun i => ((starRingEnd ℂ) u * c i).re :=
    (Complex.reCLM.summable hmul)
  have hproj : ∑' i, ((starRingEnd ℂ) u * c i).re = A := by
    have hmap : ∑' i, ((starRingEnd ℂ) u * c i).re
        = (∑' i, (starRingEnd ℂ) u * c i).re := (Complex.reCLM.map_tsum hmul).symm
    rw [hmap, tsum_mul_left, hsum]
    have hconj : (starRingEnd ℂ) u * ((A : ℂ) * u) = (A : ℂ) * ((starRingEnd ℂ) u * u) := by
      ring
    rw [hconj]
    have huu : (starRingEnd ℂ) u * u = ((‖u‖ ^ 2 : ℝ) : ℂ) := by
      rw [mul_comm]
      simpa using Complex.mul_conj' u
    rw [huu, hu]
    simp
  rw [Summable.tsum_sub hn hre, hproj]

/-- **Small defect forces alignment.**  Each individual misalignment is at most the total defect. -/
theorem alignment_defect_le {ι : Type*} (c : ι → ℂ) (hc : Summable c)
    (hn : Summable fun i => ‖c i‖) {u : ℂ} (hu : ‖u‖ = 1) {A : ℝ}
    (hsum : ∑' i, c i = (A : ℂ) * u) (i : ι) :
    ‖c i‖ - ((starRingEnd ℂ) u * c i).re ≤ (∑' j, ‖c j‖) - A := by
  have hd : Summable fun j => ‖c j‖ - ((starRingEnd ℂ) u * c j).re := by
    have hmul : Summable fun j => (starRingEnd ℂ) u * c j := hc.mul_left _
    exact hn.sub (Complex.reCLM.summable hmul)
  have h := hd.le_tsum i fun j _ => alignment_defect_nonneg (c j) hu
  rwa [tsum_alignment_defect c hc hn hu hsum] at h

/-! ## The transverse component

The per-term misalignment controls the component transverse to the direction of the sum
quadratically: a term that is nearly aligned is nearly a nonnegative multiple of `u`. -/

/-- The square of the norm splits into real and imaginary parts. -/
private theorem sq_norm_eq (w : ℂ) : ‖w‖ ^ 2 = w.re ^ 2 + w.im ^ 2 := by
  rw [Complex.norm_def, Real.sq_sqrt (Complex.normSq_nonneg w), Complex.normSq_apply]
  ring

/-- **The transverse component is quadratically small.**  The imaginary part of `ū c` is at most the
geometric mean of `2‖c‖` and the misalignment. -/
theorem sq_im_conj_mul_le (c : ℂ) {u : ℂ} (hu : ‖u‖ = 1) :
    ((starRingEnd ℂ) u * c).im ^ 2
      ≤ 2 * ‖c‖ * (‖c‖ - ((starRingEnd ℂ) u * c).re) := by
  set w : ℂ := (starRingEnd ℂ) u * c with hw
  have hnw : ‖w‖ = ‖c‖ := by
    rw [hw, norm_mul, RCLike.norm_conj, hu, one_mul]
  have hsq := sq_norm_eq w
  have hre : w.re ≤ ‖w‖ := Complex.re_le_norm w
  have hre' : -‖w‖ ≤ w.re := by
    have := Complex.abs_re_le_norm w
    have habs := abs_le.mp this
    exact habs.1
  nlinarith [hsq, hre, hre', hnw]

/-- The distance from `c` to its projection onto `u` is the transverse component. -/
theorem norm_sub_re_mul_eq (c : ℂ) {u : ℂ} (hu : ‖u‖ = 1) :
    ‖c - ((((starRingEnd ℂ) u * c).re : ℝ) : ℂ) * u‖
      = |((starRingEnd ℂ) u * c).im| := by
  have hune : u ≠ 0 := by
    intro h
    rw [h, norm_zero] at hu
    exact zero_ne_one hu
  have huu : u * (starRingEnd ℂ) u = 1 := by
    have h := Complex.mul_conj' u
    rw [h, hu]
    simp
  have hc : c = u * ((starRingEnd ℂ) u * c) := by
    rw [← mul_assoc, huu, one_mul]
  set w : ℂ := (starRingEnd ℂ) u * c with hw
  have hkey : w - ((w.re : ℝ) : ℂ) = ((w.im : ℝ) : ℂ) * Complex.I := by
    linear_combination -Complex.re_add_im w
  have hsplit : c - ((w.re : ℝ) : ℂ) * u = u * (((w.im : ℝ) : ℂ) * Complex.I) := by
    nth_rewrite 1 [hc]
    rw [← hkey]
    ring
  rw [hsplit, norm_mul, hu, one_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
    Real.norm_eq_abs]

/-- **Alignment in geometric form.**  The distance from a term to a nonnegative multiple of the
direction of the sum is controlled by the square root of its misalignment. -/
theorem norm_sub_re_mul_sq_le (c : ℂ) {u : ℂ} (hu : ‖u‖ = 1) :
    ‖c - ((((starRingEnd ℂ) u * c).re : ℝ) : ℂ) * u‖ ^ 2
      ≤ 2 * ‖c‖ * (‖c‖ - ((starRingEnd ℂ) u * c).re) := by
  rw [norm_sub_re_mul_eq c hu, sq_abs]
  exact sq_im_conj_mul_le c hu


/-! ## Weighted aggregation

The weighted sum of a nearly aligned family is, up to a real multiple of the common direction,
controlled by the square root of the total misalignment -- with the weights entering only through
their `l^2` norm.  This is the step where the square root from the previous section is converted
into a gain over the trivial bound. -/

/-- **Weighted Cauchy--Schwarz against square roots.** -/
theorem sum_weighted_sqrt_sq_le {ι : Type*} (s : Finset ι) (w d : ι → ℝ)
    (hd : ∀ i ∈ s, 0 ≤ d i) :
    (∑ i ∈ s, w i * Real.sqrt (d i)) ^ 2 ≤ (∑ i ∈ s, w i ^ 2) * ∑ i ∈ s, d i := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq s w (fun i => Real.sqrt (d i))
  refine le_trans h (le_of_eq ?_)
  congr 1
  exact Finset.sum_congr rfl fun i hi => Real.sq_sqrt (hd i hi)

/-- **The weighted sum is close to a real multiple of the direction.**  Only the transverse parts of
the terms survive, each of them bounded by the previous section. -/
theorem norm_weighted_sum_sub_le {ι : Type*} (s : Finset ι) (c : ι → ℂ) (w : ι → ℝ) (u : ℂ) :
    ‖(∑ i ∈ s, (w i : ℂ) * c i)
        - ((∑ i ∈ s, w i * ((starRingEnd ℂ) u * c i).re : ℝ) : ℂ) * u‖
      ≤ ∑ i ∈ s, |w i| * ‖c i - ((((starRingEnd ℂ) u * c i).re : ℝ) : ℂ) * u‖ := by
  have hsplit : ∑ i ∈ s, (w i : ℂ) * (c i - ((((starRingEnd ℂ) u * c i).re : ℝ) : ℂ) * u)
      = (∑ i ∈ s, (w i : ℂ) * c i)
        - ((∑ i ∈ s, w i * ((starRingEnd ℂ) u * c i).re : ℝ) : ℂ) * u := by
    push_cast
    rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [← hsplit]
  refine le_trans (norm_sum_le _ _) (le_of_eq ?_)
  exact Finset.sum_congr rfl fun i _ => by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]


/-- A complex number with vanishing imaginary part has norm the absolute value of its real part. -/
theorem norm_eq_abs_re_of_im_eq_zero {X : ℂ} (h : X.im = 0) : ‖X‖ = |X.re| := by
  rw [Complex.norm_def, Complex.normSq_apply, h]
  simp [← sq, Real.sqrt_sq_eq_abs]

/-- Dividing by a positive multiple of a unit is conjugating and scaling. -/
theorem div_ofReal_mul_unit (V : ℂ) {u : ℂ} (hu : ‖u‖ = 1) {M : ℝ} (hM : 0 < M) :
    V / ((M : ℂ) * u) = ((starRingEnd ℂ) u * V) / (M : ℂ) := by
  have hune : u ≠ 0 := by
    intro h
    rw [h, norm_zero] at hu
    exact zero_ne_one hu
  have hMne : ((M : ℝ) : ℂ) ≠ 0 := by
    simpa using ne_of_gt hM
  have huu : (starRingEnd ℂ) u * u = 1 := by
    have h := Complex.mul_conj' u
    rw [mul_comm] at h
    rw [h, hu]
    simp
  rw [div_eq_div_iff (mul_ne_zero hMne hune) hMne]
  calc V * (M : ℂ) = V * (M : ℂ) * ((starRingEnd ℂ) u * u) := by rw [huu, mul_one]
    _ = (starRingEnd ℂ) u * V * ((M : ℂ) * u) := by ring


end GaloisForLFunctions.HTGeometry
