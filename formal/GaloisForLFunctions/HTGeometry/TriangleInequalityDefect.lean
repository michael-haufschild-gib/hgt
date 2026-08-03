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

end GaloisForLFunctions.HTGeometry
