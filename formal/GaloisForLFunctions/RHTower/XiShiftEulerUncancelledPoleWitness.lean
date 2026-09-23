import GaloisForLFunctions.RHTower.XiShiftEulerRegionIndex
import GaloisForLFunctions.HTGeometry.KernelNestedFiniteSectionInertia

/-!
# Euler-region witness from one uncancelled shifted-Xi pole

An individual denominator zero whose reflected numerator does not vanish already forces a negative
square of the cleared Hermite--Biehler kernel. Analytic locality transports that square to the
Euler half-plane, independently of cancellations at every other shifted pole.
-/

open Complex Set
open scoped ComplexConjugate
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

/-- The cleared kernel is strictly negative on the diagonal at every uncancelled shifted pole. -/
theorem re_xiShiftClearedUpperKernel_pole_diagonal_neg
    {omega : ℝ} (q : XiShiftRightZeroCopy omega)
    (huncancel : suzukiCanonicalE omega (-xiShiftPoleCoordinate omega q) ≠ 0) :
    (xiShiftClearedUpperKernel omega
      (xiShiftPoleCoordinate omega q) (xiShiftPoleCoordinate omega q)).re < 0 := by
  let p := xiShiftPoleCoordinate omega q
  have hp : 0 < p.im := xiShiftPoleCoordinate_im_pos omega q
  have hden : p - (starRingEnd ℂ) p = (2 * p.im : ℝ) * I := by
    apply Complex.ext
    · simp [mul_re]
    · simp [mul_im]
      ring
  rw [xiShiftClearedUpperKernel,
    suzukiCanonicalE_xiShiftPoleCoordinate_eq_zero]
  simp only [map_zero, mul_zero, zero_sub]
  have hscale : I / (p - (starRingEnd ℂ) p) = ((2 * p.im)⁻¹ : ℝ) := by
    rw [hden, div_eq_mul_inv, mul_inv_rev, Complex.inv_I]
    rw [← Complex.ofReal_inv]
    ring_nf
    rw [show I ^ (2 : ℕ) = (-1 : ℂ) by norm_num]
    ring
  rw [hscale]
  rw [show suzukiCanonicalE omega (-p) *
      (starRingEnd ℂ) (suzukiCanonicalE omega (-p)) =
      (‖suzukiCanonicalE omega (-p)‖ ^ (2 : ℕ) : ℝ) by
    rw [← Complex.normSq_eq_norm_sq, Complex.mul_conj]]
  norm_num
  have hnorm : 0 < ‖suzukiCanonicalE omega (-p)‖ ^ (2 : ℕ) :=
    sq_pos_of_pos (norm_pos_iff.mpr huncancel)
  have hpos : 0 < p.im⁻¹ * (1 / 2 : ℝ) *
      ‖suzukiCanonicalE omega (-p)‖ ^ (2 : ℕ) :=
    mul_pos (mul_pos (inv_pos.mpr hp) (by norm_num)) hnorm
  exact_mod_cast hpos

/-- One uncancelled pole supplies one literal negative dimension of the global cleared kernel. -/
theorem xiShiftClearedUpperKernel_has_negativeDimension_one_of_uncancelled
    {omega : ℝ} (q : XiShiftRightZeroCopy omega)
    (huncancel : suzukiCanonicalE omega (-xiShiftPoleCoordinate omega q) ≠ 0) :
    HasFiniteKernelNegativeDimension
      (fun z w : upperHalfPlaneSet =>
        xiShiftClearedUpperKernel omega z.1 w.1) 1 := by
  rw [← hasNegativeKernelPacket_iff_negativeDimension_one]
  let p : upperHalfPlaneSet :=
    ⟨xiShiftPoleCoordinate omega q, xiShiftPoleCoordinate_im_pos omega q⟩
  refine ⟨1, Finsupp.single p 1, ?_, ?_⟩
  · simp
  · simpa [kernelForm, p] using
      re_xiShiftClearedUpperKernel_pole_diagonal_neg q huncancel

/-- One uncancelled shifted-Xi pole remains a negative square after restriction to the ordinary
Euler-convergence sampling half-plane. -/
theorem eulerXiShiftPick_has_negativeDimension_one_of_uncancelled
    {omega : ℝ} (homega : 0 < omega) (q : XiShiftRightZeroCopy omega)
    (huncancel : suzukiCanonicalE omega (-xiShiftPoleCoordinate omega q) ≠ 0) :
    HasFiniteKernelNegativeDimension
      (fun z w : xiShiftEulerUpperSet omega =>
        eulerXiShiftPick omega z.1 w.1) 1 := by
  have hcleared : HasFiniteKernelNegativeDimension
      (fun z w : xiShiftEulerUpperSet omega =>
        xiShiftClearedUpperKernel omega z.1 w.1) 1 :=
    (xiShiftClearedUpperKernel_openRegion_negativeDimension_iff
      omega (xiShiftEulerUpperSet omega)
      (isOpen_xiShiftEulerUpperSet omega)
      (xiShiftEulerUpperSet_subset_upperHalfPlane homega)
      (xiShiftEulerUpperSet_nonempty omega) 1).mpr
        (xiShiftClearedUpperKernel_has_negativeDimension_one_of_uncancelled q huncancel)
  have hcong : HasFiniteKernelNegativeDimension
      (fun z w : xiShiftEulerUpperSet omega =>
        xiShiftClearedUpperKernel omega z.1 w.1) 1 ↔
      HasFiniteKernelNegativeDimension
      (fun z w : xiShiftEulerUpperSet omega =>
        eulerXiShiftPick omega z.1 w.1) 1 := by
    apply hasFiniteKernelNegativeDimension_diagonal_equiv_iff
      (fun z w : xiShiftEulerUpperSet omega =>
        xiShiftClearedUpperKernel omega z.1 w.1)
      (fun z w : xiShiftEulerUpperSet omega =>
        eulerXiShiftPick omega z.1 w.1)
      (Equiv.refl _) (fun z => suzukiCanonicalE omega z.1)
      (fun z => suzukiCanonicalE_ne_zero_of_mem_xiShiftEulerUpperSet homega z.1 z.2)
    intro z w
    let zr : XiShiftRegularUpperNode omega :=
      ⟨z.1, xiShiftEulerUpperSet_subset_upperHalfPlane homega z.2,
        suzukiCanonicalE_ne_zero_of_mem_xiShiftEulerUpperSet homega z.1 z.2⟩
    let wr : XiShiftRegularUpperNode omega :=
      ⟨w.1, xiShiftEulerUpperSet_subset_upperHalfPlane homega w.2,
        suzukiCanonicalE_ne_zero_of_mem_xiShiftEulerUpperSet homega w.1 w.2⟩
    simpa [zr, wr, xiShiftRegularUpperKernel,
      eulerXiShiftPick_eq_upperHalfPlaneSchurKernel] using
      xiShiftClearedUpperKernel_eq_regular_congruence omega zr wr
  exact hcong.mp hcleared

/-- The transported negative square is witnessed by one actual finite Euler-region Pick matrix. -/
theorem exists_eulerXiShiftPick_sample_negIndex_pos_of_uncancelled
    {omega : ℝ} (homega : 0 < omega) (q : XiShiftRightZeroCopy omega)
    (huncancel : suzukiCanonicalE omega (-xiShiftPoleCoordinate omega q) ≠ 0) :
    ∃ (N : ℕ) (w : Fin N → xiShiftEulerUpperSet omega),
      0 < hermNegIndex (Matrix.of fun i j =>
        eulerXiShiftPick omega (w j).1 (w i).1) := by
  obtain ⟨N, w, hle⟩ := exists_finite_sample_negIndex_ge
    (fun z w : xiShiftEulerUpperSet omega =>
      eulerXiShiftPick omega z.1 w.1)
    (eulerXiShiftPick_has_negativeDimension_one_of_uncancelled homega q huncancel)
  exact ⟨N, w, lt_of_lt_of_le Nat.zero_lt_one hle⟩

end

end RHTower
