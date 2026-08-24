import GaloisForLFunctions.RHTower.SuzukiShiftedXiKernelOpenRegionLocality
import GaloisForLFunctions.RHTower.XiShiftEulerPointwiseContractivity
import GaloisForLFunctions.RHTower.XiShiftEulerPrimeFactor
import GaloisForLFunctions.HTGeometry.KernelCorrelationOrder
import GaloisForLFunctions.HTGeometry.UpperHalfPlaneSchurKernelProduct

/-!
# Euler-region shifted-Xi negative index and correlation order

The literal shifted-Xi quotient is pointwise contractive on its Euler
sampling half-plane, yet analytic locality preserves its complete negative
index there.  This leaf identifies the quotient with Suzuki's canonical
ratio, specializes the open-region index classification, and formalizes the
first failing finite-correlation order.
-/

open Complex Set
open scoped ComplexConjugate
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

/-- Literal Euler sampling half-plane `Im z > 1/2 + omega`. -/
def xiShiftEulerUpperSet (omega : ℝ) : Set ℂ :=
  {z | 1 / 2 + omega < z.im}

/-- The rotated centered quotient is Suzuki's literal shifted-Xi quotient. -/
theorem eulerXiShiftTheta_eq_suzukiCanonicalTheta
    (omega : ℝ) (z : ℂ) :
    eulerXiShiftTheta omega z = suzukiCanonicalTheta omega z := by
  rw [eulerXiShiftTheta, xiShiftTheta, xiCent, xiCent,
    suzukiCanonicalTheta]
  congr 1 <;> ring_nf

/-- The card's Euler Pick kernel is exactly the canonical upper-half-plane
Schur kernel. -/
theorem eulerXiShiftPick_eq_upperHalfPlaneSchurKernel
    (omega : ℝ) (z w : ℂ) :
    eulerXiShiftPick omega z w =
      upperHalfPlaneSchurKernel (suzukiCanonicalTheta omega) z w := by
  rw [eulerXiShiftPick, upperHalfPlaneSchurKernel,
    eulerXiShiftTheta_eq_suzukiCanonicalTheta,
    eulerXiShiftTheta_eq_suzukiCanonicalTheta]

theorem isOpen_xiShiftEulerUpperSet (omega : ℝ) :
    IsOpen (xiShiftEulerUpperSet omega) := by
  exact isOpen_lt continuous_const Complex.continuous_im

theorem xiShiftEulerUpperSet_nonempty (omega : ℝ) :
    (xiShiftEulerUpperSet omega).Nonempty := by
  refine ⟨((1 / 2 + omega + 1 : ℝ) : ℂ) * I, ?_⟩
  simp [xiShiftEulerUpperSet]

theorem xiShiftEulerUpperSet_subset_upperHalfPlane
    {omega : ℝ} (homega : 0 < omega) :
    xiShiftEulerUpperSet omega ⊆ upperHalfPlaneSet := by
  intro z hz
  change 0 < z.im
  change 1 / 2 + omega < z.im at hz
  linarith

/-- The denominator of the shifted quotient is zero-free throughout the
Euler sampling half-plane. -/
theorem suzukiCanonicalE_ne_zero_of_mem_xiShiftEulerUpperSet
    {omega : ℝ} (homega : 0 < omega)
    (z : ℂ) (hz : z ∈ xiShiftEulerUpperSet omega) :
    suzukiCanonicalE omega z ≠ 0 := by
  rw [suzukiCanonicalE]
  apply xi_ne_zero_of_one_lt_re
  change (1 : ℝ) < (1 / 2 + (omega : ℂ) - z * I).re
  change 1 / 2 + omega < z.im at hz
  simp only [Complex.sub_re, Complex.add_re, Complex.div_re,
    Complex.one_re, Complex.one_im, Complex.ofReal_re,
    Complex.mul_re, Complex.I_re, Complex.I_im]
  norm_num
  linarith

/-- Exact finite-or-infinite shifted-divisor count on the literal Euler
sampling half-plane. -/
theorem eulerXiShiftPick_negativeIndex_classification
    {omega : ℝ} (homega : 0 < omega)
    (hnon : SuzukiShiftNonexceptional omega) :
    (Finite (XiShiftRightZeroCopy omega) ∧
      HasFiniteKernelNegativeDimension
        (fun z w : xiShiftEulerUpperSet omega =>
          eulerXiShiftPick omega z.1 w.1)
        (Nat.card (XiShiftRightZeroCopy omega)) ∧
      ∀ r : ℕ, HasFiniteKernelNegativeDimension
          (fun z w : xiShiftEulerUpperSet omega =>
            eulerXiShiftPick omega z.1 w.1) r →
        r ≤ Nat.card (XiShiftRightZeroCopy omega)) ∨
    (Infinite (XiShiftRightZeroCopy omega) ∧
      ∀ r : ℕ, HasFiniteKernelNegativeDimension
        (fun z w : xiShiftEulerUpperSet omega =>
          eulerXiShiftPick omega z.1 w.1) r) := by
  have h := xiShiftRegularUpperKernel_openRegion_negativeIndex_classification
    homega hnon (xiShiftEulerUpperSet omega)
    (isOpen_xiShiftEulerUpperSet omega)
    (xiShiftEulerUpperSet_subset_upperHalfPlane homega)
    (suzukiCanonicalE_ne_zero_of_mem_xiShiftEulerUpperSet homega)
    (xiShiftEulerUpperSet_nonempty omega)
  simpa only [eulerXiShiftPick_eq_upperHalfPlaneSchurKernel] using h

/-- Every one-node Euler Pick test is strictly positive. -/
theorem eulerXiShiftPick_subtype_diagonal_pos
    {omega : ℝ} (homega : 0 < omega)
    (z : xiShiftEulerUpperSet omega) :
    0 < (eulerXiShiftPick omega z.1 z.1).re :=
  re_eulerXiShiftPick_diagonal_pos homega z.2

/-- Strictly positive one-node tests force the first possible failing
correlation order to be at least two. -/
theorem two_le_eulerXiShiftPick_firstFailingCorrelationOrder
    {omega : ℝ} (homega : 0 < omega) :
    (2 : WithTop ℕ) ≤ kernelFirstFailingCorrelationOrder
      (fun z w : xiShiftEulerUpperSet omega =>
        eulerXiShiftPick omega z.1 w.1) := by
  apply two_le_kernelFirstFailingCorrelationOrder_of_diagonal_nonneg
  intro z
  exact le_of_lt (eulerXiShiftPick_subtype_diagonal_pos homega z)

/-- At a nonexceptional shift, first failing order is infinite exactly when
the shifted right-divisor copy type is empty. -/
theorem eulerXiShiftPick_firstFailingCorrelationOrder_eq_top_iff_isEmpty
    {omega : ℝ} (homega : 0 < omega)
    (hnon : SuzukiShiftNonexceptional omega) :
    kernelFirstFailingCorrelationOrder
        (fun z w : xiShiftEulerUpperSet omega =>
          eulerXiShiftPick omega z.1 w.1) = ⊤ ↔
      IsEmpty (XiShiftRightZeroCopy omega) := by
  rw [kernelFirstFailingCorrelationOrder_eq_top_iff,
    hasNegativeKernelPacket_iff_negativeDimension_one]
  let K := fun z w : xiShiftEulerUpperSet omega =>
    eulerXiShiftPick omega z.1 w.1
  have hclass := eulerXiShiftPick_negativeIndex_classification homega hnon
  change ¬ HasFiniteKernelNegativeDimension K 1 ↔
    IsEmpty (XiShiftRightZeroCopy omega)
  constructor
  · intro hno
    rcases hclass with hfinite | hinfinite
    · obtain ⟨hfin, hdim, hbound⟩ := hfinite
      letI : Finite (XiShiftRightZeroCopy omega) := hfin
      rw [← not_nonempty_iff]
      intro hne
      letI : Nonempty (XiShiftRightZeroCopy omega) := hne
      exact hno (hasFiniteKernelNegativeDimension_one_of_pos K
        Nat.card_pos hdim)
    · exact (hno (hinfinite.2 1)).elim
  · intro hempty hdim
    rcases hclass with hfinite | hinfinite
    · obtain ⟨hfin, _, hbound⟩ := hfinite
      have hcard : Nat.card (XiShiftRightZeroCopy omega) = 0 := by
        rw [Nat.card_eq_zero]
        exact Or.inl hempty
      have := hbound 1 hdim
      omega
    · letI : Infinite (XiShiftRightZeroCopy omega) := hinfinite.1
      exact hempty.false
        (Infinite.nonempty (XiShiftRightZeroCopy omega)).some

/-- Zero-copy-free form of the exact all-orders positive-correlation law. -/
theorem eulerXiShiftPick_firstFailingCorrelationOrder_eq_top_iff
    {omega : ℝ} (homega : 0 < omega)
    (hnon : SuzukiShiftNonexceptional omega) :
    kernelFirstFailingCorrelationOrder
        (fun z w : xiShiftEulerUpperSet omega =>
          eulerXiShiftPick omega z.1 w.1) = ⊤ ↔
      ∀ q : XiZeroCopy, (I * xiSpectralPoint q).re ≤ omega := by
  rw [eulerXiShiftPick_firstFailingCorrelationOrder_eq_top_iff_isEmpty
    homega hnon]
  constructor
  · intro hempty q
    exact not_lt.mp fun hq => hempty.false ⟨q, hq⟩
  · intro h
    exact ⟨fun q => (not_lt_of_ge (h q.1)) q.2⟩

end
end RHTower
