import GaloisForLFunctions.RHTower.SuzukiCCMMixedScrewWeilBridge

/-!
# The parity gap of the restricted Weil form is a sum of squares over the Ξ-zeros

For a strict-interior smooth source `A` at aperture `a`, let `Ã(x) = conj A(−x)` be its Hermitian
reflection (`hermitianReflection`). Then `A + Ã` is Hermitian-even and `A − Ã` Hermitian-odd. For
`A` supported in `(0, a)` they are the even and odd extensions of `A` (the sign flip of the even
extension is the odd one).

**Theorem** (`ccmRestrictedWeilForm_hermitianReflection`). The reflected Weil pairing is a sum of
SQUARES over the zero copies of `XiC`:

`Q(A, Ã) = Σ_q F_Ā(γ_q)²`,   where `F_Ā(z) = ∫ conj A(x) e^{izx} dx`.

**Theorem** (`source_add_sub_hermitianReflection`). The even-minus-odd energy gap is

`Q(A + Ã) − Q(A − Ã) = 4 Re Σ_q F_Ā(γ_q)²`.

For `A` supported in `(0, a)` the left side is the parity gap of the restricted Weil form, and
`Q(A, Ã)` is the Hankel form `∫∫ K(x+u) A(x) A(u)` of the Weil kernel. The identity is the
explicit formula applied to the convolution square `A ∗ A`.

**Proof.** The CCM form on smooth interior sources is Suzuki's Weil distribution of the Hermitian
convolution (`ccmRestrictedWeilForm_complexSmooth_eq_suzukiWeilDistribution`), whose terms factor
as products of Fourier transforms at `∓γ_q`. The transform of `Ã` at `−γ` is the transform of
`conj A` at `γ` (`suzukiEntireFourier_hermitianReflection`), so every term is a square. The gap
identity is the polarization `Q(u+v) − Q(u−v) = 2(Q(u,v) + Q(v,u)) = 4 Re Q(u,v)`.
-/

noncomputable section

open Complex MeasureTheory Set Filter Topology

namespace RHTower.CCMParityHankel

variable {a : SuzukiPositiveAperture}

/-- The Hermitian reflection `Ã(x) = conj A(−x)` of a strict-interior smooth source. -/
def hermitianReflection (A : CCMComplexSmoothInteriorSource a) :
    CCMComplexSmoothInteriorSource a where
  toFun x := (starRingEnd ℂ) (A (-x))
  smooth := Complex.conjCLE.contDiff.comp (A.smooth.comp contDiff_neg)
  hasCompactSupport := by
    have h := (A.hasCompactSupport.comp_homeomorph (Homeomorph.neg ℝ)).comp_left
      (g := starRingEnd ℂ) (map_zero _)
    exact h
  tsupport_subset := by
    intro x hx
    have hsupp : Function.support (fun x : ℝ => (starRingEnd ℂ) (A (-x))) =
        (Homeomorph.neg ℝ) ⁻¹' Function.support A := by
      ext y
      simp [Function.mem_support]
    have hx' : x ∈ (Homeomorph.neg ℝ) ⁻¹' tsupport A := by
      rw [tsupport, (Homeomorph.neg ℝ).preimage_closure, ← hsupp]
      exact hx
    have hmem := A.tsupport_subset hx'
    have hneg : (Homeomorph.neg ℝ) x = -x := rfl
    simp only [hneg, mem_Ioo] at hmem
    simp only [mem_Ioo]
    constructor <;> linarith [hmem.1, hmem.2]

@[simp] theorem hermitianReflection_apply (A : CCMComplexSmoothInteriorSource a) (x : ℝ) :
    hermitianReflection A x = (starRingEnd ℂ) (A (-x)) := rfl

/-- **The reflected Weil pairing is a sum of squares over the Ξ-zeros.** -/
theorem ccmRestrictedWeilForm_hermitianReflection (A : CCMComplexSmoothInteriorSource a) :
    ccmRestrictedWeilForm a A.toCCMFormVector (hermitianReflection A).toCCMFormVector =
      ∑' q : XiZeroCopy,
        suzukiSmoothFourier A.toSuzukiSmoothCompactTest.conjugate (xiSpectralPoint q) ^ 2 := by
  rw [ccmRestrictedWeilForm_complexSmooth_eq_suzukiWeilDistribution,
    suzukiWeilDistribution_hermitianConvolution a.2.le]
  refine tsum_congr fun q => ?_
  have h : suzukiSmoothFourier (hermitianReflection A).toSuzukiSmoothCompactTest
      (-xiSpectralPoint q) =
      suzukiSmoothFourier A.toSuzukiSmoothCompactTest.conjugate (xiSpectralPoint q) := by
    have href := suzukiEntireFourier_hermitianReflection A.toSuzukiSmoothCompactTest
      (-xiSpectralPoint q)
    rw [neg_neg] at href
    exact href
  rw [h, sq]

theorem ccmRestrictedWeilForm_sub_sub (u v : CCMArchimedeanFormDomain a) :
    ccmRestrictedWeilForm a (u - v) (u - v) =
      ccmRestrictedWeilForm a u u - ccmRestrictedWeilForm a u v -
        ccmRestrictedWeilForm a v u + ccmRestrictedWeilForm a v v := by
  unfold ccmRestrictedWeilForm
  simp only [map_sub, inner_sub_left, inner_sub_right]
  ring

/-- **Parity gap as a sum of squares over the Ξ-zeros.** The energy of the Hermitian-even
combination `A + Ã` minus that of the Hermitian-odd combination `A − Ã` is `4 Re Σ_q F_Ā(γ_q)²`. -/
theorem source_add_sub_hermitianReflection (A : CCMComplexSmoothInteriorSource a) :
    ccmRestrictedWeilSourceQuadratic a
        (A.toCCMFormVector + (hermitianReflection A).toCCMFormVector) -
      ccmRestrictedWeilSourceQuadratic a
        (A.toCCMFormVector - (hermitianReflection A).toCCMFormVector) =
      4 * (∑' q : XiZeroCopy,
        suzukiSmoothFourier A.toSuzukiSmoothCompactTest.conjugate (xiSpectralPoint q) ^ 2).re := by
  set u := A.toCCMFormVector with hu
  set v := (hermitianReflection A).toCCMFormVector with hv
  rw [← ccmRestrictedWeilForm_self_re_eq_source, ← ccmRestrictedWeilForm_self_re_eq_source,
    ← ccmRestrictedWeilForm_hermitianReflection, ccmRestrictedWeilForm_add_add,
    ccmRestrictedWeilForm_sub_sub, ← star_ccmRestrictedWeilForm_swap a u v]
  simp only [Complex.add_re, Complex.sub_re, Complex.star_def, Complex.conj_re]
  ring

end RHTower.CCMParityHankel
