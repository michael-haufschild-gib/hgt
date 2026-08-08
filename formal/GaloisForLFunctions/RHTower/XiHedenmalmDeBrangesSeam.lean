import GaloisForLFunctions.RHTower.XiHedenmalmMultiplicityFourierBridge
import GaloisForLFunctions.HTGeometry.ReflectedDividedDifference

/-!
# The source-defined Hedenmalm--de Branges seam

The entire function `E = XiC + i XiC'` is defined from the completed theta transform without
enumerating its divisor.  Its Schwarz-reflected commutator is exactly the division-free Xi
Bezoutian.  Removing the diagonal by `dslope` gives an everywhere-defined kernel whose diagonal at
a Xi zero is `XiC'(alpha)^2`, while distinct Xi zeros are orthogonal for the kernel.

This is unconditional bridge infrastructure.  No positivity of the Bezoutian is asserted: that
positivity is the RH-bearing de Branges condition.  The final theorem identifies the separate
multiplicity obstruction exactly: the kernel diagonal at a divisor support point is nonzero if and
only if its analytic multiplicity is one.
-/

open Complex

namespace RHTower

noncomputable section

/-- The theta-source Hermite--Biehler candidate `E = XiC + i XiC'`. -/
def xiHedenmalmDeBrangesE (z : ℂ) : ℂ :=
  XiC z + I * deriv XiC z

/-- The algebraic Schwarz partner `E# = XiC - i XiC'`. -/
def xiHedenmalmDeBrangesESharp (z : ℂ) : ℂ :=
  XiC z - I * deriv XiC z

/-- Schwarz reality in the centered Xi coordinate, proved within the Hilbert--Polya route. -/
theorem xiHedenmalm_XiC_conj (z : ℂ) :
    XiC ((starRingEnd ℂ) z) = (starRingEnd ℂ) (XiC z) :=
  XiC_conj z

/-- Schwarz reality passes from `XiC` to its complex derivative. -/
theorem deriv_XiC_conj (z : ℂ) :
    deriv XiC ((starRingEnd ℂ) z) =
      (starRingEnd ℂ) (deriv XiC z) := by
  have hder : deriv XiC =
      (starRingEnd ℂ) ∘ deriv XiC ∘ (starRingEnd ℂ) := by
    calc
      deriv XiC = deriv ((starRingEnd ℂ) ∘ XiC ∘ (starRingEnd ℂ)) := by
        apply congrArg deriv
        funext w
        simp only [Function.comp_apply]
        rw [xiHedenmalm_XiC_conj]
        simp
      _ = (starRingEnd ℂ) ∘ deriv XiC ∘ (starRingEnd ℂ) := deriv_conj_conj
  have h := congrArg (starRingEnd ℂ) (congrFun hder z)
  simpa using h.symm

/-- The Weil sharp involution sends the theta-source candidate to its displayed partner. -/
theorem xiWeilSharp_xiHedenmalmDeBrangesE (z : ℂ) :
    xiWeilSharp xiHedenmalmDeBrangesE z =
      xiHedenmalmDeBrangesESharp z := by
  rw [xiWeilSharp, xiHedenmalmDeBrangesE, xiHedenmalmDeBrangesESharp,
    xiHedenmalm_XiC_conj, deriv_XiC_conj]
  simp
  ring

/-- The derivative of the centered even Xi function is odd. -/
theorem deriv_XiC_neg (z : ℂ) :
    deriv XiC (-z) = -deriv XiC z := by
  simpa only [iteratedDeriv_one, pow_one, neg_one_mul] using
    iteratedDeriv_XiC_neg 1 z

/-- Centered functional-equation reflection exchanges the Hedenmalm value with its sharp
partner. -/
theorem xiHedenmalmDeBrangesE_neg_eq_sharp (z : ℂ) :
    xiHedenmalmDeBrangesE (-z) = xiHedenmalmDeBrangesESharp z := by
  rw [xiHedenmalmDeBrangesE, xiHedenmalmDeBrangesESharp,
    XiC_even, deriv_XiC_neg]
  ring

/-- The reverse centered reflection exchanges the sharp partner back with the Hedenmalm value. -/
theorem xiHedenmalmDeBrangesESharp_neg_eq_E (z : ℂ) :
    xiHedenmalmDeBrangesESharp (-z) = xiHedenmalmDeBrangesE z := by
  rw [xiHedenmalmDeBrangesESharp, xiHedenmalmDeBrangesE,
    XiC_even, deriv_XiC_neg]
  ring

/-- The reflection-even part of the Hedenmalm pair is exactly twice the completed source. -/
theorem xiHedenmalmDeBrangesE_add_sharp (z : ℂ) :
    xiHedenmalmDeBrangesE z + xiHedenmalmDeBrangesESharp z = 2 * XiC z := by
  rw [xiHedenmalmDeBrangesE, xiHedenmalmDeBrangesESharp]
  ring

/-- The reflection-odd part of the Hedenmalm pair is exactly twice `i` times the Xi derivative. -/
theorem xiHedenmalmDeBrangesE_sub_sharp (z : ℂ) :
    xiHedenmalmDeBrangesE z - xiHedenmalmDeBrangesESharp z =
      2 * I * deriv XiC z := by
  rw [xiHedenmalmDeBrangesE, xiHedenmalmDeBrangesESharp]
  ring

/-- Division-free two-variable commutator of `E` and `E#`. -/
def xiHedenmalmDeBrangesCommutator (z v : ℂ) : ℂ :=
  xiHedenmalmDeBrangesE z * xiHedenmalmDeBrangesESharp v -
    xiHedenmalmDeBrangesESharp z * xiHedenmalmDeBrangesE v

/-- The de Branges commutator is twice `i` times the Xi derivative Bezoutian numerator. -/
theorem xiHedenmalmDeBrangesCommutator_eq (z v : ℂ) :
    xiHedenmalmDeBrangesCommutator z v =
      2 * I * (deriv XiC z * XiC v - XiC z * deriv XiC v) := by
  simp only [xiHedenmalmDeBrangesCommutator, xiHedenmalmDeBrangesE,
    xiHedenmalmDeBrangesESharp]
  ring

/-- The two-variable de Branges commutator is odd under simultaneous centered reflection. -/
theorem xiHedenmalmDeBrangesCommutator_neg_neg (z v : ℂ) :
    xiHedenmalmDeBrangesCommutator (-z) (-v) =
      -xiHedenmalmDeBrangesCommutator z v := by
  rw [xiHedenmalmDeBrangesCommutator, xiHedenmalmDeBrangesCommutator,
    xiHedenmalmDeBrangesE_neg_eq_sharp,
    xiHedenmalmDeBrangesESharp_neg_eq_E,
    xiHedenmalmDeBrangesE_neg_eq_sharp,
    xiHedenmalmDeBrangesESharp_neg_eq_E]
  ring

/-- The removable Xi derivative Bezoutian, defined on and off the diagonal. -/
def xiHedenmalmBezoutian (z v : ℂ) : ℂ :=
  dslope
    (fun w => deriv XiC z * XiC w - XiC z * deriv XiC w)
    z v

/-- The removable Xi Bezoutian is even under simultaneous centered reflection.  The numerator
is odd, and the reflected denominator supplies the second sign, including on the diagonal. -/
theorem xiHedenmalmBezoutian_neg_neg (z v : ℂ) :
    xiHedenmalmBezoutian (-z) (-v) = xiHedenmalmBezoutian z v := by
  change HTGeometry.diagonalDslopeKernel
      (fun a b => deriv XiC a * XiC b - XiC a * deriv XiC b) (-z) (-v) =
    HTGeometry.diagonalDslopeKernel
      (fun a b => deriv XiC a * XiC b - XiC a * deriv XiC b) z v
  apply HTGeometry.diagonalDslopeKernel_neg_neg_of_antiInvariant
  intro a b
  rw [deriv_XiC_neg, deriv_XiC_neg, XiC_even, XiC_even]
  ring

/-- Away from the diagonal, the removable definition is the literal Bezoutian quotient. -/
theorem xiHedenmalmBezoutian_eq_div {z v : ℂ} (h : v ≠ z) :
    xiHedenmalmBezoutian z v =
      (deriv XiC z * XiC v - XiC z * deriv XiC v) / (v - z) := by
  rw [xiHedenmalmBezoutian, dslope_of_ne _ h, slope_def_module]
  have hself : deriv XiC z * XiC z - XiC z * deriv XiC z = 0 := by ring
  rw [hself, sub_zero, smul_eq_mul]
  field_simp

/-- The division-free commutator factors through the removable Bezoutian globally. -/
theorem xiHedenmalmDeBrangesCommutator_eq_mul_bezoutian (z v : ℂ) :
    xiHedenmalmDeBrangesCommutator z v =
      2 * I * (v - z) * xiHedenmalmBezoutian z v := by
  rw [xiHedenmalmDeBrangesCommutator_eq]
  have h := sub_smul_dslope
    (fun w => deriv XiC z * XiC w - XiC z * deriv XiC w) z v
  change (v - z) * xiHedenmalmBezoutian z v =
    (deriv XiC z * XiC v - XiC z * deriv XiC v) -
      (deriv XiC z * XiC z - XiC z * deriv XiC z) at h
  have hself : deriv XiC z * XiC z - XiC z * deriv XiC z = 0 := by ring
  rw [hself, sub_zero] at h
  rw [← h]
  ring

/-- Exact diagonal value of the removable Xi Bezoutian. -/
theorem xiHedenmalmBezoutian_self (z : ℂ) :
    xiHedenmalmBezoutian z z =
      deriv XiC z ^ 2 - XiC z * deriv (deriv XiC) z := by
  rw [xiHedenmalmBezoutian, dslope_same]
  have hXi : HasDerivAt XiC (deriv XiC z) z :=
    XiC_differentiable.differentiableAt.hasDerivAt
  have hXi' : HasDerivAt (deriv XiC) (deriv (deriv XiC) z) z :=
    ((XiC_analytic z (Set.mem_univ z)).deriv).differentiableAt.hasDerivAt
  simpa [pow_two] using!
    ((hXi.const_mul (deriv XiC z)).sub
      (hXi'.const_mul (XiC z))).deriv

/-- At a Xi zero, the diagonal Bezoutian is exactly the square of the first derivative. -/
theorem xiHedenmalmBezoutian_self_of_zero {z : ℂ} (hz : XiC z = 0) :
    xiHedenmalmBezoutian z z = deriv XiC z ^ 2 := by
  rw [xiHedenmalmBezoutian_self, hz, zero_mul, sub_zero]

/-- Distinct Xi zeros are off-diagonally orthogonal for the source-defined Bezoutian. -/
theorem xiHedenmalmBezoutian_eq_zero_of_distinct_zeros
    {z v : ℂ} (hz : XiC z = 0) (hv : XiC v = 0) (h : v ≠ z) :
    xiHedenmalmBezoutian z v = 0 := by
  rw [xiHedenmalmBezoutian_eq_div h, hz, hv]
  ring

/-- The Bezoutian diagonal retains one divisor fiber precisely when that zero is simple. -/
theorem xiHedenmalmBezoutian_self_ne_zero_iff_simple
    (rho : XiDivisorSupport) :
    xiHedenmalmBezoutian (xiSpectralPointSupport rho)
        (xiSpectralPointSupport rho) ≠ 0 ↔
      xiSupportMultiplicity rho = 1 := by
  have hpos := xi_divisor_pos_on_support rho
  have hn : 0 < Int.toNat ((MeromorphicOn.divisor xi Set.univ) (rho : ℂ)) := by
    omega
  let q : XiZeroCopy := ⟨rho, ⟨0, hn⟩⟩
  have hzero : XiC (xiSpectralPointSupport rho) = 0 := by
    simpa only [q, xiSpectralPoint_eq_support] using XiC_xiSpectralPoint_eq_zero q
  rw [xiHedenmalmBezoutian_self_of_zero hzero]
  have h := xiThetaEigenFourier_self_ne_zero_iff_multiplicity_one rho
  constructor
  · intro hsq
    have hd : deriv XiC (xiSpectralPointSupport rho) ≠ 0 := by
      intro hzero'
      apply hsq
      rw [hzero', zero_pow]
      norm_num
    apply h.mp
    rw [xiThetaEigenFourier_self]
    exact mul_ne_zero I_ne_zero hd
  · intro hm
    have hmul := h.mpr hm
    rw [xiThetaEigenFourier_self] at hmul
    exact pow_ne_zero 2 (mul_ne_zero_iff.mp hmul).2

end

end RHTower
