import GaloisForLFunctions.RHTower.XiHadamardFactorization
import Mathlib.LinearAlgebra.Finsupp.LSum

/-!
# Deninger's divisor-side arithmetic flow

This file constructs the algebraic spectral target of Deninger's arithmetic cohomology directly
from the multiplicity-exact Xi divisor. It is deliberately labelled a target construction:
because its basis is indexed by the zeros, it does not provide the sought prime-geometric source
construction or prove positivity.

The construction nevertheless closes several exact parts of the program without hypotheses:

* `H⁰ = ℂ`, `H¹ = XiZeroCopy →₀ ℂ`, and `H² = ℂ`;
* the degree-zero and degree-two generators have weights zero and one;
* the degree-one generator is diagonal with eigenvalue the corresponding Xi zero;
* its exponential is an honest one-parameter algebraic flow;
* the centered characteristic product is the existing multiplicity-exact canonical product, and
  the Hadamard quotient times this product is exactly `XiC`.

No Riemann-hypothesis premise, positivity premise, `sorry`, or new axiom occurs here.
-/

noncomputable section

open Complex

namespace RHTower

/-- Deninger's algebraic degree-zero Tate term for `Spec ℤ`. -/
abbrev DeningerDivisorH0 := ℂ

/-- Multiplicity-exact algebraic degree-one target, with one basis vector per Xi-divisor copy. -/
abbrev DeningerDivisorH1 := XiZeroCopy →₀ ℂ

/-- Deninger's algebraic degree-two Tate term for `Spec ℤ`. -/
abbrev DeningerDivisorH2 := ℂ

/-- A diagonal endomorphism of a finitely supported free module. -/
def finsuppDiagonal {ι : Type*} (weight : ι → ℂ) : Module.End ℂ (ι →₀ ℂ) :=
  Finsupp.linearCombination ℂ (fun i => Finsupp.single i (weight i))

@[simp]
theorem finsuppDiagonal_single {ι : Type*} (weight : ι → ℂ) (i : ι) (c : ℂ) :
    finsuppDiagonal weight (Finsupp.single i c) =
      Finsupp.single i (weight i * c) := by
  simp [finsuppDiagonal, mul_comm]

@[simp]
theorem finsuppDiagonal_apply {ι : Type*} (weight : ι → ℂ)
    (a : ι →₀ ℂ) (i : ι) :
    finsuppDiagonal weight a i = weight i * a i := by
  classical
  induction a using Finsupp.induction with
  | zero => simp
  | single_add j c a hj _hc ha =>
      by_cases hji : j = i
      · subst j
        simp [map_add, ha, mul_add]
      · simp [map_add, ha, hji]

/-- The uncentered Frobenius-flow eigenvalue attached to a divisor copy. -/
def deningerDivisorThetaEigen (q : XiZeroCopy) : ℂ := q.1

/-- Centering the Frobenius eigenvalue recovers the existing Xi spectral coordinate. -/
theorem deningerDivisorThetaEigen_eq (q : XiZeroCopy) :
    deningerDivisorThetaEigen q =
      1 / 2 + xiSpectralPoint q * Complex.I := by
  simp only [deningerDivisorThetaEigen, xiSpectralPoint]
  have hI : (-Complex.I) * Complex.I = (1 : ℂ) := by
    rw [neg_mul, Complex.I_mul_I]
    ring
  rw [mul_assoc, hI, mul_one]
  ring

/-- Every divisor-flow eigenvalue is an actual zero of completed zeta. -/
theorem xi_deningerDivisorThetaEigen_eq_zero (q : XiZeroCopy) :
    xi (deningerDivisorThetaEigen q) = 0 :=
  xi_eq_zero_of_mem_divisor_support q.1

/-- The degree-one infinitesimal Frobenius generator. -/
def deningerDivisorTheta : Module.End ℂ DeningerDivisorH1 :=
  finsuppDiagonal deningerDivisorThetaEigen

@[simp]
theorem deningerDivisorTheta_single (q : XiZeroCopy) (c : ℂ) :
    deningerDivisorTheta (Finsupp.single q c) =
      Finsupp.single q (deningerDivisorThetaEigen q * c) :=
  finsuppDiagonal_single deningerDivisorThetaEigen q c

@[simp]
theorem xiZeroCopyReflectEquiv_apply_apply (q : XiZeroCopy) :
    xiZeroCopyReflectEquiv (xiZeroCopyReflectEquiv q) = q := by
  have hfst :
      (xiZeroCopyReflectEquiv (xiZeroCopyReflectEquiv q)).1 = q.1 := by
    apply Subtype.ext
    simp [xiZeroCopyReflectEquiv, xiZeroReflectEquiv, Equiv.sigmaCongr,
      Equiv.sigmaCongrRight, Equiv.sigmaCongrLeft]
  apply Sigma.ext hfst
  apply (Fin.heq_ext_iff (congrArg (fun rho : XiDivisorSupport =>
    Int.toNat ((MeromorphicOn.divisor xi Set.univ) (rho : ℂ))) hfst)).2
  simp [xiZeroCopyReflectEquiv, xiZeroReflectEquiv, Equiv.sigmaCongr,
    Equiv.sigmaCongrRight, Equiv.sigmaCongrLeft]
  exact Fin.val_eq_val_of_heq (cast_heq _ q.2)

/--
Algebraic cup product followed by the `H² ≃ ℂ(-1)` trace. It pairs a divisor basis vector with
its functional-equation reflection.
-/
def deningerDivisorCupTrace : LinearMap.BilinForm ℂ DeningerDivisorH1 :=
  Finsupp.linearCombination ℂ (fun q : XiZeroCopy =>
    Finsupp.lapply (R := ℂ) (M := ℂ) (xiZeroCopyReflectEquiv q))

@[simp]
theorem deningerDivisorCupTrace_single (q r : XiZeroCopy) (a b : ℂ) :
    deningerDivisorCupTrace (Finsupp.single q a) (Finsupp.single r b) =
      if xiZeroCopyReflectEquiv q = r then a * b else 0 := by
  classical
  by_cases h : xiZeroCopyReflectEquiv q = r
  · rw [if_pos h]
    simp [deningerDivisorCupTrace, h, smul_eq_mul]
  · rw [if_neg h]
    simp [deningerDivisorCupTrace, h, smul_eq_mul]

@[simp]
theorem deningerDivisorCupTrace_single_left
    (q : XiZeroCopy) (c : ℂ) (b : DeningerDivisorH1) :
    deningerDivisorCupTrace (Finsupp.single q c) b =
      c * b (xiZeroCopyReflectEquiv q) := by
  simp [deningerDivisorCupTrace, smul_eq_mul]

@[simp]
theorem deningerDivisorCupTrace_single_right
    (a : DeningerDivisorH1) (q : XiZeroCopy) (c : ℂ) :
    deningerDivisorCupTrace a (Finsupp.single q c) =
      a (xiZeroCopyReflectEquiv q) * c := by
  classical
  induction a using Finsupp.induction with
  | zero => simp
  | single_add r b a hr _hb ha =>
      rw [map_add, LinearMap.add_apply, deningerDivisorCupTrace_single, ha,
        Finsupp.add_apply]
      by_cases h : xiZeroCopyReflectEquiv r = q
      · have hrq : r = xiZeroCopyReflectEquiv q := by
          rw [← h, xiZeroCopyReflectEquiv_apply_apply]
        rw [hrq]
        simp [xiZeroCopyReflectEquiv_apply_apply]
        ring
      · have hrq : r ≠ xiZeroCopyReflectEquiv q := by
          intro hrq
          apply h
          rw [hrq, xiZeroCopyReflectEquiv_apply_apply]
        simp [h, hrq]

/-- The divisor cup-trace pairing is nondegenerate on both sides. -/
theorem deningerDivisorCupTrace_nondegenerate :
    deningerDivisorCupTrace.Nondegenerate := by
  constructor
  · intro a ha
    ext q
    have h := ha (Finsupp.single (xiZeroCopyReflectEquiv q) 1)
    simpa using h
  · intro b hb
    ext q
    have h := hb (Finsupp.single (xiZeroCopyReflectEquiv q) 1)
    simpa using h

/-- Functional-equation reflection pairs Frobenius weights summing to one. -/
theorem deningerDivisorThetaEigen_add_reflect (q : XiZeroCopy) :
    deningerDivisorThetaEigen q +
      deningerDivisorThetaEigen (xiZeroCopyReflectEquiv q) = 1 := by
  change (q.1 : ℂ) + (xiZeroReflectEquiv q.1 : ℂ) = 1
  rw [xiZeroReflectEquiv_apply]
  ring

/-- Cup products of divisor eigenlines obey Deninger's weight-one selection rule. -/
theorem deningerDivisorCupTrace_single_eq_zero_of_add_ne_one
    (q r : XiZeroCopy) (a b : ℂ)
    (hweight :
      deningerDivisorThetaEigen q + deningerDivisorThetaEigen r ≠ 1) :
    deningerDivisorCupTrace (Finsupp.single q a) (Finsupp.single r b) = 0 := by
  rw [deningerDivisorCupTrace_single]
  split_ifs with h
  · exfalso
    apply hweight
    rw [← h]
    exact deningerDivisorThetaEigen_add_reflect q
  · rfl

private theorem deningerDivisorTheta_cup_single_single
    (q r : XiZeroCopy) (a b : ℂ) :
    deningerDivisorCupTrace
          (deningerDivisorTheta (Finsupp.single q a)) (Finsupp.single r b) +
        deningerDivisorCupTrace (Finsupp.single q a)
          (deningerDivisorTheta (Finsupp.single r b)) =
      deningerDivisorCupTrace (Finsupp.single q a) (Finsupp.single r b) := by
  rw [deningerDivisorTheta_single, deningerDivisorTheta_single,
    deningerDivisorCupTrace_single, deningerDivisorCupTrace_single,
    deningerDivisorCupTrace_single]
  split_ifs with h
  · have hweight :
        deningerDivisorThetaEigen q + deningerDivisorThetaEigen r = 1 := by
      rw [← h]
      exact deningerDivisorThetaEigen_add_reflect q
    linear_combination a * b * hweight
  · ring

private theorem deningerDivisorTheta_cup_single_left
    (q : XiZeroCopy) (c : ℂ) (b : DeningerDivisorH1) :
    deningerDivisorCupTrace
          (deningerDivisorTheta (Finsupp.single q c)) b +
        deningerDivisorCupTrace (Finsupp.single q c) (deningerDivisorTheta b) =
      deningerDivisorCupTrace (Finsupp.single q c) b := by
  induction b using Finsupp.induction with
  | zero => simp
  | single_add r d b _hr _hd hb =>
      simp only [map_add]
      have hqr := deningerDivisorTheta_cup_single_single q r c d
      linear_combination hqr + hb

/--
The divisor-side generator is a derivation of cup product after the `H²` trace: its two
degree-one weights add to the Tate weight one.
-/
theorem deningerDivisorTheta_cup (a b : DeningerDivisorH1) :
    deningerDivisorCupTrace (deningerDivisorTheta a) b +
        deningerDivisorCupTrace a (deningerDivisorTheta b) =
      deningerDivisorCupTrace a b := by
  induction a using Finsupp.induction generalizing b with
  | zero => simp
  | single_add q c a _hq _hc ha =>
      simp only [map_add, LinearMap.add_apply]
      have hq := deningerDivisorTheta_cup_single_left q c b
      have hab := ha b
      linear_combination hq + hab

/-- The degree-zero generator has Tate weight zero. -/
def deningerDivisorTheta0 : Module.End ℂ DeningerDivisorH0 := 0

/-- The degree-two generator has Tate weight one. -/
def deningerDivisorTheta2 : Module.End ℂ DeningerDivisorH2 := LinearMap.id

@[simp] theorem deningerDivisorTheta0_apply (z : DeningerDivisorH0) :
    deningerDivisorTheta0 z = 0 := rfl

@[simp] theorem deningerDivisorTheta2_apply (z : DeningerDivisorH2) :
    deningerDivisorTheta2 z = z := rfl

/-- Coefficient of the time-`t` Frobenius flow on one divisor eigenline. -/
def deningerDivisorFlowEigen (t : ℝ) (q : XiZeroCopy) : ℂ :=
  Complex.exp ((t : ℂ) * deningerDivisorThetaEigen q)

/-- Algebraic exponential flow on the multiplicity-exact degree-one target. -/
def deningerDivisorFlow (t : ℝ) : Module.End ℂ DeningerDivisorH1 :=
  finsuppDiagonal (deningerDivisorFlowEigen t)

@[simp]
theorem deningerDivisorFlow_single (t : ℝ) (q : XiZeroCopy) (c : ℂ) :
    deningerDivisorFlow t (Finsupp.single q c) =
      Finsupp.single q (deningerDivisorFlowEigen t q * c) :=
  finsuppDiagonal_single (deningerDivisorFlowEigen t) q c

/-- Time zero acts identically. -/
theorem deningerDivisorFlow_zero :
    deningerDivisorFlow 0 = LinearMap.id := by
  ext q c
  simp [deningerDivisorFlow, deningerDivisorFlowEigen]

/-- The divisor-side flow satisfies the one-parameter group law. -/
theorem deningerDivisorFlow_add (t u : ℝ) :
    deningerDivisorFlow (t + u) =
      deningerDivisorFlow t ∘ₗ deningerDivisorFlow u := by
  ext a q
  simp only [LinearMap.comp_apply, deningerDivisorFlow,
    finsuppDiagonal_apply, deningerDivisorFlowEigen]
  rw [← mul_assoc, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/--
Zeros of centered Xi are exactly centered eigenvalues of the divisor-side generator, with analytic
multiplicity represented by the copy index.
-/
theorem XiC_eq_zero_iff_exists_deningerDivisorThetaEigen (z : ℂ) :
    XiC z = 0 ↔
      ∃ q : XiZeroCopy,
        deningerDivisorThetaEigen q = 1 / 2 + z * Complex.I := by
  rw [XiC_eq_zero_iff_exists_xiZeroCopy]
  constructor
  · rintro ⟨q, rfl⟩
    exact ⟨q, deningerDivisorThetaEigen_eq q⟩
  · rintro ⟨q, hq⟩
    refine ⟨q, ?_⟩
    rw [deningerDivisorThetaEigen_eq q] at hq
    have hI : Complex.I ≠ 0 := Complex.I_ne_zero
    exact mul_right_cancel₀ hI (add_left_cancel hq)

/-- The centered regularized characteristic product of the divisor generator. -/
def deningerDivisorCharacteristicProduct : ℂ → ℂ :=
  canonicalProductE1Indexed xiSpectralPoint

/-- The divisor characteristic product is the multiplicity-exact Xi canonical product. -/
theorem deningerDivisorCharacteristicProduct_eq_xiCanonicalProduct :
    deningerDivisorCharacteristicProduct = xiCanonicalProduct := rfl

/--
Exact completed determinant identity up to the zero-free Hadamard normalization: the normalization
factor times the divisor characteristic product is centered completed zeta.
-/
theorem xiHadamardQuotient_mul_deningerDivisorCharacteristicProduct :
    xiHadamardQuotient * deningerDivisorCharacteristicProduct = XiC :=
  xiHadamardQuotient_mul_canonicalProduct

end RHTower
