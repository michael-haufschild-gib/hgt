import GaloisForLFunctions.RHTower.Deninger.DeningerArithmeticJetDuality
import GaloisForLFunctions.RHTower.Deninger.DeningerArithmeticCharacteristic
import GaloisForLFunctions.RHTower.Deninger.DeningerLefschetzTrace
import GaloisForLFunctions.RHTower.XiCanonicalProduct
import GaloisForLFunctions.RHTower.XiHadamardFactorization
import Mathlib.LinearAlgebra.Matrix.Block

/-!
# Regularized determinant of the Xi-divisor jet comparison operator

On the multiplicity-bounded derivative jets at a centered Xi point `rho`, the normalized centered
source Frobenius

`B = (-I) * (Theta - 1/2)`

has lower-triangular matrix

`(B a)_k = rho * a_k + k * a_(k-1)`.

This file keeps the full nilpotent derivative term.  It proves that the local characteristic
determinant is `(z - rho)^m`, where `m` is the analytic Xi multiplicity, and that the local
genus-one normalized determinant is exactly `E₁(z/rho)^m`.  Consequently the net of determinants
over finite source-support windows converges unconditionally, and its product is the existing
multiplicity-exact Xi canonical product.

Thus nilpotent Jordan terms disappear from trace and determinant by finite-dimensional
triangularity.  No RH, positivity, zero-location, or simplicity premise is used.  The carrier is
nevertheless indexed by `XiDivisorSupport`; this is an unconditional analytic comparison
determinant, not the missing transport of a determinant from independently constructed arithmetic
cohomology.
-/

open Complex Filter Matrix Set Topology

namespace RHTower

noncomputable section

/--
Matrix of the normalized centered source Frobenius `(-I) * (Theta - 1/2)` on one full local
derivative-jet fiber.
-/
def deningerArithmeticJetCenteredMatrix
    (rho : XiDivisorSupport) :
    Matrix (DeningerArithmeticJetIndex rho)
      (DeningerArithmeticJetIndex rho) ℂ :=
  fun k j =>
    if k = j then xiSpectralPointSupport rho
    else if j.val + 1 = k.val then (k.val : ℂ) else 0

@[simp]
theorem deningerArithmeticJetCenteredMatrix_diagonal
    (rho : XiDivisorSupport)
    (k : DeningerArithmeticJetIndex rho) :
    deningerArithmeticJetCenteredMatrix rho k k =
      xiSpectralPointSupport rho := by
  simp [deningerArithmeticJetCenteredMatrix]

/-- The full local source matrix is lower triangular, including every positive-depth jet. -/
theorem deningerArithmeticJetCenteredMatrix_lowerTriangular
    (rho : XiDivisorSupport) :
    (deningerArithmeticJetCenteredMatrix rho).BlockTriangular
      OrderDual.toDual := by
  intro i j hji
  have hij : i ≠ j := by
    intro hij
    subst j
    exact (lt_irrefl (OrderDual.toDual i)) hji
  have hsucc : j.val + 1 ≠ i.val := by
    have hijlt : i < j := hji
    have hijltVal : i.val < j.val := hijlt
    exact (Nat.ne_of_lt
      (lt_trans hijltVal (Nat.lt_succ_self j.val))).symm
  simp [deningerArithmeticJetCenteredMatrix, hij, hsucc]

/--
Every local source jet block has the multiplicity-exact characteristic determinant.  The
nilpotent derivative term contributes no determinant factor.
-/
theorem det_sub_deningerArithmeticJetCenteredMatrix
    (rho : XiDivisorSupport) (z : ℂ) :
    (z • (1 : Matrix (DeningerArithmeticJetIndex rho)
          (DeningerArithmeticJetIndex rho) ℂ) -
        deningerArithmeticJetCenteredMatrix rho).det =
      (z - xiSpectralPointSupport rho) ^
        xiSupportMultiplicity rho := by
  let M :=
    z • (1 : Matrix (DeningerArithmeticJetIndex rho)
      (DeningerArithmeticJetIndex rho) ℂ) -
      deningerArithmeticJetCenteredMatrix rho
  have hM : M.BlockTriangular OrderDual.toDual := by
    intro i j hji
    have hij : i ≠ j := by
      intro hij
      subst j
      exact (lt_irrefl (OrderDual.toDual i)) hji
    have hsucc : j.val + 1 ≠ i.val := by
      have hijlt : i < j := hji
      have hijltVal : i.val < j.val := hijlt
      exact (Nat.ne_of_lt
        (lt_trans hijltVal (Nat.lt_succ_self j.val))).symm
    simp [M, deningerArithmeticJetCenteredMatrix, hij, hsucc]
  rw [Matrix.det_of_lowerTriangular M hM]
  simp [M, deningerArithmeticJetCenteredMatrix, Finset.prod_const]

/-- The local normalized source block has multiplicity-weighted trace. -/
theorem trace_deningerArithmeticJetCenteredMatrix
    (rho : XiDivisorSupport) :
    Matrix.trace (deningerArithmeticJetCenteredMatrix rho) =
      (xiSupportMultiplicity rho : ℂ) *
        xiSpectralPointSupport rho := by
  simp [Matrix.trace, deningerArithmeticJetCenteredMatrix]

theorem xiSpectralPointSupport_ne_zero
    (rho : XiDivisorSupport) :
    xiSpectralPointSupport rho ≠ 0 := by
  rw [xiSpectralPointSupport, mul_ne_zero_iff]
  exact ⟨sub_ne_zero.mpr (xi_divisor_support_ne_half rho),
    neg_ne_zero.mpr Complex.I_ne_zero⟩

/--
Genus-one regularized determinant of one local source jet block, normalized at the origin.
-/
def deningerArithmeticJetLocalRegularizedDeterminant
    (rho : XiDivisorSupport) (z : ℂ) : ℂ :=
  ((-xiSpectralPointSupport rho) ^
      xiSupportMultiplicity rho)⁻¹ *
    (z • (1 : Matrix (DeningerArithmeticJetIndex rho)
          (DeningerArithmeticJetIndex rho) ℂ) -
        deningerArithmeticJetCenteredMatrix rho).det *
    Complex.exp
      ((xiSupportMultiplicity rho : ℂ) *
        (z / xiSpectralPointSupport rho))

/--
The local matrix determinant is exactly the multiplicity power of the Weierstrass `E₁` factor.
-/
theorem deningerArithmeticJetLocalRegularizedDeterminant_eq
    (rho : XiDivisorSupport) (z : ℂ) :
    deningerArithmeticJetLocalRegularizedDeterminant rho z =
      weierstrassE1 (z / xiSpectralPointSupport rho) ^
        xiSupportMultiplicity rho := by
  rw [deningerArithmeticJetLocalRegularizedDeterminant,
    det_sub_deningerArithmeticJetCenteredMatrix]
  have hrho := xiSpectralPointSupport_ne_zero rho
  have hratio :
      (z - xiSpectralPointSupport rho) /
          (-xiSpectralPointSupport rho) =
        1 - z / xiSpectralPointSupport rho := by
    field_simp
    ring
  rw [show
      ((-xiSpectralPointSupport rho) ^
            xiSupportMultiplicity rho)⁻¹ *
          (z - xiSpectralPointSupport rho) ^
            xiSupportMultiplicity rho =
        ((z - xiSpectralPointSupport rho) /
            (-xiSpectralPointSupport rho)) ^
              xiSupportMultiplicity rho by
      rw [div_pow, div_eq_mul_inv]
      ring]
  rw [hratio, Complex.exp_nat_mul]
  simp [weierstrassE1, mul_pow]

/-- Finite regularized determinant formed from the actual local source Frobenius blocks. -/
def deningerArithmeticJetFiniteRegularizedDeterminant
    (S : Finset XiDivisorSupport) (z : ℂ) : ℂ :=
  ∏ rho ∈ S,
    deningerArithmeticJetLocalRegularizedDeterminant rho z

/--
Each finite source-support determinant is exactly the product over all of its multiplicity jet
coordinates.
-/
theorem deningerArithmeticJetFiniteRegularizedDeterminant_eq
    (S : Finset XiDivisorSupport) (z : ℂ) :
    deningerArithmeticJetFiniteRegularizedDeterminant S z =
      ∏ q ∈ S.sigma (fun _ => Finset.univ),
        weierstrassE1 (z / xiSpectralPoint q) := by
  rw [deningerArithmeticJetFiniteRegularizedDeterminant,
    Finset.prod_sigma]
  apply Finset.prod_congr rfl
  intro rho hrho
  rw [deningerArithmeticJetLocalRegularizedDeterminant_eq]
  simp [xiSpectralPoint_eq_support, xiSupportMultiplicity]

/-- Infinite regularized determinant assembled from every local source Frobenius block. -/
def deningerArithmeticJetRegularizedDeterminant (z : ℂ) : ℂ :=
  ∏' rho : XiDivisorSupport,
    deningerArithmeticJetLocalRegularizedDeterminant rho z

/--
The net of finite source-block determinants converges to the Xi canonical product.
-/
theorem deningerArithmeticJetLocalRegularizedDeterminant_hasProd
    (z : ℂ) :
    HasProd
      (fun rho : XiDivisorSupport =>
        deningerArithmeticJetLocalRegularizedDeterminant rho z)
      (xiCanonicalProduct z) := by
  have hprod :
      HasProd
        (fun q : XiZeroCopy =>
          weierstrassE1 (z / xiSpectralPoint q))
        (xiCanonicalProduct z) :=
    xiCanonicalProduct_hasProdLocallyUniformlyOn.hasProd
      (Set.mem_univ z)
  apply hprod.sigma
  intro rho
  rw [deningerArithmeticJetLocalRegularizedDeterminant_eq]
  simpa [xiSpectralPoint_eq_support, xiSupportMultiplicity] using!
    (hasProd_fintype
      (fun k : DeningerArithmeticJetIndex rho =>
        weierstrassE1
          (z / xiSpectralPoint (⟨rho, k⟩ : XiZeroCopy))))

/--
Local source-block determinants are multipliable; equivalently, every cofinal finite-window net
has the same unconditional product.
-/
theorem deningerArithmeticJetLocalRegularizedDeterminant_multipliable
    (z : ℂ) :
    Multipliable
      (fun rho : XiDivisorSupport =>
        deningerArithmeticJetLocalRegularizedDeterminant rho z) :=
  (deningerArithmeticJetLocalRegularizedDeterminant_hasProd z).multipliable

/--
The source-jet regularized determinant is exactly the multiplicity-exact Xi canonical product.
Nilpotent Jordan terms disappear by triangularity, not by replacing the source generator with a
diagonal operator.
-/
theorem deningerArithmeticJetRegularizedDeterminant_eq_xiCanonicalProduct
    (z : ℂ) :
    deningerArithmeticJetRegularizedDeterminant z =
      xiCanonicalProduct z := by
  rw [deningerArithmeticJetRegularizedDeterminant]
  exact
    (deningerArithmeticJetLocalRegularizedDeterminant_hasProd z).tprod_eq

/--
Completed source normalization of the jet determinant.  The nowhere-zero Hadamard quotient is the
global determinant-normalization factor left undetermined by the local spectrum.
-/
def deningerArithmeticJetCompletedRegularizedDeterminant
    (z : ℂ) : ℂ :=
  xiHadamardQuotient z *
    deningerArithmeticJetRegularizedDeterminant z

/--
The completed regularized determinant of source jet Frobenius is the centered completed-Xi
function.
-/
theorem deningerArithmeticJetCompletedRegularizedDeterminant_eq_XiC
    (z : ℂ) :
    deningerArithmeticJetCompletedRegularizedDeterminant z =
      XiC z := by
  rw [deningerArithmeticJetCompletedRegularizedDeterminant,
    deningerArithmeticJetRegularizedDeterminant_eq_xiCanonicalProduct]
  exact congrFun xiHadamardQuotient_mul_canonicalProduct z

/-- Source-jet determinant in Deninger's uncentered Frobenius coordinate `s`. -/
def deningerArithmeticJetUncenteredRegularizedDeterminant
    (s : ℂ) : ℂ :=
  deningerArithmeticJetCompletedRegularizedDeterminant
    ((s - 1 / 2) * (-Complex.I))

/-- The uncentered completed source-jet determinant is Riemann's entire `xi`. -/
theorem deningerArithmeticJetUncenteredRegularizedDeterminant_eq_xi
    (s : ℂ) :
    deningerArithmeticJetUncenteredRegularizedDeterminant s =
      xi s := by
  rw [deningerArithmeticJetUncenteredRegularizedDeterminant,
    deningerArithmeticJetCompletedRegularizedDeterminant_eq_XiC]
  simp only [XiC]
  congr 1
  rw [mul_assoc, neg_mul, Complex.I_mul_I, neg_neg, mul_one]
  ring

/--
Alternating determinant quotient for the source jet realization recovers completed Riemann zeta,
including the degree-zero and degree-two Tate factors.
-/
theorem deningerArithmeticJetCharacteristicQuotient_eq_completedRiemannZeta
    {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) :
    2 * deningerArithmeticJetUncenteredRegularizedDeterminant s /
        (deningerArithmeticH0Characteristic s *
          deningerArithmeticH2Characteristic s) =
      completedRiemannZeta s := by
  rw [deningerArithmeticJetUncenteredRegularizedDeterminant_eq_xi,
    ← deningerArithmeticH1Characteristic_eq_xi]
  exact deningerArithmeticCharacteristicQuotient_eq_completedRiemannZeta
    h0 h1

/--
Relative trace canonically derived from the completed source-jet determinant.
-/
def deningerArithmeticJetRegularizedRelativeTrace
    (z : ℂ) : ℂ :=
  logDeriv deningerArithmeticJetCompletedRegularizedDeterminant z

/--
The source-jet determinant trace agrees with the multiplicity-exact spectral relative-resolvent
trace away from its divisor.
-/
theorem deningerArithmeticJetRegularizedRelativeTrace_eq_divisor
    {z : ℂ} (hz : XiC z ≠ 0) :
    deningerArithmeticJetRegularizedRelativeTrace z =
      deningerDivisorRelativeResolventTrace z := by
  rw [deningerArithmeticJetRegularizedRelativeTrace,
    show deningerArithmeticJetCompletedRegularizedDeterminant = XiC by
      funext w
      exact deningerArithmeticJetCompletedRegularizedDeterminant_eq_XiC w]
  exact (deningerDivisorRelativeResolventTrace_eq_logDeriv hz).symm

/--
Continued arithmetic Lefschetz formula for the completed source-jet determinant trace.
-/
theorem deningerArithmeticJetRegularizedRelativeTrace_eq_continuedPrimeGamma
    {z : ℂ} (h : XiExplicitAdmissible z) :
    deningerArithmeticJetRegularizedRelativeTrace z =
      continuedPrimeArchSourceRelativeTrace z := by
  rw [deningerArithmeticJetRegularizedRelativeTrace_eq_divisor
    (XiC_ne_zero_of_admissible h)]
  exact deningerResolventLefschetzTrace h

/--
Absolute-convergence arithmetic Lefschetz formula.  Its finite-place side is the honest
von-Mangoldt Dirichlet series.
-/
theorem deningerArithmeticJetRegularizedRelativeTrace_eq_primeGamma
    {z : ℂ} (hz : 1 < (1 / 2 + z * Complex.I).re) :
    deningerArithmeticJetRegularizedRelativeTrace z =
      primeArchSourceRelativeTrace z := by
  rw [deningerArithmeticJetRegularizedRelativeTrace_eq_divisor
    (XiC_ne_zero_of_admissible
      (XiExplicitAdmissible_of_one_lt_re hz))]
  exact deningerResolventLefschetzTrace_primeSeries hz

end

end RHTower
