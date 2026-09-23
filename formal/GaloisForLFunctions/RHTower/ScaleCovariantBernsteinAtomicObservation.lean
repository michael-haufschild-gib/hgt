import GaloisForLFunctions.RHTower.ScaleCovariantBernsteinPurityChart
import GaloisForLFunctions.RHTower.AtomicBernsteinMaximalPacketAsymptotic
import GaloisForLFunctions.HTGeometry.ScaledCentralBinomialAbelTransfer

/-!
# Atomic realization of the scale-covariant Bernstein observation field

The finite scale-purity polynomial and the infinite atomic Bernstein packet are two descriptions
of the same observable.  This file supplies the generic bridge: whenever a real moment sequence
is represented by an absolutely summable bounded complex atomic source, evaluation at inverse
scale `R⁻¹` is exactly the square energy of the atomic packet with nodes scaled by `R⁻¹`.
-/

open Complex Filter Topology
open scoped BigOperators Polynomial Real
open Polynomial

namespace RHTower

noncomputable section

open HTGeometry

/-- Power moments of a complex atomic source. -/
def atomicPowerMoment {I : Type*} (c z : I → ℂ) (n : ℕ) : ℂ :=
  ∑' i : I, c i * z i ^ n

/-- Evaluation of a polynomial against a complex atomic source. -/
def atomicPolynomialMoment {I : Type*}
    (c z : I → ℂ) (p : Polynomial ℝ) : ℂ :=
  ∑' i : I, c i * evalRealPolynomial p (z i)

/-- The scale-covariant finite Bernstein observation. -/
def scaleCovariantBernsteinObservation
    (m : ℕ → ℝ) (N : ℕ) (R : ℝ) : ℝ :=
  (bernsteinScalePurityPolynomial m N).eval R⁻¹

/-- Abel generating field of the scale-covariant observations. -/
def scaleCovariantBernsteinAbelField
    (m : ℕ → ℝ) (R t : ℝ) : ℝ :=
  ∑' N : ℕ, scaleCovariantBernsteinObservation m N R * t ^ N

/-- Atomic nodes after inverse radial scaling. -/
def inverseScaleAtomicNode {I : Type*} (z : I → ℂ) (R : ℝ) : I → ℂ :=
  fun i => (R⁻¹ : ℂ) * z i

@[simp] theorem inverseScaleAtomicNode_eq_div
    {I : Type*} (z : I → ℂ) (R : ℝ) (i : I) :
    inverseScaleAtomicNode z R i = z i / (R : ℂ) := by
  rw [inverseScaleAtomicNode, div_eq_mul_inv]
  ring

/-- Bounded atomic weights have absolutely summable power moments. -/
theorem summable_atomicPowerMoment_term
    {I : Type*} {c z : I → ℂ} (hc : Summable c)
    {M : ℝ} (hbound : ∀ i, ‖z i‖ ≤ M) (n : ℕ) :
    Summable (fun i : I => c i * z i ^ n) := by
  apply (hc.norm.mul_right (max M 0 ^ n)).of_norm_bounded
  intro i
  rw [norm_mul, norm_pow]
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (norm_nonneg _) ((hbound i).trans (le_max_left _ _)) n)
    (norm_nonneg _)

/-- A bounded atomic source is summable against every real polynomial. -/
theorem summable_atomicPolynomialMoment_term
    {I : Type*} {c z : I → ℂ} (hc : Summable c)
    {M : ℝ} (hbound : ∀ i, ‖z i‖ ≤ M) (p : Polynomial ℝ) :
    Summable (fun i : I => c i * evalRealPolynomial p (z i)) := by
  let A : ℝ := evalRealPolynomialNormBound p (max M 0)
  apply (hc.norm.mul_right A).of_norm_bounded
  intro i
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left
    (norm_evalRealPolynomial_le p ((hbound i).trans (le_max_left _ _)))
    (norm_nonneg _)

/-- A real moment representation extends from monomials to the complete polynomial functional. -/
theorem ofReal_momentFunctional_eq_atomicPolynomialMoment
    {I : Type*} {c z : I → ℂ} (hc : Summable c)
    {M : ℝ} (hbound : ∀ i, ‖z i‖ ≤ M)
    {m : ℕ → ℝ}
    (hmoment : ∀ n, (m n : ℂ) = atomicPowerMoment c z n)
    (p : Polynomial ℝ) :
    (momentFunctional m p : ℂ) = atomicPolynomialMoment c z p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      have hsp := summable_atomicPolynomialMoment_term hc hbound p
      have hsq := summable_atomicPolynomialMoment_term hc hbound q
      rw [momentFunctional_add]
      push_cast
      rw [hp, hq, atomicPolynomialMoment, atomicPolynomialMoment,
        atomicPolynomialMoment, ← hsp.tsum_add hsq]
      apply tsum_congr
      intro i
      simp only [evalRealPolynomial]
      rw [Polynomial.map_add, Polynomial.eval_add]
      ring
  | monomial n a =>
      rw [← Polynomial.C_mul_X_pow_eq_monomial,
        ← Polynomial.smul_eq_C_mul, momentFunctional_smul,
        momentFunctional_X_pow]
      push_cast
      rw [hmoment n, atomicPowerMoment, atomicPolynomialMoment,
        ← tsum_mul_left]
      apply tsum_congr
      intro i
      simp only [evalRealPolynomial]
      rw [Polynomial.smul_eq_C_mul, Polynomial.map_mul, Polynomial.map_C,
        Polynomial.map_pow, Polynomial.map_X, Polynomial.eval_mul,
        Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
      rw [Complex.coe_algebraMap]
      ring

/-- The real Bernstein coefficient vector is the atomic Bernstein packet whenever their moments
agree. -/
theorem ofReal_bernsteinCoefficient_eq_atomicBernsteinCoefficient
    {I : Type*} {c z : I → ℂ} (hc : Summable c)
    {M : ℝ} (hbound : ∀ i, ‖z i‖ ≤ M)
    {m : ℕ → ℝ}
    (hmoment : ∀ n, (m n : ℂ) = atomicPowerMoment c z n)
    (N k : ℕ) :
    (bernsteinCoefficient m N k : ℂ) =
      atomicBernsteinCoefficient c z N k := by
  rw [bernsteinCoefficient, atomicBernsteinCoefficient]
  rw [ofReal_momentFunctional_eq_atomicPolynomialMoment hc hbound hmoment,
    atomicPolynomialMoment]
  apply tsum_congr
  intro i
  rw [atomicBernsteinCoefficientTerm, bernsteinPolynomial]
  simp only [evalRealPolynomial, Polynomial.map_mul, Polynomial.map_natCast,
    Polynomial.map_pow, Polynomial.map_X, Polynomial.map_sub, Polynomial.map_one,
    Polynomial.eval_mul, Polynomial.eval_natCast, Polynomial.eval_pow,
    Polynomial.eval_X, Polynomial.eval_sub, Polynomial.eval_one]
  ring

/-- Inverse scaling commutes exactly with atomic power moments. -/
theorem atomicPowerMoment_inverseScaleAtomicNode
    {I : Type*} (c z : I → ℂ) (R : ℝ) (n : ℕ) :
    atomicPowerMoment c (inverseScaleAtomicNode z R) n =
      (R⁻¹ : ℂ) ^ n * atomicPowerMoment c z n := by
  rw [atomicPowerMoment, atomicPowerMoment, ← tsum_mul_left]
  apply tsum_congr
  intro i
  rw [inverseScaleAtomicNode, mul_pow]
  ring

/-- A represented real moment sequence remains represented after inverse scaling. -/
theorem ofReal_inverseScaledMoment_eq_atomicPowerMoment
    {I : Type*} {c z : I → ℂ} {m : ℕ → ℝ}
    (hmoment : ∀ n, (m n : ℂ) = atomicPowerMoment c z n)
    (R : ℝ) (n : ℕ) :
    ((R⁻¹ ^ n * m n : ℝ) : ℂ) =
      atomicPowerMoment c (inverseScaleAtomicNode z R) n := by
  rw [atomicPowerMoment_inverseScaleAtomicNode, ← hmoment n]
  push_cast
  rfl

/-- Literal realization theorem: the finite observation at scale `R` is the square energy of the
same atomic source after inverse radial scaling. -/
theorem scaleCovariantBernsteinObservation_eq_atomicPacketSquareEnergy
    {I : Type*} {c z : I → ℂ} (hc : Summable c)
    {M : ℝ} (hbound : ∀ i, ‖z i‖ ≤ M)
    {m : ℕ → ℝ}
    (hmoment : ∀ n, (m n : ℂ) = atomicPowerMoment c z n)
    {R : ℝ} (hR : 0 < R) (N : ℕ) :
    scaleCovariantBernsteinObservation m N R =
      atomicBernsteinPacketSquareEnergy c (inverseScaleAtomicNode z R) N := by
  have hscaledBound : ∀ i, ‖inverseScaleAtomicNode z R i‖ ≤ M / R := by
    intro i
    rw [inverseScaleAtomicNode, norm_mul, norm_inv, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hR]
    simpa only [div_eq_mul_inv, mul_comm] using
      mul_le_mul_of_nonneg_right (hbound i) (inv_nonneg.mpr hR.le)
  rw [scaleCovariantBernsteinObservation,
    eval_bernsteinScalePurityPolynomial, bernsteinCoefficientPurity,
    atomicBernsteinPacketSquareEnergy, finiteComplexPacketSquareEnergy]
  apply Finset.sum_congr rfl
  intro k hk
  have hcoeff := ofReal_bernsteinCoefficient_eq_atomicBernsteinCoefficient
    hc hscaledBound (ofReal_inverseScaledMoment_eq_atomicPowerMoment hmoment R) N k
  rw [atomicBernsteinPacket, ← hcoeff, Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-- Consequently the full Abel field is the Abel sum of the same atomic packet energies. -/
theorem scaleCovariantBernsteinAbelField_eq_atomicPacketSquareEnergy_tsum
    {I : Type*} {c z : I → ℂ} (hc : Summable c)
    {M : ℝ} (hbound : ∀ i, ‖z i‖ ≤ M)
    {m : ℕ → ℝ}
    (hmoment : ∀ n, (m n : ℂ) = atomicPowerMoment c z n)
    {R : ℝ} (hR : 0 < R) (t : ℝ) :
    scaleCovariantBernsteinAbelField m R t =
      ∑' N : ℕ,
        atomicBernsteinPacketSquareEnergy c (inverseScaleAtomicNode z R) N * t ^ N := by
  rw [scaleCovariantBernsteinAbelField]
  apply tsum_congr
  intro N
  rw [scaleCovariantBernsteinObservation_eq_atomicPacketSquareEnergy
    hc hbound hmoment hR]

/-- Generic square-root Abel boundary for the scale-covariant observation field. -/
theorem tendsto_scaleCovariantBernsteinAbelField_of_atomic_halfOrder
    {I : Type*} {c z : I → ℂ} (hc : Summable c)
    {M : ℝ} (hbound : ∀ i, ‖z i‖ ≤ M)
    {m : ℕ → ℝ}
    (hmoment : ∀ n, (m n : ℂ) = atomicPowerMoment c z n)
    {R B L : ℝ} (hR : 0 < R) (hB : 0 < B)
    (hhalf : Tendsto
      (fun N : ℕ => Real.sqrt N *
        atomicBernsteinPacketSquareEnergy c (inverseScaleAtomicNode z R) N /
          (B ^ (2 : ℕ)) ^ N)
      atTop (nhds L)) :
    Tendsto
      (fun t : ℝ => Real.sqrt (1 - B ^ (2 : ℕ) * t) *
        scaleCovariantBernsteinAbelField m R t)
      (nhdsWithin (1 / B ^ (2 : ℕ)) (Set.Ico 0 (1 / B ^ (2 : ℕ))))
      (nhds (Real.sqrt Real.pi * L)) := by
  have hboundary :=
    GaloisForLFunctions.HTGeometry.tendsto_sqrt_scaled_boundary_mul_tsum_of_halfOrder
      hB hhalf
  apply hboundary.congr'
  filter_upwards with t
  rw [scaleCovariantBernsteinAbelField_eq_atomicPacketSquareEnergy_tsum
    hc hbound hmoment hR]

end

end RHTower
