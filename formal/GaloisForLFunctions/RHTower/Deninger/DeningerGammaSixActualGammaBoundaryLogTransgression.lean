import GaloisForLFunctions.RHTower.Deninger.DeningerGammaSixLogarithmicWoldJordanTransgression
import GaloisForLFunctions.RHTower.Deninger.DeningerCalderonWittGammaCoPoissonHodgeBoundaryComparison

/-!
# Actual Gamma/co-Poisson realization of the Gamma-six logarithmic Wold transgression

The logarithmic Gamma-six shell primitive is not merely an abstract differentiated diagonal.
After the forced half-density countertransport, it is exactly the actual common-test
Gamma/co-Poisson exterior on the equally deep ordered cells `(2,m-1)` and `(3,m-1)`.

The comparison retains both prime labels, valuation depth, the canonical Calderon--Witt Green
witness, and the boundary common test.  Its Wold coface is therefore the existing weak principal
source class.  No Xi divisor, zero-location statement, target compactness, or RH hypothesis enters.
-/

open Complex Real

namespace RHTower

noncomputable section

/-- Positive oriented `(2,3)` exterior volume before depth and half-density factors. -/
def deningerGammaSixTwoThreeExteriorVolume : ℝ :=
  Real.log 2 * Real.log 3 * (Real.log 3 - Real.log 2) / 2

theorem deningerGammaSixTwoThreeExteriorVolume_pos :
    0 < deningerGammaSixTwoThreeExteriorVolume := by
  unfold deningerGammaSixTwoThreeExteriorVolume
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have h23 : Real.log 2 < Real.log 3 := Real.strictMonoOn_log
    (Set.mem_Ioi.mpr (by norm_num)) (Set.mem_Ioi.mpr (by norm_num)) (by norm_num)
  positivity

theorem deningerGammaSixTwoThreeExteriorVolume_ne_zero :
    deningerGammaSixTwoThreeExteriorVolume ≠ 0 :=
  deningerGammaSixTwoThreeExteriorVolume_pos.ne'

/-- Actual critical modular exterior on equal `(2,3)` valuation depths. -/
def deningerGammaSixTwoThreeEqualDepthCriticalExterior
    (m : MobiusHonestDepth) : ℝ :=
  xiGammaEulerPrimitiveModularExterior 0
    ((⟨2, by norm_num⟩ : Nat.Primes), (m : ℕ) - 1)
    ((⟨3, by norm_num⟩ : Nat.Primes), (m : ℕ) - 1)

/-- Exact place/depth normal form of the equal-depth Gamma/co-Poisson exterior. -/
theorem deningerGammaSixTwoThreeEqualDepthCriticalExterior_eq
    (m : MobiusHonestDepth) :
    deningerGammaSixTwoThreeEqualDepthCriticalExterior m =
      -(m : ℝ) * deningerGammaSixTwoThreeExteriorVolume *
        deningerGammaSixHalfWeight m := by
  have hm : (m : ℕ) - 1 + 1 = (m : ℕ) := by omega
  have hlog6 : Real.log 6 = Real.log 2 + Real.log 3 := by
    rw [show (6 : ℝ) = 2 * 3 by norm_num,
      Real.log_mul (by norm_num) (by norm_num)]
  have hhalf : deningerGammaSixHalfWeight m =
      Real.exp (-((m : ℝ) / 2) * Real.log 6) := by
    rw [deningerGammaSixHalfWeight, Real.rpow_def_of_pos (by norm_num)]
    congr 1
    ring
  have hmR : (((m : ℕ) - 1 : ℕ) : ℝ) + 1 = (m : ℝ) := by
    exact_mod_cast hm
  rw [deningerGammaSixTwoThreeEqualDepthCriticalExterior,
    xiGammaEulerPrimitiveModularExterior,
    xiGammaEulerPrimitiveModularCurrent_explicit,
    xiGammaEulerPrimitiveModularCurrent_explicit]
  norm_num only [zero_add]
  rw [xiGammaEulerValuationNat, xiGammaEulerValuationNat]
  norm_num only [Nat.cast_pow, Nat.cast_ofNat]
  rw [Real.log_pow, Real.log_pow, hm]
  rw [xiGammaEulerBoundaryHalfHeight, xiGammaEulerBoundaryHalfHeight]
  rw [hmR]
  norm_num only [Nat.cast_ofNat]
  calc
    Real.log 2 * Real.exp (-(1 / 2) * ((m : ℝ) * Real.log 2)) *
          (Real.log 3 * Real.exp (-(1 / 2) * ((m : ℝ) * Real.log 3))) *
          ((m : ℝ) / 2 * Real.log 2 - (m : ℝ) / 2 * Real.log 3) =
        (Real.log 2 * Real.log 3 *
          ((m : ℝ) / 2 * Real.log 2 - (m : ℝ) / 2 * Real.log 3)) *
          (Real.exp (-(1 / 2) * ((m : ℝ) * Real.log 2)) *
            Real.exp (-(1 / 2) * ((m : ℝ) * Real.log 3))) := by ring
    _ = (Real.log 2 * Real.log 3 *
          ((m : ℝ) / 2 * Real.log 2 - (m : ℝ) / 2 * Real.log 3)) *
          Real.exp (-(1 / 2) * ((m : ℝ) * Real.log 2) +
            -(1 / 2) * ((m : ℝ) * Real.log 3)) := by rw [Real.exp_add]
    _ = -(m : ℝ) * deningerGammaSixTwoThreeExteriorVolume *
          deningerGammaSixHalfWeight m := by
      rw [hhalf, hlog6]
      unfold deningerGammaSixTwoThreeExteriorVolume
      ring_nf

/-- The Gamma-six logarithmic shell is the normalized actual critical `(2,3)` exterior after
the forced second half-density factor. -/
theorem deningerGammaSixShellLogWeight_eq_gammaBoundary
    (m : MobiusHonestDepth) :
    deningerGammaSixShellLogWeight (m : ℕ) =
      -(Real.log 6 / deningerGammaSixTwoThreeExteriorVolume) *
        deningerGammaSixHalfWeight m *
          deningerGammaSixTwoThreeEqualDepthCriticalExterior m := by
  rw [deningerGammaSixTwoThreeEqualDepthCriticalExterior_eq]
  rw [deningerGammaSixShellLogWeight]
  rw [show -(Real.log 6 / deningerGammaSixTwoThreeExteriorVolume) *
        deningerGammaSixHalfWeight m *
          (-((m : ℝ)) * deningerGammaSixTwoThreeExteriorVolume *
            deningerGammaSixHalfWeight m) =
      ((m : ℝ) * Real.log 6) *
        (deningerGammaSixHalfWeight m * deningerGammaSixHalfWeight m) by
      rw [div_eq_mul_inv]
      calc
        -(Real.log 6 * deningerGammaSixTwoThreeExteriorVolume⁻¹) *
              deningerGammaSixHalfWeight m *
              (-((m : ℝ)) * deningerGammaSixTwoThreeExteriorVolume *
                deningerGammaSixHalfWeight m) =
            ((m : ℝ) * Real.log 6) *
              (deningerGammaSixTwoThreeExteriorVolume⁻¹ *
                deningerGammaSixTwoThreeExteriorVolume) *
              (deningerGammaSixHalfWeight m *
                deningerGammaSixHalfWeight m) := by ring
        _ = ((m : ℝ) * Real.log 6) *
              (deningerGammaSixHalfWeight m *
                deningerGammaSixHalfWeight m) := by
          rw [inv_mul_cancel₀ deningerGammaSixTwoThreeExteriorVolume_ne_zero]
          ring]
  rw [deningerGammaSixHalfWeight_sq]

/-- Actual oriented common-test boundary evaluation on the canonical equal-depth `(2,3)`
Calderon--Witt Green witness. -/
def deningerGammaSixTwoThreeEqualDepthActualBoundary
    (m : MobiusHonestDepth) : ℂ :=
  let p : Nat.Primes := ⟨2, by norm_num⟩
  let q : Nat.Primes := ⟨3, by norm_num⟩
  let hpq : p ≠ q := by
    intro h
    have hv := congrArg Subtype.val h
    norm_num at hv
  let e := (m : ℕ) - 1
  (deningerCalderonWittGammaBoundaryVectorOrientation q
      (deningerCalderonWittGammaPolarizedVectorTransport 0
        (deningerCalderonWittCrossPrimeGammaWitness hpq)
        p q e e)).1
    (xiGammaEulerPrimitivePolarizedPairAction (p, e) (q, e))

/-- The scalar in the shell formula is literally the actual Gamma/co-Poisson boundary transport,
not a fitted replacement coefficient. -/
theorem deningerGammaSixTwoThreeEqualDepthActualBoundary_eq
    (m : MobiusHonestDepth) :
    deningerGammaSixTwoThreeEqualDepthActualBoundary m =
      (deningerGammaSixTwoThreeEqualDepthCriticalExterior m : ℂ) := by
  rw [deningerGammaSixTwoThreeEqualDepthActualBoundary]
  rw [
    deningerCalderonWittGammaPolarizedVectorTransport_crossPrime_orientation_eq_coPoisson]
  rw [xiGammaEulerPrimitiveGammaCoPoissonModularExterior_eq]
  rfl

/-- Shell-coordinate weight reconstructed directly from actual place/depth boundary evaluations. -/
def deningerGammaSixActualGammaBoundaryLogWeight (n : ℕ) : ℝ :=
  -(Real.log 6 / deningerGammaSixTwoThreeExteriorVolume) *
    deningerGammaSixHalfWeight (deningerGammaSixShellHonestDepth n) *
      (deningerGammaSixTwoThreeEqualDepthActualBoundary
        (deningerGammaSixShellHonestDepth n)).re

/-- Actual Gamma-boundary reconstruction equals the logarithmic Wold--Jordan weight at every
ordinary shell coordinate. -/
theorem deningerGammaSixActualGammaBoundaryLogWeight_eq (n : ℕ) :
    deningerGammaSixActualGammaBoundaryLogWeight n = deningerGammaSixLogWeight n := by
  rw [deningerGammaSixActualGammaBoundaryLogWeight,
    deningerGammaSixTwoThreeEqualDepthActualBoundary_eq]
  norm_num only [ofReal_re]
  rw [← deningerGammaSixShellLogWeight_eq_gammaBoundary]
  rfl

theorem deningerGammaSixActualGammaBoundaryLogWeight_nonneg (n : ℕ) :
    0 ≤ deningerGammaSixActualGammaBoundaryLogWeight n := by
  rw [deningerGammaSixActualGammaBoundaryLogWeight_eq]
  exact deningerGammaSixShellLogWeight_nonneg _

theorem deningerGammaSixActualGammaBoundaryLogWeight_antitone :
    Antitone deningerGammaSixActualGammaBoundaryLogWeight := by
  intro i j hij
  rw [deningerGammaSixActualGammaBoundaryLogWeight_eq,
    deningerGammaSixActualGammaBoundaryLogWeight_eq]
  exact deningerGammaSixLogWeight_antitone hij

/-- Diagonal logarithmic operator constructed from actual Gamma/co-Poisson boundary evaluations. -/
def deningerGammaSixActualGammaBoundaryLogOperator : EllTwo →L[ℂ] EllTwo :=
  antitoneDiagonalOperator deningerGammaSixActualGammaBoundaryLogWeight
    deningerGammaSixActualGammaBoundaryLogWeight_nonneg
    (fun {_ _} h => deningerGammaSixActualGammaBoundaryLogWeight_antitone h)

@[simp] theorem deningerGammaSixActualGammaBoundaryLogOperator_apply
    (x : EllTwo) (n : ℕ) :
    deningerGammaSixActualGammaBoundaryLogOperator x n =
      ((deningerGammaSixActualGammaBoundaryLogWeight n : ℝ) : ℂ) * x n := by
  simp [deningerGammaSixActualGammaBoundaryLogOperator, antitoneDiagonalOperator]

/-- Operator-level identification: the actual boundary construction is the existing logarithmic
Wold--Jordan primitive. -/
theorem deningerGammaSixActualGammaBoundaryLogOperator_eq :
    deningerGammaSixActualGammaBoundaryLogOperator = deningerGammaSixLogOperator := by
  apply ContinuousLinearMap.ext
  intro x
  apply lp.ext
  funext n
  rw [deningerGammaSixActualGammaBoundaryLogOperator_apply,
    deningerGammaSixLogOperator_apply,
    deningerGammaSixActualGammaBoundaryLogWeight_eq]

/-- The actual place/depth boundary weights obey the exact logarithmic Wold coface law. -/
theorem deningerGammaSixActualGammaBoundaryLogWeight_wold (n : ℕ) :
    deningerGammaSixActualGammaBoundaryLogWeight
          (deningerGammaSixWoldCoordinate n) -
        (1 / 6 : ℝ) * deningerGammaSixActualGammaBoundaryLogWeight n =
      (Real.log 6 / 6) * deningerGammaSixShellEigenvalue n := by
  rw [deningerGammaSixActualGammaBoundaryLogWeight_eq,
    deningerGammaSixActualGammaBoundaryLogWeight_eq]
  exact deningerGammaSixLogWeight_wold n

/-- Tensor lift of the actual Gamma-boundary logarithmic primitive. -/
def deningerGammaSixActualGammaBoundaryPrincipalLogSourceOperator :
    EllTwo →L[ℂ] lp (fun _ : ℕ => DeningerGammaSixTensorSourceL2) 2 :=
  deningerGammaSixLeadingTensorEmbedding ∘L
    deningerGammaSixActualGammaBoundaryLogOperator

theorem deningerGammaSixActualGammaBoundaryPrincipalLogSourceOperator_eq :
    deningerGammaSixActualGammaBoundaryPrincipalLogSourceOperator =
      deningerGammaSixPrincipalLogSourceOperator := by
  rw [deningerGammaSixActualGammaBoundaryPrincipalLogSourceOperator,
    deningerGammaSixActualGammaBoundaryLogOperator_eq]
  rfl

/-- The Wold coface of the actual Gamma-boundary primitive is exactly the weak principal source
class, before any Xi reader or scalar trace. -/
theorem deningerGammaSixWoldCompression_actualGammaBoundaryPrincipalLog :
    deningerGammaSixWoldCompression
        deningerGammaSixActualGammaBoundaryPrincipalLogSourceOperator =
      (1 / 6 : ℂ) • deningerGammaSixActualGammaBoundaryPrincipalLogSourceOperator +
        ((Real.log 6 / 6 : ℝ) : ℂ) •
          deningerGammaSixSourceTensorPrincipalOperator := by
  rw [deningerGammaSixActualGammaBoundaryPrincipalLogSourceOperator_eq]
  exact deningerGammaSixWoldCompression_principalLog

/-- Actual Gamma-boundary primitive retains the same strict ideal obstruction: it lies above weak
Schatten one. -/
theorem deningerGammaSixActualGammaBoundaryLogOperator_not_weak :
    ¬ MemWeakSchattenClass 1 deningerGammaSixActualGammaBoundaryLogOperator := by
  rw [deningerGammaSixActualGammaBoundaryLogOperator_eq]
  exact deningerGammaSixLogOperator_not_weak

end

end RHTower
