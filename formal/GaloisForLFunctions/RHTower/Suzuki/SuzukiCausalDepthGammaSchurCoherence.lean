import GaloisForLFunctions.RHTower.GammaConductorSchurStrictDefiniteness
import GaloisForLFunctions.RHTower.Suzuki.SuzukiValuationDepthLightCoercivity
import GaloisForLFunctions.RHTower.EulerFisherCurvature

/-!
# Strict Gamma coherence of Suzuki causal depth coordinates

Every Suzuki critical causal-depth coordinate carries a positive geometric source amplitude and a
positive half-log prime-power frequency.  Unique factorization makes the complete prime-depth
frequency spectrum simple.

This file composes that actual source spectrum with the mean-and-conductor projected Gamma
covariance.  Every injective finite packet of causal depth coordinates has a strictly positive
definite weighted Gamma Schur Gram.  Thus centered Gamma projection loses no finite arithmetic
source direction, even after the scalar conductor channel has been paid.

No Xi zero, Riemann-hypothesis premise, target positivity assumption, fitted covariance, or
numerical computation is used.  Identification of this faithful Gamma Gram with the concrete
unbounded restricted-Weil/Robin rectangular trace remains open.
-/

noncomputable section

open Complex
open scoped BigOperators Nat Real

namespace RHTower

/-- Positive Gamma frequency of one prime-depth source coordinate. -/
def suzukiCausalDepthGammaFrequency (pe : Nat.Primes × ℕ) : ℝ :=
  Real.log (xiGammaEulerValuationNat pe : ℝ) / 2

/-- Positive geometric amplitude of one actual critical causal-depth coordinate. -/
def suzukiCausalDepthGammaWeight
    (h a : ℝ) (pe : Nat.Primes × ℕ) : ℝ :=
  suzukiCriticalEntryWallEndpointAmplitude h a pe.1 0 *
    suzukiCriticalApertureDepthFusionRadius h a pe.1 ^ pe.2

theorem suzukiCausalDepthGammaFrequency_pos
    (pe : Nat.Primes × ℕ) :
    0 < suzukiCausalDepthGammaFrequency pe := by
  have hpow :
      (1 : ℝ) <
        ((pe.1 : ℝ) ^ (pe.2 + 1)) :=
    one_lt_pow₀ (by exact_mod_cast pe.1.property.one_lt) (by omega)
  rw [suzukiCausalDepthGammaFrequency, xiGammaEulerValuationNat]
  exact div_pos (Real.log_pos (by exact_mod_cast hpow)) (by norm_num)

/-- Unique factorization makes the complete positive Gamma frequency spectrum simple. -/
theorem suzukiCausalDepthGammaFrequency_injective :
    Function.Injective suzukiCausalDepthGammaFrequency := by
  intro x y hxy
  apply eulerPrimePowerNat_injective
  have hlog :
      Real.log (eulerPrimePowerNat x : ℝ) =
        Real.log (eulerPrimePowerNat y : ℝ) := by
    change
      Real.log (xiGammaEulerValuationNat x : ℝ) =
        Real.log (xiGammaEulerValuationNat y : ℝ)
    unfold suzukiCausalDepthGammaFrequency at hxy
    linarith
  have hxpos : 0 < (eulerPrimePowerNat x : ℝ) := by
    exact_mod_cast pow_pos x.1.property.pos (x.2 + 1)
  have hypos : 0 < (eulerPrimePowerNat y : ℝ) := by
    exact_mod_cast pow_pos y.1.property.pos (y.2 + 1)
  exact_mod_cast Real.strictMonoOn_log.injOn
    (Set.mem_Ioi.mpr hxpos) (Set.mem_Ioi.mpr hypos) hlog

theorem suzukiCausalDepthGammaWeight_pos
    {h a : ℝ} (hh : 0 < h) (ha : 0 < a)
    (pe : Nat.Primes × ℕ) :
    0 < suzukiCausalDepthGammaWeight h a pe := by
  exact mul_pos
    (suzukiCriticalEntryWallEndpointAmplitude_zero_pos hh ha pe.1)
    (pow_pos (suzukiCriticalApertureDepthFusionRadius_pos h a pe.1) pe.2)

/-- The Gamma weight is the literal norm amplitude of the actual critical wall atom. -/
theorem normSq_suzukiCriticalApertureBoundaryAtom_eq_causalDepthGammaWeight_sq
    (h a t : ℝ) (pe : Nat.Primes × ℕ) :
    Complex.normSq
        (suzukiCriticalApertureBoundaryAtom h a t pe.1 pe.2) =
      suzukiCausalDepthGammaWeight h a pe ^ (2 : ℕ) := by
  rw [normSq_suzukiCriticalApertureBoundaryAtom_eq_geometricDepth]
  unfold suzukiCausalDepthGammaWeight
  rw [mul_pow, ← pow_mul, ← pow_mul]
  congr 2
  omega

/-- Actual source-weighted Gamma Schur kernel on causal prime-depth coordinates. -/
def suzukiCausalDepthGammaSchurKernel
    (h a : ℝ) (x y : Nat.Primes × ℕ) : ℝ :=
  suzukiCausalDepthGammaWeight h a x *
    gammaConductorModeSchurResidual
      (suzukiCausalDepthGammaFrequency x)
      (suzukiCausalDepthGammaFrequency y) *
    suzukiCausalDepthGammaWeight h a y

theorem suzukiCausalDepthGammaSchurKernel_comm
    (h a : ℝ) (x y : Nat.Primes × ℕ) :
    suzukiCausalDepthGammaSchurKernel h a x y =
      suzukiCausalDepthGammaSchurKernel h a y x := by
  unfold suzukiCausalDepthGammaSchurKernel
  rw [gammaConductorModeSchurResidual_comm
    (suzukiCausalDepthGammaFrequency_pos x)
    (suzukiCausalDepthGammaFrequency_pos y)]
  ring

/-- **Finite causal-depth Gamma faithfulness.**  Every injective finite packet of actual Suzuki
prime-depth source coordinates remains strictly positive definite after mean and conductor
projection. -/
theorem suzukiCausalDepthGammaSchurKernel_matrix_posDef
    {n : ℕ} {h a : ℝ} (hh : 0 < h) (ha : 0 < a)
    (z : Fin n → Nat.Primes × ℕ) (hz : Function.Injective z) :
    Matrix.PosDef
      (fun i j : Fin n => suzukiCausalDepthGammaSchurKernel h a (z i) (z j)) := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · ext i j
    simp only [Matrix.conjTranspose_apply, star_trivial]
    exact suzukiCausalDepthGammaSchurKernel_comm h a (z j) (z i)
  · intro c hc
    let freq : Fin n → ℝ := fun i => suzukiCausalDepthGammaFrequency (z i)
    let d : Fin n → ℝ := fun i => suzukiCausalDepthGammaWeight h a (z i) * c i
    have hfreqPos : ∀ i, 0 < freq i :=
      fun i => suzukiCausalDepthGammaFrequency_pos (z i)
    have hfreqInj : Function.Injective freq :=
      suzukiCausalDepthGammaFrequency_injective.comp hz
    have hd : d ≠ 0 := by
      intro hd
      apply hc
      funext i
      have hi := congrFun hd i
      dsimp [d] at hi
      exact (mul_eq_zero.mp hi).resolve_left
        (suzukiCausalDepthGammaWeight_pos hh ha (z i)).ne'
    have hpos :=
      gammaConductorModeSchurResidual_quadratic_pos freq d hfreqPos hfreqInj hd
    simpa [dotProduct, Matrix.mulVec, Finset.mul_sum,
      suzukiCausalDepthGammaSchurKernel, freq, d,
      mul_assoc, mul_comm, mul_left_comm] using hpos

end RHTower
