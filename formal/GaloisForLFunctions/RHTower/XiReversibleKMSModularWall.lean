import GaloisForLFunctions.HTGeometry.ConstitutiveInvariantPositivityKMSWall
import GaloisForLFunctions.RHTower.XiSelectedBilateralPositiveSourceReceiver

/-!
# Xi reversible-KMS modular wall

The genuine Meyer/Gamma modular correction of one Xi divisor,
`Delta_p(rho) = ‖chi_p(rho)‖²`, can be used as the exchange eigenvalue of a one-sided KMS
history.  The KMS identity then assigns its depth-`k` defect layer the exact geometric weight
`(1 - Delta_p(rho)) Delta_p(rho)^k`.  On the strict-right half of the critical strip this is a
genuine positive geometric law because `0 < Delta_p(rho) < 1`.

The same exchange law cannot survive a reversible descent.  If the history generator acquires a
two-sided inverse, normalization alone forces `Delta_p(rho) = 1`, hence `Re rho = 1/2`.  No
positivity, faithfulness, spectral theorem, or post-selected bilateral receiver is assumed in
this final implication.  A single common reversible KMS realization of all Xi divisor modes
therefore proves RH.

This is a falsifiable bridge, not an RH proof.  Its unresolved producer is arithmetic: construct
the reversible source completion and prove that the actual Meyer/Gamma exchange law descends to
it.  The theorem below shows exactly why an off-line divisor can occur only in the irreversible
Toeplitz sector of any such realization.
-/

namespace RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

/-- A strict-right Xi modular correction is a genuine positive-temperature geometric ratio. -/
theorem xiPrimeModularWeight_lt_one_of_half_lt_re
    (rho : XiDivisorSupport) (p : Nat.Primes)
    (hrho : 1 / 2 < (rho : ℂ).re) :
    deningerMeyerXiPrimeGammaModularWeight rho p < 1 := by
  rw [deningerMeyerXiPrimeGammaModularWeight,
    norm_deningerMeyerXiPrimeGammaCharacter_eq_halfGammaClock,
    pow_two, ← Real.exp_add]
  apply (Real.exp_lt_one_iff).2
  have hpLog : 0 < Real.log (p : ℝ) := by
    apply Real.log_pos
    exact_mod_cast p.2.one_lt
  have hrate : 0 < primeDepthBVWoldXiCenteredRate rho := by
    rw [primeDepthBVWoldXiCenteredRate]
    linarith
  have hprod : 0 < Real.log (p : ℝ) * primeDepthBVWoldXiCenteredRate rho :=
    mul_pos hpLog hrate
  linarith

/-- On a strict-right Xi mode every geometric history-layer coefficient is strictly positive. -/
theorem xiPrimeModularHistoryLayerWeight_pos
    (rho : XiDivisorSupport) (p : Nat.Primes)
    (hrho : 1 / 2 < (rho : ℂ).re) (k : ℕ) :
    0 < (1 - deningerMeyerXiPrimeGammaModularWeight rho p) *
      deningerMeyerXiPrimeGammaModularWeight rho p ^ k := by
  exact mul_pos
    (sub_pos.mpr (xiPrimeModularWeight_lt_one_of_half_lt_re rho p hrho))
    (pow_pos (deningerMeyerXiPrimeGammaModularWeight_pos rho p) k)

/-- The actual Xi modular correction is exactly the ratio of the KMS history-layer law. -/
theorem xiPrimeKMSHistoryLayerMass
    {A : Type*} [Ring A] [Algebra ℂ A]
    (phi : A →ₗ[ℂ] ℂ) (sigma : A →ₐ[ℂ] A)
    (rho : XiDivisorSupport) (p : Nat.Primes)
    {v w : A}
    (hexch : ∀ a b : A, phi (a * b) = phi (b * sigma a))
    (henergy : sigma v =
      ((deningerMeyerXiPrimeGammaModularWeight rho p : ℝ) : ℂ) • v)
    (hleft : w * v = 1) (hnormalized : phi 1 = 1) (k : ℕ) :
    phi (v ^ k * (1 - v * w) * w ^ k) =
      (1 - (deningerMeyerXiPrimeGammaModularWeight rho p : ℂ)) *
        (deningerMeyerXiPrimeGammaModularWeight rho p : ℂ) ^ k := by
  exact kms_layer_mass phi sigma hexch henergy hleft hnormalized k

/-- Reversible descent of the actual Xi KMS mode forces critical-line placement. -/
theorem xiPrimeReversibleKMS_forces_re_eq_half
    {A : Type*} [Ring A] [Algebra ℂ A]
    (phi : A →ₗ[ℂ] ℂ) (sigma : A →ₐ[ℂ] A)
    (rho : XiDivisorSupport) (p : Nat.Primes)
    {u w : A}
    (hexch : ∀ a b : A, phi (a * b) = phi (b * sigma a))
    (henergy : sigma u =
      ((deningerMeyerXiPrimeGammaModularWeight rho p : ℝ) : ℂ) • u)
    (hleft : w * u = 1) (hright : u * w = 1)
    (hnormalized : phi 1 = 1) :
    (rho : ℂ).re = 1 / 2 := by
  have hweightComplex :
      ((deningerMeyerXiPrimeGammaModularWeight rho p : ℝ) : ℂ) = 1 :=
    kms_forces_q_eq_one phi sigma hexch henergy hleft hright hnormalized
  have hweight : deningerMeyerXiPrimeGammaModularWeight rho p = 1 := by
    exact_mod_cast hweightComplex
  have hnorm : ‖deningerMeyerXiPrimeGammaCharacter rho p‖ = 1 := by
    rw [deningerMeyerXiPrimeGammaModularWeight] at hweight
    nlinarith [norm_nonneg (deningerMeyerXiPrimeGammaCharacter rho p)]
  rw [deningerMeyerXiPrimeGammaCharacter_eq_deltaS] at hnorm
  exact (norm_deltaS_eq_one_iff p.2.two_le (rho : ℂ)).1 hnorm

/-- Off the critical line, a left-invertible Xi KMS history generator cannot become invertible. -/
theorem xiPrimeKMSHistory_not_reversible_of_re_ne_half
    {A : Type*} [Ring A] [Algebra ℂ A]
    (phi : A →ₗ[ℂ] ℂ) (sigma : A →ₐ[ℂ] A)
    (rho : XiDivisorSupport) (p : Nat.Primes)
    {u w : A}
    (hoff : (rho : ℂ).re ≠ 1 / 2)
    (hexch : ∀ a b : A, phi (a * b) = phi (b * sigma a))
    (henergy : sigma u =
      ((deningerMeyerXiPrimeGammaModularWeight rho p : ℝ) : ℂ) • u)
    (hleft : w * u = 1) (hnormalized : phi 1 = 1) :
    u * w ≠ 1 := by
  intro hright
  exact hoff (xiPrimeReversibleKMS_forces_re_eq_half phi sigma rho p
    hexch henergy hleft hright hnormalized)

/-- A common source algebra realizing every actual Xi mode reversibly with its arithmetic KMS
exchange eigenvalue proves RH. -/
theorem riemannHypothesis_of_globalXiPrimeReversibleKMS
    {A : Type*} [Ring A] [Algebra ℂ A]
    (phi : A →ₗ[ℂ] ℂ) (sigma : A →ₐ[ℂ] A)
    (p : Nat.Primes) (u w : XiDivisorSupport → A)
    (hexch : ∀ a b : A, phi (a * b) = phi (b * sigma a))
    (henergy : ∀ rho, sigma (u rho) =
      ((deningerMeyerXiPrimeGammaModularWeight rho p : ℝ) : ℂ) • u rho)
    (hleft : ∀ rho, w rho * u rho = 1)
    (hright : ∀ rho, u rho * w rho = 1)
    (hnormalized : phi 1 = 1) : RiemannHypothesis := by
  apply riemannHypothesis_of_forall_xiDivisorSupport_re_eq_half
  intro rho
  exact xiPrimeReversibleKMS_forces_re_eq_half phi sigma rho p hexch
    (henergy rho) (hleft rho) (hright rho) hnormalized

end

end RHTower
