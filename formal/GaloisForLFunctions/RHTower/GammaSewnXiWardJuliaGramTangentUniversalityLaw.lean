import GaloisForLFunctions.RHTower.GammaSewnSynchronizedRecoveryContraction

/-!
# Gamma-sewn Xi Ward Julia-Gram tangent universality

Synchronized signed Gamma recovery preserves the complete finite non-diagonal Xi Julia tangent,
not only its common-anchor or boundary column.  Its sole first-order action is multiplication by
squarefree Möbius parity.
-/

open Complex Filter Topology

namespace RHTower

noncomputable section

/-- Recovered positive-aperture slope matrix of the centered Xi Julia cross-defect. -/
def gammaSewnSynchronizedRecoveredXiWardJuliaSlopeMatrix {n : ℕ}
    (nu : Nat.Primes → ℝ) (P : Finset Nat.Primes)
    (node : Fin n → ℂ) (x : ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  fun i j =>
    (gammaSewnSynchronizedSignedRecoveryAmplitude nu x P *
        xiWardJuliaCrossDefect (node i) (node j) (x : ℂ)) / (x : ℂ)

/-- **Recovered two-node Julia tangent law.**  Every continued Xi Julia cross-cell keeps its
Cauchy-kernel tangent under synchronized Gamma recovery, up to the squarefree parity. -/
theorem gammaSewnSynchronizedSignedRecovery_preserves_xiWardJuliaCrossTangent
    (nu : Nat.Primes → ℝ) (hnu : ∀ p, 0 < nu p)
    (P : Finset Nat.Primes) {z w : ℂ}
    (hzdom : CCMContinuedCauchyDomain z)
    (hwdom : CCMContinuedCauchyDomain w)
    (hzw : z ≠ (starRingEnd ℂ) w) :
    Tendsto
      (fun x : ℝ =>
        (gammaSewnSynchronizedSignedRecoveryAmplitude nu x P *
            xiWardJuliaCrossDefect z w (x : ℂ)) / (x : ℂ))
      (𝓝[>] (0 : ℝ))
      (𝓝 (((((-1 : ℝ) ^ P.card : ℝ) : ℂ)) *
        ccmContinuedCauchyKernel z w)) := by
  have hzXi : XiC z ≠ 0 :=
    XiC_ne_zero_of_continuedPrimeArch_domain
      hzdom.1 hzdom.2.1 hzdom.2.2.1
  have hwXi : XiC ((starRingEnd ℂ) w) ≠ 0 :=
    XiC_ne_zero_of_continuedPrimeArch_domain
      hwdom.2.2.2.1 hwdom.2.2.2.2.1 hwdom.2.2.2.2.2
  have hzero : xiWardJuliaCrossDefect z w 0 = 0 := by
    simp [xiWardJuliaCrossDefect, xiWardSourcePhaseCrossRatio_zero, hzXi, hwXi]
  have hderiv :=
    hasDerivAt_xiWardJuliaCrossDefect_zero_eq_continuedCauchyKernel
      hzdom hwdom hzw
  have hjet :
      Tendsto
        (fun x : ℝ =>
          (xiWardJuliaCrossDefect z w (x : ℂ) - 0) / (x : ℂ))
        (𝓝[>] (0 : ℝ)) (𝓝 (ccmContinuedCauchyKernel z w)) := by
    simpa [hzero] using hasDerivAt_tendsto_real_slope_zero_right hderiv
  have hrecovered :=
    gammaSewnSynchronizedSignedRecovery_preserves_complex_boundary_tangent
      nu hnu P
      (fun x : ℝ => xiWardJuliaCrossDefect z w (x : ℂ))
      0 (ccmContinuedCauchyKernel z w) hjet
  simpa using hrecovered

/-- **Finite Julia-Gram tangent universality law.**  One synchronized recovery factor preserves
all entries of every finite continued Xi Cauchy-Gram tangent simultaneously, changing only its
global Möbius orientation. -/
theorem tendsto_gammaSewnSynchronizedRecoveredXiWardJuliaSlopeMatrix
    {n : ℕ} (nu : Nat.Primes → ℝ) (hnu : ∀ p, 0 < nu p)
    (P : Finset Nat.Primes) (node : Fin n → ℂ)
    (hdom : ∀ i, CCMContinuedCauchyDomain (node i))
    (hsep : ∀ i j, node i ≠ (starRingEnd ℂ) (node j)) :
    Tendsto
      (gammaSewnSynchronizedRecoveredXiWardJuliaSlopeMatrix nu P node)
      (𝓝[>] (0 : ℝ))
      (𝓝 (fun i j =>
        ((((-1 : ℝ) ^ P.card : ℝ) : ℂ)) *
          ccmContinuedCauchyKernel (node i) (node j))) := by
  apply tendsto_pi_nhds.mpr
  intro i
  apply tendsto_pi_nhds.mpr
  intro j
  exact
    gammaSewnSynchronizedSignedRecovery_preserves_xiWardJuliaCrossTangent
      nu hnu P (hdom i) (hdom j) (hsep i j)

end

end RHTower
