import GaloisForLFunctions.EulerFETransportTheory.ThePrimeCurrentPassesAcrossDyadicWindows

/-!
# Raw-prime passage at inverse-height damping

The lower endpoint of the uniform dyadic-window law gives passage at damping
`1 / im s`. The literal infinite prime sum recovers `-ζ'/ζ` on an interior
high strip supplied by failure of AAL. No counterterm remains.
-/

open Complex Filter Topology RHTower XiAtlasFinitePart

noncomputable section
namespace GaloisForLFunctions.EulerFETransportTheory

/-- Oscillation removes the continuum at inverse-height damping. One Mellin
recursion gains a factor of height before the Gaussian integral is bounded. -/
theorem norm_gaussianContinuum_inverseHeight_le {s : ℂ}
    (hs : 0 < s.re) (ht : 1 ≤ s.im) :
    ‖gaussianIncompleteMellin (1 / s.im) (1 - s)‖ ≤
      1 / s.im + Real.Gamma (3 / 2) * (1 / s.im) ^ (1 / 2 : ℝ) :=
  norm_gaussianContinuum_horizon_le hs ht le_rfl

/-- Failure of AAL supplies an interior high strip on which the raw Gaussian
prime discrepancy recovers its continued finite part at damping `1 / im s`.
No divisor-defined counterterm remains in this limit. -/
theorem not_asymptoticAbscissaLaw_has_countertermFree_highGaussianPassage
    (hnot : ¬ AsymptoticAbscissaLaw) :
    ∃ σ : ℝ, 1 / 2 < σ ∧ σ < 1 ∧ (∃ q : XiZeroCopy, σ < (q.1 : ℂ).re) ∧
      ∀ ε : ℝ, 0 < ε → ∃ T : ℝ, 0 < T ∧ ∀ s : ℂ,
        σ ≤ s.re → s.re ≤ 1 → T ≤ s.im →
        ‖gaussianPrimeContinuumGap s (1 / s.im) -
          (Real.exp (-(1 / s.im)) : ℂ) * (gaussianArchimedeanCurrent s - logDeriv xi s)‖ < ε := by
  obtain ⟨σ, hσ, hσ1, hq, hw⟩ := not_asymptoticAbscissaLaw_has_countertermFree_dyadicGaussianPassage hnot
  refine ⟨σ, hσ, hσ1, hq, fun ε hε => ?_⟩
  obtain ⟨T, hT, hh⟩ := hw ε hε
  refine ⟨T, hT, fun s hs hs1 ht => ?_⟩
  exact hh s.im ht s hs hs1 le_rfl (by linarith)

/-- The literal full von Mangoldt sum has the same high-height passage law.
The continuum and every exceptional Gamma correction have disappeared from
the observable; the strip is supplied by the actual failure of AAL. -/
theorem not_asymptoticAbscissaLaw_has_rawPrime_highGaussianPassage
    (hnot : ¬ AsymptoticAbscissaLaw) :
    ∃ σ : ℝ, 1 / 2 < σ ∧ σ < 1 ∧ (∃ q : XiZeroCopy, σ < (q.1 : ℂ).re) ∧
      ∀ ε : ℝ, 0 < ε → ∃ T : ℝ, 0 < T ∧ ∀ s : ℂ,
        σ ≤ s.re → s.re ≤ 1 → T ≤ s.im →
        ‖gaussianDampedPrimeSum s (1 / s.im) -
          (Real.exp (-(1 / s.im)) : ℂ) * (gaussianArchimedeanCurrent s - logDeriv xi s)‖ < ε := by
  obtain ⟨σ, hσ, hσ1, hq, hw⟩ := not_asymptoticAbscissaLaw_has_rawPrime_dyadicGaussianPassage hnot
  refine ⟨σ, hσ, hσ1, hq, fun ε hε => ?_⟩
  obtain ⟨T, hT, hh⟩ := hw ε hε
  refine ⟨T, hT, fun s hs hs1 ht => ?_⟩
  exact hh s.im ht s hs hs1 le_rfl (by linarith)

/-- The scalar and polar corrections cost only logarithmic height divided by
height on a strip separated from the actual divisor. -/
theorem norm_normalizedGaussianFinitePart_add_logDeriv_le {s : ℂ} {δ : ℝ}
    (hs : 1 / 2 ≤ s.re) (hs1 : s.re ≤ 1) (ht : 4 ≤ s.im)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hsep : ∀ q : XiZeroCopy, δ ≤ ‖xiZero q - s‖) :
    ‖(Real.exp (-(1 / s.im)) : ℂ) *
        (gaussianArchimedeanCurrent s - logDeriv xi s) + logDeriv riemannZeta s‖ ≤
      (logDerivZetaConstant / δ) * (Real.log s.im / s.im) + 1 / s.im :=
  norm_normalizedGaussianFinitePart_horizon_add_logDeriv_le (by linarith) le_rfl
    hs hs1 ht hδ hδ1 hsep

/-- In the actual finite-layer world, inverse-height Gaussian damping recovers
`-ζ'/ζ` uniformly on an interior high strip. The observable and target contain
no divisor, continuum, scalar, or polar counterterm. -/
theorem not_asymptoticAbscissaLaw_has_rawEuler_highGaussianPassage
    (hnot : ¬ AsymptoticAbscissaLaw) :
    ∃ σ : ℝ, 1 / 2 < σ ∧ σ < 1 ∧ (∃ q : XiZeroCopy, σ < (q.1 : ℂ).re) ∧
      ∀ ε : ℝ, 0 < ε → ∃ T : ℝ, 0 < T ∧ ∀ s : ℂ,
        σ ≤ s.re → s.re ≤ 1 → T ≤ s.im →
        ‖gaussianDampedPrimeSum s (1 / s.im) + logDeriv riemannZeta s‖ < ε := by
  obtain ⟨σ, hσ, hσ1, hq, hw⟩ := not_asymptoticAbscissaLaw_has_rawEuler_dyadicGaussianPassage hnot
  refine ⟨σ, hσ, hσ1, hq, fun ε hε => ?_⟩
  obtain ⟨T, hT, hh⟩ := hw ε hε
  refine ⟨T, hT, fun s hs hs1 ht => ?_⟩
  exact hh s.im ht s hs hs1 le_rfl (by linarith)

#print axioms norm_gaussianContinuum_inverseHeight_le
#print axioms not_asymptoticAbscissaLaw_has_countertermFree_highGaussianPassage
#print axioms not_asymptoticAbscissaLaw_has_rawPrime_highGaussianPassage
#print axioms norm_normalizedGaussianFinitePart_add_logDeriv_le
#print axioms not_asymptoticAbscissaLaw_has_rawEuler_highGaussianPassage

end GaloisForLFunctions.EulerFETransportTheory
