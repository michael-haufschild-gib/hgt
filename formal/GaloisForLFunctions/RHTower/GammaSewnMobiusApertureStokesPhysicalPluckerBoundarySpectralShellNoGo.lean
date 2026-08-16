import GaloisForLFunctions.RHTower.GammaSewnMobiusApertureStokesPhysicalPluckerBoundaryAmplificationNoGo

/-!
# Boundary spectral-shell no-go for fourth-depth amplification

P-G101 leaves one apparent canonical survivor for SP-E's unique amplitude-eight normalization:
the unnormalized inverse `(eps + T)⁻¹`.  Resolvent norm alone only says `eps ≤ 1/8`.

This module uses the literal positive rank-one source expansion rather than the coarse resolvent
norm.  Its operator norm is bounded by its nuclear trace mass, already at most `1/50`.  Exact
inverse gain eight simultaneously forces the original physical operator eigenvalue
`1/8 - eps`.  Hence no nonzero amplitude-eight inverse eigenvector exists for
`0 < eps < 21/200`, because then `1/8 - eps > 1/50`.

The full canonical resolvent split is therefore unable to pay the fourth-depth `63/64` trace debt
in any sufficiently small boundary neighborhood.  The surviving construction must change the
operator before inversion or use a genuinely oriented off-diagonal source/co-source shorting;
scalar use of the existing positive physical operator is closed.

No RH premise, Xi-zero computation, numerical estimate, or added axiom enters.
-/

open Set
open scoped InnerProductSpace ContinuousFunctionalCalculus

noncomputable section
namespace RHTower.HedenmalmThetaSource

open GaloisForLFunctions.RHTower

/-- The physical operator norm is bounded by the exact nuclear mass of its positive rank-one
source expansion. -/
theorem norm_gammaSewnCriticalPhysicalPluckerSpectralOperator_le_nuclearTraceMass :
    ‖gammaSewnCriticalPhysicalPluckerSpectralOperator‖ ≤
      gammaSewnCriticalPhysicalPluckerNuclearTraceMass := by
  rw [gammaSewnCriticalPhysicalPluckerSpectralOperator,
    gammaSewnCriticalPhysicalPluckerNuclearTraceMass]
  calc
    ‖∑' idx : (ℕ × ℕ) × Fin 6,
        gammaSewnCriticalPhysicalPluckerPositiveRankOneTerm idx‖ ≤
        ∑' idx : (ℕ × ℕ) × Fin 6,
          ‖gammaSewnCriticalPhysicalPluckerPositiveRankOneTerm idx‖ :=
      norm_tsum_le_tsum_norm
        summable_norm_gammaSewnCriticalPhysicalPluckerPositiveRankOneTerm
    _ = ∑' idx : (ℕ × ℕ) × Fin 6,
        gammaSewnCriticalAdjacentPrime_PluckerBlockWeight idx.1 *
          gammaSewnCriticalAdjacentPrime_PluckerProbability idx.1 idx.2 *
            ‖gammaSewnCriticalPhysicalPluckerCenteredVector idx.1 idx.2‖ ^ 2 := by
      apply tsum_congr
      exact norm_gammaSewnCriticalPhysicalPluckerPositiveRankOneTerm

/-- P-G99's first-trace wall also bounds every physical spectral value by `1/50`. -/
theorem norm_gammaSewnCriticalPhysicalPluckerSpectralOperator_le_one_div_fifty :
    ‖gammaSewnCriticalPhysicalPluckerSpectralOperator‖ ≤ (1 / 50 : ℝ) :=
  norm_gammaSewnCriticalPhysicalPluckerSpectralOperator_le_nuclearTraceMass.trans
    gammaSewnCriticalPhysicalPluckerNuclearTraceMass_le_one_div_fifty

/-- The unnormalized inverse cannot realize amplitude eight in the actual zero-boundary regime.
The exact threshold `21/200 = 1/8 - 1/50` is forced by the source norm budget. -/
theorem gammaSewnCriticalPhysicalPluckerBoundaryInverse_no_amplitude_eight_near_zero
    (eps : ℝ) (heps : 0 < eps) (hepsUpper : eps < 21 / 200)
    {v : GammaSewnCriticalPhysicalPluckerHilbert}
    (hv : boundaryInverse eps v = (8 : ℂ) • v) :
    v = 0 := by
  have hloc :=
    GaloisForLFunctions.RHTower.positiveBoundaryInverse_eq_real_smul_imp_operator_eq_smul
      gammaSewnCriticalPhysicalPluckerSpectralOperator_isPositive.isSelfAdjoint
      spectrum_real_subset eps heps (c := 8) (by norm_num) hv
  have hShell : (1 / 50 : ℝ) < 1 / 8 - eps := by
    linarith
  have hShellPos : 0 < (1 / 8 : ℝ) - eps :=
    (by positivity : (0 : ℝ) < 1 / 50).trans hShell
  have hbound :
      ((1 / 8 : ℝ) - eps) * ‖v‖ ≤ (1 / 50 : ℝ) * ‖v‖ := calc
    ((1 / 8 : ℝ) - eps) * ‖v‖ =
        ‖((((1 / 8 : ℝ) - eps : ℝ) : ℂ) • v)‖ := by
      rw [norm_smul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hShellPos]
    _ = ‖gammaSewnCriticalPhysicalPluckerSpectralOperator v‖ :=
      congrArg norm hloc.symm
    _ ≤ ‖gammaSewnCriticalPhysicalPluckerSpectralOperator‖ * ‖v‖ :=
      gammaSewnCriticalPhysicalPluckerSpectralOperator.le_opNorm v
    _ ≤ (1 / 50 : ℝ) * ‖v‖ :=
      mul_le_mul_of_nonneg_right
        norm_gammaSewnCriticalPhysicalPluckerSpectralOperator_le_one_div_fifty
        (norm_nonneg v)
  apply norm_eq_zero.mp
  nlinarith [norm_nonneg v]

/-- **P-G102 spectral-shell capstone.**  In the genuine zero-boundary neighborhood, none of the
three canonical resolvent channels can realize the unique amplitude-eight source correction. -/
theorem gammaSewnCriticalPhysicalPlucker_canonicalBoundaryResolvent_cannot_rebalance_near_zero
    (pe : Nat.Primes × ℕ) (eps : ℝ) (heps : 0 < eps)
    (hepsUpper : eps < 21 / 200)
    {v : GammaSewnCriticalPhysicalPluckerHilbert} (hv0 : v ≠ 0) :
    let w := routePPrimitiveBaseCauchyCubicWeight pe
    let c : ℝ := 8
    w / 64 * c ^ 2 = w ∧
      boundaryTransfer eps v ≠ (c : ℂ) • v ∧
      (eps • boundaryInverse eps) v ≠ (c : ℂ) • v ∧
      boundaryInverse eps v ≠ (c : ℂ) • v := by
  dsimp
  have hbounded :=
    gammaSewnCriticalPhysicalPlucker_canonicalBoundarySplit_cannot_rebalance_fourthDepth
      pe eps heps hv0
  refine ⟨hbounded.1, hbounded.2.1, hbounded.2.2, ?_⟩
  intro hv
  exact hv0
    (gammaSewnCriticalPhysicalPluckerBoundaryInverse_no_amplitude_eight_near_zero
      eps heps hepsUpper hv)

end RHTower.HedenmalmThetaSource
