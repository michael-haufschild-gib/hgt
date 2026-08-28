import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMThirdOrderFieldRedefinitionMinimax

open Complex

namespace RHTower

noncomputable section

/-- Exact coordinate-invariant minimax cost of a three-channel projection orbit. -/
def D4ThirdOrderProjectionTriple.orbitMinimax
    (t : D4ThirdOrderProjectionTriple) : ℝ :=
  ‖t.total‖ / 3

/-- Canonical equal-channel representative of the redistribution orbit. -/
def D4ThirdOrderProjectionTriple.orbitMinimizer
    (t : D4ThirdOrderProjectionTriple) : D4ThirdOrderProjectionTriple :=
  d4ThirdOrderProjectionEquipartition (-t.total)

theorem d4ThirdOrderProjectionOrbitMinimax_redistribute
    (delta epsilon : ℂ) (t : D4ThirdOrderProjectionTriple) :
    (t.redistribute delta epsilon).orbitMinimax = t.orbitMinimax := by
  simp [D4ThirdOrderProjectionTriple.orbitMinimax,
    d4ThirdOrderProjectionRedistribution_total]

theorem d4ThirdOrderProjectionOrbitMinimizer_total
    (t : D4ThirdOrderProjectionTriple) :
    t.orbitMinimizer.total = t.total := by
  simp [D4ThirdOrderProjectionTriple.orbitMinimizer,
    d4ThirdOrderProjectionEquipartition_total]

theorem d4ThirdOrderProjectionOrbitMinimax_le_peak_of_total_eq
    (x y : D4ThirdOrderProjectionTriple) (htotal : y.total = x.total) :
    x.orbitMinimax ≤ y.peak := by
  have htarget : y.total = -(-x.total) := by simpa using htotal
  simpa [D4ThirdOrderProjectionTriple.orbitMinimax] using
    d4ThirdOrderProjectionPeak_ge_oneThird y (-x.total) htarget

theorem d4ThirdOrderProjectionOrbitMinimax_eq_peak_iff
    (x y : D4ThirdOrderProjectionTriple) (htotal : y.total = x.total) :
    y.peak = x.orbitMinimax ↔ y = x.orbitMinimizer := by
  have htarget : y.total = -(-x.total) := by simpa using htotal
  simpa [D4ThirdOrderProjectionTriple.orbitMinimax,
    D4ThirdOrderProjectionTriple.orbitMinimizer] using
    d4ThirdOrderProjectionPeak_eq_oneThird_iff y (-x.total) htarget

/-- The equal-channel triple is the unique member of an orbit attaining its minimax cost. -/
theorem d4ThirdOrderProjectionOrbitMinimizer_unique
    (x : D4ThirdOrderProjectionTriple) :
    ∃! y : D4ThirdOrderProjectionTriple,
      y.total = x.total ∧ y.peak = x.orbitMinimax := by
  refine ⟨x.orbitMinimizer, ?_, ?_⟩
  · have htotal := d4ThirdOrderProjectionOrbitMinimizer_total x
    refine ⟨htotal, ?_⟩
    exact (d4ThirdOrderProjectionOrbitMinimax_eq_peak_iff x x.orbitMinimizer
      htotal).mpr rfl
  · intro y hy
    exact (d4ThirdOrderProjectionOrbitMinimax_eq_peak_iff x y hy.1).mp hy.2

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- Three actual non-AIME Einstein projections forced to cancel the AIME channel. -/
def d4EinsteinBMCriticalNonAIMEProjectionTriple
    (ell : V →ₗ[ℂ] ℂ)
    (B : V →ₗ[ℂ] V →ₗ[ℂ] V)
    (C : V →ₗ[ℂ] V →ₗ[ℂ] V →ₗ[ℂ] V)
    (P : V →ₗ[ℂ] V) (hPlus hMinus hPlusPlus hPlusMinus : V) :
    D4ThirdOrderProjectionTriple where
  orthogonal := ell (B hPlus (hPlusMinus - P hPlusMinus))
  secondHarmonic := ell (B hMinus hPlusPlus)
  direct := ell (d4EinsteinDirectThirdVariationPlusPlusMinus C hPlus hMinus)

theorem d4EinsteinBMCriticalNonAIMEProjectionTriple_total
    (ell : V →ₗ[ℂ] ℂ)
    (B : V →ₗ[ℂ] V →ₗ[ℂ] V)
    (C : V →ₗ[ℂ] V →ₗ[ℂ] V →ₗ[ℂ] V)
    (P : V →ₗ[ℂ] V) (hPlus hMinus hPlusPlus hPlusMinus : V)
    (n : ℕ) (amplitude : ℂ) (q : XiZeroCopy)
    (hline : (q.1 : ℂ).re = 1 / 2)
    (hmatch :
      d4FullCrossBranchProjectedResidue amplitude
          (fun _ => ell
            (B hPlus (hPlusMinus - P hPlusMinus) + B hMinus hPlusPlus +
              d4EinsteinDirectThirdVariationPlusPlusMinus C hPlus hMinus))
          (xiSpectralPoint q) =
        d4BMXiSecondHarmonicSourceScaledBoundaryConcomitant n 1 q) :
    (d4EinsteinBMCriticalNonAIMEProjectionTriple ell B C P
      hPlus hMinus hPlusPlus hPlusMinus).total =
      -d4FundamentalQNMCrossBranchAIMENumerator amplitude (xiSpectralPoint q) := by
  simpa [d4EinsteinBMCriticalNonAIMEProjectionTriple,
    D4ThirdOrderProjectionTriple.total, map_add] using
    d4EinsteinThirdOrder_nonAIMEProjection_eq_neg_AIME_of_unitBMTarget_of_criticalLine
      ell B C P hPlus hMinus hPlusPlus hPlusMinus n amplitude q hline hmatch

theorem norm_d4FundamentalQNMCrossBranchAIMENumerator
    (amplitude z : ℂ) :
    ‖d4FundamentalQNMCrossBranchAIMENumerator amplitude z‖ =
      ‖amplitude‖ ^ 3 * ‖d4FundamentalQNMCrossBranchChiralMassJetNumerator z‖ := by
  have hnormSq : ‖(Complex.normSq amplitude : ℂ)‖ = ‖amplitude‖ ^ 2 := by
    rw [Complex.normSq_eq_norm_sq]
    simp
  rw [d4FundamentalQNMCrossBranchAIMENumerator, norm_mul, norm_mul, hnormSq]
  ring

/-- Seed-normalized geometric coefficient of the invariant third-order obstruction. -/
def d4AIMEThirdOrderOrbitMinimaxKernel (z : ℂ) : ℝ :=
  ‖d4FundamentalQNMCrossBranchChiralMassJetNumerator z‖ / 3

theorem d4AIMEThirdOrderOrbitMinimaxKernel_eq (z : ℂ) :
    d4AIMEThirdOrderOrbitMinimaxKernel z =
      4 / ‖d4ThetaTeukolskyAngularQ z + 2‖ := by
  rw [d4AIMEThirdOrderOrbitMinimaxKernel,
    d4FundamentalQNMCrossBranchChiralMassJetNumerator_eq,
    norm_div, norm_neg]
  norm_num
  ring

theorem d4AIMEThirdOrderOrbitMinimaxKernel_shadow (z : ℂ) :
    d4AIMEThirdOrderOrbitMinimaxKernel (thetaCuspHawkingOpticalCuspShadow z) =
      d4AIMEThirdOrderOrbitMinimaxKernel z := by
  rw [d4AIMEThirdOrderOrbitMinimaxKernel,
    d4AIMEThirdOrderOrbitMinimaxKernel,
    d4FundamentalQNMCrossBranchChiralMassJetNumerator_shadow]

theorem d4AIMEThirdOrderOrbitMinimaxKernel_xi_pos (q : XiZeroCopy) :
    0 < d4AIMEThirdOrderOrbitMinimaxKernel (xiSpectralPoint q) := by
  exact div_pos
    (norm_pos_iff.mpr
      (d4FundamentalQNMCrossBranchChiralMassJetNumerator_xi_ne_zero q))
    (by norm_num)

theorem d4EinsteinBMCriticalNonAIMEProjectionTriple_orbitMinimax
    (ell : V →ₗ[ℂ] ℂ)
    (B : V →ₗ[ℂ] V →ₗ[ℂ] V)
    (C : V →ₗ[ℂ] V →ₗ[ℂ] V →ₗ[ℂ] V)
    (P : V →ₗ[ℂ] V) (hPlus hMinus hPlusPlus hPlusMinus : V)
    (n : ℕ) (amplitude : ℂ) (q : XiZeroCopy)
    (hline : (q.1 : ℂ).re = 1 / 2)
    (hmatch :
      d4FullCrossBranchProjectedResidue amplitude
          (fun _ => ell
            (B hPlus (hPlusMinus - P hPlusMinus) + B hMinus hPlusPlus +
              d4EinsteinDirectThirdVariationPlusPlusMinus C hPlus hMinus))
          (xiSpectralPoint q) =
        d4BMXiSecondHarmonicSourceScaledBoundaryConcomitant n 1 q) :
    (d4EinsteinBMCriticalNonAIMEProjectionTriple ell B C P
        hPlus hMinus hPlusPlus hPlusMinus).orbitMinimax =
      ‖amplitude‖ ^ 3 *
        d4AIMEThirdOrderOrbitMinimaxKernel (xiSpectralPoint q) := by
  rw [D4ThirdOrderProjectionTriple.orbitMinimax,
    d4EinsteinBMCriticalNonAIMEProjectionTriple_total ell B C P
      hPlus hMinus hPlusPlus hPlusMinus n amplitude q hline hmatch,
    norm_neg, norm_d4FundamentalQNMCrossBranchAIMENumerator,
    d4AIMEThirdOrderOrbitMinimaxKernel]
  ring

theorem d4EinsteinBMCriticalNonAIMEProjectionTriple_seedNormalizedOrbitMinimax
    (ell : V →ₗ[ℂ] ℂ)
    (B : V →ₗ[ℂ] V →ₗ[ℂ] V)
    (C : V →ₗ[ℂ] V →ₗ[ℂ] V →ₗ[ℂ] V)
    (P : V →ₗ[ℂ] V) (hPlus hMinus hPlusPlus hPlusMinus : V)
    (n : ℕ) (amplitude : ℂ) (hamplitude : amplitude ≠ 0) (q : XiZeroCopy)
    (hline : (q.1 : ℂ).re = 1 / 2)
    (hmatch :
      d4FullCrossBranchProjectedResidue amplitude
          (fun _ => ell
            (B hPlus (hPlusMinus - P hPlusMinus) + B hMinus hPlusPlus +
              d4EinsteinDirectThirdVariationPlusPlusMinus C hPlus hMinus))
          (xiSpectralPoint q) =
        d4BMXiSecondHarmonicSourceScaledBoundaryConcomitant n 1 q) :
    (d4EinsteinBMCriticalNonAIMEProjectionTriple ell B C P
          hPlus hMinus hPlusPlus hPlusMinus).orbitMinimax /
        ‖amplitude‖ ^ 3 =
      d4AIMEThirdOrderOrbitMinimaxKernel (xiSpectralPoint q) := by
  rw [d4EinsteinBMCriticalNonAIMEProjectionTriple_orbitMinimax ell B C P
    hPlus hMinus hPlusPlus hPlusMinus n amplitude q hline hmatch]
  exact mul_div_cancel_left₀ _ (pow_ne_zero 3 (norm_ne_zero_iff.mpr hamplitude))

theorem d4EinsteinBMCriticalNonAIMEProjectionTriple_orbitMinimax_pos
    (ell : V →ₗ[ℂ] ℂ)
    (B : V →ₗ[ℂ] V →ₗ[ℂ] V)
    (C : V →ₗ[ℂ] V →ₗ[ℂ] V →ₗ[ℂ] V)
    (P : V →ₗ[ℂ] V) (hPlus hMinus hPlusPlus hPlusMinus : V)
    (n : ℕ) (amplitude : ℂ) (hamplitude : amplitude ≠ 0) (q : XiZeroCopy)
    (hline : (q.1 : ℂ).re = 1 / 2)
    (hmatch :
      d4FullCrossBranchProjectedResidue amplitude
          (fun _ => ell
            (B hPlus (hPlusMinus - P hPlusMinus) + B hMinus hPlusPlus +
              d4EinsteinDirectThirdVariationPlusPlusMinus C hPlus hMinus))
          (xiSpectralPoint q) =
        d4BMXiSecondHarmonicSourceScaledBoundaryConcomitant n 1 q) :
    0 < (d4EinsteinBMCriticalNonAIMEProjectionTriple ell B C P
      hPlus hMinus hPlusPlus hPlusMinus).orbitMinimax := by
  rw [d4EinsteinBMCriticalNonAIMEProjectionTriple_orbitMinimax ell B C P
    hPlus hMinus hPlusPlus hPlusMinus n amplitude q hline hmatch]
  exact mul_pos (pow_pos (norm_pos_iff.mpr hamplitude) 3)
    (d4AIMEThirdOrderOrbitMinimaxKernel_xi_pos q)

/-- Exact physical variational principle: every coordinate representative pays the cubic AIME
cost, and a unique equal-channel representative attains it. -/
theorem d4EinsteinBMCriticalNonAIMEProjectionTriple_sharpOrbitCoercivity
    (ell : V →ₗ[ℂ] ℂ)
    (B : V →ₗ[ℂ] V →ₗ[ℂ] V)
    (C : V →ₗ[ℂ] V →ₗ[ℂ] V →ₗ[ℂ] V)
    (P : V →ₗ[ℂ] V) (hPlus hMinus hPlusPlus hPlusMinus : V)
    (n : ℕ) (amplitude : ℂ) (q : XiZeroCopy)
    (hline : (q.1 : ℂ).re = 1 / 2)
    (hmatch :
      d4FullCrossBranchProjectedResidue amplitude
          (fun _ => ell
            (B hPlus (hPlusMinus - P hPlusMinus) + B hMinus hPlusPlus +
              d4EinsteinDirectThirdVariationPlusPlusMinus C hPlus hMinus))
          (xiSpectralPoint q) =
        d4BMXiSecondHarmonicSourceScaledBoundaryConcomitant n 1 q) :
    let x := d4EinsteinBMCriticalNonAIMEProjectionTriple ell B C P
      hPlus hMinus hPlusPlus hPlusMinus
    let cost := ‖amplitude‖ ^ 3 *
      d4AIMEThirdOrderOrbitMinimaxKernel (xiSpectralPoint q)
    (∀ y : D4ThirdOrderProjectionTriple, y.total = x.total → cost ≤ y.peak) ∧
      ∃! y : D4ThirdOrderProjectionTriple, y.total = x.total ∧ y.peak = cost := by
  dsimp only
  let x := d4EinsteinBMCriticalNonAIMEProjectionTriple ell B C P
    hPlus hMinus hPlusPlus hPlusMinus
  let cost := ‖amplitude‖ ^ 3 *
    d4AIMEThirdOrderOrbitMinimaxKernel (xiSpectralPoint q)
  change (∀ y : D4ThirdOrderProjectionTriple,
      y.total = x.total → cost ≤ y.peak) ∧
    ∃! y : D4ThirdOrderProjectionTriple, y.total = x.total ∧ y.peak = cost
  have hcost : x.orbitMinimax = cost :=
    d4EinsteinBMCriticalNonAIMEProjectionTriple_orbitMinimax ell B C P
      hPlus hMinus hPlusPlus hPlusMinus n amplitude q hline hmatch
  constructor
  · intro y htotal
    rw [← hcost]
    exact d4ThirdOrderProjectionOrbitMinimax_le_peak_of_total_eq x y htotal
  · rcases d4ThirdOrderProjectionOrbitMinimizer_unique x with ⟨y, hy, hunique⟩
    refine ⟨y, ⟨hy.1, hy.2.trans hcost⟩, ?_⟩
    intro z hz
    apply hunique z
    exact ⟨hz.1, hz.2.trans hcost.symm⟩

end

end RHTower
