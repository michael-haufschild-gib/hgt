import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMSecondHarmonicPeierlsArbitraryIncidenceRealizationNoGo
import GaloisForLFunctions.RHTower.XiWeilHardyReferenceLorentzianPlane

/-!
# HB fixed-propagator global rigidity

The universal two-dimensional Peierls carrier realizes every complex incidence after scaling its
propagator by that target.  Requiring one divisor-independent propagator is much more rigid.

For unit Einstein seed and any overtone, such one-propagator global BM incidence is equivalent to
the Riemann hypothesis.  The forward implication is unconditional: Hardy's theorem supplies one
actual critical-line Xi divisor, the exact BM target zero-locus pins the common target to zero,
and global constancy then places every Xi divisor on the critical line.  Conversely RH makes all
BM targets zero, so the zero propagator realizes them simultaneously.

This is a sharp global receiver, not the missing HB producer.  It proves that any literal
source-fixed Peierls construction satisfying all-copy incidence would close RH immediately; a
nonzero constant target cannot evade the critical anchor.

`[NEW] [GLOBAL RIGIDITY] [EXACT RH RECEIVER] [PAPER-PROVED] [LEAN-PROVED]`
-/

open Complex

namespace RHTower

noncomputable section

/-- For unit seed, existence of one divisor-independent universal Peierls propagator matching all
BM boundary incidences is equivalent to RH, at every overtone. -/
theorem exists_hbUniversalPeierls_fixedPropagator_unit_BM_incidence_iff_rh
    (n : ℕ) :
    (∃ T : ℂ, ∀ q : XiZeroCopy,
      d4GaugeFixedTeukolskyPeierlsSourcePairing hbUniversalPeierlsPairing
          (hbUniversalPeierlsPropagator T)
          (d4GaugeFixedTeukolskyQuadraticPlusPlusResidual
            hbUniversalPeierlsQuadraticResidual hbUniversalPeierlsPlusBranch)
          (d4GaugeFixedTeukolskyQuadraticPlusPlusResidual
            hbUniversalPeierlsQuadraticResidual hbUniversalPeierlsMinusBranch) =
        d4BMXiSecondHarmonicSourceScaledBoundaryConcomitant n 1 q) ↔
      RiemannHypothesis := by
  constructor
  · rintro ⟨T, hT⟩
    have hconstant : ∀ q : XiZeroCopy,
        d4BMXiSecondHarmonicSourceScaledBoundaryConcomitant n 1 q = T :=
      (hbUniversalPeierls_fixedPropagator_BM_incidence_iff T n 1).mp hT
    obtain ⟨rho, hrho⟩ := exists_criticalLine_xiDivisorSupport_of_hardy
    have hpos := xi_divisor_pos_on_support rho
    have hnat : 0 < Int.toNat ((MeromorphicOn.divisor xi Set.univ) (rho : ℂ)) := by
      omega
    let q0 : XiZeroCopy := ⟨rho, ⟨0, hnat⟩⟩
    have htarget0 :
        d4BMXiSecondHarmonicSourceScaledBoundaryConcomitant n 1 q0 = 0 := by
      exact (hbUniversalPeierlsBMTarget_eq_zero_iff one_ne_zero n q0
        (z := 1 / 2) (by norm_num) (by norm_num)).mpr hrho
    have hTzero : T = 0 := by
      calc
        T = d4BMXiSecondHarmonicSourceScaledBoundaryConcomitant n 1 q0 :=
          (hconstant q0).symm
        _ = 0 := htarget0
    apply
      (forall_d4BMXiPlusPlusCanonicalPhysicalHorizonSelector_eq_zero_iff_riemannHypothesis n).mp
    intro q
    apply (d4BMXiPlusPlusCanonicalPhysicalHorizonSelector_eq_zero_iff n q).mpr
    apply (hbUniversalPeierlsBMTarget_eq_zero_iff one_ne_zero n q
      (z := 1 / 2) (by norm_num) (by norm_num)).mp
    exact (hconstant q).trans hTzero
  · intro hRH
    refine ⟨0, ?_⟩
    intro q
    rw [hbUniversalPeierls_incidence_eq]
    symm
    apply (hbUniversalPeierlsBMTarget_eq_zero_iff one_ne_zero n q
      (z := 1 / 2) (by norm_num) (by norm_num)).mpr
    exact xi_divisor_support_re_eq_half_of_rh hRH q.1

/-- No nonzero divisor-independent propagator scalar can match all unit-seed BM incidences.  Hardy's
critical-line divisor already forces any such common scalar to vanish. -/
theorem not_exists_hbUniversalPeierls_nonzero_fixedPropagator_unit_BM_incidence
    (n : ℕ) :
    ¬ ∃ T : ℂ, T ≠ 0 ∧ ∀ q : XiZeroCopy,
      d4GaugeFixedTeukolskyPeierlsSourcePairing hbUniversalPeierlsPairing
          (hbUniversalPeierlsPropagator T)
          (d4GaugeFixedTeukolskyQuadraticPlusPlusResidual
            hbUniversalPeierlsQuadraticResidual hbUniversalPeierlsPlusBranch)
          (d4GaugeFixedTeukolskyQuadraticPlusPlusResidual
            hbUniversalPeierlsQuadraticResidual hbUniversalPeierlsMinusBranch) =
        d4BMXiSecondHarmonicSourceScaledBoundaryConcomitant n 1 q := by
  rintro ⟨T, hT, hincidence⟩
  have hconstant : ∀ q : XiZeroCopy,
      d4BMXiSecondHarmonicSourceScaledBoundaryConcomitant n 1 q = T :=
    (hbUniversalPeierls_fixedPropagator_BM_incidence_iff T n 1).mp hincidence
  obtain ⟨rho, hrho⟩ := exists_criticalLine_xiDivisorSupport_of_hardy
  have hpos := xi_divisor_pos_on_support rho
  have hnat : 0 < Int.toNat ((MeromorphicOn.divisor xi Set.univ) (rho : ℂ)) := by
    omega
  let q0 : XiZeroCopy := ⟨rho, ⟨0, hnat⟩⟩
  apply hT
  calc
    T = d4BMXiSecondHarmonicSourceScaledBoundaryConcomitant n 1 q0 :=
      (hconstant q0).symm
    _ = 0 := (hbUniversalPeierlsBMTarget_eq_zero_iff one_ne_zero n q0
      (z := 1 / 2) (by norm_num) (by norm_num)).mpr hrho

end

end RHTower
