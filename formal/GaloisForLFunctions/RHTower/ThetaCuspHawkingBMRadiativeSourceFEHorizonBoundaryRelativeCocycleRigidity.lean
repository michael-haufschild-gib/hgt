import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMRadiativeSourceFEUnitPhaseRealificationNoGo
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMTransferCollisionRigidity

/-!
# Gauge-invariant horizon/boundary source-FE relative cocycle rigidity

HC91 proves that one physical BM Ward channel can be made positive-real by a global unit phase
gauge. This module closes that gauge loophole using two independent physical readouts: horizon
amplitude and exact normalizable AdS-boundary amplitude.

The Birmingham--Mokhtari gamma connection coefficient is Schwarz-compatible and nowhere zero on
Xi copies. Dressing the actual HC89 radiative source-FE cocycle by this boundary transfer produces
an exact nonzero anti-linear boundary cocycle transporting the boundary response and preserving FE
involution. For every common nowhere-zero diagonal gauge, the quotient of boundary and horizon
cocycles is unchanged. Equality of the two gauged gains is therefore equivalent to collision of the
reflected and Schwarz-conjugate BM transfers, hence exactly to critical-line placement.

Consequently, existence of one global common gauge making horizon and boundary gains agree at every
Xi copy is equivalent to the Riemann hypothesis. The final theorem packages transfer conjugation,
physical nonvanishing/transport, involution, gauge-invariant relative holonomy, copywise critical-line
classification, and the global RH equivalence as one closed unconditional proposition.

[NEW] [HORIZON-BOUNDARY] [RELATIVE COCYCLE] [GAUGE INVARIANT] [RH EQUIVALENCE]
-/

open Complex Real

namespace RHTower

noncomputable section


theorem d4BMSecondHarmonicTransferOfRho_conj (rho : ℂ) :
    d4BMSecondHarmonicTransferOfRho ((starRingEnd ℂ) rho) =
      (starRingEnd ℂ) (d4BMSecondHarmonicTransferOfRho rho) := by
  have h1 : -(starRingEnd ℂ) rho - 1 =
      (starRingEnd ℂ) (-rho - 1) := by
    simp
  have h3 : (-((starRingEnd ℂ) rho + 4) / 4) =
      (starRingEnd ℂ) (-(rho + 4) / 4) := by
    apply Complex.ext <;> norm_num [Complex.div_re, Complex.div_im] <;> ring
  have h4 : (-(3 * (starRingEnd ℂ) rho + 2) / 4) =
      (starRingEnd ℂ) (-(3 * rho + 2) / 4) := by
    apply Complex.ext <;> norm_num [Complex.div_re, Complex.div_im] <;> ring
  have hconst : Complex.Gamma (-1 / 2 : ℂ) =
      (starRingEnd ℂ) (Complex.Gamma (-1 / 2 : ℂ)) := by
    calc
      Complex.Gamma (-1 / 2 : ℂ) =
          Complex.Gamma ((starRingEnd ℂ) (-1 / 2 : ℂ)) := by
            congr 1
            apply Complex.ext <;> norm_num
      _ = (starRingEnd ℂ) (Complex.Gamma (-1 / 2 : ℂ)) :=
        Complex.Gamma_conj _
  rw [d4BMSecondHarmonicTransferOfRho, d4BMSecondHarmonicTransferOfRho,
    map_mul, map_mul, map_mul, map_inv₀, map_inv₀,
    h1, h3, h4]
  simp only [Complex.Gamma_conj]
  rw [← hconst]

theorem d4BMXiSecondHarmonicBoundaryTransfer_conj (q : XiZeroCopy) :
    d4BMXiSecondHarmonicBoundaryTransfer (xiZeroCopyConjEquiv q) =
      (starRingEnd ℂ) (d4BMXiSecondHarmonicBoundaryTransfer q) := by
  rw [d4BMXiSecondHarmonicBoundaryTransfer_eq_scalar,
    d4BMXiSecondHarmonicBoundaryTransfer_eq_scalar]
  change d4BMSecondHarmonicTransferOfRho ((starRingEnd ℂ) (q.1 : ℂ)) =
    (starRingEnd ℂ) (d4BMSecondHarmonicTransferOfRho (q.1 : ℂ))
  exact d4BMSecondHarmonicTransferOfRho_conj (q.1 : ℂ)

theorem d4BMXiSecondHarmonicBoundaryTransfer_ne_zero (q : XiZeroCopy) :
    d4BMXiSecondHarmonicBoundaryTransfer q ≠ 0 := by
  exact d4BMGravitationalNormalizableBoundaryTransfer_secondHarmonic_xi_ne_zero q

def hbXiPhaseSensitiveUnitRadiativeSourceFEBoundaryResponse (q : XiZeroCopy) : ℂ :=
  d4BMXiSecondHarmonicBoundaryTransfer q *
    hbXiPhaseSensitiveUnitRadiativeSourceFERawWardAmplitude q

def hbXiPhaseSensitiveUnitRadiativeSourceFEBoundaryCocycle (q : XiZeroCopy) : ℂ :=
  d4BMXiSecondHarmonicBoundaryTransfer (xiZeroCopyReflectEquiv q) *
      hbXiPhaseSensitiveUnitRadiativeSourceFECocycle q /
    (starRingEnd ℂ) (d4BMXiSecondHarmonicBoundaryTransfer q)

def hbXiPhaseSensitiveUnitRadiativeSourceFEBoundaryDiagonalGaugedCocycle
    (b : XiZeroCopy → ℂ) (q : XiZeroCopy) : ℂ :=
  (b (xiZeroCopyReflectEquiv q))⁻¹ * hbXiPhaseSensitiveUnitRadiativeSourceFEBoundaryCocycle q *
    (starRingEnd ℂ) (b q)

theorem hbXiPhaseSensitiveUnitRadiativeSourceFEBoundaryCocycle_transport (q : XiZeroCopy) :
    hbXiPhaseSensitiveUnitRadiativeSourceFEBoundaryCocycle q *
        (starRingEnd ℂ) (hbXiPhaseSensitiveUnitRadiativeSourceFEBoundaryResponse q) =
      hbXiPhaseSensitiveUnitRadiativeSourceFEBoundaryResponse (xiZeroCopyReflectEquiv q) := by
  have hTconj :
      (starRingEnd ℂ) (d4BMXiSecondHarmonicBoundaryTransfer q) ≠ 0 :=
    (map_ne_zero (starRingEnd ℂ)).mpr (d4BMXiSecondHarmonicBoundaryTransfer_ne_zero q)
  rw [hbXiPhaseSensitiveUnitRadiativeSourceFEBoundaryCocycle, hbXiPhaseSensitiveUnitRadiativeSourceFEBoundaryResponse, hbXiPhaseSensitiveUnitRadiativeSourceFEBoundaryResponse,
    map_mul]
  simp only [hbXiPhaseSensitiveUnitRadiativeSourceFERawWardAmplitude]
  field_simp [hTconj]
  rw [mul_assoc,
    hbXiPhaseSensitiveUnitRadiativeSourceFECocycle_transport 0 q]

theorem hbXiPhaseSensitiveUnitRadiativeSourceFEBoundaryCocycle_ne_zero (q : XiZeroCopy) :
    hbXiPhaseSensitiveUnitRadiativeSourceFEBoundaryCocycle q ≠ 0 := by
  exact div_ne_zero
    (mul_ne_zero
      (d4BMXiSecondHarmonicBoundaryTransfer_ne_zero (xiZeroCopyReflectEquiv q))
      (hbXiPhaseSensitiveUnitRadiativeSourceFECocycle_ne_zero q))
    ((map_ne_zero (starRingEnd ℂ)).mpr (d4BMXiSecondHarmonicBoundaryTransfer_ne_zero q))

theorem hbXiPhaseSensitiveUnitRadiativeSourceFEBoundaryResponse_ne_zero_of_offLine
    (q : XiZeroCopy) (hoff : (q.1 : ℂ).re ≠ 1 / 2) :
    hbXiPhaseSensitiveUnitRadiativeSourceFEBoundaryResponse q ≠ 0 := by
  exact mul_ne_zero (d4BMXiSecondHarmonicBoundaryTransfer_ne_zero q)
    (hbXiPhaseSensitiveUnitRadiativeSourceFERawWardAmplitude_ne_zero_of_offLine
      q hoff)

theorem hbXiPhaseSensitiveUnitRadiativeSourceFEBoundaryCocycle_involutive (q : XiZeroCopy) :
    hbXiPhaseSensitiveUnitRadiativeSourceFEBoundaryCocycle (xiZeroCopyReflectEquiv q) *
        (starRingEnd ℂ) (hbXiPhaseSensitiveUnitRadiativeSourceFEBoundaryCocycle q) = 1 := by
  have hTq := d4BMXiSecondHarmonicBoundaryTransfer_ne_zero q
  have hTR := d4BMXiSecondHarmonicBoundaryTransfer_ne_zero (xiZeroCopyReflectEquiv q)
  have hconjTq :
      (starRingEnd ℂ) (d4BMXiSecondHarmonicBoundaryTransfer q) ≠ 0 :=
    (map_ne_zero (starRingEnd ℂ)).mpr hTq
  have hconjTR :
      (starRingEnd ℂ)
          (d4BMXiSecondHarmonicBoundaryTransfer
            (xiZeroCopyReflectEquiv q)) ≠ 0 :=
    (map_ne_zero (starRingEnd ℂ)).mpr hTR
  rw [hbXiPhaseSensitiveUnitRadiativeSourceFEBoundaryCocycle, hbXiPhaseSensitiveUnitRadiativeSourceFEBoundaryCocycle,
    xiZeroCopyReflectEquiv_apply_apply, map_div₀, map_mul]
  have hccTq :
      (starRingEnd ℂ)
          ((starRingEnd ℂ) (d4BMXiSecondHarmonicBoundaryTransfer q)) =
        d4BMXiSecondHarmonicBoundaryTransfer q := by simp
  rw [hccTq]
  field_simp [hTq, hconjTR]
  exact hbXiPhaseSensitiveUnitRadiativeSourceFECocycle_involutive q

theorem hbXiPhaseSensitiveUnitRadiativeSourceFEBoundaryDiagonalGaugedCocycle_eq_transferRatio_mul_horizon
    (b : XiZeroCopy → ℂ) (q : XiZeroCopy) :
    hbXiPhaseSensitiveUnitRadiativeSourceFEBoundaryDiagonalGaugedCocycle b q =
      (d4BMXiSecondHarmonicBoundaryTransfer (xiZeroCopyReflectEquiv q) /
          (starRingEnd ℂ) (d4BMXiSecondHarmonicBoundaryTransfer q)) *
        hbXiPhaseSensitiveUnitRadiativeSourceFEDiagonalGaugedCocycle b q := by
  rw [hbXiPhaseSensitiveUnitRadiativeSourceFEBoundaryDiagonalGaugedCocycle, hbXiPhaseSensitiveUnitRadiativeSourceFEBoundaryCocycle,
    hbXiPhaseSensitiveUnitRadiativeSourceFEDiagonalGaugedCocycle]
  ring

theorem hbXiPhaseSensitiveUnitRadiativeSourceFEDiagonalGaugedCocycle_ne_zero
    (b : XiZeroCopy → ℂ) (hb : ∀ r : XiZeroCopy, b r ≠ 0)
    (q : XiZeroCopy) :
    hbXiPhaseSensitiveUnitRadiativeSourceFEDiagonalGaugedCocycle b q ≠ 0 := by
  rw [hbXiPhaseSensitiveUnitRadiativeSourceFEDiagonalGaugedCocycle]
  exact mul_ne_zero
    (mul_ne_zero (inv_ne_zero (hb (xiZeroCopyReflectEquiv q)))
      (hbXiPhaseSensitiveUnitRadiativeSourceFECocycle_ne_zero q))
    ((map_ne_zero (starRingEnd ℂ)).mpr (hb q))

theorem hbXiPhaseSensitiveUnitRadiativeSourceFEHorizonBoundaryRelativeCocycle_gaugeInvariant
    (b : XiZeroCopy → ℂ) (hb : ∀ r : XiZeroCopy, b r ≠ 0)
    (q : XiZeroCopy) :
    hbXiPhaseSensitiveUnitRadiativeSourceFEBoundaryDiagonalGaugedCocycle b q /
        hbXiPhaseSensitiveUnitRadiativeSourceFEDiagonalGaugedCocycle b q =
      d4BMXiSecondHarmonicBoundaryTransfer (xiZeroCopyReflectEquiv q) /
        (starRingEnd ℂ) (d4BMXiSecondHarmonicBoundaryTransfer q) := by
  rw [hbXiPhaseSensitiveUnitRadiativeSourceFEBoundaryDiagonalGaugedCocycle_eq_transferRatio_mul_horizon]
  field_simp [hbXiPhaseSensitiveUnitRadiativeSourceFEDiagonalGaugedCocycle_ne_zero b hb q]

theorem hbXiPhaseSensitiveUnitRadiativeSourceFEBoundaryHorizonGaugedCocycle_eq_iff_transfer
    (b : XiZeroCopy → ℂ) (hb : ∀ r : XiZeroCopy, b r ≠ 0)
    (q : XiZeroCopy) :
    hbXiPhaseSensitiveUnitRadiativeSourceFEBoundaryDiagonalGaugedCocycle b q =
        hbXiPhaseSensitiveUnitRadiativeSourceFEDiagonalGaugedCocycle b q ↔
      d4BMXiSecondHarmonicBoundaryTransfer (xiZeroCopyReflectEquiv q) =
        (starRingEnd ℂ) (d4BMXiSecondHarmonicBoundaryTransfer q) := by
  rw [hbXiPhaseSensitiveUnitRadiativeSourceFEBoundaryDiagonalGaugedCocycle_eq_transferRatio_mul_horizon]
  have hg := hbXiPhaseSensitiveUnitRadiativeSourceFEDiagonalGaugedCocycle_ne_zero b hb q
  have hTc :
      (starRingEnd ℂ) (d4BMXiSecondHarmonicBoundaryTransfer q) ≠ 0 :=
    (map_ne_zero (starRingEnd ℂ)).mpr (d4BMXiSecondHarmonicBoundaryTransfer_ne_zero q)
  constructor
  · intro heq
    have hratio :
        d4BMXiSecondHarmonicBoundaryTransfer (xiZeroCopyReflectEquiv q) /
            (starRingEnd ℂ) (d4BMXiSecondHarmonicBoundaryTransfer q) = 1 := by
      apply mul_right_cancel₀ hg
      simpa using heq
    calc
      d4BMXiSecondHarmonicBoundaryTransfer (xiZeroCopyReflectEquiv q) =
          (d4BMXiSecondHarmonicBoundaryTransfer (xiZeroCopyReflectEquiv q) /
            (starRingEnd ℂ) (d4BMXiSecondHarmonicBoundaryTransfer q)) *
              (starRingEnd ℂ) (d4BMXiSecondHarmonicBoundaryTransfer q) := by
                field_simp [hTc]
      _ = 1 * (starRingEnd ℂ) (d4BMXiSecondHarmonicBoundaryTransfer q) := by
        rw [hratio]
      _ = (starRingEnd ℂ) (d4BMXiSecondHarmonicBoundaryTransfer q) := by simp
  · intro heq
    rw [heq, div_self hTc, one_mul]

theorem hbXiPhaseSensitiveUnitRadiativeSourceFEBoundaryHorizonGaugedCocycle_eq_iff_re_eq_half
    (b : XiZeroCopy → ℂ) (hb : ∀ r : XiZeroCopy, b r ≠ 0)
    (q : XiZeroCopy) :
    hbXiPhaseSensitiveUnitRadiativeSourceFEBoundaryDiagonalGaugedCocycle b q =
        hbXiPhaseSensitiveUnitRadiativeSourceFEDiagonalGaugedCocycle b q ↔
      (q.1 : ℂ).re = 1 / 2 := by
  rw [hbXiPhaseSensitiveUnitRadiativeSourceFEBoundaryHorizonGaugedCocycle_eq_iff_transfer b hb q,
    ← d4BMXiSecondHarmonicBoundaryTransfer_conj q,
    d4BMXiSecondHarmonicBoundaryTransfer_reflect_conj_collision_iff]

def HBXiPhaseSensitiveUnitRadiativeSourceFEHorizonBoundaryGlobalCommonGainGauge : Prop :=
  ∃ b : XiZeroCopy → ℂ,
    (∀ q : XiZeroCopy, b q ≠ 0) ∧
    (∀ q : XiZeroCopy,
      hbXiPhaseSensitiveUnitRadiativeSourceFEBoundaryDiagonalGaugedCocycle b q =
        hbXiPhaseSensitiveUnitRadiativeSourceFEDiagonalGaugedCocycle b q)

theorem hbXiPhaseSensitiveUnitRadiativeSourceFEHorizonBoundaryGlobalCommonGainGauge_iff_rh :
    HBXiPhaseSensitiveUnitRadiativeSourceFEHorizonBoundaryGlobalCommonGainGauge ↔ RiemannHypothesis := by
  constructor
  · rintro ⟨b, hb, hgain⟩
    apply (forall_hbXiPeierlsUnitSourceFEBasisTransport_fixedPairing_iff_rh).mp
    intro q
    apply (hbXiPeierlsUnitSourceFEBasisTransport_fixedPairing_iff q).mpr
    exact (hbXiPhaseSensitiveUnitRadiativeSourceFEBoundaryHorizonGaugedCocycle_eq_iff_re_eq_half b hb q).mp
      (hgain q)
  · intro hRH
    refine ⟨fun _ => 1, ?_, ?_⟩
    · intro q
      norm_num
    · intro q
      apply (hbXiPhaseSensitiveUnitRadiativeSourceFEBoundaryHorizonGaugedCocycle_eq_iff_re_eq_half
        (fun _ => 1) (fun _ => one_ne_zero) q).mpr
      exact (hbXiPeierlsUnitSourceFEBasisTransport_fixedPairing_iff q).mp
        ((forall_hbXiPeierlsUnitSourceFEBasisTransport_fixedPairing_iff_rh).mpr
          hRH q)

def HBXiPhaseSensitiveUnitRadiativeSourceFEHorizonBoundaryRelativeCocycleRigidity : Prop :=
  (∀ q : XiZeroCopy,
    d4BMXiSecondHarmonicBoundaryTransfer (xiZeroCopyConjEquiv q) =
        (starRingEnd ℂ) (d4BMXiSecondHarmonicBoundaryTransfer q) ∧
      d4BMXiSecondHarmonicBoundaryTransfer q ≠ 0) ∧
  (∀ q : XiZeroCopy,
    ((q.1 : ℂ).re ≠ 1 / 2 → hbXiPhaseSensitiveUnitRadiativeSourceFEBoundaryResponse q ≠ 0) ∧
    hbXiPhaseSensitiveUnitRadiativeSourceFEBoundaryCocycle q *
        (starRingEnd ℂ) (hbXiPhaseSensitiveUnitRadiativeSourceFEBoundaryResponse q) =
      hbXiPhaseSensitiveUnitRadiativeSourceFEBoundaryResponse (xiZeroCopyReflectEquiv q) ∧
    hbXiPhaseSensitiveUnitRadiativeSourceFEBoundaryCocycle (xiZeroCopyReflectEquiv q) *
        (starRingEnd ℂ) (hbXiPhaseSensitiveUnitRadiativeSourceFEBoundaryCocycle q) = 1) ∧
  (∀ b : XiZeroCopy → ℂ, (∀ q : XiZeroCopy, b q ≠ 0) →
    ∀ q : XiZeroCopy,
      hbXiPhaseSensitiveUnitRadiativeSourceFEBoundaryDiagonalGaugedCocycle b q /
          hbXiPhaseSensitiveUnitRadiativeSourceFEDiagonalGaugedCocycle b q =
        d4BMXiSecondHarmonicBoundaryTransfer (xiZeroCopyReflectEquiv q) /
          (starRingEnd ℂ) (d4BMXiSecondHarmonicBoundaryTransfer q) ∧
      (hbXiPhaseSensitiveUnitRadiativeSourceFEBoundaryDiagonalGaugedCocycle b q =
          hbXiPhaseSensitiveUnitRadiativeSourceFEDiagonalGaugedCocycle b q ↔
        (q.1 : ℂ).re = 1 / 2)) ∧
  (HBXiPhaseSensitiveUnitRadiativeSourceFEHorizonBoundaryGlobalCommonGainGauge ↔ RiemannHypothesis)

theorem hbXiPhaseSensitiveUnitRadiativeSourceFEHorizonBoundaryRelativeCocycleRigidity :
    HBXiPhaseSensitiveUnitRadiativeSourceFEHorizonBoundaryRelativeCocycleRigidity := by
  refine ⟨?_, ?_, ?_, hbXiPhaseSensitiveUnitRadiativeSourceFEHorizonBoundaryGlobalCommonGainGauge_iff_rh⟩
  · intro q
    exact ⟨d4BMXiSecondHarmonicBoundaryTransfer_conj q, d4BMXiSecondHarmonicBoundaryTransfer_ne_zero q⟩
  · intro q
    exact ⟨hbXiPhaseSensitiveUnitRadiativeSourceFEBoundaryResponse_ne_zero_of_offLine q,
      hbXiPhaseSensitiveUnitRadiativeSourceFEBoundaryCocycle_transport q,
      hbXiPhaseSensitiveUnitRadiativeSourceFEBoundaryCocycle_involutive q⟩
  · intro b hb q
    exact ⟨hbXiPhaseSensitiveUnitRadiativeSourceFEHorizonBoundaryRelativeCocycle_gaugeInvariant b hb q,
      hbXiPhaseSensitiveUnitRadiativeSourceFEBoundaryHorizonGaugedCocycle_eq_iff_re_eq_half b hb q⟩

end
end RHTower

