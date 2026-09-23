import GaloisForLFunctions.RHTower.Sieve.MaynardAdjacentAggregateCellExtraction
import GaloisForLFunctions.RHTower.Sieve.MaynardMellinScaleCovariance
import GaloisForLFunctions.RHTower.Sieve.MaynardSpatialMellinL2

/-!
# Fixed-ambient Route-T defect packets

At proportional physical scales the normalized target-reference Mellin defect has one fixed shape.
This module absorbs that shape into the unit-cell coefficient and identifies the literal moving
physical packet with the fixed-ambient packet required by Maynard's spatial `L²` estimate.
-/

noncomputable section

namespace RHTower.Sieve

open Complex

/-- Fixed relative-shape coefficient attached to one ordinate cell.  It has no dependence on the
physical dilation parameter. -/
def maynardFixedAmbientDefectCellCoefficient
    (a : ℝ → ℂ) (N R H sigma : ℝ) (m : ℕ) (v : ℝ) : ℂ :=
  a ((m : ℝ) + v) *
    (routeTNormalizedSmoothWindowMellin N R
        ((sigma : ℂ) + (((m : ℝ) + v : ℝ) : ℂ) * I) -
      routeTNormalizedSmoothWindowMellin N H
        ((sigma : ℂ) + (((m : ℝ) + v : ℝ) : ℂ) * I))

/-- Literal selected-cell packet with physical base and both widths dilated together. -/
def maynardFixedAmbientPhysicalDefectPacket
    (S : Finset ℕ) (a : ℝ → ℂ) (lambda N R H sigma : ℝ) : ℂ :=
  ∫ v : ℝ in (0 : ℝ)..1,
    ∑ m ∈ S, a ((m : ℝ) + v) *
      (routeTNormalizedSmoothWindowMellin (lambda * N) (lambda * R)
          ((sigma : ℂ) + (((m : ℝ) + v : ℝ) : ℂ) * I) -
        routeTNormalizedSmoothWindowMellin (lambda * N) (lambda * H)
          ((sigma : ℂ) + (((m : ℝ) + v : ℝ) : ℂ) * I))

/-- Exact fixed-ambient factorization of the moving physical packet. -/
theorem maynardFixedAmbientPhysicalDefectPacket_eq_mellinPacket
    (S : Finset ℕ) (a : ℝ → ℂ) (lambda N R H sigma : ℝ)
    (hlambda : 0 < lambda) (hR : 0 < R) (hH : 0 < H) :
    maynardFixedAmbientPhysicalDefectPacket S a lambda N R H sigma =
      maynardUnitCellMellinPacket S
        (maynardFixedAmbientDefectCellCoefficient a N R H sigma)
        (sigma - 1) lambda := by
  classical
  simp only [maynardFixedAmbientPhysicalDefectPacket, maynardUnitCellMellinPacket,
    maynardUnitCellMellinIntegrand]
  apply intervalIntegral.integral_congr
  intro v hv
  apply Finset.sum_congr rfl
  intro m hm
  rw [routeTNormalizedSmoothWindowMellin_defect_mul_scale
    lambda N R H
      ((sigma : ℂ) + (((m : ℝ) + v : ℝ) : ℂ) * I) hlambda hR hH]
  rw [maynardFixedAmbientDefectCellCoefficient]
  have hexponent :
      ((sigma : ℂ) + (((m : ℝ) + v : ℝ) : ℂ) * I) - 1 =
        ((sigma - 1 : ℝ) : ℂ) + (((m : ℝ) + v : ℝ) : ℂ) * I := by
    push_cast
    ring
  rw [hexponent]
  ring

/-- Continuity of one fixed-ambient cell coefficient. -/
theorem continuous_maynardFixedAmbientDefectCellCoefficient
    {a : ℝ → ℂ} (ha : Continuous a) {N R H sigma : ℝ}
    (hN : 0 < N) (hR : 0 < R) (hH : 0 < H) (hsigma : 0 < sigma)
    (m : ℕ) :
    Continuous (maynardFixedAmbientDefectCellCoefficient a N R H sigma m) := by
  let shift : ℝ → ℝ := fun v => (m : ℝ) + v
  have hshift : Continuous shift := continuous_const.add continuous_id
  have hKR := continuous_routeTNormalizedSmoothWindowMellin_line hN hR hsigma
  have hKH := continuous_routeTNormalizedSmoothWindowMellin_line hN hH hsigma
  change Continuous fun v : ℝ =>
    a (shift v) *
      (routeTNormalizedSmoothWindowMellin N R
          ((sigma : ℂ) + (shift v : ℝ) * I) -
        routeTNormalizedSmoothWindowMellin N H
          ((sigma : ℂ) + (shift v : ℝ) * I))
  exact (ha.comp hshift).mul ((hKR.sub hKH).comp hshift)

/-- Maynard spatial `L²` estimate for the literal proportional-scale Route-T defect packet.  Its
cell coefficient is fixed before the physical base varies. -/
theorem integral_norm_sq_maynardFixedAmbientPhysicalDefectPacket_le_card
    {x sigma A N R H : ℝ} {cellCount : ℕ}
    (hx : 1 ≤ x) (hsigma : 1 ≤ sigma) (hA : 0 ≤ A)
    (hN : 0 < N) (hR : 0 < R) (hH : 0 < H)
    (S : Finset ℕ) (hS : S ⊆ Finset.range cellCount) (a : ℝ → ℂ)
    (ha : Continuous a)
    (hbnd : ∀ m ∈ S, ∀ v ∈ Set.Icc (0 : ℝ) 1,
      ‖maynardFixedAmbientDefectCellCoefficient a N R H sigma m v‖ ≤ A) :
    (∫ lambda : ℝ in x..(2 * x),
        ‖maynardFixedAmbientPhysicalDefectPacket
          S a lambda N R H sigma‖ ^ (2 : ℕ)) ≤
      4 * (2 * x) ^ (2 * (sigma - 1) + 1) * A ^ (2 : ℕ) * (S.card : ℝ) *
        (1 + 2 * (1 + Real.log cellCount)) := by
  have hb : ∀ m ∈ S,
      Continuous (maynardFixedAmbientDefectCellCoefficient a N R H sigma m) := by
    intro m hm
    exact continuous_maynardFixedAmbientDefectCellCoefficient ha hN hR hH
      (lt_of_lt_of_le zero_lt_one hsigma) m
  have hL2 := integral_norm_sq_maynardUnitCellMellinPacket_le_card
    hx (sub_nonneg.mpr hsigma) hA S hS
      (maynardFixedAmbientDefectCellCoefficient a N R H sigma) hb hbnd
  calc
    (∫ lambda : ℝ in x..(2 * x),
        ‖maynardFixedAmbientPhysicalDefectPacket
          S a lambda N R H sigma‖ ^ (2 : ℕ)) =
        ∫ lambda : ℝ in x..(2 * x),
          ‖maynardUnitCellMellinPacket S
            (maynardFixedAmbientDefectCellCoefficient a N R H sigma)
            (sigma - 1) lambda‖ ^ (2 : ℕ) := by
      apply intervalIntegral.integral_congr
      intro lambda hlambda
      rw [Set.uIcc_of_le (by linarith : x ≤ 2 * x)] at hlambda
      change ‖maynardFixedAmbientPhysicalDefectPacket S a lambda N R H sigma‖ ^ (2 : ℕ) =
        ‖maynardUnitCellMellinPacket S
          (maynardFixedAmbientDefectCellCoefficient a N R H sigma)
          (sigma - 1) lambda‖ ^ (2 : ℕ)
      rw [maynardFixedAmbientPhysicalDefectPacket_eq_mellinPacket
        S a lambda N R H sigma (lt_of_lt_of_le zero_lt_one (hx.trans hlambda.1)) hR hH]
    _ ≤ _ := hL2

end RHTower.Sieve
