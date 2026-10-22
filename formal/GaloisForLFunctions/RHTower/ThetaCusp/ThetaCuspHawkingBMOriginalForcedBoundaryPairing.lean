import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMOriginalRadialBracket
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! Source-dependent boundary pairing for the actual original forced radial operator. -/
open Complex Set Filter Topology MeasureTheory
namespace RHTower.D4BMLaplaceRadial
noncomputable section
attribute [-instance] instInnerProductSpaceRealComplex
attribute [-instance] RCLike.toInnerProductSpaceReal
attribute [-instance] NormedSpace.complexToReal

/-- The original pairing weight is continuous on every interior radial interval. -/
theorem radialPairingWeight_continuousAt {b : ℝ} (hb : b < 1) :
    ContinuousAt radialPairingWeight b := by
  have hp := (power_derivatives (1/2) (sub_pos.mpr hb)).1.continuousAt
  have hp' : ContinuousAt (fun t : ℝ => power (1/2) (1-t)) b :=
    hp.comp_of_eq (continuousAt_const.sub continuousAt_id) rfl
  have hx0 : (1-(b:ℂ)) ≠ 0 := by exact_mod_cast (sub_pos.mpr hb).ne'
  exact hp'.div (continuousAt_const.sub Complex.continuous_ofReal.continuousAt) hx0

/-- The actual forced horizon bracket differentiates to the original source pairing. -/
theorem original_forced_horizon_phase_hasDerivAt (w chi : ℂ) (hw : w.im ≠ 0)
    {U D DD F : ℝ → ℂ} {b : ℝ} (hb : b ∈ Ioo 0 1)
    (hU : HasDerivAt U (D b) b) (hD : HasDerivAt D (DD b) b)
    (hL : D4BMPhysicalMaster.radialJet (I*w) chi b (U b) (D b) (DD b)=F b) :
    HasDerivAt (radialBracket (horizon w chi) (horizonFirst w chi) U D)
      (radialPairingWeight b * horizon w chi b * F b) b := by
  have hH := horizon_derivatives_continued (w:=w) (chi:=chi) hb
  have h := radialBracket_hasDerivAt w chi hb hH.1 hH.2 hU hD
  simpa only [hL,horizon_equation_continued hw hb,mul_zero,sub_zero,mul_assoc] using h

/-- Exact source-dependent variation of the original horizon phase on every compact interior interval. -/
theorem original_forced_horizon_phase_integral (w chi : ℂ) (hw : w.im ≠ 0)
    {U D DD F : ℝ → ℂ}
    (hU : ∀ t ∈ Ioo 0 1, HasDerivAt U (D t) t)
    (hD : ∀ t ∈ Ioo 0 1, HasDerivAt D (DD t) t)
    (hL : ∀ t : ℝ, t ∈ Ioo 0 1 →
      D4BMPhysicalMaster.radialJet (I*w) chi t (U t) (D t) (DD t)=F t)
    (hF : ContinuousOn F (Ioo 0 1))
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b < 1) :
    (∫ t in a..b, radialPairingWeight t * horizon w chi t * F t) =
      radialBracket (horizon w chi) (horizonFirst w chi) U D b -
      radialBracket (horizon w chi) (horizonFirst w chi) U D a := by
  have hs : uIcc a b ⊆ Ioo 0 1 := by
    rw [uIcc_of_le hab]
    intro t ht
    exact ⟨lt_of_lt_of_le ha ht.1,lt_of_le_of_lt ht.2 hb⟩
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => original_forced_horizon_phase_hasDerivAt w chi hw
      (hs ht) (hU t (hs ht)) (hD t (hs ht)) (hL t (hs ht)))
  apply ContinuousOn.intervalIntegrable
  intro t ht
  have hc := (radialPairingWeight_continuousAt (hs ht).2).mul
    (horizon_derivatives_continued (w:=w) (chi:=chi) (hs ht)).1.continuousAt
  exact hc.continuousWithinAt.mul ((hF t (hs ht)).mono hs)

end
end RHTower.D4BMLaplaceRadial
