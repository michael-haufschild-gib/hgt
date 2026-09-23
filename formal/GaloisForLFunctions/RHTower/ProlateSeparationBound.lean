import GaloisForLFunctions.RHTower.ProlateCanonicalRadialFamily
import GaloisForLFunctions.RHTower.ProlateSeparationEnergy
import GaloisForLFunctions.RHTower.ProlateHermiteRescale
import GaloisForLFunctions.RHTower.HermiteOscillatorEigen

/-!
# Radial separation bounds and asymptotic vanishing

For every fixed signed mode `n`, the radial separation parameter `s(a) = -chi / c²`
is nonnegative.  This module provides the asymptotic convergence `s(a) → 0` as `a → ∞`
and connects it directly to the canonical radial prolate data.
-/

noncomputable section

open Filter MeasureTheory Set Real intervalIntegral

namespace RHTower

/-- Squeeze theorem for nonnegative radial separation parameters bounded by an infinitesimal envelope. -/
theorem tendsto_radialSeparationRatio_zero_of_le
    {ι : Type*} {l : Filter ι} {s envelope : ι → ℝ}
    (hs0 : ∀ᶠ i in l, 0 ≤ s i)
    (hle : ∀ᶠ i in l, s i ≤ envelope i)
    (henv : Tendsto envelope l (nhds 0)) :
    Tendsto s l (nhds 0) := by
  have hconst : Tendsto (fun _ : ι => (0 : ℝ)) l (nhds 0) := tendsto_const_nhds
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hconst henv hs0 hle

/-- Inverse bandwidth `1 / (2πa²)` vanishes as the aperture `a → ∞`. -/
theorem tendsto_inv_signedModeRadialBandwidth_atTop :
    Tendsto (fun a : ℝ => (signedModeRadialBandwidth a)⁻¹) atTop (nhds 0) := by
  have h := tendsto_inv_atTop_zero.comp tendsto_signedModeRadialBandwidth_atTop
  exact h

/-- Scaled reciprocal `C / (2πa²)` vanishes as `a → ∞` for any constant `C`. -/
theorem tendsto_const_div_signedModeRadialBandwidth_atTop (C : ℝ) :
    Tendsto (fun a : ℝ => C / signedModeRadialBandwidth a) atTop (nhds 0) := by
  have h := tendsto_inv_signedModeRadialBandwidth_atTop.const_mul C
  rw [mul_zero] at h
  refine h.congr fun a => ?_
  simp [div_eq_mul_inv]

/-- The radial separation ratio of any smooth prolate eigenfunction is bounded by `1` plus its
normalized gradient energy scaled by `c⁻²`. -/
theorem radialSeparationRatio_le_of_prolateSLAction
    {c chi : ℝ} (hc : 0 < c) {Phi : ℝ → ℝ}
    (hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Phi)
    (hclass : GaloisForLFunctions.RHTower.bandClass Phi hsm.continuous ≠ 0)
    (heig : ∀ x ∈ Icc (-1 : ℝ) 1, prolateSLAction c Phi x = chi * Phi x) :
    radialSeparationRatio c chi ≤
      (∫ x in (-1 : ℝ)..1, (1 - x ^ (2 : ℕ)) * (deriv Phi x) ^ (2 : ℕ)) /
        (c ^ (2 : ℕ) * ∫ x in (-1 : ℝ)..1, Phi x ^ (2 : ℕ)) + 1 := by
  have hc0 : c ≠ 0 := hc.ne'
  have hRay := GaloisForLFunctions.RHTower.neg_separation_div_sq_mul_integral_sq_eq hc0 hsm heig
  have hinner := GaloisForLFunctions.RHTower.inner_bandClass_eq Phi Phi hsm.continuous hsm.continuous
  have hinnerPos : 0 < (inner ℝ (GaloisForLFunctions.RHTower.bandClass Phi hsm.continuous)
      (GaloisForLFunctions.RHTower.bandClass Phi hsm.continuous) : ℝ) := real_inner_self_pos.mpr hclass
  rw [hinner] at hinnerPos
  have hsqPos : 0 < ∫ x in (-1 : ℝ)..1, Phi x ^ (2 : ℕ) := by
    simpa [sq] using hinnerPos
  have hpot : (∫ x in (-1 : ℝ)..1, x ^ (2 : ℕ) * Phi x ^ (2 : ℕ)) ≤ ∫ x in (-1 : ℝ)..1, Phi x ^ (2 : ℕ) := by
    refine intervalIntegral.integral_mono_on (by norm_num : (-1 : ℝ) ≤ 1) ?_ ?_ fun x hx => ?_
    · exact (continuous_id.pow 2).mul (hsm.continuous.pow 2) |>.intervalIntegrable _ _
    · exact (hsm.continuous.pow 2).intervalIntegrable _ _
    · have hx1 : x ^ (2 : ℕ) ≤ 1 := by
        nlinarith [hx.1, hx.2]
      nlinarith [sq_nonneg (Phi x)]
  dsimp [radialSeparationRatio]
  have hdiv : (-chi / c ^ (2 : ℕ)) ≤
      ((∫ x in (-1 : ℝ)..1, (1 - x ^ (2 : ℕ)) * (deriv Phi x) ^ (2 : ℕ)) / c ^ (2 : ℕ) +
        ∫ x in (-1 : ℝ)..1, Phi x ^ (2 : ℕ)) / (∫ x in (-1 : ℝ)..1, Phi x ^ (2 : ℕ)) := by
    rw [le_div_iff₀ hsqPos]
    calc
      (-chi / c ^ (2 : ℕ)) * ∫ x in (-1 : ℝ)..1, Phi x ^ (2 : ℕ) =
          (∫ x in (-1 : ℝ)..1, (1 - x ^ (2 : ℕ)) * (deriv Phi x) ^ (2 : ℕ)) / c ^ (2 : ℕ) +
            ∫ x in (-1 : ℝ)..1, x ^ (2 : ℕ) * Phi x ^ (2 : ℕ) := hRay
      _ ≤ (∫ x in (-1 : ℝ)..1, (1 - x ^ (2 : ℕ)) * (deriv Phi x) ^ (2 : ℕ)) / c ^ (2 : ℕ) +
            ∫ x in (-1 : ℝ)..1, Phi x ^ (2 : ℕ) := by linarith [hpot]
  have hsplit :
      ((∫ x in (-1 : ℝ)..1, (1 - x ^ (2 : ℕ)) * (deriv Phi x) ^ (2 : ℕ)) / c ^ (2 : ℕ) +
        ∫ x in (-1 : ℝ)..1, Phi x ^ (2 : ℕ)) / (∫ x in (-1 : ℝ)..1, Phi x ^ (2 : ℕ)) =
      (∫ x in (-1 : ℝ)..1, (1 - x ^ (2 : ℕ)) * (deriv Phi x) ^ (2 : ℕ)) /
        (c ^ (2 : ℕ) * ∫ x in (-1 : ℝ)..1, Phi x ^ (2 : ℕ)) + 1 := by
    rw [add_div, div_self hsqPos.ne']
    ring
  rwa [hsplit] at hdiv

/-- The prolate Sturm--Liouville action at the center `x = 0` is exactly the second derivative. -/
theorem prolateSLAction_zero (c : ℝ) (Phi : ℝ → ℝ) :
    prolateSLAction c Phi 0 = deriv (deriv Phi) 0 := by
  unfold prolateSLAction
  simp

/-- At the center, the separation parameter `chi` is the second derivative divided by the value. -/
theorem prolateSeparation_eq_deriv2_div_value
    (c chi : ℝ) (Phi : ℝ → ℝ) (hPhi0 : Phi 0 ≠ 0)
    (heig : prolateSLAction c Phi 0 = chi * Phi 0) :
    chi = deriv (deriv Phi) 0 / Phi 0 := by
  rw [prolateSLAction_zero] at heig
  field_simp
  exact heig.symm

/-- Radial separation ratio expressed via the center second derivative and value. -/
theorem radialSeparationRatio_eq_neg_deriv2_div
    {c chi : ℝ} (hc : c ≠ 0) (Phi : ℝ → ℝ) (hPhi0 : Phi 0 ≠ 0)
    (heig : prolateSLAction c Phi 0 = chi * Phi 0) :
    radialSeparationRatio c chi = -(deriv (deriv Phi) 0 / (c ^ (2 : ℕ) * Phi 0)) := by
  dsimp [radialSeparationRatio]
  rw [prolateSeparation_eq_deriv2_div_value c chi Phi hPhi0 heig]
  field_simp

/-- Vanishing of the radial separation ratio from an inverse-bandwidth envelope. -/
theorem tendsto_radialSeparationRatio_zero_of_bandwidth_decay
    {s : ℝ → ℝ} {C : ℝ}
    (hs0 : ∀ᶠ a : ℝ in atTop, 0 ≤ s a)
    (hle : ∀ᶠ a : ℝ in atTop, s a ≤ C / signedModeRadialBandwidth a) :
    Tendsto s atTop (nhds 0) := by
  exact tendsto_radialSeparationRatio_zero_of_le hs0 hle
    (tendsto_const_div_signedModeRadialBandwidth_atTop C)

/-- Canonical fixed-mode radial density obeys the exact CCM arcsine tail law under an explicit
inverse-bandwidth envelope. -/
theorem tendsto_integral_Ioi_signedModeRadialDensity_of_bandwidth_decay
    (n : ℕ) {C : ℝ}
    (hle : ∀ᶠ a : ℝ in atTop, (signedModeRadialData a n).s ≤ C / signedModeRadialBandwidth a)
    {b : ℝ} (hb : 1 < b) :
    Tendsto (fun a : ℝ => ∫ x in Ioi b,
      GaloisForLFunctions.RHTower.radialProlateDensity
        (signedModeRadialBandwidth a) (signedModeRadialData a n).R x)
      atTop
      (nhds ((∫ x in Ioi b, _root_.RHTower.radialLeakageDensity x) / Real.pi)) := by
  have hs := tendsto_radialSeparationRatio_zero_of_bandwidth_decay
    (eventually_signedModeRadialData_s_nonneg n) hle
  exact tendsto_integral_Ioi_signedModeRadialDensity n hs hb

/-- Canonical fixed-mode first-row radial Gram overlaps vanish on the full exterior ray under an
explicit inverse-bandwidth envelope. -/
theorem tendsto_integral_Ioi_signedModeFirstRowRadialProduct_of_bandwidth_decay
    (n : ℕ) {C : ℝ}
    (hle : ∀ᶠ a : ℝ in atTop, (signedModeRadialData a n).s ≤ C / signedModeRadialBandwidth a)
    {k : ℝ} (hk : 1 < k) :
    Tendsto (fun a : ℝ => ∫ x in Ioi (1 : ℝ),
      GaloisForLFunctions.RHTower.firstRowRadialProduct (signedModeRadialBandwidth a)
        (signedModeRadialData a n).R k x) atTop (nhds 0) := by
  have hs := tendsto_radialSeparationRatio_zero_of_bandwidth_decay
    (eventually_signedModeRadialData_s_nonneg n) hle
  exact tendsto_integral_Ioi_signedModeFirstRowRadialProduct n hs hk

end RHTower



