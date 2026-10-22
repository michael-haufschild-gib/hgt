import GaloisForLFunctions.ScaleSignedIncidenceCriticality.TheHeightFaceUnitIsTheFirstOffLineHorizon

/-!
# The horizon unit: a proper interval, and still an empty seam

In the horizon unit the bounded-height reading is sharp, so two questions arise that are vacuous in
the width unit: is the reading *informative* there, and does joining it with an aperture certificate
improve it? The answers are yes and no.

* `resolutionInterval_horizonFrequency_heightReading` — the interval left open is `[0, (1+T)⁻¹]`,
  a proper subinterval of the unit's full range `[0, 1]`. So the truncated divisor is informative
  in its own unit — unlike the width unit, where the interval is everything
  (`TheResolutionIntervalIsTheWholeRange`).
* `resolutionLimit_horizonFrequency_join` — joining the aperture-`a` certificate changes nothing:
  the limit is still exactly `(1+T)⁻¹`. The inserted pairs that witness the limit satisfy the
  certificate for a reason independent of their height (`aperturePositivity_latticeWithPairAt_iff`
  does not involve `γ₀`), so one certificate per aperture cannot shorten the horizon.

Together with `TheHeightApertureSeamIsEmpty` this says the height–aperture seam is empty in **both**
units of the two faces, not only in the depth unit where the two readings are jointly trivial. The
aperture certificate and the truncated divisor are independent in the strongest sense available: on
the depth they are jointly blind, on the horizon they are jointly no better than the divisor alone,
and on the scale they are jointly no better than the certificate alone.
-/

open Set
open GaloisForLFunctions.SquareRootThreshold

namespace GaloisForLFunctions.ScaleSignedIncidenceCriticality

open Zeta23 _root_.RHTower

set_option autoImplicit false

/-! ### 1. The interval in the horizon unit is proper -/

theorem bddBelow_horizonFrequency_image (s : Set TemperedZeroConfig) :
    BddBelow (horizonFrequency '' s) :=
  ⟨0, by rintro x ⟨Z, -, rfl⟩; exact horizonFrequency_nonneg Z⟩

/-- The on-line lattice has no off-line zero, so the floor of the horizon unit is `0`. -/
theorem resolutionFloor_horizonFrequency_heightReading {L T : ℝ} (hL : 0 < L) :
    resolutionFloor horizonFrequency (heightReading T) (onLineLattice hL) = 0 := by
  refine le_antisymm ?_
    ((certifiesLower_iff_le_resolutionFloor (bddBelow_horizonFrequency_image _)).mp
      fun W _ => horizonFrequency_nonneg W)
  have h := resolutionFloor_le (I := horizonFrequency) (r := heightReading T)
    (d := onLineLattice hL) (bddBelow_horizonFrequency_image _)
  have hzero : horizonFrequency (onLineLattice hL) = 0 :=
    (horizonFrequency_eq_zero_iff _).mpr (width_onLineLattice hL)
  rwa [hzero] at h

/-- **The truncated divisor is informative in its own unit.** -/
theorem resolutionInterval_horizonFrequency_heightReading {L T : ℝ} (hL : 0 < L) (hT : 0 ≤ T) :
    resolutionInterval horizonFrequency (heightReading T) (onLineLattice hL) =
      Icc 0 ((1 + T)⁻¹) := by
  rw [resolutionInterval, resolutionFloor_horizonFrequency_heightReading hL,
    resolutionLimit_horizonFrequency_heightReading hL hT]

/-! ### 2. The aperture certificate does not shorten the horizon -/

/-- **The seam is empty in the horizon unit.** At every spacing `L ≥ 2a + sinh a` the joint reading
of the truncated divisor and the aperture-`a` certificate still has horizon limit `(1+T)⁻¹`. -/
theorem resolutionLimit_horizonFrequency_join {L a T : ℝ} (ha : 0 < a) (hT : 0 ≤ T)
    (hLa : 2 * a + Real.sinh a ≤ L) (hL : 0 < L) :
    resolutionLimit horizonFrequency
        (joinReading (heightReading T) (aperturePositivity a)) (onLineLattice hL) =
      (1 + T)⁻¹ := by
  have hδ : (0 : ℝ) < 1 / 2 := by norm_num
  have hs : 0 < Real.sinh a := Real.sinh_pos_iff.mpr ha
  have haL : a ≤ L / 2 := by linarith
  have hthr : Real.sinh (2 * (1 / 2 : ℝ) * a) / (1 / 2 : ℝ) ≤ 2 * L + 2 * a := by
    rw [show 2 * (1 / 2 : ℝ) * a = a by ring, div_le_iff₀ (by norm_num : (0 : ℝ) < 1 / 2)]
    linarith
  set S := horizonFrequency ''
    shadow (joinReading (heightReading T) (aperturePositivity a)) (onLineLattice hL) with hS
  have hub : ∀ x ∈ S, x ≤ (1 + T)⁻¹ := by
    rintro x ⟨W, hW, rfl⟩
    exact horizonFrequency_le_of_mem_shadow hL hT ((shadow_joinReading _ _ _).subset hW).1
  have hmemS : ∀ γ : ℝ, T < γ → (1 + γ)⁻¹ ∈ S := by
    intro γ hγ
    have hγ0 : 0 ≤ γ := by linarith
    refine ⟨latticeWithPairAt hL hδ le_rfl γ, ?_, ?_⟩
    · refine (shadow_joinReading _ _ _).symm.subset ⟨?_, ?_⟩
      · exact heightReading_latticeWithPairAt hL hδ le_rfl (by rwa [abs_of_nonneg hγ0])
      · exact propext (iff_of_true
          ((aperturePositivity_latticeWithPairAt_iff hL hδ le_rfl γ ha haL).mpr hthr)
          (aperturePositivity_onLineLattice hL a))
    · rw [horizonFrequency_latticeWithPairAt hL hδ le_rfl γ, abs_of_nonneg hγ0]
  have hbdd : BddAbove S := ⟨(1 + T)⁻¹, hub⟩
  have hne : S.Nonempty := ⟨(1 + (T + 1))⁻¹, hmemS (T + 1) (by linarith)⟩
  show sSup S = (1 + T)⁻¹
  refine le_antisymm (Real.sSup_le hub (by positivity)) ?_
  rw [Real.le_sSup_iff hbdd hne]
  intro ε hε
  rcases le_or_gt ((1 + T)⁻¹ + ε) 0 with ht | ht
  · refine ⟨(1 + (T + 1))⁻¹, hmemS (T + 1) (by linarith), ?_⟩
    have : (0 : ℝ) < (1 + (T + 1))⁻¹ := by positivity
    linarith
  · have htlt : (1 + T)⁻¹ + ε < (1 + T)⁻¹ := by linarith
    have h1T : (0 : ℝ) < 1 + T := by positivity
    have hinvgt : 1 + T < ((1 + T)⁻¹ + ε)⁻¹ := by
      have h := (inv_lt_inv₀ (inv_pos.mpr h1T) ht).mpr htlt
      rwa [inv_inv] at h
    set γ : ℝ := ((1 + T) + ((1 + T)⁻¹ + ε)⁻¹) / 2 - 1 with hγdef
    have hγT : T < γ := by simp only [hγdef]; linarith
    have hγ1 : 1 + γ < ((1 + T)⁻¹ + ε)⁻¹ := by simp only [hγdef]; linarith
    have hγ0 : (0 : ℝ) < 1 + γ := by linarith
    refine ⟨(1 + γ)⁻¹, hmemS γ hγT, ?_⟩
    have h := (inv_lt_inv₀ (inv_pos.mpr ht) hγ0).mpr hγ1
    rwa [inv_inv] at h

/-! ### 3. Both units, one conclusion -/

/-- **The two readings are independent in every unit of the two faces.** On the depth they are
jointly trivial, on the horizon the certificate adds nothing to the divisor, and the interval the
divisor leaves open in its own unit is proper. -/
theorem theHorizonSeamIsEmpty {L a T : ℝ} (ha : 0 < a) (hT : 0 ≤ T)
    (hLa : 2 * a + Real.sinh a ≤ L) (hL : 0 < L) :
    resolutionInterval horizonFrequency (heightReading T) (onLineLattice hL) =
        Icc 0 ((1 + T)⁻¹) ∧
      resolutionLimit horizonFrequency
          (joinReading (heightReading T) (aperturePositivity a)) (onLineLattice hL) =
        (1 + T)⁻¹ :=
  ⟨resolutionInterval_horizonFrequency_heightReading hL hT,
    resolutionLimit_horizonFrequency_join ha hT hLa hL⟩

end GaloisForLFunctions.ScaleSignedIncidenceCriticality
