import GaloisForLFunctions.ScaleSignedIncidenceCriticality.TheTwoFacesReadOneScaleDatum

/-!
# Refutation is finite, confirmation is not

All the programme's entries are upper floors: a bounded reading cannot certify a small width. The
lower theory had only the entry `0` — a bounded certificate cannot force an off-line zero either.
That is a statement about the *aperture* face. On the height face the lower theory is not trivial,
and the asymmetry it exposes is the sharpest structural fact about the two directions of RH.

A divisor truncated at height `T` pins every zero below `T`, multiplicity and real part included.
So if the datum has an off-line zero below `T`, **every** datum sharing the reading has that same
zero, and the reading certifies a positive lower bound on the width
(`certifiesLower_width_heightReading`), hence a positive resolution floor
(`resolutionFloor_width_heightReading_pos`). Meanwhile the upper limit at the same reading is the
trivial `½` (`resolutionLimit_width_heightReading`).

`theAsymmetryOfTheTwoDirections` states the pair, and
`exists_height_certifying_refutation` completes it: **if RH is false, some bounded-height reading
certifies that it is.** Refutation is therefore a finite task — a bounded reading suffices, and the
calculus says which one — while confirmation is not available from any bounded reading at all.

This is why the programme's floors are not symmetric and should not be read as "RH is undecidable
from finite data". Finite data decide the negative side completely; it is the positive side that
lives at infinity.
-/

open Set
open GaloisForLFunctions.SquareRootThreshold

namespace GaloisForLFunctions.ScaleSignedIncidenceCriticality

open Zeta23 _root_.RHTower

set_option autoImplicit false

/-! ### 1. A truncated divisor pins the zeros below its height -/

/-- Every datum sharing the truncated divisor carries the same zeros below the height. -/
theorem mem_carrier_of_mem_shadow_heightReading {T : ℝ} {Z W : TemperedZeroConfig}
    (hW : W ∈ shadow (heightReading T) Z) {ρ : ℂ} (hρ : ρ ∈ Z.1.carrier) (hT : |ρ.im| ≤ T) :
    ρ ∈ W.1.carrier := by
  have hmemZ : ρ ∈ heightWindow T Z := mem_heightWindow.mpr ⟨hρ, hT⟩
  have hnz : heightReading T Z ρ ≠ 0 := by
    rw [heightReading_of_mem hmemZ]
    have h1 := Z.1.one_le_mult ρ hρ
    omega
  rw [← mem_shadow_iff.mp hW] at hnz
  by_contra hcon
  exact hnz (heightReading_of_notMem fun hmem => hcon (mem_heightWindow.mp hmem).1)

/-- **A truncated divisor certifies a lower bound on the width.** -/
theorem certifiesLower_width_heightReading {T : ℝ} {Z : TemperedZeroConfig} {ρ : ℂ}
    (hρ : ρ ∈ Z.1.carrier) (hT : |ρ.im| ≤ T) :
    CertifiesLower width (heightReading T) Z |ρ.re - 1 / 2| := fun _ hW =>
  abs_re_sub_half_le_configWidth (mem_carrier_of_mem_shadow_heightReading hW hρ hT)

/-- **The floor is positive once an off-line zero lies below the height.** -/
theorem resolutionFloor_width_heightReading_pos {T : ℝ} {Z : TemperedZeroConfig} {ρ : ℂ}
    (hρ : ρ ∈ Z.1.carrier) (hT : |ρ.im| ≤ T) (hoff : ρ.re ≠ 1 / 2) :
    0 < resolutionFloor width (heightReading T) Z := by
  have hpos : 0 < |ρ.re - 1 / 2| := abs_pos.mpr (sub_ne_zero_of_ne hoff)
  exact lt_of_lt_of_le hpos
    ((certifiesLower_iff_le_resolutionFloor (bddBelow_width_image _)).mp
      (certifiesLower_width_heightReading hρ hT))

/-! ### 2. The asymmetry -/

/-- **The two directions of RH have different admissibility.** At a datum with an off-line zero
below the truncation height the bounded-height reading certifies a positive width — it refutes —
while at the on-line lattice its upper limit for the width is the trivial `½` — it never
confirms. -/
theorem theAsymmetryOfTheTwoDirections {L T : ℝ} (hL : 0 < L) {Z : TemperedZeroConfig} {ρ : ℂ}
    (hρ : ρ ∈ Z.1.carrier) (hT : |ρ.im| ≤ T) (hoff : ρ.re ≠ 1 / 2) :
    0 < resolutionFloor width (heightReading T) Z ∧
      resolutionLimit width (heightReading T) (onLineLattice hL) = 1 / 2 :=
  ⟨resolutionFloor_width_heightReading_pos hρ hT hoff,
    resolutionLimit_width_heightReading hL T⟩

/-! ### 3. Refutation is complete -/

/-- **If RH is false, a bounded-height reading certifies it.** The refutation side of the problem
is decided by finite data, and the calculus names the height: that of the off-line zero. -/
theorem exists_height_certifying_refutation (h : ¬ RiemannHypothesis) :
    ∃ T β : ℝ, 0 < β ∧ CertifiesLower width (heightReading T) zetaConfig β := by
  have hw : width zetaConfig ≠ 0 := fun hw =>
    h (riemannHypothesis_iff_configWidth_zetaZeroConfig_eq_zero.mpr hw)
  obtain ⟨ρ, hρ, hoff⟩ : ∃ ρ ∈ zetaConfig.1.carrier, ρ.re ≠ 1 / 2 := by
    by_contra hcon
    push Not at hcon
    exact hw (configWidth_eq_zero_iff_onLine.mpr fun ρ hρ => hcon ρ hρ)
  exact ⟨|ρ.im|, |ρ.re - 1 / 2|, abs_pos.mpr (sub_ne_zero_of_ne hoff),
    certifiesLower_width_heightReading hρ le_rfl⟩

/-- **Completeness of the refutation side.** RH fails exactly when some bounded-height reading
certifies a positive width. -/
theorem riemannHypothesis_iff_no_height_certifies_positive :
    RiemannHypothesis ↔
      ¬ ∃ T β : ℝ, 0 < β ∧ CertifiesLower width (heightReading T) zetaConfig β := by
  refine ⟨fun hRH ⟨T, β, hβ, hcert⟩ => ?_, fun h => ?_⟩
  · have hw : width zetaConfig = 0 :=
      riemannHypothesis_iff_configWidth_zetaZeroConfig_eq_zero.mp hRH
    have := hcert zetaConfig (mem_shadow_self (heightReading T) zetaConfig)
    rw [hw] at this
    linarith
  · by_contra hRH
    exact h (exists_height_certifying_refutation hRH)

end GaloisForLFunctions.ScaleSignedIncidenceCriticality
