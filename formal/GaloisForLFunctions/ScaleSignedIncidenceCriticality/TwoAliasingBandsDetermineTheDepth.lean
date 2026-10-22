import GaloisForLFunctions.ScaleSignedIncidenceCriticality.TheSquareRootPrecisionLaw
import GaloisForLFunctions.ScaleSignedIncidenceCriticality.TheResolutionLimitOfAReading

/-!
# Two aliasing bands determine the depth

`TheDepthIsTheCompleteDilationInvariant` shows a level certificate at a *single* aperture resolves
no depth unless the scale is known. That obstruction is an artefact of using one aperture. With two,
the scale is not needed, and the inversion is explicit.

The ground energy of an off-line lattice at aliasing index `n` is `−L·latticeFloor L δ n`. At the
first two nontrivial indices, with `x = δL` and `c = cosh x`,

`t₂ = 2L(c − 1)`,  `t₃ = 4L(c² − 1)`

(`groundEnergy_index_two`, `groundEnergy_index_three`). The ratio strips the scale,
`t₃/(2t₂) − 1 = c`, and the remaining combination restores it, `(t₃ − 4t₂)/t₂² = 1/L`, so

`δ = arcosh(t₃/(2t₂) − 1) · (t₃ − 4t₂)/t₂²`   (`depthFromBands_eq`),

and the pair determines the depth uniquely (`depth_determined_by_two_bands`). No scale bound, no
asymptotics, no uniformity, no limit: two measured magnitudes and elementary functions.

Exactness is not the whole story. The scale-free datum is the ratio, whose critical value is `1`,
and `1 + y²/2 ≤ cosh y` turns an excess `η` into `δL ≤ √(2η)` (`depth_le_sqrt_of_ratio_le`). So the
precision needed to certify depth `β` is of order `β²` — the square-root law of
`TheSquareRootPrecisionLaw` again, now with the scale eliminated.
-/

open Set
open GaloisForLFunctions.SquareRootThreshold
open Zeta23 _root_.RHTower

namespace GaloisForLFunctions.ScaleSignedIncidenceCriticality

set_option autoImplicit false

-- from TwoAliasingBandsDetermineTheDepth.lean
/-! ### 1. The ground energy at the first two nontrivial indices -/

/-- At aliasing index two the ground energy is `2L(cosh x − 1)`. -/
theorem groundEnergy_index_two {L δ : ℝ} (hδL : 0 < δ * L) :
    -(L * latticeFloor L δ 2) = 2 * L * (Real.cosh (δ * L) - 1) := by
  rw [latticeFloor_two hδL]
  ring

/-- At aliasing index three it is `4L sinh²x`. -/
theorem groundEnergy_index_three {L δ : ℝ} (hδL : 0 < δ * L) :
    -(L * latticeFloor L δ 3) = 4 * L * Real.sinh (δ * L) ^ 2 := by
  have hs : Real.sinh (δ * L) ≠ 0 := ne_of_gt (Real.sinh_pos_iff.mpr hδL)
  rw [latticeFloor_eq hδL 3]
  have h3 : ((3 : ℕ) : ℝ) * (δ * L) = 3 * (δ * L) := by norm_num
  rw [h3, Real.sinh_three_mul]
  have hdiv : (4 * Real.sinh (δ * L) ^ 3 + 3 * Real.sinh (δ * L)) / Real.sinh (δ * L)
      = 4 * Real.sinh (δ * L) ^ 2 + 3 := by
    field_simp
  rw [hdiv]
  push_cast
  ring

/-! ### 2. The inversion -/

/-- **Two aliasing bands determine the depth.** The ratio of the two ground energies is `cosh x + 1`,
free of the scale, so the pair determines `x = δL`, then `L`, then `δ`. -/
theorem depth_determined_by_two_bands {L δ L' δ' : ℝ} (hL : 0 < L) (hδ : 0 < δ) (hL' : 0 < L')
    (hδ' : 0 < δ')
    (h2 : -(L * latticeFloor L δ 2) = -(L' * latticeFloor L' δ' 2))
    (h3 : -(L * latticeFloor L δ 3) = -(L' * latticeFloor L' δ' 3)) :
    δ = δ' := by
  have hx : (0 : ℝ) < δ * L := by positivity
  have hx' : (0 : ℝ) < δ' * L' := by positivity
  rw [groundEnergy_index_two hx, groundEnergy_index_two hx'] at h2
  rw [groundEnergy_index_three hx, groundEnergy_index_three hx'] at h3
  -- `sinh² = cosh² − 1`
  have hsq : Real.sinh (δ * L) ^ 2 = Real.cosh (δ * L) ^ 2 - 1 := by
    have := Real.cosh_sq (δ * L)
    linarith
  have hsq' : Real.sinh (δ' * L') ^ 2 = Real.cosh (δ' * L') ^ 2 - 1 := by
    have := Real.cosh_sq (δ' * L')
    linarith
  have hc1 : (1 : ℝ) < Real.cosh (δ * L) := Real.one_lt_cosh.mpr (ne_of_gt hx)
  have hc1' : (1 : ℝ) < Real.cosh (δ' * L') := Real.one_lt_cosh.mpr (ne_of_gt hx')
  rw [hsq] at h3
  rw [hsq'] at h3
  -- the ratio identity forces `cosh x = cosh x'`
  have e2 : L * (Real.cosh (δ * L) - 1) = L' * (Real.cosh (δ' * L') - 1) := by linarith
  have e3 : L * (Real.cosh (δ * L) ^ 2 - 1) = L' * (Real.cosh (δ' * L') ^ 2 - 1) := by linarith
  have hcosh : Real.cosh (δ * L) = Real.cosh (δ' * L') := by
    have hfac : L * (Real.cosh (δ * L) - 1) * (Real.cosh (δ * L) + 1) =
        L' * (Real.cosh (δ' * L') - 1) * (Real.cosh (δ' * L') + 1) := by
      have hid1 : L * (Real.cosh (δ * L) ^ 2 - 1) =
          L * (Real.cosh (δ * L) - 1) * (Real.cosh (δ * L) + 1) := by ring
      have hid2 : L' * (Real.cosh (δ' * L') ^ 2 - 1) =
          L' * (Real.cosh (δ' * L') - 1) * (Real.cosh (δ' * L') + 1) := by ring
      rw [← hid1, ← hid2]
      exact e3
    rw [e2] at hfac
    have hA : (0 : ℝ) < L' * (Real.cosh (δ' * L') - 1) := by nlinarith
    have hcc := mul_left_cancel₀ (ne_of_gt hA) hfac
    linarith
  have hLL : L = L' := by
    rw [hcosh] at e2
    have hpos : (0 : ℝ) < Real.cosh (δ' * L') - 1 := by linarith
    exact mul_right_cancel₀ (ne_of_gt hpos) e2
  have hxx : δ * L = δ' * L' := by
    rcases lt_trichotomy (δ * L) (δ' * L') with hlt | heq | hgt
    · have hlt' : Real.cosh (δ * L) < Real.cosh (δ' * L') := by
        rw [Real.cosh_lt_cosh, abs_of_pos hx, abs_of_pos hx']
        exact hlt
      linarith [hcosh, hlt']
    · exact heq
    · have hgt' : Real.cosh (δ' * L') < Real.cosh (δ * L) := by
        rw [Real.cosh_lt_cosh, abs_of_pos hx', abs_of_pos hx]
        exact hgt
      linarith [hcosh, hgt']
  rw [hLL] at hxx
  exact mul_right_cancel₀ (ne_of_gt hL') hxx

/-! ### 3. The recipe -/

/-- **The recipe.** Two measurements of the ground energy, at aliasing indices two and three,
determine the depth — with no scale bound, no asymptotics and no uniformity. -/
theorem twoAliasingBandsSuffice {L δ L' δ' : ℝ} (hL : 0 < L) (hδ : 0 < δ) (hL' : 0 < L')
    (hδ' : 0 < δ') :
    -(L * latticeFloor L δ 2) = -(L' * latticeFloor L' δ' 2) →
      -(L * latticeFloor L δ 3) = -(L' * latticeFloor L' δ' 3) → δ = δ' :=
  fun h2 h3 => depth_determined_by_two_bands hL hδ hL' hδ' h2 h3

-- from TheExplicitDepthFormula.lean
/-! ### 1. The formula -/

/-- The depth read off two ground energies. -/
noncomputable def depthFromBands (t₂ t₃ : ℝ) : ℝ :=
  Real.arcosh (t₃ / (2 * t₂) - 1) * (t₃ - 4 * t₂) / t₂ ^ 2

/-- **The formula is exact.** -/
theorem depthFromBands_eq {L δ : ℝ} (hL : 0 < L) (hδ : 0 < δ) :
    depthFromBands (-(L * latticeFloor L δ 2)) (-(L * latticeFloor L δ 3)) = δ := by
  have hx : (0 : ℝ) < δ * L := by positivity
  have hc : (1 : ℝ) < Real.cosh (δ * L) := Real.one_lt_cosh.mpr (ne_of_gt hx)
  have ht2 : -(L * latticeFloor L δ 2) = 2 * L * (Real.cosh (δ * L) - 1) :=
    groundEnergy_index_two hx
  have hsq : Real.sinh (δ * L) ^ 2 = Real.cosh (δ * L) ^ 2 - 1 := by
    have := Real.cosh_sq (δ * L)
    linarith
  have ht3 : -(L * latticeFloor L δ 3) = 4 * L * (Real.cosh (δ * L) ^ 2 - 1) := by
    rw [groundEnergy_index_three hx, hsq]
  rw [depthFromBands, ht2, ht3]
  have hc1 : Real.cosh (δ * L) - 1 ≠ 0 := by intro h; linarith [h]
  have hLne : L ≠ 0 := ne_of_gt hL
  -- the ratio strips the scale
  have hden : (2 * (2 * L * (Real.cosh (δ * L) - 1))) ≠ 0 := by
    have hpos : (0 : ℝ) < Real.cosh (δ * L) - 1 := by linarith
    positivity
  have hratio : 4 * L * (Real.cosh (δ * L) ^ 2 - 1) / (2 * (2 * L * (Real.cosh (δ * L) - 1))) - 1 =
      Real.cosh (δ * L) := by
    have h1 : 4 * L * (Real.cosh (δ * L) ^ 2 - 1) /
        (2 * (2 * L * (Real.cosh (δ * L) - 1))) = Real.cosh (δ * L) + 1 := by
      rw [div_eq_iff hden]
      ring
    rw [h1]
    ring
  rw [hratio, Real.arcosh_cosh hx.le]
  -- the remaining combination restores it
  have hden2 : (2 * L * (Real.cosh (δ * L) - 1)) ^ 2 ≠ 0 := by
    have hpos : (0 : ℝ) < Real.cosh (δ * L) - 1 := by linarith
    positivity
  have hscale : (4 * L * (Real.cosh (δ * L) ^ 2 - 1) - 4 * (2 * L * (Real.cosh (δ * L) - 1))) /
      (2 * L * (Real.cosh (δ * L) - 1)) ^ 2 = 1 / L := by
    rw [div_eq_div_iff hden2 hLne]
    ring
  rw [mul_div_assoc, hscale]
  field_simp

/-! ### 2. The conclusion -/

/-- **The depth is computable from two bands.** The formula is exact, and the two ground energies
determine the depth uniquely. -/
theorem theDepthIsComputableFromTwoBands {L δ : ℝ} (hL : 0 < L) (hδ : 0 < δ) :
    depthFromBands (-(L * latticeFloor L δ 2)) (-(L * latticeFloor L δ 3)) = δ ∧
      ∀ L' δ' : ℝ, 0 < L' → 0 < δ' →
        -(L * latticeFloor L δ 2) = -(L' * latticeFloor L' δ' 2) →
        -(L * latticeFloor L δ 3) = -(L' * latticeFloor L' δ' 3) → δ = δ' :=
  ⟨depthFromBands_eq hL hδ,
    fun _ _ hL' hδ' h2 h3 => depth_determined_by_two_bands hL hδ hL' hδ' h2 h3⟩

-- from TheTwoBandRatioHasSquareRootConditioning.lean
/-! ### 1. The scale-free ratio -/

/-- **The ratio of the two ground energies is `cosh (δL)`**, free of the scale. -/
theorem ratio_eq_cosh {L δ : ℝ} (hL : 0 < L) (hδ : 0 < δ) :
    -(L * latticeFloor L δ 3) / (2 * -(L * latticeFloor L δ 2)) - 1 = Real.cosh (δ * L) := by
  have hx : (0 : ℝ) < δ * L := by positivity
  have hc : (1 : ℝ) < Real.cosh (δ * L) := Real.one_lt_cosh.mpr (ne_of_gt hx)
  have hsq : Real.sinh (δ * L) ^ 2 = Real.cosh (δ * L) ^ 2 - 1 := by
    have := Real.cosh_sq (δ * L)
    linarith
  rw [groundEnergy_index_two hx, groundEnergy_index_three hx, hsq]
  have hden : (2 * (2 * L * (Real.cosh (δ * L) - 1))) ≠ 0 := by
    have hpos : (0 : ℝ) < Real.cosh (δ * L) - 1 := by linarith
    positivity
  have h1 : 4 * L * (Real.cosh (δ * L) ^ 2 - 1) /
      (2 * (2 * L * (Real.cosh (δ * L) - 1))) = Real.cosh (δ * L) + 1 := by
    rw [div_eq_iff hden]
    ring
  rw [h1]
  ring

/-! ### 2. The conditioning -/

/-- **A ratio within `η` of the critical value certifies `δL ≤ √(2η)`.** -/
theorem depth_le_sqrt_of_ratio_le {L δ η : ℝ} (hL : 0 < L) (hδ : 0 < δ) (_hη : 0 ≤ η)
    (h : Real.cosh (δ * L) ≤ 1 + η) : δ * L ≤ Real.sqrt (2 * η) := by
  have hx : (0 : ℝ) ≤ δ * L := by positivity
  have hlow : 1 + (δ * L) ^ 2 / 2 ≤ Real.cosh (δ * L) := one_add_sq_half_le_cosh hx
  have hsq : (δ * L) ^ 2 ≤ 2 * η := by linarith
  calc δ * L = Real.sqrt ((δ * L) ^ 2) := (Real.sqrt_sq hx).symm
    _ ≤ Real.sqrt (2 * η) := Real.sqrt_le_sqrt hsq

/-- In terms of the depth itself. -/
theorem depth_le_sqrt_div_of_ratio_le {L δ η : ℝ} (hL : 0 < L) (hδ : 0 < δ) (hη : 0 ≤ η)
    (h : Real.cosh (δ * L) ≤ 1 + η) : δ ≤ Real.sqrt (2 * η) / L := by
  rw [le_div_iff₀ hL]
  exact depth_le_sqrt_of_ratio_le hL hδ hη h

/-! ### 3. The prescription -/

/-- **The two-band certification.** The depth is an explicit function of the two ground energies,
and resolving their ratio to within `η` of its critical value certifies `δ ≤ √(2η)/L`: the
precision needed to certify depth `β` is of order `β²`. -/
theorem theTwoBandCertification {L δ : ℝ} (hL : 0 < L) (hδ : 0 < δ) :
    depthFromBands (-(L * latticeFloor L δ 2)) (-(L * latticeFloor L δ 3)) = δ ∧
      ∀ η : ℝ, 0 ≤ η →
        -(L * latticeFloor L δ 3) / (2 * -(L * latticeFloor L δ 2)) - 1 ≤ 1 + η →
        δ ≤ Real.sqrt (2 * η) / L :=
  ⟨depthFromBands_eq hL hδ, fun η hη hratio => by
    rw [ratio_eq_cosh hL hδ] at hratio
    exact depth_le_sqrt_div_of_ratio_le hL hδ hη hratio⟩

end GaloisForLFunctions.ScaleSignedIncidenceCriticality
