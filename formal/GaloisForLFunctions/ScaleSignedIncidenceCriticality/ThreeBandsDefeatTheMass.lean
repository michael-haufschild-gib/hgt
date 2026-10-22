import GaloisForLFunctions.ScaleSignedIncidenceCriticality.TwoAliasingBandsDetermineTheDepth
import GaloisForLFunctions.ScaleSignedIncidenceCriticality.TheResolutionLimitOfAReading
import GaloisForLFunctions.SquareRootThreshold.IsolatedOffLinePairVisibilityLaw

/-!
# Three bands defeat the mass, and one doubling reads a pair

A real configuration carries on-line mass, which adds an unknown and shifts every measured deficit
by the same constant. Two bands are then underdetermined; three are not, and the inversion stays
elementary.

With `x = δℓ` and `c = cosh x` the deficits at the first three nontrivial indices are
`t₂ = 2ℓ(c − 1) − 2L`, `t₃ = 4ℓ(c² − 1) − 2L`, `t₄ = ℓ(8c³ − 4c − 4) − 2L`. Consecutive differences
cancel the mass and their ratio cancels the dilution as well:

`(t₄ − t₃)/(t₃ − t₂) = 2 cosh(δℓ)`   (`difference_ratio_eq`),

so three deficits determine the depth with the mass unknown (`depth_determined_by_three_bands`).
Against `TheHidingLaws` — where mass buys an exponential amount of hiding — this says mass buys
nothing at all against a mechanism that measures one more band. Each unknown of the configuration
costs exactly one aliasing index.

The same move works on a single off-line pair, where the aperture axis is continuous and there are
no bands. The pair's window moment `M(a) = S(a) + a = sinh(2δa)/(2δ)` satisfies
`M(2a)/M(a) = 2cosh(2δa)` (`pairMoment_doubling`), hence

`δ = arcosh(M(2a)/(2M(a)))/(2a)`   (`depth_from_doubling`),

and the on-line mass cancels between the two apertures (`gain_difference_eq`). One aperture doubling
reads the depth of a pair; two or three bands read the depth of a lattice. In every case the
mechanism is a ratio of magnitudes, never a sign.
-/

open Set
open GaloisForLFunctions.SquareRootThreshold
open Zeta23 _root_.RHTower

namespace GaloisForLFunctions.ScaleSignedIncidenceCriticality

set_option autoImplicit false


/-- The off-line ground energy at aliasing index `n`. -/
noncomputable def bandEnergy (ℓ δ : ℝ) (n : ℕ) : ℝ := -(ℓ * latticeFloor ℓ δ n)

theorem bandEnergy_eq {ℓ δ : ℝ} (hδℓ : 0 < δ * ℓ) (n : ℕ) :
    bandEnergy ℓ δ n = ℓ * (Real.sinh ((n : ℝ) * (δ * ℓ)) / Real.sinh (δ * ℓ) - n) := by
  rw [bandEnergy, latticeFloor_eq hδℓ n]
  ring

-- from ThreeBandsDefeatTheMass.lean
/-! ### 1. The three deficits -/

/-- The deficit measured at aliasing index `n`: the off-line ground energy less the on-line mass. -/
noncomputable def bandDeficit (ℓ δ L : ℝ) (n : ℕ) : ℝ := -(ℓ * latticeFloor ℓ δ n) - 2 * L

theorem bandDeficit_two {ℓ δ L : ℝ} (hδℓ : 0 < δ * ℓ) :
    bandDeficit ℓ δ L 2 = 2 * ℓ * (Real.cosh (δ * ℓ) - 1) - 2 * L := by
  rw [bandDeficit, groundEnergy_index_two hδℓ]

theorem bandDeficit_three {ℓ δ L : ℝ} (hδℓ : 0 < δ * ℓ) :
    bandDeficit ℓ δ L 3 = 4 * ℓ * (Real.cosh (δ * ℓ) ^ 2 - 1) - 2 * L := by
  have hsq : Real.sinh (δ * ℓ) ^ 2 = Real.cosh (δ * ℓ) ^ 2 - 1 := by
    have := Real.cosh_sq (δ * ℓ)
    linarith
  rw [bandDeficit, groundEnergy_index_three hδℓ, hsq]

/-- At the fourth index, from `sinh 4x = 4 sinh x cosh x (2cosh²x − 1)`. -/
theorem bandDeficit_four {ℓ δ L : ℝ} (hδℓ : 0 < δ * ℓ) :
    bandDeficit ℓ δ L 4 =
      ℓ * (8 * Real.cosh (δ * ℓ) ^ 3 - 4 * Real.cosh (δ * ℓ) - 4) - 2 * L := by
  have hs : Real.sinh (δ * ℓ) ≠ 0 := ne_of_gt (Real.sinh_pos_iff.mpr hδℓ)
  have h4 : ((4 : ℕ) : ℝ) * (δ * ℓ) = 2 * (2 * (δ * ℓ)) := by push_cast; ring
  have hpy : Real.sinh (δ * ℓ) ^ 2 = Real.cosh (δ * ℓ) ^ 2 - 1 := by
    have := Real.cosh_sq (δ * ℓ)
    linarith
  have hsinh4 : Real.sinh (2 * (2 * (δ * ℓ))) =
      4 * Real.sinh (δ * ℓ) * Real.cosh (δ * ℓ) * (2 * Real.cosh (δ * ℓ) ^ 2 - 1) := by
    rw [Real.sinh_two_mul, Real.sinh_two_mul, Real.cosh_two_mul, hpy]
    ring
  rw [bandDeficit, latticeFloor_eq hδℓ 4, h4, hsinh4]
  have hdiv : 4 * Real.sinh (δ * ℓ) * Real.cosh (δ * ℓ) * (2 * Real.cosh (δ * ℓ) ^ 2 - 1) /
      Real.sinh (δ * ℓ) =
      8 * Real.cosh (δ * ℓ) ^ 3 - 4 * Real.cosh (δ * ℓ) := by
    field_simp
    ring
  rw [hdiv]
  push_cast
  ring

/-! ### 2. The mass cancels in differences -/

/-- **The ratio of consecutive differences is `2 cosh x`** — free of the mass and of the
dilution. -/
theorem difference_ratio_eq {ℓ δ L : ℝ} (hℓ : 0 < ℓ) (hδ : 0 < δ) :
    (bandDeficit ℓ δ L 4 - bandDeficit ℓ δ L 3) /
        (bandDeficit ℓ δ L 3 - bandDeficit ℓ δ L 2) = 2 * Real.cosh (δ * ℓ) := by
  have hx : (0 : ℝ) < δ * ℓ := by positivity
  have hc : (1 : ℝ) < Real.cosh (δ * ℓ) := Real.one_lt_cosh.mpr (ne_of_gt hx)
  rw [bandDeficit_two hx, bandDeficit_three hx, bandDeficit_four hx]
  have hden : 2 * ℓ * (Real.cosh (δ * ℓ) - 1) * (2 * Real.cosh (δ * ℓ) + 1) ≠ 0 := by
    have h1 : (0 : ℝ) < Real.cosh (δ * ℓ) - 1 := by linarith
    have h2 : (0 : ℝ) < 2 * Real.cosh (δ * ℓ) + 1 := by linarith
    positivity
  rw [div_eq_iff (by
    have h1 : (0 : ℝ) < Real.cosh (δ * ℓ) - 1 := by linarith
    have h2 : (0 : ℝ) < 2 * Real.cosh (δ * ℓ) + 1 := by linarith
    have : (0 : ℝ) < 2 * ℓ * (Real.cosh (δ * ℓ) - 1) * (2 * Real.cosh (δ * ℓ) + 1) := by
      positivity
    intro hz
    nlinarith [this, hz])]
  ring

/-! ### 3. The inversion -/

/-- **Three bands determine the depth**, with the on-line mass unknown. -/
theorem depth_determined_by_three_bands {ℓ δ L ℓ' δ' L' : ℝ} (hℓ : 0 < ℓ) (hδ : 0 < δ)
    (hℓ' : 0 < ℓ') (hδ' : 0 < δ')
    (h2 : bandDeficit ℓ δ L 2 = bandDeficit ℓ' δ' L' 2)
    (h3 : bandDeficit ℓ δ L 3 = bandDeficit ℓ' δ' L' 3)
    (h4 : bandDeficit ℓ δ L 4 = bandDeficit ℓ' δ' L' 4) : δ = δ' := by
  have hx : (0 : ℝ) < δ * ℓ := by positivity
  have hx' : (0 : ℝ) < δ' * ℓ' := by positivity
  have hc : (1 : ℝ) < Real.cosh (δ * ℓ) := Real.one_lt_cosh.mpr (ne_of_gt hx)
  have hc' : (1 : ℝ) < Real.cosh (δ' * ℓ') := Real.one_lt_cosh.mpr (ne_of_gt hx')
  -- the ratio of consecutive differences agrees, hence `cosh x = cosh x'`
  have hcosh : Real.cosh (δ * ℓ) = Real.cosh (δ' * ℓ') := by
    have hr := difference_ratio_eq (L := L) hℓ hδ
    have hr' := difference_ratio_eq (L := L') hℓ' hδ'
    rw [h2, h3, h4] at hr
    rw [hr'] at hr
    linarith
  -- the first difference then gives the dilution
  have hdiff : 2 * ℓ * (Real.cosh (δ * ℓ) - 1) * (2 * Real.cosh (δ * ℓ) + 1) =
      2 * ℓ' * (Real.cosh (δ' * ℓ') - 1) * (2 * Real.cosh (δ' * ℓ') + 1) := by
    have e1 : bandDeficit ℓ δ L 3 - bandDeficit ℓ δ L 2 =
        2 * ℓ * (Real.cosh (δ * ℓ) - 1) * (2 * Real.cosh (δ * ℓ) + 1) := by
      rw [bandDeficit_two hx, bandDeficit_three hx]; ring
    have e2 : bandDeficit ℓ' δ' L' 3 - bandDeficit ℓ' δ' L' 2 =
        2 * ℓ' * (Real.cosh (δ' * ℓ') - 1) * (2 * Real.cosh (δ' * ℓ') + 1) := by
      rw [bandDeficit_two hx', bandDeficit_three hx']; ring
    rw [← e1, ← e2, h2, h3]
  have hll : ℓ = ℓ' := by
    rw [hcosh] at hdiff
    have hfac : (0 : ℝ) < 2 * (Real.cosh (δ' * ℓ') - 1) * (2 * Real.cosh (δ' * ℓ') + 1) := by
      have h1 : (0 : ℝ) < Real.cosh (δ' * ℓ') - 1 := by linarith
      have h2' : (0 : ℝ) < 2 * Real.cosh (δ' * ℓ') + 1 := by linarith
      positivity
    nlinarith [hdiff, hfac]
  -- and then the depth
  have hxx : δ * ℓ = δ' * ℓ' := by
    rcases lt_trichotomy (δ * ℓ) (δ' * ℓ') with hlt | heq | hgt
    · have hlt' : Real.cosh (δ * ℓ) < Real.cosh (δ' * ℓ') := by
        rw [Real.cosh_lt_cosh, abs_of_pos hx, abs_of_pos hx']
        exact hlt
      linarith [hcosh, hlt']
    · exact heq
    · have hgt' : Real.cosh (δ' * ℓ') < Real.cosh (δ * ℓ) := by
        rw [Real.cosh_lt_cosh, abs_of_pos hx', abs_of_pos hx]
        exact hgt
      linarith [hcosh, hgt']
  rw [hll] at hxx
  exact mul_right_cancel₀ (ne_of_gt hℓ') hxx

/-! ### 4. The conclusion -/

/-- **Three bands defeat the mass.** Consecutive differences cancel the on-line mass, their ratio
cancels the dilution, and the three deficits determine the depth. -/
theorem threeBandsDefeatTheMass {ℓ δ L : ℝ} (hℓ : 0 < ℓ) (hδ : 0 < δ) :
    (bandDeficit ℓ δ L 4 - bandDeficit ℓ δ L 3) /
        (bandDeficit ℓ δ L 3 - bandDeficit ℓ δ L 2) = 2 * Real.cosh (δ * ℓ) ∧
      ∀ ℓ' δ' L' : ℝ, 0 < ℓ' → 0 < δ' →
        bandDeficit ℓ δ L 2 = bandDeficit ℓ' δ' L' 2 →
        bandDeficit ℓ δ L 3 = bandDeficit ℓ' δ' L' 3 →
        bandDeficit ℓ δ L 4 = bandDeficit ℓ' δ' L' 4 → δ = δ' :=
  ⟨difference_ratio_eq hℓ hδ,
    fun _ _ _ hℓ' hδ' h2 h3 h4 => depth_determined_by_three_bands hℓ hδ hℓ' hδ' h2 h3 h4⟩

-- from TheApertureDoublingLawForAnIsolatedPair.lean
/-! ### 1. The pair's window moment -/

/-- The pair's window moment: its energy plus the aperture length. -/
noncomputable def pairMoment (δ a : ℝ) : ℝ := pairEnergy δ a + a

theorem pairMoment_eq (δ a : ℝ) : pairMoment δ a = Real.sinh (2 * δ * a) / (2 * δ) := by
  rw [pairMoment, pairEnergy]
  ring

theorem pairMoment_pos {δ a : ℝ} (hδ : 0 < δ) (ha : 0 < a) : 0 < pairMoment δ a := by
  rw [pairMoment_eq]
  have h : (0 : ℝ) < 2 * δ * a := by positivity
  exact div_pos (Real.sinh_pos_iff.mpr h) (by positivity)

/-! ### 2. The doubling law -/

/-- **The doubling law**: the moment at twice the aperture is `2cosh(2δa)` times the moment. -/
theorem pairMoment_doubling {δ a : ℝ} (hδ : 0 < δ) (ha : 0 < a) :
    pairMoment δ (2 * a) / pairMoment δ a = 2 * Real.cosh (2 * δ * a) := by
  have hq : Real.sinh (2 * δ * a) / (2 * δ) ≠ 0 := by
    have h1 : (0 : ℝ) < Real.sinh (2 * δ * a) := Real.sinh_pos_iff.mpr (by positivity)
    have h2 : (0 : ℝ) < 2 * δ := by positivity
    exact ne_of_gt (div_pos h1 h2)
  have hdouble : Real.sinh (2 * δ * (2 * a)) =
      2 * Real.sinh (2 * δ * a) * Real.cosh (2 * δ * a) := by
    rw [show 2 * δ * (2 * a) = 2 * (2 * δ * a) by ring, Real.sinh_two_mul]
  have key : Real.sinh (2 * δ * (2 * a)) / (2 * δ) =
      2 * Real.cosh (2 * δ * a) * (Real.sinh (2 * δ * a) / (2 * δ)) := by
    rw [hdouble]
    ring
  rw [pairMoment_eq, pairMoment_eq, key, mul_div_cancel_right₀ _ hq]

/-- **The depth from one doubling.** -/
theorem depth_from_doubling {δ a : ℝ} (hδ : 0 < δ) (ha : 0 < a) :
    Real.arcosh (pairMoment δ (2 * a) / pairMoment δ a / 2) / (2 * a) = δ := by
  rw [pairMoment_doubling hδ ha]
  have h2 : 2 * Real.cosh (2 * δ * a) / 2 = Real.cosh (2 * δ * a) := by ring
  rw [h2, Real.arcosh_cosh (by positivity)]
  field_simp

/-- Equal doubling ratios at a common aperture force equal depths. -/
theorem depth_eq_of_doubling_eq {δ δ' a : ℝ} (hδ : 0 < δ) (hδ' : 0 < δ') (ha : 0 < a)
    (h : pairMoment δ (2 * a) / pairMoment δ a = pairMoment δ' (2 * a) / pairMoment δ' a) :
    δ = δ' := by
  rw [← depth_from_doubling hδ ha, ← depth_from_doubling hδ' ha, h]

/-! ### 3. The mass cancels between two apertures -/

/-- **The on-line mass cancels in an aperture difference.** The pair's gain is `2(L − S(a))`, so the
difference of the gains at two apertures is the difference of the energies alone. -/
theorem gain_difference_eq (L δ a b : ℝ) :
    2 * (L - pairEnergy δ a) - 2 * (L - pairEnergy δ b) =
      2 * (pairEnergy δ b - pairEnergy δ a) := by ring

/-- In moment form: the measured difference at `a` and `2a` is the moment difference, shifted by the
known aperture lengths. -/
theorem moment_difference_from_gains (L δ a : ℝ) :
    2 * (L - pairEnergy δ a) - 2 * (L - pairEnergy δ (2 * a)) =
      2 * (pairMoment δ (2 * a) - pairMoment δ a) - 2 * a := by
  simp only [pairMoment]
  ring

/-! ### 4. The prescription on the pair face -/

/-- **The pair-face prescription.** One aperture doubling gives the depth in closed form, and the
on-line mass cancels between the two apertures. -/
theorem theApertureDoublingPrescription {δ a : ℝ} (hδ : 0 < δ) (ha : 0 < a) :
    pairMoment δ (2 * a) / pairMoment δ a = 2 * Real.cosh (2 * δ * a) ∧
      Real.arcosh (pairMoment δ (2 * a) / pairMoment δ a / 2) / (2 * a) = δ ∧
      ∀ L : ℝ, 2 * (L - pairEnergy δ a) - 2 * (L - pairEnergy δ (2 * a)) =
        2 * (pairMoment δ (2 * a) - pairMoment δ a) - 2 * a :=
  ⟨pairMoment_doubling hδ ha, depth_from_doubling hδ ha,
    fun L => moment_difference_from_gains L δ a⟩

end GaloisForLFunctions.ScaleSignedIncidenceCriticality
