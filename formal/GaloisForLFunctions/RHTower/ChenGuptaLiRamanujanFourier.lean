import GaloisForLFunctions.RHTower.ChenGuptaLiHZero

open scoped BigOperators

open Finset

noncomputable section

namespace RHTower

/-- A positive CGL character modulus, with its positivity carried by certified data rather than
an undischarged theorem premise. -/
structure CGLPositiveModulus where
  value : ℕ
  positive : 0 < value

instance cglPositiveModulus_neZero (Q : CGLPositiveModulus) : NeZero Q.value :=
  ⟨Nat.ne_of_gt Q.positive⟩

/-- Indicator of the reduced residue classes modulo a CGL modulus. -/
def cglUnitResidueIndicator (Q : CGLPositiveModulus) (a : ZMod Q.value) : ℂ :=
  if IsUnit a then 1 else 0

/-- CGL's finite additive sum over reduced residues, written as a filtered finite sum. -/
def cglRamanujanAdditiveSum (Q : CGLPositiveModulus) (m : ZMod Q.value) : ℂ :=
  ∑ a ∈ Finset.univ.filter IsUnit, ZMod.stdAddChar (a * m)

/-- The same reduced-residue additive sum written with its exact unit indicator. -/
def cglRamanujanAdditiveSumIndicator (Q : CGLPositiveModulus) (m : ZMod Q.value) : ℂ :=
  ∑ a : ZMod Q.value,
    ZMod.stdAddChar (a * m) * cglUnitResidueIndicator Q a

/-- The reduced-residue additive sum equals its all-residue unit-indicator expansion. -/
theorem cglRamanujanAdditiveSum_eq_indicator
    (Q : CGLPositiveModulus) (m : ZMod Q.value) :
    cglRamanujanAdditiveSum Q m = cglRamanujanAdditiveSumIndicator Q m := by
  classical
  unfold cglRamanujanAdditiveSum cglRamanujanAdditiveSumIndicator
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro a ha
  unfold cglUnitResidueIndicator
  by_cases hau : IsUnit a <;> simp [hau]

/-- The finite character sum in CGL Lemma 4.4 is exactly the DFT of the unit-residue indicator.
The negated frequency is forced by Mathlib's DFT convention. -/
theorem cglRamanujanAdditiveSum_eq_dft_unitIndicator
    (Q : CGLPositiveModulus) (m : ZMod Q.value) :
    cglRamanujanAdditiveSum Q m = ZMod.dft (cglUnitResidueIndicator Q) (-m) := by
  rw [cglRamanujanAdditiveSum_eq_indicator, ZMod.dft_apply]
  apply Finset.sum_congr rfl
  intro a ha
  unfold cglUnitResidueIndicator
  by_cases hau : IsUnit a
  · simp only [if_pos hau, smul_eq_mul, mul_one]
    congr 1
    ring
  · simp [hau]

end RHTower
