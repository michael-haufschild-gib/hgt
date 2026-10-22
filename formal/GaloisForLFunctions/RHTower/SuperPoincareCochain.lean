import GaloisForLFunctions.HTGeometry.SuperPoincareAlgebra
import GaloisForLFunctions.RHTower.Deninger.DeningerArithmeticCochainComplex

noncomputable section

namespace RHTower

/-- The total space of the closed three-term Deninger arithmetic cochain complex. -/
abbrev DeningerArithmeticTotalCochain :=
  DeningerArithmeticC0 × (DeningerArithmeticC1 × DeningerArithmeticC2)

/-- The cochain differential, viewed on the total space. -/
def deningerArithmeticTotalDifferential :
    Module.End ℂ DeningerArithmeticTotalCochain where
  toFun x := (0, (deningerArithmeticD0 x.1, deningerArithmeticD1 x.2.1))
  map_add' x y := by
    ext <;> simp
  map_smul' c x := by
    ext <;> simp

/-- Degree parity on the total Deninger arithmetic cochain space. -/
def deningerArithmeticTotalParity :
    Module.End ℂ DeningerArithmeticTotalCochain where
  toFun x := (x.1, (-x.2.1, x.2.2))
  map_add' x y := by
    ext <;> simp [add_comm]
  map_smul' c x := by
    ext <;> simp

theorem deningerArithmeticTotalDifferential_sq :
    deningerArithmeticTotalDifferential * deningerArithmeticTotalDifferential = 0 := by
  apply LinearMap.ext
  rintro ⟨x0, x1, x2⟩
  change deningerArithmeticTotalDifferential
    (deningerArithmeticTotalDifferential (x0, (x1, x2))) =
      (0 : DeningerArithmeticTotalCochain)
  simp [deningerArithmeticTotalDifferential, deningerArithmeticD1]

theorem deningerArithmeticTotalParity_sq :
    deningerArithmeticTotalParity * deningerArithmeticTotalParity = 1 := by
  apply LinearMap.ext
  rintro ⟨x0, x1, x2⟩
  ext <;> simp [deningerArithmeticTotalParity]

theorem deningerArithmeticTotalDifferential_mul_parity_eq_neg :
    deningerArithmeticTotalDifferential * deningerArithmeticTotalParity =
      -(deningerArithmeticTotalParity * deningerArithmeticTotalDifferential) := by
  apply LinearMap.ext
  rintro ⟨x0, x1, x2⟩
  ext <;> simp [deningerArithmeticTotalDifferential, deningerArithmeticTotalParity]

/-- Closed `D = 1`, `N = 2` split: cochain differential and degree parity anticommute. -/
def deningerArithmeticCochainD1N2Split :
    SuperPoincare.D1N2Split (Module.End ℂ DeningerArithmeticTotalCochain) :=
  SuperPoincare.D1N2Split.ofEqNeg
    deningerArithmeticTotalDifferential deningerArithmeticTotalParity
    deningerArithmeticTotalDifferential_mul_parity_eq_neg

theorem deningerArithmeticCochain_momentum0_eq_zero :
    deningerArithmeticCochainD1N2Split.momentum0 = 0 :=
  deningerArithmeticTotalDifferential_sq

theorem deningerArithmeticCochain_momentum1_eq_one :
    deningerArithmeticCochainD1N2Split.momentum1 = 1 :=
  deningerArithmeticTotalParity_sq

end RHTower
