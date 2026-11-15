import GaloisForLFunctions.RHTower.GL3Plucker
import Mathlib.RingTheory.Valuation.ValuationSubring

/-!
# Plücker weights and integral height invariance on the open SL₃ cell

The bottom-row and exterior-square coordinates of `w₀ n(a,b,c)` are
`(1,a,c)` and `(ab-c,-b,1)`. The root scaling `(a,b,c) ↦ (λa,μb,λμc)`
gives their exact weights. Their valuation maxima are unchanged by right
translation by integral upper unipotents, so their product descends to the
integral unipotent quotient.
-/

namespace GaloisForLFunctions.BiarithmeticGeometry
noncomputable section

open Matrix
open GaloisForLFunctions.RHTower.GL3

section Coordinates
variable {R : Type*} [CommRing R]

/-- The longest-Weyl open cell, using the existing upper unipotent coordinates. -/
def sl3PluckerCell (a b c : R) : Matrix (Fin 3) (Fin 3) R :=
  !![0, 0, 1; 0, -1, 0; 1, 0, 0] * unip b a c

theorem sl3PluckerCell_botRow (a b c : R) :
    botRow (sl3PluckerCell a b c) = ![1, a, c] := by
  ext i
  fin_cases i <;> simp [sl3PluckerCell, botRow, unip, Matrix.mul_apply, Fin.sum_univ_three]

theorem sl3PluckerCell_plk (a b c : R) :
    plk (sl3PluckerCell a b c) = ![a * b - c, -b, 1] := by
  ext i
  fin_cases i <;> simp [sl3PluckerCell, plk, unip, Matrix.mul_apply, Fin.sum_univ_three]
  all_goals ring

/-- These open-cell coordinates have determinant one over every commutative ring. -/
theorem sl3PluckerCell_det (a b c : R) : (sl3PluckerCell a b c).det = 1 := by
  rw [det_eq_row0_dot_plk, sl3PluckerCell_plk]
  simp [sl3PluckerCell, unip, dotProduct, Matrix.mul_apply, Fin.sum_univ_three]

/-- The standard coordinates have root weights `1`, `λ`, and `λμ`. -/
theorem sl3PluckerCell_botRow_homogeneous (a b c lam mu : R) :
    botRow (sl3PluckerCell (lam * a) (mu * b) (lam * mu * c)) =
      ![botRow (sl3PluckerCell a b c) 0, lam * botRow (sl3PluckerCell a b c) 1,
        lam * mu * botRow (sl3PluckerCell a b c) 2] := by
  simp only [sl3PluckerCell_botRow]
  rfl

/-- The exterior-square coordinates have root weights `λμ`, `μ`, and `1`. -/
theorem sl3PluckerCell_plk_homogeneous (a b c lam mu : R) :
    plk (sl3PluckerCell (lam * a) (mu * b) (lam * mu * c)) =
      ![lam * mu * plk (sl3PluckerCell a b c) 0,
        mu * plk (sl3PluckerCell a b c) 1, plk (sl3PluckerCell a b c) 2] := by
  simp only [sl3PluckerCell_plk]
  ext i
  fin_cases i <;> simp
  all_goals ring

/-- Right multiplication is the Heisenberg translation of the three root coordinates. -/
theorem sl3PluckerCell_mul_unip (a b c x y z : R) :
    sl3PluckerCell a b c * unip y x z =
      sl3PluckerCell (a + x) (b + y) (c + a * y + z) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sl3PluckerCell, unip, Matrix.mul_apply, Fin.sum_univ_three] <;> ring

end Coordinates

section Height
variable {K Γ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ]

/-- The valuation maximum of an affine row `(1,a,c)`. -/
def affinePluckerHeight (v : Valuation K Γ) (a c : K) : Γ := max 1 (max (v a) (v c))

private theorem affinePluckerHeight_translate_le (v : Valuation K Γ) (a c : K)
    (x y z : v.valuationSubring) :
    affinePluckerHeight v (a + x) (c + a * y + z) ≤ affinePluckerHeight v a c := by
  have hx : v (x : K) ≤ 1 := x.property
  have hy : v (y : K) ≤ 1 := y.property
  have hz : v (z : K) ≤ 1 := z.property
  have hone : 1 ≤ affinePluckerHeight v a c := le_max_left _ _
  have ha : v a ≤ affinePluckerHeight v a c := (le_max_left _ _).trans (le_max_right _ _)
  have hc : v c ≤ affinePluckerHeight v a c := (le_max_right _ _).trans (le_max_right _ _)
  apply max_le hone
  apply max_le
  · exact (v.map_add _ _).trans (max_le ha (hx.trans hone))
  · apply (v.map_add _ _).trans
    apply max_le _ (hz.trans hone)
    apply (v.map_add _ _).trans
    apply max_le hc
    rw [map_mul]
    exact (mul_le_mul' (le_refl (v a)) hy).trans (by simpa only [mul_one] using ha)

/-- The inverse integral shear proves exact invariance of the affine row height. -/
theorem affinePluckerHeight_integral_translate (v : Valuation K Γ) (a c : K)
    (x y z : v.valuationSubring) :
    affinePluckerHeight v (a + x) (c + a * y + z) = affinePluckerHeight v a c := by
  apply le_antisymm (affinePluckerHeight_translate_le v a c x y z)
  have h := affinePluckerHeight_translate_le v (a + x) (c + a * y + z)
    (-x) (-y) (x * y - z)
  have hfirst : a + (x : K) + ↑(-x) = a := by simp
  have hlast : (c + a * (y : K) + z) + (a + x) * ↑(-y) + ↑(x * y - z) = c := by
    change (c + a * (y : K) + z) + (a + x) * (-(y : K)) + ((x : K) * y - z) = c
    ring
  rw [hfirst, hlast] at h
  exact h

/-- Product of the two fundamental Plücker heights. -/
def sl3PluckerHeight (v : Valuation K Γ) (a b c : K) : Γ :=
  affinePluckerHeight v a c * affinePluckerHeight v b (a * b - c)

/-- The formula is the product of the maxima of the actual fundamental coordinates. -/
theorem sl3PluckerHeight_eq_coordinate_maxima (v : Valuation K Γ) (a b c : K) :
    sl3PluckerHeight v a b c =
      max (v (botRow (sl3PluckerCell a b c) 0))
        (max (v (botRow (sl3PluckerCell a b c) 1)) (v (botRow (sl3PluckerCell a b c) 2))) *
      max (v (plk (sl3PluckerCell a b c) 0))
        (max (v (plk (sl3PluckerCell a b c) 1)) (v (plk (sl3PluckerCell a b c) 2))) := by
  simp [sl3PluckerHeight, affinePluckerHeight, sl3PluckerCell_botRow,
    sl3PluckerCell_plk, max_comm, max_left_comm]

/-- Both coordinate maxima, hence their product, descend through integral unipotent translation. -/
theorem sl3PluckerHeight_integral_translate (v : Valuation K Γ) (a b c : K)
    (x y z : v.valuationSubring) :
    sl3PluckerHeight v (a + x) (b + y) (c + a * y + z) = sl3PluckerHeight v a b c := by
  have hcross : (a + (x : K)) * (b + y) - (c + a * y + z) =
      (a * b - c) + b * x + ↑(x * y - z) := by
    change (a + (x : K)) * (b + y) - (c + a * y + z) =
      (a * b - c) + b * x + ((x : K) * y - z)
    ring
  rw [sl3PluckerHeight, hcross,
    affinePluckerHeight_integral_translate v a c x y z,
    affinePluckerHeight_integral_translate v b (a * b - c) y x (x * y - z)]
  rfl

/-- The normalized coordinates force both fundamental heights to be at least one. -/
theorem one_le_sl3PluckerHeight (v : Valuation K Γ) (a b c : K) :
    1 ≤ sl3PluckerHeight v a b c := by
  simpa only [sl3PluckerHeight, affinePluckerHeight, one_mul] using mul_le_mul'
    (le_max_left 1 (max (v a) (v c)))
    (le_max_left 1 (max (v b) (v (a * b - c))))

end Height

#print axioms sl3PluckerCell_plk_homogeneous
#print axioms sl3PluckerCell_det
#print axioms sl3PluckerCell_mul_unip
#print axioms sl3PluckerHeight_eq_coordinate_maxima
#print axioms sl3PluckerHeight_integral_translate

end
end GaloisForLFunctions.BiarithmeticGeometry
