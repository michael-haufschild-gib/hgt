import GaloisForLFunctions.HTGeometry.PolynomialODEEvenCompactMomentZero
import GaloisForLFunctions.HTGeometry.PolynomialODEEvenCompactMomentOne
import GaloisForLFunctions.HTGeometry.PolynomialODEEvenCompactMomentTwo
import GaloisForLFunctions.HTGeometry.PolynomialODEEvenCompactMomentThree
import GaloisForLFunctions.HTGeometry.PolynomialODEEvenCompactMomentFour
import GaloisForLFunctions.HTGeometry.PolynomialODEEvenCompactMomentFive
import GaloisForLFunctions.HTGeometry.PolynomialODEEvenCompactMomentSix
import GaloisForLFunctions.HTGeometry.HankelFourDeterminant

/-! # The exact coupled even four-by-four source model -/
namespace HTGeometry
noncomputable section
open GaloisForLFunctions.HTGeometry

/-- Seven signed source moments in the full modular chart. -/
def evenCompactSignedMoment (k : Fin 7) (u a w : ℝ) : ℝ :=
  match k.val with
  | 0 => (oddCompactSourceZero u a)^(2 : ℕ)
  | 1 => (-1 : ℝ)^(1 : ℕ)*oddCompactReflectedScalar2 u a w
  | 2 => (-1 : ℝ)^(2 : ℕ)*oddCompactReflectedScalar4 u a w
  | 3 => (-1 : ℝ)^(3 : ℕ)*oddCompactReflectedScalar6 u a w
  | 4 => (-1 : ℝ)^(4 : ℕ)*oddCompactReflectedScalar8 u a w
  | 5 => (-1 : ℝ)^(5 : ℕ)*oddCompactReflectedScalar10 u a w
  | _ => evenCompactReflectedScalar12 u a w

/-- Seven moments after the proved coupled-coordinate substitution and fixed balancing. -/
def evenCompactUnitMoment (k : Fin 7) (r t v : ℝ) : ℝ :=
  match k.val with
  | 0 => evenCompactUnitMomentZero r t v
  | 1 => evenCompactUnitMomentOne r t v
  | 2 => evenCompactUnitMomentTwo r t v
  | 3 => evenCompactUnitMomentThree r t v
  | 4 => evenCompactUnitMomentFour r t v
  | 5 => evenCompactUnitMomentFive r t v
  | _ => evenCompactUnitMomentSix r t v

/-- The exact finite-coordinate identity holds for every real state. -/
theorem evenCompactSignedMoment_unit_eq (k : Fin 7) (u t v : ℝ) :
    evenCompactSignedMoment k u (evenCompactUnitGap (u^(2 : ℕ)) t) (u*(1+v/4))/(100 : ℝ)^k.val =
      evenCompactUnitMoment k (u^(2 : ℕ)) t v := by
  fin_cases k
  · simpa [evenCompactSignedMoment, evenCompactUnitMoment] using evenCompactUnitMomentZero_eq u t v
  · simpa [evenCompactSignedMoment, evenCompactUnitMoment] using evenCompactUnitMomentOne_eq u t v
  · simpa [evenCompactSignedMoment, evenCompactUnitMoment] using evenCompactUnitMomentTwo_eq u t v
  · simpa [evenCompactSignedMoment, evenCompactUnitMoment] using evenCompactUnitMomentThree_eq u t v
  · simpa [evenCompactSignedMoment, evenCompactUnitMoment] using evenCompactUnitMomentFour_eq u t v
  · simpa [evenCompactSignedMoment, evenCompactUnitMoment] using evenCompactUnitMomentFive_eq u t v
  · have h := evenCompactUnitMomentSix_eq u t v
    norm_num at h
    norm_num [evenCompactSignedMoment, evenCompactUnitMoment]
    exact h

/-- Full four-by-four determinant, with the proved even correction lower comparison in its last entry. -/
def evenCompactUnitDet (r t v : ℝ) : ℝ :=
  hankelFourDet (evenCompactUnitMoment 0 r t v) (evenCompactUnitMoment 1 r t v)
    (evenCompactUnitMoment 2 r t v) (evenCompactUnitMoment 3 r t v)
    (evenCompactUnitMoment 4 r t v) (evenCompactUnitMoment 5 r t v)
    (evenCompactUnitMoment 6 r t v+evenCompactUnitCorrection r t)

end
end HTGeometry
