import GaloisForLFunctions.HTGeometry.MultipleEllipticGammaLogKernel
import Mathlib.Algebra.Polynomial.Div

/-!
# Elliptic-gamma group-to-boundary source fracture

The trigonometric degeneration of the multiplicative elliptic-gamma product is not deletion of an
unlabelled period.  At zero nome the forward double-product face becomes trivial, while precisely
the zero column of the backward face survives and obeys the one-dimensional Pochhammer source
recurrence.

The accompanying universal algebraic theorem isolates the change of source category.  A scaling
endomorphism on a unit coordinate can send that coordinate to `q*x` only when `q` is a unit, so it
cannot specialize to `q = 0`.  After compactifying the orbit coordinate from a Laurent algebra to
a polynomial algebra, zero scaling does extend: it is exactly boundary evaluation, with kernel the
boundary ideal `(X)` and image the constant boundary algebra.

Thus an invertible source action degenerates to a boundary endomorphism rather than remaining an
action of the same group.  The statements here are unconditional finite-product and algebraic
foundations; passage to the locally uniform infinite elliptic-gamma product is kept separate.
-/

open Complex
open scoped BigOperators Polynomial

namespace GaloisForLFunctions

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- At arbitrary multiple-elliptic-Gamma rank, a zero nome kills every numerator-side atom. -/
theorem multipleEllipticGammaForwardArgument_zero_nome_coordinate
    (p : ι → ℂ) (x : ℂ) (q : ι) (n : ι → ℕ)
    (hpq : p q = 0) :
    multipleEllipticGammaForwardArgument p x n = 0 := by
  rw [multipleEllipticGammaForwardArgument,
    Fintype.prod_eq_mul_prod_subtype_ne (fun i => p i ^ (n i + 1)) q, hpq]
  simp

/-- At arbitrary rank, every positive slice in a zero-nome direction vanishes.  Together with
`multipleEllipticGammaBackwardArgument_coordinate_zero`, this leaves exactly the
coordinate-deletion face. -/
theorem multipleEllipticGammaBackwardArgument_zero_nome_coordinate_succ
    (p : ι → ℂ) (x : ℂ) (q : ι) (k : ℕ)
    (m : {i : ι // i ≠ q} → ℕ) (hpq : p q = 0) :
    multipleEllipticGammaBackwardArgument p x
      (multipleEllipticGammaMergeIndex q (k + 1) m) = 0 := by
  rw [multipleEllipticGammaBackwardArgument,
    Fintype.prod_eq_mul_prod_subtype_ne
      (fun i => p i ^ multipleEllipticGammaMergeIndex q (k + 1) m i) q]
  simp [hpq]

/-- Every numerator-side elliptic-gamma argument vanishes when the second nome is zero. -/
theorem ellipticGammaForwardArgument_zero_nome
    (p x : ℂ) (j k : ℕ) :
    ellipticGammaForwardArgument p 0 x j k = 0 := by
  simp [ellipticGammaForwardArgument]

/-- The zero column of the denominator-side face survives zero-nome specialization. -/
theorem ellipticGammaBackwardArgument_zero_nome_zero
    (p x : ℂ) (j : ℕ) :
    ellipticGammaBackwardArgument p 0 x j 0 = p ^ j * x := by
  simp [ellipticGammaBackwardArgument]

/-- Every positive column of the denominator-side face vanishes at zero nome. -/
theorem ellipticGammaBackwardArgument_zero_nome_succ
    (p x : ℂ) (j k : ℕ) :
    ellipticGammaBackwardArgument p 0 x j (k + 1) = 0 := by
  simp [ellipticGammaBackwardArgument]

/-- A finite rectangle of the denominator-side elliptic-gamma product. -/
def finiteEllipticGammaBackwardProduct
    (p q x : ℂ) (J K : ℕ) : ℂ :=
  ∏ j ∈ Finset.range J, ∏ k ∈ Finset.range K,
    (1 - ellipticGammaBackwardArgument p q x j k)

/-- The finite trigonometric Pochhammer boundary left after one nome degenerates. -/
def finiteTrigonometricBoundaryDenominator (p x : ℂ) (J : ℕ) : ℂ :=
  ∏ j ∈ Finset.range J, (1 - p ^ j * x)

/-- Adjoining one exponent appends exactly its boundary factor. -/
theorem finiteTrigonometricBoundaryDenominator_succ
    (p x : ℂ) (J : ℕ) :
    finiteTrigonometricBoundaryDenominator p x (J + 1) =
      finiteTrigonometricBoundaryDenominator p x J * (1 - p ^ J * x) := by
  rw [finiteTrigonometricBoundaryDenominator, Finset.prod_range_succ]
  rfl

/-- At zero nome, a complete finite row retains only its zero-column factor. -/
theorem finiteEllipticGammaBackwardRow_zero_nome
    (p x : ℂ) (j K : ℕ) :
    (∏ k ∈ Finset.range (K + 1),
      (1 - ellipticGammaBackwardArgument p 0 x j k)) =
        1 - p ^ j * x := by
  induction K with
  | zero => simp [ellipticGammaBackwardArgument]
  | succ K ih =>
      rw [show K.succ + 1 = (K + 1) + 1 by omega, Finset.prod_range_succ, ih]
      simp [ellipticGammaBackwardArgument]

/-- **Exact finite source-face collapse.** Every nonempty zero-nome rectangle is the same
one-dimensional trigonometric boundary, independently of its depth in the collapsed direction. -/
theorem finiteEllipticGammaBackwardProduct_zero_nome
    (p x : ℂ) (J K : ℕ) :
    finiteEllipticGammaBackwardProduct p 0 x J (K + 1) =
      finiteTrigonometricBoundaryDenominator p x J := by
  simp only [finiteEllipticGammaBackwardProduct,
    finiteTrigonometricBoundaryDenominator]
  apply Finset.prod_congr rfl
  intro j hj
  exact finiteEllipticGammaBackwardRow_zero_nome p x j K

/-- **Surviving source law.** The zero-nome boundary retains the multiplicative Pochhammer
recurrence; degeneration produces a lower-dimensional constraint rather than erasing the source. -/
theorem finiteTrigonometricBoundaryDenominator_source
    (p x : ℂ) (J : ℕ) :
    finiteTrigonometricBoundaryDenominator p x (J + 1) =
      (1 - x) * finiteTrigonometricBoundaryDenominator p (p * x) J := by
  induction J with
  | zero => simp [finiteTrigonometricBoundaryDenominator]
  | succ J ih =>
      rw [show J.succ + 1 = (J + 1) + 1 by omega,
        finiteTrigonometricBoundaryDenominator_succ, ih,
        finiteTrigonometricBoundaryDenominator_succ]
      rw [pow_succ]
      ring

/-- **Invertible-source obstruction.** If a ring endomorphism scales a unit coordinate by `q`,
then `q` is a unit.  Hence a scaling action on an invertible orbit coordinate cannot specialize
to a nonunit parameter. -/
theorem scaling_image_of_unit_forces_parameter_unit
    {R : Type*} [CommRing R] (phi : R →+* R) {q x : R}
    (hx : IsUnit x) (hscale : phi x = q * x) : IsUnit q := by
  have hqx : IsUnit (q * x) := hscale ▸ hx.map phi
  exact isUnit_of_mul_isUnit_left hqx

/-- In a nontrivial ring, no endomorphism scales a unit coordinate by zero. -/
theorem no_zero_scaling_endomorphism_on_unit_coordinate
    {R : Type*} [CommRing R] [Nontrivial R] (phi : R →+* R) {x : R}
    (hx : IsUnit x) : ¬ phi x = 0 * x := by
  intro hscale
  exact not_isUnit_zero
    (scaling_image_of_unit_forces_parameter_unit phi hx hscale)

/-- Scaling on the polynomial compactification of a multiplicative orbit coordinate. -/
def polynomialScaling {R : Type*} [CommRing R] (q : R) : R[X] →+* R[X] :=
  Polynomial.compRingHom (Polynomial.C q * Polynomial.X)

/-- At zero parameter, polynomial scaling is exactly restriction to the boundary `X = 0`. -/
theorem polynomialScaling_zero_is_boundary
    {R : Type*} [CommRing R] (P : R[X]) :
    polynomialScaling 0 P = Polynomial.C (P.eval 0) := by
  simp [polynomialScaling, Polynomial.comp_zero]

/-- The information lost by zero scaling is exactly the principal boundary ideal `(X)`. -/
theorem polynomialScaling_zero_eq_zero_iff_boundaryIdeal
    {R : Type*} [CommRing R] (P : R[X]) :
    polynomialScaling 0 P = 0 ↔ Polynomial.X ∣ P := by
  rw [polynomialScaling_zero_is_boundary]
  rw [Polynomial.C_eq_zero, ← Polynomial.coeff_zero_eq_eval_zero,
    ← Polynomial.X_dvd_iff]

/-- The zero-scaling image is exactly the constant algebra carried by the boundary. -/
theorem polynomialScaling_zero_range_is_boundary
    {R : Type*} [CommRing R] :
    Set.range (polynomialScaling (R := R) 0) = Set.range Polynomial.C := by
  ext Q
  constructor
  · rintro ⟨P, rfl⟩
    exact ⟨P.eval 0, (polynomialScaling_zero_is_boundary P).symm⟩
  · rintro ⟨c, rfl⟩
    refine ⟨Polynomial.C c, ?_⟩
    simp [polynomialScaling_zero_is_boundary]

end

end GaloisForLFunctions
