import GaloisForLFunctions.HTGeometry.DifferentialIndependence
import Mathlib.Algebra.MvPolynomial.Monad

/-!
# Projective law space of derivation directions

A finite constant family of derivations determines an ordinary derivation in every coefficient
direction.  No commutativity hypothesis is needed.  Rescaling a direction by `a` rescales its
`n`-th jet by `a^n`; hence algebraic differential properties of the jet tower are intrinsically
projective.

This is the unconditional algebraic foundation for the directional hypertranscendence
discriminant.  The Lie bracket of a bracket-closed family is additional law-space structure, not a
prerequisite for the construction below.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {k L ι : Type*} [Field k] [Field L] [Algebra k L]
  [Fintype ι]

/-- The constant linear combination of a finite family of derivations. -/
def directionalDerivation (δ : ι → Derivation k L L) (c : ι → k) :
    Derivation k L L :=
  ∑ i, c i • δ i

@[simp]
theorem directionalDerivation_apply
    (δ : ι → Derivation k L L) (c : ι → k) (x : L) :
    directionalDerivation δ c x = ∑ i, c i • δ i x := by
  classical
  change (∑ i, c i • δ i) x = _
  induction (Finset.univ : Finset ι) using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi, Derivation.add_apply, ih,
        Finset.sum_insert hi, Derivation.smul_apply]

/-- Multiplying all direction coordinates multiplies the resulting derivation. -/
theorem directionalDerivation_smul
    (δ : ι → Derivation k L L) (c : ι → k) (a : k) :
    directionalDerivation δ (a • c) = a • directionalDerivation δ c := by
  classical
  ext x
  simp [directionalDerivation, Finset.smul_sum, smul_smul]

/-- The ordinary jet along one direction in a multi-derivation law space. -/
def directionalJet (δ : ι → Derivation k L L) (c : ι → k)
    (n : ℕ) (x : L) : L :=
  ((directionalDerivation δ c : L → L)^[n]) x

@[simp]
theorem directionalJet_zero
    (δ : ι → Derivation k L L) (c : ι → k) (x : L) :
    directionalJet δ c 0 x = x := by
  simp [directionalJet]

theorem directionalJet_succ
    (δ : ι → Derivation k L L) (c : ι → k) (n : ℕ) (x : L) :
    directionalJet δ c (n + 1) x =
      directionalDerivation δ c (directionalJet δ c n x) := by
  exact Function.iterate_succ_apply' (directionalDerivation δ c) n x

/-- The `n`-jet is homogeneous of degree `n` in the direction.  This theorem uses only
`k`-linearity of each directional derivation, not commutation between the family members. -/
theorem directionalJet_smul
    (δ : ι → Derivation k L L) (c : ι → k) (a : k)
    (n : ℕ) (x : L) :
    directionalJet δ (a • c) n x = a ^ n • directionalJet δ c n x := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [show n + 1 = n.succ by rfl, directionalJet_succ,
        directionalJet_succ, directionalDerivation_smul,
        Derivation.smul_apply, ih, Derivation.map_smul, pow_succ,
        smul_smul]
      rw [mul_comm a (a ^ n)]

/-- Coordinatewise multiplication of polynomial variables. -/
def diagonalCoordinateMap {R σ : Type*} [CommRing R] (u : σ → R) :
    MvPolynomial σ R →+* MvPolynomial σ R :=
  MvPolynomial.eval₂Hom MvPolynomial.C fun i ↦
    MvPolynomial.C (u i) * MvPolynomial.X i

/-- The inverse coordinate multiplication used when every coefficient is nonzero. -/
def diagonalCoordinateMapInv {R σ : Type*} [Field R] (u : σ → R) :
    MvPolynomial σ R →+* MvPolynomial σ R :=
  MvPolynomial.eval₂Hom MvPolynomial.C fun i ↦
    MvPolynomial.C (u i)⁻¹ * MvPolynomial.X i

/-- Multiplying every polynomial coordinate by a nonzero scalar is an injective substitution. -/
theorem diagonalCoordinateMap_injective
    {R σ : Type*} [Field R] (u : σ → R) (hu : ∀ i, u i ≠ 0) :
    Function.Injective (diagonalCoordinateMap u) := by
  have hcomp : (diagonalCoordinateMapInv u).comp (diagonalCoordinateMap u) =
      RingHom.id _ := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [diagonalCoordinateMap, diagonalCoordinateMapInv]
    · intro i
      simp only [RingHom.comp_apply, diagonalCoordinateMap,
        diagonalCoordinateMapInv, MvPolynomial.eval₂Hom_X', map_mul,
        MvPolynomial.eval₂Hom_C, RingHom.id_apply]
      rw [← mul_assoc, ← MvPolynomial.C_mul]
      simp [hu i]
  apply Function.LeftInverse.injective
  intro P
  simpa using RingHom.congr_fun hcomp P

/-- Nonzero diagonal rescalings of the universal polynomial coordinates remain algebraically
independent. -/
theorem algebraicIndependent_diagonalPolynomials
    {R σ : Type*} [Field R] (u : σ → R) (hu : ∀ i, u i ≠ 0) :
    AlgebraicIndependent R
      (fun i ↦ MvPolynomial.C (u i) * MvPolynomial.X i) := by
  rw [algebraicIndependent_iff_injective_aeval]
  have h := diagonalCoordinateMap_injective u hu
  simpa [diagonalCoordinateMap] using h

/-- Algebraic independence is preserved by coordinatewise multiplication by nonzero constants. -/
theorem AlgebraicIndependent.const_mul_coordinates
    {R A σ : Type*} [Field R] [CommRing A] [Algebra R A]
    {x : σ → A} (hx : AlgebraicIndependent R x)
    (u : σ → R) (hu : ∀ i, u i ≠ 0) :
    AlgebraicIndependent R
      (fun i ↦ algebraMap R A (u i) * x i) := by
  have hpoly := algebraicIndependent_diagonalPolynomials u hu
  have h := hx.aeval_of_algebraicIndependent hpoly
  simpa using h

/-- Nonzero diagonal coordinate rescaling preserves and reflects algebraic independence. -/
theorem algebraicIndependent_const_mul_coordinates_iff
    {R A σ : Type*} [Field R] [Field A] [Algebra R A]
    (x : σ → A) (u : σ → R) (hu : ∀ i, u i ≠ 0) :
    AlgebraicIndependent R (fun i ↦ algebraMap R A (u i) * x i) ↔
      AlgebraicIndependent R x := by
  constructor
  · intro hscaled
    have hback := AlgebraicIndependent.const_mul_coordinates hscaled
      (fun i ↦ (u i)⁻¹) (fun i ↦ inv_ne_zero (hu i))
    simpa [mul_assoc, hu] using hback
  · intro hx
    exact AlgebraicIndependent.const_mul_coordinates hx u hu

/-- Algebraic independence of the complete directional jet tower depends only on the projective
direction. -/
theorem directionalJet_algebraicIndependent_smul_iff
    (δ : ι → Derivation k L L) (c : ι → k) {a : k} (ha : a ≠ 0)
    (x : L) :
    AlgebraicIndependent k (fun n ↦ directionalJet δ (a • c) n x) ↔
      AlgebraicIndependent k (fun n ↦ directionalJet δ c n x) := by
  simp_rw [directionalJet_smul]
  simpa [Algebra.smul_def] using
    (algebraicIndependent_const_mul_coordinates_iff
      (fun n ↦ directionalJet δ c n x) (fun n ↦ a ^ n)
      (fun n ↦ pow_ne_zero n ha))

end

end GaloisForLFunctions.HTGeometry
