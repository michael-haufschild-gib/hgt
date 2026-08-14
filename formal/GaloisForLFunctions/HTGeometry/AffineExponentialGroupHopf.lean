import Mathlib.RingTheory.Bialgebra.SymmetricAlgebra
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.HopfAlgebra.MonoidAlgebra
import Mathlib.RingTheory.HopfAlgebra.TensorProduct
import Mathlib.Algebra.MvPolynomial.Nilpotent
import Mathlib.LinearAlgebra.SymmetricAlgebra.Basis
import Mathlib.RingTheory.TensorProduct.MonoidAlgebra

/-!
# Hopf coordinates for additive-exponential algebraic groups

This file supplies the concrete commutative Hopf algebras needed to study algebraic subgroups of
`Gₐⁿ × Gₘⁿ`.  It constructs the missing antipode on a symmetric algebra, identifies the additive
coordinates as primitive and torus characters as group-like, and proves the two cross-factor
rigidity theorems

* `Hom(Gₐ, Gₘ) = 0`, and
* `Hom(Gₘ, Gₐ) = 0`

directly in contravariant Hopf coordinates.  The second theorem rests on a coefficientwise
classification: the only primitive Laurent polynomial is zero.
-/

open scoped TensorProduct
open Coalgebra Bialgebra HopfAlgebra

namespace GaloisForLFunctions.HTGeometry

namespace AdditiveSymmetricHopf

noncomputable section

variable (R : Type*) [CommRing R] (M : Type*) [AddCommGroup M] [Module R M]

/-- The additive antipode on the symmetric algebra, induced by `m ↦ -m`. -/
noncomputable def antipode :
    SymmetricAlgebra R M →ₐ[R] SymmetricAlgebra R M :=
  SymmetricAlgebra.lift (-SymmetricAlgebra.ι R M)

@[simp]
theorem antipode_ι (m : M) :
    antipode R M (SymmetricAlgebra.ι R M m) = -SymmetricAlgebra.ι R M m := by
  simp [antipode]

/-- The symmetric algebra is the Hopf coordinate algebra of the additive vector group. -/
@[implicit_reducible] noncomputable def hopfAlgebra :
    HopfAlgebra R (SymmetricAlgebra R M) :=
  HopfAlgebra.ofAlgHom (antipode R M)
    (by
      ext m
      change
        (Algebra.TensorProduct.lift (antipode R M)
            (AlgHom.id R (SymmetricAlgebra R M)) (fun _ _ => Commute.all _ _))
              (Bialgebra.comulAlgHom R (SymmetricAlgebra R M)
                (SymmetricAlgebra.ι R M m)) =
          (Algebra.ofId R (SymmetricAlgebra R M))
            (Bialgebra.counitAlgHom R (SymmetricAlgebra R M)
              (SymmetricAlgebra.ι R M m))
      simp [SymmetricAlgebra.algebraMapInv_ι])
    (by
      ext m
      change
        (Algebra.TensorProduct.lift (AlgHom.id R (SymmetricAlgebra R M))
            (antipode R M) (fun _ _ => Commute.all _ _))
              (Bialgebra.comulAlgHom R (SymmetricAlgebra R M)
                (SymmetricAlgebra.ι R M m)) =
          (Algebra.ofId R (SymmetricAlgebra R M))
            (Bialgebra.counitAlgHom R (SymmetricAlgebra R M)
              (SymmetricAlgebra.ι R M m))
      simp [SymmetricAlgebra.algebraMapInv_ι])

@[implicit_reducible] noncomputable instance instHopfAlgebra :
    HopfAlgebra R (SymmetricAlgebra R M) :=
  hopfAlgebra R M

@[simp]
theorem antipode_eq :
    HopfAlgebra.antipode R (A := SymmetricAlgebra R M) =
      (antipode R M).toLinearMap := by
  rfl

end

end AdditiveSymmetricHopf

namespace AffineExponentialGroup

noncomputable section

variable (k : Type*) [CommRing k]

/-- Polynomial coordinate algebra of `Gₐⁿ`. -/
abbrev AdditiveCoordinateAlgebra (n : ℕ) :=
  SymmetricAlgebra k (Fin n → k)

/-- Laurent-monomial coordinate algebra of `Gₘⁿ`. -/
abbrev TorusCoordinateAlgebra (n : ℕ) :=
  AddMonoidAlgebra k (Fin n →₀ ℤ)

/-- Coordinate algebra of `Gₐⁿ × Gₘⁿ`. -/
abbrev CoordinateAlgebra (n : ℕ) :=
  TorusCoordinateAlgebra k n ⊗[k] AdditiveCoordinateAlgebra k n

@[implicit_reducible] noncomputable instance instCoordinateHopfAlgebra (n : ℕ) :
    HopfAlgebra k (CoordinateAlgebra k n) :=
  TensorProduct.instHopfAlgebra

/-- The `i`th standard vector in the additive coordinate space. -/
noncomputable def additiveBasisVector {n : ℕ} (i : Fin n) : Fin n → k :=
  Pi.single i 1

/-- The primitive `i`th coordinate of `Gₐⁿ` inside the product coordinate algebra. -/
noncomputable def additiveCoordinate {n : ℕ} (i : Fin n) : CoordinateAlgebra k n :=
  1 ⊗ₜ[k] SymmetricAlgebra.ι k (Fin n → k) (additiveBasisVector k i)

/-- The group-like torus character indexed by an integral exponent vector. -/
noncomputable def torusCharacter {n : ℕ} (m : Fin n →₀ ℤ) : CoordinateAlgebra k n :=
  AddMonoidAlgebra.single m 1 ⊗ₜ[k] 1

@[simp]
theorem counit_additiveCoordinate {n : ℕ} (i : Fin n) :
    Coalgebra.counit (R := k) (additiveCoordinate k i) = 0 := by
  simp [additiveCoordinate]

@[simp]
theorem counit_torusCharacter {n : ℕ} (m : Fin n →₀ ℤ) :
    Coalgebra.counit (R := k) (torusCharacter k m) = 1 := by
  simp [torusCharacter]

@[simp]
theorem comul_additiveCoordinate {n : ℕ} (i : Fin n) :
    Coalgebra.comul (R := k) (additiveCoordinate k i) =
      additiveCoordinate k i ⊗ₜ[k] 1 + 1 ⊗ₜ[k] additiveCoordinate k i := by
  simp [additiveCoordinate, Algebra.TensorProduct.one_def, TensorProduct.tmul_add]

@[simp]
theorem comul_torusCharacter {n : ℕ} (m : Fin n →₀ ℤ) :
    Coalgebra.comul (R := k) (torusCharacter k m) =
      torusCharacter k m ⊗ₜ[k] torusCharacter k m := by
  simp [torusCharacter, Algebra.TensorProduct.one_def]

@[simp]
theorem antipode_additiveCoordinate {n : ℕ} (i : Fin n) :
    HopfAlgebra.antipode k (additiveCoordinate k i) = -additiveCoordinate k i := by
  simp [TensorProduct.antipode_def, additiveCoordinate, TensorProduct.tmul_neg]

@[simp]
theorem antipode_torusCharacter {n : ℕ} (m : Fin n →₀ ℤ) :
    HopfAlgebra.antipode k (torusCharacter k m) = torusCharacter k (-m) := by
  simp [TensorProduct.antipode_def, torusCharacter]

@[simp]
theorem torusCharacter_zero {n : ℕ} :
    torusCharacter k (0 : Fin n →₀ ℤ) = 1 := by
  simp [torusCharacter, AddMonoidAlgebra.one_def, Algebra.TensorProduct.one_def]

@[simp]
theorem torusCharacter_add {n : ℕ} (m₁ m₂ : Fin n →₀ ℤ) :
    torusCharacter k (m₁ + m₂) = torusCharacter k m₁ * torusCharacter k m₂ := by
  simp [torusCharacter, AddMonoidAlgebra.single_mul_single]

end


end AffineExponentialGroup

namespace AlgebraicGroupCrossHom

noncomputable section

open LaurentPolynomial

variable (k : Type*) [Field k]

/-- Hopf coordinate algebra of the one-dimensional additive group. -/
abbrev GaCoordinate := SymmetricAlgebra k k

/-- Hopf coordinate algebra of the one-dimensional multiplicative group. -/
abbrev GmCoordinate := LaurentPolynomial k

/-- The trivial Hopf-coordinate morphism: counit followed by unit. -/
noncomputable def trivialBialgHom {A B : Type*} [Semiring A] [Semiring B]
    [Bialgebra k A] [Bialgebra k B] : A →ₐc[k] B :=
  (Bialgebra.unitBialgHom k B).comp (Bialgebra.counitBialgHom k A)

@[simp]
theorem trivialBialgHom_apply {A B : Type*} [Semiring A] [Semiring B]
    [Bialgebra k A] [Bialgebra k B] (x : A) :
    trivialBialgHom k (A := A) (B := B) x =
      algebraMap k B (Coalgebra.counit (R := k) x) := by
  rfl

/-- Any Hopf-coordinate morphism from `𝒪(Gₘ)` to `𝒪(Gₐ)` sends the torus generator to one. -/
theorem laurentToSymmetric_T_one (f : GmCoordinate k →ₐc[k] GaCoordinate k) :
    f (T 1) = 1 := by
  let e : GaCoordinate k ≃ₐ[k] MvPolynomial Unit k :=
    SymmetricAlgebra.equivMvPolynomial (Module.Basis.singleton Unit k)
  have hu : IsUnit (e (f (T 1))) :=
    (LaurentPolynomial.isUnit_T (R := k) 1).map (e.toAlgHom.comp f.toAlgHom)
  obtain ⟨c, hc, hec⟩ := MvPolynomial.isUnit_iff_eq_C_of_isReduced.mp hu
  have hfc : f (T 1) = algebraMap k (GaCoordinate k) c := by
    apply e.injective
    simpa using hec
  have hcounit := DFunLike.congr_fun (BialgHom.counitAlgHom_comp f) (T 1)
  change Coalgebra.counit (R := k) (f (T 1)) =
    Coalgebra.counit (R := k) (T 1 : GmCoordinate k) at hcounit
  rw [hfc] at hcounit
  have hc1 : c = 1 := by simpa using hcounit
  rw [hfc, hc1, map_one]

/-- There are no nontrivial algebraic-group morphisms `Gₐ → Gₘ`, in contravariant Hopf
coordinates. -/
theorem laurentToSymmetric_eq_trivial (f : GmCoordinate k →ₐc[k] GaCoordinate k) :
    f = trivialBialgHom k := by
  have hT : f (T 1) = 1 := laurentToSymmetric_T_one k f
  have hTneg : f (T (-1)) = 1 := by
    have h := congrArg f (LaurentPolynomial.T_add (R := k) 1 (-1))
    rw [map_mul, hT, one_mul] at h
    simpa using h.symm
  have hT_all : ∀ n : ℤ, f (T n) = 1 := by
    intro n
    induction n using Int.induction_on with
    | zero => simp
    | succ n ih =>
        rw [show (T ((n : ℤ) + 1) : GmCoordinate k) = T n * T 1 by
          exact LaurentPolynomial.T_add n 1]
        rw [map_mul, ih, hT, one_mul]
    | pred n ih =>
        rw [show (T (-(n : ℤ) - 1) : GmCoordinate k) = T (-n) * T (-1) by
          exact LaurentPolynomial.T_add (-n) (-1)]
        rw [map_mul, ih, hTneg, one_mul]
  apply BialgHom.ext
  intro p
  induction p using LaurentPolynomial.induction_on' with
  | add p q hp hq => rw [map_add, map_add, hp, hq]
  | C_mul_T n a =>
      change f (C a * T n) =
        algebraMap k (GaCoordinate k) (Coalgebra.counit (R := k) (C a * T n))
      rw [map_mul, hT_all, mul_one]
      rw [LaurentPolynomial.counit_C_mul_T, CommSemiring.counit_apply]
      change f (algebraMap k (GmCoordinate k) a) = algebraMap k (GaCoordinate k) a
      exact f.toAlgHom.commutes a

/-- Coefficients of a pure tensor under the group-algebra tensor equivalence factor. -/
theorem tensorEquiv_tmul_coeff (p q : GmCoordinate k) (a b : ℤ) :
    ((AddMonoidAlgebra.tensorEquiv k) (p ⊗ₜ[k] q)).coeff (a, b) =
      p.coeff a * q.coeff b := by
  classical
  induction p using AddMonoidAlgebra.induction_linear with
  | zero =>
      simp only [TensorProduct.zero_tmul, map_zero,
        AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply, zero_mul]
  | add p₁ p₂ hp₁ hp₂ =>
      rw [TensorProduct.add_tmul, map_add, AddMonoidAlgebra.coeff_add,
        Finsupp.add_apply, hp₁, hp₂]
      change p₁.coeff a * q.coeff b + p₂.coeff a * q.coeff b =
        (p₁.coeff a + p₂.coeff a) * q.coeff b
      ring
  | single x c =>
      induction q using AddMonoidAlgebra.induction_linear with
      | zero =>
          simp only [TensorProduct.tmul_zero, map_zero,
            AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply, mul_zero]
      | add q₁ q₂ hq₁ hq₂ =>
          rw [TensorProduct.tmul_add, map_add, AddMonoidAlgebra.coeff_add,
            Finsupp.add_apply, hq₁, hq₂]
          change (AddMonoidAlgebra.single x c).coeff a * q₁.coeff b +
              (AddMonoidAlgebra.single x c).coeff a * q₂.coeff b =
            (AddMonoidAlgebra.single x c).coeff a * (q₁.coeff b + q₂.coeff b)
          ring
      | single y d =>
          rw [AddMonoidAlgebra.tensorEquiv_single_tmul_single]
          change (Finsupp.single (x, y) (c * d)) (a, b) =
            (Finsupp.single x c) a * (Finsupp.single y d) b
          by_cases hxa : x = a <;> by_cases hyb : y = b <;>
            simp [hxa, hyb, Prod.ext_iff]

/-- The comultiplication of a Laurent polynomial is supported on the diagonal. -/
theorem tensorEquiv_comul_coeff (p : GmCoordinate k) (a b : ℤ) :
    ((AddMonoidAlgebra.tensorEquiv k) (Coalgebra.comul (R := k) p)).coeff (a, b) =
      if a = b then p.coeff a else 0 := by
  classical
  induction p using AddMonoidAlgebra.induction_linear with
  | zero =>
      simp only [map_zero, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply, ite_self]
  | add p q hp hq =>
      rw [map_add, map_add, AddMonoidAlgebra.coeff_add,
        Finsupp.add_apply, hp, hq]
      by_cases hab : a = b <;> simp [hab]
  | single x c =>
      rw [AddMonoidAlgebra.comul_single]
      simp only [CommSemiring.comul_apply, TensorProduct.map_tmul,
        AddMonoidAlgebra.lsingle_apply, AddMonoidAlgebra.tensorEquiv_single_tmul_single]
      simp only [one_mul, AddMonoidAlgebra.coeff_single]
      by_cases hab : a = b <;> by_cases hxa : x = a <;> by_cases hxb : x = b <;>
        simp [hab, hxa, hxb, Prod.ext_iff]

/-- Laurent Hopf algebras have no nonzero primitive elements.  Equivalently, `Gₘ` admits no
nontrivial algebraic-group morphism to `Gₐ`. -/
theorem primitive_laurent_eq_zero (p : GmCoordinate k)
    (hp : Coalgebra.comul (R := k) p = p ⊗ₜ[k] 1 + 1 ⊗ₜ[k] p) : p = 0 := by
  classical
  apply LaurentPolynomial.ext
  intro n
  change p.coeff n = 0
  have h := congrArg
    (fun z : GmCoordinate k ⊗[k] GmCoordinate k =>
      ((AddMonoidAlgebra.tensorEquiv k) z).coeff (n, n)) hp
  rw [tensorEquiv_comul_coeff k p n n] at h
  simp only [map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply] at h
  rw [tensorEquiv_tmul_coeff k p 1 n n,
    tensorEquiv_tmul_coeff k 1 p n n] at h
  have hone : (1 : GmCoordinate k).coeff n = if 0 = n then 1 else 0 := by
    rw [AddMonoidAlgebra.one_def, AddMonoidAlgebra.coeff_single]
    exact Finsupp.single_apply
  rw [hone] at h
  by_cases hn : n = 0
  · subst n
    rw [if_pos rfl, mul_one, one_mul] at h
    change p.coeff 0 = p.coeff 0 + p.coeff 0 at h
    linear_combination -h
  · rw [if_neg (Ne.symm hn), mul_zero, zero_mul, add_zero] at h
    exact h

/-- There are no nontrivial algebraic-group morphisms `Gₘ → Gₐ`, in contravariant Hopf
coordinates. -/
theorem symmetricToLaurent_eq_trivial (f : GaCoordinate k →ₐc[k] GmCoordinate k) :
    f = trivialBialgHom k := by
  have hιzero : ∀ x : k, f (SymmetricAlgebra.ι k k x) = 0 := by
    intro x
    have hmap := DFunLike.congr_fun (BialgHom.map_comp_comulAlgHom f)
      (SymmetricAlgebra.ι k k x)
    change
      (Algebra.TensorProduct.map f.toAlgHom f.toAlgHom)
          (Coalgebra.comul (R := k) (SymmetricAlgebra.ι k k x)) =
        Coalgebra.comul (R := k) (f (SymmetricAlgebra.ι k k x)) at hmap
    rw [SymmetricAlgebra.comul_ι, map_add,
      Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul, map_one] at hmap
    have hprim : Coalgebra.comul (R := k) (f (SymmetricAlgebra.ι k k x)) =
        f (SymmetricAlgebra.ι k k x) ⊗ₜ[k] 1 +
          1 ⊗ₜ[k] f (SymmetricAlgebra.ι k k x) := by
      exact hmap.symm
    exact primitive_laurent_eq_zero k _ hprim
  have halg : f.toAlgHom = (trivialBialgHom k).toAlgHom := by
    apply SymmetricAlgebra.algHom_ext
    apply LinearMap.ext
    intro x
    change f (SymmetricAlgebra.ι k k x) =
      trivialBialgHom k (SymmetricAlgebra.ι k k x)
    rw [hιzero]
    simp [trivialBialgHom]
  apply BialgHom.ext
  intro x
  exact DFunLike.congr_fun halg x

end


end AlgebraicGroupCrossHom

end GaloisForLFunctions.HTGeometry
