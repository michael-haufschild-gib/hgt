import Mathlib.Algebra.Group.Submonoid.Membership
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Tactic.Ring

/-!
# A cyclic conifold monomial chart

Four border generators have one relation and a unique reduced monomial form.
Their semigroup equals the lattice points in four integral half-spaces, hence
is saturated. Its algebra is the hypersurface u₀u₁ = u₂u₃ over any commutative ring.

For cyclic weights (1,3,2) modulo four, the graph {1,x,y,z} has exactly this
semigroup. Explicit invariant-lattice coordinates identify the actual chart
with the conifold and prove saturation in its character lattice. This realizes
the four-generator chart mechanism of Kaijima, arXiv:2611.20586, Lemma 2.7.
-/

noncomputable section
namespace GaloisForLFunctions.RepresentationLifting.Conifold

/-- Four border generators with the conifold relation u₀+u₁=u₂+u₃. -/
def coordinates : (Fin 4 → ℕ) →+ (Fin 3 → ℤ) where
  toFun c := ![(c 0 : ℤ) - c 1, (c 1 : ℤ) + c 2, (c 1 : ℤ) + c 3]
  map_zero' := by ext i; fin_cases i <;> simp
  map_add' c d := by ext i; fin_cases i <;> simp <;> omega

/-- Removing the common u₀,u₁ power leaves a unique monomial normal form. -/
def normalize (c : Fin 4 → ℕ) : Fin 4 → ℕ :=
  let m := min (c 0) (c 1)
  ![c 0 - m, c 1 - m, c 2 + m, c 3 + m]

theorem normalize_coordinates (c : Fin 4 → ℕ) :
    coordinates (normalize c) = coordinates c := by
  have h0 := Nat.min_le_left (c 0) (c 1)
  have h1 := Nat.min_le_right (c 0) (c 1)
  ext i
  fin_cases i
  · change ((c 0 - min (c 0) (c 1) : ℕ) : ℤ) - (c 1 - min (c 0) (c 1) : ℕ) = (c 0 : ℤ) - c 1
    omega
  · change ((c 1 - min (c 0) (c 1) : ℕ) : ℤ) + (c 2 + min (c 0) (c 1) : ℕ) = (c 1 : ℤ) + c 2
    omega
  · change ((c 1 - min (c 0) (c 1) : ℕ) : ℤ) + (c 3 + min (c 0) (c 1) : ℕ) = (c 1 : ℤ) + c 3
    omega

theorem normalize_reduced (c : Fin 4 → ℕ) : normalize c 0 = 0 ∨ normalize c 1 = 0 := by
  change c 0 - min (c 0) (c 1) = 0 ∨ c 1 - min (c 0) (c 1) = 0
  omega

/-- The single conifold relation accounts for every equality between border monomials. -/
theorem coordinates_injective_on_reduced {c d : Fin 4 → ℕ}
    (hc : c 0 = 0 ∨ c 1 = 0) (hd : d 0 = 0 ∨ d 1 = 0)
    (h : coordinates c = coordinates d) : c = d := by
  have h0 : (c 0 : ℤ) - c 1 = (d 0 : ℤ) - d 1 := congrFun h 0
  have h1 : (c 1 : ℤ) + c 2 = (d 1 : ℤ) + d 2 := congrFun h 1
  have h2 : (c 1 : ℤ) + c 3 = (d 1 : ℤ) + d 3 := congrFun h 2
  funext i
  fin_cases i
  · change c 0 = d 0; omega
  · change c 1 = d 1; omega
  · change c 2 = d 2; omega
  · change c 3 = d 3; omega

theorem coordinates_eq_iff_normalize_eq (c d : Fin 4 → ℕ) :
    coordinates c = coordinates d ↔ normalize c = normalize d := by
  constructor
  · intro h
    apply coordinates_injective_on_reduced (normalize_reduced c) (normalize_reduced d)
    rw [normalize_coordinates, normalize_coordinates, h]
  · intro h
    rw [← normalize_coordinates c, ← normalize_coordinates d, h]

section Presentation
variable {M : Type*} [CommMonoid M]

/-- Evaluate a border monomial at four commuting elements. -/
def monomial (a : Fin 4 → M) (c : Fin 4 → ℕ) : M :=
  a 0 ^ c 0 * a 1 ^ c 1 * a 2 ^ c 2 * a 3 ^ c 3

theorem monomial_add (a : Fin 4 → M) (c d : Fin 4 → ℕ) :
    monomial a (c + d) = monomial a c * monomial a d := by
  simp only [monomial, Pi.add_apply, pow_add]
  ac_rfl

/-- The conifold relation preserves evaluation under monomial normalization. -/
theorem monomial_normalize (a : Fin 4 → M) (ha : a 0 * a 1 = a 2 * a 3)
    (c : Fin 4 → ℕ) : monomial a c = monomial a (normalize c) := by
  let m := min (c 0) (c 1)
  have h0 : c 0 = (c 0 - m) + m := (Nat.sub_add_cancel (Nat.min_le_left _ _)).symm
  have h1 : c 1 = (c 1 - m) + m := (Nat.sub_add_cancel (Nat.min_le_right _ _)).symm
  change a 0 ^ c 0 * a 1 ^ c 1 * a 2 ^ c 2 * a 3 ^ c 3 =
    a 0 ^ (c 0 - m) * a 1 ^ (c 1 - m) * a 2 ^ (c 2 + m) * a 3 ^ (c 3 + m)
  calc
    _ = (a 0 ^ (c 0 - m) * a 1 ^ (c 1 - m) * a 2 ^ c 2 * a 3 ^ c 3) *
        (a 0 * a 1) ^ m := by
      conv_lhs => rw [h0, h1, pow_add, pow_add]
      rw [mul_pow]
      ac_rfl
    _ = _ := by
      rw [ha, mul_pow, pow_add, pow_add]
      ac_rfl

/-- Every equality of border exponents follows from the one conifold relation. -/
theorem monomial_eq_of_coordinates_eq (a : Fin 4 → M)
    (ha : a 0 * a 1 = a 2 * a 3) {c d : Fin 4 → ℕ}
    (h : coordinates c = coordinates d) : monomial a c = monomial a d := by
  rw [monomial_normalize a ha c, monomial_normalize a ha d,
    (coordinates_eq_iff_normalize_eq c d).mp h]

end Presentation

/-- The four integral half-spaces of the conifold's character cone. -/
def cone : AddSubmonoid (Fin 3 → ℤ) where
  carrier := {x | 0 ≤ x 1 ∧ 0 ≤ x 2 ∧ 0 ≤ x 0 + x 1 ∧ 0 ≤ x 0 + x 2}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    change 0 ≤ x 1 + y 1 ∧ 0 ≤ x 2 + y 2 ∧
      0 ≤ (x 0 + y 0) + (x 1 + y 1) ∧ 0 ≤ (x 0 + y 0) + (x 2 + y 2)
    rcases hx with ⟨hx1, hx2, hx01, hx02⟩
    rcases hy with ⟨hy1, hy2, hy01, hy02⟩
    omega

theorem coordinates_mem (c : Fin 4 → ℕ) : coordinates c ∈ cone := by
  change 0 ≤ (c 1 : ℤ) + c 2 ∧ 0 ≤ (c 1 : ℤ) + c 3 ∧
    0 ≤ ((c 0 : ℤ) - c 1) + (c 1 + c 2) ∧
    0 ≤ ((c 0 : ℤ) - c 1) + (c 1 + c 3)
  omega

/-- Every lattice point in the cone is already a nonnegative border combination. -/
theorem cone_eq_range : cone = AddMonoidHom.mrange coordinates := by
  apply le_antisymm
  · intro x hx
    rcases hx with ⟨h1, h2, h01, h02⟩
    by_cases h0 : 0 ≤ x 0
    · refine ⟨![(x 0).toNat, 0, (x 1).toNat, (x 2).toNat], ?_⟩
      ext i
      fin_cases i <;> simp [coordinates, Int.toNat_of_nonneg h0,
        Int.toNat_of_nonneg h1, Int.toNat_of_nonneg h2]
    · refine ⟨![0, (-x 0).toNat, (x 0 + x 1).toNat, (x 0 + x 2).toNat], ?_⟩
      have hn : 0 ≤ -x 0 := by omega
      ext i
      fin_cases i
      · change (0 : ℤ) - ((-x 0).toNat : ℤ) = x 0
        omega
      · change ((-x 0).toNat : ℤ) + ((x 0 + x 1).toNat : ℤ) = x 1
        omega
      · change ((-x 0).toNat : ℤ) + ((x 0 + x 2).toNat : ℤ) = x 2
        omega
  · rintro _ ⟨c, rfl⟩
    exact coordinates_mem c

/-- The conifold semigroup is saturated in its full rank-three character lattice. -/
theorem saturated (x : Fin 3 → ℤ) (n : ℕ) (hn : 0 < n) :
    n • x ∈ AddMonoidHom.mrange coordinates ↔ x ∈ AddMonoidHom.mrange coordinates := by
  rw [← cone_eq_range]
  constructor
  · intro hx
    rcases hx with ⟨h1, h2, h01, h02⟩
    simp only [Pi.smul_apply, nsmul_eq_mul] at h1 h2 h01 h02
    have hn' : (0 : ℤ) < n := by exact_mod_cast hn
    change 0 ≤ x 1 ∧ 0 ≤ x 2 ∧ 0 ≤ x 0 + x 1 ∧ 0 ≤ x 0 + x 2
    rw [← mul_add] at h01 h02
    exact ⟨nonneg_of_mul_nonneg_right h1 hn', nonneg_of_mul_nonneg_right h2 hn',
      nonneg_of_mul_nonneg_right h01 hn', nonneg_of_mul_nonneg_right h02 hn'⟩
  · intro hx
    exact cone.nsmul_mem hx n

/-- A border expression for a semigroup point. Normalization makes its evaluation independent of choice. -/
def coefficientChoice (x : AddMonoidHom.mrange coordinates) : Fin 4 → ℕ :=
  Classical.choose x.property

theorem coefficientChoice_spec (x : AddMonoidHom.mrange coordinates) :
    coordinates (coefficientChoice x) = (x : Fin 3 → ℤ) := Classical.choose_spec x.property

/-- Four commuting elements satisfying the conifold relation define a homomorphism out of the border semigroup. -/
def liftBorder {M : Type*} [CommMonoid M] (a : Fin 4 → M)
    (ha : a 0 * a 1 = a 2 * a 3) : Multiplicative (AddMonoidHom.mrange coordinates) →* M where
  toFun x := monomial a (coefficientChoice x.toAdd)
  map_one' := by
    have he : coordinates (coefficientChoice (0 : AddMonoidHom.mrange coordinates)) =
        coordinates 0 := by rw [coefficientChoice_spec, map_zero]; rfl
    exact (monomial_eq_of_coordinates_eq a ha he).trans (by simp [monomial])
  map_mul' x y := by
    have he : coordinates (coefficientChoice (x * y).toAdd) =
        coordinates (coefficientChoice x.toAdd + coefficientChoice y.toAdd) := by
      rw [map_add, coefficientChoice_spec, coefficientChoice_spec, coefficientChoice_spec]
      rfl
    exact (monomial_eq_of_coordinates_eq a ha he).trans (monomial_add a _ _)

/-- The universal homomorphism has the prescribed value on every border monomial. -/
theorem liftBorder_coordinates {M : Type*} [CommMonoid M] (a : Fin 4 → M)
    (ha : a 0 * a 1 = a 2 * a 3) (c : Fin 4 → ℕ) :
    liftBorder a ha (Multiplicative.ofAdd ⟨coordinates c, ⟨c, rfl⟩⟩) = monomial a c :=
  monomial_eq_of_coordinates_eq a ha (coefficientChoice_spec _)

/-- Border coordinates valued in their image semigroup. -/
def coordinatesInto : (Fin 4 → ℕ) →+ AddMonoidHom.mrange coordinates where
  toFun c := ⟨coordinates c, ⟨c, rfl⟩⟩
  map_zero' := Subtype.ext (map_zero coordinates)
  map_add' c d := Subtype.ext (map_add coordinates c d)

/-- The four primitive border vectors. -/
def border (i : Fin 4) : AddMonoidHom.mrange coordinates := coordinatesInto (Pi.single i 1)

@[simp] theorem coe_coordinatesInto (c : Fin 4 → ℕ) :
    (coordinatesInto c : Fin 3 → ℤ) = coordinates c := rfl

@[simp] theorem coe_border (i : Fin 4) :
    (border i : Fin 3 → ℤ) = coordinates (Pi.single i 1) := rfl

theorem border_relation : border 0 + border 1 = border 2 + border 3 := by
  apply Subtype.ext
  ext i
  fin_cases i <;> rfl

theorem border_monomial (c : Fin 4 → ℕ) :
    monomial (fun i => Multiplicative.ofAdd (border i)) c =
      Multiplicative.ofAdd (coordinatesInto c) := by
  change c 0 • border 0 + c 1 • border 1 + c 2 • border 2 + c 3 • border 3 = coordinatesInto c
  have hc : c = c 0 • Pi.single 0 1 + c 1 • Pi.single 1 1 +
      c 2 • Pi.single 2 1 + c 3 • Pi.single 3 1 := by
    funext i
    fin_cases i <;> simp
  have he := congrArg coordinatesInto hc
  simp only [map_add, map_nsmul] at he
  exact he.symm

section Algebra
variable (K : Type*) [CommRing K]
open MvPolynomial

/-- The conifold equation in four border variables. -/
def relation : MvPolynomial (Fin 4) K := X 0 * X 1 - X 2 * X 3

/-- The hypersurface's defining ideal. -/
def relationIdeal : Ideal (MvPolynomial (Fin 4) K) := Ideal.span {relation K}

/-- Residue class of a border variable. -/
def quotientVariable (i : Fin 4) : MvPolynomial (Fin 4) K ⧸ relationIdeal K :=
  Ideal.Quotient.mkₐ K (relationIdeal K) (X i)

theorem quotientVariable_relation : quotientVariable K 0 * quotientVariable K 1 =
    quotientVariable K 2 * quotientVariable K 3 := by
  apply sub_eq_zero.mp
  change Ideal.Quotient.mk (relationIdeal K) (relation K) = 0
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))

/-- Border monomials define the polynomial map to the actual semigroup algebra. -/
def polynomialToSemigroup : MvPolynomial (Fin 4) K →ₐ[K]
    AddMonoidAlgebra K (AddMonoidHom.mrange coordinates) :=
  aeval (fun i => AddMonoidAlgebra.single (border i) 1)

theorem polynomialToSemigroup_relation : polynomialToSemigroup K (relation K) = 0 := by
  simp only [polynomialToSemigroup, relation, map_sub, map_mul, aeval_X,
    AddMonoidAlgebra.single_mul_single, one_mul, border_relation, sub_self]

/-- The conifold equation vanishes identically in its border chart. -/
def quotientToSemigroup : (MvPolynomial (Fin 4) K ⧸ relationIdeal K) →ₐ[K]
    AddMonoidAlgebra K (AddMonoidHom.mrange coordinates) :=
  Ideal.Quotient.liftₐ (relationIdeal K) (polynomialToSemigroup K) (by
    have hle : relationIdeal K ≤ RingHom.ker (polynomialToSemigroup K).toRingHom := by
      apply Ideal.span_le.mpr
      rintro x (rfl : x = relation K)
      exact polynomialToSemigroup_relation K
    exact fun x hx => hle hx)

/-- The unique monomial normal form constructs the inverse map from the border chart. -/
def semigroupToQuotient : AddMonoidAlgebra K (AddMonoidHom.mrange coordinates) →ₐ[K]
    (MvPolynomial (Fin 4) K ⧸ relationIdeal K) :=
  AddMonoidAlgebra.lift K _ _ (liftBorder (quotientVariable K) (quotientVariable_relation K))

theorem semigroupToQuotient_coordinates (c : Fin 4 → ℕ) :
    semigroupToQuotient K (AddMonoidAlgebra.single (coordinatesInto c) 1) =
      Conifold.monomial (quotientVariable K) c := by
  rw [semigroupToQuotient, AddMonoidAlgebra.lift_single, one_smul]
  exact liftBorder_coordinates _ _ c

theorem quotientToSemigroup_variable (i : Fin 4) :
    quotientToSemigroup K (quotientVariable K i) = AddMonoidAlgebra.single (border i) 1 := by
  change polynomialToSemigroup K (X i) = _
  exact aeval_X _ i

theorem semigroupToQuotient_border (i : Fin 4) :
    semigroupToQuotient K (AddMonoidAlgebra.single (border i) 1) = quotientVariable K i := by
  rw [border, semigroupToQuotient_coordinates]
  fin_cases i <;> simp [Conifold.monomial]

theorem quotient_semigroup_inverse :
    (semigroupToQuotient K).comp (quotientToSemigroup K) = AlgHom.id K _ := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro i
  change semigroupToQuotient K (quotientToSemigroup K (quotientVariable K i)) = quotientVariable K i
  rw [quotientToSemigroup_variable, semigroupToQuotient_border]

theorem semigroup_quotient_inverse :
    (quotientToSemigroup K).comp (semigroupToQuotient K) = AlgHom.id K _ := by
  apply (AddMonoidAlgebra.lift K _ (AddMonoidHom.mrange coordinates)).symm.injective
  apply MonoidHom.ext
  intro x
  obtain ⟨c, hc⟩ := x.toAdd.property
  have hx : x.toAdd = coordinatesInto c := Subtype.ext hc.symm
  change quotientToSemigroup K (semigroupToQuotient K (AddMonoidAlgebra.single x.toAdd 1)) =
    AddMonoidAlgebra.single x.toAdd 1
  rw [hx, semigroupToQuotient_coordinates]
  have hm := congrArg (AddMonoidAlgebra.of K (AddMonoidHom.mrange coordinates)) (border_monomial c)
  simpa only [Conifold.monomial, map_mul, map_pow, quotientToSemigroup_variable,
    AddMonoidAlgebra.of_apply, toAdd_ofAdd] using hm

/-- The complete conifold presentation: its semigroup chart is exactly xy=zw. -/
def conifoldChart : (MvPolynomial (Fin 4) K ⧸ relationIdeal K) ≃ₐ[K]
    AddMonoidAlgebra K (AddMonoidHom.mrange coordinates) :=
  AlgEquiv.ofAlgHom (quotientToSemigroup K) (semigroupToQuotient K)
    (semigroup_quotient_inverse K) (quotient_semigroup_inverse K)

#print axioms conifoldChart
end Algebra

#print axioms coordinates_eq_iff_normalize_eq
#print axioms cone_eq_range
#print axioms saturated
end GaloisForLFunctions.RepresentationLifting.Conifold

namespace GaloisForLFunctions.RepresentationLifting.CyclicFourChart

/-- Character residue for cyclic weights (1,3,2) modulo four. -/
def residue (u : Fin 3 → ℕ) : ℕ := (u 0 + 3 * u 1 + 2 * u 2) % 4

/-- The monomial graph consists of 1,x,z,y in character order. -/
def representative (r : ℕ) : Fin 3 → ℤ :=
  if r = 0 then ![0, 0, 0] else if r = 1 then ![1, 0, 0]
  else if r = 2 then ![0, 0, 1] else ![0, 1, 0]

/-- Discrepancy from the representative of the same character. -/
def defect (u : Fin 3 → ℕ) : Fin 3 → ℤ := fun i => (u i : ℤ) - representative (residue u) i

/-- The discrepancy semigroup of the four-monomial graph. -/
def semigroup : AddSubmonoid (Fin 3 → ℤ) := AddSubmonoid.closure (Set.range defect)

/-- A basis of the invariant character lattice, of index four in the exponent lattice. -/
def latticeMap : (Fin 3 → ℤ) →+ (Fin 3 → ℤ) where
  toFun v := ![2 * v 1 - v 2, 2 * v 0 + v 2, -v 0 - v 1 + v 2]
  map_zero' := by ext i; fin_cases i <;> simp
  map_add' v w := by ext i; fin_cases i <;> simp <;> ring

theorem latticeMap_injective : Function.Injective latticeMap := by
  intro v w h
  have h0 : 2 * v 1 - v 2 = 2 * w 1 - w 2 := congrFun h 0
  have h1 : 2 * v 0 + v 2 = 2 * w 0 + w 2 := congrFun h 1
  have h2 : -v 0 - v 1 + v 2 = -w 0 - w 1 + w 2 := congrFun h 2
  funext i
  fin_cases i
  · change v 0 = w 0; linarith only [h0, h1, h2]
  · change v 1 = w 1; linarith only [h0, h1, h2]
  · change v 2 = w 2; linarith only [h0, h1, h2]

/-- Integral coordinates of an invariant monomial in the chart's lattice basis. -/
def inverseCoordinates (v : Fin 3 → ℤ) : Fin 3 → ℤ :=
  ![(v 1 - v 0 - 2 * v 2) / 4, (3 * v 0 + v 1 + 2 * v 2) / 4,
    (v 0 + v 1 + 2 * v 2) / 2]

theorem inverseCoordinates_spec (v : Fin 3 → ℤ)
    (hv : (v 0 + 3 * v 1 + 2 * v 2) % 4 = 0) :
    latticeMap (inverseCoordinates v) = v := by
  ext i
  fin_cases i <;> simp [latticeMap, inverseCoordinates] <;> omega

theorem defect_invariant (u : Fin 3 → ℕ) :
    (defect u 0 + 3 * defect u 1 + 2 * defect u 2) % 4 = 0 := by
  have hr : residue u < 4 := Nat.mod_lt _ (by decide)
  have hd : (residue u : ℤ) + 4 * ((u 0 + 3 * u 1 + 2 * u 2) / 4 : ℕ) =
      (u 0 : ℤ) + 3 * u 1 + 2 * u 2 := by
    exact_mod_cast Nat.mod_add_div (u 0 + 3 * u 1 + 2 * u 2) 4
  generalize he : residue u = r at hr hd ⊢
  interval_cases r <;> simp [defect, representative, he] <;> omega

/-- Every discrepancy lies in the conifold cone, proved by its four character classes. -/
theorem inverseCoordinates_defect_mem (u : Fin 3 → ℕ) :
    inverseCoordinates (defect u) ∈ Conifold.cone := by
  have hr : residue u < 4 := Nat.mod_lt _ (by decide)
  have hd : (residue u : ℤ) + 4 * ((u 0 + 3 * u 1 + 2 * u 2) / 4 : ℕ) =
      (u 0 : ℤ) + 3 * u 1 + 2 * u 2 := by
    exact_mod_cast Nat.mod_add_div (u 0 + 3 * u 1 + 2 * u 2) 4
  change 0 ≤ inverseCoordinates (defect u) 1 ∧ 0 ≤ inverseCoordinates (defect u) 2 ∧
    0 ≤ inverseCoordinates (defect u) 0 + inverseCoordinates (defect u) 1 ∧
    0 ≤ inverseCoordinates (defect u) 0 + inverseCoordinates (defect u) 2
  generalize he : residue u = r at hr hd
  interval_cases r <;> simp [inverseCoordinates, defect, representative, he] <;> omega

/-- All four conifold borders occur among actual discrepancies of the cyclic graph. -/
theorem border_mem (i : Fin 4) : latticeMap (Conifold.border i) ∈ semigroup := by
  fin_cases i
  · refine AddSubmonoid.subset_closure ⟨![0, 2, 0], ?_⟩
    ext j
    fin_cases j <;> simp [defect, residue, representative, latticeMap,
      Conifold.coe_border, Conifold.coordinates]
  · refine AddSubmonoid.subset_closure ⟨![1, 0, 1], ?_⟩
    ext j
    fin_cases j <;> simp [defect, residue, representative, latticeMap,
      Conifold.coe_border, Conifold.coordinates]
  · refine AddSubmonoid.subset_closure ⟨![2, 0, 0], ?_⟩
    ext j
    fin_cases j <;> simp [defect, residue, representative, latticeMap,
      Conifold.coe_border, Conifold.coordinates]
  · refine AddSubmonoid.subset_closure ⟨![0, 1, 1], ?_⟩
    ext j
    fin_cases j <;> simp [defect, residue, representative, latticeMap,
      Conifold.coe_border, Conifold.coordinates]

/-- The actual cyclic chart semigroup is the image of the complete conifold semigroup. -/
theorem semigroup_eq_cone_map : semigroup = Conifold.cone.map latticeMap := by
  apply le_antisymm
  · apply AddSubmonoid.closure_le.mpr
    rintro _ ⟨u, rfl⟩
    exact ⟨inverseCoordinates (defect u), inverseCoordinates_defect_mem u,
      inverseCoordinates_spec (defect u) (defect_invariant u)⟩
  · rintro _ ⟨v, hv, rfl⟩
    rw [Conifold.cone_eq_range] at hv
    obtain ⟨c, rfl⟩ := hv
    have he : latticeMap (Conifold.coordinates c) =
        c 0 • latticeMap (Conifold.border 0) + c 1 • latticeMap (Conifold.border 1) +
          c 2 • latticeMap (Conifold.border 2) + c 3 • latticeMap (Conifold.border 3) := by
      have hb := congrArg (fun x : Multiplicative (AddMonoidHom.mrange Conifold.coordinates) =>
        (x.toAdd : Fin 3 → ℤ)) (Conifold.border_monomial c)
      change c 0 • (Conifold.border 0 : Fin 3 → ℤ) +
        c 1 • (Conifold.border 1 : Fin 3 → ℤ) +
        c 2 • (Conifold.border 2 : Fin 3 → ℤ) +
        c 3 • (Conifold.border 3 : Fin 3 → ℤ) = Conifold.coordinates c at hb
      rw [← hb, map_add, map_add, map_add, map_nsmul, map_nsmul, map_nsmul, map_nsmul]
    rw [he]
    exact semigroup.add_mem (semigroup.add_mem (semigroup.add_mem
      (semigroup.nsmul_mem (border_mem 0) (c 0)) (semigroup.nsmul_mem (border_mem 1) (c 1)))
      (semigroup.nsmul_mem (border_mem 2) (c 2))) (semigroup.nsmul_mem (border_mem 3) (c 3))

/-- No invariant-lattice holes remain in the cyclic conifold chart. -/
theorem saturated (v : Fin 3 → ℤ) (n : ℕ) (hn : 0 < n)
    (hv : (v 0 + 3 * v 1 + 2 * v 2) % 4 = 0) :
    n • v ∈ semigroup ↔ v ∈ semigroup := by
  constructor
  · intro h
    rw [semigroup_eq_cone_map] at h ⊢
    obtain ⟨w, hw, he⟩ := h
    have hv' := inverseCoordinates_spec v hv
    have he' : w = n • inverseCoordinates v := by
      apply latticeMap_injective
      rw [map_nsmul, hv']
      exact he
    rw [he', Conifold.cone_eq_range] at hw
    have hi := (Conifold.saturated (inverseCoordinates v) n hn).mp hw
    rw [← Conifold.cone_eq_range] at hi
    exact ⟨inverseCoordinates v, hi, hv'⟩
  · intro h
    exact semigroup.nsmul_mem h n

/-- Lattice inclusion restricted to the actual border semigroups. -/
def chartMap : AddMonoidHom.mrange Conifold.coordinates →+ semigroup where
  toFun v := ⟨latticeMap v, by
    rw [semigroup_eq_cone_map]
    exact ⟨v, by rw [Conifold.cone_eq_range]; exact v.property, rfl⟩⟩
  map_zero' := Subtype.ext (map_zero latticeMap)
  map_add' v w := Subtype.ext (map_add latticeMap (v : Fin 3 → ℤ) (w : Fin 3 → ℤ))

/-- The cyclic graph has precisely the conifold monomial semigroup. -/
def chartAddEquiv : AddMonoidHom.mrange Conifold.coordinates ≃+ semigroup :=
  AddEquiv.ofBijective chartMap ⟨fun _ _ h =>
    Subtype.ext (latticeMap_injective (congrArg Subtype.val h)), fun v => by
      have hv := (show semigroup ≤ Conifold.cone.map latticeMap from
        le_of_eq semigroup_eq_cone_map) v.property
      obtain ⟨w, hw, he⟩ := hv
      rw [Conifold.cone_eq_range] at hw
      exact ⟨⟨w, hw⟩, Subtype.ext he⟩⟩

/-- The cyclic quotient chart for weights (1,3,2) and graph {1,x,y,z} has equation xy=zw. -/
def conifoldChart (K : Type*) [CommRing K] :
    (MvPolynomial (Fin 4) K ⧸ Conifold.relationIdeal K) ≃ₐ[K] AddMonoidAlgebra K semigroup :=
  (Conifold.conifoldChart K).trans (AddMonoidAlgebra.domCongr K K chartAddEquiv)

#print axioms semigroup_eq_cone_map
#print axioms saturated
#print axioms chartAddEquiv
#print axioms conifoldChart
end GaloisForLFunctions.RepresentationLifting.CyclicFourChart
