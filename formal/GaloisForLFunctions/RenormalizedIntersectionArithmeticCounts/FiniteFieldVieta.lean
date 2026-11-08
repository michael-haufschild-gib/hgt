import Mathlib.FieldTheory.Finite.Extension
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.UniqueFactorizationDomain.NormalizedFactors
import Mathlib.Data.Nat.Factorial.Basic
import GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts.FiniteFieldOrbitCounts
import GaloisForLFunctions.ArithmeticGaugeTheory.TheFunctionFieldCalibrationIsDerived

/-!
# Arithmetic Vieta correspondence

Monic polynomials of degree n over a finite field split in the common
extension of degree n!. Root multiplicities identify coefficient polynomials
with permutation orbits. Independent coefficient and normal-basis counts
then give a bijection with the Frobenius-stable root orbits.
-/

noncomputable section
open Polynomial Module Finset UniqueFactorizationMonoid
namespace GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts
variable (F E : Type*) [Field F] [Field E] [Algebra F E] [Fintype F] [Finite E]

omit [Fintype F] in
/-- A residue field embeds whenever its degree divides the ambient finite extension degree. -/
theorem finiteField_irreducible_splits {P : F[X]} (hP : Irreducible P) (hm : P.Monic)
    (hd : P.natDegree ∣ finrank F E) : (P.map (algebraMap F E)).Splits := by
  letI : Fact (Irreducible P) := ⟨hP⟩
  letI : Module.Finite F (AdjoinRoot P) := Module.Finite.of_basis (AdjoinRoot.powerBasis hP.ne_zero).basis
  have hd' : finrank F (AdjoinRoot P) ∣ finrank F E := by
    rw [(AdjoinRoot.powerBasis hP.ne_zero).finrank, AdjoinRoot.powerBasis_dim]
    exact hd
  obtain ⟨e⟩ := FiniteField.nonempty_algHom_of_finrank_dvd hd'
  have he : minpoly F (e (AdjoinRoot.root P)) = P := by
    rw [minpoly.algHom_eq e e.injective, AdjoinRoot.minpoly_root hP.ne_zero,
      hm.leadingCoeff, inv_one, C_1, mul_one]
  have hs := (inferInstance : Normal F E).splits (e (AdjoinRoot.root P))
  rwa [he] at hs

omit [Fintype F] in
/-- Every monic polynomial of bounded degree splits in a factorial-degree extension. -/
theorem finiteField_bounded_monic_splits {n : ℕ} (hd : n.factorial ∣ finrank F E)
    {f : F[X]} (hm : f.Monic) (hn : f.natDegree ≤ n) :
    (f.map (algebraMap F E)).Splits := by
  classical
  have hf : (normalizedFactors f).prod = f := by
    simpa only [hm.leadingCoeff, C_1, one_mul] using
      leadingCoeff_mul_prod_normalizedFactors f
  rw [← hf, Polynomial.map_multiset_prod]
  apply Splits.multisetProd
  intro Q hQ
  obtain ⟨P, hP, rfl⟩ := Multiset.mem_map.mp hQ
  obtain ⟨hi, hp, hdiv⟩ := (Polynomial.mem_normalizedFactors_iff hm.ne_zero).mp hP
  apply finiteField_irreducible_splits F E hi hp
  exact (Nat.dvd_factorial hi.natDegree_pos
    ((natDegree_le_of_dvd hdiv hm.ne_zero).trans hn)).trans hd

#print axioms finiteField_irreducible_splits
#print axioms finiteField_bounded_monic_splits
end GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts

namespace GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts
open MulAction
variable {E : Type*} [Field E] {n : ℕ}
local instance : MulAction (Equiv.Perm (Fin n)) (Fin n → E) :=
  permutationTupleAction E (Equiv.Perm (Fin n)) (Fin n)

/-- The coefficient polynomial associated to an ordered tuple of roots. -/
def tupleRootPolynomial (x : Fin n → E) : E[X] := ∏ i, (X - C (x i))

/-- Root multiplicities are retained, including colliding coordinates. -/
theorem tupleRootPolynomial_roots (x : Fin n → E) :
    (tupleRootPolynomial x).roots = (Finset.univ.val.map x) := by
  classical
  have h : tupleRootPolynomial x =
      ((Finset.univ.val.map x).map (fun a => X - C a)).prod := by
    rw [Multiset.map_map]
    rfl
  rw [h, roots_multiset_prod_X_sub_C]

/-- Reordering the roots does not change their coefficient polynomial. -/
theorem tupleRootPolynomial_smul (g : Equiv.Perm (Fin n)) (x : Fin n → E) :
    tupleRootPolynomial (g • x) = tupleRootPolynomial x := by
  classical
  exact Fintype.prod_equiv g.symm _ _ (fun _ => rfl)

/-- Equality of coefficient polynomials is exactly equality of permutation orbits. -/
theorem tupleRootPolynomial_eq_iff (x y : Fin n → E) :
    tupleRootPolynomial x = tupleRootPolynomial y ↔
      (Quotient.mk'' x : Quotient (orbitRel (Equiv.Perm (Fin n)) (Fin n → E))) =
        Quotient.mk'' y := by
  classical
  constructor
  · intro h
    have hr := congrArg Polynomial.roots h
    rw [tupleRootPolynomial_roots, tupleRootPolynomial_roots] at hr
    -- Matching each root's occurrence fibre assembles the required permutation.
    have hc (a : E) : Fintype.card {i : Fin n // x i = a} =
        Fintype.card {i : Fin n // y i = a} := by
      rw [Fintype.card_subtype, Fintype.card_subtype]
      change (Multiset.filter (fun i => x i = a) (univ : Finset (Fin n)).val).card =
        (Multiset.filter (fun i => y i = a) (univ : Finset (Fin n)).val).card
      have hcount := congrArg (Multiset.count a) hr
      simpa only [Multiset.count_map, eq_comm] using hcount
    let e (a : E) : {i : Fin n // x i = a} ≃ {i : Fin n // y i = a} :=
      Fintype.equivOfCardEq (hc a)
    let σ : Equiv.Perm (Fin n) := Equiv.ofFiberEquiv e
    apply Quotient.sound
    change x ∈ orbit (Equiv.Perm (Fin n)) y
    refine ⟨σ⁻¹, ?_⟩
    change (fun i => y (σ i)) = x
    exact funext (Equiv.ofFiberEquiv_map e)
  · intro h
    obtain ⟨g, hg⟩ := Quotient.exact h
    rw [← hg, tupleRootPolynomial_smul]

#print axioms tupleRootPolynomial_roots
#print axioms tupleRootPolynomial_smul
#print axioms tupleRootPolynomial_eq_iff
end GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts

namespace GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts
open MulAction ArithmeticGaugeTheory
variable (F E : Type*) [Field F] [Field E] [Algebra F E] [Fintype F] [Fintype E]
  (n : ℕ)
local instance : MulAction (Equiv.Perm (Fin n)) (Fin n → E) :=
  permutationTupleAction E (Equiv.Perm (Fin n)) (Fin n)
attribute [local instance] Classical.propDecidable

/-- A root ordering exists in the common factorial-degree extension. -/
theorem monic_exists_root_tuple (hd : n.factorial ∣ finrank F E)
    (f : monicOfDeg F n) :
    ∃ x : Fin n → E, f.val.map (algebraMap F E) = tupleRootPolynomial x := by
  obtain ⟨hm, hn⟩ := mem_monicOfDeg.mp f.property
  classical
  have hs := finiteField_bounded_monic_splits F E hd hm hn.le
  let r := (f.val.map (algebraMap F E)).roots.toList
  have hr : r.length = n := by
    rw [Multiset.length_toList, ← hs.natDegree_eq_card_roots,
      natDegree_map_eq_of_injective (algebraMap F E).injective, hn]
  let e := (finCongr hr).symm
  refine ⟨fun i => r.get (e i), ?_⟩
  have hp : ∀ l : List E, (l.map (fun a => X - C a)).prod =
      ∏ i : Fin l.length, (X - C (l.get i)) := by
    intro l
    conv_lhs => rw [← List.ofFn_get l]
    rw [List.map_ofFn, List.prod_ofFn]
    rfl
  rw [hs.eq_prod_roots_of_monic (hm.map _),
    ← Multiset.coe_toList (f.val.map (algebraMap F E)).roots,
    Multiset.map_coe, Multiset.prod_coe, hp]
  exact Fintype.prod_equiv (finCongr hr) _ _ (fun i => by
    change X - C (r.get i) = X - C (r.get (e ((finCongr hr) i)))
    rw [Equiv.symm_apply_apply])

/-- An ordered root tuple, used only through its permutation orbit. -/
def monicRootTuple (hd : n.factorial ∣ finrank F E) (f : monicOfDeg F n) : Fin n → E :=
  (monic_exists_root_tuple F E n hd f).choose

theorem monicRootTuple_spec (hd : n.factorial ∣ finrank F E) (f : monicOfDeg F n) :
    f.val.map (algebraMap F E) = tupleRootPolynomial (monicRootTuple F E n hd f) :=
  (monic_exists_root_tuple F E n hd f).choose_spec

/-- The arithmetic Frobenius preserves the polynomial of a root tuple over the base field. -/
theorem monicRootTuple_frobenius (hd : n.factorial ∣ finrank F E) (f : monicOfDeg F n) :
    tupleFrobenius F E (Equiv.Perm (Fin n)) (Fin n) (monicRootTuple F E n hd f) ∈
      orbit (Equiv.Perm (Fin n)) (monicRootTuple F E n hd f) := by
  let x := monicRootTuple F E n hd f
  let σ := FiniteField.frobeniusAlgEquivOfAlgebraic F E
  have hx : tupleRootPolynomial x = f.val.map (algebraMap F E) :=
    (monicRootTuple_spec F E n hd f).symm
  have hφ : tupleRootPolynomial (tupleFrobenius F E (Equiv.Perm (Fin n)) (Fin n) x) =
      (tupleRootPolynomial x).map σ.toRingHom := by
    simp only [tupleRootPolynomial, Polynomial.map_prod, Polynomial.map_sub,
      Polynomial.map_X, Polynomial.map_C]
    rfl
  have hcoeff : σ.toRingHom.comp (algebraMap F E) = algebraMap F E := by
    ext a
    exact σ.commutes a
  have heq : tupleRootPolynomial
      (tupleFrobenius F E (Equiv.Perm (Fin n)) (Fin n) x) = tupleRootPolynomial x := by
    rw [hφ, hx, Polynomial.map_map, hcoeff]
  exact Quotient.exact ((tupleRootPolynomial_eq_iff _ _).mp heq)

/-- Vieta sends each monic polynomial to its arithmetic Frobenius-stable root orbit. -/
def monicRootOrbit (hd : n.factorial ∣ finrank F E) (f : monicOfDeg F n) :
    frobeniusTupleOrbits F E (Equiv.Perm (Fin n)) (Fin n) := by
  let x := monicRootTuple F E n hd f
  let q : Quotient (orbitRel (Equiv.Perm (Fin n)) (Fin n → E)) := Quotient.mk'' x
  refine ⟨q, ?_⟩
  simp only [frobeniusTupleOrbits, equivariantFixedOrbits, Finset.mem_filter,
    Finset.mem_univ, true_and]
  have hx : x ∈ orbit (Equiv.Perm (Fin n)) q.out :=
    Quotient.exact (Quotient.out_eq q).symm
  exact (transporter_exists_on_orbit
    (tupleFrobenius F E (Equiv.Perm (Fin n)) (Fin n)) hx).mp
      (monicRootTuple_frobenius F E n hd f)

/-- The coefficient polynomial recovers the original monic polynomial from its orbit. -/
theorem monicRootOrbit_injective (hd : n.factorial ∣ finrank F E) :
    Function.Injective (monicRootOrbit F E n hd) := by
  intro f g h
  apply Subtype.ext
  apply Polynomial.map_injective (algebraMap F E) (algebraMap F E).injective
  rw [monicRootTuple_spec F E n hd f, monicRootTuple_spec F E n hd g]
  exact (tupleRootPolynomial_eq_iff _ _).mpr (congrArg Subtype.val h)

#print axioms monic_exists_root_tuple
#print axioms monicRootTuple_frobenius
#print axioms monicRootOrbit_injective
end GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts

namespace GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts
open MulAction ArithmeticGaugeTheory
variable (F E : Type*) [Field F] [Field E] [Algebra F E] [Fintype F] [Fintype E]
  (n : ℕ)
local instance : MulAction (Equiv.Perm (Fin n)) (Fin n → E) :=
  permutationTupleAction E (Equiv.Perm (Fin n)) (Fin n)
attribute [local instance] Classical.propDecidable

/-- Independent coefficient and normal-basis counts make Vieta onto the arithmetic orbits. -/
theorem monicRootOrbit_bijective (hd : n.factorial ∣ finrank F E) :
    Function.Bijective (monicRootOrbit F E n hd) := by
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  refine ⟨monicRootOrbit_injective F E n hd, ?_⟩
  rw [Fintype.card_coe, Fintype.card_coe, card_monicOfDeg]
  have hg : Fintype.card (Equiv.Perm (Fin n)) ∣ finrank F E := by
    simpa only [Fintype.card_perm, Fintype.card_fin] using hd
  simpa only [Fintype.card_fin] using (frobeniusTupleOrbits_card
    F E (Equiv.Perm (Fin n)) (Fin n) hg).symm

/-- Vieta's arithmetic bijection retains every root multiplicity. -/
def monicFrobeniusOrbitEquiv (hd : n.factorial ∣ finrank F E) :
    monicOfDeg F n ≃ frobeniusTupleOrbits F E (Equiv.Perm (Fin n)) (Fin n) :=
  Equiv.ofBijective (monicRootOrbit F E n hd) (monicRootOrbit_bijective F E n hd)

/-- The coefficient polynomial of a stable tuple orbit is uniquely defined over the base field. -/
theorem frobeniusOrbit_unique_monic (hd : n.factorial ∣ finrank F E)
    (q : frobeniusTupleOrbits F E (Equiv.Perm (Fin n)) (Fin n)) :
    ∃! f : monicOfDeg F n, monicRootOrbit F E n hd f = q := by
  obtain ⟨f, hf⟩ := (monicRootOrbit_bijective F E n hd).surjective q
  exact ⟨f, hf, fun g hg => (monicRootOrbit_injective F E n hd) (hg.trans hf.symm)⟩

#print axioms monicRootOrbit_bijective
#print axioms monicFrobeniusOrbitEquiv
#print axioms frobeniusOrbit_unique_monic
end GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts

namespace GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts
open ArithmeticGaugeTheory FiniteField
variable (F : Type*) [Field F] [Fintype F]
  (p : ℕ) [Fact p.Prime] [CharP F p] (n : ℕ)
attribute [local instance] Classical.propDecidable

/-- The actual finite extension gives an unconditional arithmetic Vieta equivalence. -/
def arithmeticVietaEquiv :
    monicOfDeg F n ≃ arithmeticFrobeniusOrbits F p (Equiv.Perm (Fin n)) (Fin n) := by
  let E := Extension F p (Fintype.card (Equiv.Perm (Fin n)))
  letI : Fintype E := Fintype.ofFinite E
  exact monicFrobeniusOrbitEquiv F E n (by
    change n.factorial ∣ finrank F (Extension F p (Fintype.card (Equiv.Perm (Fin n))))
    simp only [finrank_extension, Fintype.card_perm, Fintype.card_fin, dvd_refl])

#print axioms arithmeticVietaEquiv
end GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts
