import GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts.FiniteFieldVieta
import GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts.FiniteFieldSignedOrbits
import GaloisForLFunctions.HTGeometry.GaloisFixedByAll
import GaloisForLFunctions.HTGeometry.VandermondeSign
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic

/-!
# Independent root-orientation cover counts

The square of the Vandermonde coordinate defines an actual finite cover
of monic coefficient polynomials in a common finite extension. Collisions
have one point; Frobenius-preserved and reversed orientations have two
and zero points. Independent signed transporter counts give q^n points
in every degree at least two over an odd finite field.
-/

noncomputable section
open Finset FiniteField
namespace GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts
variable (F E : Type*) [Field F] [Field E] [Algebra F E] [Fintype F] [Fintype E]
attribute [local instance] Classical.propDecidable

/-- Frobenius-fixed elements of the finite extension descend to the base field. -/
theorem exists_base_of_frobenius_fixed {v : E} (hv : v ^ Fintype.card F = v) :
    ∃ a : F, algebraMap F E a = v := by
  apply HTGeometry.exists_algebraMap_of_forall_fixed
  have hi (m : ℕ) : (frobeniusAlgEquivOfAlgebraic F E ^ m) v = v := by
    induction m with
    | zero => rfl
    | succ m hm =>
      rw [pow_succ, AlgEquiv.mul_apply]
      change (frobeniusAlgEquivOfAlgebraic F E ^ m) (v ^ Fintype.card F) = v
      rw [hv, hm]
  intro σ
  obtain ⟨m, rfl⟩ := (bijective_frobeniusAlgEquivOfAlgebraic_pow F E).surjective σ
  exact hi m.val

/-- Base-field solutions to the square of an extension-field orientation coordinate. -/
def baseOrientationFibre (v : E) : Finset F :=
  univ.filter (fun y => (algebraMap F E y) ^ 2 = v ^ 2)

omit [Fintype E] in
/-- Ramification leaves exactly the zero point in the orientation fibre. -/
theorem baseOrientationFibre_zero : baseOrientationFibre F E 0 = {0} := by
  classical
  ext y
  simp only [baseOrientationFibre, mem_filter, mem_univ, true_and,
    zero_pow two_ne_zero, mem_singleton]
  constructor
  · intro h
    apply (algebraMap F E).injective
    simpa only [map_zero] using (sq_eq_zero_iff.mp h)
  · rintro rfl
    simp only [map_zero, zero_pow two_ne_zero]

/-- A nonzero base-field orientation coordinate has exactly two square roots. -/
theorem baseOrientationFibre_card_of_fixed (hF : ringChar F ≠ 2) {v : E}
    (hne : v ≠ 0) (hv : v ^ Fintype.card F = v) :
    ((baseOrientationFibre F E v).card : ℤ) = 2 := by
  classical
  obtain ⟨a, ha⟩ := exists_base_of_frobenius_fixed F E hv
  have ha0 : a ≠ 0 := by
    intro h
    apply hne
    simpa only [h, map_zero] using ha.symm
  have hf : baseOrientationFibre F E v = univ.filter (fun y : F => y ^ 2 = a ^ 2) := by
    ext y
    simp only [baseOrientationFibre, mem_filter, mem_univ, true_and, ← ha, ← map_pow]
    exact (algebraMap F E).injective.eq_iff
  have hc := quadraticChar_card_sqrts hF (a ^ 2)
  rw [quadraticChar_sq_one' ha0] at hc
  simpa only [hf, Set.toFinset_setOf, one_add_one_eq_two] using hc

/-- A nonzero orientation reversed by Frobenius has no base-field square roots. -/
theorem baseOrientationFibre_empty_of_neg (hF : ringChar F ≠ 2) {v : E}
    (hne : v ≠ 0) (hv : v ^ Fintype.card F = -v) :
    baseOrientationFibre F E v = ∅ := by
  classical
  ext y
  constructor
  · intro hy
    exfalso
    have hs := (mem_filter.mp hy).2
    have he : ∃ a : F, algebraMap F E a = v := by
      rcases sq_eq_sq_iff_eq_or_eq_neg.mp hs with h | h
      · exact ⟨y, h⟩
      · exact ⟨-y, by rw [map_neg, h, neg_neg]⟩
    obtain ⟨a, ha⟩ := he
    have hfix : v ^ Fintype.card F = v := by
      have h := (frobeniusAlgEquivOfAlgebraic F E).commutes a
      change (algebraMap F E a) ^ Fintype.card F = algebraMap F E a at h
      rwa [ha] at h
    have hneg : (-1 : E) = 1 := by
      apply mul_right_cancel₀ hne
      simpa only [neg_one_mul, one_mul] using hv.symm.trans hfix
    apply Ring.neg_one_ne_one_of_char_ne_two hF
    apply (algebraMap F E).injective
    simpa only [map_neg, map_one] using hneg

  · intro hy
    simp at hy

#print axioms baseOrientationFibre_zero
#print axioms baseOrientationFibre_card_of_fixed
#print axioms baseOrientationFibre_empty_of_neg

/-- The actual root-discriminant cover, retaining the ramified fibre at every collision. -/
def rootOrientationCover (n : ℕ) (hd : n.factorial ∣ Module.finrank F E) :
    Finset (ArithmeticGaugeTheory.monicOfDeg F n × F) :=
  univ.filter (fun fy => (algebraMap F E fy.2) ^ 2 =
    HTGeometry.vandermondeProd (monicRootTuple F E n hd fy.1) ^ 2)

#print axioms exists_base_of_frobenius_fixed
end GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts

namespace GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts
open MulAction Equiv HTGeometry
variable (F E : Type*) [Field F] [Field E] [Algebra F E] [Fintype F] [Fintype E]
  (n : ℕ)
local instance : MulAction (Perm (Fin n)) (Fin n → E) :=
  permutationTupleAction E (Perm (Fin n)) (Fin n)
attribute [local instance] Classical.propDecidable

omit [Fintype E] in
/-- Squaring removes the ordering ambiguity of the Vandermonde orientation. -/
theorem vandermonde_square_eq_of_orbit (x y : Fin n → E)
    (h : (Quotient.mk'' x : Quotient (orbitRel (Perm (Fin n)) (Fin n → E))) =
      Quotient.mk'' y) : vandermondeProd x ^ 2 = vandermondeProd y ^ 2 := by
  obtain ⟨g, hg⟩ := Quotient.exact h
  rw [← hg]
  change vandermondeProd (y ∘ g.symm) ^ 2 = _
  rw [vandermondeProd_comp]
  rcases Int.units_eq_one_or (Perm.sign g.symm) with hs | hs <;> simp only [hs,
    Units.val_one, Units.val_neg, neg_smul, one_smul, neg_sq]

/-- The Vandermonde polynomial commutes with arithmetic Frobenius. -/
theorem vandermonde_frobenius (x : Fin n → E) :
    vandermondeProd (tupleFrobenius F E (Perm (Fin n)) (Fin n) x) =
      vandermondeProd x ^ Fintype.card F := by
  change vandermondeProd (fun i => (frobeniusAlgEquivOfAlgebraic F E) (x i)) =
    (frobeniusAlgEquivOfAlgebraic F E) (vandermondeProd x)
  simp only [vandermondeProd, map_prod, map_sub]

/-- Every stable orbit contributes one plus its signed orientation weight to the actual cover. -/
theorem baseOrientationFibre_card_eq_weight (hF : ringChar F ≠ 2)
    (q : frobeniusTupleOrbits F E (Perm (Fin n)) (Fin n)) :
    ((baseOrientationFibre F E (vandermondeProd q.val.out)).card : ℚ) =
      1 + orientationOrbitWeight (tupleFrobenius F E (Perm (Fin n)) (Fin n))
        Perm.sign q.val := by
  classical
  by_cases hx : Function.Injective q.val.out
  · have hne := vandermondeProd_ne_zero hx
    have hfixed : tupleFrobenius F E (Perm (Fin n)) (Fin n) q.val.out ∈
        orbit (Perm (Fin n)) q.val.out := by
      simpa only [frobeniusTupleOrbits, equivariantFixedOrbits, mem_filter,
        mem_univ, true_and] using q.property
    obtain ⟨g, hg⟩ := hfixed
    have hv : vandermondeProd q.val.out ^ Fintype.card F =
        (Perm.sign g⁻¹ : ℤ) • vandermondeProd q.val.out := by
      rw [← vandermonde_frobenius F E n, ← hg]
      change vandermondeProd (q.val.out ∘ g.symm) = _
      exact vandermondeProd_comp q.val.out g.symm
    rw [frobeniusOrientationWeight_eq_sign F E (Fin n) q.val hx g hg]
    rcases Int.units_eq_one_or (Perm.sign g) with hs | hs
    · simp only [map_inv, hs, inv_one, Units.val_one, one_smul] at hv
      have hc := baseOrientationFibre_card_of_fixed F E hF hne hv
      simp only [hs, Units.val_one, Int.cast_one]
      exact_mod_cast hc
    · simp only [map_inv, hs, inv_neg, inv_one, Units.val_neg, Units.val_one,
        neg_smul, one_smul] at hv
      rw [baseOrientationFibre_empty_of_neg F E hF hne hv]
      simp only [card_empty, Nat.cast_zero, hs, Units.val_neg, Units.val_one,
        Int.cast_neg, Int.cast_one, add_neg_cancel]
  · have hz : vandermondeProd q.val.out = 0 := by
      by_contra hn
      apply hx
      intro i j hij
      by_contra hne
      apply hn
      rw [← det_vandermonde_eq_vandermondeProd, Matrix.det_vandermonde_eq_zero_iff]
      exact ⟨i, j, hij, hne⟩
    rw [hz, baseOrientationFibre_zero,
      frobeniusOrientationWeight_eq_zero_of_collision F E (Fin n) q.val hx]
    simp only [card_singleton, Nat.cast_one, add_zero]

#print axioms vandermonde_square_eq_of_orbit
#print axioms vandermonde_frobenius
#print axioms baseOrientationFibre_card_eq_weight
end GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts

namespace GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts
open MulAction Equiv ArithmeticGaugeTheory HTGeometry
variable (F E : Type*) [Field F] [Field E] [Algebra F E] [Fintype F] [Fintype E]
  (n : ℕ)
local instance : MulAction (Perm (Fin n)) (Fin n → E) :=
  permutationTupleAction E (Perm (Fin n)) (Fin n)
attribute [local instance] Classical.propDecidable

/-- Restricting to stable orbits retains the complete signed cancellation. -/
theorem sum_stableOrientationWeight_eq_zero [Nontrivial (Fin n)]
    (hd : n.factorial ∣ Module.finrank F E) :
    (∑ q : frobeniusTupleOrbits F E (Perm (Fin n)) (Fin n),
      orientationOrbitWeight (tupleFrobenius F E (Perm (Fin n)) (Fin n))
        Perm.sign q.val) = 0 := by
  classical
  obtain ⟨a, b, hab⟩ := exists_pair_ne (Fin n)
  have hdeg : Fintype.card (Perm (Fin n)) ∣ Module.finrank F E := by
    simpa only [Fintype.card_perm, Fintype.card_fin] using hd
  have hall := sum_frobeniusOrientationWeight_eq_zero F E (Perm (Fin n)) (Fin n)
    Perm.sign hdeg (swap a b) (Perm.sign_swap hab)
  rw [Finset.sum_coe_sort]
  calc
    _ = ∑ q : Quotient (orbitRel (Perm (Fin n)) (Fin n → E)),
        orientationOrbitWeight (tupleFrobenius F E (Perm (Fin n)) (Fin n)) Perm.sign q := by
      apply Finset.sum_subset (Finset.subset_univ _)
      intro q _ hq
      apply orientationOrbitWeight_eq_zero _ _ q
      left
      intro hf
      apply hq
      simpa only [frobeniusTupleOrbits, equivariantFixedOrbits, mem_filter,
        mem_univ, true_and] using hf
    _ = 0 := hall

/-- The actual root-discriminant cover has affine-space cardinality in degree at least two. -/
theorem rootOrientationCover_card [Nontrivial (Fin n)] (hF : ringChar F ≠ 2)
    (hd : n.factorial ∣ Module.finrank F E) :
    (rootOrientationCover F E n hd).card = Fintype.card F ^ n := by
  classical
  let e := monicFrobeniusOrbitEquiv F E n hd
  let w := fun q : Quotient (orbitRel (Perm (Fin n)) (Fin n → E)) =>
    orientationOrbitWeight (tupleFrobenius F E (Perm (Fin n)) (Fin n)) Perm.sign q
  have hfibre (f : monicOfDeg F n) :
      ((baseOrientationFibre F E (vandermondeProd (monicRootTuple F E n hd f))).card : ℚ) =
        1 + w (e f).val := by
    have hq : (Quotient.mk'' (monicRootTuple F E n hd f) :
        Quotient (orbitRel (Perm (Fin n)) (Fin n → E))) = (e f).val := rfl
    have hv := vandermonde_square_eq_of_orbit (E := E) (n := n)
      (monicRootTuple F E n hd f) (e f).val.out
      (hq.trans (Quotient.out_eq (e f).val).symm)
    have heq : baseOrientationFibre F E (vandermondeProd (monicRootTuple F E n hd f)) =
        baseOrientationFibre F E (vandermondeProd (e f).val.out) := by
      ext y
      simp only [baseOrientationFibre, mem_filter, mem_univ, true_and, hv]
    rw [heq]
    exact baseOrientationFibre_card_eq_weight F E n hF (e f)
  have hw : (∑ f : monicOfDeg F n, w (e f).val) = 0 := by
    calc
      _ = ∑ q : frobeniusTupleOrbits F E (Perm (Fin n)) (Fin n), w q.val :=
        Fintype.sum_equiv e _ _ (fun _ => rfl)
      _ = 0 := sum_stableOrientationWeight_eq_zero F E n hd
  have hc : ((rootOrientationCover F E n hd).card : ℚ) = (Fintype.card F : ℚ) ^ n := by
    calc
      _ = ∑ f : monicOfDeg F n,
          ((baseOrientationFibre F E (vandermondeProd (monicRootTuple F E n hd f))).card : ℚ) := by
        simp only [rootOrientationCover, baseOrientationFibre, card_eq_sum_ones,
          Nat.cast_sum, sum_filter]
        rw [← Finset.univ_product_univ]
        exact Finset.sum_product _ _ _
      _ = ∑ f : monicOfDeg F n, (1 + w (e f).val) := sum_congr rfl (fun f _ => hfibre f)
      _ = _ := by
        rw [sum_add_distrib, hw, add_zero, sum_const, card_univ, nsmul_eq_mul, mul_one,
          Fintype.card_coe, card_monicOfDeg, Nat.cast_pow]
  exact_mod_cast hc

#print axioms sum_stableOrientationWeight_eq_zero
#print axioms rootOrientationCover_card
end GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts

namespace GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts
open FiniteField ArithmeticGaugeTheory Equiv
variable (F : Type*) [Field F] [Fintype F]
  (p : ℕ) [Fact p.Prime] [CharP F p] (n : ℕ)
attribute [local instance] Classical.propDecidable

/-- The root-discriminant equation in the explicitly constructed common finite extension. -/
def arithmeticRootOrientationCover : Finset (monicOfDeg F n × F) := by
  let E := Extension F p (Fintype.card (Perm (Fin n)))
  letI : Fintype E := Fintype.ofFinite E
  exact rootOrientationCover F E n (by
    change n.factorial ∣ Module.finrank F (Extension F p (Fintype.card (Perm (Fin n))))
    simp only [finrank_extension, Fintype.card_perm, Fintype.card_fin, dvd_refl])

/-- Independent signed transporters count the actual arithmetic cover in every degree at least two. -/
theorem arithmeticRootOrientationCover_card [Nontrivial (Fin n)] (hF : ringChar F ≠ 2) :
    (arithmeticRootOrientationCover F p n).card = Fintype.card F ^ n := by
  letI : Fintype (Extension F p (Fintype.card (Perm (Fin n)))) := Fintype.ofFinite _
  unfold arithmeticRootOrientationCover
  apply rootOrientationCover_card
  exact hF

#print axioms arithmeticRootOrientationCover
#print axioms arithmeticRootOrientationCover_card
end GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts
