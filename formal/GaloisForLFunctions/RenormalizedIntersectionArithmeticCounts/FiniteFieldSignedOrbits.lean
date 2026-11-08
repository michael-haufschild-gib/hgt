import GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts.FiniteFieldOrbitCounts
import Mathlib.GroupTheory.Perm.Sign

/-!
# Signed Frobenius orbits

Actual transporter sets define orbit orientation weights in {-1,0,1}.
Odd stabilizers cancel opposite signs; fixed orbits with even stabilizers
retain their Frobenius orientation. Independent normal-basis counts force
exact cancellation for permutation actions with at least two labels.
-/

noncomputable section
attribute [local instance] Classical.propDecidable
namespace GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts
open Finset MulAction
variable {G X : Type*} [Group G] [MulAction G X] [Fintype G] [Fintype X]

/-- Signed count of actual transporters from a point to its arithmetic image. -/
def transporterSignSum (φ : X →[G] X) (χ : G →* ℤˣ) (x : X) : ℤ := by
  classical
  exact ∑ g : G, if g • x = φ x then (χ g : ℤ) else 0

omit [Fintype X] in
/-- An orientation-reversing stabilizer pairs transporters of opposite signs. -/
theorem transporterSignSum_eq_zero_of_odd_stabilizer
    (φ : X →[G] X) (χ : G →* ℤˣ) (x : X) (h : G)
    (hx : h • x = x) (hχ : χ h = -1) : transporterSignSum φ χ x = 0 := by
  classical
  have he : transporterSignSum φ χ x = -transporterSignSum φ χ x := by
    unfold transporterSignSum
    rw [← sum_neg_distrib]
    apply Fintype.sum_equiv (Equiv.mulRight h)
    intro g
    change (if g • x = φ x then (χ g : ℤ) else 0) =
      -(if (g * h) • x = φ x then (χ (g * h) : ℤ) else 0)
    simp only [mul_smul, hx, map_mul, hχ, Units.val_neg, 
      mul_neg, mul_one]
    split_ifs <;> omega
  omega

/-- Summing signed transporters by their group label counts each arithmetic twist. -/
theorem sum_transporterSignSum (φ : X →[G] X) (χ : G →* ℤˣ) :
    (∑ x : X, transporterSignSum φ χ x) =
      ∑ g : G, (χ g : ℤ) * Nat.card {x : X // g • x = φ x} := by
  classical
  unfold transporterSignSum
  rw [sum_comm]
  apply sum_congr rfl
  intro g _
  rw [← sum_filter, sum_const, nsmul_eq_mul]
  simp only [Nat.card_eq_fintype_card, Fintype.card_subtype]
  exact mul_comm _ _

/-- Signed transporter mass assigned to its actual orbit, including all stabilizers. -/
def orientationOrbitNumerator (φ : X →[G] X) (χ : G →* ℤˣ)
    (q : Quotient (orbitRel G X)) : ℤ := by
  classical
  exact ∑ x : X, if Quotient.mk (orbitRel G X) x = q then transporterSignSum φ χ x else 0

/-- The orbit decomposition retains the complete signed transporter count. -/
theorem sum_orientationOrbitNumerator (φ : X →[G] X) (χ : G →* ℤˣ) :
    (∑ q : Quotient (orbitRel G X), orientationOrbitNumerator φ χ q) =
      ∑ g : G, (χ g : ℤ) * Nat.card {x : X // g • x = φ x} := by
  classical
  rw [← sum_transporterSignSum φ χ]
  unfold orientationOrbitNumerator
  rw [sum_comm]
  apply sum_congr rfl
  intro x _
  simp

/-- Normalize each orbit's signed transporter mass by the acting group order. -/
def orientationOrbitWeight (φ : X →[G] X) (χ : G →* ℤˣ)
    (q : Quotient (orbitRel G X)) : ℚ :=
  (orientationOrbitNumerator φ χ q : ℚ) / Fintype.card G

omit [Fintype G] [Fintype X] in
private theorem orbitClass_eq_iff (x : X) (q : Quotient (orbitRel G X)) :
    Quotient.mk (orbitRel G X) x = q ↔ x ∈ orbit G q.out := by
  constructor
  · intro h
    exact Quotient.exact (h.trans (Quotient.out_eq q).symm)
  · intro h
    exact (Quotient.sound h).trans (Quotient.out_eq q)

/-- Orbit orientation mass is a sum over the actual points of the orbit. -/
theorem orientationOrbitNumerator_eq_sum_orbit (φ : X →[G] X) (χ : G →* ℤˣ)
    (q : Quotient (orbitRel G X)) : orientationOrbitNumerator φ χ q =
      ∑ x : orbit G q.out, transporterSignSum φ χ x.val := by
  classical
  unfold orientationOrbitNumerator
  simp_rw [orbitClass_eq_iff]
  rw [← sum_filter]
  exact sum_subtype _ (fun _ => by simp) _

omit [Fintype X] in
private theorem transporterSignSum_eq_zero_of_not_in_orbit
    (φ : X →[G] X) (χ : G →* ℤˣ) (x : X) (hx : φ x ∉ orbit G x) :
    transporterSignSum φ χ x = 0 := by
  classical
  unfold transporterSignSum
  apply sum_eq_zero
  intro g _
  exact if_neg (fun h => hx ⟨g, h⟩)

/-- Orbits not preserved by the arithmetic map have zero orientation mass. -/
theorem orientationOrbitNumerator_eq_zero_of_not_fixed
    (φ : X →[G] X) (χ : G →* ℤˣ) (q : Quotient (orbitRel G X))
    (hq : φ q.out ∉ orbit G q.out) : orientationOrbitNumerator φ χ q = 0 := by
  classical
  rw [orientationOrbitNumerator_eq_sum_orbit]
  apply sum_eq_zero
  intro x _
  apply transporterSignSum_eq_zero_of_not_in_orbit
  exact fun hx => hq ((transporter_exists_on_orbit φ x.property).mp hx)

/-- An odd stabilizer cancels the complete orientation mass of its orbit. -/
theorem orientationOrbitNumerator_eq_zero_of_odd_stabilizer
    (φ : X →[G] X) (χ : G →* ℤˣ) (q : Quotient (orbitRel G X)) (h : G)
    (hx : h • q.out = q.out) (hχ : χ h = -1) :
    orientationOrbitNumerator φ χ q = 0 := by
  classical
  rw [orientationOrbitNumerator_eq_sum_orbit]
  apply sum_eq_zero
  intro x _
  obtain ⟨a, ha⟩ := x.property
  apply transporterSignSum_eq_zero_of_odd_stabilizer φ χ x.val (a * h * a⁻¹)
  · change a • q.out = x.val at ha
    rw [← ha, mul_smul, mul_smul, inv_smul_smul, hx]
  · simp only [map_mul, map_inv, hχ, mul_neg, mul_one, neg_mul, mul_inv_cancel]

/-- Orientation weights vanish on non-fixed orbits and on orbits with odd stabilizers. -/
theorem orientationOrbitWeight_eq_zero
    (φ : X →[G] X) (χ : G →* ℤˣ) (q : Quotient (orbitRel G X))
    (hq : φ q.out ∉ orbit G q.out ∨ ∃ h : G, h • q.out = q.out ∧ χ h = -1) :
    orientationOrbitWeight φ χ q = 0 := by
  have hz : orientationOrbitNumerator φ χ q = 0 := by
    rcases hq with hn | ⟨h, hx, hχ⟩
    · exact orientationOrbitNumerator_eq_zero_of_not_fixed φ χ q hn
    · exact orientationOrbitNumerator_eq_zero_of_odd_stabilizer φ χ q h hx hχ
  simp only [orientationOrbitWeight, hz, Int.cast_zero, zero_div]

#print axioms orientationOrbitNumerator_eq_sum_orbit
#print axioms orientationOrbitNumerator_eq_zero_of_not_fixed
#print axioms orientationOrbitNumerator_eq_zero_of_odd_stabilizer
#print axioms orientationOrbitWeight_eq_zero

#print axioms transporterSignSum_eq_zero_of_odd_stabilizer
#print axioms sum_transporterSignSum
#print axioms sum_orientationOrbitNumerator
end GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts

namespace GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts
open Finset MulAction Module
variable {G : Type*} [Group G] [Fintype G]

private theorem sum_character_eq_zero_of_odd (χ : G →* ℤˣ) (h : G) (hχ : χ h = -1) :
    (∑ g : G, (χ g : ℤ)) = 0 := by
  classical
  have he : (∑ g : G, (χ g : ℤ)) = -(∑ g : G, (χ g : ℤ)) := by
    rw [← sum_neg_distrib]
    apply Fintype.sum_equiv (Equiv.mulRight h)
    intro g
    change (χ g : ℤ) = -(χ (g * h) : ℤ)
    simp only [map_mul, hχ, Units.val_neg, 
      mul_neg, mul_one, neg_neg]
  omega

end GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts

namespace GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts
open Finset MulAction Module
variable (F E G I : Type*) [Field F] [Field E] [Algebra F E]
  [Fintype F] [Fintype E] [Group G] [Fintype G] [Fintype I] [DecidableEq I] [MulAction G I]
local instance : MulAction G (I → E) := permutationTupleAction E G I

/-- The signed orbit mass is obtained from independent permutation-twist counts. -/
theorem sum_frobeniusOrientationNumerator (χ : G →* ℤˣ)
    (hd : Fintype.card G ∣ finrank F E) :
    (∑ q : Quotient (orbitRel G (I → E)),
      orientationOrbitNumerator (tupleFrobenius F E G I) χ q) =
        (Fintype.card F ^ Fintype.card I : ℤ) * ∑ g : G, (χ g : ℤ) := by
  classical
  rw [sum_orientationOrbitNumerator]
  have ht (g : G) : Nat.card {x : I → E // g • x = tupleFrobenius F E G I x} =
      Fintype.card F ^ Fintype.card I := by
    let e : {x : I → E // g • x = tupleFrobenius F E G I x} ≃
        frobeniusTwistedTuples F E G I g⁻¹ :=
      Equiv.subtypeEquivRight (fun _ => funext_iff)
    rw [Nat.card_congr e]
    have ho : orderOf (g⁻¹) ∣ Fintype.card G := by
      simpa only [Fintype.card_eq_nat_card] using (orderOf_dvd_natCard (x := g⁻¹))
    exact frobeniusTwistedTuples_card F E G I g⁻¹ (ho.trans hd)
  simp_rw [ht, Nat.cast_pow]
  rw [← sum_mul, mul_comm]

/-- A sign-reversing group element forces exact cancellation of the orbit orientation weights. -/
theorem sum_frobeniusOrientationWeight_eq_zero (χ : G →* ℤˣ)
    (hd : Fintype.card G ∣ finrank F E) (h : G) (hχ : χ h = -1) :
    (∑ q : Quotient (orbitRel G (I → E)),
      orientationOrbitWeight (tupleFrobenius F E G I) χ q) = 0 := by
  classical
  unfold orientationOrbitWeight
  simp only [div_eq_mul_inv]
  rw [← sum_mul, ← Int.cast_sum, sum_frobeniusOrientationNumerator F E G I χ hd,
    sum_character_eq_zero_of_odd χ h hχ, mul_zero, Int.cast_zero, zero_mul]

#print axioms sum_frobeniusOrientationNumerator
#print axioms sum_frobeniusOrientationWeight_eq_zero
end GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts

namespace GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts
open FiniteField Finset MulAction Equiv
variable (F : Type*) [Field F] [Fintype F] (p : ℕ) [Fact p.Prime] [CharP F p]
  (I : Type*) [Fintype I] [DecidableEq I]

/-- The total Frobenius orientation weight over permutation orbits. -/
def arithmeticOrientationSum : ℚ :=
  let E := Extension F p (Fintype.card (Perm I))
  letI : Fintype E := Fintype.ofFinite E
  letI : MulAction (Perm I) (I → E) := permutationTupleAction E (Perm I) I
  ∑ q : Quotient (orbitRel (Perm I) (I → E)),
    orientationOrbitWeight (tupleFrobenius F E (Perm I) I) Perm.sign q

/-- With at least two labels the arithmetic orientation weights cancel exactly. -/
theorem arithmeticOrientationSum_eq_zero [Nontrivial I] : arithmeticOrientationSum F p I = 0 := by
  let E := Extension F p (Fintype.card (Perm I))
  letI : Fintype E := Fintype.ofFinite E
  letI : MulAction (Perm I) (I → E) := permutationTupleAction E (Perm I) I
  obtain ⟨a, b, hab⟩ := exists_pair_ne I
  apply sum_frobeniusOrientationWeight_eq_zero F E (Perm I) I Perm.sign
    (by simpa only [E, finrank_extension] using (dvd_rfl : Fintype.card (Perm I) ∣ Fintype.card (Perm I)))
    (swap a b)
  exact Perm.sign_swap hab

#print axioms arithmeticOrientationSum_eq_zero
end GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts


namespace GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts
open Finset MulAction
variable {G X : Type*} [Group G] [MulAction G X] [Fintype G] [Fintype X]

omit [Fintype X] in
private theorem transporterSignSum_eq_sum (φ : X →[G] X) (χ : G →* ℤˣ) (x : X) :
    transporterSignSum φ χ x = ∑ g : {g : G // g • x = φ x}, (χ g.val : ℤ) := by
  classical
  unfold transporterSignSum
  rw [← sum_filter]
  exact sum_subtype _ (fun _ => by simp) _

/-- Orbit mass counts the signed transporter pairs in that orbit. -/
theorem orientationOrbitNumerator_eq_sum_transporters
    (φ : X →[G] X) (χ : G →* ℤˣ) (q : Quotient (orbitRel G X)) :
    orientationOrbitNumerator φ χ q = ∑ t : orbitTransporters φ q, (χ t.2.val : ℤ) := by
  classical
  rw [orientationOrbitNumerator_eq_sum_orbit]
  simp_rw [transporterSignSum_eq_sum]
  exact (Fintype.sum_sigma (fun t : orbitTransporters φ q => (χ t.2.val : ℤ))).symm

omit [Fintype G] [Fintype X] in
/-- When the stabilizer preserves orientation, every transporter has the same sign. -/
private theorem orbit_transporter_character (φ : X →[G] X) (χ : G →* ℤˣ)
    (q : Quotient (orbitRel G X)) (g₀ : G) (hg : g₀ • q.out = φ q.out)
    (hstab : ∀ h : G, h • q.out = q.out → χ h = 1) (t : orbitTransporters φ q) :
    χ t.2.val = χ g₀ := by
  obtain ⟨a, ha⟩ := t.1.property
  change a • q.out = t.1.val at ha
  let z := g₀⁻¹ * a⁻¹ * t.2.val * a
  have hz : z • q.out = q.out := by
    dsimp only [z]
    rw [mul_smul, mul_smul, mul_smul]
    rw [ha, t.2.property, ← ha, φ.map_smul, inv_smul_smul, ← hg, inv_smul_smul]
  have hc := hstab z hz
  simp only [z, map_mul, map_inv] at hc
  rw [mul_assoc (χ g₀)⁻¹ (χ a)⁻¹ (χ t.2.val),
    mul_comm (χ a)⁻¹ (χ t.2.val),
    ← mul_assoc (χ g₀)⁻¹ (χ t.2.val) (χ a)⁻¹,
    mul_assoc ((χ g₀)⁻¹ * χ t.2.val) (χ a)⁻¹ (χ a), inv_mul_cancel, mul_one] at hc
  simpa only [mul_inv_cancel_left, mul_one] using congrArg (χ g₀ * ·) hc

/-- A fixed orbit with orientation-preserving stabilizer has one unit of signed weight. -/
theorem orientationOrbitWeight_eq_character (φ : X →[G] X) (χ : G →* ℤˣ)
    (q : Quotient (orbitRel G X)) (g₀ : G) (hg : g₀ • q.out = φ q.out)
    (hstab : ∀ h : G, h • q.out = q.out → χ h = 1) :
    orientationOrbitWeight φ χ q = ((χ g₀ : ℤ) : ℚ) := by
  classical
  have hn : orientationOrbitNumerator φ χ q = (Fintype.card G : ℤ) * (χ g₀ : ℤ) := by
    rw [orientationOrbitNumerator_eq_sum_transporters]
    have he := orbitTransportersEquiv φ q ⟨g₀, hg⟩
    calc
      _ = ∑ _t : orbitTransporters φ q, (χ g₀ : ℤ) :=
        sum_congr rfl (fun t _ => congrArg (fun u : ℤˣ => (u : ℤ))
          (orbit_transporter_character φ χ q g₀ hg hstab t))
      _ = _ := by rw [sum_const, card_univ, nsmul_eq_mul, Fintype.card_congr he]
  have hc : (Fintype.card G : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  simp only [orientationOrbitWeight, hn, Int.cast_mul, Int.cast_natCast]
  rw [mul_comm (Fintype.card G : ℚ), mul_div_assoc, div_self hc, mul_one]

#print axioms orientationOrbitNumerator_eq_sum_transporters
#print axioms orientationOrbitWeight_eq_character
end GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts


namespace GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts
open Finset MulAction
variable {G X : Type*} [Group G] [MulAction G X] [Fintype G] [Fintype X]

/-- Every orbit orientation weight is an integer in {-1,0,1}. -/
theorem orientationOrbitWeight_trichotomy (φ : X →[G] X) (χ : G →* ℤˣ)
    (q : Quotient (orbitRel G X)) : orientationOrbitWeight φ χ q = 0 ∨
      orientationOrbitWeight φ χ q = 1 ∨ orientationOrbitWeight φ χ q = -1 := by
  classical
  by_cases hf : φ q.out ∈ orbit G q.out
  · by_cases ho : ∃ h : G, h • q.out = q.out ∧ χ h = -1
    · exact Or.inl (orientationOrbitWeight_eq_zero φ χ q (Or.inr ho))
    · obtain ⟨g, hg⟩ := hf
      have hs : ∀ h : G, h • q.out = q.out → χ h = 1 := by
        intro h hh
        rcases Int.units_eq_one_or (χ h) with he | he
        · exact he
        · exact False.elim (ho ⟨h, hh, he⟩)
      rw [orientationOrbitWeight_eq_character φ χ q g hg hs]
      rcases Int.units_eq_one_or (χ g) with he | he
      · exact Or.inr (Or.inl (by simp only [he, Units.val_one, Int.cast_one]))
      · exact Or.inr (Or.inr (by simp only [he, Units.val_neg, Units.val_one,
          Int.cast_neg, Int.cast_one]))
  · exact Or.inl (orientationOrbitWeight_eq_zero φ χ q (Or.inl hf))

#print axioms orientationOrbitWeight_trichotomy
end GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts


namespace GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts
open Finset MulAction Equiv
section Swaps
variable {E I : Type*} [DecidableEq I]
local instance : MulAction (Perm I) (I → E) := permutationTupleAction E (Perm I) I

private theorem swap_stabilizes_tuple (x : I → E) {a b : I} (hab : x a = x b) :
    (swap a b : Perm I) • x = x := by
  funext i
  change x (swap a b i) = x i
  by_cases ha : i = a
  · subst i
    simpa only [swap_apply_left] using hab.symm
  · by_cases hb : i = b
    · subst i
      simpa only [swap_apply_right] using hab
    · rw [swap_apply_of_ne_of_ne ha hb]
end Swaps

variable (F E I : Type*) [Field F] [Field E] [Algebra F E]
  [Fintype F] [Fintype E] [Fintype I] [DecidableEq I]
local instance : MulAction (Perm I) (I → E) := permutationTupleAction E (Perm I) I

omit [Field F] [Algebra F E] in
/-- Repeated coordinates give zero Frobenius orientation weight through an actual odd stabilizer. -/
theorem frobeniusOrientationWeight_eq_zero_of_collision
    (q : Quotient (orbitRel (Perm I) (I → E))) (hx : ¬Function.Injective q.out) :
    orientationOrbitWeight (tupleFrobenius F E (Perm I) I) Perm.sign q = 0 := by
  have hp : ∃ a b : I, a ≠ b ∧ q.out a = q.out b := by
    by_contra h
    apply hx
    intro a b hab
    by_contra hne
    exact h ⟨a, b, hne, hab⟩
  obtain ⟨a, b, hab, heq⟩ := hp
  apply orientationOrbitWeight_eq_zero
  exact Or.inr ⟨swap a b, swap_stabilizes_tuple q.out heq, Perm.sign_swap hab⟩

omit [Field F] [Algebra F E] in
/-- Distinct coordinates retain precisely the sign of their Frobenius permutation. -/
theorem frobeniusOrientationWeight_eq_sign
    (q : Quotient (orbitRel (Perm I) (I → E))) (hx : Function.Injective q.out)
    (g : Perm I) (hg : g • q.out = tupleFrobenius F E (Perm I) I q.out) :
    orientationOrbitWeight (tupleFrobenius F E (Perm I) I) Perm.sign q =
      ((Perm.sign g : ℤ) : ℚ) := by
  apply orientationOrbitWeight_eq_character _ _ q g hg
  intro h hh
  have hi : h⁻¹ = 1 := by
    apply Equiv.ext
    intro i
    apply hx
    exact congrFun hh i
  have h1 : h = 1 := inv_eq_one.mp hi
  rw [h1, map_one]

#print axioms frobeniusOrientationWeight_eq_zero_of_collision
#print axioms frobeniusOrientationWeight_eq_sign
end GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts
