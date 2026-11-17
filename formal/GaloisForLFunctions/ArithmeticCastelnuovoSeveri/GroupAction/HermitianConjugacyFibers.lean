import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.GroupAction.HermitianTranslationCenter
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FiniteField.HermitianFiberCodes

/-!
# Conjugacy classes in the Hermitian translation group

The central shear of a Heisenberg group (Braverman–Kazhdan,
arXiv:2604.11735, §3.3) determines the orbital measures of this finite
group. Each noncentral conjugacy class is the full abscissa fiber.
The trace-one scalar gives an explicit conjugator in every characteristic.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
variable (p : ℕ) [Fact p.Prime] (s : ℕ)
local notation "Q" => p ^ (s + 1)
local notation "k₀" => SquareConstantField p s
local notation "G" => HermitianAffinePoint p s k₀

private theorem prescribed_shear (a d : k₀) (ha : a ≠ 0) (hd : d ^ Q = -d) :
    ∃ c : k₀, c ^ Q * a - a ^ Q * c = d := by
  let t := squareTraceOne p s
  have ht : t ^ Q + t = 1 := squareTraceOne_trace p s
  refine ⟨-(d * t / a ^ Q), ?_⟩
  have hneg (b : k₀) : (-b) ^ Q = -(b ^ Q) := map_neg (iterateFrobenius k₀ p (s+1)) b
  rw [hneg, div_pow, mul_pow, squareConstantField_frobenius_sq, hd]
  simp only [neg_mul, neg_div, neg_neg, mul_neg, sub_neg_eq_add, div_mul_cancel₀ _ ha]
  rw [mul_comm (a ^ Q) (_ / _), div_mul_cancel₀ _ (pow_ne_zero _ ha)]
  linear_combination d * ht

/-- Two translations are conjugate exactly on nonvertical abscissa fibers and on central singletons. -/
theorem hermitianTranslation_isConj_iff (P U : G) :
    IsConj P U ↔ P.val.1 = U.val.1 ∧ (P.val.1 = 0 → P = U) := by
  constructor
  · intro h
    obtain ⟨g, hg⟩ := isConj_iff.mp h
    have he : g * P = U * g := (mul_inv_eq_iff_eq_mul).mp hg
    have hx := congrArg (fun V : G => V.val.1) he
    change g.val.1 + P.val.1 = U.val.1 + g.val.1 at hx
    refine ⟨by linear_combination hx, fun hP => ?_⟩
    exact mul_right_cancel (((hermitianTranslation_commutes_iff p s P).2 hP g).trans he)
  · rintro ⟨hx, hcentral⟩
    by_cases hP : P.val.1 = 0
    · exact (hcentral hP) ▸ IsConj.refl _
    · let d := U.val.2 - P.val.2
      have hd : d ^ Q = -d := by
        have hU := U.property
        rw [← hx] at hU
        change (U.val.2 - P.val.2) ^ Q = -(U.val.2 - P.val.2)
        rw [show (U.val.2 - P.val.2) ^ Q = U.val.2 ^ Q - P.val.2 ^ Q from
          map_sub (iterateFrobenius k₀ p (s+1)) _ _]
        linear_combination hU - P.property
      obtain ⟨c, hc⟩ := prescribed_shear p s P.val.1 d hP hd
      let g := hermitianAffinePointWithFirst p s c
      apply isConj_iff.mpr
      refine ⟨g, mul_inv_eq_iff_eq_mul.mpr ?_⟩
      apply Subtype.ext
      apply Prod.ext
      · change c + P.val.1 = U.val.1 + c
        rw [hx, add_comm]
      · change g.val.2 + P.val.2 + c ^ Q * P.val.1 = U.val.2 + g.val.2 + U.val.1 ^ Q * c
        rw [← hx]
        change _ = U.val.2 - P.val.2 at hc
        linear_combination hc

open scoped Classical in
/-- Orbital support is a singleton on the center and a whole vertical fiber elsewhere. -/
theorem hermitian_conjugatesOf (P : G) :
    conjugatesOf P = if P.val.1 = 0 then {P} else {U : G | U.val.1 = P.val.1} := by
  ext U
  rw [conjugatesOf, Set.mem_setOf_eq, hermitianTranslation_isConj_iff]
  by_cases h : P.val.1 = 0
  · simp only [h, if_pos, true_implies, Set.mem_singleton_iff]
    exact ⟨fun hh => hh.2.symm, fun hh => ⟨by rw [hh, h], hh.symm⟩⟩
  · simp only [if_neg h, h, false_implies, and_true, Set.mem_setOf_eq]
    exact eq_comm

open scoped Classical in
/-- Cardinality of each orbital measure's support. -/
theorem hermitian_conjugates_card (P : G) :
    Nat.card (conjugatesOf P) = if P.val.1 = 0 then 1 else Q := by
  rw [hermitian_conjugatesOf]
  split_ifs
  · simp
  · exact hermitianFirstCoordinate_fiber_card p s P.val.1

/-- Parameter space for orbital kernels, one label per central point or nonzero abscissa. -/
abbrev HermitianClassParameters := {P : G // P.val.1 = 0} ⊕ {a : k₀ // a ≠ 0}

open scoped Classical in
def hermitianClassParameter (P : G) : HermitianClassParameters p s :=
  if h : P.val.1 = 0 then .inl ⟨P,h⟩ else .inr ⟨P.val.1,h⟩

private theorem classParameter_eq_iff (P U : G) :
    hermitianClassParameter p s P = hermitianClassParameter p s U ↔ IsConj P U := by
  rw [hermitianTranslation_isConj_iff]
  by_cases hP : P.val.1 = 0 <;> by_cases hU : U.val.1 = 0 <;>
    simp [hermitianClassParameter, hP, hU, Subtype.ext_iff]

/-- The conjugacy quotient is explicitly parametrized over the original constant field. -/
def hermitianConjClassesEquiv : ConjClasses G ≃ HermitianClassParameters p s :=
  let f : ConjClasses G → HermitianClassParameters p s :=
    Quotient.lift (hermitianClassParameter p s) fun P U h => (classParameter_eq_iff p s P U).2 h
  Equiv.ofBijective f ⟨by
    intro X Y
    obtain ⟨P, rfl⟩ := ConjClasses.mk_surjective X
    obtain ⟨U, rfl⟩ := ConjClasses.mk_surjective Y
    exact fun h => ConjClasses.mk_eq_mk_iff_isConj.mpr ((classParameter_eq_iff p s P U).1 h),
    by
      rintro (P | a)
      · exact ⟨ConjClasses.mk P.val, by change hermitianClassParameter p s P.val = _; simp [hermitianClassParameter, P.property]⟩
      · refine ⟨ConjClasses.mk (hermitianAffinePointWithFirst p s a.val), ?_⟩
        change (if h : a.val = 0 then Sum.inl _ else Sum.inr _) = _
        rw [dif_neg a.property]⟩

/-- Number of conjugacy classes, hence number of independent orbital kernels. -/
theorem hermitian_translation_class_number :
    Nat.card (ConjClasses G) = Q + (Q^2 - 1) := by
  have he : {P : G // P.val.1 = 0} ≃ {P : G // ∀ U : G, P * U = U * P} :=
    Equiv.subtypeEquivRight fun P => (hermitianTranslation_commutes_iff p s P).symm
  rw [Nat.card_congr (hermitianConjClassesEquiv p s), HermitianClassParameters, Nat.card_sum,
    Nat.card_congr he, hermitianTranslation_center_card,
    ← Nat.card_congr (unitsEquivNeZero (G₀ := k₀)), Nat.card_units, squareConstantField_card,
    Nat.mul_comm 2 (s+1), pow_mul]

#print axioms hermitianTranslation_isConj_iff
#print axioms hermitian_conjugatesOf
#print axioms hermitian_conjugates_card
#print axioms hermitian_translation_class_number
#print axioms hermitianConjClassesEquiv

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
