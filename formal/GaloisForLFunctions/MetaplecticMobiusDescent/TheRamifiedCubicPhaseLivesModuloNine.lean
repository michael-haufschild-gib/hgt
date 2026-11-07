/-
The composite supplementary laws and denominator congruence are adapted from
OpenAI’s formalization, Apache-2.0. See LICENSE and NOTICE for attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.TheRamifiedCubicSupplement

/-!
# Ramified cubic phases are fixed modulo nine

Primary factorization extends the prime supplementary laws multiplicatively.
The symbols of the cubic root, the ramified prime, and the different are
explicit linear functions of the primary coordinates modulo three. They are
therefore fixed by the denominator modulo nine. Factoring an arbitrary
numerator then gives the denominator congruence needed for the Kubota character.
-/

noncomputable section
open scoped BigOperators Classical
namespace GaloisForLFunctions.MetaplecticMobiusDescent
namespace CubicRamified
open Eisenstein CubicJacobi
private instance : IsCyclotomicExtension {3} ℚ K :=
  CyclotomicField.isCyclotomicExtension 3 ℚ
private instance : IsPrincipalIdealRing O :=
  IsCyclotomicExtension.Rat.three_pid K

/-- A cubic root indexed by an integer modulo three. -/
def cubicExp (n : ℤ) : O := omega ^ (n % 3).toNat

lemma cubicExp_eq_of_dvd_sub {a b : ℤ} (h : 3 ∣ a - b) : cubicExp a = cubicExp b := by
  obtain ⟨k, hk⟩ := h
  have heq : a % 3 = b % 3 := by omega
  simp only [cubicExp, heq]

lemma cubicExp_add (a b : ℤ) : cubicExp (a + b) = cubicExp a * cubicExp b := by
  simp only [cubicExp, ← pow_add]
  apply ((omega_primitive.isOfFinOrder (by decide)).pow_inj_mod).mpr
  rw [← omega_primitive.eq_orderOf]
  omega

@[simp] lemma cubicExp_zero : cubicExp 0 = 1 := by simp [cubicExp]

/-- A multiplicative phase on primary elements, read from their coordinates modulo nine. -/
def linearRay (u v : ℤ) (x : O) : O :=
  cubicExp (u * (((Eisenstein.Coordinates.coords x).1 - 1) / 3) +
    v * ((Eisenstein.Coordinates.coords x).2 / 3))

lemma linearRay_primaryCoord (u v A B : ℤ) :
    linearRay u v (primaryCoord A B) = cubicExp (u*A + v*B) := by
  simp only [linearRay, primaryCoord, Eisenstein.Coordinates.coords_eval]
  rw [show (1 + 3*A - 1) / 3 = A by omega,
    show 3*B / 3 = B by omega]

/-- Primary elements are exactly of the form `1+3A+3Bω`. -/
lemma exists_primaryCoord (x : O) (hx : lambda ^ 2 ∣ x - 1) :
    ∃ A B : ℤ, x = primaryCoord A B := by
  have hthree : (3 : O) ∣ lambda ^ 2 := by
    refine ⟨-omega, ?_⟩
    rw [lambda_sq_eq]
    ring
  obtain ⟨z, hz⟩ := hthree.trans hx
  obtain ⟨A, B, hAB⟩ := Eisenstein.Coordinates.exists_coordinates z
  change z = (A : O) + (B : O) * omega at hAB
  refine ⟨A, B, ?_⟩
  rw [primaryCoord_eq]
  rw [hAB] at hz
  linear_combination hz

lemma primaryCoord_mul (A B C D : ℤ) :
    primaryCoord A B * primaryCoord C D =
      primaryCoord (A+C+3*(A*C-B*D)) (B+D+3*(A*D+B*C-B*D)) := by
  simp only [primaryCoord, Eisenstein.Coordinates.eval_mul]
  congr 1 <;> ring

lemma linearRay_one (u v : ℤ) : linearRay u v 1 = 1 := by
  have hone : (1 : O) = primaryCoord 0 0 := by rw [primaryCoord_eq]; simp
  conv_lhs => rw [hone, linearRay_primaryCoord]
  simp

lemma linearRay_mul (u v : ℤ) (x y : O)
    (hx : lambda ^ 2 ∣ x - 1) (hy : lambda ^ 2 ∣ y - 1) :
    linearRay u v (x*y) = linearRay u v x * linearRay u v y := by
  obtain ⟨A,B,rfl⟩ := exists_primaryCoord x hx
  obtain ⟨C,D,rfl⟩ := exists_primaryCoord y hy
  rw [primaryCoord_mul]
  simp only [linearRay_primaryCoord]
  rw [← cubicExp_add]
  apply cubicExp_eq_of_dvd_sub
  refine ⟨u*(A*C-B*D)+v*(A*D+B*C-B*D), ?_⟩
  ring

/-- Exact primary factorization propagates a prime supplementary law to composite moduli. -/
theorem symbol_eq_linearRay_of_prime (x : O) (u v : ℤ)
    (hprime : ∀ p : O, Prime p → lambda ^ 2 ∣ p-1 → symbol x p = linearRay u v p)
    (y : O) (hy : lambda ^ 2 ∣ y-1) : symbol x y = linearRay u v y := by
  obtain ⟨A,B,hyAB⟩ := exists_primaryCoord y hy
  have hy0 : y ≠ 0 := by rw [hyAB]; exact primaryCoord_ne_zero A B
  obtain ⟨s,hsprod,hs⟩ := exists_primary_prime_factorization y hy0 hy
  rw [← hsprod]
  clear hsprod hyAB hy hy0 A B y
  induction s using Multiset.induction_on with
  | empty => simp only [Multiset.prod_zero, symbol_one, linearRay_one]
  | @cons p s ih =>
    have hp := hs p (Multiset.mem_cons_self _ _)
    have hss : ∀ r ∈ s, Prime r ∧ lambda ^ 2 ∣ r-1 :=
      fun r hr => hs r (Multiset.mem_cons_of_mem hr)
    rw [Multiset.prod_cons, symbol_mul_denominator,
      hprime p hp.1 hp.2, ih hss,
      linearRay_mul u v p s.prod hp.2 (primary_multiset_prod s (fun r hr => (hss r hr).2))]

/-- The ramified prime has coordinate phase `A`. -/
theorem symbol_lambda_eq_linearRay (y : O) (hy : lambda ^ 2 ∣ y-1) :
    symbol lambda y = linearRay 1 0 y := by
  apply symbol_eq_linearRay_of_prime lambda 1 0 _ y hy
  intro p hp hprimary
  let : (Ideal.span {p} : Ideal O).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  have hg : lambda ∉ (Ideal.span {p} : Ideal O) :=
    primary_maximal_divisor_good p hprimary _ (Ideal.subset_span (by simp))
  obtain ⟨A,B,hpAB⟩ := exists_primaryCoord p hprimary
  rw [symbol, idealSymbol_prime _ hg]
  have hc := cubicValue_lambda_primary (Ideal.span {p}) hg A B (by rw [hpAB])
  rw [hc, hpAB, linearRay_primaryCoord]
  simp [cubicExp]

/-- The cubic root has coordinate phase `2A−B`. -/
theorem symbol_omega_eq_linearRay (y : O) (hy : lambda ^ 2 ∣ y-1) :
    symbol omega y = linearRay 2 (-1) y := by
  apply symbol_eq_linearRay_of_prime omega 2 (-1) _ y hy
  intro p hp hprimary
  let : (Ideal.span {p} : Ideal O).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  have hg : lambda ∉ (Ideal.span {p} : Ideal O) :=
    primary_maximal_divisor_good p hprimary _ (Ideal.subset_span (by simp))
  obtain ⟨A,B,hpAB⟩ := exists_primaryCoord p hprimary
  rw [symbol, idealSymbol_prime _ hg]
  have hc := cubicValue_omega_primary (Ideal.span {p}) hg A B (by rw [hpAB])
  rw [hc, hpAB, linearRay_primaryCoord]
  simp [cubicExp, sub_eq_add_neg]

theorem cubicValue_traceLambda_primary (P : Ideal O) [P.IsMaximal]
    (hg : lambda ∉ P) (A B : ℤ) (hP : P = Ideal.span {primaryCoord A B}) :
    cubicChar P hg (Ideal.Quotient.mk P traceLambda) = cubicExp (-B) := by
  rw [traceLambda_eq_unit_mul_lambda, map_mul, map_mul, cubicValue_neg,
    cubicValue_omega_primary P hg A B hP, cubicValue_lambda_primary P hg A B hP]
  change cubicExp (2*A-B) * cubicExp A = cubicExp (-B)
  rw [← cubicExp_add]
  exact cubicExp_eq_of_dvd_sub ⟨A, by ring⟩

/-- The different has coordinate phase `−B`. -/
theorem symbol_traceLambda_eq_linearRay (y : O) (hy : lambda ^ 2 ∣ y-1) :
    symbol traceLambda y = linearRay 0 (-1) y := by
  apply symbol_eq_linearRay_of_prime traceLambda 0 (-1) _ y hy
  intro p hp hprimary
  let : (Ideal.span {p} : Ideal O).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  have hg : lambda ∉ (Ideal.span {p} : Ideal O) :=
    primary_maximal_divisor_good p hprimary _ (Ideal.subset_span (by simp))
  obtain ⟨A,B,hpAB⟩ := exists_primaryCoord p hprimary
  rw [symbol, idealSymbol_prime _ hg]
  have hc := cubicValue_traceLambda_primary (Ideal.span {p}) hg A B (by rw [hpAB])
  rw [hc, hpAB, linearRay_primaryCoord]
  simp

/-- Congruence modulo nine fixes each primary coordinate modulo three. -/
theorem linearRay_congr_mod_nine (u v : ℤ) (x y : O)
    (hx : lambda ^ 2 ∣ x-1) (hy : lambda ^ 2 ∣ y-1) (hxy : (9 : O) ∣ x-y) :
    linearRay u v x = linearRay u v y := by
  obtain ⟨A,B,rfl⟩ := exists_primaryCoord x hx
  obtain ⟨C,D,rfl⟩ := exists_primaryCoord y hy
  obtain ⟨z,hz⟩ := hxy
  obtain ⟨E,F,hEF⟩ := Eisenstein.Coordinates.exists_coordinates z
  change z = (E : O) + (F : O) * omega at hEF
  have hcoords : Eisenstein.Coordinates.eval (3*(A-C)) (3*(B-D)) =
      Eisenstein.Coordinates.eval (9*E) (9*F) := by
    have he (a b : ℤ) : Eisenstein.Coordinates.eval a b =
        (a : O) + (b : O) * omega := rfl
    simp only [he]
    rw [hEF, primaryCoord_eq, primaryCoord_eq] at hz
    push_cast
    linear_combination hz
  have hab := Eisenstein.Coordinates.unique_coordinates hcoords
  have ha : A-C = 3*E := by omega
  have hb : B-D = 3*F := by omega
  rw [linearRay_primaryCoord, linearRay_primaryCoord]
  apply cubicExp_eq_of_dvd_sub
  refine ⟨u*E+v*F, ?_⟩
  linear_combination u*ha + v*hb

theorem symbol_lambda_congr_mod_nine (x y : O)
    (hx : lambda ^ 2 ∣ x-1) (hy : lambda ^ 2 ∣ y-1) (hxy : (9 : O) ∣ x-y) :
    symbol lambda x = symbol lambda y := by
  rw [symbol_lambda_eq_linearRay x hx, symbol_lambda_eq_linearRay y hy]
  exact linearRay_congr_mod_nine 1 0 x y hx hy hxy

theorem symbol_traceLambda_congr_mod_nine (x y : O)
    (hx : lambda ^ 2 ∣ x-1) (hy : lambda ^ 2 ∣ y-1) (hxy : (9 : O) ∣ x-y) :
    symbol traceLambda x = symbol traceLambda y := by
  rw [symbol_traceLambda_eq_linearRay x hx, symbol_traceLambda_eq_linearRay y hy]
  exact linearRay_congr_mod_nine 0 (-1) x y hx hy hxy


end CubicRamified
namespace CubicJacobi
open Eisenstein CubicRamified
private instance : IsCyclotomicExtension {3} ℚ K :=
  CyclotomicField.isCyclotomicExtension 3 ℚ
private instance : IsPrincipalIdealRing O :=
  IsCyclotomicExtension.Rat.three_pid K

/-- The six Eisenstein units have phases fixed modulo nine. -/
theorem symbol_unit_congr_mod_nine (x a b : O) (hx : IsUnit x)
    (ha : lambda ^ 2 ∣ a-1) (hb : lambda ^ 2 ∣ b-1) (hab : (9 : O) ∣ a-b) :
    symbol x a = symbol x b := by
  obtain ⟨u,rfl⟩ := hx
  let ζ := IsCyclotomicExtension.zeta_spec 3 ℚ K
  let η : Oˣ := (ζ.toInteger_isPrimitiveRoot.isUnit (by decide)).unit
  have hη : (η : O) = omega := rfl
  have hu : u ∈ ([1, -1, η, -η, η^2, -η^2] : List Oˣ) :=
    IsCyclotomicExtension.Rat.Three.Units.mem ζ u
  have hω : symbol omega a = symbol omega b := by
    rw [symbol_omega_eq_linearRay a ha, symbol_omega_eq_linearRay b hb]
    exact linearRay_congr_mod_nine 2 (-1) a b ha hb hab
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hu
  rcases hu with h | h | h | h | h | h
  · simp only [h, Units.val_one, symbol_one_numerator _ ha, symbol_one_numerator _ hb]
  · simp only [h, Units.val_neg, Units.val_one, symbol_neg_one _ ha, symbol_neg_one _ hb]
  · simpa only [h, hη] using hω
  · simpa only [h, Units.val_neg, hη, symbol_neg_numerator _ _ ha,
      symbol_neg_numerator _ _ hb] using hω
  · simpa only [h, Units.val_pow_eq_pow_val, hη, symbol_pow_numerator _ _ ha,
      symbol_pow_numerator _ _ hb] using congrArg (fun t : O => t^2) hω
  · simpa only [h, Units.val_neg, Units.val_pow_eq_pow_val, hη,
      symbol_neg_numerator _ _ ha, symbol_neg_numerator _ _ hb,
      symbol_pow_numerator _ _ ha, symbol_pow_numerator _ _ hb]
      using congrArg (fun t : O => t^2) hω

private theorem associated_congr_denominator {x y a b : O} (hxy : Associated x y)
    (ha : lambda ^ 2 ∣ a-1) (hb : lambda ^ 2 ∣ b-1) (hab : (9 : O) ∣ a-b)
    (hy : symbol y a = symbol y b) : symbol x a = symbol x b := by
  obtain ⟨u,hu⟩ := hxy
  apply mul_right_cancel₀ (symbol_isUnit_ne_zero (u : O) a u.isUnit ha)
  calc
    symbol x a * symbol (u : O) a = symbol y a := by
      rw [← symbol_mul_numerator _ _ a, hu]
    _ = symbol y b := hy
    _ = symbol x b * symbol (u : O) b := by rw [← hu, symbol_mul_numerator _ _ b]
    _ = symbol x b * symbol (u : O) a := by
      rw [symbol_unit_congr_mod_nine (u : O) b a u.isUnit hb ha (by simpa only [neg_sub] using dvd_neg.mpr hab)]

private theorem ramified_prime : Prime lambda := by
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact (IsCyclotomicExtension.zeta_spec 3 ℚ K).zeta_sub_one_prime'

private theorem symbol_prime_denominator_congr (p a b : O) (hp : Prime p)
    (ha : lambda ^ 2 ∣ a-1) (hb : lambda ^ 2 ∣ b-1)
    (h9 : (9 : O) ∣ a-b) (hpab : p ∣ a-b) : symbol p a = symbol p b := by
  let : (Ideal.span {p} : Ideal O).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  by_cases hg : lambda ∉ (Ideal.span {p} : Ideal O)
  · let q := primaryGenerator (Ideal.span {p}) hg
    have hq := (primaryGenerator_spec (Ideal.span {p}) hg).1
    have hprimary := (primaryGenerator_spec (Ideal.span {p}) hg).2
    have hpq : Associated p q := Ideal.span_singleton_eq_span_singleton.mp hq
    apply associated_congr_denominator hpq ha hb h9
    rw [symbol_reciprocity q a hprimary ha,
      symbol_reciprocity q b hprimary hb]
    exact symbol_congr (hpq.dvd'.trans hpab)
  · have hdiv : p ∣ lambda := Ideal.mem_span_singleton.mp (not_not.mp hg)
    apply associated_congr_denominator (hp.associated_of_dvd ramified_prime hdiv) ha hb h9
    exact symbol_lambda_congr_mod_nine a b ha hb h9

/-- A primary denominator may be changed by a multiple of both nine and the numerator. -/
theorem symbol_denominator_congr (x a b : O)
    (ha : lambda ^ 2 ∣ a-1) (hb : lambda ^ 2 ∣ b-1)
    (h9 : (9 : O) ∣ a-b) (hx : x ∣ a-b) : symbol x a = symbol x b := by
  induction x using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => have heq : a = b := sub_eq_zero.mp (zero_dvd_iff.mp hx); rw [heq]
  | h₂ u hu => exact symbol_unit_congr_mod_nine u a b hu ha hb h9
  | h₃ x p hx0 hp ih =>
    have hpab : p ∣ a-b := (dvd_mul_right p x).trans hx
    have hxab : x ∣ a-b := (dvd_mul_left x p).trans hx
    rw [symbol_mul_numerator _ _ a, symbol_mul_numerator _ _ b,
      symbol_prime_denominator_congr p a b hp ha hb h9, ih hxab]
    exact hpab


end CubicJacobi
end GaloisForLFunctions.MetaplecticMobiusDescent

#print axioms GaloisForLFunctions.MetaplecticMobiusDescent.CubicRamified.symbol_lambda_eq_linearRay
#print axioms GaloisForLFunctions.MetaplecticMobiusDescent.CubicRamified.symbol_omega_eq_linearRay
#print axioms GaloisForLFunctions.MetaplecticMobiusDescent.CubicRamified.symbol_traceLambda_eq_linearRay
#print axioms GaloisForLFunctions.MetaplecticMobiusDescent.CubicRamified.symbol_traceLambda_congr_mod_nine
#print axioms GaloisForLFunctions.MetaplecticMobiusDescent.CubicJacobi.symbol_unit_congr_mod_nine
#print axioms GaloisForLFunctions.MetaplecticMobiusDescent.CubicJacobi.symbol_denominator_congr
