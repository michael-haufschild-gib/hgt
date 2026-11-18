import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.HermitianQuadraticAbscissas
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FiniteField.KummerConstructedPointCount
import Mathlib.FieldTheory.Finite.GaloisField

/-!
# Geometric fiber counts and Hermitian Frobenius strata

The fixed locus descends coordinatewise to the square constant field.
Every geometric abscissa has exactly Q lifts. Combining these facts with
the displacement obstruction counts the entire degree-2p stratum lying
over quadratic abscissae.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open Polynomial Function
variable (p : ℕ) [Fact p.Prime] (s : ℕ)
local notation "Q" => p^(s+1)
local notation "k" => SquareConstantField p s
local notation "E" => HermitianGeometricConstants p s
local notation "Pts" => HermitianAffinePoint p s E
local notation "F" => hermitianFrobeniusPoint p s E
local notation "ι" => algebraMap k E

private theorem baseCard : Nat.card k = Q*Q := by
  rw [squareConstantField_card,two_mul,pow_add]

private theorem roots_card {L : Type*} [Field L] [IsAlgClosed L] (f : L[X]) (hf : f ≠ 0) (hs : f.Separable) :
    Nat.card {x : L // f.eval x = 0} = f.natDegree := by
  classical
  have he : {x : L | f.eval x=0} = (f.roots.toFinset : Set L) := by
    ext x; simp [Polynomial.mem_roots hf,Polynomial.IsRoot]
  change Nat.card (↑{x : L | f.eval x=0}) = _
  rw [he,Nat.card_coe_set_eq,Set.ncard_coe_finset,Multiset.toFinset_card_of_nodup (nodup_roots hs)]
  exact ((IsAlgClosed.splits f).natDegree_eq_card_roots).symm

/-- The Frobenius-fixed coordinates in the geometric closure are exactly the embedded constants. -/
theorem hermitianCoordinate_fixed_base (x : E) :
    x^(Q*Q) = x ↔ ∃ b : k, ι b = x := by
  have h := squareFrobenius_coordinate_fixed_iff p s x 1
  rw [pow_one,baseCard,Nat.dvd_one,minpoly.natDegree_eq_one_iff] at h
  exact h

/-- Descent identifies the fixed affine point locus with the literal finite-field curve. -/
def hermitianFixedPointEquiv :
    HermitianAffinePoints p s ≃ {P : Pts // F P=P} := by
  let lift (P : HermitianAffinePoints p s) : Pts := ⟨(ι P.val.1,ι P.val.2),by
    have h := congrArg ι P.property
    simpa only [map_pow,map_add] using h⟩
  let e (P : HermitianAffinePoints p s) : {P : Pts // F P=P} :=
    ⟨lift P,(hermitianFrobeniusPoint_eq_self_iff p s E _).2
      ((hermitianCoordinate_fixed_base p s _).2 ⟨P.val.1,rfl⟩)⟩
  apply Equiv.ofBijective e
  constructor
  · intro A B h
    apply Subtype.ext; apply Prod.ext
    · exact (ι).injective (congrArg (fun P : {P : Pts // F P=P} => P.val.val.1) h)
    · exact (ι).injective (congrArg (fun P : {P : Pts // F P=P} => P.val.val.2) h)
  · intro P
    obtain ⟨a,ha⟩ := (hermitianCoordinate_fixed_base p s _).1
      (congrArg (fun U : Pts => U.val.1) P.property)
    obtain ⟨b,hb⟩ := (hermitianCoordinate_fixed_base p s _).1
      (congrArg (fun U : Pts => U.val.2) P.property)
    have hP := P.val.property
    refine ⟨⟨(a,b),(ι).injective ?_⟩,Subtype.ext (Subtype.ext (Prod.ext ha hb))⟩
    change ι (b^Q+b) = ι (a^(Q+1))
    rw [map_add,map_pow,map_pow,ha,hb]; exact hP

/-- Both the first and second geometric Frobenius fixed sets have exactly Q³ affine points. -/
theorem hermitianFirstTwoFixed_card :
    Nat.card {P : Pts // F P=P} = Q^3 ∧ Nat.card {P : Pts // F^[2] P=P} = Q^3 := by
  have he := (Nat.card_congr (hermitianFixedPointEquiv p s)).symm.trans (hermitianAffinePoints_card p s)
  exact ⟨he,(Nat.card_congr (Equiv.subtypeEquivRight fun P => hermitianFrobenius_two_fixed_iff p s P)).trans he⟩

/-- Every geometric abscissa has Q distinct ordinates, regardless of its degree. -/
theorem hermitianGeometricAbscissa_fiber_card (x : E) :
    Nat.card {P : Pts // P.val.1=x} = Q := by
  let f : E[X] := X^Q + (X - C (x^(Q+1)))
  have hQ : 1<Q := Nat.one_lt_pow (Nat.succ_ne_zero s) (Fact.out : p.Prime).one_lt
  have hd : f.natDegree = Q := by
    dsimp only [f]
    rw [natDegree_add_eq_left_of_natDegree_lt, natDegree_X_pow]
    rw [natDegree_X_sub_C,natDegree_X_pow]; exact hQ
  have hne : f≠0 := fun h => by rw [h,natDegree_zero] at hd; omega
  have hs : f.Separable := by
    have hp : ((Q:ℕ):E[X])=0 := (CharP.cast_eq_zero_iff E[X] p Q).2 (dvd_pow dvd_rfl (Nat.succ_ne_zero s))
    have hder : derivative f = 1 := by
      simp only [f,derivative_add,derivative_X_pow,C_eq_natCast,hp,zero_mul,derivative_sub,derivative_X,
        derivative_C,sub_zero,zero_add]
    exact (show IsCoprime f f.derivative by rw [hder]; exact isCoprime_one_right)
  have he (y : E) : f.eval y=0 ↔ y^Q+y=x^(Q+1) := by
    simp only [f,eval_add,eval_pow,eval_X,eval_sub,eval_C]; constructor <;> intro h <;> linear_combination h
  let e : {P : Pts // P.val.1=x} ≃ {y : E // f.eval y=0} :=
    { toFun := fun v => ⟨v.val.val.2,(he _).2
        (v.val.property.trans (congrArg (fun a : E => a^(Q+1)) v.property))⟩
      invFun := fun y => ⟨⟨(x,y.val),(he _).1 y.property⟩,rfl⟩
      left_inv := fun v => Subtype.ext (Subtype.ext (Prod.ext v.property.symm rfl))
      right_inv := fun _ => rfl }
  rw [Nat.card_congr e,roots_card f hne hs,hd]

/-- Geometric abscissae rational over the degree-n constant extension have the expected cardinality. -/
theorem hermitianGeometricAbscissa_card_dvd (n : ℕ) (hn : 0<n) :
    Nat.card {x : E // (minpoly k x).natDegree ∣ n} = (Nat.card k)^n := by
  let c := (Nat.card k)^n
  have hpBase : p ∣ Nat.card k := by
    rw [baseCard]; exact dvd_mul_of_dvd_left (dvd_pow dvd_rfl (Nat.succ_ne_zero s)) Q
  have hp : p ∣ c := dvd_pow hpBase hn.ne'
  have hq : 1<Q := Nat.one_lt_pow (Nat.succ_ne_zero s) (Fact.out : p.Prime).one_lt
  have hcard : 1<Nat.card k := by rw [baseCard]; nlinarith only [hq]
  have hc : 1<c := Nat.one_lt_pow hn.ne' hcard
  let f : E[X] := X^c-X
  have hd : f.natDegree=c := by
    rw [show f = X^c-X from rfl,natDegree_sub_eq_left_of_natDegree_lt,natDegree_X_pow]
    rw [natDegree_X,natDegree_X_pow]; exact hc
  have he (x:E) : ((minpoly k x).natDegree ∣ n) ↔ f.eval x=0 := by
    rw [← squareFrobenius_coordinate_fixed_iff]
    simp only [f,c,eval_sub,eval_pow,eval_X,sub_eq_zero]
  rw [Nat.card_congr (Equiv.subtypeEquivRight he),roots_card f (fun hz => by
    rw [hz,natDegree_zero] at hd; omega) (galois_poly_separable p c hp),hd]

private theorem degreeStratum_finite (n : ℕ) (hn : 0<n) :
    Finite {x : E // (minpoly k x).natDegree=n} := by
  let D := {x : E // (minpoly k x).natDegree ∣ n}
  have h : Nat.card D = (Nat.card k)^n := hermitianGeometricAbscissa_card_dvd p s n hn
  letI : Finite D := Nat.finite_of_card_ne_zero (h.trans_ne (pow_ne_zero _ Nat.card_pos.ne'))
  let e (x : {x : E // (minpoly k x).natDegree=n}) : D := ⟨x.val,by rw [x.property]⟩
  exact Finite.of_injective e fun _ _ he => Subtype.ext (congrArg (fun y : D => y.val) he)

/-- In every prime degree the count of new abscissae is the full extension minus the base. -/
theorem hermitianGeometric_prime_degree_abscissae (l : ℕ) (hl : l.Prime) :
    Nat.card {x : E // (minpoly k x).natDegree=l} = (Nat.card k)^l - Nat.card k := by
  classical
  let D (x : E) := (minpoly k x).natDegree
  let A := {x : E // D x=1}
  let B := {x : E // D x=l}
  letI : Finite A := degreeStratum_finite p s 1 zero_lt_one
  letI : Finite B := degreeStratum_finite p s l hl.pos
  let e : {x : E // D x ∣ l} ≃ A ⊕ B :=
    { toFun := fun x => if h : D x.val=1 then Sum.inl ⟨x.val,h⟩
          else Sum.inr ⟨x.val,((Nat.dvd_prime hl).1 x.property).resolve_left h⟩
      invFun := Sum.elim (fun a => ⟨a.val,by rw [a.property]; exact one_dvd l⟩)
        (fun b => ⟨b.val,by rw [b.property]⟩)
      left_inv := fun x => by by_cases h : D x.val=1 <;> simp [h]
      right_inv := by
        rintro (a|b)
        · simp [a.property]
        · simp [b.property,hl.ne_one] }
  have hA : Nat.card A = Nat.card k := by
    simpa only [Nat.dvd_one,pow_one,A,D] using hermitianGeometricAbscissa_card_dvd p s 1 zero_lt_one
  have h := Nat.card_congr e
  change Nat.card {x : E // (minpoly k x).natDegree ∣ l} = Nat.card (A ⊕ B) at h
  rw [hermitianGeometricAbscissa_card_dvd p s l hl.pos,Nat.card_sum,hA] at h
  change Nat.card B = _
  omega

/-- Projection counts points above every positive-degree abscissa stratum with constant multiplicity Q. -/
theorem hermitianGeomPoints_over_degree (n : ℕ) (hn : 0<n) :
    Nat.card {P : Pts // hermitianAbscissaDegree p s P=n} =
      Nat.card {x : E // (minpoly k x).natDegree=n} * Q := by
  classical
  let A := {x : E // (minpoly k x).natDegree=n}
  let B (x : A) := {P : Pts // P.val.1=x.val}
  letI : Finite A := degreeStratum_finite p s n hn
  letI : Fintype A := Fintype.ofFinite _
  have hB (x : A) : Nat.card (B x)=Q := hermitianGeometricAbscissa_fiber_card p s x.val
  letI (x : A) : Finite (B x) := Nat.finite_of_card_ne_zero ((hB x).trans_ne (pow_ne_zero _ (Fact.out : p.Prime).ne_zero))
  let e : {P : Pts // hermitianAbscissaDegree p s P=n} ≃ Σ x : A, B x :=
    { toFun := fun P => ⟨⟨P.val.val.1,P.property⟩,P.val,rfl⟩
      invFun := fun t => ⟨t.2.val,by change (minpoly k t.2.val.val.1).natDegree=n
                                     rw [t.2.property]; exact t.1.property⟩
      left_inv := fun _ => rfl
      right_inv := by
        rintro ⟨⟨x,hx⟩,⟨P,h⟩⟩
        change P.val.1 = x at h
        subst x
        rfl }
  rw [Nat.card_congr e,Nat.card_sigma]
  change (∑ x : A, Nat.card (B x)) = Nat.card A * Q
  simp only [hB,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.cast_id,← Nat.card_eq_fintype_card]

/-- Exactly Q(Q⁴-Q²) points lie above quadratic abscissae, all of exact geometric degree 2p. -/
theorem hermitianQuadraticAbscissa_stratum_card :
    Nat.card {P : Pts // hermitianAbscissaDegree p s P=2 ∧ hermitianOrbitDegree p s P=2*p} =
      (Q^4-Q^2)*Q := by
  have he (P : Pts) : (hermitianAbscissaDegree p s P=2 ∧ hermitianOrbitDegree p s P=2*p) ↔
      hermitianAbscissaDegree p s P=2 := ⟨And.left,fun h => ⟨h,hermitianQuadraticAbscissa_lift_degree p s P h⟩⟩
  rw [Nat.card_congr (Equiv.subtypeEquivRight he),hermitianGeomPoints_over_degree p s 2 zero_lt_two,
    hermitianGeometric_prime_degree_abscissae p s 2 Nat.prime_two,baseCard]
  rw [show (Q*Q)^2=Q^4 by ring,← sq]

#print axioms hermitianGeometric_prime_degree_abscissae
#print axioms hermitianGeomPoints_over_degree
#print axioms hermitianQuadraticAbscissa_stratum_card
#print axioms hermitianCoordinate_fixed_base
#print axioms hermitianFixedPointEquiv
#print axioms hermitianFirstTwoFixed_card
#print axioms hermitianGeometricAbscissa_fiber_card
#print axioms hermitianGeometricAbscissa_card_dvd
end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
