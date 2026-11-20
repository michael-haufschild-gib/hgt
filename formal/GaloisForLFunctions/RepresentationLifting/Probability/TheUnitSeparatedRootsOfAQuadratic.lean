import GaloisForLFunctions.RepresentationLifting.Probability.QuadraticMatrixFibres
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.RingTheory.LocalRing.RingHom.Basic
import Mathlib.Data.Nat.Totient

/-!
# The split simple stratum of monic quadratics

In a local ring two roots separated by a unit exhaust the root set. Marking
one root identifies the split simple coefficient pairs with a two-to-one
image of a root and a unit separation. At every positive p-adic precision
this stratum has the finite density (p-1)/(2p) of the simple split branch
in Lapid and Shusterman, Lemma C.1.
-/

namespace GaloisForLFunctions.RepresentationLifting
open Finset
noncomputable section
open scoped Classical

variable {R : Type*} [CommRing R] [IsLocalRing R]

/-- Over a local ring, a monic quadratic with two unit-separated roots has
no further roots, even in the presence of nilpotents. -/
theorem unit_separated_root_iff {u v : R} (hu : IsUnit (u-v)) (x : R) :
    x*(u+v-x)=u*v ↔ x=u ∨ x=v := by
  constructor
  · intro hx
    have hz : (x-u)*(x-v)=0 := by linear_combination -hx
    have hunit : IsUnit ((u-x)+(x-v)) := by rwa [sub_add_sub_cancel]
    rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add hunit with h|h
    · right
      have ht : IsUnit (x-u) := by simpa only [neg_sub] using h.neg
      exact sub_eq_zero.mp (ht.mul_right_inj.mp (by simpa only [mul_zero] using hz))
    · left
      exact sub_eq_zero.mp (h.mul_left_inj.mp (by simpa only [zero_mul] using hz))
  · rintro (rfl|rfl) <;> ring

/-- Monic quadratics labeled by sum and product of two unit-separated roots. -/
abbrev SimpleSplitLabels (R : Type*) [CommRing R] :=
  {z : R×R // ∃ u v : R, IsUnit (u-v) ∧ z=(u+v,u*v)}

private def separatedLabel (x : R) (s : Rˣ) : SimpleSplitLabels R :=
  ⟨(x+(x-s),x*(x-s)),x,x-s,by simpa only [sub_sub_cancel] using s.isUnit,rfl⟩

private theorem marked_ext {s t : (z : SimpleSplitLabels R) × traceDetRoot z.val.1 z.val.2}
    (hz : s.1=t.1) (hr : s.2.val=t.2.val) : s=t := by
  rcases s with ⟨a,⟨x,hx⟩⟩
  rcases t with ⟨b,⟨y,hy⟩⟩
  change a=b at hz
  subst b
  change x=y at hr
  subst y
  rfl

private def markedSimpleEquiv :
    (R×Rˣ) ≃ (z : SimpleSplitLabels R) × traceDetRoot z.val.1 z.val.2 := by
  let encode (w : R×Rˣ) : (z : SimpleSplitLabels R) × traceDetRoot z.val.1 z.val.2 :=
    ⟨separatedLabel w.1 w.2,w.1,by dsimp only [separatedLabel]; ring⟩
  refine Equiv.ofBijective encode ⟨?_,?_⟩
  · rintro ⟨x,s⟩ ⟨y,t⟩ he
    have hroot : x=y := congrArg (fun z => z.2.val) he
    have htrace : x+(x-s)=y+(y-t) := congrArg (fun z => z.1.val.1) he
    exact Prod.ext hroot (Units.ext (by linear_combination 2*hroot-htrace))
  · rintro ⟨⟨_,u,v,hu,rfl⟩,⟨x,hx⟩⟩
    change x*(u+v-x)=u*v at hx
    rcases (unit_separated_root_iff hu x).mp hx with h|h
    · subst x
      refine ⟨(u,hu.unit),marked_ext (Subtype.ext ?_) rfl⟩
      have he : u-(hu.unit:R)=v := by rw [hu.unit_spec,sub_sub_cancel]
      exact Prod.ext (congrArg (u+·) he) (congrArg (u*·) he)
    · subst x
      have hv : IsUnit (v-u) := by simpa only [neg_sub] using hu.neg
      refine ⟨(v,hv.unit),marked_ext (Subtype.ext ?_) rfl⟩
      have he : v-(hv.unit:R)=u := by rw [hv.unit_spec,sub_sub_cancel]
      exact Prod.ext ((congrArg (v+·) he).trans (add_comm ..))
        ((congrArg (v*·) he).trans (mul_comm ..))

/-- Every coefficient label in the split simple stratum has exactly two
roots, without imposing a field or odd residue characteristic. -/
theorem card_unit_separated_roots {u v : R} (hu : IsUnit (u-v)) :
    Nat.card (traceDetRoot (u+v) (u*v))=2 := by
  have huv : u≠v := sub_ne_zero.mp hu.ne_zero
  let e : traceDetRoot (u+v) (u*v) ≃ ↥({u,v}:Finset R) :=
    Equiv.subtypeEquivRight (fun x => (unit_separated_root_iff hu x).trans (by simp))
  rw [Nat.card_congr e,Nat.card_eq_finsetCard,card_insert_of_notMem (by simpa using huv),card_singleton]

/-- Counting a marked root gives twice the number of simple split labels.
The free parameters are one arbitrary root and one invertible difference. -/
theorem twice_card_simple_split_labels (R : Type*) [CommRing R] [IsLocalRing R] [Fintype R] :
    2*Nat.card (SimpleSplitLabels R) = Fintype.card R*Nat.card Rˣ := by
  have h := Nat.card_congr (markedSimpleEquiv (R:=R))
  rw [Nat.card_prod,Nat.card_eq_fintype_card (α:=R),Nat.card_sigma] at h
  have roots (z : SimpleSplitLabels R) : Nat.card (traceDetRoot z.val.1 z.val.2)=2 := by
    obtain ⟨⟨_,_⟩,u,v,hu,hz⟩ := z
    cases hz
    exact card_unit_separated_roots hu
  simp only [roots,sum_const,card_univ,nsmul_eq_mul,Nat.cast_id,←Nat.card_eq_fintype_card] at h
  simpa only [Nat.mul_comm 2,Nat.card_eq_fintype_card (α:=R)] using h.symm

/-- The exact finite count of split simple monic quadratics modulo p^(h+1).
The fraction among all coefficient pairs is independent of the precision. -/
theorem twice_card_simple_split_mod_prime_power (p h : ℕ) [Fact p.Prime] :
    2*Nat.card (SimpleSplitLabels (ZMod (p^(h+1)))) = p^(h+1)*(p^h*(p-1)) := by
  have hp := (Fact.out : p.Prime)
  let q := p^(h+1)
  letI : NeZero q := ⟨pow_ne_zero _ hp.ne_zero⟩
  letI : Fact (1<q) := ⟨one_lt_pow₀ hp.one_lt (Nat.succ_ne_zero h)⟩
  letI : IsLocalRing (ZMod q) := IsLocalRing.of_surjective (PadicInt.toZModPow (p:=p) (h+1))
    (ZMod.ringHom_surjective _)
  have hcard := twice_card_simple_split_labels (ZMod q)
  rw [ZMod.card,Nat.card_eq_fintype_card (α:=(ZMod q)ˣ),ZMod.card_units_eq_totient] at hcard
  simpa only [q,Nat.totient_prime_pow_succ hp] using hcard

/-- The unramified split branch takes the same positive fraction of all
quadratic coefficient pairs at every finite precision. -/
theorem simple_split_coefficient_probability (p h : ℕ) [Fact p.Prime] :
    (Nat.card (SimpleSplitLabels (ZMod (p^(h+1)))):ℝ)/((p:ℝ)^(h+1))^2 =
      ((p:ℝ)-1)/(2*p) := by
  have hp := (Fact.out : p.Prime)
  have hpR : (p:ℝ)≠0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hc := congrArg (fun t : ℕ => (t:ℝ)) (twice_card_simple_split_mod_prime_power p h)
  simp only [Nat.cast_mul,Nat.cast_ofNat,Nat.cast_pow,Nat.cast_sub hp.one_le,Nat.cast_one,pow_succ (p:ℝ) h] at hc
  rw [pow_succ (p:ℝ) h,div_eq_div_iff (pow_ne_zero _ (mul_ne_zero (pow_ne_zero _ hpR) hpR))
    (mul_ne_zero (by norm_num) hpR)]
  linear_combination (p:ℝ)*hc

end
end GaloisForLFunctions.RepresentationLifting
