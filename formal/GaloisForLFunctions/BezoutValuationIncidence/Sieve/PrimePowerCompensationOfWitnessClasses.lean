import GaloisForLFunctions.BezoutValuationIncidence.Sieve.ConditioningTheLocalEgyptianFractionSieve
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheJordanLimitCountsProjectiveSpace

/-!
# The compensation weight at each prime-power depth

A forbidden primitive triple modulo p has T³ lifts modulo p^(h+1),
where T=p^h. On a compatible ray, fixing the lifts of the two shape
parameters leaves exactly T−1 choices of the third coordinate for which
Kacd−1 is divisible by p but does not vanish modulo p^(h+1).
These counts determine the unique unbiased compensation weight.
-/

noncomputable section
open Finset
namespace GaloisForLFunctions.BezoutValuationIncidence.LocalConditioning
variable (p h : ℕ) [hp : Fact p.Prime]

abbrev RingAt := ZMod (p^(h+1))

def reduce : RingAt p h →+* ZMod p := ZMod.castHom (dvd_pow_self p (Nat.succ_ne_zero h)) _

abbrev Lift (v : ZMod p) := {z : RingAt p h // reduce p h z=v}

private instance ringAtNeZero : NeZero (p^(h+1)) := ⟨pow_ne_zero _ hp.out.ne_zero⟩

/-- Each low digit has p^h lifts. Translating the fiber to zero identifies it
with the nonunits of the prime-power ring. -/
theorem count_lift (v : ZMod p) : Fintype.card (Lift p h v)=p^h := by
  let a : RingAt p h := v.val
  have ha : reduce p h a = v := by simp [a]
  let e : Lift p h v ≃ Lift p h 0 :=
    { toFun := fun x => ⟨x.val-a,by rw [map_sub,x.property,ha,sub_self]⟩,
      invFun := fun x => ⟨x.val+a,by rw [map_add,x.property,ha,zero_add]⟩,
      left_inv := fun _ => Subtype.ext (sub_add_cancel _ _),
      right_inv := fun _ => Subtype.ext (add_sub_cancel_right _ _) }
  let f : Lift p h 0 ≃ {z : RingAt p h // ¬IsUnit z} :=
    Equiv.subtypeEquivRight fun z => by
      rw [ArithmeticHodgeTheoryOfDegenerations.isUnit_iff_castHom_ne_zero hp.out (Nat.succ_pos h),not_not]
      rfl
  calc
    _ = Nat.card {z : RingAt p h // ¬IsUnit z} := by
      rw [Fintype.card_congr (e.trans f),Nat.card_eq_fintype_card]
    _ = p ^ (h.succ-1) :=
      ArithmeticHodgeTheoryOfDegenerations.natCard_nonunits hp.out (Nat.succ_pos h)
    _ = p^h := rfl

abbrev TripleLift (s : Sample (ZMod p)) :=
  Lift p h s.1.val.1 × Lift p h s.1.val.2 × Lift p h s.2

/-- Recording the low primitive residue together with the lifts
parametrizes every primitive prime-power triple exactly once. -/
def rawEquiv : (Σ s : Sample (ZMod p), TripleLift p h s) ≃
    {t : (RingAt p h × RingAt p h) × RingAt p h //
      (reduce p h t.1.1,reduce p h t.1.2) ≠ (0,0)} where
  toFun x := ⟨((x.2.1.val,x.2.2.1.val),x.2.2.2.val),by
    rw [x.2.1.property,x.2.2.1.property]
    exact x.1.1.property⟩
  invFun t := ⟨(⟨(reduce p h t.val.1.1,reduce p h t.val.1.2),t.property⟩,reduce p h t.val.2),
    ⟨_,rfl⟩,⟨_,rfl⟩,⟨_,rfl⟩⟩
  left_inv := by
    rintro ⟨⟨⟨⟨a,c⟩,hac⟩,d⟩,⟨A,hA⟩,⟨C,hC⟩,⟨D,hD⟩⟩
    change reduce p h A = a at hA
    change reduce p h C = c at hC
    change reduce p h D = d at hD
    subst a
    subst c
    subst d
    rfl
  right_inv _ := rfl

private theorem unique_root (K : RingAt p h) (s : Hit (ZMod p) (reduce p h K))
    (A : Lift p h s.val.1.val.1) (C : Lift p h s.val.1.val.2) :
    ∃! D : Lift p h s.val.2, K*A.val*C.val*D.val=1 := by
  let L := K*A.val*C.val
  have he : reduce p h L*s.val.2=1 := by
    simpa only [L,map_mul,A.property,C.property,product] using s.property
  have hn : reduce p h L ≠ 0 := by intro hz; simp only [hz,zero_mul,zero_ne_one] at he
  have hu := (ArithmeticHodgeTheoryOfDegenerations.isUnit_iff_castHom_ne_zero hp.out
    (Nat.succ_pos h) L).2 hn
  let U := hu.unit
  have hU : (U : RingAt p h) = L := hu.unit_spec
  let b : RingAt p h := ↑U⁻¹
  have hb : L*b=1 := by rw [← hU]; exact U.mul_inv
  have hred : reduce p h b = s.val.2 := mul_left_cancel₀ hn (by rw [← map_mul,hb,map_one,he])
  refine ⟨⟨b,hred⟩,hb,fun t ht => Subtype.ext ?_⟩
  change L*t.val=1 at ht
  have hh : (↑U : RingAt p h)*t.val=1 := by rw [hU]; exact ht
  exact (Units.inv_eq_of_mul_eq_one_right hh).symm

theorem surviving_lifts (K : RingAt p h) (s : Hit (ZMod p) (reduce p h K))
    (A : Lift p h s.val.1.val.1) (C : Lift p h s.val.1.val.2) :
    Fintype.card {D : Lift p h s.val.2 // K*A.val*C.val*D.val ≠ 1} = p^h-1 := by
  obtain ⟨b,hb,hu⟩ := unique_root p h K s A C
  let e : {D : Lift p h s.val.2 // K*A.val*C.val*D.val=1} ≃
      {D : Lift p h s.val.2 // D=b} :=
    Equiv.subtypeEquivRight fun D => ⟨fun hh => hu _ hh,fun hh => hh ▸ hb⟩
  rw [Fintype.card_subtype_compl (fun D : Lift p h s.val.2 => K*A.val*C.val*D.val=1),
    count_lift,Fintype.card_congr e,Fintype.card_subtype_eq]

/-- All high triples in the forbidden mod-p classes. -/
abbrev Removed (K : RingAt p h) :=
  Σ s : Hit (ZMod p) (reduce p h K), TripleLift p h s.val

/-- High triples on a compatible primitive ray which survive the prime-power
test, but fail the rough test. -/
abbrev Recovered (K : RingAt p h) (r : (ZMod p)ˣ) :=
  Σ s : RayHit (ZMod p) (reduce p h K) (r : ZMod p), Σ A : Lift p h s.val.val.1.val.1,
    Σ C : Lift p h s.val.val.1.val.2, {D : Lift p h s.val.val.2 // K*A.val*C.val*D.val ≠ 1}

theorem count_removed (K : (RingAt p h)ˣ) :
    Fintype.card (Removed p h (K : RingAt p h))=(p-1)^2*(p^h)^3 := by
  let k := Units.map (reduce p h : RingAt p h →* ZMod p) K
  change Fintype.card (Σ s : Hit (ZMod p) (k : ZMod p), TripleLift p h s.val)=_
  simp only [Fintype.card_sigma,TripleLift,Fintype.card_prod,count_lift,sum_const,card_univ,
    nsmul_eq_mul,count_hit,ZMod.card,Nat.cast_id]
  ring

theorem count_recovered (K : (RingAt p h)ˣ) (r : (ZMod p)ˣ) :
    Fintype.card (Recovered p h (K : RingAt p h) r)=(p-1)*(p^h)^2*(p^h-1) := by
  let k := Units.map (reduce p h : RingAt p h →* ZMod p) K
  unfold Recovered
  simp only [Fintype.card_sigma,surviving_lifts,sum_const,card_univ,nsmul_eq_mul,count_lift,Nat.cast_id]
  rw [show Fintype.card (RayHit (ZMod p) (reduce p h (K : RingAt p h)) (r : ZMod p))=p-1
    from (count_ray k r).trans (by rw [ZMod.card])]
  ring

/-- The paper's compensation by p is exact at the first square level. -/
theorem square_compensation (K : (RingAt p 1)ˣ) (r : (ZMod p)ˣ) :
    p * Fintype.card (Recovered p 1 (K : RingAt p 1) r) =
      Fintype.card (Removed p 1 (K : RingAt p 1)) := by
  rw [count_removed,count_recovered,pow_one]
  ring

/-- At greater depth the denominator T−1 replaces p−1. The weight
is uniquely fixed by requiring the recovered mass to equal the removed mass. -/
theorem compensation_iff (K : (RingAt p h)ˣ) (r : (ZMod p)ˣ) (hh : 0<h) (w : ℚ) :
    w*Fintype.card (Recovered p h (K : RingAt p h) r) = Fintype.card (Removed p h (K : RingAt p h)) ↔
      w=(p^h : ℕ)*(p-1 : ℕ)/((p^h-1 : ℕ) : ℚ) := by
  have hT : 1 < p^h := one_lt_pow₀ hp.out.one_lt hh.ne'
  have P : (0 : ℚ)<(p-1 : ℕ) := by exact_mod_cast Nat.sub_pos_of_lt hp.out.one_lt
  have T : (0 : ℚ)<(p : ℚ)^h := pow_pos (Nat.cast_pos.mpr hp.out.pos) _
  have E : (0 : ℚ)<(p^h-1 : ℕ) := by exact_mod_cast Nat.sub_pos_of_lt hT
  rw [count_removed,count_recovered,eq_div_iff E.ne']
  push_cast only [Nat.cast_mul,Nat.cast_pow]
  constructor
  · intro he
    apply mul_right_cancel₀ (mul_ne_zero P.ne' (pow_ne_zero 2 T.ne'))
    linear_combination he
  · intro he
    linear_combination ((p-1 : ℕ) : ℚ)*((p : ℚ)^h)^2*he

end GaloisForLFunctions.BezoutValuationIncidence.LocalConditioning

#print axioms GaloisForLFunctions.BezoutValuationIncidence.LocalConditioning.count_lift
#print axioms GaloisForLFunctions.BezoutValuationIncidence.LocalConditioning.surviving_lifts
#print axioms GaloisForLFunctions.BezoutValuationIncidence.LocalConditioning.count_removed
#print axioms GaloisForLFunctions.BezoutValuationIncidence.LocalConditioning.count_recovered
#print axioms GaloisForLFunctions.BezoutValuationIncidence.LocalConditioning.square_compensation
#print axioms GaloisForLFunctions.BezoutValuationIncidence.LocalConditioning.compensation_iff
#print axioms GaloisForLFunctions.BezoutValuationIncidence.LocalConditioning.rawEquiv
