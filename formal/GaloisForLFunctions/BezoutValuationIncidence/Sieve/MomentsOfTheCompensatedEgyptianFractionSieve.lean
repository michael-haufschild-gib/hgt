import GaloisForLFunctions.BezoutValuationIncidence.Sieve.PrimePowerCompensationOfWitnessClasses
import Mathlib.Data.Real.Basic

/-!
# Moments of the compensated primitive-triple sieve

On primitive triples modulo p² the compensation weight has values 0, 1
and p. The support and all positive moments are determined by the
measure of the recovered ray. Constant compensation is the unique
least-square correction among unbiased weights on that ray.
-/

noncomputable section
open Finset
open scoped Classical
namespace GaloisForLFunctions.BezoutValuationIncidence.LocalConditioning.Moments

variable (p : ℕ) [hp : Fact p.Prime]
abbrev High := Σ s : Sample (ZMod p), TripleLift p 1 s
private instance : NeZero (p^(1+1)) := ⟨pow_ne_zero _ hp.out.ne_zero⟩

def hit (K : (RingAt p 1)ˣ) (t : High p) : Prop :=
  product (ZMod p) (reduce p 1 (K : RingAt p 1)) t.1=1

def recovered (K : (RingAt p 1)ˣ) (r : (ZMod p)ˣ) (t : High p) : Prop :=
  hit p K t ∧ t.1.1.val.1 + (r : ZMod p)*t.1.1.val.2=0 ∧
  (K : RingAt p 1)*t.2.1.val*t.2.2.1.val*t.2.2.2.val ≠ 1

private def removedEquiv (K : (RingAt p 1)ˣ) :
    {t : High p // hit p K t} ≃ Removed p 1 (K : RingAt p 1) where
  toFun t := ⟨⟨t.val.1,t.property⟩,t.val.2⟩
  invFun t := ⟨⟨t.1.val,t.2⟩,t.1.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

private def recoveredEquiv (K : (RingAt p 1)ˣ) (r : (ZMod p)ˣ) :
    {t : High p // recovered p K r t} ≃ Recovered p 1 (K : RingAt p 1) r where
  toFun t := ⟨⟨⟨t.val.1,t.property.1⟩,t.property.2.1⟩,t.val.2.1,t.val.2.2.1,
    ⟨t.val.2.2.2,t.property.2.2⟩⟩
  invFun t := ⟨⟨t.1.val.val,t.2.1,t.2.2.1,t.2.2.2.val⟩,
    t.1.val.property,t.1.property,t.2.2.2.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

private theorem card_high : Fintype.card (High p) = ((p^2-1)*p)*p^3 := by
  simp only [High,Fintype.card_sigma,TripleLift,Fintype.card_prod,count_lift,pow_one,
    sum_const,card_univ,count_sample,ZMod.card,nsmul_eq_mul,Nat.cast_id]
  ring

/-- Uniform average on a finite residue space. -/
def mean {X : Type*} [Fintype X] (f : X → ℝ) := (∑ x, f x)/Fintype.card X

def mark {X : Type*} (P : X → Prop) (x : X) : ℝ := if P x then 1 else 0

private theorem sum_mark {X : Type*} [Fintype X] (P : X → Prop) :
    ∑ x, mark P x = (Fintype.card {x : X // P x} : ℝ) := by
  rw [Fintype.card_subtype,Finset.natCast_card_filter]
  rfl

/-- Probability of landing on the recovered ray in the full primitive sample. -/
def rayMass (p : ℕ) : ℝ := ((p : ℝ)-1)/((p : ℝ)^2*(p+1))

theorem recovered_mass (K : (RingAt p 1)ˣ) (r : (ZMod p)ˣ) :
    mean (mark (recovered p K r))=rayMass p := by
  rw [mean,sum_mark,Fintype.card_congr (recoveredEquiv p K r),count_recovered,card_high,pow_one]
  have h₁ := hp.out.one_lt
  have h₂ : 1 ≤ p^2 := pow_pos hp.out.pos 2
  push_cast [Nat.cast_sub (by omega : 1≤p),Nat.cast_sub h₂]
  have hP : (1 : ℝ)<p := by exact_mod_cast h₁
  have hs : (p : ℝ)^2-1 ≠ 0 := by nlinarith only [hP,sq_nonneg ((p : ℝ)-1)]
  have hpos : (0 : ℝ)<p := one_pos.trans hP
  unfold rayMass
  field_simp
  ring

private theorem balance (K : (RingAt p 1)ˣ) (r : (ZMod p)ˣ) :
    (p : ℝ)*(∑ t, mark (recovered p K r) t) = ∑ t, mark (hit p K) t := by
  rw [sum_mark,sum_mark,Fintype.card_congr (recoveredEquiv p K r),
    Fintype.card_congr (removedEquiv p K)]
  exact_mod_cast square_compensation p K r

/-- Compensated local weight on a primitive lift. -/
def weight (K : (RingAt p 1)ˣ) (r : (ZMod p)ˣ) (t : High p) : ℝ :=
  if recovered p K r t then p else if hit p K t then 0 else 1

private theorem high_pos : (0 : ℝ)<Fintype.card (High p) := by
  rw [card_high]
  have hpos : 0<p^2-1 := Nat.sub_pos_of_lt (one_lt_pow₀ hp.out.one_lt (by norm_num))
  exact_mod_cast Nat.mul_pos (Nat.mul_pos hpos hp.out.pos) (pow_pos hp.out.pos 3)

/-- Complete three-point law. It applies to every real observable of the
weight, including indicators and arbitrary moments. -/
theorem local_law (K : (RingAt p 1)ˣ) (r : (ZMod p)ˣ) (F : ℝ → ℝ) :
    mean (fun t => F (weight p K r t)) =
      F 1+(((p : ℝ)-1)*F 0-p*F 1+F p)*rayMass p := by
  have he := recovered_mass p K r
  have law (t : High p) : F (weight p K r t) =
      F 1+(F 0-F 1)*mark (hit p K) t+(F p-F 0)*mark (recovered p K r) t := by
    by_cases hr : recovered p K r t
    · simp [weight,mark,hr,hr.1]
    · by_cases hh : hit p K t <;> simp [weight,mark,hr,hh]
  rw [mean] at he
  simp only [mean,law,sum_add_distrib,← mul_sum,← balance p K r,
    sum_const,card_univ,nsmul_eq_mul,← he]
  field_simp [(high_pos p).ne']
  ring

/-- All positive integer moments are affine functions of the recovered mass. -/
theorem moment (K : (RingAt p 1)ˣ) (r : (ZMod p)ˣ) (k : ℕ) :
    mean (fun t => (weight p K r t)^(k+1)) = 1+((p : ℝ)^(k+1)-p)*rayMass p := by
  simpa [sub_eq_add_neg,add_comm,add_left_comm,add_assoc] using
    local_law p K r (fun x => x^(k+1))

theorem mean_one (K : (RingAt p 1)ˣ) (r : (ZMod p)ˣ) : mean (weight p K r)=1 := by
  simpa only [pow_one,sub_self,zero_mul,add_zero] using moment p K r 0

/-- After compensation the surviving support loses a fraction (p−1) times
the recovered-ray mass. -/
theorem support_mass (K : (RingAt p 1)ˣ) (r : (ZMod p)ˣ) :
    mean (mark (fun t => weight p K r t ≠ 0)) = 1-(p-1)*rayMass p := by
  have hp' : (p : ℝ)≠0 := Nat.cast_ne_zero.mpr hp.out.ne_zero
  have h := local_law p K r (fun x : ℝ => if x≠0 then 1 else 0)
  change mean (fun t => if weight p K r t≠0 then 1 else 0) = _
  rw [h]
  simp only [one_ne_zero,ite_true,ne_self,ite_false,hp',mul_zero,mul_one,zero_sub]
  ring

/-- Exact square-level variance. It approaches one along the primes. -/
theorem variance (K : (RingAt p 1)ˣ) (r : (ZMod p)ˣ) :
    mean (fun t => (weight p K r t-1)^2) = ((p : ℝ)-1)^2/(p*(p+1)) := by
  have hp' : (0 : ℝ)<p := Nat.cast_pos.mpr hp.out.pos
  rw [local_law p K r (fun x => (x-1)^2),rayMass]
  field_simp
  ring

/-- Redistributing a fixed total among recovered triples adds precisely
the sum of squared deviations from the constant correction. -/
theorem redistribution (K : (RingAt p 1)ˣ) (r : (ZMod p)ˣ)
    (f : Recovered p 1 (K : RingAt p 1) r → ℝ)
    (h : ∑ x, f x = Fintype.card (Removed p 1 (K : RingAt p 1))) :
    ∑ x, (f x)^2 = (Fintype.card (Recovered p 1 (K : RingAt p 1) r) : ℝ)*p^2 +
      ∑ x, (f x-p)^2 := by
  have hc : (p : ℝ)*Fintype.card (Recovered p 1 (K : RingAt p 1) r)=
      Fintype.card (Removed p 1 (K : RingAt p 1)) := by exact_mod_cast square_compensation p K r
  simp_rw [sub_sq,sum_add_distrib,sum_sub_distrib,← mul_sum,← sum_mul,h,← hc,
    sum_const,card_univ,nsmul_eq_mul]
  ring

/-- Equality in the least second-moment bound determines the correction
on every recovered residue class. -/
theorem least_square_iff (K : (RingAt p 1)ˣ) (r : (ZMod p)ˣ)
    (f : Recovered p 1 (K : RingAt p 1) r → ℝ)
    (h : ∑ x, f x = Fintype.card (Removed p 1 (K : RingAt p 1))) :
    (∑ x, (f x)^2) = (Fintype.card (Recovered p 1 (K : RingAt p 1) r) : ℝ)*p^2 ↔
      ∀ x, f x=p := by
  rw [redistribution p K r f h,add_eq_left,Finset.sum_eq_zero_iff_of_nonneg (fun x _ => sq_nonneg _)]
  simp [sub_eq_zero]

end GaloisForLFunctions.BezoutValuationIncidence.LocalConditioning.Moments

#print axioms GaloisForLFunctions.BezoutValuationIncidence.LocalConditioning.Moments.recovered_mass
#print axioms GaloisForLFunctions.BezoutValuationIncidence.LocalConditioning.Moments.local_law
#print axioms GaloisForLFunctions.BezoutValuationIncidence.LocalConditioning.Moments.moment
#print axioms GaloisForLFunctions.BezoutValuationIncidence.LocalConditioning.Moments.mean_one
#print axioms GaloisForLFunctions.BezoutValuationIncidence.LocalConditioning.Moments.support_mass
#print axioms GaloisForLFunctions.BezoutValuationIncidence.LocalConditioning.Moments.variance
#print axioms GaloisForLFunctions.BezoutValuationIncidence.LocalConditioning.Moments.redistribution
#print axioms GaloisForLFunctions.BezoutValuationIncidence.LocalConditioning.Moments.least_square_iff
