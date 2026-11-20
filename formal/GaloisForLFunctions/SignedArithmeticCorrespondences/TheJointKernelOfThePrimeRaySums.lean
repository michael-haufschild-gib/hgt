import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.TheEulerFactorsOfTheDivisorSumPayEveryContact
import Mathlib.LinearAlgebra.Finsupp.Supported
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Joint cancellation on prime rays

Summing a profile over each p-ray sets the p-dilation equal to the
identity. Its kernel consists precisely of p-differences. Independent
prime directions can be divided out successively. Every division keeps
the first occupied integer and divides the last by p, so the exact cost
in multiplicative width is the product of the selected primes.
-/
noncomputable section
open Finset GaloisForLFunctions.AbsoluteGeometryOfSpecZ
namespace GaloisForLFunctions.SignedArithmeticCorrespondences.PrimeRays
abbrev Profile := ℕ+ →₀ ℝ

/-- Unique p-free member of the ray of a positive integer. -/
def core (p : Nat.Primes) (u : ℕ+) : ℕ+ :=
  ⟨ordCompl[(p:ℕ)] (u:ℕ),Nat.ordCompl_pos _ u.ne_zero⟩

/-- Sum over each ray of integers differing by a power of p. -/
def ray (p : Nat.Primes) (c : Profile) : Profile := c.mapDomain (core p)
private def shift (p : Nat.Primes) (c : Profile) : Profile :=
  c.mapDomain (fun n => primePNat p*n)

/-- Multiplicative finite difference from the identity to dilation by p. -/
def difference (p : Nat.Primes) (c : Profile) : Profile := shift p c-c

private theorem same_core (p : Nat.Primes) (u : ℕ+) :
    core p (primePNat p*u)=core p u := by
  apply PNat.eq
  simp [core,PNat.mul_coe,Nat.ordCompl_mul,show ordCompl[(p:ℕ)] (p:ℕ)=1 by simpa using (Nat.ordCompl_self_pow (k:=1) p.2)]

private theorem other_core {q p : Nat.Primes} (hq : q≠p) (u : ℕ+) :
    core q (primePNat p*u)=primePNat p*core q u := by
  have hh : ¬(q:ℕ) ∣ (p:ℕ) := fun hd => hq (Subtype.ext ((Nat.prime_dvd_prime_iff_eq q.2 p.2).mp hd))
  have he : ordCompl[(q:ℕ)] (p:ℕ)=(p:ℕ) := by
    change (p:ℕ)/(q:ℕ)^((p:ℕ).factorization q)=(p:ℕ)
    rw [Nat.factorization_eq_zero_of_not_dvd hh,pow_zero,Nat.div_one]
  apply PNat.eq
  simp only [core,PNat.mul_coe,primePNat_coe,PNat.mk_coe,Nat.ordCompl_mul,he]

theorem ray_difference_self (p : Nat.Primes) (b : Profile) : ray p (difference p b)=0 := by
  unfold ray difference shift
  rw [Finsupp.mapDomain_sub,←Finsupp.mapDomain_comp]
  exact sub_eq_zero.mpr (Finsupp.mapDomain_congr fun u _ => same_core p u)

theorem ray_difference_other {q p : Nat.Primes} (h : q≠p) (b : Profile) :
    ray q (difference p b)=difference p (ray q b) := by
  unfold ray difference shift
  rw [Finsupp.mapDomain_sub,←Finsupp.mapDomain_comp,←Finsupp.mapDomain_comp]
  exact congrArg (· - Finsupp.mapDomain (core q) b) (Finsupp.mapDomain_congr fun u _ => other_core h u)

/-- The removed prime power times the p-free component recovers the site. -/
theorem core_power (p : Nat.Primes) (u : ℕ+) :
    primePNat p^((u:ℕ).factorization p)*core p u=u :=
  PNat.eq (Nat.ordProj_mul_ordCompl_eq_self _ _)

private def primitiveAtom (p : Nat.Primes) (u : ℕ+) (c : ℝ) : Profile :=
  ∑ j∈range ((u:ℕ).factorization p), Finsupp.single ((primePNat p)^j*core p u) c

private theorem diff_atom (p : Nat.Primes) (u : ℕ+) (a : ℝ) :
    difference p (primitiveAtom p u a)=Finsupp.single u a-Finsupp.single (core p u) a := by
  let f (j : ℕ) : Profile := Finsupp.single ((primePNat p)^j*core p u) a
  change Finsupp.mapDomain _ (∑ j∈range _, f j) - (∑ j∈range _, f j)=_
  rw [Finsupp.mapDomain_finsetSum,←sum_sub_distrib]
  have he (j : ℕ) : Finsupp.mapDomain (fun n => primePNat p*n) (f j)=f (j+1) := by
    dsimp only [f]; rw [Finsupp.mapDomain_single,pow_succ',mul_assoc]
  simp_rw [he]
  rw [sum_range_sub, f, f, pow_zero,one_mul,core_power]

/-- Division by a prime difference is possible on finitely supported
profiles exactly when every full ray sum vanishes. -/
theorem one_ray_exact (p : Nat.Primes) (c : Profile) : ray p c=0 ↔ ∃ b, difference p b=c := by
  constructor
  · intro hc
    refine ⟨∑ u∈c.support,primitiveAtom p u (c u),?_⟩
    unfold difference shift
    rw [Finsupp.mapDomain_finsetSum,←sum_sub_distrib]
    change ∑ u∈c.support,difference p (primitiveAtom p u (c u))=c
    simp_rw [diff_atom]
    rw [sum_sub_distrib]
    change c.sum Finsupp.single - ray p c=c
    rw [Finsupp.sum_single,hc,sub_zero]
  · rintro ⟨b,rfl⟩; exact ray_difference_self p b

/-- Support on the actual comb, permitting precisely A<n and d*n≤B. -/
def inside (A B d : ℕ) (c : Profile) := ∀ n∈c.support,A<(n:ℕ) ∧ d*(n:ℕ)≤B

private theorem shift_at (p : Nat.Primes) (b : Profile) (n : ℕ+) :
    shift p b (primePNat p*n)=b n :=
  Finsupp.mapDomain_apply (fun _ _ h => mul_left_cancel h) b n

private theorem shift_mem {p : Nat.Primes} {b : Profile} {n : ℕ+} (h : shift p b n≠0) :
    ∃ u∈b.support,primePNat p*u=n := by
  by_contra! hn
  exact h <| Finsupp.mapDomain_of_not_mem_image_support (fun ⟨u,hu,he⟩ => hn u hu he)

private theorem grows (p : Nat.Primes) (u : ℕ+) : u<primePNat p*u := by
  change (u:ℕ)<(p:ℕ)*(u:ℕ)
  simpa only [one_mul] using Nat.mul_lt_mul_of_pos_right p.2.one_lt u.pos

/-- The first and last occupied sites cannot cancel with their own
nontrivial dilates. This gives the exact support cost in both directions. -/
theorem inside_difference (A B d : ℕ) (p : Nat.Primes) (b : Profile) :
    inside A B d (difference p b) ↔ inside A B (d*p) b := by
  classical
  constructor
  · intro h n hn
    let l := b.support.min' ⟨n,hn⟩
    let u := b.support.max' ⟨n,hn⟩
    have hl : l∈b.support := min'_mem _ _
    have hu : u∈b.support := max'_mem _ _
    have hsl : shift p b l=0 := by
      by_contra hh
      obtain ⟨v,hv,he⟩ := shift_mem hh
      exact (not_lt_of_ge (b.support.min'_le v hv)) (he ▸ grows p v)
    have hsu : b (primePNat p*u)=0 := by
      by_contra hh
      exact (grows p u).not_ge (b.support.le_max' _ (Finsupp.mem_support_iff.mpr hh))
    have hl' : l∈(difference p b).support := by
      simp only [Finsupp.mem_support_iff,difference,Finsupp.sub_apply,hsl,zero_sub,neg_ne_zero]
      exact Finsupp.mem_support_iff.mp hl
    have hu' : primePNat p*u∈(difference p b).support := by
      simp only [Finsupp.mem_support_iff,difference,Finsupp.sub_apply,hsu,sub_zero,shift_at]
      exact Finsupp.mem_support_iff.mp hu
    refine ⟨(h l hl').1.trans_le (b.support.min'_le n hn),?_⟩
    calc d*(p:ℕ)*(n:ℕ) ≤ d*p*(u:ℕ) := Nat.mul_le_mul_left _ (b.support.le_max' n hn)
         _ = d*((primePNat p*u:ℕ+):ℕ) := Nat.mul_assoc _ _ _
         _ ≤ B := (h _ hu').2
  · intro h n hn
    have hne := Finsupp.mem_support_iff.mp hn
    by_cases hb : b n=0
    · have hs : shift p b n≠0 := by
        simpa only [difference,Finsupp.sub_apply,hb,sub_zero] using hne
      obtain ⟨u,hu,rfl⟩ := shift_mem hs
      exact ⟨(h u hu).1.trans (grows p u),by simpa only [PNat.mul_coe,primePNat_coe,Nat.mul_assoc] using (h u hu).2⟩
    · have hh := h n (Finsupp.mem_support_iff.mpr hb)
      refine ⟨hh.1,?_⟩
      calc d*(n:ℕ) ≤ (d*p)*n := by
             simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left d (le_of_lt (grows p n) : (n:ℕ)≤(p:ℕ)*n)
           _ ≤ B := hh.2

private theorem difference_kernel (p : Nat.Primes) {b : Profile} (h : difference p b=0) : b=0 := by
  classical
  by_contra hb
  obtain ⟨n,hn⟩ := Finsupp.support_nonempty_iff.mpr hb
  let M := b.support.max' ⟨n,hn⟩
  have hM : M∈b.support := max'_mem _ _
  have hz : b (primePNat p*M)=0 := by
    by_contra he
    exact (grows p M).not_ge (b.support.le_max' _ (Finsupp.mem_support_iff.mpr he))
  have hh := DFunLike.congr_fun h (primePNat p*M)
  simp only [difference,Finsupp.sub_apply,shift_at,hz,sub_zero,Finsupp.zero_apply] at hh
  exact Finsupp.mem_support_iff.mp hM hh

theorem difference_injective (p : Nat.Primes) : Function.Injective (difference p) := by
  intro u v h
  apply sub_eq_zero.mp
  apply difference_kernel p
  change Finsupp.mapDomain _ (u-v)-(u-v)=0
  rw [Finsupp.mapDomain_sub]
  change shift p u-shift p v-(u-v)=0
  change shift p u-u=shift p v-v at h
  calc _ = (shift p u-u)-(shift p v-v) := by abel
       _ = 0 := sub_eq_zero.mpr h

/-- Product of the independent prime differences. -/
def mixedDifference : List Nat.Primes → Profile → Profile
  | [],b => b
  | p::P,b => difference p (mixedDifference P b)

def modulus (P : List Nat.Primes) : ℕ := (P.map (fun p => (p:ℕ))).prod

theorem mixed_injective (P : List Nat.Primes) : Function.Injective (mixedDifference P) := by
  induction P with
  | nil => exact fun _ _ h => h
  | cons p P ih => exact (difference_injective p).comp ih

private theorem mixed_zero (P : List Nat.Primes) : mixedDifference P 0=0 := by
  induction P with
  | nil => rfl
  | cons p P ih => simp [mixedDifference,ih,difference,shift]

private theorem mixed_range (P : List Nat.Primes) (hP : P.Nodup) (c : Profile) :
    (∀ p∈P,ray p c=0) ↔ ∃ b,mixedDifference P b=c := by
  induction P generalizing c with
  | nil => simp [mixedDifference]
  | cons p P ih =>
    have hn := List.nodup_cons.mp hP
    constructor
    · intro h
      obtain ⟨u,hu⟩ := (one_ray_exact p c).mp (h p (by simp))
      have htail (q : Nat.Primes) (hq:q∈P) : ray q u=0 := by
        apply difference_kernel p
        rw [←ray_difference_other (show q≠p by rintro rfl; exact hn.1 hq),hu]
        exact h q (List.mem_cons_of_mem _ hq)
      obtain ⟨b,hb⟩ := (ih hn.2 u).mp htail
      exact ⟨b,by rw [mixedDifference,hb,hu]⟩
    · rintro ⟨b,rfl⟩ q hq
      rcases List.mem_cons.mp hq with rfl|hq
      · exact ray_difference_self _ _
      · rw [mixedDifference,ray_difference_other (show q≠p by rintro rfl; exact hn.1 hq),
          (ih hn.2 _).mpr ⟨b,rfl⟩ q hq]
        simp [difference,shift]

private theorem inside_mixed (P : List Nat.Primes) (A B d : ℕ) (b : Profile) :
    inside A B d (mixedDifference P b) ↔ inside A B (d*modulus P) b := by
  induction P generalizing d with
  | nil => simp [mixedDifference,modulus]
  | cons p P ih => simpa [mixedDifference,modulus,Nat.mul_assoc] using
      (inside_difference A B d p (mixedDifference P b)).trans (ih (d*(p:ℕ)))

/-- Complete parametrization. The residual profile on the shortened
integer interval is unique. Every such profile supplies a joint kernel
vector on the original comb. -/
theorem joint_ray_kernel (P : List Nat.Primes) (hP : P.Nodup) (A B : ℕ) (c : Profile) :
    (inside A B 1 c ∧ ∀ p∈P,ray p c=0) ↔
      ∃! b,inside A B (modulus P) b ∧ mixedDifference P b=c := by
  constructor
  · rintro ⟨hi,hr⟩
    obtain ⟨b,rfl⟩ := (mixed_range P hP c).mp hr
    refine ⟨b,⟨?_,rfl⟩,fun y hy => mixed_injective P hy.2⟩
    simpa only [one_mul] using (inside_mixed P A B 1 b).mp hi
  · rintro ⟨b,⟨hi,rfl⟩,_⟩
    exact ⟨(inside_mixed P A B 1 b).mpr (by simpa only [one_mul] using hi),
      (mixed_range P hP _).mpr ⟨b,rfl⟩⟩

/-- The primorial width is necessary and sufficient at the exact integer
endpoints, attained by a mixed difference of one mass at A+1. -/
theorem nonzero_joint_ray_kernel_iff (P : List Nat.Primes) (hP : P.Nodup) (A B : ℕ) :
    (∃ c : Profile,c≠0 ∧ inside A B 1 c ∧ ∀ p∈P,ray p c=0) ↔
      modulus P*(A+1)≤B := by
  constructor
  · rintro ⟨c,hc,hi,hr⟩
    obtain ⟨b,⟨hb,he⟩,_⟩ := (joint_ray_kernel P hP A B c).mp ⟨hi,hr⟩
    have hb' : b≠0 := fun hz => hc (he.symm.trans (hz ▸ mixed_zero P))
    obtain ⟨n,hn⟩ := Finsupp.support_nonempty_iff.mpr hb'
    exact (Nat.mul_le_mul_left _ (hb n hn).1).trans (hb n hn).2
  · intro h
    let a : ℕ+ := ⟨A+1,by omega⟩
    let b : Profile := Finsupp.single a 1
    have hb : b≠0 := Finsupp.single_ne_zero.mpr one_ne_zero
    have hi : inside A B (modulus P) b := by
      intro n hn
      have he : n=a := by simpa [b] using hn
      subst n; exact ⟨by dsimp only [a];omega,h⟩
    refine ⟨mixedDifference P b,fun hz => hb (mixed_injective P (hz.trans (mixed_zero P).symm)),
      (inside_mixed P A B 1 b).mpr (by simpa only [one_mul] using hi),(mixed_range P hP _).mpr ⟨b,rfl⟩⟩

private def mixedMap : List Nat.Primes → Profile →ₗ[ℝ] Profile
  | [] => LinearMap.id
  | p::P => (Finsupp.lmapDomain ℝ ℝ (fun n => primePNat p*n)-LinearMap.id).comp (mixedMap P)

private theorem mixedMap_apply (P : List Nat.Primes) (c : Profile) :
    mixedMap P c=mixedDifference P c := by
  induction P with
  | nil => rfl
  | cons p P ih => simp only [mixedMap,mixedDifference,LinearMap.comp_apply,LinearMap.sub_apply,
      LinearMap.id_apply,Finsupp.lmapDomain_apply,ih,difference,shift]

private def box (A B d : ℕ) := Finsupp.supported ℝ ℝ {n : ℕ+ | A<(n:ℕ) ∧ d*(n:ℕ)≤B}

/-- Linear space of comb profiles whose sums vanish on every selected ray. -/
def cancellationSpace (P : List Nat.Primes) (A B : ℕ) : Submodule ℝ Profile :=
  box A B 1 ⊓ ⨅ p : {q // q∈P},(Finsupp.lmapDomain ℝ ℝ (core p.val)).ker

private theorem mem_cancel {P : List Nat.Primes} {A B : ℕ} {c : Profile} :
    c∈cancellationSpace P A B ↔ inside A B 1 c ∧ ∀ p∈P,ray p c=0 := by
  simp only [cancellationSpace,Submodule.mem_inf,Submodule.mem_iInf,LinearMap.mem_ker,
    Finsupp.lmapDomain_apply,Subtype.forall,ray]
  rfl

private def residualMap (P : List Nat.Primes) (hP : P.Nodup) (A B : ℕ) :
    box A B (modulus P) →ₗ[ℝ] cancellationSpace P A B :=
  (((mixedMap P).comp (box A B (modulus P)).subtype).codRestrict (cancellationSpace P A B)
    (fun x => by
      rw [LinearMap.comp_apply,Submodule.subtype_apply,mixedMap_apply,mem_cancel]
      exact ⟨(inside_mixed P A B 1 _).mpr (by simpa only [one_mul] using x.property),
        (mixed_range P hP _).mpr ⟨x.val,rfl⟩⟩))

private theorem box_dimension (A B d : ℕ) (hd : 0<d) :
    Module.finrank ℝ (box A B d)=B/d-A := by
  classical
  let S := {n : ℕ+ | A<(n:ℕ) ∧ d*(n:ℕ)≤B}
  let T := Ioc A (B/d)
  let e : S ≃ T :=
    { toFun := fun n => ⟨n.val.val,mem_Ioc.mpr ⟨n.property.1,(Nat.le_div_iff_mul_le hd).mpr
        (by simpa only [Nat.mul_comm] using n.property.2)⟩⟩
      invFun := fun n => ⟨⟨n.val,(Nat.zero_le _).trans_lt (mem_Ioc.mp n.property).1⟩,
        (mem_Ioc.mp n.property).1,by
          simpa only [Nat.mul_comm] using (Nat.le_div_iff_mul_le hd).mp (mem_Ioc.mp n.property).2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  letI : Fintype S := Fintype.ofEquiv T e.symm
  calc Module.finrank ℝ (box A B d) = Module.finrank ℝ (S →₀ ℝ) :=
         (Finsupp.supportedEquivFinsupp (R:=ℝ) (M:=ℝ) S).finrank_eq
       _ = Fintype.card S := Module.finrank_finsupp_self
       _ = Fintype.card T := Fintype.card_congr e
       _ = B/d-A := by simp [T]

/-- Exact multiplicity of the lowest possible prime contact energy. Every
integer remaining after division of the upper cutoff by the primorial
supplies one independent mixed-difference profile. -/
theorem dimension_joint_ray_kernel (P : List Nat.Primes) (hP : P.Nodup) (A B : ℕ) :
    Module.finrank ℝ (cancellationSpace P A B)=B/modulus P-A := by
  let f := residualMap P hP A B
  have hval (x : box A B (modulus P)) :
      (f x:Profile)=mixedDifference P x := mixedMap_apply P x
  have hi : Function.Injective f := by
    intro x y he
    apply Subtype.ext
    apply mixed_injective P
    exact (hval _).symm.trans ((congrArg Subtype.val he).trans (hval _))
  have hs : Function.Surjective f := by
    intro c
    obtain ⟨b,⟨hb,he⟩,_⟩ := (joint_ray_kernel P hP A B c).mp (mem_cancel.mp c.property)
    exact ⟨⟨b,hb⟩,Subtype.ext ((hval _).trans he)⟩
  have hp : 0<modulus P := by
    induction P with
    | nil => exact Nat.zero_lt_one
    | cons p P ih => exact Nat.mul_pos p.2.pos (ih (List.nodup_cons.mp hP).2)
  exact (LinearEquiv.ofBijective f ⟨hi,hs⟩).finrank_eq.symm.trans (box_dimension A B _ hp)

end GaloisForLFunctions.SignedArithmeticCorrespondences.PrimeRays
