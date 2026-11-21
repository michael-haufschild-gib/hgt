import GaloisForLFunctions.SignedArithmeticCorrespondences.TheJointKernelOfThePrimeRaySums
import GaloisForLFunctions.HodgeTheoryOfAFixedPart.TheCombOfUnitMassesFixesTheContacts

/-!
# The lower spectral endpoint of the prime-power contacts

The selected von Mangoldt matrix is a sum of complete graphs on the
prime rays, with the diagonal subtracted. Equality in its lower bound
requires every ray sum to vanish. The prime-difference factorization
therefore determines the exact finite-window endpoint and its eigenspace.
-/
noncomputable section
open Finset ArithmeticFunction GaloisForLFunctions.AbsoluteGeometryOfSpecZ
open GaloisForLFunctions.HodgeTheoryOfAFixedPart
open scoped ArithmeticFunction.vonMangoldt
namespace GaloisForLFunctions.SignedArithmeticCorrespondences.PrimeRays

private theorem ordered_ray {p : Nat.Primes} {m n : ℕ+} (hmn : m<n) :
    core p m=core p n ↔ ∃ j : ℕ, 0<j ∧ n=m*primePNat p^j := by
  constructor
  · intro h
    let a := (m:ℕ).factorization p
    let b := (n:ℕ).factorization p
    have he₁ := core_power p m
    have he₂ := core_power p n
    rw [←h] at he₂
    have hlt : a<b := by
      by_contra! hh
      have hs : (p:ℕ)^b ≤ (p:ℕ)^a := Nat.pow_le_pow_right p.2.pos hh
      have hbad : n≤ m := by
        rw [←he₁,←he₂]
        exact mul_le_mul_right' (show primePNat p^b≤primePNat p^a from hs) _
      exact hmn.not_ge hbad
    refine ⟨b-a,by omega,?_⟩
    calc n = primePNat p^b*core p m := he₂.symm
         _ = (primePNat p^a*core p m)*primePNat p^(b-a) := by
           nth_rw 1 [show b=a+(b-a) by omega]
           rw [pow_add];ring
         _ = _ := by rw [he₁]
  · rintro ⟨j,_,rfl⟩
    apply PNat.eq
    simp only [core,PNat.mk_coe,PNat.mul_coe,PNat.pow_coe,primePNat_coe,Nat.ordCompl_mul,
      Nat.ordCompl_self_pow p.2,mul_one]

open scoped Classical in
/-- Projection of an actual Mangoldt contact onto the selected primes. -/
def selectedWeight (P : Finset Nat.Primes) (k : ℕ) : ℝ :=
  if ∃ p∈P, ∃ j : ℕ,0<j ∧ k=(p:ℕ)^j then ArithmeticFunction.vonMangoldt k else 0

private def clique (p : Nat.Primes) (m n : ℕ+) : ℝ :=
  if m≠n ∧ core p m=core p n then Real.log p else 0
private theorem clique_comm (p : Nat.Primes) (m n : ℕ+) : clique p m n=clique p n m := by
  unfold clique
  by_cases h : m ≠ n ∧ core p m = core p n
  · rw [if_pos h,if_pos ⟨Ne.symm h.1,h.2.symm⟩]
  · rw [if_neg h,if_neg (fun h' => h ⟨Ne.symm h'.1,h'.2.symm⟩)]

/-- Each selected contact is the sum of its prime-ray clique entries. -/
theorem selected_entry (P : Finset Nat.Primes) (m n : ℕ+) :
    contactW (selectedWeight P) m n=∑ p∈P,clique p m n := by
  classical
  suffices h : ∀ m n : ℕ+,m<n → contactW (selectedWeight P) m n=∑ p∈P,clique p m n by
    rcases lt_trichotomy m n with hl|rfl|hl
    · exact h _ _ hl
    · have h1 : ¬∃ p∈P,∃ j : ℕ,0<j ∧ 1=(p:ℕ)^j := by
        rintro ⟨p,_,j,hj,hj'⟩
        exact (one_lt_pow₀ p.2.one_lt hj.ne').ne' hj'.symm
      simp [contactW,selectedWeight,clique,Nat.div_self m.pos,h1]
    · simpa only [contactW,add_comm,clique_comm _ n m] using h n m hl
  intro m n hmn
  have hn : ¬(n:ℕ)∣m := fun hd => hmn.not_ge (Nat.le_of_dvd m.pos hd)
  rw [contactW,if_neg hn,add_zero]
  by_cases hw : ∃ p∈P,core p m=core p n
  · obtain ⟨p,hp,he⟩ := hw
    obtain ⟨j,hj,h⟩ := (ordered_ray hmn).mp he
    have hn' : (n:ℕ)=(m:ℕ)*(p:ℕ)^j := congrArg PNat.val h
    rw [if_pos (show (m:ℕ)∣n from ⟨_,hn'⟩),hn',Nat.mul_div_cancel_left _ m.pos,
      selectedWeight,if_pos ⟨p,hp,j,hj,rfl⟩,vonMangoldt_apply_pow hj.ne',vonMangoldt_apply_prime p.2]
    rw [sum_eq_single p,clique,if_pos ⟨hmn.ne,he⟩]
    · intro q hq hqp
      rw [clique,if_neg]
      rintro ⟨_,hcore⟩
      obtain ⟨k,hk,hh⟩ := (ordered_ray hmn).mp hcore
      have hpows := mul_left_cancel (h.symm.trans hh)
      have hd : (q:ℕ) ∣ (p:ℕ)^j := by
        rw [show (p:ℕ)^j=(q:ℕ)^k from congrArg PNat.val hpows]
        exact dvd_pow_self _ hk.ne'
      exact hqp (Subtype.ext ((Nat.prime_dvd_prime_iff_eq q.2 p.2).mp (q.2.dvd_of_dvd_pow hd)))
    · exact fun h => False.elim (h hp)
  · rw [sum_eq_zero (f := fun q => clique q m n) (fun q hq =>
      if_neg (show ¬(m≠n ∧ core q m=core q n) from fun e => hw ⟨q,hq,e.2⟩))]
    split_ifs with hd
    · rw [selectedWeight,if_neg]
      rintro ⟨p,hp,j,hj,h⟩
      apply hw
      refine ⟨p,hp,(ordered_ray hmn).mpr ⟨j,hj,PNat.eq ?_⟩⟩
      change (n:ℕ)=(m:ℕ)*(p:ℕ)^j
      rw [←h,Nat.mul_div_cancel' hd]
    · rfl

/-- Squared mass on the support of the finite profile. -/
def profileSquare (c : Profile) := ∑ n∈c.support,c n^2
/-- Sum of the squares of the signed masses on all occupied p-rays. -/
def raySquare (p : Nat.Primes) (c : Profile) :=
  ∑ u∈c.support.image (core p),(ray p c u)^2

private theorem ray_at (p : Nat.Primes) (c : Profile) (u : ℕ+) :
    ray p c u=∑ n∈c.support.filter (fun n => core p n=u),c n := by
  simp only [ray,Finsupp.mapDomain,Finsupp.sum,Finsupp.finset_sum_apply,Finsupp.single_apply,sum_filter]

private theorem ray_square (p : Nat.Primes) (c : Profile) :
    raySquare p c = ∑ m∈c.support,∑ n∈c.support,
      if core p m=core p n then c m*c n else 0 := by
  let S := c.support
  let T := S.image (core p)
  have hm (m : ℕ+) (h : m∈S) : core p m∈T := mem_image_of_mem _ h
  rw [←sum_fiberwise_of_maps_to hm (fun m => ∑ n∈c.support,if core p m=core p n then c m*c n else 0)]
  refine sum_congr rfl fun u _ => ?_
  rw [ray_at,sq,sum_mul]
  refine sum_congr rfl fun m hm' => ?_
  rw [mul_sum,sum_filter]
  refine sum_congr rfl fun n _ => ?_
  rw [(mem_filter.mp hm').2]
  exact if_congr eq_comm rfl rfl

private theorem ray_square_zero_iff (p : Nat.Primes) (c : Profile) : raySquare p c=0 ↔ ray p c=0 := by
  constructor
  · intro he
    ext u
    by_cases hu : u∈c.support.image (core p)
    · exact sq_eq_zero_iff.mp ((sum_eq_zero_iff_of_nonneg (fun _ _ => sq_nonneg _)).mp he u hu)
    · apply Finsupp.mapDomain_of_not_mem_image_support
      simpa using hu
  · intro h; simp [raySquare,h]

/-- Rayleigh numerator for the selected actual prime weights. -/
def contactEnergy (P : Finset Nat.Primes) (c : Profile) :=
  ∑ m∈c.support,∑ n∈c.support,contactW (selectedWeight P) m n*c m*c n

private theorem clique_gram (p : Nat.Primes) (c : Profile) :
    (∑ m∈c.support,∑ n∈c.support,clique p m n*c m*c n)=
      Real.log p*(raySquare p c-profileSquare c) := by
  have hterm (m n : ℕ+) :
      clique p m n*c m*c n = Real.log p*
        ((if core p m=core p n then c m*c n else 0)-(if m=n then c m^2 else 0)) := by
    by_cases he : m=n
    · subst n; simp [clique,sq]
    · simp only [clique,he,ne_eq,not_false_eq_true,true_and,if_false,sub_zero]
      split_ifs <;> ring
  simp_rw [hterm]
  rw [ray_square,profileSquare]
  simp_rw [←mul_sum,sum_sub_distrib,Finset.sum_ite_eq]
  congr 2
  exact sum_congr rfl fun m hm => if_pos hm

/-- Exact positive decomposition of the full defect above the lower
endpoint. It also gives every equality case of the contact floor. -/
theorem contact_energy_decomposition (P : Finset Nat.Primes) (c : Profile) :
    contactEnergy P c+(∑ p∈P,Real.log p)*profileSquare c=
      ∑ p∈P,Real.log p*raySquare p c := by
  unfold contactEnergy
  simp_rw [selected_entry,sum_mul]
  -- Move the prime index outside both conductor indices.
  have hswap (m : ℕ+) :
      (∑ n∈c.support,∑ p∈P,clique p m n*c m*c n)=∑ p∈P,∑ n∈c.support,clique p m n*c m*c n := sum_comm
  simp_rw [hswap]
  rw [sum_comm,←sum_add_distrib]
  apply sum_congr rfl
  intro p _
  rw [clique_gram];ring

theorem contact_floor_equality (P : Finset Nat.Primes) (c : Profile) :
    contactEnergy P c= -(∑ p∈P,Real.log p)*profileSquare c ↔ ∀ p∈P,ray p c=0 := by
  have h := contact_energy_decomposition P c
  have he : (contactEnergy P c= -(∑ p∈P,Real.log p)*profileSquare c) ↔
      ∑ p∈P,Real.log p*raySquare p c=0 := by constructor <;> intro hh <;> linarith only [h,hh]
  rw [he,sum_eq_zero_iff_of_nonneg (fun p _ => mul_nonneg
    (Real.log_nonneg (by exact_mod_cast p.2.one_le)) (show 0 ≤ raySquare p c from sum_nonneg fun _ _ => sq_nonneg _))]
  exact forall₂_congr fun p _ => by rw [mul_eq_zero,or_iff_right
    (Real.log_pos (by exact_mod_cast p.2.one_lt)).ne',ray_square_zero_iff]

/-- The finite-window lower endpoint is attained exactly at primorial
width, with all profiles given by the prime-difference factorization. -/
theorem attainable_contact_floor (P : List Nat.Primes) (hP : P.Nodup) (A B : ℕ) :
    (∃ c : Profile,c≠0 ∧ inside A B 1 c ∧
      contactEnergy P.toFinset c= -(∑ p∈P.toFinset,Real.log p)*profileSquare c) ↔
      modulus P*(A+1)≤B := by
  simp only [contact_floor_equality,List.mem_toFinset]
  exact nonzero_joint_ray_kernel_iff P hP A B

/-- All primes that occur as quotients of sites in the integer comb. -/
def primesThrough (k : ℕ) : Finset Nat.Primes := (range (k+1)).subtype Nat.Prime

@[simp] private theorem in_primes (p : Nat.Primes) (k : ℕ) :
    p∈primesThrough k ↔ (p:ℕ)≤k := by
  have h := @Finset.mem_subtype ℕ Nat.Prime _ (range (k+1)) p
  rw [mem_range,Nat.lt_succ_iff] at h
  exact h

private theorem full_weight {r k : ℕ} (hk : r≤k) :
    selectedWeight (primesThrough k) r=ArithmeticFunction.vonMangoldt r := by
  by_cases h : IsPrimePow r
  · obtain ⟨p,j,hp,hj,he⟩ := (isPrimePow_nat_iff _).mp h
    let q : Nat.Primes := ⟨p,hp⟩
    have hpr : p≤r := by
      rw [←he]; simpa only [pow_one] using (Nat.pow_le_pow_right hp.pos hj : p^1≤p^j)
    rw [selectedWeight,if_pos ⟨q,(in_primes q k).mpr (hpr.trans hk),j,hj,he.symm⟩]
  · simp only [selectedWeight,vonMangoldt_eq_zero_iff.mpr h,ite_self]

/-- Quadratic form of the full Mangoldt prime block. -/
def fullContactEnergy (c : Profile) :=
  ∑ m∈c.support,∑ n∈c.support,contactW vonMangoldt m n*c m*c n

private theorem full_on_window {c : Profile} {A B : ℕ} (h : inside A B 1 c) :
    contactEnergy (primesThrough (B/(A+1))) c=fullContactEnergy c := by
  unfold contactEnergy fullContactEnergy
  refine sum_congr rfl fun m hm => sum_congr rfl fun n hn => ?_
  have hquot (m : ℕ+) (hm : m∈c.support) (n : ℕ+) (hn : n∈c.support) :
      (m:ℕ)/n≤B/(A+1) := by
    apply (Nat.div_le_div_right (show (m:ℕ)≤B by simpa only [one_mul] using (h m hm).2)).trans
    exact Nat.div_le_div_left (h n hn).1 (Nat.succ_pos _)
  simp only [contactW,full_weight (hquot m hm n hn),full_weight (hquot n hn m hm)]

private theorem prime_product_pos (P : List Nat.Primes) : 0< modulus P := by
  induction P with
  | nil => exact Nat.zero_lt_one
  | cons p P ih => exact Nat.mul_pos p.2.pos ih

private theorem prime_product_dvd {P : List Nat.Primes} {p : Nat.Primes} (h : p∈P) :
    (p:ℕ) ∣ modulus P := by
  unfold modulus
  exact List.dvd_prod (by simp; exact ⟨p,h,rfl⟩)

/-- Once the quotient cutoff includes 3, the full prime block never
attains the sum of its individual prime lower bounds. Every nonzero
profile on the actual window leaves a strictly positive remainder. -/
theorem strict_full_prime_floor {A B : ℕ} (hB : 3*(A+1)≤B) {c : Profile} (hc : c≠0)
    (h : inside A B 1 c) :
    -(∑ p∈primesThrough (B/(A+1)),Real.log p)*profileSquare c < fullContactEnergy c := by
  let k := B/(A+1)
  let S := primesThrough k
  let P := S.toList
  have hP : P.Nodup := Finset.nodup_toList _
  have hS : P.toFinset=S := Finset.toList_toFinset _
  have hk : 3≤k := (Nat.le_div_iff_mul_le (Nat.succ_pos _)).mpr hB
  have hpos := prime_product_pos P
  have hdiv (p : Nat.Primes) (hp : (p:ℕ)≤k) : (p:ℕ)∣modulus P := by
    apply prime_product_dvd
    exact Finset.mem_toList.mpr ((in_primes p k).mpr hp)
  have h3 : 3≤ modulus P := Nat.le_of_dvd hpos (hdiv ⟨3,Nat.prime_three⟩ hk)
  have hwide : k< modulus P := by
    by_contra! hsmall
    obtain ⟨q,hq,hd⟩ := Nat.exists_prime_and_dvd (show modulus P-1 ≠1 by omega)
    have hqle := Nat.le_of_dvd (show 0< modulus P-1 by omega) hd
    have hqP := hdiv ⟨q,hq⟩ (by show q ≤ k; omega)
    have hone : q∣1 := by
      have he := Nat.dvd_sub hqP hd
      rwa [show modulus P-(modulus P-1)=1 by omega] at he
    exact hq.not_dvd_one hone
  have hem := contact_energy_decomposition S c
  have hnn : 0≤∑ p∈S,Real.log (p:ℝ)*raySquare p c := sum_nonneg fun p _ =>
    mul_nonneg (Real.log_nonneg (by exact_mod_cast p.2.one_le)) (sum_nonneg fun _ _ => sq_nonneg _)
  have hweak : -(∑ p∈S,Real.log (p:ℝ))*profileSquare c≤contactEnergy S c := by linarith only [hem,hnn]
  rw [←full_on_window h]
  refine lt_of_le_of_ne hweak fun he => ?_
  have hn : modulus P*(A+1)≤B := (attainable_contact_floor P hP A B).mp
    ⟨c,hc,h,by simpa only [hS] using he.symm⟩
  exact hwide.not_ge ((Nat.le_div_iff_mul_le (Nat.succ_pos _)).mpr hn)

end GaloisForLFunctions.SignedArithmeticCorrespondences.PrimeRays
