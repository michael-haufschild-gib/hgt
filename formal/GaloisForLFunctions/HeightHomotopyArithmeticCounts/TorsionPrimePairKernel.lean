import GaloisForLFunctions.HeightHomotopyArithmeticCounts.WeightedTorsionLimit

/-!
# Exact prime-pair compressions of the torsion kernel

On a prime and its double, the spacing kernel has a fixed negative coupling
and two tame diagonal terms. Distinct odd-prime pairs have zero mixed entries.
The prime diagonal tends to zero, so equal-coefficient pair vectors eventually
have negative energy, while single prime conductors have positive energy.
-/

noncomputable section
open Filter Topology
namespace GaloisForLFunctions.HeightHomotopyArithmeticCounts
open ArithmeticEffectivityTheory ArithmeticIntersectionTheory

/-- The fixed off-diagonal coupling between a conductor and its double. -/
def spacingPrimePairCoupling : ℝ := Real.log 2 / Real.sqrt 2

/-- The two conductors in an arithmetic prime-pair block. -/
def spacingPrimePairConductor (p : ℕ) : Bool → ℕ
  | false => p
  | true => 2*p

/-- The diagonal of the spacing kernel is exactly the tame different. -/
theorem spacingLimitKernel_self (n : ℕ) : spacingLimitKernel n n = tameDifferent n := by
  rw [spacingLimitKernel,ArithmeticElectrostatics.weilPrimeKernel_self,if_pos rfl,neg_zero,zero_add]

/-- At a prime, the tame different is its single local ramification term. -/
theorem spacing_tameDifferent_prime (p : ℕ) (hp : p.Prime) :
    tameDifferent p = Real.log p / ((p:ℝ)-1) := by
  simpa only [pow_one] using tameDifferent_prime_pow hp (show (1:ℕ)≠0 from one_ne_zero)

private theorem spacing_two_coprime_prime (p : ℕ) (hp : p.Prime) (hp2 : 2<p) :
    Nat.Coprime 2 p := by
  apply Nat.prime_two.coprime_iff_not_dvd.mpr
  intro h
  rcases (Nat.dvd_prime hp).mp h with h1 | h2
  · norm_num at h1
  · omega

/-- Doubling an odd prime adds exactly the local term at two. -/
theorem spacing_tameDifferent_double_prime (p : ℕ) (hp : p.Prime) (hp2 : 2<p) :
    tameDifferent (2*p)=tameDifferent p+Real.log 2 := by
  rw [tameDifferent_mul (spacing_two_coprime_prime p hp hp2),
    spacing_tameDifferent_prime 2 Nat.prime_two]
  norm_num
  ring

private theorem spacing_primeKernel_one_two : weilPrimeKernel 1 2=spacingPrimePairCoupling := by
  rw [weilPrimeKernel,if_pos ⟨one_dvd 2,by norm_num⟩]
  norm_num [spacingPrimePairCoupling,ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]

/-- Doubling any positive conductor gives the same off-diagonal coupling. -/
theorem spacingLimitKernel_double (p : ℕ) (hp : 0<p) :
    spacingLimitKernel p (2*p) = -spacingPrimePairCoupling := by
  have hne : p≠2*p := by omega
  have hP : weilPrimeKernel p (2*p)=spacingPrimePairCoupling := by
    calc _ = weilPrimeKernel (p*1) (p*2) := by rw [mul_one,mul_comm p 2]
         _ = weilPrimeKernel 1 2 := weilPrimeKernel_mul_left hp 1 2
         _ = _ := spacing_primeKernel_one_two
  rw [spacingLimitKernel,if_neg hne,add_zero,hP]

/-- A prime-pair off-diagonal entry is independent of the prime. -/
theorem spacingLimitKernel_prime_double (p : ℕ) (hp : p.Prime) :
    spacingLimitKernel p (2*p) = -spacingPrimePairCoupling :=
  spacingLimitKernel_double p hp.pos

/-- The exact arithmetic matrix on a prime and its double. -/
theorem spacingLimitKernel_primePair (p : ℕ) (hp : p.Prime) (hp2 : 2<p) (i j : Bool) :
    spacingLimitKernel (spacingPrimePairConductor p i) (spacingPrimePairConductor p j) =
      match i,j with
      | false,false => tameDifferent p
      | true,true => tameDifferent p+Real.log 2
      | _,_ => -spacingPrimePairCoupling := by
  cases i <;> cases j
  · exact spacingLimitKernel_self p
  · exact spacingLimitKernel_prime_double p hp
  · exact (spacingLimitKernel_comm (2*p) p).trans (spacingLimitKernel_prime_double p hp)
  · exact (spacingLimitKernel_self (2*p)).trans (spacing_tameDifferent_double_prime p hp hp2)

private theorem spacing_prime_not_dvd_double_prime (p q : ℕ)
    (hp : p.Prime) (hq : q.Prime) (hp2 : 2<p) (hpq : p≠q) : ¬p∣2*q := by
  intro h
  rcases hp.dvd_mul.mp h with htwo | hqdiv
  · have hle := Nat.le_of_dvd (show 0<2 by omega) htwo
    omega
  · rcases (Nat.dvd_prime hq).mp hqdiv with h1 | he
    · exact hp.ne_one h1
    · exact hpq he

private theorem spacing_primePair_not_dvd (p q : ℕ)
    (hp : p.Prime) (hq : q.Prime) (hp2 : 2<p) (hpq : p≠q) (i j : Bool) :
    ¬spacingPrimePairConductor p i ∣ spacingPrimePairConductor q j := by
  have hown : p ∣ spacingPrimePairConductor p i := by
    cases i
    · exact dvd_refl p
    · exact dvd_mul_left p 2
  have htarget : spacingPrimePairConductor q j ∣ 2*q := by
    cases j
    · exact dvd_mul_left q 2
    · exact dvd_refl (2*q)
  exact fun h => spacing_prime_not_dvd_double_prime p q hp hq hp2 hpq
    ((hown.trans h).trans htarget)

/-- Distinct odd-prime blocks are exactly orthogonal for the actual spacing kernel. -/
theorem spacingLimitKernel_primePairs_orthogonal (p q : ℕ)
    (hp : p.Prime) (hq : q.Prime) (hp2 : 2<p) (hq2 : 2<q) (hpq : p≠q) (i j : Bool) :
    spacingLimitKernel (spacingPrimePairConductor p i) (spacingPrimePairConductor q j)=0 := by
  have h12 := spacing_primePair_not_dvd p q hp hq hp2 hpq i j
  have h21 := spacing_primePair_not_dvd q p hq hp hq2 hpq.symm j i
  have hne : spacingPrimePairConductor p i≠spacingPrimePairConductor q j := by
    intro h
    apply h12
    simpa only [h] using dvd_refl (spacingPrimePairConductor q j)
  rw [spacingLimitKernel,weilPrimeKernel,if_neg (fun h => h12 h.1),
    if_neg (fun h => h21 h.1),if_neg hne,neg_zero,zero_add]

/-- The equal-coefficient vector has this exact prime-pair energy. -/
theorem spacingLimitKernel_primePair_sum (p : ℕ) (hp : p.Prime) (hp2 : 2<p) :
    spacingLimitKernel p p + spacingLimitKernel p (2*p) +
      spacingLimitKernel (2*p) p + spacingLimitKernel (2*p) (2*p) =
        2*tameDifferent p+Real.log 2-2*spacingPrimePairCoupling := by
  rw [spacingLimitKernel_self,spacingLimitKernel_prime_double p hp,
    spacingLimitKernel_comm (2*p) p,spacingLimitKernel_prime_double p hp,
    spacingLimitKernel_self,spacing_tameDifferent_double_prime p hp hp2]
  ring

/-- The fixed coupling beats the additional diagonal contribution at two. -/
theorem spacingPrimePair_gap_pos : 0 < 2*spacingPrimePairCoupling-Real.log 2 := by
  have hl : 0<Real.log 2 := Real.log_pos (by norm_num)
  have hs0 : 0<Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hs2 := Real.sq_sqrt (show (0:ℝ)≤2 by norm_num)
  have hs : Real.sqrt 2<2 := by nlinarith only [hs2,hs0]
  have hb := div_lt_div_of_pos_left hl hs0 hs
  unfold spacingPrimePairCoupling
  linarith only [hb]

/-- The small prime diagonal tends to zero, leaving a strict negative pair energy. -/
theorem eventually_spacingPrimePair_energy_neg :
    ∀ᶠ p : ℕ in atTop,
      2*(Real.log p/((p:ℝ)-1))+Real.log 2-2*spacingPrimePairCoupling<0 := by
  have hlim : Tendsto (fun p : ℕ => 2*(Real.log p/((p:ℝ)-1))) atTop (𝓝 0) := by
    have h := ((Real.tendsto_pow_log_div_mul_add_atTop 1 (-1) 1 one_ne_zero).comp
      tendsto_natCast_atTop_atTop).const_mul 2
    simpa only [Function.comp_apply,pow_one,one_mul,sub_eq_add_neg,mul_zero] using h
  filter_upwards [hlim.eventually (gt_mem_nhds spacingPrimePair_gap_pos)] with p hp
  linarith only [hp]

/-- Every prime conductor has strictly positive diagonal energy. -/
theorem spacingLimitKernel_prime_self_pos (p : ℕ) (hp : p.Prime) :
    0<spacingLimitKernel p p := by
  rw [spacingLimitKernel_self,spacing_tameDifferent_prime p hp]
  have hp1 : (1:ℝ)<p := by exact_mod_cast hp.one_lt
  exact div_pos (Real.log_pos hp1) (sub_pos.mpr hp1)

#print axioms spacingLimitKernel_primePair
#print axioms spacingLimitKernel_primePairs_orthogonal
#print axioms spacingLimitKernel_primePair_sum
#print axioms eventually_spacingPrimePair_energy_neg
#print axioms spacingLimitKernel_prime_self_pos
end GaloisForLFunctions.HeightHomotopyArithmeticCounts
