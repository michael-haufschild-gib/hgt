import GaloisForLFunctions.RestrictedFactorizationCalculus.ShortPrimeExchangesOfPositiveMass
import GaloisForLFunctions.QuantitativeFactorizationMatching.AllFiniteLayersCellMatching
import GaloisForLFunctions.RHTower.MobiusWholeAnchorGlobalTerminalCapacity
import GaloisForLFunctions.RHTower.MobiusDivisorSectionSignLaw

/-!
# Relative density of short exchanges in a complete period

The integers whose gcd with a prime-range modulus is a given paired
prime occupy a full totient fibre. Different primes give disjoint fibres.
The Euler product for a fixed ratio of logarithmic endpoints bounds the
coprime fraction uniformly, even as the available prime factors change.
-/

noncomputable section

open Finset Filter RHTower
open scoped Classical
open GaloisForLFunctions.QuantitativeFactorizationMatching

namespace GaloisForLFunctions.RestrictedFactorizationCalculus

/-- The squarefree modulus which records the complete local set of prime divisors. -/
def switchModulus (k : ℕ) := ∏ p ∈ switchPrimes k, p

theorem mem_switchPrimes {p k : ℕ} :
    p ∈ switchPrimes k ↔ p.Prime ∧ 2^k < p ∧ p ≤ (2^k)^24 := by
  change p ∈ windowPrimes ((2:ℝ)^k) (((2:ℝ)^k)^24) ↔ _
  rw [mem_windowPrimes (by positivity) (by positivity)]
  norm_cast

theorem switchModulus_spec (k : ℕ) : Squarefree (switchModulus k) ∧
    (switchModulus k).primeFactors=switchPrimes k ∧ 0 < switchModulus k :=
  squarefree_and_primeFactors_prod_primes (fun _ hp => (mem_switchPrimes.mp hp).1)

/-- Residues for which none of the specified complete local gcds occurs. -/
def missedResidues (m : ℕ) (P : Finset ℕ) :=
  (range m).filter (fun a => a.gcd m ∉ P)

private theorem card_gcd_fibre {m p : ℕ} (hp : 0 < p) (hm : p ∣ m) :
    ((range m).filter (fun a => a.gcd m=p)).card = (m/p).totient := by
  let b := m/p
  have he : b*p=m := Nat.div_mul_cancel hm
  have hset : (range m).filter (fun a => a.gcd m=p) =
      ((range b).filter (fun a => b.Coprime a)).image (· * p) := by
    ext n
    constructor
    · intro hn
      obtain ⟨hr,hg⟩ := mem_filter.mp hn
      have hd : p ∣ n := hg ▸ Nat.gcd_dvd_left n m
      let a := n/p
      have ha : a*p=n := Nat.div_mul_cancel hd
      have hlt : a*p < b*p := by rw [ha,he]; exact mem_range.mp hr
      have hg' : (a*p).gcd (b*p)=p := by rw [ha,he,hg]
      rw [Nat.gcd_mul_right] at hg'
      have hc : a.gcd b=1 := Nat.eq_of_mul_eq_mul_right hp (hg'.trans (one_mul p).symm)
      exact mem_image.mpr ⟨a,mem_filter.mpr ⟨mem_range.mpr ((Nat.mul_lt_mul_right hp).mp hlt),
        Nat.coprime_comm.mp hc⟩,ha⟩
    · intro hn
      obtain ⟨a,ha,rfl⟩ := mem_image.mp hn
      obtain ⟨hr,hc⟩ := mem_filter.mp ha
      rw [←he]
      exact mem_filter.mpr ⟨mem_range.mpr (Nat.mul_lt_mul_of_pos_right (mem_range.mp hr) hp),
        by rw [Nat.gcd_mul_right,hc.symm.gcd_eq_one,one_mul]⟩
  rw [hset,card_image_of_injOn (fun _ _ _ _ h => Nat.eq_of_mul_eq_mul_right hp h)]
  exact (Nat.totient_eq_card_coprime b).symm

/-- A uniform lower bound on the coprime fraction in every switching range. -/
private theorem coprime_fraction {k : ℕ} (hk : 1 ≤ k) :
    1/(24*mertensBandProductConst)^2 ≤ ((switchModulus k).totient:ℝ)/(switchModulus k) := by
  let Y := (2:ℕ)^k
  have hY : 2 ≤ Y := by
    change 2 ≤ (2:ℕ)^k
    simpa only [pow_one] using Nat.pow_le_pow_right (by decide : 0 < 2) hk
  have hYZ : Y ≤ Y^24 := by
    simpa only [pow_one] using Nat.pow_le_pow_right (by omega : 0 < Y) (by decide : 1 ≤ 24)
  have he : switchPrimes k=wholeAnchorBandPrimes Y (Y^24) := by
    ext p
    rw [mem_switchPrimes]
    change (_ ∧ _ ∧ _) ↔ p ∈ (Ioc Y (Y^24)).filter Nat.Prime
    rw [mem_filter,mem_Ioc]
    tauto
  let A := ∏ p ∈ switchPrimes k, (1+1/(p:ℝ))
  let V := ∏ p ∈ switchPrimes k, (1-1/(p:ℝ))
  have hK := mertensBandProductConst_pos
  have hupper : A ≤ 24*mertensBandProductConst := by
    have hh := bandPrimes_eulerProduct_le hY hYZ
    rw [←he,Nat.cast_pow,Real.log_pow] at hh
    have hl := Real.log_pos (by exact_mod_cast hY : (1:ℝ) < Y)
    convert hh using 1
    field_simp [hl.ne']
    ring
  have hv (p : ℕ) (hp : p ∈ switchPrimes k) :
      0 ≤ 1-1/(p:ℝ) ∧ 1 ≤ (1-1/(p:ℝ))*(1+1/(p:ℝ))^2 := by
    have h2 : (2:ℝ) ≤ p := by exact_mod_cast (mem_switchPrimes.mp hp).1.two_le
    have hp0 : (0:ℝ) < p := by linarith only [h2]
    have hhalf : 1/(p:ℝ) ≤ 1/2 := one_div_le_one_div_of_le (by norm_num) h2
    have hpos := (one_div_pos.mpr hp0).le
    have hs := mul_nonneg hpos (sub_nonneg.mpr hhalf)
    have hq := mul_nonneg (sq_nonneg (1/(p:ℝ))) (sub_nonneg.mpr hhalf)
    constructor <;> nlinarith only [hhalf,hpos,hs,hq]
  have ident : V*((A)^2) = ∏ p ∈ switchPrimes k, ((1-1/(p:ℝ))*(1+1/(p:ℝ))^2) := by
    dsimp only [V,A]; rw [←prod_pow,prod_mul_distrib]
  have hVA : 1 ≤ V*A^2 := by
    rw [ident]
    exact Finset.one_le_prod (fun p hp => (hv p hp).2)
  have hV : 0 ≤ V := prod_nonneg (fun p hp => (hv p hp).1)
  have hA : 0 ≤ A := prod_nonneg (fun p _ => by positivity)
  have hbound := hVA.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hA hupper 2) hV)
  obtain ⟨_,hpf,hm⟩ := switchModulus_spec k
  have hratio := prod_one_sub_inv_primeFactors_eq_totient_div hm.ne'
  rw [hpf] at hratio
  have hr : V=((switchModulus k).totient:ℝ)/(switchModulus k) := by
    simpa only [V,Nat.zero_add,pow_one,one_div] using hratio
  rw [←hr,div_le_iff₀ (by positivity : 0 < (24*mertensBandProductConst)^2)]
  exact hbound

/-- Uniform loss of residue density contributed by any subset of the paired
single primes. The divisor of each integer is its full gcd with the modulus. -/
theorem missedResidues_density {k : ℕ} (hk : 1 ≤ k) {P : Finset ℕ} (hP : P ⊆ switchPrimes k) :
    ((missedResidues (switchModulus k) P).card:ℝ)/(switchModulus k) ≤
      1-(1/(24*mertensBandProductConst)^2)*(∑ p ∈ P,1/(p:ℝ)) := by
  let M := switchModulus k
  obtain ⟨hsq,hpf,hm0⟩ := switchModulus_spec k
  have hm : (0:ℝ) < M := by exact_mod_cast hm0
  let family := fun p => (range M).filter (fun a => a.gcd M=p)
  let G := P.biUnion family
  have hg : G = (range M).filter (fun a => a.gcd M ∈ P) := by
    ext a
    simp only [G,family,mem_biUnion,mem_filter,mem_range]
    constructor
    · rintro ⟨p,hp,ha,he⟩; exact ⟨ha,he ▸ hp⟩
    · rintro ⟨ha,hp⟩; exact ⟨_,hp,ha,rfl⟩
  have hcard : G.card=∑ p ∈ P,(M/p).totient := by
    dsimp only [G]
    rw [card_biUnion]
    · refine sum_congr rfl fun p hp => card_gcd_fibre (mem_switchPrimes.mp (hP hp)).1.pos ?_
      exact Nat.dvd_of_mem_primeFactors (hpf ▸ hP hp)
    · intro p hp q hq hne
      exact disjoint_left.mpr (fun _ ha hb => hne ((mem_filter.mp ha).2.symm.trans (mem_filter.mp hb).2))
  have row (p : ℕ) (hp : p ∈ P) :
      ((M.totient:ℝ)/M)*(1/(p:ℝ)) ≤ ((M/p).totient:ℝ)/M := by
    have hpr := (mem_switchPrimes.mp (hP hp)).1
    have hd : p ∣ M := Nat.dvd_of_mem_primeFactors (hpf ▸ hP hp)
    have hc := Sieve.coprime_div_of_dvd_squarefree hsq hd
    have he : p*(M/p)=M := (Nat.mul_comm ..).trans (Nat.div_mul_cancel hd)
    have hphi := Nat.totient_mul hc
    rw [he,Nat.totient_prime hpr] at hphi
    have hpn : M.totient ≤ p*(M/p).totient := hphi.le.trans
      (Nat.mul_le_mul_right _ (Nat.sub_le _ _))
    have hp0 : (0:ℝ) < p := by exact_mod_cast hpr.pos
    rw [div_mul_div_comm,mul_one]
    apply (div_le_div_iff₀ (mul_pos hm hp0) hm).2
    have cast : (M.totient:ℝ) ≤ p*((M/p).totient:ℝ) := by exact_mod_cast hpn
    nlinarith only [mul_le_mul_of_nonneg_right cast hm.le]
  have hmass : ((M.totient:ℝ)/M)*(∑ p ∈ P,1/(p:ℝ)) ≤ (G.card:ℝ)/M := by
    rw [hcard,Nat.cast_sum,sum_div,mul_sum]
    exact sum_le_sum row
  have hsum : 0 ≤ ∑ p ∈ P, 1/(p:ℝ) := sum_nonneg fun _ _ => by positivity
  have hfrac := (mul_le_mul_of_nonneg_right (coprime_fraction hk) hsum).trans hmass
  have hn := card_filter_add_card_filter_not (s := range M) (fun a => a.gcd M ∈ P)
  rw [←hg,card_range] at hn
  change G.card+(missedResidues M P).card=M at hn
  have hreal : (G.card:ℝ)/M+((missedResidues M P).card:ℝ)/M=1 := by
    rw [←add_div,←Nat.cast_add,hn,div_self hm.ne']
  linarith only [hreal,hfrac]

end GaloisForLFunctions.RestrictedFactorizationCalculus
