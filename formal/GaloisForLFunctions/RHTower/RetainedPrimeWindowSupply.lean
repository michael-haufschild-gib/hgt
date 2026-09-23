import GaloisForLFunctions.RHTower.RetainedPrimeDescentOrders
import GaloisForLFunctions.RHTower.MobiusDivisorCoupledTwoPrimeBatches

/-!
# Actual prime windows for arbitrary finite source witnesses

A common multiple of the child cutoffs synchronizes all witness windows at
one parent cutoff. Every copied prime has the prescribed quotient and an
explicit clipping bound. The unconditional prime-window supply theorem
makes every fixed window capacity grow beyond any finite demand.
-/

noncomputable section
open Finset Filter Topology
namespace RHTower

/-- Every nontrivial child cutoff has an explicit uniform macroscopic-window clipping bound. -/
theorem divisorPrimeClipWeight_general_quotient_window {K b N p : ℕ}
    (hK : 1≤K) (hb : K≤b)
    (hlo : b*N<p) (hhi : p≤(b+1)*N) :
    (b:ℝ)*divisorPrimeClipWeight (K*(b+1)*N) p≤2*(K:ℝ)*(K+1) := by
  have hp : 0<p := by omega
  have hN : 0<N := by nlinarith
  have hquot := natDiv_fixed_quotient_window hb hlo hhi
  have hw := divisorPrimeClipWeight_nonneg (K*(b+1)*N) p hp
  have hstep := divisorPrimeClipWeight_mul_step (K*(b+1)*N) p hp
  rw [hquot] at hstep
  have hgap : 1 ≤ (2*((K:ℝ)+1))*(Real.sqrt (K+1:ℕ)-Real.sqrt K) := by
    push_cast
    have ha := Real.sq_sqrt (show 0≤(K:ℝ)+1 by positivity)
    have hb' := Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) K)
    have hkr : (1:ℝ)≤K := by exact_mod_cast hK
    have hdiff : 0≤Real.sqrt ((K:ℝ)+1)-Real.sqrt K :=
      sub_nonneg.mpr (Real.sqrt_le_sqrt (by linarith))
    have hs0 : Real.sqrt ((K:ℝ)+1) ≤ (K:ℝ)+1 := by
      apply Real.sqrt_le_iff.mpr
      constructor <;> nlinarith
    have hs1 : Real.sqrt (K:ℝ) ≤ (K:ℝ)+1 := by
      apply Real.sqrt_le_iff.mpr
      constructor <;> nlinarith
    have hsum : Real.sqrt ((K:ℝ)+1)+Real.sqrt K≤2*((K:ℝ)+1) := by linarith
    have hm := mul_nonneg (sub_nonneg.mpr hsum) hdiff
    nlinarith only [ha,hb',hm]
  have hroot : Real.sqrt (p:ℝ)≤Real.sqrt (p*K:ℕ) := by
    apply Real.sqrt_le_sqrt
    exact_mod_cast (show p≤p*K by simpa using Nat.mul_le_mul_left p hK)
  have hdiff : 0≤Real.sqrt (K*(b+1)*N:ℕ)-Real.sqrt (p*K:ℕ) := by
    apply sub_nonneg.mpr
    apply Real.sqrt_le_sqrt
    exact_mod_cast (show p*K≤K*(b+1)*N by
      have h := Nat.mul_le_mul_left K hhi; nlinarith only [h])
  have hsM := Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) (K*(b+1)*N))
  have hsK := Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) (p*K))
  have hsp := Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) p)
  have hmul := mul_le_mul_of_nonneg_left
    (show Real.sqrt p≤Real.sqrt (K*(b+1)*N:ℕ)+Real.sqrt (p*K:ℕ) by
      linarith only [hroot,Real.sqrt_nonneg ((K*(b+1)*N:ℕ):ℝ)]) hdiff
  have hNat : ((K*(b+1)*N:ℕ):ℝ)≤(p*K:ℕ)+(K:ℝ)*N := by
    exact_mod_cast (show K*(b+1)*N≤p*K+K*N by
      have h := Nat.mul_le_mul_left K hlo.le; nlinarith only [h])
  have hbound : (Real.sqrt (K*(b+1)*N:ℕ)-Real.sqrt (p*K:ℕ))*Real.sqrt p≤(K:ℝ)*N := by
    nlinarith only [hmul,hsM,hsK,hNat]
  have he := congrArg (fun x : ℝ => x*Real.sqrt p) hstep
  have he' : divisorPrimeClipWeight (K*(b+1)*N) p*(p:ℝ)*
      (Real.sqrt (K+1:ℕ)-Real.sqrt K)≤(K:ℝ)*N := by
    calc
      _ = divisorPrimeClipWeight (K*(b+1)*N) p*(Real.sqrt p)^(2 : ℕ)*
          (Real.sqrt (K+1:ℕ)-Real.sqrt K) := by rw [hsp]
      _ = divisorPrimeClipWeight (K*(b+1)*N) p*Real.sqrt p*
          (Real.sqrt (K+1:ℕ)-Real.sqrt K)*Real.sqrt p := by ring
      _ = _ := he
      _ ≤ _ := hbound
  have hgapmul := mul_le_mul_of_nonneg_left hgap
    (mul_nonneg hw (Nat.cast_nonneg (α := ℝ) p))
  have hscaled := mul_le_mul_of_nonneg_left he' (show 0 ≤ 2*((K:ℝ)+1) by positivity)
  have hbn : (b:ℝ)*N≤p := by exact_mod_cast hlo.le
  have hbmul := mul_le_mul_of_nonneg_left hbn hw
  have hNr : (0:ℝ)<N := by exact_mod_cast hN
  nlinarith only [hscaled,hgapmul,hbmul,hNr]

/-- A common-multiple parent window copying one prescribed integer child cutoff. -/
def retainedPrimeWitnessWindow (A b N k : ℕ) : Finset ℕ :=
  GaloisForLFunctions.HTGeometry.primesInIoc (b*((A/k)*N)) ((b+1)*((A/k)*N))

/-- Every prime in a witness window has the required exact quotient and clipping estimate. -/
theorem retainedPrimeWitnessWindow_data {A b N k p : ℕ}
    (hk : 2 ≤ k) (hkb : k ≤ b) (hA : 0 < A) (hkA : k ∣ A) (_hN : 1 ≤ N)
    (hp : p ∈ retainedPrimeWitnessWindow A b N k) :
    p.Prime ∧ p < A*(b+1)*N ∧ b < p ∧ (A*(b+1)*N)/p = k ∧
      (b:ℝ)*divisorPrimeClipWeight (A*(b+1)*N) p ≤ 2*(k:ℝ)*(k+1) := by
  obtain ⟨hpp, hlo, hhi⟩ := GaloisForLFunctions.HTGeometry.mem_primesInIoc hp
  have heA : k*(A/k)=A := Nat.mul_div_cancel' hkA
  have hdiv : 1 ≤ A/k := by nlinarith
  have he : k*(b+1)*((A/k)*N)=A*(b+1)*N := by
    calc
      _ = (k*(A/k))*((b+1)*N) := by ring
      _ = _ := by rw [heA]; ring
  have hquot := natDiv_fixed_quotient_window hkb hlo hhi
  have hw := divisorPrimeClipWeight_general_quotient_window (by omega : 1≤k) hkb hlo hhi
  rw [he] at hquot hw
  refine ⟨hpp, ?_, ?_, hquot, hw⟩
  · have hpM : k*p ≤ A*(b+1)*N := by nlinarith [hhi, he]
    nlinarith [hpp.pos]
  · nlinarith

/-- Each fixed witness window eventually contains any prescribed finite number of actual primes. -/
theorem eventually_retainedPrimeWitnessWindow_card_ge {A b k : ℕ}
    (hA : 0 < A) (hkA : k ∣ A) (hb : 1 ≤ b) (n : ℕ) :
    ∀ᶠ N : ℕ in atTop, n ≤ (retainedPrimeWitnessWindow A b N k).card := by
  have heA : k*(A/k)=A := Nat.mul_div_cancel' hkA
  have hdiv : 0 < A/k := by nlinarith
  have ht : Tendsto (fun N : ℕ => (A/k)*N) atTop atTop :=
    Filter.Tendsto.const_mul_atTop' hdiv tendsto_id
  exact ht.eventually (eventually_fixed_prime_window_card_ge b n hb)

end RHTower
