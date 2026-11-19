import GaloisForLFunctions.RHTower.Sieve.CoprimeCounting
import GaloisForLFunctions.RHTower.Sieve.TotientMoebiusNormalisation

/-!
# The large prime dividing the midpoint modulus

If p divides n and p² > 4n, put a = n/p. All candidate cofactors are
below p. Both adjacent intervals of length a then carry a full period
of the coprime residues modulo a. A partial cut sees the two prefixes
of exactly the same period.
-/

noncomputable section
open Finset
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

private def residueCount (a t : ℕ) : ℝ :=
  (((Icc 1 t).filter (a.Coprime ·)).card : ℝ)

private theorem residueCount_mono (a : ℕ) : Monotone (residueCount a) := by
  intro s t hst
  apply Nat.cast_le.mpr
  apply card_le_card
  intro w hw
  obtain ⟨hi,hc⟩ := mem_filter.mp hw
  exact mem_filter.mpr ⟨mem_Icc.mpr ⟨(mem_Icc.mp hi).1,(mem_Icc.mp hi).2.trans hst⟩,hc⟩

private theorem residueCount_period {a : ℕ} (ha : 0 < a) : residueCount a a=a.totient := by
  rw [residueCount,_root_.RHTower.Sieve.coprimeCount_eq_sum_divisors ha,
    ←_root_.RHTower.Sieve.totient_eq_sum_moebius_mul a ha]

/-- Cumulative cofactor price with p allowed even if it divides n,
right minus left, through the closed cofactor endpoint K. -/
def unrestrictedPrimeCofactorCut (n p K : ℕ) : ℝ :=
  (((Ioc (max 1 (3*n/p)) (min K (4*n/p))).filter (n.Coprime ·)).card : ℝ) -
  (((Ioc (max 1 (2*n/p)) (min K (3*n/p))).filter (n.Coprime ·)).card : ℝ)

private theorem shifted_coprime_prefix {a p : ℕ} (hp : p.Prime) (hsep : 4*a < p)
    {j t : ℕ} (hj : j ≤ 3) (ht : t ≤ a) :
    (((Ioc (j*a) (j*a+t)).filter ((a*p).Coprime ·)).card : ℝ)=residueCount a t := by
  classical
  have hcop {w : ℕ} (hw : w ∈ Icc 1 t) : (a*p).Coprime (j*a+w) ↔ a.Coprime w := by
    obtain ⟨hw1,hwt⟩ := mem_Icc.mp hw
    have hj3 := Nat.mul_le_mul_right a hj
    have hv : j*a+w < p := by omega
    have hpv : p.Coprime (j*a+w) := hp.coprime_iff_not_dvd.mpr
      (fun hd => hv.not_ge (Nat.le_of_dvd (by omega) hd))
    rw [Nat.coprime_mul_iff_left,and_iff_left hpv,Nat.add_comm (j*a) w,Nat.coprime_add_mul_right_right]
  apply Nat.cast_inj.mpr
  apply card_nbij' (fun v => v-j*a) (fun w => j*a+w)
  · intro v hv
    obtain ⟨hi,hc⟩ := mem_filter.mp hv
    obtain ⟨hl,hu⟩ := mem_Ioc.mp hi
    have hw : v-j*a ∈ Icc 1 t := mem_Icc.mpr ⟨by omega,by omega⟩
    exact mem_filter.mpr ⟨hw,(hcop hw).mp (by rwa [show j*a+(v-j*a)=v by omega])⟩
  · intro w hw
    obtain ⟨hi,hc⟩ := mem_filter.mp hw
    obtain ⟨hl,hu⟩ := mem_Icc.mp hi
    exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨by omega,by omega⟩,(hcop hi).mpr hc⟩
  · intro v hv
    have := (mem_Ioc.mp (mem_filter.mp hv).1).1
    omega
  · intro w _; omega

private theorem truncated_period {a p : ℕ} (hp : p.Prime) (hsep : 4*a < p)
    (j K : ℕ) (hj : j ≤ 3) :
    (((Ioc (j*a) (min K ((j+1)*a))).filter ((a*p).Coprime ·)).card : ℝ) =
      residueCount a (min a (K-j*a)) := by
  have he : Ioc (j*a) (min K ((j+1)*a))=Ioc (j*a) (j*a+min a (K-j*a)) := by
    ext v
    simp only [mem_Ioc,Nat.add_mul,Nat.one_mul]
    omega
  rw [he]
  exact shifted_coprime_prefix hp hsep hj (min_le_left a (K-j*a))

/-- The exact partial price of a large divisor prime is a difference of
two truncated copies of the same primitive residue count. -/
theorem forbidden_prime_cofactor_cut {n p : ℕ} (hn : 0 < n) (hp : p.Prime)
    (hdiv : p ∣ n) (hlarge : 4*n < p^2) (K : ℕ) :
    let a := n/p
    unrestrictedPrimeCofactorCut n p K =
      residueCount a (min a (K-3*a))-residueCount a (min a (K-2*a)) := by
  let a := n/p
  have hmul : a*p=n := Nat.div_mul_cancel hdiv
  have ha : 0 < a := Nat.div_pos (Nat.le_of_dvd hn hdiv) hp.pos
  have hsep : 4*a < p := (Nat.mul_lt_mul_right hp.pos).mp (by
    rw [Nat.mul_assoc,hmul,←sq]; exact hlarge)
  have hq (j : ℕ) : j*n/p=j*a := Nat.mul_div_assoc j hdiv
  dsimp only
  change unrestrictedPrimeCofactorCut n p K=residueCount a _-residueCount a _
  simp only [unrestrictedPrimeCofactorCut,hq,max_eq_right (show 1 ≤ 2*a by omega),
    max_eq_right (show 1 ≤ 3*a by omega)]
  rw [←hmul]
  exact congrArg₂ (· - ·) (truncated_period hp hsep 3 K (by decide)) (truncated_period hp hsep 2 K (by decide))

/-- Every partial cut has nonpositive signed price. The middle cut
attains minus one totient and the last cut cancels the row exactly. -/
theorem forbidden_prime_cofactor_boundaries {n p : ℕ} (hn : 0 < n) (hp : p.Prime)
    (hdiv : p ∣ n) (hlarge : 4*n < p^2) :
    let a := n/p
    (∀ K : ℕ, -(a.totient:ℝ) ≤ unrestrictedPrimeCofactorCut n p K ∧
      unrestrictedPrimeCofactorCut n p K ≤ 0) ∧
    unrestrictedPrimeCofactorCut n p (3*a) = -(a.totient:ℝ) ∧
    unrestrictedPrimeCofactorCut n p (4*a) = 0 := by
  let a := n/p
  have ha : 0 < a := Nat.div_pos (Nat.le_of_dvd hn hdiv) hp.pos
  have hf (K : ℕ) := forbidden_prime_cofactor_cut hn hp hdiv hlarge K
  have hz : residueCount a 0=0 := by simp [residueCount]
  change (∀ K : ℕ, -(a.totient:ℝ) ≤ _ ∧ _ ≤ (0:ℝ)) ∧ _ ∧ _
  constructor
  · intro K
    rw [hf]
    change -(a.totient:ℝ) ≤ residueCount a _-residueCount a _ ∧ residueCount a _-residueCount a _ ≤ 0
    refine ⟨?_,sub_nonpos.mpr (residueCount_mono a (by omega))⟩
    have h1 := residueCount_mono a (min_le_left a (K-2*a))
    have h2 := residueCount_mono a (Nat.zero_le (min a (K-3*a)))
    rw [residueCount_period ha] at h1
    linarith only [h1,h2,hz]
  · rw [hf,hf]
    change residueCount a _-residueCount a _ = -(a.totient:ℝ) ∧ residueCount a _-residueCount a _ = 0
    simp only [Nat.sub_self,Nat.min_zero,show 3*a-2*a=a by omega,show 4*a-3*a=a by omega,min_self,
      min_eq_left (show a ≤ 4*a-2*a by omega),hz,residueCount_period ha,zero_sub,sub_self,and_self]

#print axioms forbidden_prime_cofactor_cut
#print axioms forbidden_prime_cofactor_boundaries

end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
