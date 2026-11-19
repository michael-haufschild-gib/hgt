import GaloisForLFunctions.ExclusionOfTheCriticalState.Wall.OddQuotientsInTheFractionalPrimeTest
import Mathlib.Data.ZMod.Basic

/-!
# The complete-period Gram matrix of odd quotients

The sign of the quotient is a character under translation by its denominator.
The affine character-support rule for translations, as in the abelian case of
Maktouf (arXiv:2610.40099), separates incompatible parity classes. For two
odd coprime reduced denominators the remaining correlation factors by CRT.
-/

open Finset
namespace GaloisForLFunctions.ExclusionOfTheCriticalState

noncomputable section
open scoped Classical

/-- The centered binary quotient digit with values +1 and -1. -/
def quotientSign (n H : ℕ) : ℝ := (-1) ^ (H / n)

private theorem sign_translate {n : ℕ} (hn : 0 < n) (H k : ℕ) :
    quotientSign n (H + n*k) = quotientSign n H * (-1)^k := by
  rw [quotientSign, Nat.add_mul_div_left _ _ hn, pow_add]
  rfl

private theorem sign_odd_product {a b : ℕ} (ha : a % 2 = 1) (hb : b % 2 = 1) (H : ℕ) :
    quotientSign a H * quotientSign b H = (-1 : ℝ)^(H % a) * (-1 : ℝ)^(H % b) := by
  have digit {n : ℕ} (hn : n % 2 = 1) :
      (H % n + H / n) % 2 = H % 2 := by
    have h := congrArg (fun t : ℕ => t % 2) (Nat.mod_add_div H n)
    change (H % n + n * (H / n)) % 2 = H % 2 at h
    rwa [Nat.add_mod, Nat.mul_mod, hn, one_mul, ← Nat.add_mod] at h
  have h₁ := digit ha
  have h₂ := digit hb
  unfold quotientSign
  rw [← pow_add, ← pow_add]
  calc
    _ = (-1 : ℝ)^((H/a + H/b)%2) := neg_one_pow_eq_pow_mod_two _
    _ = (-1 : ℝ)^((H%a + H%b)%2) := by congr 1; omega
    _ = _ := (neg_one_pow_eq_pow_mod_two _).symm

private theorem alternating_block (n : ℕ) :
    ∑ H ∈ range n, (-1 : ℝ)^H = if n % 2 = 1 then 1 else 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, ih, neg_one_pow_eq_pow_mod_two n]
    have hn := Nat.mod_lt n (by decide : 0 < 2)
    rcases (show n%2=0 ∨ n%2=1 by omega) with h|h <;>
      simp [h, show (n+1)%2 = 1 - n%2 by omega]

private theorem sum_zmod_val (n : ℕ) [NeZero n] (f : ℕ → ℝ) :
    ∑ x : ZMod n, f x.val = ∑ h ∈ range n, f h := by
  cases n with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ n => exact Fin.sum_univ_eq_sum_range f _

private theorem crt_product {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : a.Coprime b)
    (f g : ℕ → ℝ) :
    ∑ H ∈ range (a*b), f (H%a) * g (H%b) =
      (∑ h ∈ range a, f h) * ∑ h ∈ range b, g h := by
  letI : NeZero a := ⟨ha.ne'⟩
  letI : NeZero b := ⟨hb.ne'⟩
  let e := ZMod.chineseRemainder hc
  let F (p : ZMod a × ZMod b) := f p.1.val * g p.2.val
  have he (x : ZMod (a*b)) : F (e x) = f (x.val%a) * g (x.val%b) := by
    conv_lhs => rw [← ZMod.natCast_zmod_val x, map_natCast]
    simp only [F, Prod.fst_natCast, Prod.snd_natCast, ZMod.val_natCast]
  calc
    _ = ∑ x : ZMod (a*b), f (x.val%a) * g (x.val%b) :=
      (sum_zmod_val (a*b) _).symm
    _ = ∑ x : ZMod (a*b), F (e x) := sum_congr rfl fun x _ => (he x).symm
    _ = ∑ p : ZMod a × ZMod b, F p := e.toEquiv.sum_comp F
    _ = _ := by
      rw [Fintype.sum_prod_type]
      simp only [F, ← mul_sum, ← sum_mul, sum_zmod_val]

/-- Over twice the product of two coprime positive denominators, the
unnormalized correlation is two when both are odd and zero otherwise. -/
theorem coprime_quotientSign_gram {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : a.Coprime b) :
    ∑ H ∈ range (2*(a*b)), quotientSign a H * quotientSign b H =
      if a%2=1 ∧ b%2=1 then 2 else 0 := by
  let f (H : ℕ) := quotientSign a H * quotientSign b H
  have hshift (H : ℕ) : f (a*b+H) = f H * ((-1:ℝ)^a * (-1)^b) := by
    dsimp only [f]
    rw [Nat.add_comm (a*b), sign_translate ha, Nat.mul_comm a b, sign_translate hb]
    ring
  change ∑ H ∈ range _, f H = _
  rw [two_mul, sum_range_add, sum_congr rfl (fun H _ => hshift H), ← sum_mul]
  by_cases ho : a%2=1 ∧ b%2=1
  · obtain ⟨ha',hb'⟩ := ho
    rw [if_pos ⟨ha',hb'⟩]
    have hsum : ∑ H ∈ range (a*b), f H = 1 := by
      rw [sum_congr rfl (fun H _ => sign_odd_product ha' hb' H), crt_product ha hb hc,
        alternating_block, alternating_block, if_pos ha', if_pos hb', one_mul]
    rw [hsum, neg_one_pow_eq_pow_mod_two a, neg_one_pow_eq_pow_mod_two b, ha', hb']
    norm_num
  · rw [if_neg ho]
    have hne : ¬(a%2=0 ∧ b%2=0) := by
      rintro ⟨h₁,h₂⟩
      have hd := Nat.dvd_gcd (Nat.dvd_of_mod_eq_zero h₁) (Nat.dvd_of_mod_eq_zero h₂)
      rw [hc.gcd_eq_one] at hd
      omega
    have ha' := Nat.mod_lt a (by decide : 0 < 2)
    have hb' := Nat.mod_lt b (by decide : 0 < 2)
    rw [neg_one_pow_eq_pow_mod_two a, neg_one_pow_eq_pow_mod_two b]
    rcases (show (a%2=1 ∧ b%2=0) ∨ (a%2=0 ∧ b%2=1) by omega) with h|h <;>
      simp [h.1,h.2]

private theorem sum_repeated_blocks (f : ℕ → ℝ) (d k : ℕ) :
    ∑ H ∈ range (k*d), f (H/d) = d * ∑ j ∈ range k, f j := by
  by_cases hd : d=0
  · simp [hd]
  have hd' : 0<d := Nat.pos_of_ne_zero hd
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.succ_mul, sum_range_add, ih, sum_range_succ, mul_add]
    congr 1
    have he (H : ℕ) (hH : H ∈ range d) : f ((k*d + H)/d) = f k := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ hd', Nat.div_eq_of_lt (mem_range.mp hH), zero_add]
    rw [sum_congr rfl he, sum_const, card_range, nsmul_eq_mul]

/-- Complete correlation over the common period. Reducing by the gcd exposes
the only cross-correlations surviving the translation character. -/
theorem quotientSign_gram (n m : ℕ) :
    let d := n.gcd m
    ∑ H ∈ range (2 * n.lcm m), quotientSign n H * quotientSign m H =
      if (n/d)%2=1 ∧ (m/d)%2=1 then 2*(d : ℝ) else 0 := by
  dsimp only
  rcases n with _|n
  · simp
  rcases m with _|m
  · simp
  let d := (n+1).gcd (m+1)
  let a := (n+1)/d
  let b := (m+1)/d
  have hd : 0 < d := Nat.gcd_pos_of_pos_left _ (Nat.succ_pos n)
  have hn : d*a = n+1 := Nat.mul_div_cancel' (Nat.gcd_dvd_left _ _)
  have hm : d*b = m+1 := Nat.mul_div_cancel' (Nat.gcd_dvd_right _ _)
  have ha : 0 < a := by by_contra! h; rw [Nat.eq_zero_of_le_zero h, mul_zero] at hn; omega
  have hb : 0 < b := by by_contra! h; rw [Nat.eq_zero_of_le_zero h, mul_zero] at hm; omega
  have hc : a.Coprime b := Nat.coprime_div_gcd_div_gcd hd
  have hperiod : (n+1).lcm (m+1) = a*b*d := by
    apply Nat.eq_of_mul_eq_mul_left hd
    calc d * (n+1).lcm (m+1) = (n+1)*(m+1) := Nat.gcd_mul_lcm _ _
         _ = d * (a*b*d) := by rw [←hn,←hm]; ring
  have hval (H : ℕ) : quotientSign (n+1) H * quotientSign (m+1) H =
      quotientSign a (H/d) * quotientSign b (H/d) := by
    unfold quotientSign
    rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, hn, hm]
  change _ = if a%2=1 ∧ b%2=1 then 2*(d:ℝ) else 0
  rw [hperiod, ← Nat.mul_assoc, sum_congr rfl (fun H _ => hval H),
    sum_repeated_blocks (fun j => quotientSign a j * quotientSign b j),
    coprime_quotientSign_gram ha hb hc]
  split_ifs <;> ring

/-- Twice the centered discrepancy, with sign chosen to match quotientSign. -/
def centeredQuotientReading (S : Finset ℕ) (H : ℕ) : ℝ :=
  (∑ n ∈ S, ordinaryPrimeExcessCoeff n) - 2 * oddQuotientPrimeExcess S H

theorem centeredQuotientReading_eq (S : Finset ℕ) (H : ℕ) :
    centeredQuotientReading S H = ∑ n ∈ S, ordinaryPrimeExcessCoeff n * quotientSign n H := by
  rw [centeredQuotientReading, oddQuotientPrimeExcess, mul_sum, ← sum_sub_distrib]
  refine sum_congr rfl fun n _ => ?_
  unfold quotientSign
  rw [neg_one_pow_eq_pow_mod_two]
  have hb := Nat.mod_lt (H/n) (by decide : 0 < 2)
  rcases (show H/n%2=0 ∨ H/n%2=1 by omega) with h|h <;> simp [h] <;> ring

private theorem quotientSign_period (n : ℕ) : Function.Periodic (quotientSign n) (2*n) := by
  rcases n with _|n
  · simp only [Nat.mul_zero]; exact fun h => by rw [Nat.add_zero]
  · intro H
    rw [Nat.mul_comm 2, sign_translate (Nat.succ_pos n)]
    ring

private theorem pair_period (n m : ℕ) :
    Function.Periodic (fun H => quotientSign n H * quotientSign m H) (2*n.lcm m) := by
  have lift (a : ℕ) (ha : a ∣ n.lcm m) :
      Function.Periodic (quotientSign a) (2*n.lcm m) := by
    obtain ⟨j,hj⟩ := ha
    rw [hj, show 2*(a*j) = j*(2*a) by ring]
    exact (quotientSign_period a).nat_mul j
  exact (lift n (Nat.dvd_lcm_left ..)).mul (lift m (Nat.dvd_lcm_right ..))

/-- Signed kernel retained by one complete common period. -/
def quotientGramMass (n m : ℕ) : ℝ :=
  if (n/n.gcd m)%2=1 ∧ (m/n.gcd m)%2=1 then 2*(n.gcd m : ℝ) else 0

/-- Each denominator pair has its own terminal block. No simultaneous
completion to the lcm of all denominators is necessary. -/
theorem quotientSign_prefix_gram (n m X : ℕ) :
    let P := 2*n.lcm m
    ∑ H ∈ range X, quotientSign n H * quotientSign m H =
      ((X/P : ℕ) : ℝ) * quotientGramMass n m +
        ∑ H ∈ range (X%P), quotientSign n H * quotientSign m H := by
  let P := 2*n.lcm m
  let f (H : ℕ) := quotientSign n H * quotientSign m H
  have hp : Function.Periodic f P := pair_period n m
  have shift (k H : ℕ) : f (k*P+H) = f H := by
    rw [Nat.add_comm]; exact hp.nat_mul k H
  have block (k : ℕ) : ∑ H ∈ range (k*P), f H = k * quotientGramMass n m := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Nat.succ_mul, sum_range_add, ih, sum_congr rfl (fun H _ => shift k H),
        show ∑ H ∈ range P, f H = quotientGramMass n m from quotientSign_gram n m,
        Nat.cast_succ, add_mul, one_mul]
  change ∑ H ∈ range X, f H = ((X/P : ℕ) : ℝ) * quotientGramMass n m + ∑ H ∈ range (X%P), f H
  conv_lhs => rw [← Nat.div_add_mod X P, Nat.mul_comm P (X/P), sum_range_add]
  rw [block, sum_congr rfl (fun H _ => shift (X/P) H)]

/-- Exact common-numerator mixed moment for any two fixed prime bands.
All arithmetic signs survive in both the complete and terminal terms. -/
theorem centeredQuotientReading_prefix_product (S T : Finset ℕ) (X : ℕ) :
    ∑ H ∈ range X, centeredQuotientReading S H * centeredQuotientReading T H =
      ∑ n ∈ S, ∑ m ∈ T, ordinaryPrimeExcessCoeff n * ordinaryPrimeExcessCoeff m *
        (((X / (2*n.lcm m) : ℕ) : ℝ) * quotientGramMass n m +
          ∑ H ∈ range (X % (2*n.lcm m)), quotientSign n H * quotientSign m H) := by
  conv_lhs => simp_rw [centeredQuotientReading_eq, sum_mul, mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro n _
  rw [sum_comm]
  apply sum_congr rfl
  intro m _
  rw [← quotientSign_prefix_gram, mul_sum]
  exact sum_congr rfl fun H _ => by ring

#print axioms quotientSign_gram
#print axioms quotientSign_prefix_gram
#print axioms centeredQuotientReading_prefix_product
end
end GaloisForLFunctions.ExclusionOfTheCriticalState
