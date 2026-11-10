import GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.GeometricPrefixCost
import GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.ResiduePrefixGaps

/-!
# Geometric prefix cost in an exponent residue

Quotient exponents by their common residue degree. Ordered digit-count gaps
become level gaps, so the finite double-geometric estimate bounds actual
base-`p` prefix values, including empty prefixes.
-/

open Finset
namespace GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss

/-- Positive prefix gaps accumulate up to a finite terminal prefix. -/
theorem card_gap_of_positive_prefixes_upto {α : Type*} [DecidableEq α]
    (A : ℕ → Finset α) (b K : ℕ)
    (hgap : ∀ i < K, (A i).Nonempty → (A i).card + b ≤ (A (i + 1)).card)
    {j : ℕ} (hj : (A j).Nonempty) :
    ∀ n, j + n ≤ K → (A j).card + n * b ≤ (A (j + n)).card := by
  intro n
  induction n with
  | zero => exact fun _ => by simp only [zero_mul, add_zero, le_refl]
  | succ n ih =>
    intro hn
    have hi := ih (by omega)
    have hne : (A (j + n)).Nonempty := by
      apply card_pos.mp
      have hpos := card_pos.mpr hj
      omega
    have hg := hgap (j + n) (by omega) hne
    rw [Nat.succ_mul]
    have he : j + (n + 1) = (j + n) + 1 := by omega
    rw [he]
    omega

/-- The arithmetic-geometric prefix estimate in one actual exponent residue. -/
theorem residue_prefix_weight_le_of_exponent_gap {p s : ℕ} (hp : 2 ≤ p) (hs : 0 < s)
    (m E : ℕ) (A : ℕ → Finset (Digit p))
    (hres : ∀ n ∈ Icc 1 m, ∀ x ∈ A n, x.1 % s = E % s)
    (hgap : ∀ n ∈ Icc 1 m, ∀ x ∈ A n, x.1 + n * s ≤ E) :
    ((p : ℤ) ^ s - 1) ^ 2 * (∑ n ∈ Icc 1 m, digitValue p (A n)) ≤
      ((p : ℤ) - 1) * (p : ℤ) ^ s * (p : ℤ) ^ E := by
  let f : Digit p → Digit p := fun x => (x.1 / s, x.2)
  let B := fun n => (A n).image f
  have hinj (n : ℕ) (hn : n ∈ Icc 1 m) : Set.InjOn f (↑(A n) : Set (Digit p)) := by
    intro x hx y hy he
    change (x.1 / s, x.2) = (y.1 / s, y.2) at he
    obtain ⟨hq, hl⟩ := Prod.mk.inj he
    apply Prod.ext _ hl
    have hxid := Nat.mod_add_div x.1 s
    have hyid := Nat.mod_add_div y.1 s
    rw [hres n hn x hx, hq] at hxid
    rw [hres n hn y hy] at hyid
    omega
  have hg : ∀ n ∈ Icc 1 m, ∀ z ∈ B n, z.1 + n ≤ E / s := by
    intro n hn z hz
    obtain ⟨x, hx, rfl⟩ := mem_image.mp hz
    have h := hgap n hn x hx
    have hxid := Nat.mod_add_div x.1 s
    have hEid := Nat.mod_add_div E s
    rw [hres n hn x hx] at hxid
    change x.1 / s + n ≤ E / s
    nlinarith only [h, hxid, hEid, hs]
  have hpow (x : Digit p) (n : ℕ) (hn : n ∈ Icc 1 m) (hx : x ∈ A n) :
      (p : ℤ) ^ x.1 = (p : ℤ) ^ (E % s) * ((p : ℤ) ^ s) ^ (f x).1 := by
    change (p : ℤ) ^ x.1 = (p : ℤ) ^ (E % s) * ((p : ℤ) ^ s) ^ (x.1 / s)
    rw [← pow_mul, ← pow_add, ← hres n hn x hx, Nat.mod_add_div]
  have he (n : ℕ) (hn : n ∈ Icc 1 m) :
      digitValue p (A n) = (p : ℤ) ^ (E % s) * ∑ z ∈ B n, ((p : ℤ) ^ s) ^ z.1 := by
    rw [show B n = (A n).image f from rfl, sum_image (hinj n hn), mul_sum]
    exact sum_congr rfl fun x hx => hpow x n hn hx
  have hp1 : (1 : ℤ) ≤ p := by omega
  have hg' := prefix_weight_le_of_exponent_gap (q := (p : ℤ) ^ s)
    (one_le_pow₀ hp1) (p - 1) m (E / s) B hg
  have hm := mul_le_mul_of_nonneg_left hg' (pow_nonneg (by omega : (0 : ℤ) ≤ p) (E % s))
  have hsume : (∑ n ∈ Icc 1 m, digitValue p (A n)) =
      (p : ℤ) ^ (E % s) * (∑ n ∈ Icc 1 m, ∑ z ∈ B n, ((p : ℤ) ^ s) ^ z.1) := by
    rw [mul_sum]
    exact sum_congr rfl he
  have hfactor : (p : ℤ) ^ (E % s) * ((p : ℤ) ^ s) ^ (E / s) = (p : ℤ) ^ E := by
    rw [← pow_mul, ← pow_add, Nat.mod_add_div]
  rw [hsume]
  rw [pow_succ ((p : ℤ) ^ s) (E / s), Nat.cast_sub (by omega : 1 ≤ p), Nat.cast_one] at hm
  calc
    _ = (p : ℤ) ^ (E % s) *
        (((p : ℤ) ^ s - 1) ^ 2 * ∑ n ∈ Icc 1 m, ∑ z ∈ B n, ((p : ℤ) ^ s) ^ z.1) := by ring
    _ ≤ (p : ℤ) ^ (E % s) * ((p - 1) *
        (((p : ℤ) ^ s) ^ (E / s) * (p : ℤ) ^ s)) := hm
    _ = _ := by rw [← hfactor]; ring

/-- Ordered residue prefixes with `n(p−1)` missing digits satisfy the sharp
finite geometric cost bound below their terminal maximum. -/
theorem residue_prefix_weight_le_of_card_gap {p s r : ℕ} (hp : 2 ≤ p) (hs : 0 < s)
    (m E : ℕ) (A : ℕ → Finset (Digit p)) (B : Finset (Digit p))
    (hres : ∀ z ∈ B, z.1 % s = r) (hEres : E % s = r)
    (hmax : ∀ z ∈ B, z.1 ≤ E)
    (hsub : ∀ n ∈ Icc 1 m, A n ⊆ B)
    (hsmall : ∀ n ∈ Icc 1 m, ∀ x ∈ A n, ∀ y ∈ B \ A n, x.1 ≤ y.1)
    (hcard : ∀ n ∈ Icc 1 m, (A n).Nonempty → (A n).card + n * (p - 1) ≤ B.card) :
    ((p : ℤ) ^ s - 1) ^ 2 * (∑ n ∈ Icc 1 m, digitValue p (A n)) ≤
      ((p : ℤ) - 1) * (p : ℤ) ^ s * (p : ℤ) ^ E := by
  apply residue_prefix_weight_le_of_exponent_gap hp hs
  · exact fun n hn x hx => (hres x (hsub n hn hx)).trans hEres.symm
  · exact fun n hn x hx => exponent_gap_of_prefix_card_gap (hsub n hn)
      hres hEres hmax (hsmall n hn) (hcard n hn ⟨x, hx⟩) hx

end GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss

#print axioms GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.residue_prefix_weight_le_of_card_gap
