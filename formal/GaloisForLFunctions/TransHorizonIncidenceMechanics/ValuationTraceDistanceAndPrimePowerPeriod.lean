import GaloisForLFunctions.TransHorizonIncidenceMechanics.TotientObservabilityThresholdAndValuationFiberCollision
import Mathlib.InformationTheory.Hamming

/-!
# Exact finite-window distance between prime-power valuation traces

The prior totient observability theorem and its explicit collision pair determine
more than injectivity. Every complete prime-power period contributes at least two
disagreements, and the residual prefix contributes one exactly when it reaches the
totient threshold. The same collision pair attains this bound for every window.

This is the local component of the corrupted valuation-clock recovery programme.
It does not assert the global errors-and-erasures recovery theorem.
-/

set_option autoImplicit false
open Finset

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics
noncomputable section

/-- Number of unequal observations in two finite shifted GCD traces. -/
def valuationTraceDistance (L W k l : ℕ) : ℕ :=
  hammingDist (fun t : Fin W => Nat.gcd (k + t) L)
    (fun t : Fin W => Nat.gcd (l + t) L)

/-- Sharp prime-power disagreement floor: two per complete period, then the totient cutoff. -/
def primePowerTraceDistanceFloor (q W : ℕ) : ℕ :=
  2 * (W / q) + if q.totient ≤ W % q then 1 else 0

/-- The trace distance as a sum of disagreement indicators. -/
theorem valuationTraceDistance_eq_sum (L W k l : ℕ) :
    valuationTraceDistance L W k l =
      ∑ t ∈ range W, if Nat.gcd (k + t) L ≠ Nat.gcd (l + t) L then 1 else 0 := by
  rw [valuationTraceDistance, hammingDist, Finset.card_filter]
  exact Fin.sum_univ_eq_sum_range
    (fun t : ℕ => if Nat.gcd (k + t) L ≠ Nat.gcd (l + t) L then (1 : ℕ) else 0) W

private theorem periodic_sum (f : ℕ → ℕ) (q n r : ℕ)
    (hf : ∀ t, f (q + t) = f t) :
    (∑ t ∈ range (q * n + r), f t) =
      n * (∑ t ∈ range q, f t) + ∑ t ∈ range r, f t := by
  have hstep : ∀ m t, f (q * m + t) = f t := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      intro t
      calc
        f (q * (m + 1) + t) = f (q + (q * m + t)) := by congr 1; ring
        _ = f (q * m + t) := hf _
        _ = f t := ih t
  have hfull : ∀ m, (∑ t ∈ range (q * m), f t) = m * ∑ t ∈ range q, f t := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Nat.mul_succ, sum_range_add, ih, Nat.succ_mul]
      congr 1
      exact sum_congr rfl fun t _ => hstep m t
  rw [sum_range_add, hfull]
  congr 1
  exact sum_congr rfl fun t _ => hstep n t

private theorem gcd_period (L k t : ℕ) :
    Nat.gcd (k + (L + t)) L = Nat.gcd (k + t) L := by
  calc
    Nat.gcd (k + (L + t)) L = Nat.gcd ((k + t) + 1 * L) L := by congr 1; omega
    _ = Nat.gcd (k + t) L := Nat.gcd_add_mul_right_left L (k + t) 1

/-- Exact decomposition into complete modulus periods and a residual prefix. -/
theorem valuationTraceDistance_period_decomposition (L W k l : ℕ) :
    valuationTraceDistance L W k l =
      (W / L) * valuationTraceDistance L L k l +
        valuationTraceDistance L (W % L) k l := by
  simp only [valuationTraceDistance_eq_sum]
  have h := periodic_sum
    (fun t => if Nat.gcd (k + t) L ≠ Nat.gcd (l + t) L then 1 else 0)
    L (W / L) (W % L) (fun t => by rw [gcd_period, gcd_period])
  simpa only [Nat.div_add_mod] using h

private theorem modEq_of_joint_return {L k l t : ℕ}
    (hk : L ∣ k + t) (hl : L ∣ l + t) : Nat.ModEq L k l :=
  Nat.ModEq.add_right_cancel' t
    ((Nat.modEq_zero_iff_dvd.mpr hk).trans (Nat.modEq_zero_iff_dvd.mpr hl).symm)

private theorem gcd_ne_of_return {L k l t : ℕ}
    (hk : L ∣ k + t) (hne : ¬ Nat.ModEq L k l) :
    Nat.gcd (k + t) L ≠ Nat.gcd (l + t) L := by
  intro heq
  apply hne
  apply modEq_of_joint_return hk
  rw [Nat.gcd_eq_right hk] at heq
  rw [heq]
  exact Nat.gcd_dvd_left _ _

/-- Distinct phases disagree at both distinct modulus-divisibility return times. -/
theorem valuationTraceDistance_full_period_ge_two {L k l : ℕ}
    (hL : 0 < L) (hne : ¬ Nat.ModEq L k l) :
    2 ≤ valuationTraceDistance L L k l := by
  obtain ⟨tk, htk, hk⟩ := exists_divisibility_return L k hL
  obtain ⟨tl, htl, hl⟩ := exists_divisibility_return L l hL
  have hdiff : tk ≠ tl := by
    intro h
    subst tl
    exact hne (modEq_of_joint_return hk hl)
  have hkt := gcd_ne_of_return hk hne
  have hlt : Nat.gcd (k + tl) L ≠ Nat.gcd (l + tl) L :=
    (gcd_ne_of_return hl (fun h => hne h.symm)).symm
  rw [valuationTraceDistance_eq_sum, ← Finset.card_filter]
  calc
    2 = ({tk, tl} : Finset ℕ).card := by simp [hdiff]
    _ ≤ ((range L).filter (fun t => Nat.gcd (k + t) L ≠ Nat.gcd (l + t) L)).card := by
      apply card_le_card
      intro t ht
      rcases mem_insert.mp ht with rfl | ht
      · exact mem_filter.mpr ⟨mem_range.mpr htk, hkt⟩
      · have : t = tl := mem_singleton.mp ht
        subst t
        exact mem_filter.mpr ⟨mem_range.mpr htl, hlt⟩

/-- The existing totient observability threshold forces a disagreement in each long enough prefix. -/
theorem valuationTraceDistance_prime_pow_prefix_pos {p a k l W : ℕ}
    (hp : p.Prime) (hW : (p ^ a).totient ≤ W)
    (hne : ¬ Nat.ModEq (p ^ a) k l) :
    1 ≤ valuationTraceDistance (p ^ a) W k l := by
  apply Nat.one_le_iff_ne_zero.mpr
  intro hz
  have heq := eq_of_hammingDist_eq_zero hz
  apply hne
  apply modEq_prime_pow_of_gcd_eq_below_totient hp a k l
  intro t ht
  exact congrFun heq ⟨t, ht.trans_le hW⟩

/-- Every pair of distinct prime-power phases satisfies the sharp finite-window distance bound. -/
theorem valuationTraceDistance_prime_pow_lower {p a k l : ℕ}
    (hp : p.Prime) (hne : ¬ Nat.ModEq (p ^ a) k l) (W : ℕ) :
    primePowerTraceDistanceFloor (p ^ a) W ≤
      valuationTraceDistance (p ^ a) W k l := by
  have hfull := valuationTraceDistance_full_period_ge_two (pow_pos hp.pos a) hne
  have hrem : (if (p ^ a).totient ≤ W % (p ^ a) then 1 else 0) ≤
      valuationTraceDistance (p ^ a) (W % (p ^ a)) k l := by
    split_ifs with h
    · exact valuationTraceDistance_prime_pow_prefix_pos hp h hne
    · exact Nat.zero_le _
  rw [primePowerTraceDistanceFloor, valuationTraceDistance_period_decomposition]
  nlinarith [Nat.mul_le_mul_left (W / (p ^ a)) hfull]

private theorem prime_pair_disagrees_iff {p a t : ℕ} (hp : p.Prime) (ha : 1 ≤ a)
    (ht : t < p ^ a) :
    Nat.gcd (1 + t) (p ^ a) ≠ Nat.gcd (1 + p ^ (a - 1) + t) (p ^ a) ↔
      t = (p ^ a).totient - 1 ∨ t = p ^ a - 1 := by
  have hspos : 0 < p ^ (a - 1) := pow_pos hp.pos _
  have hslt : p ^ (a - 1) < p ^ a := Nat.pow_lt_pow_right hp.one_lt (by omega)
  have hsum := totient_prime_pow_add_pred p a hp ha
  have htot : 0 < (p ^ a).totient := by omega
  have hne := (gcd_prime_pow_collision_below_totient hp ha).1
  have hd1 : p ^ a ∣ 1 + t ↔ t = p ^ a - 1 := by
    constructor
    · intro h
      have hx := Nat.eq_of_dvd_of_lt_two_mul (by omega : 1 + t ≠ 0) h (by omega)
      omega
    · intro h
      have hx : 1 + t = p ^ a := by omega
      rw [hx]
  have hd2 : p ^ a ∣ 1 + p ^ (a - 1) + t ↔ t = (p ^ a).totient - 1 := by
    constructor
    · intro h
      have hx := Nat.eq_of_dvd_of_lt_two_mul
        (by omega : 1 + p ^ (a - 1) + t ≠ 0) h (by omega)
      omega
    · intro h
      have hx : 1 + p ^ (a - 1) + t = p ^ a := by omega
      rw [hx]
  have hdiv : Nat.gcd (1 + t) (p ^ a) ≠ Nat.gcd (1 + p ^ (a - 1) + t) (p ^ a) ↔
      p ^ a ∣ 1 + t ∨ p ^ a ∣ 1 + p ^ (a - 1) + t := by
    constructor
    · intro h
      by_contra hn
      push Not at hn
      apply h
      rw [gcd_prime_pow_eq_gcd_pred_of_not_dvd hp ha hn.1,
        gcd_prime_pow_eq_gcd_pred_of_not_dvd hp ha hn.2]
      have hx : 1 + p ^ (a - 1) + t = (1 + t) + 1 * p ^ (a - 1) := by ring
      rw [hx, Nat.gcd_add_mul_right_left]
    · rintro (h | h)
      · exact gcd_ne_of_return h hne
      · exact (gcd_ne_of_return h (fun hc => hne hc.symm)).symm
  rw [hdiv, hd1, hd2, or_comm]

private theorem prime_pair_prefix_distance {p a W : ℕ} (hp : p.Prime) (ha : 1 ≤ a)
    (hW : W ≤ p ^ a) :
    valuationTraceDistance (p ^ a) W 1 (1 + p ^ (a - 1)) =
      (if (p ^ a).totient ≤ W then 1 else 0) + (if p ^ a ≤ W then 1 else 0) := by
  have hspos : 0 < p ^ (a - 1) := pow_pos hp.pos _
  have hslt : p ^ (a - 1) < p ^ a := Nat.pow_lt_pow_right hp.one_lt (by omega)
  have hsum := totient_prime_pow_add_pred p a hp ha
  have htot : 0 < (p ^ a).totient := by omega
  have hneq : (p ^ a).totient - 1 ≠ p ^ a - 1 := by omega
  rw [valuationTraceDistance_eq_sum]
  calc
    (∑ t ∈ range W,
        if Nat.gcd (1 + t) (p ^ a) ≠ Nat.gcd (1 + p ^ (a - 1) + t) (p ^ a)
        then 1 else 0) =
        ∑ t ∈ range W,
          ((if t = (p ^ a).totient - 1 then (1 : ℕ) else 0) +
            (if t = p ^ a - 1 then 1 else 0)) := by
      apply sum_congr rfl
      intro t ht
      simp only [prime_pair_disagrees_iff hp ha ((mem_range.mp ht).trans_le hW)]
      by_cases hta : t = (p ^ a).totient - 1 <;>
        by_cases htb : t = p ^ a - 1 <;> simp_all
    _ = _ := by
      rw [sum_add_distrib, sum_ite_eq', sum_ite_eq']
      simp only [mem_range]
      have hphi : (p ^ a).totient - 1 < W ↔ (p ^ a).totient ≤ W := by omega
      have hq : p ^ a - 1 < W ↔ p ^ a ≤ W := by omega
      simp only [hphi, hq]

/-- The existing valuation-fiber collision pair attains the distance floor for every window. -/
theorem valuationTraceDistance_prime_pow_attainer {p a : ℕ}
    (hp : p.Prime) (ha : 1 ≤ a) (W : ℕ) :
    valuationTraceDistance (p ^ a) W 1 (1 + p ^ (a - 1)) =
      primePowerTraceDistanceFloor (p ^ a) W := by
  have hsum := totient_prime_pow_add_pred p a hp ha
  have hspos : 0 < p ^ (a - 1) := pow_pos hp.pos _
  have htot : (p ^ a).totient < p ^ a := by omega
  have hmod := Nat.mod_lt W (pow_pos hp.pos a)
  rw [valuationTraceDistance_period_decomposition,
    prime_pair_prefix_distance hp ha (le_refl _),
    prime_pair_prefix_distance hp ha hmod.le]
  simp [primePowerTraceDistanceFloor, htot.le, not_le.mpr hmod, Nat.mul_comm]

/-- Exact minimum finite-window distance between distinct prime-power valuation phases. -/
theorem valuationTraceDistance_prime_pow_minimum {p a : ℕ}
    (hp : p.Prime) (ha : 1 ≤ a) (W : ℕ) :
    (∀ k l, ¬ Nat.ModEq (p ^ a) k l →
      primePowerTraceDistanceFloor (p ^ a) W ≤ valuationTraceDistance (p ^ a) W k l) ∧
      ∃ k l, ¬ Nat.ModEq (p ^ a) k l ∧
        valuationTraceDistance (p ^ a) W k l = primePowerTraceDistanceFloor (p ^ a) W := by
  refine ⟨fun k l hne => valuationTraceDistance_prime_pow_lower hp hne W, ?_⟩
  exact ⟨1, 1 + p ^ (a - 1), (gcd_prime_pow_collision_below_totient hp ha).1,
    valuationTraceDistance_prime_pow_attainer hp ha W⟩

end
end GaloisForLFunctions.TransHorizonIncidenceMechanics
