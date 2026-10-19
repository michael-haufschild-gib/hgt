import GaloisForLFunctions.BiScaleUncertainty.SieveRawMomentPerturbation
import GaloisForLFunctions.BiScaleUncertainty.SieveCanonicalTranslation
import Mathlib.Data.Nat.Log

/-! Highest admitted dyadic order, its actual half-period action, and noisy quintic products. -/

open scoped BigOperators
open Finset
noncomputable section
namespace GaloisForLFunctions.BiScaleUncertainty.SieveMoments.TopAnchor
open ValuationPhase
set_option autoImplicit false

/-- The only admitted mode at the greatest possible two-adic depth. -/
def topOrder (N : ℕ) : ℕ := 2 ^ Nat.log 2 N

theorem topOrder_mem (N : ℕ) (hN : 2 ≤ N) : topOrder N ∈ Icc 1 N := by
  apply mem_Icc.mpr
  constructor
  · change 1 ≤ 2 ^ Nat.log 2 N
    have hh : 0 < 2 ^ Nat.log 2 N := by positivity
    exact hh
  · exact Nat.pow_log_le_self 2 (by omega)

theorem topOrder_depth (N : ℕ) : (topOrder N).factorization 2 = Nat.log 2 N := by
  exact Nat.factorization_pow_self Nat.prime_two

private theorem depth_le_log {N q : ℕ} (hq : q ∈ Icc 1 N) :
    q.factorization 2 ≤ Nat.log 2 N := by
  obtain ⟨p, hp⟩ := order_odd_decomposition (mem_Icc.mp hq).1
  have hpow : 2 ^ (q.factorization 2) ≤ q := by
    have hh : 1 ≤ 2*p+1 := by omega
    have hm := Nat.mul_le_mul_left (2 ^ (q.factorization 2)) hh
    simpa only [Nat.mul_one, ← hp] using hm
  exact Nat.le_log_of_pow_le (by decide) (hpow.trans (mem_Icc.mp hq).2)

/-- All other admitted modes lie strictly below the top dyadic order. -/
theorem depth_lt_top {N q : ℕ} (hq : q ∈ Icc 1 N) (hne : q ≠ topOrder N) :
    q.factorization 2 < Nat.log 2 N := by
  have hle := depth_le_log hq
  have hnot : q.factorization 2 ≠ Nat.log 2 N := by
    intro he
    obtain ⟨p, hp⟩ := order_odd_decomposition (mem_Icc.mp hq).1
    rw [he] at hp
    change q = topOrder N * (2*p+1) at hp
    have hNlt : N < topOrder N * 2 := by
      simpa only [Nat.succ_eq_add_one, pow_succ, topOrder] using
        Nat.lt_pow_succ_log_self (by decide : 1 < 2) N
    by_cases hp0 : p = 0
    · exact hne (by simpa only [hp0, Nat.mul_zero, Nat.zero_add, Nat.mul_one] using hp)
    · have hp1 : 1 ≤ p := by omega
      have hm := Nat.mul_le_mul_left (topOrder N) (by omega : 3 ≤ 2*p+1)
      have hqN := (mem_Icc.mp hq).2
      have htop : 0 < topOrder N := by unfold topOrder; positivity
      nlinarith
  omega

private theorem log_pos (N : ℕ) (hN : 2 ≤ N) : 0 < Nat.log 2 N := by
  have hh := Nat.le_log_of_pow_le (by decide : 1 < 2)
    (show 2^1 ≤ N by simpa only [pow_one] using hN)
  omega

/-- A nonzero top coordinate fixes the active depth even when other support changes. -/
theorem activeDepth_eq_top (N : ℕ) (hN : 2 ≤ N) (c : ℕ → ℝ)
    (hc : selbergMultiplesCoord N c (topOrder N) ≠ 0) :
    activeDepth N c = Nat.log 2 N := by
  apply le_antisymm
  · unfold activeDepth
    apply Finset.sup_le
    intro q hq
    exact depth_le_log (mem_filter.mp hq).1
  · simpa only [topOrder_depth] using
      depth_le_activeDepth N (topOrder N) c (topOrder_mem N hN) hc

/-- The actual canonical shift changes only the top coordinate on this stratum. -/
theorem coordinate_companion_top (N : ℕ) (hN : 2 ≤ N) (c : ℕ → ℝ)
    (hc : selbergMultiplesCoord N c (topOrder N) ≠ 0)
    (q : ℕ) (hq : q ∈ Icc 1 N) :
    selbergMultiplesCoord N (companion N c) q =
      if q = topOrder N then -selbergMultiplesCoord N c q else selbergMultiplesCoord N c q := by
  rw [coordinate_companion N c q hq, activeDepth_eq_top N hN c hc]
  have hpos := log_pos N hN
  by_cases he : q = topOrder N
  · simp only [he, topOrder_depth, hpos, and_self, if_true]
  · have hlt := depth_lt_top hq he
    simp only [he, if_false]
    rw [if_neg (by omega)]

/-- Raw fifth-array noise controls every lower-cube/upper-square product. -/
theorem lower_product_error (N : ℕ) (c e : ℕ → ℝ) (ε : ℝ)
    (h5 : ∀ v : Fin 5 → ℕ, |translatedMoment N c v-translatedMoment N e v| ≤ ε)
    {d u : ℕ} (hd : d ∈ Icc 1 N) (hu : u ∈ Icc 1 N)
    (hdu : d.factorization 2 < u.factorization 2) :
    |selbergMultiplesCoord N c d^3 * selbergMultiplesCoord N c u^2 -
      selbergMultiplesCoord N e d^3 * selbergMultiplesCoord N e u^2| ≤ ε := by
  obtain ⟨p, hp⟩ := order_odd_decomposition (mem_Icc.mp hd).1
  obtain ⟨q, hq⟩ := order_odd_decomposition (mem_Icc.mp hu).1
  let k := d.factorization 2
  let s := u.factorization 2-k-1
  have hk : k+(s+1) = u.factorization 2 := by dsimp [k, s]; omega
  have hlow : MixedValuation.lowerOrder k p = d := hp.symm
  have hupp : MixedValuation.upperOrder k s q = u := by
    unfold MixedValuation.upperOrder
    rw [hk]
    exact hq.symm
  let n := N-max d u
  have hcut : MixedValuation.cutoff n k s p q = N := by
    unfold MixedValuation.cutoff
    rw [hlow, hupp]
    dsimp [n]
    have := (mem_Icc.mp hd).2
    have := (mem_Icc.mp hu).2
    omega
  have hobs : ∀ v : Fin 5 → ℕ,
      |translatedMoment (MixedValuation.cutoff n k s p q) c v -
        translatedMoment (MixedValuation.cutoff n k s p q) e v| ≤ ε := by
    rw [hcut]
    exact h5
  have hh := resonant_product_error (MixedValuation.cutoff n k s p q) c e 5 ε hobs
    (MixedValuation.frequencies n k s p q) (MixedValuation.frequencies_sum n k s p q)
  have hprod (v : ℕ → ℝ) :
      (∏ i, v (addOrderOf (MixedValuation.frequencies n k s p q i))) =
        v (MixedValuation.lowerOrder k p)^3 * v (MixedValuation.upperOrder k s q)^2 := by
    have he := MixedValuation.frequencies_order_product n k s p q (fun j => (v j : ℂ))
    exact_mod_cast he
  rw [hprod, hprod, hcut, hlow, hupp] at hh
  exact hh

end GaloisForLFunctions.BiScaleUncertainty.SieveMoments.TopAnchor
