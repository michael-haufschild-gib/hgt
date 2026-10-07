import GaloisForLFunctions.HTGeometry.ExponentialPolynomialVandermonde

/-!
# Bounded finite polar modes cannot grow exponentially

Distinct geometric nodes outside the unit disk cannot have a bounded polynomially weighted
sum unless every coefficient polynomial vanishes. The finite-difference induction retains
arbitrary polynomial degrees, hence arbitrary logarithmic orders of a finite pole packet.
It makes no separation assumption on the moduli of the nodes.

This is an analytic bridge for WP07. No representation of the actual cubic quotient's
boundary defect is asserted in this module.
-/

open Polynomial Filter Topology
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower.WeilHigherDenominator

private theorem polynomial_geometric_eq_zero_of_bounded_aux {ι : Type*} [DecidableEq ι]
    (z : ι → ℂ) (S : Finset ι) (hinj : Set.InjOn z ↑S) (hz : ∀ i ∈ S, 1 < ‖z i‖) :
    ∀ N : ℕ, ∀ p : ι → Polynomial ℂ, (∑ i ∈ S, polyWeight (p i)) ≤ N →
      (∃ B : ℝ, ∀ m : ℕ, 1 ≤ m → ‖∑ i ∈ S, (p i).eval (m : ℂ) * z i ^ m‖ ≤ B) →
      ∀ i ∈ S, p i = 0 := by
  have hz0 : ∀ i ∈ S, z i ≠ 0 := fun i hi => norm_pos_iff.mp (lt_trans zero_lt_one (hz i hi))
  intro N
  induction N with
  | zero =>
    intro p hsum _ i hi
    exact polyWeight_eq_zero_iff.mp
      (Finset.sum_eq_zero_iff.mp (Nat.le_zero.mp hsum) i hi)
  | succ N ih =>
    intro p hsum hbounded i hi
    by_cases hall : ∀ j ∈ S, p j = 0
    · exact hall i hi
    obtain ⟨a, ha, hpa⟩ : ∃ a ∈ S, p a ≠ 0 := by
      simpa only [not_forall, exists_prop] using hall
    let q : ι → Polynomial ℂ := fun j => vandermondeStep (p j) (z j) (z a)
    have hweight : (∑ j ∈ S, polyWeight (q j)) ≤ N := by
      have hsplit : (∑ j ∈ S, polyWeight (q j)) =
          polyWeight (q a) + ∑ j ∈ S.erase a, polyWeight (q j) :=
        (Finset.add_sum_erase S _ ha).symm
      have hsplit' : (∑ j ∈ S, polyWeight (p j)) =
          polyWeight (p a) + ∑ j ∈ S.erase a, polyWeight (p j) :=
        (Finset.add_sum_erase S _ ha).symm
      have hrest : ∑ j ∈ S.erase a, polyWeight (q j) = ∑ j ∈ S.erase a, polyWeight (p j) := by
        refine Finset.sum_congr rfl fun j hj => ?_
        obtain ⟨hja, hjS⟩ := Finset.mem_erase.mp hj
        exact polyWeight_vandermondeStep_of_ne
          (fun hzz => hja (hinj hjS ha hzz)) (hz0 j hjS)
      have hlt : polyWeight (q a) < polyWeight (p a) :=
        polyWeight_vandermondeStep_self_lt hpa (hz0 a ha)
      rw [hsplit, hrest]
      rw [hsplit'] at hsum
      omega
    obtain ⟨B, hB⟩ := hbounded
    have hqb : ∃ D : ℝ, ∀ m : ℕ, 1 ≤ m →
        ‖∑ j ∈ S, (q j).eval (m : ℂ) * z j ^ m‖ ≤ D := by
      refine ⟨B + ‖z a‖ * B, ?_⟩
      intro m hm
      have heq : ∑ j ∈ S, (q j).eval (m : ℂ) * z j ^ m =
          (∑ j ∈ S, (p j).eval ((m + 1 : ℕ) : ℂ) * z j ^ (m + 1)) -
            z a * ∑ j ∈ S, (p j).eval (m : ℂ) * z j ^ m := by
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [show q j = vandermondeStep (p j) (z j) (z a) from rfl, eval_vandermondeStep]
        push_cast
        ring
      rw [heq]
      exact (norm_sub_le _ _).trans (add_le_add (hB (m + 1) (by omega))
        (by rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hB m hm) (norm_nonneg _)))
    have hqzero := ih q hweight hqb
    have hpzero : ∀ j ∈ S, j ≠ a → p j = 0 := by
      intro j hj hja
      have hw := polyWeight_vandermondeStep_of_ne
        (fun hzz => hja (hinj hj ha hzz)) (hz0 j hj) (p := p j)
      change polyWeight (q j) = polyWeight (p j) at hw
      rw [hqzero j hj, polyWeight, if_pos rfl] at hw
      exact polyWeight_eq_zero_iff.mp hw.symm
    have hconst (n : ℕ) : (p a).eval ((n + 1 : ℕ) : ℂ) = (p a).eval 1 := by
      induction n with
      | zero => simp
      | succ n hn =>
        have he := congrArg (fun P : Polynomial ℂ => P.eval ((n + 1 : ℕ) : ℂ)) (hqzero a ha)
        change (vandermondeStep (p a) (z a) (z a)).eval _ = _ at he
        rw [eval_vandermondeStep, eval_zero] at he
        have hs : (p a).eval (((n + 1 : ℕ) : ℂ) + 1) = (p a).eval ((n + 1 : ℕ) : ℂ) := by
          apply (mul_right_cancel₀ (hz0 a ha))
          linear_combination he
        simpa only [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one] using hs.trans hn
    have honly (m : ℕ) : ∑ j ∈ S, (p j).eval (m : ℂ) * z j ^ m =
        (p a).eval (m : ℂ) * z a ^ m := by
      exact Finset.sum_eq_single_of_mem a ha fun j hj hja => by simp [hpzero j hj hja]
    have hc : (p a).eval 1 = 0 := by
      have hlim : Tendsto (fun m : ℕ => B / ‖z a‖ ^ m) atTop (𝓝 0) := by
        have hi : ‖z a‖⁻¹ < 1 := (inv_lt_one₀ (lt_trans zero_lt_one (hz a ha))).mpr (hz a ha)
        simpa only [div_eq_mul_inv, inv_pow, mul_zero] using
          (tendsto_pow_atTop_nhds_zero_of_lt_one (inv_nonneg.mpr (norm_nonneg (z a))) hi).const_mul B
      have hle : ‖(p a).eval 1‖ ≤ 0 := by
        apply le_of_tendsto_of_tendsto tendsto_const_nhds hlim
        filter_upwards [eventually_ge_atTop (1 : ℕ)] with m hm
        obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hm
        have hb := hB (1 + n) (by omega)
        rw [honly, norm_mul, norm_pow, Nat.add_comm 1 n, hconst] at hb
        apply (le_div_iff₀ (pow_pos (lt_trans zero_lt_one (hz a ha)) _)).mpr
        simpa only [Nat.add_comm] using hb
      exact norm_eq_zero.mp (le_antisymm hle (norm_nonneg _))
    have hpa0 : p a = 0 := by
      apply Polynomial.eq_zero_of_infinite_isRoot
      have hroots : Set.range (fun n : ℕ => ((n + 1 : ℕ) : ℂ)) ⊆ {x : ℂ | (p a).IsRoot x} := by
        rintro x ⟨n, rfl⟩
        exact (hconst n).trans hc
      apply Set.Infinite.mono hroots
      apply Set.infinite_range_of_injective
      intro n m h
      change ((n + 1 : ℕ) : ℂ) = ((m + 1 : ℕ) : ℂ) at h
      have hnm : n + 1 = m + 1 := by exact_mod_cast h
      omega
    by_cases hia : i = a
    · simpa [hia] using hpa0
    · exact hpzero i hi hia

/-- Every coefficient vanishes in a bounded polynomial-geometric sum whose distinct nodes
lie outside the unit disk. Equal moduli and arbitrary polynomial degrees are allowed. -/
theorem polynomial_geometric_eq_zero_of_bounded {ι : Type*} [DecidableEq ι]
    (z : ι → ℂ) (S : Finset ι) (hinj : Set.InjOn z ↑S) (hz : ∀ i ∈ S, 1 < ‖z i‖)
    (p : ι → Polynomial ℂ)
    (hbounded : ∃ B : ℝ, ∀ m : ℕ, 1 ≤ m →
      ‖∑ i ∈ S, (p i).eval (m : ℂ) * z i ^ m‖ ≤ B) :
    ∀ i ∈ S, p i = 0 :=
  polynomial_geometric_eq_zero_of_bounded_aux z S hinj hz
    (∑ i ∈ S, polyWeight (p i)) p le_rfl hbounded

end RHTower.WeilHigherDenominator
