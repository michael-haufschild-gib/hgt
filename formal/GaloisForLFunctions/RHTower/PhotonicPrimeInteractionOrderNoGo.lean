import GaloisForLFunctions.RHTower.PhotonicParabolicReturn
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Powerset
import Mathlib.NumberTheory.EulerProduct.Basic

/-!
# Unbounded prime-interaction order required by the PTR shifted return

The corpus's prime temporal-Maxwell cells realize parabolic first jets, while
its prime-occupation model realizes the Euler indexing of positive integers.
The PTR matrix return has coefficient `photonicParabolic ^ n` at integer `n`,
so its off-diagonal coefficient is `n`.  After removing the common unit-cell
shear, the coefficient is `n - 1`.

Independent local parabolic shears compose additively.  More generally, a
prime-clock source with a uniformly bounded interaction order `d` has a
Boolean cluster response whose coefficient at a packet `B` is a sum over
subpackets of size at most `d`.  The target integer weight instead has a
nonzero mixed interaction at every order.  This file proves that exact
classification and the resulting no-go.  It does not exclude an unbounded
cross-prime interaction or a non-cluster/nonlocal readout.
-/

open scoped BigOperators

namespace RHTower

private theorem ptr_powerset_sum_unique_on {α : Type*} [DecidableEq α]
    (S : Finset α) (c d : Finset α → ℂ)
    (h : ∀ B : Finset α, B ⊆ S →
      (∑ T ∈ B.powerset, c T) = ∑ T ∈ B.powerset, d T) :
    ∀ B : Finset α, B ⊆ S → c B = d B := by
  intro B
  refine Finset.strongInductionOn B ?_
  intro B ih hBS
  have hmem : B ∈ B.powerset := by simp
  have hproper : (∑ T ∈ B.powerset.erase B, c T) =
      ∑ T ∈ B.powerset.erase B, d T := by
    apply Finset.sum_congr rfl
    intro T hT
    have hsub : T ⊂ B :=
      Finset.ssubset_iff_subset_ne.mpr
        ⟨Finset.mem_powerset.mp (Finset.mem_erase.mp hT).2,
          (Finset.mem_erase.mp hT).1⟩
    exact ih T hsub ((le_of_lt hsub).trans hBS)
  have hc := Finset.sum_erase_add B.powerset c hmem
  have hd := Finset.sum_erase_add B.powerset d hmem
  have heq : (∑ T ∈ B.powerset.erase B, c T) + c B =
      (∑ T ∈ B.powerset.erase B, d T) + d B := by
    rw [hc, hd]
    exact h B hBS
  rw [hproper] at heq
  exact add_left_cancel heq

/-- **Exact positive survivor.** If a Boolean cluster response agrees with a
product on every subpacket, its top interaction is forced.  There is no
choice of lower interactions that can alter this coefficient. -/
theorem ptr_full_mixed_interaction {α : Type*} [DecidableEq α]
    (S : Finset α) (a : α → ℂ) (c : Finset α → ℂ)
    (h : ∀ B : Finset α, B ⊆ S →
      (∑ T ∈ B.powerset, c T) = ∏ i ∈ B, (1 + a i)) :
    c S = ∏ i ∈ S, a i := by
  apply ptr_powerset_sum_unique_on S c (fun T => ∏ i ∈ T, a i) ?_ S (by rfl)
  intro B hBS
  rw [h B hBS]
  exact Finset.prod_one_add B

/-- The exact interaction demanded at every prime packet is the product of
its nontrivial local increments `p - 1`.  In particular it is nonzero at
arbitrarily high orders, since prime packets have unbounded size. -/
theorem ptr_prime_packet_full_mixed_interaction (S : Finset Nat.Primes)
    (c : Finset Nat.Primes → ℂ)
    (h : ∀ B : Finset Nat.Primes, B ⊆ S →
      (∑ T ∈ B.powerset, c T) = ∏ p ∈ B, (((p : ℕ) : ℂ))) :
    c S = ∏ p ∈ S, ((((p : ℕ) : ℂ)) - 1) := by
  classical
  apply ptr_full_mixed_interaction S
    (fun p => ((((p : ℕ) : ℂ)) - 1)) c
  intro B hBS
  calc
    _ = ∏ p ∈ B, (((p : ℕ) : ℂ)) := h B hBS
    _ = ∏ p ∈ B, (1 + ((((p : ℕ) : ℂ)) - 1)) := by
      apply Finset.prod_congr rfl
      intro p _
      ring

/-- No interaction model of order strictly below the packet size can match
the multiplicative packet weight on every subpacket when all labels matter. -/
theorem ptr_finite_order_cluster_no_go {α : Type*} [DecidableEq α]
    (S : Finset α) (a : α → ℂ) (d : ℕ) (hcard : d < S.card)
    (ha : ∀ i ∈ S, a i ≠ 0) :
    ¬ ∃ c : Finset α → ℂ,
      ∀ B : Finset α, B ⊆ S →
        (∑ T ∈ B.powerset, if T.card ≤ d then c T else 0) =
          ∏ i ∈ B, (1 + a i) := by
  rintro ⟨c, hc⟩
  have hfull := ptr_full_mixed_interaction S a
    (fun T => if T.card ≤ d then c T else 0) hc
  have hzero : (if S.card ≤ d then c S else 0) = 0 :=
    if_neg (not_le.mpr hcard)
  rw [hzero] at hfull
  have hnonzero : (∏ i ∈ S, a i) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr ha
  exact hnonzero hfull.symm

/-- **All-order PTR source obstruction.** For every finite packet with more
than `d` distinct primes, no order-`d` cluster source matches the integer
weight even on all squarefree subpackets.  Hence an all-prime model needs
unbounded cross-prime interaction order to supply the shifted-zeta channel. -/
theorem ptr_prime_packet_finite_order_no_go (S : Finset Nat.Primes)
    (d : ℕ) (hcard : d < S.card) :
    ¬ ∃ c : Finset Nat.Primes → ℂ,
      ∀ B : Finset Nat.Primes, B ⊆ S →
        (∑ T ∈ B.powerset, if T.card ≤ d then c T else 0) =
          ∏ p ∈ B, (((p : ℕ) : ℂ)) := by
  classical
  intro h
  have ha : ∀ p ∈ S, (((p : ℕ) : ℂ) - 1) ≠ 0 := by
    intro p _ hzero
    have he : (((p : ℕ) : ℂ)) = 1 := sub_eq_zero.mp hzero
    have hnat : (p : ℕ) = 1 := by exact_mod_cast he
    have hp1 := p.property.one_lt
    omega
  apply ptr_finite_order_cluster_no_go S
    (fun p => (((p : ℕ) : ℂ)) - 1) d hcard ha
  obtain ⟨c, hc⟩ := h
  refine ⟨c, ?_⟩
  intro B hBS
  calc
    _ = ∏ p ∈ B, (((p : ℕ) : ℂ)) := hc B hBS
    _ = ∏ p ∈ B, (1 + ((((p : ℕ) : ℂ)) - 1)) := by
      apply Finset.prod_congr rfl
      intro p _
      ring

/-- The exact shifted return coefficient `n - 1`, not merely `n`, still
requires interactions of unbounded prime-packet order.  Adding the common
unit-cell shear only changes the empty cluster. -/
theorem ptr_prime_packet_shifted_finite_order_no_go (S : Finset Nat.Primes)
    (d : ℕ) (hcard : d < S.card) :
    ¬ ∃ c : Finset Nat.Primes → ℂ,
      ∀ B : Finset Nat.Primes, B ⊆ S →
        (∑ T ∈ B.powerset, if T.card ≤ d then c T else 0) =
          (∏ p ∈ B, (((p : ℕ) : ℂ))) - 1 := by
  classical
  rintro ⟨c, hc⟩
  apply ptr_prime_packet_finite_order_no_go S d hcard
  let c' : Finset Nat.Primes → ℂ := fun T => c T + if T = ∅ then 1 else 0
  refine ⟨c', ?_⟩
  intro B hBS
  have hterm (T : Finset Nat.Primes) :
      (if T.card ≤ d then c' T else 0) =
        (if T.card ≤ d then c T else 0) +
          (if T = ∅ then (1 : ℂ) else 0) := by
    by_cases hT : T = ∅
    · subst T
      simp [c']
    · by_cases hd : T.card ≤ d <;> simp [c', hT, hd]
  calc
    (∑ T ∈ B.powerset, if T.card ≤ d then c' T else 0) =
        (∑ T ∈ B.powerset,
          ((if T.card ≤ d then c T else 0) +
            (if T = ∅ then (1 : ℂ) else 0))) := by
              apply Finset.sum_congr rfl
              intro T _
              exact hterm T
    _ = (∑ T ∈ B.powerset, if T.card ≤ d then c T else 0) +
          (∑ T ∈ B.powerset, if T = ∅ then (1 : ℂ) else 0) :=
            Finset.sum_add_distrib
    _ = ((∏ p ∈ B, (((p : ℕ) : ℂ))) - 1) + 1 := by
      rw [hc B hBS]
      simp
    _ = ∏ p ∈ B, (((p : ℕ) : ℂ)) := by ring

/-- For the actual shifted return, the top mixed coefficient is unchanged:
only the empty cluster loses the common unit-cell contribution. -/
theorem ptr_prime_packet_shifted_full_mixed_interaction
    (S : Finset Nat.Primes) (hS : S.Nonempty)
    (c : Finset Nat.Primes → ℂ)
    (h : ∀ B : Finset Nat.Primes, B ⊆ S →
      (∑ T ∈ B.powerset, c T) =
        (∏ p ∈ B, (((p : ℕ) : ℂ))) - 1) :
    c S = ∏ p ∈ S, ((((p : ℕ) : ℂ)) - 1) := by
  classical
  let c' : Finset Nat.Primes → ℂ := fun T => c T + if T = ∅ then 1 else 0
  have hc' : ∀ B : Finset Nat.Primes, B ⊆ S →
      (∑ T ∈ B.powerset, c' T) = ∏ p ∈ B, (((p : ℕ) : ℂ)) := by
    intro B hBS
    simp [c', Finset.sum_add_distrib, h B hBS]
  have htop := ptr_prime_packet_full_mixed_interaction S c' hc'
  simpa [c', hS.ne_empty] using htop

/-- Even after factoring out the unit-cell shear, the PTR coefficient family
is not coprime-multiplicative.  An independent prime-jet product cannot be
the coefficient family in `photonicReturn_hasSum`. -/
theorem ptr_coprime_factorized_parabolic_return_no_go :
    ¬ ∃ F : ℕ → Matrix (Fin 2) (Fin 2) ℂ,
      (∀ m n : ℕ, m.Coprime n → F (m * n) = F m * F n) ∧
      (∀ n : ℕ, 1 ≤ n → F n = photonicParabolic ^ (n - 1)) := by
  rintro ⟨F, hmul, htarget⟩
  have h23 := hmul 2 3 (by norm_num)
  have h6 : F 6 = F 2 * F 3 := by simpa using h23
  rw [htarget 6 (by norm_num), htarget 2 (by norm_num),
    htarget 3 (by norm_num)] at h6
  simp only [Nat.reduceSub, photonicParabolic_pow, photonicUpper_mul] at h6
  have hentry := congrArg
    (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 1) h6
  norm_num [photonicUpper] at hentry

end RHTower
