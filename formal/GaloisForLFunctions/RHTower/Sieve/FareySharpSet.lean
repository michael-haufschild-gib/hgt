import GaloisForLFunctions.RHTower.Sieve.FareySharp

/-!
# The sharp large sieve indexed by fractions

`largeSieve_farey_sharp` is indexed by the *values* of the proper Farey fractions.  Distinct reduced
fractions have distinct values — they are separated — so the sum may equally be indexed by the pairs
`(a,q)`, which is how a sieve application presents them.  Specialising the coefficients to the
indicator of a set of integers gives

`∑_{1 ≤ a < q ≤ Q, (a,q)=1} |∑_{n ∈ A} e(na/q)|² ≤ (Q² + 4πN) |A|`.
-/

namespace RHTower.Sieve

open Finset

/-- Distinct proper Farey fractions have distinct values. -/
theorem properFarey_val_injOn {Q : ℕ} (hQ : 0 < Q) :
    ∀ p ∈ properFareySet Q, ∀ r ∈ properFareySet Q,
      (p.1 : ℝ) / (p.2 : ℝ) = (r.1 : ℝ) / (r.2 : ℝ) → p = r := by
  intro p hp r hr hval
  by_contra hne
  have hps : p ∈ fareySet Q := (mem_properFareySet.mp hp).1
  have hrs : r ∈ fareySet Q := (mem_properFareySet.mp hr).1
  have hsep := fareySet_sep r hrs p hps (Ne.symm hne)
  rw [hval, sub_self] at hsep
  have hzero : toIntDist (0 : ℝ) = 0 := by
    rw [toIntDist]
    norm_num
  rw [hzero] at hsep
  have hQR : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast hQ
  have : (0 : ℝ) < 1 / (Q : ℝ) ^ (2 : ℕ) := by positivity
  linarith

/-- The sum over values equals the sum over fractions. -/
theorem sum_properFareyReals_eq {Q : ℕ} (hQ : 0 < Q) (f : ℝ → ℝ) :
    ∑ x ∈ properFareyReals Q, f x
      = ∑ p ∈ properFareySet Q, f ((p.1 : ℝ) / (p.2 : ℝ)) := by
  classical
  rw [properFareyReals, Finset.sum_image (properFarey_val_injOn hQ)]

/-- **The sharp large sieve for a set of integers, indexed by fractions.** -/
theorem largeSieve_set_properFarey (N : ℕ) (hN : 0 < N) {Q : ℕ} (hQ : 2 ≤ Q) (A : Finset ℕ)
    (hA : A ⊆ Finset.range N) :
    ∑ p ∈ properFareySet Q,
        ‖∑ n ∈ A, circleFreq ((n : ℝ) * ((p.1 : ℝ) / (p.2 : ℝ)))‖ ^ (2 : ℕ)
      ≤ ((Q : ℝ) ^ (2 : ℕ) + 4 * Real.pi * (N : ℝ)) * (A.card : ℝ) := by
  have hQ0 : 0 < Q := by omega
  have hbase := largeSieve_farey_sharp N hN hQ (indicatorVec N A)
  rw [sum_normSq_indicatorVec A hA] at hbase
  rw [sum_properFareyReals_eq hQ0 (fun x => ‖expSum N (indicatorVec N A) x‖ ^ (2 : ℕ))] at hbase
  simp only [expSum_indicatorVec A hA] at hbase
  exact hbase

end RHTower.Sieve
