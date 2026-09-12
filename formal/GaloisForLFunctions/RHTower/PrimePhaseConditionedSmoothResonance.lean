import GaloisForLFunctions.HTGeometry.ArchimedeanCorank
import GaloisForLFunctions.HTGeometry.BohrMultiFejerMultiplier
import GaloisForLFunctions.RHTower.StieltjesLogWeldTierOne

open Filter Topology

namespace GaloisForLFunctions.RHTower

noncomputable section

open scoped BigOperators

/-- A natural-number frequency supported on conditioned primes survives the
multi-Fejer phase localization with its exact positive-frequency multiplier. -/
theorem bohrMean_expChar_neg_log_nat_mul_primeMultiFejerKernel
    (n : ℕ) (hn : n ≠ 0) (S : Finset Nat.Primes)
    (hS : ∀ p : Nat.Primes, n.factorization (p : ℕ) ≠ 0 → p ∈ S)
    (N : S → ℕ)
    (hN : ∀ p : S, n.factorization p.1.1 ≤ N p) :
    bohrMean (fun u =>
      expChar (-Real.log (n : ℝ)) u *
        multiFejerKernel
          (fun p : S => Real.log (p.1.1 : ℝ)) N u) =
      ((fejerMultiplier N
        (fun p : S => -(n.factorization p.1.1 : ℤ)) : ℝ) : ℂ) := by
  let beta : S → ℝ := fun p => Real.log (p.1.1 : ℝ)
  let m : S → ℤ := fun p => -(n.factorization p.1.1 : ℤ)
  have hind : LinearIndependent ℚ beta := by
    simpa only [beta] using primeLogFiniteSlice_linearIndependent S
  have hm : ∀ p : S, (m p).natAbs ≤ N p := by
    intro p
    simpa only [m, Int.natAbs_neg, Int.natAbs_natCast] using hN p
  have hlog := log_natCast_eq_sum_factorization n hn S hS
  have hlog' : Real.log (n : ℝ) =
      ∑ p : S, (n.factorization p.1.1 : ℝ) * Real.log (p.1.1 : ℝ) := by
    let f : Nat.Primes → ℝ := fun p =>
      (n.factorization p.1 : ℝ) * Real.log (p.1 : ℝ)
    have hsum : (∑ p ∈ S, f p) = ∑ p : S, f p.1 :=
      Finset.sum_subtype S (fun _ => Iff.rfl) f
    exact hlog.trans (by simpa only [f] using hsum)
  have hfreq : ∑ p : S, (m p : ℝ) * beta p = -Real.log (n : ℝ) := by
    rw [hlog', ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro p _
    simp only [m, beta, Int.cast_neg, Int.cast_natCast]
    ring
  simpa only [beta, m, hfreq] using
    (bohrMean_expChar_mul_multiFejerKernel hind N m hm)

/-- A supported natural frequency is never annihilated by the conditioned
prime Fejer kernel. -/
theorem fejerMultiplier_neg_factorization_pos
    (n : ℕ) (S : Finset Nat.Primes) (N : S → ℕ)
    (hN : ∀ p : S, n.factorization p.1.1 ≤ N p) :
    0 < fejerMultiplier N
      (fun p : S => -(n.factorization p.1.1 : ℤ)) := by
  rw [fejerMultiplier]
  apply Finset.prod_pos
  intro p _
  rw [sub_pos, div_lt_one (by positivity)]
  norm_num only [Int.natAbs_neg, Int.natAbs_natCast]
  exact_mod_cast Nat.lt_succ_of_le (hN p)

/-- Quantitative survival: the multiplier is at least the reciprocal product
of the Fejer orders. -/
theorem prod_inv_succ_le_fejerMultiplier_neg_factorization
    (n : ℕ) (S : Finset Nat.Primes) (N : S → ℕ)
    (hN : ∀ p : S, n.factorization p.1.1 ≤ N p) :
    (∏ p : S, (((N p : ℝ) + 1)⁻¹)) ≤
      fejerMultiplier N
        (fun p : S => -(n.factorization p.1.1 : ℤ)) := by
  rw [fejerMultiplier]
  apply Finset.prod_le_prod
  · intro p _
    positivity
  · intro p _
    norm_num only [Int.natAbs_neg, Int.natAbs_natCast]
    have hden : 0 < (N p : ℝ) + 1 := by positivity
    have hexp : (n.factorization p.1.1 : ℝ) ≤ N p := by
      exact_mod_cast hN p
    rw [inv_eq_one_div]
    apply (div_le_iff₀ hden).2
    field_simp [hden.ne']
    linarith

end

end GaloisForLFunctions.RHTower
