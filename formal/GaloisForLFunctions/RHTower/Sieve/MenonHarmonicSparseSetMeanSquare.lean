import GaloisForLFunctions.RHTower.Sieve.GallagherAffineMeanSquare
import GaloisForLFunctions.RHTower.Sieve.MenonHarmonicRamareBlockSwapped

/-!
# The harmonic mean square of a sparse set, by cardinality alone

For a set `S` of integers confined to `[A, M]`, the harmonic Moebius polynomial over `S` has
frequency mean square controlled by nothing but `#S` and the lower endpoint `A`:

```text
∫_{[-T,T]} ‖∑_{n ∈ S} μ(n) n^{-1-2πiw}‖² dw
   ≤ (5π/2)·T·(#S/A²) + (5e/2)·(#S/A) + (5/4)·(#S/A²) .
```

Both energies are proportional to `#S`, so the bound is proportional to the *density* of `S` — which
is what makes it useful for the parts of Menon's shell that a sieve counts rather than a
factorisation estimates.
-/

namespace RHTower.Sieve

open Finset MeasureTheory
open scoped ArithmeticFunction.Moebius

noncomputable section

/-- The harmonic Moebius coefficients restricted to a set. -/
def harmonicMoebiusOn (S : Finset ℕ) (n : ℕ) : ℂ :=
  if n ∈ S then harmonicMoebiusC n else 0

theorem logPoly_harmonicMoebiusOn_eq {S : Finset ℕ} {N : ℕ}
    (hS : S ⊆ Finset.Icc 1 N) (w : ℝ) :
    logPoly (harmonicMoebiusOn S) (Finset.Icc 1 N) w = logPoly harmonicMoebiusC S w := by
  classical
  rw [logPoly, logPoly]
  rw [← Finset.sum_subset hS (fun n _ hn => by rw [harmonicMoebiusOn, if_neg hn, zero_mul])]
  exact Finset.sum_congr rfl fun n hn => by rw [harmonicMoebiusOn, if_pos hn]

/-- A weighted energy over `Fin N` of a set-restricted coefficient family is at most the
cardinality times the weight bound. -/
theorem sum_weight_normSq_harmonicMoebiusOn_le {S : Finset ℕ} {N : ℕ} {c : ℝ} (hc : 0 ≤ c)
    (f : ℕ → ℝ) (hf : ∀ n ∈ S, f n * ‖harmonicMoebiusC n‖ ^ (2 : ℕ) ≤ c) (_hf0 : ∀ n, 0 ≤ f n) :
    (∑ m : Fin N, f ((m : ℕ) + 1) * ‖harmonicMoebiusOn S ((m : ℕ) + 1)‖ ^ (2 : ℕ))
      ≤ c * (S.card : ℝ) := by
  classical
  have hterm : ∀ m : Fin N,
      f ((m : ℕ) + 1) * ‖harmonicMoebiusOn S ((m : ℕ) + 1)‖ ^ (2 : ℕ)
        ≤ c * (if ((m : ℕ) + 1) ∈ S then (1 : ℝ) else 0) := by
    intro m
    by_cases h : ((m : ℕ) + 1) ∈ S
    · rw [if_pos h, mul_one, harmonicMoebiusOn, if_pos h]
      exact hf _ h
    · rw [if_neg h, mul_zero, harmonicMoebiusOn, if_neg h]
      simp
  refine (Finset.sum_le_sum fun m _ => hterm m).trans ?_
  rw [← Finset.mul_sum, Finset.sum_boole]
  refine mul_le_mul_of_nonneg_left ?_ hc
  have hcard : ((Finset.univ.filter (fun m : Fin N => ((m : ℕ) + 1) ∈ S)).card : ℕ)
      ≤ S.card := by
    refine Finset.card_le_card_of_injOn (fun m : Fin N => (m : ℕ) + 1) ?_ ?_
    · intro m hm
      exact (Finset.mem_filter.1 hm).2
    · intro x _ y _ hxy
      exact Fin.ext (Nat.add_right_cancel hxy)
  exact_mod_cast hcard

/-- **The harmonic mean square of a sparse set, by cardinality alone.** -/
theorem integral_Icc_normSq_logPoly_harmonicMoebius_le_card
    {S : Finset ℕ} {A N : ℕ} (hA : 1 ≤ A) (hS : S ⊆ Finset.Icc A N)
    {T : ℝ} (hT : 0 ≤ T) :
    (∫ w in Set.Icc (-T) T, ‖logPoly harmonicMoebiusC S w‖ ^ (2 : ℕ))
      ≤ (5 * Real.pi / 2) * ((S.card : ℝ) / (A : ℝ) ^ (2 : ℕ)) * T
        + ((5 * Real.exp 1 / 2) * ((S.card : ℝ) / (A : ℝ))
          + (5 / 4) * ((S.card : ℝ) / (A : ℝ) ^ (2 : ℕ))) := by
  classical
  have hA0 : (0 : ℝ) < (A : ℝ) := by exact_mod_cast Nat.zero_lt_of_lt hA
  have hSI : S ⊆ Finset.Icc 1 N := by
    intro n hn
    have hn' := Finset.mem_Icc.1 (hS hn)
    exact Finset.mem_Icc.2 ⟨le_trans hA hn'.1, hn'.2⟩
  have hnormSq : ∀ n ∈ S, ‖harmonicMoebiusC n‖ ^ (2 : ℕ) ≤ 1 / (A : ℝ) ^ (2 : ℕ) := by
    intro n hn
    have hn' := Finset.mem_Icc.1 (hS hn)
    have hAn : (A : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn'.1
    have hb := norm_harmonicMoebiusC_le_inv n
    have h1 : (1 : ℝ) / (n : ℝ) ≤ 1 / (A : ℝ) := one_div_le_one_div_of_le hA0 hAn
    have h2 : ‖harmonicMoebiusC n‖ ≤ 1 / (A : ℝ) := hb.trans h1
    have h3 : (0 : ℝ) ≤ ‖harmonicMoebiusC n‖ := norm_nonneg _
    calc ‖harmonicMoebiusC n‖ ^ (2 : ℕ) ≤ (1 / (A : ℝ)) ^ (2 : ℕ) := pow_le_pow_left₀ h3 h2 2
      _ = 1 / (A : ℝ) ^ (2 : ℕ) := by rw [div_pow, one_pow]
  have hweight : ∀ n ∈ S,
      ((n : ℝ)) * ‖harmonicMoebiusC n‖ ^ (2 : ℕ) ≤ 1 / (A : ℝ) := by
    intro n hn
    have hn' := Finset.mem_Icc.1 (hS hn)
    have hAn : (A : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn'.1
    have hn0 : (0 : ℝ) < (n : ℝ) := lt_of_lt_of_le hA0 hAn
    have hb := norm_harmonicMoebiusC_le_inv n
    have h3 : (0 : ℝ) ≤ ‖harmonicMoebiusC n‖ := norm_nonneg _
    have hsq : ‖harmonicMoebiusC n‖ ^ (2 : ℕ) ≤ 1 / (n : ℝ) ^ (2 : ℕ) := by
      have := mul_le_mul hb hb h3 (by positivity)
      calc ‖harmonicMoebiusC n‖ ^ (2 : ℕ) = ‖harmonicMoebiusC n‖ * ‖harmonicMoebiusC n‖ := by ring
        _ ≤ (1 / (n : ℝ)) * (1 / (n : ℝ)) := this
        _ = 1 / (n : ℝ) ^ (2 : ℕ) := by ring
    have hstep : (n : ℝ) * ‖harmonicMoebiusC n‖ ^ (2 : ℕ) ≤ (n : ℝ) * (1 / (n : ℝ) ^ (2 : ℕ)) :=
      mul_le_mul_of_nonneg_left hsq hn0.le
    have heq : (n : ℝ) * (1 / (n : ℝ) ^ (2 : ℕ)) = 1 / (n : ℝ) := by field_simp
    rw [heq] at hstep
    exact hstep.trans (one_div_le_one_div_of_le hA0 hAn)
  have hbase := integral_Icc_normSq_logPoly_le_affine_majorant (harmonicMoebiusOn S) N hT
  have hrw : (∫ w in Set.Icc (-T) T, ‖logPoly harmonicMoebiusC S w‖ ^ (2 : ℕ))
      = ∫ w in Set.Icc (-T) T,
        ‖logPoly (harmonicMoebiusOn S) (Finset.Icc 1 N) w‖ ^ (2 : ℕ) := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc fun w _ => ?_
    rw [logPoly_harmonicMoebiusOn_eq hSI]
  have hplain : (∑ m : Fin N, ‖harmonicMoebiusOn S ((m : ℕ) + 1)‖ ^ (2 : ℕ))
      ≤ (1 / (A : ℝ) ^ (2 : ℕ)) * (S.card : ℝ) := by
    have := sum_weight_normSq_harmonicMoebiusOn_le (S := S) (N := N)
      (c := 1 / (A : ℝ) ^ (2 : ℕ)) (by positivity) (fun _ => 1)
      (fun n hn => by simpa using hnormSq n hn) (fun _ => zero_le_one)
    simpa using this
  have hweighted : (∑ m : Fin N, (((m : ℕ) : ℝ) + 1) * ‖harmonicMoebiusOn S ((m : ℕ) + 1)‖ ^ (2 : ℕ))
      ≤ (1 / (A : ℝ)) * (S.card : ℝ) := by
    have := sum_weight_normSq_harmonicMoebiusOn_le (S := S) (N := N)
      (c := 1 / (A : ℝ)) (by positivity) (fun n => (n : ℝ))
      (fun n hn => hweight n hn) (fun n => by positivity)
    simpa using this
  rw [hrw]
  refine hbase.trans ?_
  have hcard0 : (0 : ℝ) ≤ (S.card : ℝ) := Nat.cast_nonneg _
  have e1 : (1 / (A : ℝ) ^ (2 : ℕ)) * (S.card : ℝ) = (S.card : ℝ) / (A : ℝ) ^ (2 : ℕ) := by ring
  have e2 : (1 / (A : ℝ)) * (S.card : ℝ) = (S.card : ℝ) / (A : ℝ) := by ring
  rw [e1] at hplain
  rw [e2] at hweighted
  have hpi : (0 : ℝ) ≤ 5 * Real.pi / 2 := by positivity
  have he : (0 : ℝ) ≤ 5 * Real.exp 1 / 2 := by positivity
  have h1 : (5 * Real.pi / 2) * (∑ m : Fin N, ‖harmonicMoebiusOn S ((m : ℕ) + 1)‖ ^ (2 : ℕ)) * T
      ≤ (5 * Real.pi / 2) * ((S.card : ℝ) / (A : ℝ) ^ (2 : ℕ)) * T :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hplain hpi) hT
  have h2 : (5 * Real.exp 1 / 2)
        * (∑ m : Fin N, (((m : ℕ) : ℝ) + 1) * ‖harmonicMoebiusOn S ((m : ℕ) + 1)‖ ^ (2 : ℕ))
      ≤ (5 * Real.exp 1 / 2) * ((S.card : ℝ) / (A : ℝ)) :=
    mul_le_mul_of_nonneg_left hweighted he
  have h3 : (5 / 4 : ℝ) * (∑ m : Fin N, ‖harmonicMoebiusOn S ((m : ℕ) + 1)‖ ^ (2 : ℕ))
      ≤ (5 / 4 : ℝ) * ((S.card : ℝ) / (A : ℝ) ^ (2 : ℕ)) :=
    mul_le_mul_of_nonneg_left hplain (by norm_num)
  linarith

end

end RHTower.Sieve
