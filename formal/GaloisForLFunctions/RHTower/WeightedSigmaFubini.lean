import GaloisForLFunctions.RHTower.SigmaContractionCorollary

/-!
# The discrete Fubini for the weighted remainder mass

The `(log N − log v)`-weighted harmonic remainder mass is an
increment-average of the plain σ-partial sums:

`∑_{v ≤ N} |R(v)|(1/v − 1/(v+1))·(log N − log v)
   = ∑_{1 < t ≤ N} (log t − log(t−1))·σ(t−1)`,

where `σ(s) = ∑_{v ≤ s} |R(v)|(1/v − 1/(v+1))`: the weight telescopes as
`log N − log v = ∑_{v < t ≤ N} (log t − log(t−1))` and the double sum
swaps.  Since each increment is at most `1/(t−1)`, the σ-contraction
applies scale by scale — this converts the fiber-transferred weighted mass
into iterated plain contractions with no weighted ladder.
-/

noncomputable section

namespace RHTower

open ArithmeticFunction Finset

/-- The σ-partial sum `σ(s) = ∑_{v ≤ s} |R(v)|(1/v − 1/(v+1))`. -/
def sigmaPartial (s : ℕ) : ℝ :=
  ∑ v ∈ Finset.Icc 1 s, |psiRemainder v| * (1 / (v : ℝ) - 1 / ((v : ℝ) + 1))

theorem sigmaPartial_nonneg (s : ℕ) : 0 ≤ sigmaPartial s := by
  apply Finset.sum_nonneg
  intro v hv
  rw [Finset.mem_Icc] at hv
  have hv0 : (0 : ℝ) < v := by exact_mod_cast (by omega : 0 < v)
  apply mul_nonneg (abs_nonneg _)
  rw [sub_nonneg]
  apply div_le_div_of_nonneg_left one_pos.le hv0
  linarith

/-- **Discrete Fubini**: the log-weighted remainder mass equals the
increment-weighted sum of σ-partial sums. -/
theorem weighted_sigma_eq (N : ℕ) :
    ∑ v ∈ Finset.Icc 1 N, |psiRemainder v|
        * (1 / (v : ℝ) - 1 / ((v : ℝ) + 1)) * (Real.log N - Real.log v)
      = ∑ t ∈ Finset.Ioc 1 N,
          (Real.log t - Real.log ((t - 1 : ℕ) : ℝ)) * sigmaPartial (t - 1) := by
  -- expand the weight as a telescoping sum over `t ∈ (v, N]`
  have hexp : ∀ v ∈ Finset.Icc 1 N,
      |psiRemainder v| * (1 / (v : ℝ) - 1 / ((v : ℝ) + 1))
          * (Real.log N - Real.log v)
        = ∑ t ∈ Finset.Ioc v N,
            (|psiRemainder v| * (1 / (v : ℝ) - 1 / ((v : ℝ) + 1)))
              * (Real.log t - Real.log ((t - 1 : ℕ) : ℝ)) := by
    intro v hv
    rw [Finset.mem_Icc] at hv
    have htel : ∑ t ∈ Finset.Ioc v N,
        (Real.log t - Real.log ((t - 1 : ℕ) : ℝ))
        = Real.log N - Real.log v := by
      have hre : ∑ t ∈ Finset.Ioc v N,
          (Real.log t - Real.log ((t - 1 : ℕ) : ℝ))
          = ∑ n ∈ Finset.Ioc (v - 1) (N - 1),
              (Real.log ((n : ℝ) + 1) - Real.log n) := by
        apply Finset.sum_nbij' (i := fun t => t - 1) (j := fun n => n + 1)
        · intro t ht
          rw [Finset.mem_Ioc] at ht
          rw [Finset.mem_Ioc]
          omega
        · intro n hn
          rw [Finset.mem_Ioc] at hn
          rw [Finset.mem_Ioc]
          omega
        · intro t ht
          rw [Finset.mem_Ioc] at ht
          omega
        · intro n _
          omega
        · intro t ht
          rw [Finset.mem_Ioc] at ht
          have hc : ((t - 1 : ℕ) : ℝ) + 1 = (t : ℝ) := by
            rw [Nat.cast_sub (by omega), Nat.cast_one]
            linarith
          rw [hc]
      rcases Nat.lt_or_ge v N with hvN | hvN
      · rw [hre, sum_log_inc_window (v - 1) (N - 1) (by omega)]
        have hc1 : (((N - 1 : ℕ)) : ℝ) + 1 = (N : ℝ) := by
          rw [Nat.cast_sub (by omega), Nat.cast_one]
          linarith
        have hc2 : (((v - 1 : ℕ)) : ℝ) + 1 = (v : ℝ) := by
          rw [Nat.cast_sub (by omega), Nat.cast_one]
          linarith
        rw [hc1, hc2]
      · have hvN' : v = N := by omega
        rw [hvN']
        simp
    rw [← Finset.mul_sum, htel]
  rw [Finset.sum_congr rfl hexp, Finset.sum_sigma']
  -- swap the double sum
  have hbij : ∑ x ∈ (Finset.Icc 1 N).sigma (fun v => Finset.Ioc v N),
      (|psiRemainder x.1| * (1 / (x.1 : ℝ) - 1 / ((x.1 : ℝ) + 1)))
        * (Real.log x.2 - Real.log ((x.2 - 1 : ℕ) : ℝ))
      = ∑ y ∈ (Finset.Ioc 1 N).sigma (fun t => Finset.Icc 1 (t - 1)),
          (|psiRemainder y.2| * (1 / (y.2 : ℝ) - 1 / ((y.2 : ℝ) + 1)))
            * (Real.log y.1 - Real.log ((y.1 - 1 : ℕ) : ℝ)) := by
    apply Finset.sum_nbij' (i := fun x => ⟨x.2, x.1⟩)
      (j := fun y => ⟨y.2, y.1⟩)
    · rintro ⟨v, t⟩ hx
      rw [Finset.mem_sigma, Finset.mem_Icc, Finset.mem_Ioc] at hx
      dsimp only at hx
      rw [Finset.mem_sigma, Finset.mem_Ioc, Finset.mem_Icc]
      dsimp only
      omega
    · rintro ⟨t, v⟩ hy
      rw [Finset.mem_sigma, Finset.mem_Ioc, Finset.mem_Icc] at hy
      dsimp only at hy
      rw [Finset.mem_sigma, Finset.mem_Icc, Finset.mem_Ioc]
      dsimp only
      omega
    · rintro ⟨v, t⟩ _
      rfl
    · rintro ⟨t, v⟩ _
      rfl
    · rintro ⟨v, t⟩ _
      rfl
  rw [hbij, Finset.sum_sigma]
  apply Finset.sum_congr rfl
  intro t _
  dsimp only
  rw [sigmaPartial, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v _
  ring

/-- **Increment domination**: the weighted mass is bounded by reciprocal-
weighted σ-partial sums. -/
theorem weighted_sigma_le (N : ℕ) :
    ∑ v ∈ Finset.Icc 1 N, |psiRemainder v|
        * (1 / (v : ℝ) - 1 / ((v : ℝ) + 1)) * (Real.log N - Real.log v)
      ≤ ∑ t ∈ Finset.Ioc 1 N,
          (1 / ((t - 1 : ℕ) : ℝ)) * sigmaPartial (t - 1) := by
  rw [weighted_sigma_eq N]
  apply Finset.sum_le_sum
  intro t ht
  rw [Finset.mem_Ioc] at ht
  apply mul_le_mul_of_nonneg_right _ (sigmaPartial_nonneg (t - 1))
  have h := log_succ_sub_log_le (j := t - 1) (by omega)
  have hc : ((t - 1 : ℕ) : ℝ) + 1 = (t : ℝ) := by
    rw [Nat.cast_sub (by omega), Nat.cast_one]
    linarith
  rw [hc] at h
  linarith

end RHTower
