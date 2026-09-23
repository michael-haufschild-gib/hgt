import GaloisForLFunctions.RHTower.Sieve.KloostermanTerminalOrbitParseval

/-!
# Row-by-row lcm-Parseval control of terminal Kloosterman Gram forms

This module composes exact lcm-period orbit Parseval with the symmetric Schur
test.  Each squared modulus weight is charged only against its own row of
source-residue/lcm-Parseval pair energies, avoiding both the former harmonic
orbit loss and the global modulus-pair Cauchy factor.  A literal source-interval
receiver inserts the exact residue multiplicity bound.

These are unconditional finite Fourier estimates.  They do not supply the
collective signed modulus-average Kuznetsov saving required by Route E.
-/

open scoped BigOperators ComplexConjugate
open Complex Finset

namespace RHTower.Sieve

noncomputable section

/-- Square-root pair kernel obtained from exact source-residue energies and the exact
`lcm`-period Parseval orbit budget. -/
def kloostermanTerminalLcmParsevalSchurPairBudget
    (M q r : ℕ) (B : Finset ℕ) (b : ℕ → ℂ) : ℝ :=
  Real.sqrt
    (kloostermanSourceResidueEnergy q B b *
      kloostermanSourceResidueEnergy r B b *
        kloostermanTerminalOrbitLcmParsevalBudget M q r)

private theorem kloostermanTerminalOrbitLcmParsevalBudget_comm
    (M q r : ℕ) :
    kloostermanTerminalOrbitLcmParsevalBudget M q r =
      kloostermanTerminalOrbitLcmParsevalBudget M r q := by
  unfold kloostermanTerminalOrbitLcmParsevalBudget
  rw [Nat.mul_comm (q + 1) (r + 1), Nat.lcm_comm (q + 1) (r + 1)]

private theorem kloostermanTerminalLcmParsevalSchurPairBudget_comm
    (M q r : ℕ) (B : Finset ℕ) (b : ℕ → ℂ) :
    kloostermanTerminalLcmParsevalSchurPairBudget M q r B b =
      kloostermanTerminalLcmParsevalSchurPairBudget M r q B b := by
  unfold kloostermanTerminalLcmParsevalSchurPairBudget
  rw [kloostermanTerminalOrbitLcmParsevalBudget_comm M q r]
  congr 1
  ring

private theorem kloostermanTerminalLcmParsevalSchurPairBudget_nonneg
    (M q r : ℕ) (B : Finset ℕ) (b : ℕ → ℂ) :
    0 ≤ kloostermanTerminalLcmParsevalSchurPairBudget M q r B b := by
  unfold kloostermanTerminalLcmParsevalSchurPairBudget
  exact Real.sqrt_nonneg _

/-- One stored terminal source quadratic is bounded by the square root of its exact
source-residue/lcm-Parseval energy. -/
theorem norm_sourceQuadratic_terminalBlock_succ_le_lcmParsevalSchurPairBudget
    (M q r : ℕ) (B : Finset ℕ) (b : ℕ → ℂ) :
    ‖∑ n ∈ B, star (b n) * ∑ k ∈ B, b k *
      kloostermanNaturalCrossIntervalTerminalBlock M (q + 1) (r + 1)
        (n : ZMod (q + 1)) (k : ZMod (r + 1))‖ ≤
      kloostermanTerminalLcmParsevalSchurPairBudget M q r B b := by
  rw [kloostermanTerminalLcmParsevalSchurPairBudget]
  rw [show ‖∑ n ∈ B, star (b n) * ∑ k ∈ B, b k *
      kloostermanNaturalCrossIntervalTerminalBlock M (q + 1) (r + 1)
        (n : ZMod (q + 1)) (k : ZMod (r + 1))‖ =
      Real.sqrt (‖∑ n ∈ B, star (b n) * ∑ k ∈ B, b k *
        kloostermanNaturalCrossIntervalTerminalBlock M (q + 1) (r + 1)
          (n : ZMod (q + 1)) (k : ZMod (r + 1))‖ ^ (2 : ℕ)) by
    rw [Real.sqrt_sq (norm_nonneg _)]]
  exact Real.sqrt_le_sqrt
    (norm_sourceQuadratic_terminalBlock_succ_sq_le_residue_lcmParseval
      M q r B b)

/-- Symmetric exact-period Parseval Schur kernel, zero on the modulus diagonal. -/
def kloostermanTerminalLcmParsevalSchurKernel
    (M : ℕ) (B : Finset ℕ) (b : ℕ → ℂ) (q r : ℕ) : ℝ :=
  if q = r then 0 else
    kloostermanTerminalLcmParsevalSchurPairBudget M q r B b

/-- Exact row mass of the lcm-Parseval Schur kernel over the stored modulus family. -/
def kloostermanTerminalLcmParsevalSchurRowBudget
    (M : ℕ) (Q B : Finset ℕ) (b : ℕ → ℂ) (q : ℕ) : ℝ :=
  ∑ r ∈ Q, kloostermanTerminalLcmParsevalSchurKernel M B b q r

/-- Squared modulus weights charged row-by-row against the exact lcm-Parseval kernel. -/
def kloostermanTerminalLcmParsevalSchurWeightEnergy
    (M : ℕ) (Q : Finset ℕ) (w : ℕ → ℂ)
    (B : Finset ℕ) (b : ℕ → ℂ) : ℝ :=
  ∑ q ∈ Q, ‖w q‖ ^ (2 : ℕ) *
    kloostermanTerminalLcmParsevalSchurRowBudget M Q B b q

private theorem kloostermanTerminalLcmParsevalSchurKernel_comm
    (M : ℕ) (B : Finset ℕ) (b : ℕ → ℂ) (q r : ℕ) :
    kloostermanTerminalLcmParsevalSchurKernel M B b q r =
      kloostermanTerminalLcmParsevalSchurKernel M B b r q := by
  unfold kloostermanTerminalLcmParsevalSchurKernel
  by_cases h : q = r
  · simp [h]
  · rw [if_neg h, if_neg (Ne.symm h),
      kloostermanTerminalLcmParsevalSchurPairBudget_comm]

private theorem kloostermanTerminalLcmParsevalSchurKernel_nonneg
    (M : ℕ) (B : Finset ℕ) (b : ℕ → ℂ) (q r : ℕ) :
    0 ≤ kloostermanTerminalLcmParsevalSchurKernel M B b q r := by
  unfold kloostermanTerminalLcmParsevalSchurKernel
  split_ifs
  · exact le_rfl
  · exact kloostermanTerminalLcmParsevalSchurPairBudget_nonneg M q r B b

private theorem symmetric_schur_rows_lcmParseval
    {α : Type*} [DecidableEq α]
    (S : Finset α) (a : α → ℝ) (K : α → α → ℝ)
    (hKsymm : ∀ i j, K i j = K j i)
    (hKnn : ∀ i j, 0 ≤ K i j) :
    (∑ i ∈ S, ∑ j ∈ S, |a i| * |a j| * K i j) ≤
      ∑ i ∈ S, (a i) ^ (2 : ℕ) * ∑ j ∈ S, K i j := by
  have hamgm : ∀ i j, |a i| * |a j| * K i j ≤
      ((a i) ^ (2 : ℕ) / 2 + (a j) ^ (2 : ℕ) / 2) * K i j := by
    intro i j
    apply mul_le_mul_of_nonneg_right _ (hKnn i j)
    nlinarith [sq_nonneg (|a i| - |a j|), sq_abs (a i), sq_abs (a j)]
  calc
    _ ≤ ∑ i ∈ S, ∑ j ∈ S,
        ((a i) ^ (2 : ℕ) / 2 + (a j) ^ (2 : ℕ) / 2) * K i j := by
      exact Finset.sum_le_sum fun i hi =>
        Finset.sum_le_sum fun j hj => hamgm i j
    _ = (∑ i ∈ S, (a i) ^ (2 : ℕ) / 2 * ∑ j ∈ S, K i j) +
        ∑ i ∈ S, ∑ j ∈ S, (a j) ^ (2 : ℕ) / 2 * K i j := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ = (∑ i ∈ S, (a i) ^ (2 : ℕ) / 2 * ∑ j ∈ S, K i j) +
        ∑ j ∈ S, (a j) ^ (2 : ℕ) / 2 * ∑ i ∈ S, K j i := by
      congr 1
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [hKsymm i j]
    _ = ∑ i ∈ S, (a i) ^ (2 : ℕ) * ∑ j ∈ S, K i j := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      ring

/-- Full terminal Gram quadratic controlled row-by-row by the exact lcm-period Parseval kernel.
Each squared modulus weight is charged only to its own row; no global pairwise Cauchy product and
no spectral cancellation premise is used. -/
theorem norm_kloostermanDistinctModulusTerminalGramQuadratic_le_lcmParsevalSchurWeightEnergy
    (M : ℕ) (Q : Finset ℕ) (w : ℕ → ℂ)
    (B : Finset ℕ) (b : ℕ → ℂ) :
    ‖kloostermanDistinctModulusTerminalGramQuadratic M Q w B b‖ ≤
      kloostermanTerminalLcmParsevalSchurWeightEnergy M Q w B b := by
  classical
  rw [kloostermanDistinctModulusTerminalGramQuadratic_eq_sourceFourierOrbits]
  simp_rw [← sourceQuadratic_terminalBlock_eq_fourierOrbits]
  let S : ℕ → ℕ → ℂ := fun q r =>
    ∑ n ∈ B, star (b n) * ∑ k ∈ B, b k *
      kloostermanNaturalCrossIntervalTerminalBlock M (q + 1) (r + 1)
        (n : ZMod (q + 1)) (k : ZMod (r + 1))
  calc
    ‖∑ q ∈ Q, ∑ r ∈ Q.erase q, star (w q) * w r * S q r‖ ≤
        ∑ q ∈ Q, ∑ r ∈ Q.erase q, ‖star (w q) * w r * S q r‖ := by
      refine (norm_sum_le _ _).trans ?_
      apply Finset.sum_le_sum
      intro q hq
      exact norm_sum_le _ _
    _ = ∑ q ∈ Q, ∑ r ∈ Q.erase q, ‖w q‖ * ‖w r‖ * ‖S q r‖ := by
      apply Finset.sum_congr rfl
      intro q hq
      apply Finset.sum_congr rfl
      intro r hr
      rw [norm_mul, norm_mul, norm_star]
    _ ≤ ∑ q ∈ Q, ∑ r ∈ Q.erase q,
        ‖w q‖ * ‖w r‖ *
          kloostermanTerminalLcmParsevalSchurPairBudget M q r B b := by
      apply Finset.sum_le_sum
      intro q hq
      apply Finset.sum_le_sum
      intro r hr
      apply mul_le_mul_of_nonneg_left
      · dsimp only [S]
        exact norm_sourceQuadratic_terminalBlock_succ_le_lcmParsevalSchurPairBudget
          M q r B b
      · positivity
    _ = ∑ q ∈ Q, ∑ r ∈ Q,
        ‖w q‖ * ‖w r‖ *
          kloostermanTerminalLcmParsevalSchurKernel M B b q r := by
      apply Finset.sum_congr rfl
      intro q hq
      let f : ℕ → ℝ := fun r =>
        ‖w q‖ * ‖w r‖ *
          kloostermanTerminalLcmParsevalSchurKernel M B b q r
      have hfq : f q = 0 := by
        simp [f, kloostermanTerminalLcmParsevalSchurKernel]
      rw [← Finset.sum_erase Q hfq]
      apply Finset.sum_congr rfl
      intro r hr
      have hrq : r ≠ q := (Finset.mem_erase.mp hr).1
      simp only [f, kloostermanTerminalLcmParsevalSchurKernel,
        if_neg (Ne.symm hrq)]
    _ ≤ ∑ q ∈ Q, ‖w q‖ ^ (2 : ℕ) * ∑ r ∈ Q,
        kloostermanTerminalLcmParsevalSchurKernel M B b q r := by
      simpa only [abs_norm] using
        symmetric_schur_rows_lcmParseval Q (fun q => ‖w q‖)
          (kloostermanTerminalLcmParsevalSchurKernel M B b)
          (kloostermanTerminalLcmParsevalSchurKernel_comm M B b)
          (kloostermanTerminalLcmParsevalSchurKernel_nonneg M B b)
    _ = kloostermanTerminalLcmParsevalSchurWeightEnergy M Q w B b := by
      rfl

/-- Exact lcm-Parseval Schur pair budget after inserting literal interval source multiplicity. -/
def kloostermanIntervalTerminalLcmParsevalSchurPairBudget
    (M q r N : ℕ) (b : ℕ → ℂ) : ℝ :=
  Real.sqrt
    (kloostermanIntervalSourceEnergyBudget q N b *
      kloostermanIntervalSourceEnergyBudget r N b *
        kloostermanTerminalOrbitLcmParsevalBudget M q r)

/-- Literal-interval exact-period Parseval Schur kernel, zero on the modulus diagonal. -/
def kloostermanIntervalTerminalLcmParsevalSchurKernel
    (M N : ℕ) (b : ℕ → ℂ) (q r : ℕ) : ℝ :=
  if q = r then 0 else
    kloostermanIntervalTerminalLcmParsevalSchurPairBudget M q r N b

/-- Literal-interval row mass of the exact-period Parseval Schur kernel. -/
def kloostermanIntervalTerminalLcmParsevalSchurRowBudget
    (M N : ℕ) (Q : Finset ℕ) (b : ℕ → ℂ) (q : ℕ) : ℝ :=
  ∑ r ∈ Q, kloostermanIntervalTerminalLcmParsevalSchurKernel M N b q r

/-- Squared modulus weights charged against their own literal-interval lcm-Parseval rows. -/
def kloostermanIntervalTerminalLcmParsevalSchurWeightEnergy
    (M N : ℕ) (Q : Finset ℕ) (w b : ℕ → ℂ) : ℝ :=
  ∑ q ∈ Q, ‖w q‖ ^ (2 : ℕ) *
    kloostermanIntervalTerminalLcmParsevalSchurRowBudget M N Q b q

private theorem kloostermanIntervalSourceEnergyBudget_nonneg_lcmParseval
    (q N : ℕ) (b : ℕ → ℂ) :
    0 ≤ kloostermanIntervalSourceEnergyBudget q N b := by
  unfold kloostermanIntervalSourceEnergyBudget
  exact mul_nonneg (by positivity) <| mul_nonneg (by positivity)
    (Finset.sum_nonneg fun n hn => Complex.normSq_nonneg _)

private theorem kloostermanTerminalOrbitLcmParsevalBudget_nonneg
    (M q r : ℕ) :
    0 ≤ kloostermanTerminalOrbitLcmParsevalBudget M q r := by
  unfold kloostermanTerminalOrbitLcmParsevalBudget
  positivity

private theorem kloostermanTerminalLcmParsevalSchurPairBudget_Icc_le_interval
    (M q r N : ℕ) (b : ℕ → ℂ) :
    kloostermanTerminalLcmParsevalSchurPairBudget
        M q r (Finset.Icc 1 N) b ≤
      kloostermanIntervalTerminalLcmParsevalSchurPairBudget M q r N b := by
  unfold kloostermanTerminalLcmParsevalSchurPairBudget
    kloostermanIntervalTerminalLcmParsevalSchurPairBudget
  apply Real.sqrt_le_sqrt
  have hEq0 : 0 ≤ kloostermanSourceResidueEnergy q (Finset.Icc 1 N) b := by
    unfold kloostermanSourceResidueEnergy
    exact mul_nonneg (by positivity)
      (Finset.sum_nonneg fun z hz => Complex.normSq_nonneg _)
  have hEr0 : 0 ≤ kloostermanSourceResidueEnergy r (Finset.Icc 1 N) b := by
    unfold kloostermanSourceResidueEnergy
    exact mul_nonneg (by positivity)
      (Finset.sum_nonneg fun z hz => Complex.normSq_nonneg _)
  have hBq0 := kloostermanIntervalSourceEnergyBudget_nonneg_lcmParseval q N b
  have hT0 := kloostermanTerminalOrbitLcmParsevalBudget_nonneg M q r
  calc
    kloostermanSourceResidueEnergy q (Finset.Icc 1 N) b *
          kloostermanSourceResidueEnergy r (Finset.Icc 1 N) b *
        kloostermanTerminalOrbitLcmParsevalBudget M q r ≤
        kloostermanIntervalSourceEnergyBudget q N b *
          kloostermanSourceResidueEnergy r (Finset.Icc 1 N) b *
        kloostermanTerminalOrbitLcmParsevalBudget M q r := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (kloostermanSourceResidueEnergy_Icc_le_intervalBudget q N b) hEr0)
        hT0
    _ ≤ kloostermanIntervalSourceEnergyBudget q N b *
          kloostermanIntervalSourceEnergyBudget r N b *
        kloostermanTerminalOrbitLcmParsevalBudget M q r := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left
          (kloostermanSourceResidueEnergy_Icc_le_intervalBudget r N b) hBq0)
        hT0

private theorem kloostermanTerminalLcmParsevalSchurKernel_Icc_le_interval
    (M N : ℕ) (b : ℕ → ℂ) (q r : ℕ) :
    kloostermanTerminalLcmParsevalSchurKernel M (Finset.Icc 1 N) b q r ≤
      kloostermanIntervalTerminalLcmParsevalSchurKernel M N b q r := by
  unfold kloostermanTerminalLcmParsevalSchurKernel
    kloostermanIntervalTerminalLcmParsevalSchurKernel
  by_cases hqr : q = r
  · simp [hqr]
  · rw [if_neg hqr, if_neg hqr]
    exact kloostermanTerminalLcmParsevalSchurPairBudget_Icc_le_interval
      M q r N b

private theorem kloostermanTerminalLcmParsevalSchurWeightEnergy_Icc_le_interval
    (M N : ℕ) (Q : Finset ℕ) (w b : ℕ → ℂ) :
    kloostermanTerminalLcmParsevalSchurWeightEnergy
        M Q w (Finset.Icc 1 N) b ≤
      kloostermanIntervalTerminalLcmParsevalSchurWeightEnergy M N Q w b := by
  unfold kloostermanTerminalLcmParsevalSchurWeightEnergy
    kloostermanTerminalLcmParsevalSchurRowBudget
    kloostermanIntervalTerminalLcmParsevalSchurWeightEnergy
    kloostermanIntervalTerminalLcmParsevalSchurRowBudget
  apply Finset.sum_le_sum
  intro q hq
  apply mul_le_mul_of_nonneg_left
  · exact Finset.sum_le_sum fun r hr =>
      kloostermanTerminalLcmParsevalSchurKernel_Icc_le_interval M N b q r
  · positivity

/-- Full weighted terminal Gram receiver on the literal source interval with exact lcm-period
Parseval charged row-by-row.  No support injectivity, global pairwise Cauchy factor, or spectral
estimate is assumed. -/
theorem norm_kloostermanDistinctModulusTerminalGramQuadratic_Icc_le_interval_lcmParsevalSchurWeightEnergy
    (M N : ℕ) (Q : Finset ℕ) (w b : ℕ → ℂ) :
    ‖kloostermanDistinctModulusTerminalGramQuadratic
        M Q w (Finset.Icc 1 N) b‖ ≤
      kloostermanIntervalTerminalLcmParsevalSchurWeightEnergy M N Q w b := by
  exact
    (norm_kloostermanDistinctModulusTerminalGramQuadratic_le_lcmParsevalSchurWeightEnergy
      M Q w (Finset.Icc 1 N) b).trans
      (kloostermanTerminalLcmParsevalSchurWeightEnergy_Icc_le_interval
        M N Q w b)

end

end RHTower.Sieve
