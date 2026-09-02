import GaloisForLFunctions.RHTower.Sieve.KloostermanTerminalOrbitEnergy

/-!
# Literal-interval multiplicity for Kloosterman source residues

Reduction of `Finset.Icc 1 N` modulo the stored modulus `q + 1` has multiplicity at most
`0` for `N = 0` and `(N - 1) / (q + 1) + 1` otherwise. Fibrewise Cauchy--Schwarz therefore
replaces exact residue-collision energy by
an explicit interval coefficient-energy budget. The final theorem inserts that budget into the
full weighted terminal Gram receiver without claiming collective spectral cancellation.
-/

open scoped BigOperators ComplexConjugate
open Complex Finset

namespace RHTower.Sieve

noncomputable section

/-- Exact maximum occupancy of a residue class in the positive interval `Finset.Icc 1 N`. -/
def kloostermanIntervalResidueMultiplicity (q N : ℕ) : ℕ :=
  if N = 0 then 0 else (N - 1) / (q + 1) + 1

/-- Every residue class modulo the stored modulus `q + 1` occurs at most the exact positive-
interval residue multiplicity in `Finset.Icc 1 N`. -/
theorem card_filter_Icc_natCast_zmod_succ_le
    (q N : ℕ) (z : ZMod (q + 1)) :
    ((Finset.Icc 1 N).filter (fun n : ℕ => (n : ZMod (q + 1)) = z)).card ≤
      kloostermanIntervalResidueMultiplicity q N := by
  classical
  by_cases hN : N = 0
  · subst N
    simp [kloostermanIntervalResidueMultiplicity]
  · let S := (Finset.Icc 1 N).filter (fun n : ℕ => (n : ZMod (q + 1)) = z)
    let f : ↥S → ↥(Finset.range ((N - 1) / (q + 1) + 1)) := fun n =>
      ⟨(n.1 - 1) / (q + 1), by
        rw [Finset.mem_range]
        have hnN : n.1 ≤ N :=
          (Finset.mem_Icc.mp (Finset.mem_filter.mp n.2).1).2
        exact Nat.lt_succ_of_le
          (Nat.div_le_div_right (Nat.sub_le_sub_right hnN 1))⟩
    have hf : Function.Injective f := by
      intro n m hnm
      apply Subtype.ext
      have hn1 : 1 ≤ n.1 :=
        (Finset.mem_Icc.mp (Finset.mem_filter.mp n.2).1).1
      have hm1 : 1 ≤ m.1 :=
        (Finset.mem_Icc.mp (Finset.mem_filter.mp m.2).1).1
      have hdiv : (n.1 - 1) / (q + 1) = (m.1 - 1) / (q + 1) :=
        congrArg Subtype.val hnm
      have hnz : (n.1 : ZMod (q + 1)) = z :=
        (Finset.mem_filter.mp n.2).2
      have hmz : (m.1 : ZMod (q + 1)) = z :=
        (Finset.mem_filter.mp m.2).2
      have hcast : (n.1 : ZMod (q + 1)) = (m.1 : ZMod (q + 1)) :=
        hnz.trans hmz.symm
      have hcastSub : ((n.1 - 1 : ℕ) : ZMod (q + 1)) =
          ((m.1 - 1 : ℕ) : ZMod (q + 1)) := by
        rw [Nat.cast_sub hn1, Nat.cast_sub hm1, hcast]
      have hmodEq : n.1 - 1 ≡ m.1 - 1 [MOD q + 1] :=
        (ZMod.natCast_eq_natCast_iff (n.1 - 1) (m.1 - 1) (q + 1)).mp hcastSub
      have hmod : (n.1 - 1) % (q + 1) = (m.1 - 1) % (q + 1) := hmodEq
      have hsub : n.1 - 1 = m.1 - 1 := by
        calc
          n.1 - 1 = (n.1 - 1) % (q + 1) +
              (q + 1) * ((n.1 - 1) / (q + 1)) :=
            (Nat.mod_add_div (n.1 - 1) (q + 1)).symm
          _ = (m.1 - 1) % (q + 1) +
              (q + 1) * ((m.1 - 1) / (q + 1)) := by
            rw [hmod, hdiv]
          _ = m.1 - 1 := Nat.mod_add_div (m.1 - 1) (q + 1)
      omega
    change S.card ≤ kloostermanIntervalResidueMultiplicity q N
    rw [kloostermanIntervalResidueMultiplicity, if_neg hN]
    simpa only [Finset.card_range] using
      (Finset.card_le_card_of_injective (f := f) hf)

private theorem normSq_sum_le_card_mul_sum_normSq
    (S : Finset ℕ) (b : ℕ → ℂ) :
    Complex.normSq (∑ n ∈ S, b n) ≤
      (S.card : ℝ) * ∑ n ∈ S, Complex.normSq (b n) := by
  have htri : ‖∑ n ∈ S, b n‖ ≤ ∑ n ∈ S, ‖b n‖ := norm_sum_le _ _
  have hsum0 : 0 ≤ ∑ n ∈ S, ‖b n‖ := by positivity
  calc
    Complex.normSq (∑ n ∈ S, b n) = ‖∑ n ∈ S, b n‖ ^ 2 :=
      (Complex.sq_norm _).symm
    _ ≤ (∑ n ∈ S, ‖b n‖) ^ 2 := by
      nlinarith [norm_nonneg (∑ n ∈ S, b n)]
    _ ≤ (S.card : ℝ) * ∑ n ∈ S, Complex.normSq (b n) := by
      simpa only [Complex.sq_norm] using
        (sq_sum_le_card_mul_sum_sq (s := S) (f := fun n => ‖b n‖))

/-- Explicit source-energy budget for literal interval `Finset.Icc 1 N`. -/
def kloostermanIntervalSourceEnergyBudget
    (q N : ℕ) (b : ℕ → ℂ) : ℝ :=
  ((q + 1 : ℕ) : ℝ) *
    ((kloostermanIntervalResidueMultiplicity q N : ℝ) *
      ∑ n ∈ Finset.Icc 1 N, Complex.normSq (b n))

/-- Exact residue-collision source energy on `Finset.Icc 1 N` is bounded by modulus size times
sharp maximum residue multiplicity times coefficient `ℓ²` energy. -/
theorem kloostermanSourceResidueEnergy_Icc_le_intervalBudget
    (q N : ℕ) (b : ℕ → ℂ) :
    kloostermanSourceResidueEnergy q (Finset.Icc 1 N) b ≤
      kloostermanIntervalSourceEnergyBudget q N b := by
  classical
  unfold kloostermanSourceResidueEnergy kloostermanIntervalSourceEnergyBudget
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  calc
    (∑ z : ZMod (q + 1),
        Complex.normSq
          (kloostermanSourceResidue (q + 1) (Finset.Icc 1 N) b z)) ≤
        ∑ z : ZMod (q + 1),
          (kloostermanIntervalResidueMultiplicity q N : ℝ) *
            ∑ n ∈ (Finset.Icc 1 N).filter
              (fun n : ℕ => (n : ZMod (q + 1)) = z),
              Complex.normSq (b n) := by
      apply Finset.sum_le_sum
      intro z hz
      unfold kloostermanSourceResidue
      calc
        Complex.normSq
            (∑ n ∈ (Finset.Icc 1 N).filter
              (fun n : ℕ => (n : ZMod (q + 1)) = z), b n) ≤
            ((((Finset.Icc 1 N).filter
              (fun n : ℕ => (n : ZMod (q + 1)) = z)).card : ℕ) : ℝ) *
              ∑ n ∈ (Finset.Icc 1 N).filter
                (fun n : ℕ => (n : ZMod (q + 1)) = z),
                Complex.normSq (b n) :=
          normSq_sum_le_card_mul_sum_normSq _ b
        _ ≤ (kloostermanIntervalResidueMultiplicity q N : ℝ) *
              ∑ n ∈ (Finset.Icc 1 N).filter
                (fun n : ℕ => (n : ZMod (q + 1)) = z),
                Complex.normSq (b n) := by
          apply mul_le_mul_of_nonneg_right _
            (Finset.sum_nonneg fun n hn => Complex.normSq_nonneg _)
          exact_mod_cast card_filter_Icc_natCast_zmod_succ_le q N z
    _ = (kloostermanIntervalResidueMultiplicity q N : ℝ) *
        ∑ z : ZMod (q + 1),
          ∑ n ∈ (Finset.Icc 1 N).filter
            (fun n : ℕ => (n : ZMod (q + 1)) = z),
            Complex.normSq (b n) := by
      rw [Finset.mul_sum]
    _ = (kloostermanIntervalResidueMultiplicity q N : ℝ) *
        ∑ n ∈ Finset.Icc 1 N, Complex.normSq (b n) := by
      rw [Finset.sum_fiberwise]

/-- Full weighted terminal Gram receiver on literal source interval, with every exact source
residue energy replaced by its unconditional multiplicity budget. -/
theorem norm_kloostermanDistinctModulusTerminalGramQuadratic_Icc_sq_le_interval_interpolated
    (M N : ℕ) (Q : Finset ℕ) (w b : ℕ → ℂ) :
    ‖kloostermanDistinctModulusTerminalGramQuadratic
        M Q w (Finset.Icc 1 N) b‖ ^ 2 ≤
      kloostermanDistinctModulusWeightPairEnergy Q w *
        ∑ q ∈ Q, ∑ r ∈ Q.erase q,
          kloostermanIntervalSourceEnergyBudget q N b *
            kloostermanIntervalSourceEnergyBudget r N b *
              kloostermanTerminalOrbitInterpolatedBudget M q r := by
  calc
    _ ≤ kloostermanDistinctModulusWeightPairEnergy Q w *
        ∑ q ∈ Q, ∑ r ∈ Q.erase q,
          kloostermanSourceResidueEnergy q (Finset.Icc 1 N) b *
            kloostermanSourceResidueEnergy r (Finset.Icc 1 N) b *
              kloostermanTerminalOrbitInterpolatedBudget M q r :=
      norm_kloostermanDistinctModulusTerminalGramQuadratic_sq_le_weightPair_residue_interpolated
        M Q w (Finset.Icc 1 N) b
    _ ≤ kloostermanDistinctModulusWeightPairEnergy Q w *
        ∑ q ∈ Q, ∑ r ∈ Q.erase q,
          kloostermanIntervalSourceEnergyBudget q N b *
            kloostermanIntervalSourceEnergyBudget r N b *
              kloostermanTerminalOrbitInterpolatedBudget M q r := by
      apply mul_le_mul_of_nonneg_left _
      · unfold kloostermanDistinctModulusWeightPairEnergy
        positivity
      · apply Finset.sum_le_sum
        intro q hq
        apply Finset.sum_le_sum
        intro r hr
        have hSr : 0 ≤ kloostermanSourceResidueEnergy r (Finset.Icc 1 N) b := by
          unfold kloostermanSourceResidueEnergy
          exact mul_nonneg (by positivity)
            (Finset.sum_nonneg fun z hz => Complex.normSq_nonneg _)
        have hBq : 0 ≤ kloostermanIntervalSourceEnergyBudget q N b := by
          unfold kloostermanIntervalSourceEnergyBudget
          exact mul_nonneg (by positivity) <| mul_nonneg (by positivity)
            (Finset.sum_nonneg fun n hn => Complex.normSq_nonneg _)
        have hT : 0 ≤ kloostermanTerminalOrbitInterpolatedBudget M q r := by
          unfold kloostermanTerminalOrbitInterpolatedBudget
          exact mul_nonneg (by positivity)
            (kloostermanProductHarmonicPairBudget_nonneg q r)
        calc
          kloostermanSourceResidueEnergy q (Finset.Icc 1 N) b *
                kloostermanSourceResidueEnergy r (Finset.Icc 1 N) b *
              kloostermanTerminalOrbitInterpolatedBudget M q r ≤
              kloostermanIntervalSourceEnergyBudget q N b *
                kloostermanSourceResidueEnergy r (Finset.Icc 1 N) b *
              kloostermanTerminalOrbitInterpolatedBudget M q r := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right
                (kloostermanSourceResidueEnergy_Icc_le_intervalBudget q N b) hSr)
              hT
          _ ≤ kloostermanIntervalSourceEnergyBudget q N b *
                kloostermanIntervalSourceEnergyBudget r N b *
              kloostermanTerminalOrbitInterpolatedBudget M q r := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left
                (kloostermanSourceResidueEnergy_Icc_le_intervalBudget r N b) hBq)
              hT

/-! ### Literal-interval Schur-row receiver -/

/-- Terminal Schur pair kernel after replacing both exact residue energies by their literal
positive-interval multiplicity budgets. -/
def kloostermanIntervalTerminalSchurPairBudget
    (M q r N : ℕ) (b : ℕ → ℂ) : ℝ :=
  Real.sqrt
    (kloostermanIntervalSourceEnergyBudget q N b *
      kloostermanIntervalSourceEnergyBudget r N b *
        kloostermanTerminalOrbitInterpolatedBudget M q r)

/-- Literal-interval Schur kernel, zero on the modulus diagonal. -/
def kloostermanIntervalTerminalSchurKernel
    (M N : ℕ) (b : ℕ → ℂ) (q r : ℕ) : ℝ :=
  if q = r then 0 else kloostermanIntervalTerminalSchurPairBudget M q r N b

/-- Exact literal-interval Schur row over the stored modulus family. -/
def kloostermanIntervalTerminalSchurRowBudget
    (M N : ℕ) (Q : Finset ℕ) (b : ℕ → ℂ) (q : ℕ) : ℝ :=
  ∑ r ∈ Q, kloostermanIntervalTerminalSchurKernel M N b q r

/-- Squared modulus weights charged against their own literal-interval Schur rows. -/
def kloostermanIntervalTerminalSchurWeightEnergy
    (M N : ℕ) (Q : Finset ℕ) (w b : ℕ → ℂ) : ℝ :=
  ∑ q ∈ Q, ‖w q‖ ^ 2 *
    kloostermanIntervalTerminalSchurRowBudget M N Q b q

private theorem kloostermanIntervalSourceEnergyBudget_nonneg
    (q N : ℕ) (b : ℕ → ℂ) :
    0 ≤ kloostermanIntervalSourceEnergyBudget q N b := by
  unfold kloostermanIntervalSourceEnergyBudget
  exact mul_nonneg (by positivity) <| mul_nonneg (by positivity)
    (Finset.sum_nonneg fun n hn => Complex.normSq_nonneg _)

private theorem kloostermanTerminalOrbitInterpolatedBudget_nonneg
    (M q r : ℕ) :
    0 ≤ kloostermanTerminalOrbitInterpolatedBudget M q r := by
  unfold kloostermanTerminalOrbitInterpolatedBudget
  exact mul_nonneg (by positivity)
    (kloostermanProductHarmonicPairBudget_nonneg q r)

private theorem kloostermanTerminalSchurPairBudget_Icc_le_interval
    (M q r N : ℕ) (b : ℕ → ℂ) :
    kloostermanTerminalSchurPairBudget M q r (Finset.Icc 1 N) b ≤
      kloostermanIntervalTerminalSchurPairBudget M q r N b := by
  unfold kloostermanTerminalSchurPairBudget
    kloostermanIntervalTerminalSchurPairBudget
  apply Real.sqrt_le_sqrt
  have hEq0 : 0 ≤ kloostermanSourceResidueEnergy q (Finset.Icc 1 N) b := by
    unfold kloostermanSourceResidueEnergy
    exact mul_nonneg (by positivity)
      (Finset.sum_nonneg fun z hz => Complex.normSq_nonneg _)
  have hEr0 : 0 ≤ kloostermanSourceResidueEnergy r (Finset.Icc 1 N) b := by
    unfold kloostermanSourceResidueEnergy
    exact mul_nonneg (by positivity)
      (Finset.sum_nonneg fun z hz => Complex.normSq_nonneg _)
  have hBq0 := kloostermanIntervalSourceEnergyBudget_nonneg q N b
  have hT0 := kloostermanTerminalOrbitInterpolatedBudget_nonneg M q r
  calc
    kloostermanSourceResidueEnergy q (Finset.Icc 1 N) b *
          kloostermanSourceResidueEnergy r (Finset.Icc 1 N) b *
        kloostermanTerminalOrbitInterpolatedBudget M q r ≤
        kloostermanIntervalSourceEnergyBudget q N b *
          kloostermanSourceResidueEnergy r (Finset.Icc 1 N) b *
        kloostermanTerminalOrbitInterpolatedBudget M q r := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (kloostermanSourceResidueEnergy_Icc_le_intervalBudget q N b) hEr0)
        hT0
    _ ≤ kloostermanIntervalSourceEnergyBudget q N b *
          kloostermanIntervalSourceEnergyBudget r N b *
        kloostermanTerminalOrbitInterpolatedBudget M q r := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left
          (kloostermanSourceResidueEnergy_Icc_le_intervalBudget r N b) hBq0)
        hT0

private theorem kloostermanTerminalSchurKernel_Icc_le_interval
    (M N : ℕ) (b : ℕ → ℂ) (q r : ℕ) :
    kloostermanTerminalSchurKernel M (Finset.Icc 1 N) b q r ≤
      kloostermanIntervalTerminalSchurKernel M N b q r := by
  unfold kloostermanTerminalSchurKernel kloostermanIntervalTerminalSchurKernel
  by_cases hqr : q = r
  · simp [hqr]
  · rw [if_neg hqr, if_neg hqr]
    exact kloostermanTerminalSchurPairBudget_Icc_le_interval M q r N b

private theorem kloostermanTerminalSchurWeightEnergy_Icc_le_interval
    (M N : ℕ) (Q : Finset ℕ) (w b : ℕ → ℂ) :
    kloostermanTerminalSchurWeightEnergy M Q w (Finset.Icc 1 N) b ≤
      kloostermanIntervalTerminalSchurWeightEnergy M N Q w b := by
  unfold kloostermanTerminalSchurWeightEnergy
    kloostermanTerminalSchurRowBudget
    kloostermanIntervalTerminalSchurWeightEnergy
    kloostermanIntervalTerminalSchurRowBudget
  apply Finset.sum_le_sum
  intro q hq
  apply mul_le_mul_of_nonneg_left
  · exact Finset.sum_le_sum fun r hr =>
      kloostermanTerminalSchurKernel_Icc_le_interval M N b q r
  · positivity

/-- Full weighted terminal Gram receiver on the literal source interval, with source multiplicity
inserted before the exact Schur-row test.  Each squared modulus weight is charged only against its
own explicit interval-kernel row; no support injectivity or spectral estimate is assumed. -/
theorem norm_kloostermanDistinctModulusTerminalGramQuadratic_Icc_le_interval_schurWeightEnergy
    (M N : ℕ) (Q : Finset ℕ) (w b : ℕ → ℂ) :
    ‖kloostermanDistinctModulusTerminalGramQuadratic
        M Q w (Finset.Icc 1 N) b‖ ≤
      kloostermanIntervalTerminalSchurWeightEnergy M N Q w b := by
  exact (norm_kloostermanDistinctModulusTerminalGramQuadratic_le_schurWeightEnergy
    M Q w (Finset.Icc 1 N) b).trans
      (kloostermanTerminalSchurWeightEnergy_Icc_le_interval M N Q w b)

end

end RHTower.Sieve
