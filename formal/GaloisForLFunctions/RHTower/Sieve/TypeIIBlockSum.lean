import GaloisForLFunctions.RHTower.Sieve.BlockCountAssembly

/-!
# The type-II bilinear form on one dyadic block, in both orientations

Cauchy--Schwarz may be applied to either variable of the block form.  Applying it to the long
variable makes the diagonal proportional to the block length; applying it to the short variable
makes it proportional to the length of the effective short interval.  Which of the two is better
depends on the block, so both are needed, and the dyadic decomposition allows the choice to be made
block by block.
-/

namespace RHTower.Sieve

open Finset ArithmeticFunction RHTower

noncomputable section

/-- The type-II bilinear form restricted to a block of the long variable. -/
def maskedBlockSum (T r : ℝ) (A B L P Q : ℕ) (a b : ℕ → ℝ) : ℂ :=
  ∑ d ∈ Finset.Ico P Q, ((a d : ℝ) : ℂ)
    * ∑ m ∈ Finset.Icc 1 L, ((b m : ℝ) : ℂ) * maskedNdExp T r A B d m

/-- **The type-II piece is the sum of its dyadic block forms.** -/
theorem norm_typeII_piece_le_sum_blockSums {A B L : ℕ} (hA : 1 ≤ A) (hB : 1 ≤ B) (hBL : B - 1 ≤ L)
    (T r : ℝ) (U V : ℕ) :
    ‖∑ n ∈ Finset.Ico A B, (((typeIILong U * typeIIShort V) n : ℝ) : ℂ) * ndPhaseExp T r n‖
      ≤ ∑ j ∈ Finset.range (Nat.log 2 L + 1),
          ‖maskedBlockSum T r A B L (2 ^ j) (min (2 ^ (j + 1)) (L + 1))
            (fun d => typeIILong U d) (fun m => typeIIShort V m)‖ := by
  rw [sum_typeII_piece_eq hA hB hBL T r U V]
  refine le_trans (norm_sum_Icc_le_sum_dyadic_blocks
    (fun d => ((typeIILong U d : ℝ) : ℂ)
      * ∑ m ∈ Finset.Icc 1 L, ((typeIIShort V m : ℝ) : ℂ) * maskedNdExp T r A B d m)) ?_
  refine Finset.sum_le_sum fun j _ => ?_
  rw [dyadic_block_eq_Ico]
  simp only [maskedBlockSum]
  exact le_rfl

/-- **Cauchy--Schwarz on the long variable.** -/
theorem norm_maskedBlockSum_sq_le (T r : ℝ) (A B L P Q : ℕ) (a b : ℕ → ℝ) :
    ‖maskedBlockSum T r A B L P Q a b‖ ^ (2 : ℕ)
      ≤ (∑ d ∈ Finset.Ico P Q, |a d| ^ (2 : ℕ))
        * ∑ m₁ ∈ Finset.Icc 1 L, ∑ m₂ ∈ Finset.Icc 1 L, |b m₁| * |b m₂|
            * ‖∑ d ∈ Finset.Ico P Q,
                maskedNdExp T r A B d m₁ * (starRingEnd ℂ) (maskedNdExp T r A B d m₂)‖ := by
  have h := norm_typeII_masked_sq_le T r A B P Q (Finset.Icc 1 L)
    (fun d => ((a d : ℝ) : ℂ)) (fun m => ((b m : ℝ) : ℂ))
  have hnorm : ∀ x : ℝ, ‖((x : ℝ) : ℂ)‖ = |x| := fun x => by
    rw [Complex.norm_real, Real.norm_eq_abs]
  simpa only [hnorm, maskedBlockSum] using h

/-- The fibre of a block member lies in the effective short interval. -/
theorem maskedNdExp_eq_zero_of_not_mem_eff {A B P Q : ℕ} (hP : 1 ≤ P) (hQ : 2 ≤ Q) (T r : ℝ)
    {d m : ℕ} (hd : d ∈ Finset.Ico P Q)
    (hm : m ∉ Finset.Ico (effLow A Q) (effHigh B P + 1)) :
    maskedNdExp T r A B d m = 0 := by
  classical
  rw [maskedNdExp, if_neg]
  intro hmem
  refine hm ?_
  rw [fibreIco, Finset.mem_Ico] at hmem
  rw [Finset.mem_Ico] at hd ⊢
  rw [effLow, effHigh]
  constructor
  · exact le_trans (Nat.succ_le_succ (Nat.div_le_div_left (by omega) (by omega))) hmem.1
  · have := hmem.2
    have hdiv : (B - 1) / d ≤ (B - 1) / P := Nat.div_le_div_left hd.1 (by omega)
    omega

/-- **The block form, with the roles of the two variables exchanged.** -/
theorem maskedBlockSum_eq_swap {A B L P Q : ℕ} (hA : 1 ≤ A) (hB : 1 ≤ B) (hP : 1 ≤ P)
    (hQ : 2 ≤ Q) (hBL : B - 1 ≤ L) (T r : ℝ) (a b : ℕ → ℝ) :
    maskedBlockSum T r A B L P Q a b
      = ∑ m ∈ Finset.Ico (effLow A Q) (effHigh B P + 1), ((b m : ℝ) : ℂ)
          * ∑ d ∈ Finset.Ico P Q, ((a d : ℝ) : ℂ) * maskedNdExp T r A B m d := by
  classical
  have hsub : Finset.Ico (effLow A Q) (effHigh B P + 1) ⊆ Finset.Icc 1 L := by
    intro m hm
    rw [Finset.mem_Ico] at hm
    rw [Finset.mem_Icc]
    have hlow : 1 ≤ effLow A Q := one_le_effLow A Q
    have hhigh : effHigh B P ≤ L := by
      rw [effHigh]
      exact le_trans (Nat.div_le_self _ _) hBL
    omega
  have hinner : ∀ d ∈ Finset.Ico P Q,
      (∑ m ∈ Finset.Icc 1 L, ((b m : ℝ) : ℂ) * maskedNdExp T r A B d m)
        = ∑ m ∈ Finset.Ico (effLow A Q) (effHigh B P + 1),
            ((b m : ℝ) : ℂ) * maskedNdExp T r A B d m := by
    intro d hd
    refine (Finset.sum_subset hsub fun m _ hm => ?_).symm
    rw [maskedNdExp_eq_zero_of_not_mem_eff hP hQ T r hd hm, mul_zero]
  rw [maskedBlockSum, Finset.sum_congr rfl (fun d hd => by rw [hinner d hd])]
  have hexp : ∀ d ∈ Finset.Ico P Q,
      (((a d : ℝ) : ℂ) * ∑ m ∈ Finset.Ico (effLow A Q) (effHigh B P + 1),
          ((b m : ℝ) : ℂ) * maskedNdExp T r A B d m)
        = ∑ m ∈ Finset.Ico (effLow A Q) (effHigh B P + 1),
            ((b m : ℝ) : ℂ) * (((a d : ℝ) : ℂ) * maskedNdExp T r A B d m) := by
    intro d _
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun m _ => by ring
  rw [Finset.sum_congr rfl hexp, Finset.sum_comm]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  rw [Finset.mem_Ico] at hm hd
  have hd1 : 1 ≤ d := le_trans hP hd.1
  have hm1 : 1 ≤ m := le_trans (one_le_effLow A Q) hm.1
  rw [maskedNdExp_symm hA hB T r hd1 hm1]

/-- **Cauchy--Schwarz on the short variable.** -/
theorem norm_maskedBlockSum_sq_le_swap {A B L P Q : ℕ} (hA : 1 ≤ A) (hB : 1 ≤ B) (hP : 1 ≤ P)
    (hQ : 2 ≤ Q) (hBL : B - 1 ≤ L) (T r : ℝ) (a b : ℕ → ℝ) :
    ‖maskedBlockSum T r A B L P Q a b‖ ^ (2 : ℕ)
      ≤ (∑ m ∈ Finset.Ico (effLow A Q) (effHigh B P + 1), |b m| ^ (2 : ℕ))
        * ∑ d₁ ∈ Finset.Ico P Q, ∑ d₂ ∈ Finset.Ico P Q, |a d₁| * |a d₂|
            * ‖∑ m ∈ Finset.Ico (effLow A Q) (effHigh B P + 1),
                maskedNdExp T r A B m d₁ * (starRingEnd ℂ) (maskedNdExp T r A B m d₂)‖ := by
  have h := norm_typeII_masked_sq_le T r A B (effLow A Q) (effHigh B P + 1) (Finset.Ico P Q)
    (fun m => ((b m : ℝ) : ℂ)) (fun d => ((a d : ℝ) : ℂ))
  have hnorm : ∀ x : ℝ, ‖((x : ℝ) : ℂ)‖ = |x| := fun x => by
    rw [Complex.norm_real, Real.norm_eq_abs]
  rw [maskedBlockSum_eq_swap hA hB hP hQ hBL T r a b]
  simpa only [hnorm] using h

end

end RHTower.Sieve
