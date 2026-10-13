import GaloisForLFunctions.RHTower.DirichletFamilyPrimeMeanSquare
import GaloisForLFunctions.RHTower.ThmEUniformCoprimeSums
import GaloisForLFunctions.RHTower.FamilyTaperBridge

/-!
# The family prime mean square in Alpöge–Furman's normalisation

Summed over all characters modulo `q`, the bilinear form `𝓜[P_χ, P_χ]` of the prime polynomials is its
diagonal `φ(q)/(2π²) Σ_{(n,q)=1} a_n² A⁻(log n, log n)` up to the residue-class Montgomery–Vaughan error
(`sum_Mform_PXc_dirichlet_sub_diag_le`).  With `A⁻(y, y) ≤ T ∫ Φ² cos(xy) + ∫ Φ²|x| = 2πT g(y) + ∫ Φ²|x|` this
gives

`Σ_χ 𝓜[P_χ, P_χ] ≤ φ(q) (T/π) Σ_{n ≤ X, (n,q)=1} Λ(n)²/n · g(log n)
                    + φ(q)/(2π²) (Σ a_n²) ∫ Φ²|x| + (off-diagonal error)`          (`family_PP_le`),

and the coprime sum is at most `L³/6 + (B + K log²(log q + 8)) L²` at every bandwidth
(`sumA2gCoprime_upper_uniform_wide`).
-/

open MeasureTheory Real Set Zeta23 Zeta23.ThmE Zeta23.PrimeSide
open scoped ArithmeticFunction

noncomputable section

namespace RHTower

variable {cϱ : ℝ} {p : Setting} {F : LocalFun}

theorem two_le_X_of_coreW (hF : LocalHypsCoreW cϱ p F) : 2 ≤ p.X := by
  have h8 := hF.eight_le_L
  have : p.X = Real.exp p.L := rfl
  rw [this]
  linarith [Real.add_one_le_exp p.L]

/-- **The coprime sandwich, upper half, at every bandwidth.** -/
theorem sumA2gCoprime_upper_uniform_wide :
    ∃ B K : ℝ, 0 ≤ B ∧ 0 ≤ K ∧ ∀ q : ℕ, 1 ≤ q → ∀ (p : Setting) (F : LocalFun),
      LocalHypsCoreW cϱ p F →
        sumA2gCoprime q p.X F.g ≤ p.L ^ 3 / 6 + (B + K * Real.log (Real.log q + 8) ^ 2) * p.L ^ 2 := by
  obtain ⟨B, K, hB, hK, hC⟩ := coprime_cheb2b_uniform
  refine ⟨B, K, hB, hK, fun q hq p F hF => ?_⟩
  have hX2 := two_le_X_of_coreW hF
  have hX1 : (1:ℝ) ≤ p.X := by linarith
  have h1 : sumA2gCoprime q p.X F.g
      ≤ ∑ n ∈ (Finset.Ioc 0 ⌊p.X⌋₊).filter (fun n => Nat.Coprime n q),
          (Λ n : ℝ) ^ 2 / n * (p.L - Real.log n) := by
    unfold sumA2gCoprime
    refine Finset.sum_le_sum fun n hn => ?_
    have hn' : n ∈ primeRange p.X := (Finset.mem_filter.mp hn).1
    refine mul_le_mul_of_nonneg_left ?_ (a2_nonneg n)
    calc F.g (Real.log n) ≤ F.Aphi (Real.log n) := hF.g_le_Aphi _
      _ ≤ max (p.L - |Real.log n|) 0 := hF.Aphi_le _
      _ = p.L - Real.log n := by
          rw [abs_of_nonneg (log_nonneg_of_mem_primeRange hn'), max_eq_left]
          have := log_le_of_mem_primeRange hX1 hn'
          rw [p.log_X] at this; linarith
  have h2 := hC q hq p.X hX2
  rw [p.log_X] at h2
  have h3 := (abs_le.mp h2).2
  linarith

theorem sameUnitClass_self (q n : ℕ) [NeZero q] :
    sameUnitClass q n n = if Nat.Coprime n q then 1 else 0 := by
  unfold sameUnitClass
  by_cases h : Nat.Coprime n q
  · rw [if_pos ((ZMod.isUnit_iff_coprime n q).mpr h |> fun hu => ⟨hu, rfl⟩), if_pos h]
  · have : ¬ (IsUnit (n : ZMod q) ∧ (n : ZMod q) = n) := fun h' =>
      h ((ZMod.isUnit_iff_coprime n q).mp h'.1)
    rw [if_neg this, if_neg h]

/-- **The family prime mean square, concrete form.** -/
theorem family_PP_le {C : ℝ} (hMV : Zeta23.MVHilbert C) (hC : 0 ≤ C) {q : ℕ} [NeZero q]
    (hF : LocalHypsCoreW cϱ p F) (hT : 0 ≤ p.T) :
    ∑ χ : DirichletCharacter ℂ q, Mform F.Phi p.T (PXc (fun n => χ n) p.X) (PXc (fun n => χ n) p.X)
      ≤ (q.totient : ℝ) * (p.T / π * sumA2gCoprime q p.X F.g)
        + (q.totient : ℝ) / (2 * π ^ 2) * ((∑ n ∈ primeRange p.X, acoef n ^ 2) * ∫ x, F.Phi x ^ 2 * |x|)
        + (q.totient : ℝ) / (2 * π ^ 2) * ((∫ x, F.Phi x ^ 2) / q
          * (8 * C + 2 + 2 * Real.log ((⌊p.X⌋₊ : ℝ) + 1))
          * ∑ n ∈ primeRange p.X, acoef n ^ 2 * ((n : ℝ) + q)) := by
  classical
  have hΦ : Continuous F.Phi := hF.Phi_contDiff.continuous
  have h := sum_Mform_PXc_dirichlet_sub_diag_le hMV hC (q := q) hT hΦ hF.Phi_sq_integrable p.X
  have hK0 : 0 ≤ (q.totient : ℝ) / (2 * π ^ 2) := by positivity
  set W := ∫ x, F.Phi x ^ 2 * |x| with hW
  have hW0 : 0 ≤ W := integral_nonneg fun x => by positivity
  have hdiag : ∑ n ∈ primeRange p.X, sameUnitClass q n n * acoef n ^ 2
        * Aminus F.Phi p.T (Real.log n) (Real.log n)
      ≤ 2 * π * p.T * sumA2gCoprime q p.X F.g + (∑ n ∈ primeRange p.X, acoef n ^ 2) * W := by
    have hpt : ∀ n ∈ primeRange p.X, sameUnitClass q n n * acoef n ^ 2
          * Aminus F.Phi p.T (Real.log n) (Real.log n)
        ≤ sameUnitClass q n n * acoef n ^ 2 * (2 * π * p.T * F.g (Real.log n)) + acoef n ^ 2 * W := by
      intro n _
      have hA := abs_Aminus_diag_sub_le hT hΦ hF.Phi_sq_integrable hF.Phi_sq_mul_abs_integrable
        (Real.log n)
      rw [hF.Phi_sq_fourier] at hA
      have hA' : Aminus F.Phi p.T (Real.log n) (Real.log n) ≤ 2 * π * p.T * F.g (Real.log n) + W := by
        have := (abs_le.mp hA).2
        have e : p.T * (2 * π * F.g (Real.log n)) = 2 * π * p.T * F.g (Real.log n) := by ring
        linarith
      have hs0 : 0 ≤ sameUnitClass q n n := by unfold sameUnitClass; split_ifs <;> norm_num
      have hs1 : sameUnitClass q n n ≤ 1 := by unfold sameUnitClass; split_ifs <;> norm_num
      have ha2 : 0 ≤ acoef n ^ 2 := sq_nonneg _
      have h1 : sameUnitClass q n n * acoef n ^ 2 * Aminus F.Phi p.T (Real.log n) (Real.log n)
          ≤ sameUnitClass q n n * acoef n ^ 2 * (2 * π * p.T * F.g (Real.log n) + W) :=
        mul_le_mul_of_nonneg_left hA' (mul_nonneg hs0 ha2)
      have h2 : sameUnitClass q n n * acoef n ^ 2 * W ≤ acoef n ^ 2 * W := by
        have := mul_le_mul_of_nonneg_right hs1 (mul_nonneg ha2 hW0)
        linarith
      nlinarith
    refine (Finset.sum_le_sum hpt).trans (le_of_eq ?_)
    rw [Finset.sum_add_distrib, ← Finset.sum_mul]
    congr 1
    unfold sumA2gCoprime primeRange
    rw [Finset.mul_sum, Finset.sum_filter]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [sameUnitClass_self, acoef_sq]
    split_ifs <;> ring
  have hup := (abs_le.mp h).2
  have hstep : (q.totient : ℝ) / (2 * π ^ 2) *
      ∑ n ∈ primeRange p.X, sameUnitClass q n n * acoef n ^ 2 * Aminus F.Phi p.T (Real.log n) (Real.log n)
      ≤ (q.totient : ℝ) * (p.T / π * sumA2gCoprime q p.X F.g)
        + (q.totient : ℝ) / (2 * π ^ 2) * ((∑ n ∈ primeRange p.X, acoef n ^ 2) * W) := by
    have h1 := mul_le_mul_of_nonneg_left hdiag hK0
    have e : (q.totient : ℝ) / (2 * π ^ 2) * (2 * π * p.T * sumA2gCoprime q p.X F.g)
        = (q.totient : ℝ) * (p.T / π * sumA2gCoprime q p.X F.g) := by
      field_simp
    rw [mul_add, e] at h1
    exact h1
  linarith

end RHTower
