import GaloisForLFunctions.RHTower.EvenSectorWeightGrowth
import GaloisForLFunctions.RHTower.WeilOddBlindPoleWeightWindow

/-!
# Growth of weights that are Weil-positive on odd tests

**Theorem** (`exists_abs_le_of_weilPositiveOddAt`).  If real weights `lam` make the Weil functional
(pole weight `1`) nonnegative on every autocorrelation of an odd compactly supported `C²` test,
then `|lam(n)| ≤ C √n (1 + log n)` for every `n ≥ 2`.

The bound is two-sided although odd positivity is a one-sided condition at every node.  The odd
two-bump tests at the node `log n` (`oddPlus`, `oddMinus`) reach it with node value `+2‖φ₋‖²/√n`
and `−2‖φ₊‖²/√n`, where `φ₋`, `φ₊` are the odd and even profiles of the node bump, a dilate of a
fixed bump by `m = 2n + 3`.

Proof.  Both tests are signed sums of four (resp. two) translates of the node bump with total
coefficient mass `4`, so `‖f̂(r)‖ ≤ 4‖φ̂(r)‖` on the real line and
`‖f̂(σi)‖ ≤ 4 e^{(log n)/4 + 1/4} P₀/m` for `|σ| ≤ 1/2`.  The archimedean and pole parts are then
bounded exactly as for the even node tests (`abs_weilArchRe_node_le`), and dividing the Weil
inequality by the node value `≍ J₀/(m√n)` gives `±lam(n) ≤ C(n/m + √n(1 + log m))`.

Reading.  As for even tests, an imaginary frequency `ia` of the odd functional would make the
weights grow like `n^{a − 1/2}`, so only `|a| ≤ 1` can occur.  This is the growth input for the
odd-sector uniqueness problem (odd positivity ⟹ `lam = Λ`).
-/

open Complex MeasureTheory Set Finsupp Zeta23
open scoped ComplexConjugate

noncomputable section

namespace RHTower.OddSector

open WeilOneSided SeparatedBump EvenSector WeilPoleWeight

/-! ## The odd node tests as signed sums of translates of the node bump -/

theorem oddPlusC_eq (j : ℕ) :
    (fun u => (oddPlusFn j u : ℂ)) = fun u => ∑ k : Fin 4, (![1, -1, 1, -1] k : ℂ) *
      (fun v => (nodeBump j v : ℂ)) (u - ![Real.log j / 2 + 2 * (nodeBump j).rOut,
        Real.log j / 2 - 2 * (nodeBump j).rOut, -(Real.log j / 2) + 2 * (nodeBump j).rOut,
        -(Real.log j / 2) - 2 * (nodeBump j).rOut] k) := by
  funext u
  rw [Fin.sum_univ_four]
  simp only [oddPlusFn, bumpSum, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    oddProfile_eq]
  simp
  ring_nf

theorem oddMinusC_eq (j : ℕ) :
    (fun u => (oddMinusFn j u : ℂ)) = fun u => ∑ k : Fin 2, (![2, -2] k : ℂ) *
      (fun v => (nodeBump j v : ℂ)) (u - ![Real.log j / 2, -(Real.log j / 2)] k) := by
  funext u
  simp only [oddMinusFn, bumpSum, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    evenProfile_eq]
  push_cast
  ring

theorem norm_paperFT_oddPlus_le (j : ℕ) (r : ℝ) :
    ‖paperFT (fun u => (oddPlusFn j u : ℂ)) r‖ ≤
      4 * ‖paperFT (fun u => (nodeBump j u : ℂ)) r‖ := by
  rw [oddPlusC_eq]
  refine (norm_paperFT_sum_translate_le Finset.univ _ _ (continuous_nodeBumpC j)
    (hasCompactSupport_nodeBumpC j) r).trans (le_of_eq ?_)
  simp [Fin.sum_univ_four]
  norm_num

theorem norm_paperFT_oddMinus_le (j : ℕ) (r : ℝ) :
    ‖paperFT (fun u => (oddMinusFn j u : ℂ)) r‖ ≤
      4 * ‖paperFT (fun u => (nodeBump j u : ℂ)) r‖ := by
  rw [oddMinusC_eq]
  refine (norm_paperFT_sum_translate_le Finset.univ _ _ (continuous_nodeBumpC j)
    (hasCompactSupport_nodeBumpC j) r).trans (le_of_eq ?_)
  simp [Fin.sum_univ_two]
  norm_num

/-- The pole bound for the odd node tests: `‖f̂(σ i)‖ ≤ 4 e^{(log j)/4 + 1/4} P₀ / m`. -/
theorem norm_paperFT_oddPlus_imag_le (j : ℕ) {σ : ℝ} (hσ : |σ| ≤ 1 / 2) :
    ‖paperFT (fun u => (oddPlusFn j u : ℂ)) ((σ : ℂ) * I)‖ ≤
      4 * Real.exp (Real.log j / 4 + 1 / 4) * ((nodeScale j)⁻¹ * bumpPoleConst) := by
  rw [oddPlusC_eq]
  have hρ := nodeBump_rOut_le j
  have hρ0 := (nodeBump j).rOut_pos
  have hl : 0 ≤ Real.log j := Real.log_natCast_nonneg j
  have hX : ∀ k ∈ (Finset.univ : Finset (Fin 4)),
      |![Real.log j / 2 + 2 * (nodeBump j).rOut, Real.log j / 2 - 2 * (nodeBump j).rOut,
        -(Real.log j / 2) + 2 * (nodeBump j).rOut, -(Real.log j / 2) - 2 * (nodeBump j).rOut] k| ≤
        Real.log j / 2 + 1 / 2 := by
    intro k _
    fin_cases k <;> simp <;> rw [abs_le] <;> constructor <;> linarith
  refine (norm_paperFT_sum_translate_imag_le Finset.univ _ _ (continuous_nodeBumpC j)
    (hasCompactSupport_nodeBumpC j) hσ hX).trans ?_
  have hs : (∑ k : Fin 4, ‖(![1, -1, 1, -1] k : ℂ)‖) = 4 := by simp [Fin.sum_univ_four]; norm_num
  rw [hs, show (Real.log j / 2 + 1 / 2) / 2 = Real.log j / 4 + 1 / 4 by ring]
  exact mul_le_mul_of_nonneg_left (norm_paperFT_nodeBump_imag_le j hσ) (by positivity)

theorem norm_paperFT_oddMinus_imag_le (j : ℕ) {σ : ℝ} (hσ : |σ| ≤ 1 / 2) :
    ‖paperFT (fun u => (oddMinusFn j u : ℂ)) ((σ : ℂ) * I)‖ ≤
      4 * Real.exp (Real.log j / 4 + 1 / 4) * ((nodeScale j)⁻¹ * bumpPoleConst) := by
  rw [oddMinusC_eq]
  have hX : ∀ k ∈ (Finset.univ : Finset (Fin 2)),
      |![Real.log j / 2, -(Real.log j / 2)] k| ≤ Real.log j / 2 + 1 / 2 := by
    intro k _
    have hl : 0 ≤ Real.log j := Real.log_natCast_nonneg j
    fin_cases k <;> simp [abs_of_nonneg (by linarith : 0 ≤ Real.log j / 2)]
  refine (norm_paperFT_sum_translate_imag_le Finset.univ _ _ (continuous_nodeBumpC j)
    (hasCompactSupport_nodeBumpC j) hσ hX).trans ?_
  have hs : (∑ k : Fin 2, ‖(![2, -2] k : ℂ)‖) = 4 := by simp [Fin.sum_univ_two]; norm_num
  rw [hs, show (Real.log j / 2 + 1 / 2) / 2 = Real.log j / 4 + 1 / 4 by ring]
  exact mul_le_mul_of_nonneg_left (norm_paperFT_nodeBump_imag_le j hσ) (by positivity)

/-! ## The growth bound -/

/-- **Odd-positive weights grow at most like `√n log n`.** -/
theorem exists_abs_le_of_weilPositiveOddAt {lam : ℕ → ℝ} (h : WeilPositiveOddAt 1 lam) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 2 ≤ n → |lam n| ≤ C * Real.sqrt n * (1 + Real.log n) := by
  have hJ : 0 < ∫ u, narrowBump 0 u ^ 2 := integral_narrowBump_sq_pos 0
  refine ⟨16 * Real.exp (1 / 2) * bumpPoleConst ^ 2 / (∫ u, narrowBump 0 u ^ 2) +
    4 * ((|gammaLogConst| + 3) * bumpMassConst + bumpLogConst) /
      (Real.pi * ∫ u, narrowBump 0 u ^ 2),
    add_nonneg (by positivity)
      (div_nonneg (by have := bumpMassConst_nonneg; have := bumpLogConst_nonneg; positivity)
        (by positivity)), fun n hn => ?_⟩
  have hn1 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hsq : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by linarith)
  have hm0 := nodeScale_pos n
  have hmeq : nodeScale n = 2 * (n : ℝ) + 3 := rfl
  set Bd := 32 * Real.exp (Real.log n / 2 + 1 / 2) * bumpPoleConst ^ 2 / nodeScale n ^ 2 +
    8 / (Real.pi * nodeScale n) *
      ((gammaLogConst + Real.log (nodeScale n)) * bumpMassConst + bumpLogConst) with hBd
  have hWp := h (oddPlus n).1.1 (oddPlus n).1.2.1 (oddPlus n).1.2.2 (oddPlus n).2
  rw [re_weilPoleWeightFunctional_eq 1 lam (oddPlus n).1,
    logVector_oddPlus ⟨n, hn⟩, Finsupp.linearCombination_single] at hWp
  have hWm := h (oddMinus n).1.1 (oddMinus n).1.2.1 (oddMinus n).1.2.2 (oddMinus n).2
  rw [re_weilPoleWeightFunctional_eq 1 lam (oddMinus n).1,
    logVector_oddMinus ⟨n, hn⟩, Finsupp.linearCombination_single] at hWm
  simp only [poleWeightArchRe, sub_self, zero_mul, add_zero, smul_eq_mul] at hWp hWm
  have hAp : |weilArchRe (EF.weilTest (oddPlus n).1.1 (oddPlus n).1.1)| ≤ Bd :=
    abs_weilArchRe_node_le n (oddPlus n).1.2.1.continuous (oddPlus n).1.2.2
      (norm_paperFT_oddPlus_le n) fun σ hσ => norm_paperFT_oddPlus_imag_le n hσ
  have hAm : |weilArchRe (EF.weilTest (oddMinus n).1.1 (oddMinus n).1.1)| ≤ Bd :=
    abs_weilArchRe_node_le n (oddMinus n).1.2.1.continuous (oddMinus n).1.2.2
      (norm_paperFT_oddMinus_le n) fun σ hσ => norm_paperFT_oddMinus_imag_le n hσ
  have hBd0 : 0 ≤ Bd := (abs_nonneg _).trans hAp
  set c₀ := 2 * ((nodeScale n)⁻¹ * ∫ u, narrowBump 0 u ^ 2) / Real.sqrt n with hc₀
  have hc₀0 : 0 < c₀ := by positivity
  -- the upper bound, from the test with positive node value
  have hcp : c₀ ≤ 2 * (∫ u, oddProfile n u ^ 2) / Real.sqrt n :=
    div_le_div_of_nonneg_right (by linarith [le_integral_oddProfile_sq n]) hsq.le
  have hup : (lam n) ≤ Bd / c₀ :=
    (le_div_of_node (lt_of_lt_of_le hc₀0 hcp) hWp hAp).trans
      (div_le_div_of_nonneg_left hBd0 hc₀0 hcp)
  -- the lower bound, from the test with negative node value
  have hcm : c₀ ≤ 2 * (∫ u, evenProfile n u ^ 2) / Real.sqrt n := by
    rw [integral_evenProfile_sq_eq]
    refine div_le_div_of_nonneg_right ?_ hsq.le
    have : 0 ≤ (nodeScale n)⁻¹ * ∫ u, narrowBump 0 u ^ 2 := by positivity
    linarith
  have hWm' : 0 ≤ weilArchRe (EF.weilTest (oddMinus n).1.1 (oddMinus n).1.1) -
      2 * (∫ u, evenProfile n u ^ 2) / Real.sqrt n * (-lam n) := by linarith
  have hlo : -lam n ≤ Bd / c₀ :=
    (le_div_of_node (lt_of_lt_of_le hc₀0 hcm) hWm' hAm).trans
      (div_le_div_of_nonneg_left hBd0 hc₀0 hcm)
  have hfin : Bd / c₀ = Bd * (Real.sqrt n * nodeScale n / (2 * ∫ u, narrowBump 0 u ^ 2)) := by
    rw [hc₀]
    field_simp
  have hkey := node_bound_le (n := n) (J₀ := ∫ u, narrowBump 0 u ^ 2) (P := bumpPoleConst)
    (K := gammaLogConst) (I₀ := bumpMassConst) (I₁ := bumpLogConst) hn1 hJ bumpMassConst_nonneg
    bumpLogConst_nonneg
  rw [← hmeq, ← hBd, ← hfin] at hkey
  rw [abs_le]
  constructor <;> linarith

end RHTower.OddSector

end
