import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.OccupationProbabilities.HeatPair

/-! # The relative partition at one as an ordinary rank-one trace -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open ContinuousLinearMap InnerProductSpace _root_.RHTower Filter Topology
open scoped InnerProductSpace

/-- Total diagonal weight on the first N vectors of an orthonormal family. -/
def prefixDiagonal (T : GasOp) (e : ℕ → Gas) (N : ℕ) := ∑ i ∈ Finset.range N, (inner ℂ (e i) (T (e i))).re

private theorem prefix_le (T : GasOp) (hT : IsCompactOperator T) (hp : T.IsPositive)
    (e : ℕ → Gas) (he : Orthonormal ℂ e) (N : ℕ) :
    prefixDiagonal T e N ≤ ∑ i ∈ Finset.range N, singVal T i :=
  sum_re_inner_le_sum_singVal hT ((nonneg_iff_isPositive _).mpr hp) e
    (fun n => Or.inr (he.1 n)) (fun i j hij => he.2 hij) _ (by simp)

private theorem prefix_eigen {T : GasOp} {e : ℕ → Gas} (he : Orthonormal ℂ e)
    {b : ℕ → ℝ} (h : ∀ n, T (e n) = (b n:ℂ) • e n) (N : ℕ) :
    prefixDiagonal T e N = ∑ i ∈ Finset.range N, b i := by
  apply Finset.sum_congr rfl
  intro n _
  rw [h n,inner_smul_right,inner_self_eq_norm_sq_to_K,he.1 n]
  simp

private theorem prefix_sub (A B : GasOp) (e : ℕ → Gas) (N : ℕ) :
    prefixDiagonal (A-B) e N = prefixDiagonal A e N-prefixDiagonal B e N := by
  simp only [prefixDiagonal,sub_apply,inner_sub_right,Complex.sub_re,Finset.sum_sub_distrib]

private theorem rank_prefix_limit {ι : Type*} (e : HilbertBasis ι ℂ Gas) (x : Gas) :
    HasSum (fun n => (inner ℂ (e n) (rankOne ℂ x x (e n))).re) (‖x‖^2) := by
  have h := (e.hasSum_inner_mul_inner x x).mapL Complex.reCLM
  change HasSum (fun n => (inner ℂ x (e n)*inner ℂ (e n) x).re) (inner ℂ x x).re at h
  rw [show (inner ℂ x x).re = ‖x‖^2 from inner_self_eq_norm_sq (𝕜 := ℂ) x] at h
  simpa only [rankOne_apply,inner_smul_right] using h

/-- The rank-one trace trapped between the spectral sums in the two eigenbases. -/
theorem harmonic_prefix_bounds (v : MissingWave) (e : HilbertBasis ℕ ℂ Gas)
    (he : ∀ n, survivingHeat v (e n) = ((missingSpectrum v n).val:ℂ) • e n) (N : ℕ) :
    let R := rankOne ℂ (defectVector v) (defectVector v)
    let gap := ∑ n ∈ Finset.range N, (occupationWeight n-(missingSpectrum v n).val)
    prefixDiagonal R e N ≤ gap ∧ gap ≤ prefixDiagonal R occupationMode N := by
  dsimp only
  have hA := prefix_le squareHeat.val squareHeat.property.2.isCompactOperator nativeHeat_positive e e.orthonormal N
  have hB := prefix_le (survivingHeat v) (survivingHeat_hs v).isCompactOperator (projected_square_positive _) occupationMode occupationMode_orthonormal N
  simp only [nativeHeat_singVal] at hA
  simp only [survivingHeat_singVal] at hB
  have hl := prefix_eigen e.orthonormal he N
  rw [survivingHeat_eq,prefix_sub] at hl hB
  rw [prefix_eigen occupationMode_orthonormal nativeHeat_eigen N] at hB
  rw [Finset.sum_sub_distrib]
  exact ⟨by linarith only [hl,hA],by linarith only [hB]⟩

/-- Convergence to the positive trace of the single removed outer product, although both ambient harmonic traces diverge. -/
theorem harmonic_gap_tendsto (v : MissingWave) :
    Tendsto (fun N => ∑ n ∈ Finset.range N, (occupationWeight n-(missingSpectrum v n).val)) atTop (𝓝 (‖defectVector v‖^2)) := by
  obtain ⟨e,he⟩ := survivingHeat_basis v
  let d : ℕ ≃ ℕ+ := Equiv.ofBijective number ⟨number_injective,number_surjective⟩
  have h := d.hasSum_iff.mpr (rank_prefix_limit (HilbertSchmidt.lpBasis ℕ+) (defectVector v))
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le (rank_prefix_limit e _).tendsto_sum_nat h.tendsto_sum_nat
    (fun N => (harmonic_prefix_bounds v e he N).1) (fun N => (harmonic_prefix_bounds v e he N).2)

/-- The regular relative partition at the zeta pole is the first normalized occupation moment. -/
theorem omissionPartition_pole (v : MissingWave) :
    omissionPartition v 1 = (firstMoment v.val:ℂ) := by
  have hz : 0 < (1:ℂ).re := by norm_num
  have hs := (summable_complexDrop (missingSpectrum v) hz).hasSum.tendsto_sum_nat
  have he : Tendsto (fun N => ((∑ n ∈ Finset.range N, (occupationWeight n-(missingSpectrum v n).val):ℝ):ℂ)) atTop
      (𝓝 ((‖defectVector v‖^2:ℝ):ℂ)) := Complex.continuous_ofReal.continuousAt.tendsto.comp (harmonic_gap_tendsto v)
  rw [← defectVector_norm_sq v]
  apply tendsto_nhds_unique hs
  simpa only [complexDrop,Complex.cpow_one,Complex.ofReal_sum,Complex.ofReal_sub] using he

#print axioms harmonic_prefix_bounds
#print axioms harmonic_gap_tendsto
#print axioms omissionPartition_pole

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
