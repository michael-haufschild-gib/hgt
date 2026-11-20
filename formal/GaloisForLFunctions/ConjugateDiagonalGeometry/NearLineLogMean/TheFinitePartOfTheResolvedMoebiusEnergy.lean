import GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.TheIsolatedDiagonalOfTheShortMoebiusWindows
import GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.TheShortRatioEnergyBeyondTheDiagonalScale
import GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.TheConstantTermOfTheSquarefreeHarmonicDiagonal

/-!
# The finite part of the resolved Möbius energy

The finite part of ζ(s)/ζ(2s) at one gives a lower bound at every
resolved prefix, even inside an arbitrarily long section. At the fully
resolved cutoff the bound is attained up to O(1/√N). Above that length,
the independent error from overlapping sites is at most 4N/T. Thus
lengths as large as o(T log N) have the same leading logarithm.
-/

namespace GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.MoebiusGram
open Finset MeasureTheory Filter Topology _root_.RHTower _root_.RHTower.Sieve
noncomputable section

private theorem diagonal_nat (N : ℕ) :
    harmonicMoebiusDiagonal N = ∑ n ∈ Icc 1 N, mobiusRealCoefficient n^2/n := by
  simp only [harmonicMoebiusDiagonal,Nat.floor_natCast,mobiusRealCoefficient]

/-- A resolved prefix retains the full explicit squarefree finite part,
with its inverse-square-root error, regardless of all later coefficients. -/
theorem resolved_prefix_finite_part_envelope {M N : ℕ} (hm : 1 ≤ M) (hmn : M ≤ N)
    {T : ℝ} (hT : ((M+1 : ℕ) : ℝ) ≤ T) :
    squarefreeDensity*Real.log M+squarefreeHarmonicConstant-12*(M : ℝ)^(-(1/2 : ℝ)) ≤
      T*bandEnergy N T⁻¹ := by
  have ht := (Nat.cast_pos.mpr (Nat.succ_pos M)).trans_le hT
  have hh := (abs_le.mp (squarefree_harmonic_finite_part (X:=M) (by exact_mod_cast hm))).1
  rw [diagonal_nat] at hh
  rw [bandEnergy_isolated_prefix hm hmn (inv_nonneg.mpr ht.le)
      (inv_anti₀ (Nat.cast_pos.mpr (Nat.succ_pos M)) hT),
    mul_add,←mul_assoc,mul_inv_cancel₀ ht.ne',one_mul]
  exact le_add_of_le_of_nonneg (by linarith only [hh])
    (mul_nonneg ht.le (integral_nonneg fun _ => sq_nonneg _))

/-- At complete resolution the normalized energy attains the squarefree
logarithm and its zeta-derivative constant, with an explicit error. -/
theorem resolved_energy_finite_part {N : ℕ} (hn : 1 ≤ N) {T : ℝ} (ht : (N : ℝ) ≤ T) :
    |T*bandEnergy N T⁻¹-squarefreeDensity*Real.log N-squarefreeHarmonicConstant| ≤
      12*(N : ℝ)^(-(1/2 : ℝ)) := by
  have hp : (0 : ℝ) < N := Nat.cast_pos.mpr hn
  have ht' := hp.trans_le ht
  rw [bandEnergy_diagonal (inv_nonneg.mpr ht'.le) (inv_anti₀ hp ht),←mul_assoc,
    mul_inv_cancel₀ ht'.ne',one_mul,←diagonal_nat]
  exact squarefree_harmonic_finite_part (by exact_mod_cast hn)

/-- At every length, the departure from the same logarithm and finite
part is bounded by the sum of the counting and overlap errors. -/
theorem energy_finite_part_with_overlap {N : ℕ} (hn : 1 ≤ N) {T : ℝ} (ht : 2 ≤ T) :
    |T*bandEnergy N T⁻¹-squarefreeDensity*Real.log N-squarefreeHarmonicConstant| ≤
      4*(N : ℝ)/T+12*(N : ℝ)^(-(1/2 : ℝ)) := by
  have ha := normalized_energy_diagonal_error N ht
  rw [←diagonal_nat] at ha
  have hb := squarefree_harmonic_finite_part (X:=N) (by exact_mod_cast hn)
  calc
    _ = |(T*bandEnergy N T⁻¹-harmonicMoebiusDiagonal N) +
        (harmonicMoebiusDiagonal N-squarefreeDensity*Real.log N-squarefreeHarmonicConstant)| :=
      congrArg abs (by ring)
    _ ≤ _ := (abs_add_le _ _).trans (add_le_add ha hb)

/-- All lengths with N/T = o(log N) retain the full logarithmic main
term, including lengths that grow faster than the inverse bandwidth. -/
theorem energy_log_asymptotic_beyond_resolution (T : ℕ → ℝ) (ht : ∀ᶠ n : ℕ in atTop, 2 ≤ T n)
    (hscale : Tendsto (fun n : ℕ => ((n : ℝ)/T n)/Real.log n) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => (T n*bandEnergy n (T n)⁻¹)/Real.log n) atTop (𝓝 squarefreeDensity) := by
  let C := 12+|squarefreeHarmonicConstant|
  have hlog := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  have hz := (hscale.const_mul 4).add ((tendsto_inv_atTop_zero.comp hlog).const_mul C)
  simp only [mul_zero,add_zero] at hz
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero' (.of_forall fun _ => norm_nonneg _) _ hz
  filter_upwards [ht,eventually_ge_atTop (2 : ℕ)] with n hT hn
  have hr : (1 : ℝ)<n := by exact_mod_cast hn
  have hp := Real.log_pos hr
  have hn' : 1 ≤ n := by omega
  have hsmall : (n : ℝ)^(-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hr.le (by norm_num)
  have hb := energy_finite_part_with_overlap hn' hT
  have hab : |T n*bandEnergy n (T n)⁻¹-squarefreeDensity*Real.log n| ≤ 4*(n : ℝ)/T n+C := by
    have htri := abs_add_le (T n*bandEnergy n (T n)⁻¹-squarefreeDensity*Real.log n-squarefreeHarmonicConstant)
      squarefreeHarmonicConstant
    rw [sub_add_cancel] at htri
    dsimp only [C]
    linarith only [hb,htri,hsmall]
  change ‖(T n*bandEnergy n (T n)⁻¹)/Real.log n-squarefreeDensity‖ ≤ _
  rw [Real.norm_eq_abs,show T n*bandEnergy n (T n)⁻¹/Real.log n-squarefreeDensity =
      (T n*bandEnergy n (T n)⁻¹-squarefreeDensity*Real.log n)/Real.log n by
    rw [sub_div,mul_div_cancel_right₀ _ hp.ne'],abs_div,abs_of_pos hp]
  refine (div_le_div_of_nonneg_right hab hp.le).trans_eq ?_
  dsimp only [Function.comp_apply]
  ring

end
end GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.MoebiusGram
