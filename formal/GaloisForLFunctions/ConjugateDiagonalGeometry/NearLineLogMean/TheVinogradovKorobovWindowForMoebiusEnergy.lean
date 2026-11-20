import GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.PoissonEnergyOfTheMertensPrefixes
import GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy.MobiusHilbertVinogradovKorobov
import GaloisForLFunctions.RHTower.MobiusHilbertExponentLaw

/-!
# A Vinogradov–Korobov time window for the Möbius second moment

The exact Poisson energy uses positive squared Mertens prefixes. Its
largest prefix and its entire sum obey the same Vinogradov–Korobov
estimate, uniformly over all smaller cutoffs. The reciprocal square
root of this saving is the time scale up to which the sharp signed
moment stays small relative to the outer length.
-/
noncomputable section
open Finset Filter MeasureTheory Topology
open _root_.RHTower _root_.RHTower.Sieve
open GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy
open GaloisForLFunctions.MultiscaleMollifiedZetaField
namespace GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean

private theorem gram_le_prefix_envelope (N : ℕ) :
    mertensPoissonGram N ≤ (N:ℝ)*(shiftedMertensReal N^2/(N:ℝ)^2) +
      2*∑ n ∈ Icc 1 N, shiftedMertensReal n^2/(n:ℝ)^2 := by
  by_cases hN : N = 0
  · subst N; simp [mertensPoissonGram]
  have hN' := Nat.pos_of_ne_zero hN
  have hn : 0 < (N:ℝ) := Nat.cast_pos.mpr hN'
  rw [mertens_gram_prefix_squares hN']
  simp only [norm_mobiusMertensPartialSum_eq_abs_shiftedMertensReal,sq_abs]
  have terminal : shiftedMertensReal N^2/(N:ℝ) =
      (N:ℝ)*(shiftedMertensReal N^2/(N:ℝ)^2) := by field_simp
  rw [terminal]
  refine add_le_add le_rfl ?_
  let f := fun n : ℕ => shiftedMertensReal n^2/(n:ℝ)^2
  have hrow (k : ℕ) (hk : k ∈ Icc 1 (N-1)) :
      ((k:ℝ)⁻¹-((k:ℝ)+1)⁻¹)*shiftedMertensReal k^2 ≤ f k := by
    have hp : 0 < (k:ℝ) := Nat.cast_pos.mpr (mem_Icc.mp hk).1
    have hp1 : 0 < (k:ℝ)+1 := by positivity
    have hw : (k:ℝ)⁻¹-((k:ℝ)+1)⁻¹ ≤ ((k:ℝ)^2)⁻¹ := by
      field_simp <;> nlinarith only [hp]
    exact (mul_le_mul_of_nonneg_right hw (sq_nonneg _)).trans_eq (by dsimp only [f]; ring)
  have hf (k : ℕ) : 0 ≤ f k := div_nonneg (sq_nonneg _) (sq_nonneg _)
  have hsub : Icc 1 (N-1) ⊆ Icc 1 N := Icc_subset_Icc_right (Nat.sub_le _ _)
  have h := (sum_le_sum hrow).trans (sum_le_sum_of_subset_of_nonneg hsub (fun k _ _ => hf k))
  have hpos := sum_nonneg (s:=Icc 1 N) (fun k _ => hf k)
  change _ ≤ 2*∑ k ∈ Icc 1 N,f k
  linarith only [h,hpos]

/-- The bound holds simultaneously for every section below the same
outer horizon, including cutoffs inside the square-root range. -/
theorem uniform_mertens_gram_vk_saving :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ X : ℕ in atTop, ∀ N ≤ X,
      mertensPoissonGram N ≤ C*X*Real.exp (-(vkKappa*vkScale X/27)) := by
  obtain ⟨C,hC,h⟩ := exists_uniform_mertens_square_envelope_vk
  refine ⟨C,hC,?_⟩
  filter_upwards [h] with X hX N hN
  exact (gram_le_prefix_envelope N).trans (hX N hN)

/-- After dividing by the outer length, the sharp energy is bounded
by a constant times the squared ratio of height to the VK time scale. -/
theorem signed_moebius_moment_vk_time_scale :
    ∃ D : ℝ, 0 < D ∧ ∀ᶠ X : ℕ in atTop, ∀ N ≤ X, ∀ T : ℝ, 1 ≤ T →
      (∫ t in (1:ℝ)..T, ‖moebiusPoly N (MultiscaleMollifiedZetaField.linePoint t)‖^2) ≤
        D*X*(T/Real.exp (vkKappa*vkScale X/54))^2 := by
  obtain ⟨C,hC,h⟩ := uniform_mertens_gram_vk_saving
  refine ⟨4*Real.pi*C,by positivity,?_⟩
  filter_upwards [h] with X hX N hN T hT
  have he : (Real.exp (vkKappa*vkScale X/54))⁻¹^2 =
      Real.exp (-(vkKappa*vkScale X/27)) := by
    rw [←Real.exp_neg,←Real.exp_nat_mul]; congr 1; push_cast; ring
  have hbase := sharp_moebius_moment_le_mertens_gram N hT
  simp only [edPoly_moebiusMollifierCoeff_eq_moebiusPoly] at hbase
  refine hbase.trans
    ((mul_le_mul_of_nonneg_left (hX N hN) (by positivity)).trans_eq ?_)
  rw [div_eq_mul_inv T,mul_pow T,he]
  ring

/-- Any prescribed fraction of the outer length is achieved uniformly
over all smaller polynomials by taking a fixed small fraction of the
same growing time scale. -/
theorem uniform_sublinear_moebius_vk_windows {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ X : ℕ in atTop, ∀ N ≤ X, ∀ T : ℝ, 1 ≤ T →
      T ≤ δ*Real.exp (vkKappa*vkScale X/54) →
      (∫ t in (1:ℝ)..T, ‖moebiusPoly N (MultiscaleMollifiedZetaField.linePoint t)‖^2) ≤ ε*X := by
  obtain ⟨D,hD,h⟩ := signed_moebius_moment_vk_time_scale
  refine ⟨Real.sqrt (ε/D),Real.sqrt_pos.mpr (div_pos hε hD),?_⟩
  filter_upwards [h] with X hX N hN T hT hscale
  have he := (div_le_iff₀ (Real.exp_pos _)).mpr hscale
  have hsq := pow_le_pow_left₀ (div_nonneg (zero_le_one.trans hT) (Real.exp_pos _).le) he 2
  rw [Real.sq_sqrt (div_pos hε hD).le] at hsq
  exact (hX N hN T hT).trans ((mul_le_mul_of_nonneg_left hsq
    (mul_nonneg hD.le (Nat.cast_nonneg X))).trans_eq (by field_simp))

#print axioms uniform_mertens_gram_vk_saving
#print axioms signed_moebius_moment_vk_time_scale
#print axioms uniform_sublinear_moebius_vk_windows
end GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean
