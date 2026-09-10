import GaloisForLFunctions.RHTower.FokasLenellsCausalBoundedUnitEigenchains
import GaloisForLFunctions.HTGeometry.AtomicMomentDeterminacy

/-! Actual contractive frequency averages on the genuine bounded Cauchy derivative space. -/
open Complex MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.FokasLenells
namespace RHTower.FokasLenells
noncomputable section
set_option backward.isDefEq.respectTransparency false
local instance causalFrequencyMeanLowerComplete : CompleteSpace (hardyL2ᗮ) := hardyL2.isClosed_orthogonal.completeSpace_coe
local instance causalFrequencyMeanChainComplete : CompleteSpace causalBoundedChain := causalBoundedChain_complete
local instance causalFrequencyMeanChainNormedGroup : NormedAddCommGroup causalBoundedChain := causalBoundedChain.normedAddCommGroup
local instance causalFrequencyMeanChainNormedSpace : NormedSpace ℂ causalBoundedChain := causalBoundedChain.normedSpace
local instance causalFrequencyMeanEndNormedRing : NormedRing (causalBoundedChain →L[ℂ] causalBoundedChain) :=
  ContinuousLinearMap.toNormedRing
local instance causalFrequencyMeanEndTopology : TopologicalSpace (causalBoundedChain →L[ℂ] causalBoundedChain) :=
  (inferInstance : NormedAddCommGroup
    (causalBoundedChain →L[ℂ] causalBoundedChain)).toUniformSpace.toTopologicalSpace
local instance causalFrequencyMeanEndTopologicalRing : IsTopologicalRing (causalBoundedChain →L[ℂ] causalBoundedChain) :=
  NonUnitalSeminormedRing.toIsTopologicalRing

/-- Normalizing the actual boundary rates retains every frequency at each fixed damping scale. -/
theorem causalUnitBoundaryRate_injective (b : ℝ) :
    Function.Injective (fun ω : ℝ => (causalUnitBoundaryRate b ω).val) := by
  intro ω η h
  have hr := congrArg Complex.re h
  have hi := congrArg Complex.im h
  rw [causalUnitBoundaryRate_re, causalUnitBoundaryRate_re] at hr
  rw [causalUnitBoundaryRate_im, causalUnitBoundaryRate_im] at hi
  have hn (t : ℝ) : ‖(causalBoundaryRate b t).val‖ ≠ 0 := by
    apply norm_ne_zero_iff.mpr
    intro hz
    have hh := (causalBoundaryRate b t).property
    rw [hz] at hh
    exact (lt_irrefl 0) hh
  field_simp [hn ω, hn η] at hr hi
  have hd : ‖(causalBoundaryRate b ω).val‖ = ‖(causalBoundaryRate b η).val‖ := by
    nlinarith [Real.exp_pos b]
  rw [hd] at hi
  exact (mul_left_cancel₀ (hn η)) hi

/-- Cesàro averages of the actual derivative shift, rotated to a chosen unit boundary rate. -/
def causalBoundedFrequencyMean (b ω : ℝ) (N : ℕ) :
    causalBoundedChain →L[ℂ] causalBoundedChain :=
  (((N : ℝ)⁻¹ : ℂ)) • ∑ j ∈ Finset.range N,
    (((causalUnitBoundaryRate b ω).val)⁻¹)^j • causalBoundedChainShift^j

private theorem frequencyMean_apply (b ω : ℝ) (N : ℕ) (u : causalBoundedChain) :
    causalBoundedFrequencyMean b ω N u = ((N : ℝ)⁻¹ : ℂ) •
      ∑ j ∈ Finset.range N, (((causalUnitBoundaryRate b ω).val)⁻¹)^j •
        ((causalBoundedChainShift^j) u) := by
  have hs : (∑ j ∈ Finset.range N, (((causalUnitBoundaryRate b ω).val)⁻¹)^j •
      causalBoundedChainShift^j) u = ∑ j ∈ Finset.range N,
      (((causalUnitBoundaryRate b ω).val)⁻¹)^j • ((causalBoundedChainShift^j) u) :=
    sum_apply (Finset.range N)
      (fun j => (((causalUnitBoundaryRate b ω).val)⁻¹)^j • causalBoundedChainShift^j) u
  exact congrArg (fun v : causalBoundedChain => ((N : ℝ)⁻¹ : ℂ) • v) hs

/-- The actual average has the scalar geometric character on every actual unit eigenchain. -/
theorem causalBoundedFrequencyMean_unitEigenchain (b ω η : ℝ) (N : ℕ) :
    causalBoundedFrequencyMean b ω N (causalBoundedUnitEigenchain b η) =
      ((((N : ℝ)⁻¹ : ℂ)) * ∑ j ∈ Finset.range N,
        (((causalUnitBoundaryRate b ω).val)⁻¹ * (causalUnitBoundaryRate b η).val)^j) •
          causalBoundedUnitEigenchain b η := by
  have hs : (∑ j ∈ Finset.range N, (((causalUnitBoundaryRate b ω).val)⁻¹)^j •
      ((causalBoundedChainShift^j) (causalBoundedUnitEigenchain b η))) =
      (∑ j ∈ Finset.range N,
        (((causalUnitBoundaryRate b ω).val)⁻¹ * (causalUnitBoundaryRate b η).val)^j) •
          causalBoundedUnitEigenchain b η := by
    calc
      _ = ∑ j ∈ Finset.range N,
          (((causalUnitBoundaryRate b ω).val)⁻¹ * (causalUnitBoundaryRate b η).val)^j •
            causalBoundedUnitEigenchain b η := by
        apply Finset.sum_congr rfl
        intro j hj
        exact (congrArg
          (fun v : causalBoundedChain => (((causalUnitBoundaryRate b ω).val)⁻¹)^j • v)
          (causalBoundedChainShift_pow_unitEigenchain b η j)).trans
          ((smul_smul _ _ _).trans
            (congrArg (fun z : ℂ => z • causalBoundedUnitEigenchain b η)
              (mul_pow _ _ j).symm))
      _ = _ := Finset.sum_smul.symm
  exact (frequencyMean_apply b ω N (causalBoundedUnitEigenchain b η)).trans
    ((congrArg (fun v : causalBoundedChain => ((N : ℝ)⁻¹ : ℂ) • v) hs).trans
      (mul_smul _ _ _).symm)

/-- Averaging never enlarges the norm of any actual bounded derivative chain. -/
theorem causalBoundedFrequencyMean_norm_apply_le (b ω : ℝ) (N : ℕ)
    (u : causalBoundedChain) : ‖causalBoundedFrequencyMean b ω N u‖ ≤ ‖u‖ := by
  have hNpos : 0 ≤ (N : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg N)
  have hc : ‖((N : ℝ)⁻¹ : ℂ)‖ = (N : ℝ)⁻¹ := by
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
  have hterm (j : ℕ) :
      ‖(((causalUnitBoundaryRate b ω).val)⁻¹)^j • ((causalBoundedChainShift^j) u)‖ ≤ ‖u‖ := by
    have hn : ‖(((causalUnitBoundaryRate b ω).val)⁻¹)^j‖ = 1 := by
      rw [norm_pow, norm_inv, norm_causalUnitBoundaryRate, inv_one, one_pow]
    calc
      _ = ‖(((causalUnitBoundaryRate b ω).val)⁻¹)^j‖ * ‖(causalBoundedChainShift^j) u‖ := norm_smul ((((causalUnitBoundaryRate b ω).val)⁻¹)^j) ((causalBoundedChainShift^j) u)
      _ = ‖(causalBoundedChainShift^j) u‖ := (congrArg (fun r : ℝ => r * ‖(causalBoundedChainShift^j) u‖) hn).trans (one_mul _)
      _ ≤ ‖u‖ := causalBoundedChainShift_pow_norm_le j u
  have he := congrArg (fun v : causalBoundedChain => ‖v‖) (frequencyMean_apply b ω N u)
  have hs : ‖((N : ℝ)⁻¹ : ℂ) • (∑ j ∈ Finset.range N,
      (((causalUnitBoundaryRate b ω).val)⁻¹)^j • ((causalBoundedChainShift^j) u))‖ =
      (N : ℝ)⁻¹ * ‖∑ j ∈ Finset.range N,
        (((causalUnitBoundaryRate b ω).val)⁻¹)^j • ((causalBoundedChainShift^j) u)‖ := by
    exact (norm_smul ((N : ℝ)⁻¹ : ℂ) (∑ j ∈ Finset.range N,
      (((causalUnitBoundaryRate b ω).val)⁻¹)^j • ((causalBoundedChainShift^j) u))).trans (congrArg
      (fun r : ℝ => r * ‖∑ j ∈ Finset.range N,
        (((causalUnitBoundaryRate b ω).val)⁻¹)^j • ((causalBoundedChainShift^j) u)‖) hc)
  apply (he.trans hs).le.trans
  calc
    (N : ℝ)⁻¹ * ‖∑ j ∈ Finset.range N,
        (((causalUnitBoundaryRate b ω).val)⁻¹)^j • ((causalBoundedChainShift^j) u)‖
      ≤ (N : ℝ)⁻¹ * ∑ j ∈ Finset.range N,
          ‖(((causalUnitBoundaryRate b ω).val)⁻¹)^j • ((causalBoundedChainShift^j) u)‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) hNpos
    _ ≤ (N : ℝ)⁻¹ * ∑ _j ∈ Finset.range N, ‖u‖ :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun j _ => hterm j)) hNpos
    _ ≤ ‖u‖ := by
      by_cases hN : N = 0
      · simp [hN]
      · simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← mul_assoc,
          inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hN : (N : ℝ) ≠ 0), one_mul]
        exact le_rfl

/-- Every genuine frequency mean is an operator contraction. -/
theorem norm_causalBoundedFrequencyMean_le (b ω : ℝ) (N : ℕ) :
    ‖causalBoundedFrequencyMean b ω N‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro u
  simpa only [one_mul] using causalBoundedFrequencyMean_norm_apply_le b ω N u

/-- The averages select their own actual unit frequency and annihilate every other one. -/
theorem causalBoundedFrequencyMean_tendsto_unitEigenchain (b ω η : ℝ) :
    Tendsto (fun N : ℕ => causalBoundedFrequencyMean b ω N (causalBoundedUnitEigenchain b η))
      atTop (𝓝 (if ω = η then causalBoundedUnitEigenchain b η else 0)) := by
  have hn : (causalUnitBoundaryRate b ω).val ≠ 0 := by
    intro h
    have hh := norm_causalUnitBoundaryRate b ω
    rw [h, norm_zero] at hh
    norm_num at hh
  by_cases h : ω = η
  · subst η
    simpa only [causalBoundedFrequencyMean_unitEigenchain, inv_mul_cancel₀ hn,
      ite_true, one_smul] using
      (tendsto_geomSum_cesaro_one.smul_const (causalBoundedUnitEigenchain b ω))
  · have hratio : ((causalUnitBoundaryRate b ω).val)⁻¹ * (causalUnitBoundaryRate b η).val ≠ 1 := by
      intro he
      have he' := congrArg (fun z : ℂ => (causalUnitBoundaryRate b ω).val * z) he
      simp only [← mul_assoc, mul_inv_cancel₀ hn, one_mul, mul_one] at he'
      exact h ((causalUnitBoundaryRate_injective b he').symm)
    have hnorm : ‖((causalUnitBoundaryRate b ω).val)⁻¹ * (causalUnitBoundaryRate b η).val‖ ≤ 1 := by
      rw [norm_mul, norm_inv, norm_causalUnitBoundaryRate, norm_causalUnitBoundaryRate]
      norm_num
    simpa only [causalBoundedFrequencyMean_unitEigenchain, if_neg h, zero_smul] using
      ((tendsto_geomSum_cesaro_of_norm_le_one hnorm hratio).smul_const
        (causalBoundedUnitEigenchain b η))

/-- Distinct unit frequencies stay at least one unit apart in the actual bounded-chain norm. -/
theorem causalBoundedUnitEigenchain_pairwise_separated (b : ℝ) :
    Pairwise (fun ω η : ℝ => 1 ≤ dist
      (causalBoundedUnitEigenchain b ω) (causalBoundedUnitEigenchain b η)) := by
  intro ω η h
  have hx := causalBoundedFrequencyMean_tendsto_unitEigenchain b ω ω
  have hy := causalBoundedFrequencyMean_tendsto_unitEigenchain b ω η
  simp only [ite_true] at hx
  simp only [if_neg h] at hy
  have ht : Tendsto (fun N : ℕ => causalBoundedFrequencyMean b ω N
      (causalBoundedUnitEigenchain b ω - causalBoundedUnitEigenchain b η))
      atTop (𝓝 (causalBoundedUnitEigenchain b ω)) := by
    simpa only [map_sub, sub_zero] using hx.sub hy
  have hh := le_of_tendsto ht.norm (Filter.Eventually.of_forall
    (fun N => causalBoundedFrequencyMean_norm_apply_le b ω N
      (causalBoundedUnitEigenchain b ω - causalBoundedUnitEigenchain b η)))
  simpa only [norm_causalBoundedUnitEigenchain, dist_eq_norm] using hh

end
end RHTower.FokasLenells
