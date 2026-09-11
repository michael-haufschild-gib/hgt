import GaloisForLFunctions.RHTower.FokasLenellsCausalBoundedFrequencyMeans
import Mathlib.Analysis.Normed.Operator.Completeness
/-! Sharp norms and failure of operator-norm convergence for the actual causal
frequency means. Finite scalar characters are continuous in frequency, even though
the actual unit eigenchain family is nowhere continuous in the stronger chain norm. -/
open Complex MeasureTheory Set Filter Topology
open scoped NNReal
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.FokasLenells
namespace RHTower.FokasLenells
noncomputable section
set_option backward.isDefEq.respectTransparency false
local instance causalFrequencyNormLowerComplete : CompleteSpace (hardyL2ᗮ) := hardyL2.isClosed_orthogonal.completeSpace_coe
local instance causalFrequencyNormChainComplete : CompleteSpace causalBoundedChain := causalBoundedChain_complete
local instance causalFrequencyNormChainNormedGroup : NormedAddCommGroup causalBoundedChain := causalBoundedChain.normedAddCommGroup
local instance causalFrequencyNormChainNormedSpace : NormedSpace ℂ causalBoundedChain := causalBoundedChain.normedSpace
local instance causalFrequencyNormEndNormedRing : NormedRing (causalBoundedChain →L[ℂ] causalBoundedChain) := ContinuousLinearMap.toNormedRing
local instance causalFrequencyNormEndTopology : TopologicalSpace (causalBoundedChain →L[ℂ] causalBoundedChain) :=
  (inferInstance : NormedAddCommGroup (causalBoundedChain →L[ℂ] causalBoundedChain)).toUniformSpace.toTopologicalSpace
local instance causalFrequencyNormEndTopologicalRing : IsTopologicalRing (causalBoundedChain →L[ℂ] causalBoundedChain) := NonUnitalSeminormedRing.toIsTopologicalRing
local instance causalFrequencyNormEndNormedSpace : NormedSpace ℂ (causalBoundedChain →L[ℂ] causalBoundedChain) := ContinuousLinearMap.toNormedSpace

private theorem left_rate_ne_zero (q : {z : ℂ // z.re < 0}) : q.val ≠ 0 := by
  intro h
  have hh := q.property
  rw [h, Complex.zero_re] at hh
  exact (lt_irrefl 0) hh

private theorem continuous_normalized_rate (b : ℝ) :
    Continuous (fun η : ℝ => (causalUnitBoundaryRate b η).val) := by
  have hr : Continuous (fun η : ℝ => (causalBoundaryRate b η).val) := by
    change Continuous (fun η : ℝ => -(Real.exp b : ℂ) + (η : ℂ) * I)
    exact continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
  change Continuous (fun η : ℝ => (causalBoundaryRate b η).val /
    (‖(causalBoundaryRate b η).val‖ : ℂ))
  exact hr.div (Complex.continuous_ofReal.comp hr.norm)
    (fun η => Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (left_rate_ne_zero (causalBoundaryRate b η))))

private def meanCharacter (b ω : ℝ) (N : ℕ) (η : ℝ) : ℂ :=
  ((N : ℝ)⁻¹ : ℂ) * ∑ j ∈ Finset.range N,
    (((causalUnitBoundaryRate b ω).val)⁻¹ * (causalUnitBoundaryRate b η).val)^j

private theorem meanCharacter_continuous (b ω : ℝ) (N : ℕ) :
    Continuous (meanCharacter b ω N) :=
  continuous_const.mul (continuous_finsetSum _ (fun j _ =>
    (continuous_const.mul (continuous_normalized_rate b)).pow j))

private theorem meanCharacter_self (b ω : ℝ) (N : ℕ) (hN : N ≠ 0) :
    meanCharacter b ω N ω = 1 := by
  have hq := left_rate_ne_zero (causalUnitBoundaryRate b ω)
  have hNne : ((N : ℝ) : ℂ) ≠ 0 := by
    simpa using (Nat.cast_ne_zero (R := ℂ)).mpr hN
  simp only [meanCharacter, inv_mul_cancel₀ hq, one_pow,
    Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  push_cast
  field_simp

private theorem mean_fixes_own (b ω : ℝ) (N : ℕ) (hN : N ≠ 0) :
    causalBoundedFrequencyMean b ω N (causalBoundedUnitEigenchain b ω) =
      causalBoundedUnitEigenchain b ω := by
  have he : causalBoundedFrequencyMean b ω N (causalBoundedUnitEigenchain b ω) =
      meanCharacter b ω N ω • causalBoundedUnitEigenchain b ω :=
    causalBoundedFrequencyMean_unitEigenchain b ω ω N
  exact he.trans ((congrArg (fun z : ℂ => z • causalBoundedUnitEigenchain b ω)
    (meanCharacter_self b ω N hN)).trans (one_smul ℂ _))

/-- Every nonempty actual frequency average has sharp operator norm one; the
empty average is exactly zero. -/
theorem norm_causalBoundedFrequencyMean (b ω : ℝ) (N : ℕ) :
    ‖causalBoundedFrequencyMean b ω N‖ = if N = 0 then 0 else 1 := by
  by_cases hN : N = 0
  · subst N
    have hz : causalBoundedFrequencyMean b ω 0 = 0 := by
      apply ContinuousLinearMap.ext
      intro u
      simpa only [causalBoundedFrequencyMean, Finset.range_zero, Finset.sum_empty,
        smul_apply, zero_apply, Nat.cast_zero, Complex.ofReal_zero] using
        (smul_zero ((0 : ℝ)⁻¹ : ℂ) : ((0 : ℝ)⁻¹ : ℂ) • (0 : causalBoundedChain) = 0)
    rw [hz, norm_zero, if_pos rfl]
  · rw [if_neg hN]
    apply le_antisymm (norm_causalBoundedFrequencyMean_le b ω N)
    have h := (causalBoundedFrequencyMean b ω N).le_opNorm (causalBoundedUnitEigenchain b ω)
    simpa only [mean_fixes_own b ω N hN, norm_causalBoundedUnitEigenchain, mul_one] using h

private theorem frequency_projection_gap (b ω : ℝ)
    (T : causalBoundedChain →L[ℂ] causalBoundedChain)
    (hT : ∀ η : ℝ, ω ≠ η → T (causalBoundedUnitEigenchain b η) = 0)
    (N : ℕ) (hN : N ≠ 0) : 1 ≤ ‖causalBoundedFrequencyMean b ω N - T‖ := by
  let η : ℕ → ℝ := fun n => ω + 1 / ((n : ℝ) + 1)
  have hη : Tendsto η atTop (𝓝 ω) := by
    simpa only [add_zero] using (tendsto_const_nhds (x := ω)).add
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hne (n : ℕ) : ω ≠ η n := by
    have hp : 0 < (1 : ℝ) / ((n : ℝ) + 1) := by positivity
    dsimp [η]
    linarith
  have hc : Tendsto (fun n => ‖meanCharacter b ω N (η n)‖) atTop (𝓝 1) := by
    have h := ((meanCharacter_continuous b ω N).tendsto ω).comp hη
    simpa only [Function.comp_def, meanCharacter_self b ω N hN, norm_one] using h.norm
  refine le_of_tendsto hc (Filter.Eventually.of_forall (fun n => ?_))
  have he : (causalBoundedFrequencyMean b ω N - T) (causalBoundedUnitEigenchain b (η n)) =
      meanCharacter b ω N (η n) • causalBoundedUnitEigenchain b (η n) := by
    calc
      _ = causalBoundedFrequencyMean b ω N (causalBoundedUnitEigenchain b (η n)) -
          T (causalBoundedUnitEigenchain b (η n)) := rfl
      _ = causalBoundedFrequencyMean b ω N (causalBoundedUnitEigenchain b (η n)) - 0 :=
        congrArg (fun v : causalBoundedChain =>
          causalBoundedFrequencyMean b ω N (causalBoundedUnitEigenchain b (η n)) - v) (hT (η n) (hne n))
      _ = causalBoundedFrequencyMean b ω N (causalBoundedUnitEigenchain b (η n)) := sub_zero _
      _ = _ := causalBoundedFrequencyMean_unitEigenchain b ω (η n) N
  have hb := (causalBoundedFrequencyMean b ω N - T).le_opNorm (causalBoundedUnitEigenchain b (η n))
  have hs : ‖meanCharacter b ω N (η n) • causalBoundedUnitEigenchain b (η n)‖ =
      ‖meanCharacter b ω N (η n)‖ :=
    (norm_smul _ _).trans ((congrArg (fun r : ℝ => ‖meanCharacter b ω N (η n)‖ * r)
      (norm_causalBoundedUnitEigenchain b (η n))).trans (mul_one _))
  have hr : ‖causalBoundedFrequencyMean b ω N - T‖ * ‖causalBoundedUnitEigenchain b (η n)‖ =
      ‖causalBoundedFrequencyMean b ω N - T‖ :=
    (congrArg (fun r : ℝ => ‖causalBoundedFrequencyMean b ω N - T‖ * r)
      (norm_causalBoundedUnitEigenchain b (η n))).trans (mul_one _)
  exact ((congrArg (fun v : causalBoundedChain => ‖v‖) he).trans hs).symm.trans_le (hb.trans_eq hr)

/-- Actual frequency means are never Cauchy in operator norm, despite being
contractions and converging on every individual actual frequency eigenchain. -/
theorem causalBoundedFrequencyMean_not_cauchySeq (b ω : ℝ) :
    ¬CauchySeq (fun N : ℕ => causalBoundedFrequencyMean b ω N) := by
  intro hC
  obtain ⟨T, hT⟩ : ∃ T : causalBoundedChain →L[ℂ] causalBoundedChain,
      Tendsto (fun N : ℕ => causalBoundedFrequencyMean b ω N) atTop (𝓝 T) :=
    cauchySeq_tendsto_of_complete hC
  have hkill : ∀ η : ℝ, ω ≠ η → T (causalBoundedUnitEigenchain b η) = 0 := by
    intro η hη
    have ht : Tendsto (fun N : ℕ => causalBoundedFrequencyMean b ω N
        (causalBoundedUnitEigenchain b η)) atTop (𝓝 (T (causalBoundedUnitEigenchain b η))) :=
      (((ContinuousLinearMap.apply ℂ causalBoundedChain (causalBoundedUnitEigenchain b η)).continuous).tendsto T).comp hT
    have hz : Tendsto (fun N : ℕ => causalBoundedFrequencyMean b ω N
        (causalBoundedUnitEigenchain b η)) atTop (𝓝 0) := by
      simpa only [if_neg hη] using causalBoundedFrequencyMean_tendsto_unitEigenchain b ω η
    exact tendsto_nhds_unique ht hz
  have hzero : Tendsto (fun N : ℕ => ‖causalBoundedFrequencyMean b ω N - T‖) atTop (𝓝 0) := by
    simpa only [sub_self, norm_zero] using (hT.sub_const T).norm
  have hbad : (1 : ℝ) ≤ 0 := ge_of_tendsto hzero (eventually_atTop.mpr
    ⟨1, fun N hN => frequency_projection_gap b ω T hkill N (by omega)⟩)
  norm_num at hbad
end
end RHTower.FokasLenells
