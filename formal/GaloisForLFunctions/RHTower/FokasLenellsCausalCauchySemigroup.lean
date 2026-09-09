import GaloisForLFunctions.RHTower.FokasLenellsCauchyCausalGate

/-!
# Causal Cauchy evolution on the completion of the encoded core

The exact encoded evolution extends to a strongly continuous contraction
semigroup on the full lower Hardy space. Every operator is onto, but every
positive-time operator has an explicit nonzero kernel vector. Its restriction
to the dense encoded core remains algebraically invertible. Completion thus
preserves forward continuity while losing injectivity.
-/

open Complex MeasureTheory Set Filter Topology
open scoped NNReal InnerProductSpace
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.FokasLenells
namespace RHTower.FokasLenells
noncomputable section

private theorem cauchy_mem_lower (u : SoninL2) : negativeCauchy u ∈ hardyL2ᗮ :=
  (negativeCauchy_eq_neg_iff _).1 (negativeCauchy_square u)

/-- Actual signed Cauchy compression restricted to the completed lower Hardy data space. -/
def causalLowerCauchyEvolution (t : ℝ≥0) : hardyL2ᗮ →L[ℂ] hardyL2ᗮ :=
  ((-cauchyEvolution (t:ℝ)).comp (hardyL2ᗮ).subtypeL).codRestrict (hardyL2ᗮ)
    (fun u => (hardyL2ᗮ).neg_mem (cauchy_mem_lower (evolution t u.val)))

/-- The completed evolution contracts the original L² norm. -/
theorem causalLowerCauchyEvolution_norm_le (t : ℝ≥0) (u : hardyL2ᗮ) :
    ‖causalLowerCauchyEvolution t u‖ ≤ ‖u‖ := by
  change ‖-negativeCauchy (evolution t u.val)‖ ≤ ‖u.val‖
  rw [norm_neg]
  exact (negativeCauchy_bound _).trans_eq (norm_evolution t u.val)

/-- The actual completed operators obey the additive semigroup law. -/
theorem causalLowerCauchyEvolution_add (s t : ℝ≥0) (u : hardyL2ᗮ) :
    causalLowerCauchyEvolution (s+t) u = causalLowerCauchyEvolution s (causalLowerCauchyEvolution t u) := by
  apply Subtype.ext
  change -negativeCauchy (evolution ((s:ℝ)+(t:ℝ)) u.val) =
    -negativeCauchy (evolution s (-negativeCauchy (evolution t u.val)))
  rw [evolution_add,map_neg,map_neg,neg_neg,negativeCauchy_causal_sandwich]

/-- Completed causal evolution starts at the identity. -/
theorem causalLowerCauchyEvolution_zero (u : hardyL2ᗮ) : causalLowerCauchyEvolution 0 u = u := by
  apply Subtype.ext
  change -negativeCauchy (evolution 0 u.val) = u.val
  rw [evolution_zero,(negativeCauchy_eq_neg_iff _).2 u.property,neg_neg]

/-- Every completed causal orbit is continuous in the inherited L² topology. -/
theorem causalLowerCauchyEvolution_continuous (u : hardyL2ᗮ) :
    Continuous (fun t : ℝ≥0 => causalLowerCauchyEvolution t u) := by
  apply continuous_induced_rng.2
  change Continuous (fun t : ℝ≥0 => -cauchyEvolution (t:ℝ) u.val)
  exact ((continuous_cauchyEvolution_apply u.val).comp continuous_subtype_val).neg

/-- The actual completed kernel consists exactly of lower Hardy data carried into upper Hardy. -/
theorem causalLowerCauchyEvolution_kernel_iff (t : ℝ≥0) (u : hardyL2ᗮ) :
    causalLowerCauchyEvolution t u = 0 ↔ evolution t u.val ∈ hardyL2 := by
  constructor
  · intro h
    have hv := congrArg (fun v : hardyL2ᗮ => v.val) h
    change -negativeCauchy (evolution t u.val) = 0 at hv
    exact (negativeCauchy_eq_zero_iff _).1 (neg_eq_zero.mp hv)
  · intro h
    apply Subtype.ext
    change -negativeCauchy (evolution t u.val) = 0
    rw [(negativeCauchy_eq_zero_iff _).2 h,neg_zero]

/-- The literal encoded core embeds isometrically into its lower Hardy completion. -/
def cauchyCoreLowerEmbedding : rawComplexCauchyCoreRange →ₗᵢ[ℂ] hardyL2ᗮ where
  toLinearMap := rawComplexCauchyCoreRange.subtype.codRestrict (hardyL2ᗮ) (fun y => by
    obtain ⟨u,hu⟩ := y.property
    change negativeCauchy u.val = y.val at hu
    change y.val ∈ hardyL2ᗮ
    rw [← hu]
    exact cauchy_mem_lower u.val)
  norm_map' _ := rfl

/-- Every lower Hardy datum is a limit of actual encoded core data in the same norm. -/
theorem cauchyCoreLowerEmbedding_denseRange : DenseRange cauchyCoreLowerEmbedding := by
  intro y
  rw [closure_subtype]
  have he : (Subtype.val : hardyL2ᗮ → SoninL2) '' Set.range cauchyCoreLowerEmbedding =
      (rawComplexCauchyCoreRange : Set SoninL2) := by
    ext z
    constructor
    · rintro ⟨w,⟨v,rfl⟩,rfl⟩
      exact v.property
    · intro hz
      exact ⟨cauchyCoreLowerEmbedding ⟨z,hz⟩,⟨⟨z,hz⟩,rfl⟩,rfl⟩
  rw [he,closure_rawComplexCauchyCoreRange]
  exact y.property

/-- The completed semigroup is the literal extension of the encoded causal action. -/
theorem cauchyCoreLowerEmbedding_intertwines (t : ℝ≥0) (y : rawComplexCauchyCoreRange) :
    causalLowerCauchyEvolution t (cauchyCoreLowerEmbedding y) =
      cauchyCoreLowerEmbedding (rawComplexCauchyCoreCausalEvolution t y) := by
  apply Subtype.ext
  change -negativeCauchy (evolution t y.val) = (rawComplexCauchyCoreGroup ((t:ℝ):ℂ) y).val
  exact (rawComplexCauchyCoreGroup_nonnegative_value t y).symm

private def unitCauchyFeature : UpperHardyL2 := lowerCauchyFeatureAt I (by simp)

/-- A concrete completed kernel candidate obtained from the reverse-time Cauchy feature. -/
def causalCauchyKernelWitness (a : ℝ) : hardyL2ᗮ :=
  ⟨negativeCauchy (evolution (-Real.exp a) unitCauchyFeature.val),cauchy_mem_lower _⟩

/-- Every concrete positive-time kernel witness is nonzero in actual L². -/
theorem causalCauchyKernelWitness_ne_zero (a : ℝ) : causalCauchyKernelWitness a ≠ 0 := by
  intro h
  have hv := congrArg (fun u : hardyL2ᗮ => u.val) h
  change negativeCauchy (evolution (-Real.exp a) unitCauchyFeature.val) = 0 at hv
  exact evolution_neg_exp_not_mem_hardy a ((negativeCauchy_eq_zero_iff _).1 hv)

/-- The completed positive-time operator kills its concrete nonzero kernel witness. -/
theorem causalLowerCauchyEvolution_kills_witness (a : ℝ) :
    causalLowerCauchyEvolution ⟨Real.exp a,(Real.exp_pos a).le⟩ (causalCauchyKernelWitness a) = 0 := by
  apply Subtype.ext
  change -negativeCauchy (evolution (Real.exp a)
    (negativeCauchy (evolution (-Real.exp a) unitCauchyFeature.val))) = 0
  have hs := negativeCauchy_causal_sandwich ⟨Real.exp a,(Real.exp_pos a).le⟩
    (evolution (-Real.exp a) unitCauchyFeature.val)
  change negativeCauchy (evolution (Real.exp a)
    (negativeCauchy (evolution (-Real.exp a) unitCauchyFeature.val))) =
      -negativeCauchy (evolution (Real.exp a) (evolution (-Real.exp a) unitCauchyFeature.val)) at hs
  rw [hs,neg_neg,
    ← evolution_add,add_neg_cancel,evolution_zero]
  exact (negativeCauchy_eq_zero_iff _).2 unitCauchyFeature.property

/-- Completion destroys injectivity at every positive time, with zero time the sole exception. -/
theorem causalLowerCauchyEvolution_injective_iff (t : ℝ≥0) :
    Function.Injective (causalLowerCauchyEvolution t) ↔ t = 0 := by
  constructor
  · intro h
    by_contra ht
    have ht' : 0 < (t:ℝ) := lt_of_le_of_ne t.property (by
      intro he
      apply ht
      exact Subtype.ext he.symm)
    have he : (⟨Real.exp (Real.log (t:ℝ)),(Real.exp_pos _).le⟩ : ℝ≥0) = t :=
      Subtype.ext (Real.exp_log ht')
    have hk := causalLowerCauchyEvolution_kills_witness (Real.log (t:ℝ))
    rw [he] at hk
    apply causalCauchyKernelWitness_ne_zero (Real.log (t:ℝ))
    exact h (hk.trans (map_zero (causalLowerCauchyEvolution t)).symm)
  · rintro rfl u v h
    simpa only [causalLowerCauchyEvolution_zero] using h

/-- Opposite causal time preserves lower Hardy, by orthogonality and the actual unitary identity. -/
theorem evolution_nonpositive_mem_lowerHardy (t : ℝ≥0) (u : hardyL2ᗮ) :
    evolution (-(t:ℝ)) u.val ∈ hardyL2ᗮ := by
  apply (Submodule.mem_orthogonal hardyL2 _).2
  intro v hv
  have hh := (Submodule.mem_orthogonal hardyL2 _).1 u.property
    (evolution t v) (evolution_nonnegative_mem_hardy t ⟨v,hv⟩)
  have hi := (evolution (t:ℝ)).inner_map_map v (evolution (-(t:ℝ)) u.val)
  rw [← evolution_add,add_neg_cancel,evolution_zero] at hi
  exact hi.symm.trans hh

/-- Every completed causal operator is onto, despite its nontrivial positive-time kernel. -/
theorem causalLowerCauchyEvolution_surjective (t : ℝ≥0) :
    Function.Surjective (causalLowerCauchyEvolution t) := by
  intro u
  refine ⟨⟨evolution (-(t:ℝ)) u.val,evolution_nonpositive_mem_lowerHardy t u⟩,?_⟩
  apply Subtype.ext
  change -negativeCauchy (evolution t (evolution (-(t:ℝ)) u.val)) = u.val
  rw [← evolution_add,add_neg_cancel,evolution_zero,(negativeCauchy_eq_neg_iff _).2 u.property,neg_neg]

end
end RHTower.FokasLenells
