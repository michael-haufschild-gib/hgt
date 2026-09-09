import GaloisForLFunctions.RHTower.FokasLenellsCausalGeneratorGraph

/-!
# Actual causal evolution on the closed maximal generator graph

The input and derivative evolve together. The product Hilbert-space topology
on the closed graph supplies the complete graph norm needed for integration
of an unbounded generator, without assuming boundedness in the input norm.
-/

open Complex MeasureTheory Set Filter Topology
open scoped NNReal
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.FokasLenells
namespace RHTower.FokasLenells
noncomputable section

private def graphEvolutionLinear (t : ℝ≥0) : causalGeneratorGraph →ₗ[ℂ] causalGeneratorGraph where
  toFun p := ⟨(causalLowerCauchyEvolution t p.val.1,causalLowerCauchyEvolution t p.val.2),by
    intro s
    change causalLowerCauchyEvolution s (causalLowerCauchyEvolution t p.val.1)-
      causalLowerCauchyEvolution t p.val.1 = causalOrbitIntegral s (causalLowerCauchyEvolution t p.val.2)
    have he : causalLowerCauchyEvolution s (causalLowerCauchyEvolution t p.val.1) =
        causalLowerCauchyEvolution t (causalLowerCauchyEvolution s p.val.1) := by
      rw [← causalLowerCauchyEvolution_add,add_comm,causalLowerCauchyEvolution_add]
    rw [he,← map_sub,p.property s,causalOrbitIntegral_commutes]⟩
  map_add' p q := by apply Subtype.ext; apply Prod.ext <;> exact map_add _ _ _
  map_smul' c p := by apply Subtype.ext; apply Prod.ext <;> exact map_smul _ _ _

/-- The literal evolution of both components of the actual maximal generator graph. -/
def causalGeneratorGraphEvolution (t : ℝ≥0) : causalGeneratorGraph →L[ℂ] causalGeneratorGraph :=
  (graphEvolutionLinear t).mkContinuous 1 (fun p => by
    change max ‖causalLowerCauchyEvolution t p.val.1‖ ‖causalLowerCauchyEvolution t p.val.2‖ ≤
      1 * max ‖p.val.1‖ ‖p.val.2‖
    rw [one_mul]
    exact max_le_max (causalLowerCauchyEvolution_norm_le t p.val.1)
      (causalLowerCauchyEvolution_norm_le t p.val.2))

/-- Graph evolution has the original causal orbit as its actual input component. -/
theorem causalGeneratorGraphEvolution_input (t : ℝ≥0) (p : causalGeneratorGraph) :
    causalGeneratorGraphInput (causalGeneratorGraphEvolution t p) =
      causalLowerCauchyEvolution t (causalGeneratorGraphInput p) := rfl

/-- The actual derivative output evolves by the same completed causal semigroup. -/
theorem causalGeneratorGraphEvolution_output (t : ℝ≥0) (p : causalGeneratorGraph) :
    causalGeneratorGraphOutput (causalGeneratorGraphEvolution t p) =
      causalLowerCauchyEvolution t (causalGeneratorGraphOutput p) := rfl

/-- The actual graph norm contracts under causal evolution. -/
theorem causalGeneratorGraphEvolution_norm_le (t : ℝ≥0) (p : causalGeneratorGraph) :
    ‖causalGeneratorGraphEvolution t p‖ ≤ ‖p‖ :=
  max_le_max (causalLowerCauchyEvolution_norm_le t p.val.1)
    (causalLowerCauchyEvolution_norm_le t p.val.2)

/-- The graph evolution obeys the exact additive semigroup law. -/
theorem causalGeneratorGraphEvolution_add (s t : ℝ≥0) (p : causalGeneratorGraph) :
    causalGeneratorGraphEvolution (s+t) p =
      causalGeneratorGraphEvolution s (causalGeneratorGraphEvolution t p) := by
  apply Subtype.ext
  apply Prod.ext <;> exact causalLowerCauchyEvolution_add _ _ _

/-- The graph semigroup starts at the identity on the actual complete graph. -/
theorem causalGeneratorGraphEvolution_zero (p : causalGeneratorGraph) :
    causalGeneratorGraphEvolution 0 p = p := by
  apply Subtype.ext
  apply Prod.ext <;> exact causalLowerCauchyEvolution_zero _

/-- Both graph components vary continuously, in the actual graph norm. -/
theorem causalGeneratorGraphEvolution_continuous (p : causalGeneratorGraph) :
    Continuous (fun t : ℝ≥0 => causalGeneratorGraphEvolution t p) := by
  apply continuous_induced_rng.2
  change Continuous (fun t : ℝ≥0 =>
    (causalLowerCauchyEvolution t p.val.1,causalLowerCauchyEvolution t p.val.2))
  exact (causalLowerCauchyEvolution_continuous p.val.1).prodMk
    (causalLowerCauchyEvolution_continuous p.val.2)

/-- Away from zero, every maximal-domain orbit has its actual full real derivative. -/
theorem causalGenerator_positiveOrbit_hasDerivAt (a : ℝ) (u : causalGeneratorDomain) :
    HasDerivAt (causalForwardOrbit u.val)
      (causalForwardOrbit (causalGenerator u) (Real.exp a)) (Real.exp a) := by
  have hd := (causalOrbitPrimitive_hasDerivAt (Real.exp a) (causalGenerator u)).const_add u.val
  apply hd.congr_of_eventuallyEq
  have hpos : ∀ᶠ r : ℝ in 𝓝 (Real.exp a), 0 < r :=
    eventually_gt_nhds (Real.exp_pos a)
  filter_upwards [hpos] with r hr
  have he := (causalForwardOrbit_rightDerivative_iff _ _).1 (causalGenerator_hasRightDeriv u) r.toNNReal
  change causalForwardOrbit u.val r-u.val = causalOrbitPrimitive (r.toNNReal:ℝ) (causalGenerator u) at he
  rw [Real.coe_toNNReal r hr.le] at he
  change causalForwardOrbit u.val r = u.val+causalOrbitPrimitive r (causalGenerator u)
  rw [← he,← add_sub_assoc,add_sub_cancel_left]

end
end RHTower.FokasLenells
