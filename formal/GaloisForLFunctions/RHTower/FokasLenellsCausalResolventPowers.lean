import GaloisForLFunctions.RHTower.FokasLenellsCausalBoundaryOrbits

/-! Finite powers of the actual resolvent retain their sharp norm at every causal time. -/
open Complex MeasureTheory Set Filter Topology
open scoped NNReal
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.FokasLenells
namespace RHTower.FokasLenells
noncomputable section

/-- Repeated actual resolvent application, embedded in the underlying lower Hardy space. -/
def causalResolventPower (z : {z : ℂ // 0 < z.re}) : ℕ → (hardyL2ᗮ →L[ℂ] hardyL2ᗮ)
  | 0 => ContinuousLinearMap.id ℂ _
  | k+1 => causalGeneratorDomain.subtypeL.comp ((causalComplexResolvent z).comp (causalResolventPower z k))

/-- A positive-order power is the actual maximal-domain resolvent of the preceding power. -/
theorem causalResolventPower_succ (z : {z : ℂ // 0 < z.re}) (k : ℕ) (u : hardyL2ᗮ) :
    causalResolventPower z (k+1) u = (causalComplexResolvent z (causalResolventPower z k u)).val := rfl

/-- Iteration gives the actual sharp damping scale as a uniform bound on every input. -/
theorem causalResolventPower_norm_le (z : {z : ℂ // 0 < z.re}) (k : ℕ) (u : hardyL2ᗮ) :
    ‖causalResolventPower z k u‖ ≤ (z.val.re⁻¹)^k*‖u‖ := by
  induction k with
  | zero => simp [causalResolventPower]
  | succ k ih =>
    change ‖causalComplexResolvent z (causalResolventPower z k u)‖ ≤ _
    exact (causalComplexResolvent_norm_le z _).trans
      ((mul_le_mul_of_nonneg_left ih (inv_nonneg.mpr z.property.le)).trans_eq
        (by rw [← mul_assoc, ← pow_succ']))

/-- Every normalized boundary vector diagonalizes every finite actual resolvent power. -/
theorem causalResolventPower_boundaryEigenvector (z : {z : ℂ // 0 < z.re}) (k : ℕ) (b ω : ℝ) :
    causalResolventPower z k (causalBoundaryEigenvector b ω).val =
      ((z.val-(causalBoundaryRate b ω).val)⁻¹)^k • (causalBoundaryEigenvector b ω).val := by
  induction k with
  | zero => simp [causalResolventPower]
  | succ k ih =>
    rw [causalResolventPower_succ, ih, map_smul, causalComplexResolvent_boundaryEigenvector]
    change _ • (_ • (causalBoundaryEigenvector b ω).val) = _
    rw [smul_smul, ← pow_succ]

/-- Causal evolution following an actual finite resolvent power. -/
def causalSmoothedEvolution (z : {z : ℂ // 0 < z.re}) (k : ℕ) (t : ℝ≥0) :
    hardyL2ᗮ →L[ℂ] hardyL2ᗮ :=
  (causalLowerCauchyEvolution t).comp (causalResolventPower z k)

/-- The exact boundary test norm combines exponential decay with reciprocal spectral distance. -/
theorem norm_causalSmoothedEvolution_boundaryEigenvector (z : {z : ℂ // 0 < z.re})
    (k : ℕ) (t : ℝ≥0) (b : ℝ) :
    ‖causalSmoothedEvolution z k t (causalBoundaryEigenvector b z.val.im).val‖ =
      Real.exp (-(t : ℝ)*Real.exp b)*((z.val.re+Real.exp b)⁻¹)^k := by
  change ‖causalLowerCauchyEvolution t (causalResolventPower z k _)‖ = _
  rw [causalResolventPower_boundaryEigenvector, map_smul, norm_smul,
    norm_pow, norm_inv, norm_causalLowerCauchyEvolution_boundaryEigenvector]
  have he : z.val-(causalBoundaryRate b z.val.im).val = ((z.val.re+Real.exp b : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [causalBoundaryRate]
  rw [he, Complex.norm_real,
    Real.norm_of_nonneg (add_pos z.property (Real.exp_pos b)).le, mul_comm]

/-- The actual evolved resolvent power is bounded at the same sharp damping scale. -/
theorem causalSmoothedEvolution_norm_le (z : {z : ℂ // 0 < z.re})
    (k : ℕ) (t : ℝ≥0) (u : hardyL2ᗮ) :
    ‖causalSmoothedEvolution z k t u‖ ≤ (z.val.re⁻¹)^k*‖u‖ :=
  (causalLowerCauchyEvolution_norm_le t _).trans (causalResolventPower_norm_le z k u)

/-- No finite resolvent smoothing improves the uniform decay norm, at any causal time. -/
theorem norm_causalSmoothedEvolution (z : {z : ℂ // 0 < z.re}) (k : ℕ) (t : ℝ≥0) :
    ‖causalSmoothedEvolution z k t‖ = (z.val.re⁻¹)^k := by
  apply le_antisymm
  · exact ContinuousLinearMap.opNorm_le_bound _ (pow_nonneg (inv_nonneg.mpr z.property.le) k)
      (causalSmoothedEvolution_norm_le z k t)
  · have hb (b : ℝ) : Real.exp (-(t : ℝ)*Real.exp b)*((z.val.re+Real.exp b)⁻¹)^k ≤
        ‖causalSmoothedEvolution z k t‖ := by
      have h := (causalSmoothedEvolution z k t).le_opNorm (causalBoundaryEigenvector b z.val.im).val
      rw [norm_causalSmoothedEvolution_boundaryEigenvector] at h
      change _ ≤ ‖causalSmoothedEvolution z k t‖ * ‖causalBoundaryEigenvector b z.val.im‖ at h
      simpa only [norm_causalBoundaryEigenvector, mul_one] using h
    have harg : Tendsto (fun b : ℝ => -(t : ℝ)*Real.exp b) atBot (𝓝 0) := by
      simpa only [mul_zero] using tendsto_const_nhds.mul Real.tendsto_exp_atBot
    have hadd : Tendsto (fun b : ℝ => z.val.re+Real.exp b) atBot (𝓝 z.val.re) := by
      simpa only [add_zero] using tendsto_const_nhds.add Real.tendsto_exp_atBot
    have hexp := (Real.continuous_exp.tendsto (0 : ℝ)).comp harg
    have ht := hexp.mul ((hadd.inv₀ z.property.ne').pow k)
    simpa only [Real.exp_zero, one_mul] using le_of_tendsto ht (Eventually.of_forall hb)

/-- Every actual finite resolvent power has precisely the expected sharp damping norm. -/
theorem norm_causalResolventPower (z : {z : ℂ // 0 < z.re}) (k : ℕ) :
    ‖causalResolventPower z k‖ = (z.val.re⁻¹)^k := by
  have he : causalSmoothedEvolution z k 0 = causalResolventPower z k := by
    apply ContinuousLinearMap.ext
    intro u
    exact causalLowerCauchyEvolution_zero _
  rw [← he, norm_causalSmoothedEvolution]

end
end RHTower.FokasLenells
