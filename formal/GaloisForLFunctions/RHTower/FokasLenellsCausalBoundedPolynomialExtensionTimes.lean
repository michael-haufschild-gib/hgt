import GaloisForLFunctions.RHTower.FokasLenellsCausalBoundedPolynomialL2Extension
/-! Exact complex-time geometry for bounded L2 extensions of the polynomial chain flows.
Constants admit the whole plane; linear polynomials admit one forward ray; higher
polynomials admit only zero. Opposite nonzero times survive precisely for constants. -/
open Complex MeasureTheory Set Filter Topology Polynomial
open scoped NNReal
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.FokasLenells
namespace RHTower.FokasLenells
noncomputable section
set_option backward.isDefEq.respectTransparency false
local instance causalPolynomialTimesLowerEndNormedSpace :
    NormedSpace ℂ (hardyL2ᗮ →L[ℂ] hardyL2ᗮ) := ContinuousLinearMap.toNormedSpace
local instance causalPolynomialTimesLowerEndNormSMul :
    NormSMulClass ℂ (hardyL2ᗮ →L[ℂ] hardyL2ᗮ) :=
  NormedSpace.toNormSMulClass (𝕜 := ℂ) (E := hardyL2ᗮ →L[ℂ] hardyL2ᗮ)

private theorem constant_coeff_one (p : ℂ[X]) (h : p.natDegree = 0) : p.coeff 1 = 0 := by
  have he := congrArg (fun q : ℂ[X] => q.coeff 1) (Polynomial.eq_C_of_natDegree_eq_zero h)
  simpa only [Polynomial.coeff_C, if_neg (by omega : (1 : ℕ) ≠ 0)] using he

private theorem linear_zero_slope (p : ℂ[X]) (hd : p.natDegree ≤ 1) (hc : p.coeff 1 = 0) :
    p.natDegree = 0 := by
  have he : p = C (p.coeff 0) := by
    simpa only [hc, map_zero, zero_mul, zero_add] using
      (Polynomial.eq_X_add_C_of_natDegree_le_one hd)
  exact (congrArg Polynomial.natDegree he).trans (Polynomial.natDegree_C _)

private theorem scaled_positive_affine_iff (p : ℂ[X]) (z : ℂ) :
    (∃ a : ℝ≥0, ∃ b : ℂ, z • p = C ((a : ℝ) : ℂ) * X + C b) ↔
      (z = 0 ∨ p.natDegree ≤ 1) ∧ (z * p.coeff 1).im = 0 ∧ 0 ≤ (z * p.coeff 1).re := by
  constructor
  · rintro ⟨a, b, hp⟩
    have hd : (z • p).natDegree ≤ 1 := by
      rw [hp]
      exact Polynomial.natDegree_linear_le
    have hc : z * p.coeff 1 = ((a : ℝ) : ℂ) := by
      simpa using congrArg (fun q : ℂ[X] => q.coeff 1) hp
    refine ⟨?_, ?_, ?_⟩
    · by_cases hz : z = 0
      · exact Or.inl hz
      · exact Or.inr ((Polynomial.natDegree_smul p hz) ▸ hd)
    · rw [hc]
      exact Complex.ofReal_im _
    · rw [hc]
      exact a.property
  · rintro ⟨hd, him, hre⟩
    by_cases hz : z = 0
    · exact ⟨0, 0, by simp [hz]⟩
    · have hdeg : (z • p).natDegree ≤ 1 :=
        (Polynomial.natDegree_smul_le z p).trans (hd.resolve_left hz)
      let a : ℝ≥0 := ⟨(z * p.coeff 1).re, hre⟩
      have hslope : (z • p).coeff 1 = ((a : ℝ) : ℂ) := by
        rw [Polynomial.coeff_smul, smul_eq_mul]
        apply Complex.ext
        · rfl
        · exact him
      exact ⟨a, (z • p).coeff 0,
        (Polynomial.eq_X_add_C_of_natDegree_le_one hdeg).trans
          (congrArg (fun c : ℂ => C c * X + C ((z • p).coeff 0)) hslope)⟩

/-- Degree and the rotated linear coefficient completely decide whether a
polynomial chain flow has a bounded original L2 extension at any derivative coordinate. -/
theorem causalBoundedPolynomialExponential_has_coordinateExtension_iff (j : ℕ) (p : ℂ[X]) (z : ℂ) :
    (∃ T : hardyL2ᗮ →L[ℂ] hardyL2ᗮ,
      causalBoundedCoordinateExtension j (causalBoundedPolynomialExponential p z) T) ↔
      (z = 0 ∨ p.natDegree ≤ 1) ∧ (z * p.coeff 1).im = 0 ∧ 0 ≤ (z * p.coeff 1).re := by
  rw [← scaled_positive_affine_iff p z]
  constructor
  · rintro ⟨T, hT⟩
    obtain ⟨a, b, hp, _, _⟩ :=
      (causalBoundedPolynomialExponential_coordinateExtension_iff j p z T).mp hT
    exact ⟨a, b, hp⟩
  · rintro ⟨a, b, hp⟩
    refine ⟨Complex.exp b • causalLowerCauchyEvolution a,
      (causalBoundedPolynomialExponential_coordinateExtension_iff j p z _).mpr ⟨a, b, hp, rfl, ?_⟩⟩
    rw [norm_smul, norm_causalLowerCauchyEvolution, Complex.norm_exp, mul_one]

/-- The complete allowed-time set is the whole complex plane, a rotated closed
forward ray, or the singleton zero, according to whether the polynomial is constant,
linear, or of higher degree. This holds at every genuine derivative coordinate. -/
theorem causalBoundedPolynomialExponential_coordinateExtension_times (j : ℕ) (p : ℂ[X]) :
    {z : ℂ | ∃ T : hardyL2ᗮ →L[ℂ] hardyL2ᗮ,
      causalBoundedCoordinateExtension j (causalBoundedPolynomialExponential p z) T} =
      if p.natDegree = 0 then Set.univ else
        if p.natDegree = 1 then Set.range (fun a : ℝ≥0 => ((a : ℝ) : ℂ) / p.coeff 1)
        else {0} := by
  ext z
  change (∃ T : hardyL2ᗮ →L[ℂ] hardyL2ᗮ,
    causalBoundedCoordinateExtension j (causalBoundedPolynomialExponential p z) T) ↔ _
  rw [causalBoundedPolynomialExponential_has_coordinateExtension_iff]
  by_cases h0 : p.natDegree = 0
  · rw [if_pos h0]
    have hc := constant_coeff_one p h0
    simp [hc, h0]
  · rw [if_neg h0]
    by_cases h1 : p.natDegree = 1
    · rw [if_pos h1]
      have hc : p.coeff 1 ≠ 0 := by
        intro he
        exact h0 (linear_zero_slope p h1.le he)
      constructor
      · rintro ⟨_, him, hre⟩
        refine ⟨⟨(z * p.coeff 1).re, hre⟩, (div_eq_iff hc).mpr ?_⟩
        apply Complex.ext
        · rfl
        · exact him.symm
      · rintro ⟨a, ha⟩
        have hm : z * p.coeff 1 = ((a : ℝ) : ℂ) :=
          (congrArg (fun w : ℂ => w * p.coeff 1) ha.symm).trans (div_mul_cancel₀ _ hc)
        refine ⟨Or.inr h1.le, ?_, ?_⟩
        · rw [hm]
          exact Complex.ofReal_im _
        · rw [hm]
          exact a.property
    · rw [if_neg h1]
      constructor
      · rintro ⟨hz | hd, _, _⟩
        · exact hz
        · omega
      · intro hz
        change z = 0 at hz
        simp [hz]

/-- Bounded L2 extension in both time directions at a given time is possible
exactly at zero time or for a constant polynomial generator. -/
theorem causalBoundedPolynomialExponential_opposite_coordinateExtensions_iff (j : ℕ) (p : ℂ[X]) (z : ℂ) :
    ((∃ T : hardyL2ᗮ →L[ℂ] hardyL2ᗮ,
      causalBoundedCoordinateExtension j (causalBoundedPolynomialExponential p z) T) ∧
     (∃ T : hardyL2ᗮ →L[ℂ] hardyL2ᗮ,
      causalBoundedCoordinateExtension j (causalBoundedPolynomialExponential p (-z)) T)) ↔
      z = 0 ∨ p.natDegree = 0 := by
  rw [causalBoundedPolynomialExponential_has_coordinateExtension_iff,
    causalBoundedPolynomialExponential_has_coordinateExtension_iff]
  constructor
  · rintro ⟨⟨hd, him, hre⟩, ⟨_, _, hnre⟩⟩
    by_cases hz : z = 0
    · exact Or.inl hz
    · have hn : -(z * p.coeff 1).re ≥ 0 := by
        simpa only [neg_mul, Complex.neg_re] using hnre
      have hm : z * p.coeff 1 = 0 := by
        apply Complex.ext
        · change (z * p.coeff 1).re = 0
          linarith
        · exact him
      exact Or.inr (linear_zero_slope p (hd.resolve_left hz) ((mul_eq_zero.mp hm).resolve_left hz))
  · rintro (hz | hp)
    · simp [hz]
    · have hc := constant_coeff_one p hp
      simp [hc, hp]
end
end RHTower.FokasLenells
