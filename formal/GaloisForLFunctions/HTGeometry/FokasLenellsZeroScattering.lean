import GaloisForLFunctions.HTGeometry.FokasLenellsZeroEnergy

/-!
# Zero-energy transparency of the actual Fokas–Lenells scattering data

The general derivative-profile gauge applies with f=q' and p(x)=q(-x).
Consequently S(0)=I and both regularized reflections vanish at zero for every
Schwartz potential, without rescaling. Continuity gives a nontrivial spectral
neighborhood with nonzero transmissions and small reflection coefficients.
The paper's 5/9 jump-coercivity estimate therefore holds there at every position
and prescribed time, even for potentials outside the global small-data regime.
-/

open MeasureTheory Complex Matrix Filter Topology Metric
namespace GaloisForLFunctions.HTGeometry.FokasLenells
noncomputable section

/-- The derivative of the reflected Schwartz primitive is exactly the paper's reflected profile. -/
theorem derivCLM_reflectedPrimitive (q : SchwartzMap ℝ ℂ) :
    SchwartzMap.derivCLM ℂ ℂ (RHTower.negSchwartz' q) = reflectedDerivative q := by
  ext x
  rw [SchwartzMap.derivCLM_apply,reflectedDerivative_apply]
  exact congrArg (fun F : ℝ → ℂ => deriv F x) (funext fun y => RHTower.negSchwartz'_apply q y)

/-- The regularized scattering matrix is exactly the identity at zero for every Schwartz potential. -/
theorem regularScatteringMatrix_zero (q : SchwartzMap ℝ ℂ) : regularScatteringMatrix q 0 = 1 := by
  simpa only [regularScatteringMatrix,derivCLM_reflectedPrimitive] using
    uniformizedScatteringMatrix_zero_derivative_data (SchwartzMap.derivCLM ℂ ℂ q) (RHTower.negSchwartz' q)

theorem regularScatteringMatrix_tendsto_zero (q : SchwartzMap ℝ ℂ) :
    Tendsto (regularScatteringMatrix q) (𝓝 0) (𝓝 1) := by
  simpa only [regularScatteringMatrix_zero] using (continuous_regularScatteringMatrix q).tendsto 0

/-- Both regularized reflections have an exact zero at the spectral origin, without smallness. -/
theorem regularReflectionCoefficients_zero (q : SchwartzMap ℝ ℂ) :
    regularReflectionCoefficient q 0 = 0 ∧ regularReverseReflectionCoefficient q 0 = 0 := by
  simp [regularReflectionCoefficient,regularReverseReflectionCoefficient,regularScatteringMatrix_zero]

/-- Transmissions equal one at zero, so both quotients are continuous there for arbitrary q. -/
theorem continuousAt_regularReflectionCoefficients_zero (q : SchwartzMap ℝ ℂ) :
    ContinuousAt (regularReflectionCoefficient q) 0 ∧ ContinuousAt (regularReverseReflectionCoefficient q) 0 := by
  have hc (i j : Fin 2) : ContinuousAt (fun z => regularScatteringMatrix q z i j) 0 :=
    ((continuous_apply j).comp ((continuous_apply i).comp (continuous_regularScatteringMatrix q))).continuousAt
  exact ⟨(hc 1 0).div (hc 0 0) (by simp [regularScatteringMatrix_zero]),
    (hc 0 1).div (hc 1 1) (by simp [regularScatteringMatrix_zero])⟩

/-- The singular time phase multiplies an exact zero at the origin. -/
theorem regularJumpReflection_zero (q : SchwartzMap ℝ ℂ) (t x : ℝ) :
    regularJumpReflection q t x 0 = 0 ∧ regularJumpReverseReflection q t x 0 = 0 := by
  simp [regularJumpReflection,regularJumpReverseReflection,
    (regularReflectionCoefficients_zero q).1,(regularReflectionCoefficients_zero q).2]

/-- The actual time-dependent jump equals the identity at the origin for every Schwartz potential. -/
theorem regularJump_zero (q : SchwartzMap ℝ ℂ) (t x : ℝ) : regularJump q t x 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [regularJump,(regularJumpReflection_zero q t x).1,(regularJumpReflection_zero q t x).2,jump]

/-- Every Schwartz potential has a spectral neighborhood in which both transmissions are nonzero. -/
theorem exists_regularTransmission_neighborhood (q : SchwartzMap ℝ ℂ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ z : ℝ, |z| < ε →
      1/2 ≤ ‖regularScatteringMatrix q z 0 0‖ ∧ 1/2 ≤ ‖regularScatteringMatrix q z 1 1‖ := by
  let F : ℝ → ℂ × ℂ := fun z => (regularScatteringMatrix q z 0 0,regularScatteringMatrix q z 1 1)
  have hc : ContinuousAt F 0 := by
    exact (((continuous_apply 0).comp ((continuous_apply 0).comp (continuous_regularScatteringMatrix q))).prodMk
      ((continuous_apply 1).comp ((continuous_apply 1).comp (continuous_regularScatteringMatrix q)))).continuousAt
  obtain ⟨ε,hε,hb⟩ := Metric.continuousAt_iff.mp hc (1/2) (by positivity)
  refine ⟨ε,hε,fun z hz => ?_⟩
  have hn := hb (by simpa [dist_eq_norm,Real.norm_eq_abs] using hz)
  have he : F 0 = (1,1) := by simp [F,regularScatteringMatrix_zero]
  rw [he,dist_eq_norm,Prod.norm_def,max_lt_iff] at hn
  have h0 := norm_sub_norm_le (1:ℂ) (regularScatteringMatrix q z 0 0)
  have h1 := norm_sub_norm_le (1:ℂ) (regularScatteringMatrix q z 1 1)
  rw [norm_one,norm_sub_rev] at h0 h1
  change ‖regularScatteringMatrix q z 0 0-1‖ < 1/2 ∧ ‖regularScatteringMatrix q z 1 1-1‖ < 1/2 at hn
  constructor <;> linarith [hn.1,hn.2]

/-- Every Schwartz potential has a spectral neighborhood with uniformly small actual reflections. -/
theorem exists_regularReflection_neighborhood (q : SchwartzMap ℝ ℂ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ z : ℝ, |z| < ε →
      ‖regularReflectionCoefficient q z‖ ≤ 1/3 ∧ ‖regularReverseReflectionCoefficient q z‖ ≤ 1/3 := by
  let F : ℝ → ℂ × ℂ := fun z => (regularReflectionCoefficient q z,regularReverseReflectionCoefficient q z)
  have hc : ContinuousAt F 0 := (continuousAt_regularReflectionCoefficients_zero q).1.prodMk
    (continuousAt_regularReflectionCoefficients_zero q).2
  obtain ⟨ε,hε,hb⟩ := Metric.continuousAt_iff.mp hc (1/3) (by positivity)
  refine ⟨ε,hε,fun z hz => ?_⟩
  have hn := hb (by simpa [dist_eq_norm,Real.norm_eq_abs] using hz)
  have he : F 0 = 0 := Prod.ext (regularReflectionCoefficients_zero q).1 (regularReflectionCoefficients_zero q).2
  rw [he,dist_eq_norm,sub_zero,Prod.norm_def,max_lt_iff] at hn
  exact ⟨hn.1.le,hn.2.le⟩

/-- The paper's jump coercivity holds near zero for every unscaled Schwartz potential, uniformly in space and time. -/
theorem exists_regularJump_coercive_neighborhood (q : SchwartzMap ℝ ℂ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ z : ℝ, |z| < ε → ∀ t x : ℝ, ∀ u v : ℂ,
      (5/9 : ℝ)*(normSq u+normSq v) ≤
        energy (regularJumpReflection q t x z) (regularJumpReverseReflection q t x z) u v := by
  obtain ⟨ε,hε,hb⟩ := exists_regularReflection_neighborhood q
  refine ⟨ε,hε,fun z hz t x u v => ?_⟩
  let a := regularJumpReflection q t x z
  let b := regularJumpReverseReflection q t x z
  have ha : ‖a‖ ≤ 1/3 := by rw [(regularJumpReflection_norms q t x z).1]; exact (hb z hz).1
  have hb' : ‖b‖ ≤ 1/3 := by rw [(regularJumpReflection_norms q t x z).2]; exact (hb z hz).2
  have hab : ‖a‖*‖b‖ ≤ 1/9 := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ 1/3-‖a‖) (norm_nonneg b)]
  have h1 : 5/9 ≤ 1-(‖a‖+‖b‖)/2 := by linarith
  have h2 : 5/9 ≤ 1-‖a‖*‖b‖-(‖a‖+‖b‖)/2 := by linarith
  calc
    (5/9 : ℝ)*(normSq u+normSq v) = (5/9 : ℝ)*normSq u+(5/9 : ℝ)*normSq v := by ring
    _ ≤ (1-(‖a‖+‖b‖)/2)*normSq u+(1-‖a‖*‖b‖-(‖a‖+‖b‖)/2)*normSq v :=
      add_le_add (mul_le_mul_of_nonneg_right h1 (normSq_nonneg u))
        (mul_le_mul_of_nonneg_right h2 (normSq_nonneg v))
    _ ≤ _ := energy_norm_lower_bound a b u v

end
end GaloisForLFunctions.HTGeometry.FokasLenells
