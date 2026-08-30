import GaloisForLFunctions.HTGeometry.PosteriorContrastProjection
import GaloisForLFunctions.HTGeometry.FinitePacketMeasure
import GaloisForLFunctions.RHTower.HedenmalmThetaMobiusHyperbolicRapidity
import GaloisForLFunctions.RHTower.HedenmalmThetaSourceJuliaPythagoras

/-!
# The two-point posterior realization of the Möbius--Hardy cell

The source Cayley discrepancy and the normalized Hardy Gram of a two-sided aperture pair are the
contrast and the visibility of one explicit two-point binary experiment.  Under the
sign-forgetting observation the observed contrast is zero, so the whole coherence work of the
experiment is vertical information current, and the Julia identity `c² + g² = 1` becomes the
single-edge posterior projection law.
-/

namespace RHTower.HedenmalmThetaSource

open MeasureTheory ProbabilityTheory GaloisForLFunctions.HTGeometry
open scoped ENNReal

noncomputable section

/-- The sign observable on the two-point source. -/
def twoPointSign (b : Bool) : ℝ := if b then 1 else -1

@[simp] theorem twoPointSign_true : twoPointSign true = 1 := rfl

@[simp] theorem twoPointSign_false : twoPointSign false = -1 := rfl

@[simp] theorem twoPointSign_sq (b : Bool) : twoPointSign b ^ 2 = 1 := by
  cases b <;> norm_num

/-- `(PMP.34)`  The exponentially tilted two-point weights. -/
def twoPointWeight (δ : ℝ) (b : Bool) : ℝ :=
  Real.exp (twoPointSign b * δ) / (2 * Real.cosh δ)

theorem twoPointWeight_pos (δ : ℝ) (b : Bool) : 0 < twoPointWeight δ b := by
  rw [twoPointWeight]
  have : 0 < Real.cosh δ := Real.cosh_pos δ
  positivity

theorem exp_add_exp_neg_of_sign (δ : ℝ) (b : Bool) :
    Real.exp (twoPointSign b * δ) + Real.exp (twoPointSign b * (-δ))
      = Real.exp δ + Real.exp (-δ) := by
  cases b
  · simp only [twoPointSign_false, neg_one_mul, neg_neg]
    ring
  · simp only [twoPointSign_true, one_mul]

theorem sum_twoPointWeight (δ : ℝ) : ∑ b, twoPointWeight δ b = 1 := by
  have hc : (0:ℝ) < Real.cosh δ := Real.cosh_pos δ
  have hnum : Real.exp (twoPointSign true * δ) + Real.exp (twoPointSign false * δ)
      = Real.exp δ + Real.exp (-δ) := by
    simp only [twoPointSign_true, twoPointSign_false, one_mul, neg_one_mul]
  rw [Fintype.sum_bool, twoPointWeight, twoPointWeight,
    show Real.exp (twoPointSign true * δ) / (2 * Real.cosh δ)
        + Real.exp (twoPointSign false * δ) / (2 * Real.cosh δ)
      = (Real.exp (twoPointSign true * δ) + Real.exp (twoPointSign false * δ))
        / (2 * Real.cosh δ) by ring, hnum, Real.cosh_eq]
  field_simp

theorem sum_twoPointWeight_neg (δ : ℝ) : ∑ b, twoPointWeight (-δ) b = 1 := sum_twoPointWeight (-δ)

/-- `(PMP.34)`  The forward member of the two-point experiment. -/
def twoPointLawPos (δ : ℝ) : Measure Bool := packetMeasure (twoPointWeight δ)

/-- `(PMP.34)`  The reflected member of the two-point experiment. -/
def twoPointLawNeg (δ : ℝ) : Measure Bool := packetMeasure (twoPointWeight (-δ))

instance isProbabilityMeasure_twoPointLawPos (δ : ℝ) :
    IsProbabilityMeasure (twoPointLawPos δ) :=
  isProbabilityMeasure_packetMeasure (fun b => (twoPointWeight_pos δ b).le) (sum_twoPointWeight δ)

instance isProbabilityMeasure_twoPointLawNeg (δ : ℝ) :
    IsProbabilityMeasure (twoPointLawNeg δ) :=
  isProbabilityMeasure_packetMeasure (fun b => (twoPointWeight_pos (-δ) b).le)
    (sum_twoPointWeight (-δ))

theorem twoPointWeight_add_neg (δ : ℝ) (b : Bool) :
    twoPointWeight δ b + twoPointWeight (-δ) b = 1 := by
  have hc : (0:ℝ) < Real.cosh δ := Real.cosh_pos δ
  rw [twoPointWeight, twoPointWeight, Real.cosh_neg,
    show Real.exp (twoPointSign b * δ) / (2 * Real.cosh δ)
        + Real.exp (twoPointSign b * -δ) / (2 * Real.cosh δ)
      = (Real.exp (twoPointSign b * δ) + Real.exp (twoPointSign b * (-δ)))
        / (2 * Real.cosh δ) by ring, exp_add_exp_neg_of_sign δ b, Real.cosh_eq]
  field_simp

/-! ## The balanced law is uniform -/

theorem withDensity_packetMeasure_singleton {Z : Type*} [Fintype Z] [Nonempty Z]
    [MeasurableSpace Z] [MeasurableSingletonClass Z] (p : Z → ℝ) {f : Z → ℝ≥0∞}
    (_hfhf : Measurable f) (b : Z) :
    ((packetMeasure p).withDensity f) {b} = ENNReal.ofReal (p b) * f b := by
  rw [withDensity_apply _ (measurableSet_singleton b),
    ← lintegral_indicator (measurableSet_singleton b), lintegral_packetMeasure]
  rw [Finset.sum_eq_single b]
  · rw [Set.indicator_of_mem (Set.mem_singleton b)]
  · intro x _ hx
    rw [Set.indicator_of_notMem (by simpa using hx), mul_zero]
  · intro hb
    exact absurd (Finset.mem_univ b) hb

/-- The balanced law of the two-point experiment is the uniform law. -/
theorem balancedLaw_twoPoint (δ : ℝ) :
    balancedLaw (twoPointLawPos δ) (twoPointLawNeg δ)
      = packetMeasure (fun _ : Bool => (1 : ℝ) / 2) := by
  refine Measure.ext_iff_singleton.mpr fun b => ?_
  rw [balancedLaw, Measure.smul_apply, Measure.add_apply, smul_eq_mul, twoPointLawPos,
    twoPointLawNeg, packetMeasure_singleton, packetMeasure_singleton, packetMeasure_singleton,
    ← ENNReal.ofReal_add (twoPointWeight_pos δ b).le (twoPointWeight_pos (-δ) b).le,
    twoPointWeight_add_neg, ENNReal.ofReal_one, mul_one]
  rw [show ((1 : ℝ) / 2) = (2 : ℝ)⁻¹ by norm_num, ENNReal.ofReal_inv_of_pos (by norm_num)]
  norm_num

/-- The forward density of the two-point experiment against the uniform law. -/
theorem rnDeriv_twoPointLawPos (δ : ℝ) :
    (twoPointLawPos δ).rnDeriv (balancedLaw (twoPointLawPos δ) (twoPointLawNeg δ))
      =ᵐ[balancedLaw (twoPointLawPos δ) (twoPointLawNeg δ)]
        fun b => ENNReal.ofReal (2 * twoPointWeight δ b) := by
  have hmeas : Measurable fun b : Bool => ENNReal.ofReal (2 * twoPointWeight δ b) := by
    measurability
  have hw : (balancedLaw (twoPointLawPos δ) (twoPointLawNeg δ)).withDensity
      (fun b => ENNReal.ofReal (2 * twoPointWeight δ b)) = twoPointLawPos δ := by
    rw [balancedLaw_twoPoint]
    refine Measure.ext_iff_singleton.mpr fun b => ?_
    rw [withDensity_packetMeasure_singleton _ hmeas, twoPointLawPos, packetMeasure_singleton,
      ← ENNReal.ofReal_mul (by norm_num)]
    congr 1
    ring
  calc (twoPointLawPos δ).rnDeriv (balancedLaw (twoPointLawPos δ) (twoPointLawNeg δ))
      = ((balancedLaw (twoPointLawPos δ) (twoPointLawNeg δ)).withDensity
          (fun b => ENNReal.ofReal (2 * twoPointWeight δ b))).rnDeriv
            (balancedLaw (twoPointLawPos δ) (twoPointLawNeg δ)) := by rw [hw]
    _ =ᵐ[balancedLaw (twoPointLawPos δ) (twoPointLawNeg δ)]
          fun b => ENNReal.ofReal (2 * twoPointWeight δ b) :=
        Measure.rnDeriv_withDensity _ hmeas

/-- `(PMP.35)`  The posterior contrast of the two-point experiment is the signed hyperbolic
tangent. -/
theorem two_mul_twoPointWeight_sub_one (δ : ℝ) (b : Bool) :
    2 * twoPointWeight δ b - 1 = twoPointSign b * Real.tanh δ := by
  have hc : (0:ℝ) < Real.cosh δ := Real.cosh_pos δ
  rw [twoPointWeight, Real.tanh_eq_sinh_div_cosh]
  cases b
  · simp only [twoPointSign_false, neg_one_mul]
    rw [Real.sinh_eq, Real.cosh_eq] at *
    field_simp
    ring
  · simp only [twoPointSign_true, one_mul]
    rw [Real.sinh_eq, Real.cosh_eq] at *
    field_simp
    ring

theorem posteriorContrast_twoPoint (δ : ℝ) :
    posteriorContrast (twoPointLawPos δ) (twoPointLawNeg δ)
      =ᵐ[balancedLaw (twoPointLawPos δ) (twoPointLawNeg δ)]
        fun b => twoPointSign b * Real.tanh δ := by
  filter_upwards [rnDeriv_twoPointLawPos δ] with b hb
  rw [posteriorContrast, hb,
    ENNReal.toReal_ofReal (by nlinarith [twoPointWeight_pos δ b] :
      (0:ℝ) ≤ 2 * twoPointWeight δ b),
    two_mul_twoPointWeight_sub_one]

/-! ## The sign-forgetting observation -/

/-- The observation that forgets the sign. -/
def signForget : Kernel Bool Unit := Kernel.const Bool (Measure.dirac ())

instance : IsMarkovKernel signForget := by
  rw [signForget]; infer_instance

theorem comp_signForget (μ : Measure Bool) [IsProbabilityMeasure μ] :
    ⇑signForget ∘ₘ μ = Measure.dirac () := by
  refine Measure.ext fun s hs => ?_
  rw [Measure.bind_apply hs (Kernel.aemeasurable _)]
  simp only [signForget, Kernel.const_apply]
  rw [lintegral_const, measure_univ, mul_one]

theorem posteriorContrast_signForget (δ : ℝ) :
    posteriorContrast (⇑signForget ∘ₘ (twoPointLawPos δ)) (⇑signForget ∘ₘ (twoPointLawNeg δ))
      =ᵐ[balancedLaw (⇑signForget ∘ₘ (twoPointLawPos δ)) (⇑signForget ∘ₘ (twoPointLawNeg δ))]
        fun _ => 0 := by
  rw [comp_signForget, comp_signForget]
  exact posteriorContrast_self _

/-- `(PMP.36)`  Under the sign-forgetting observation the vertical current carries the whole
posterior contrast. -/
theorem informationCurrent_twoPoint (δ : ℝ) :
    informationCurrent signForget (twoPointLawPos δ) (twoPointLawNeg δ)
      =ᵐ[balancedLaw (twoPointLawPos δ) (twoPointLawNeg δ) ⊗ₘ signForget]
        fun p => twoPointSign p.1 * Real.tanh δ := by
  have h1 : ∀ᵐ p ∂(balancedLaw (twoPointLawPos δ) (twoPointLawNeg δ) ⊗ₘ signForget),
      posteriorContrast (twoPointLawPos δ) (twoPointLawNeg δ) p.1
        = twoPointSign p.1 * Real.tanh δ := by
    have h : ∀ᵐ b ∂((balancedLaw (twoPointLawPos δ) (twoPointLawNeg δ) ⊗ₘ signForget).map
        Prod.fst), posteriorContrast (twoPointLawPos δ) (twoPointLawNeg δ) b
          = twoPointSign b * Real.tanh δ := by
      rw [← Measure.fst, Measure.fst_compProd]
      exact posteriorContrast_twoPoint δ
    exact (ae_map_iff measurable_fst.aemeasurable
      (measurableSet_eq_fun (measurable_posteriorContrast _ _)
        (by measurability))).mp h
  have h2 : ∀ᵐ p ∂(balancedLaw (twoPointLawPos δ) (twoPointLawNeg δ) ⊗ₘ signForget),
      posteriorContrast (⇑signForget ∘ₘ (twoPointLawPos δ))
        (⇑signForget ∘ₘ (twoPointLawNeg δ)) p.2 = 0 := by
    refine ae_snd_compProd signForget (balancedLaw (twoPointLawPos δ) (twoPointLawNeg δ))
      (measurableSet_eq_fun (measurable_posteriorContrast _ _) measurable_const) ?_
    rw [← balancedLaw_comp signForget (twoPointLawPos δ) (twoPointLawNeg δ)]
    exact posteriorContrast_signForget δ
  filter_upwards [h1, h2] with p hp1 hp2
  have : informationCurrent signForget (twoPointLawPos δ) (twoPointLawNeg δ) p
      = posteriorContrast (twoPointLawPos δ) (twoPointLawNeg δ) p.1
        - posteriorContrast (⇑signForget ∘ₘ (twoPointLawPos δ))
            (⇑signForget ∘ₘ (twoPointLawNeg δ)) p.2 := rfl
  rw [this, hp1, hp2, sub_zero]

/-- `(PMP.36)`  The coherence work of the two-point experiment. -/
theorem coherenceWork_twoPoint (δ : ℝ) :
    coherenceWork (twoPointLawPos δ) (twoPointLawNeg δ) = 4 * (Real.tanh δ) ^ 2 := by
  rw [coherenceWork]
  congr 1
  rw [integral_congr_ae (g := fun _ : Bool => (Real.tanh δ) ^ 2) ?_]
  · rw [integral_const, probReal_univ, one_smul]
  · filter_upwards [posteriorContrast_twoPoint δ] with b hb
    rw [hb, mul_pow, twoPointSign_sq, one_mul]

/-- `(PMP.36)`  The whole coherence work is vertical current energy. -/
theorem integral_sq_informationCurrent_twoPoint (δ : ℝ) :
    ∫ p, (informationCurrent signForget (twoPointLawPos δ) (twoPointLawNeg δ) p) ^ 2
      ∂(balancedLaw (twoPointLawPos δ) (twoPointLawNeg δ) ⊗ₘ signForget)
      = (Real.tanh δ) ^ 2 := by
  rw [integral_congr_ae (g := fun _ : Bool × Unit => (Real.tanh δ) ^ 2) ?_]
  · rw [integral_const, probReal_univ, one_smul]
  · filter_upwards [informationCurrent_twoPoint δ] with p hp
    rw [hp, mul_pow, twoPointSign_sq, one_mul]

/-! ## The Möbius--Hardy cell as a posterior projection -/

/-- **Section 8, `(PMP.32)`–`(PMP.36)`.**  The source Cayley discrepancy of a two-sided aperture
pair is the posterior contrast of an explicit two-point experiment, its whole coherence work is
vertical information current under the sign-forgetting observation, and the Julia identity
`c² + g² = 1` is exactly the resulting single-edge projection law. -/
theorem mobiusHardyCell_posterior_certificate {u v : ℝ} (hu : -(1 / 2 : ℝ) < u)
    (hv : -(1 / 2 : ℝ) < v) :
    coherenceWork
        (twoPointLawPos (mobiusCriticalTwoSidedRapidity u - mobiusCriticalTwoSidedRapidity v))
        (twoPointLawNeg (mobiusCriticalTwoSidedRapidity u - mobiusCriticalTwoSidedRapidity v))
        = 4 * (mobiusCriticalTwoSidedCayleyDiscrepancy u v) ^ 2
      ∧ ∫ p, (informationCurrent signForget
            (twoPointLawPos (mobiusCriticalTwoSidedRapidity u - mobiusCriticalTwoSidedRapidity v))
            (twoPointLawNeg (mobiusCriticalTwoSidedRapidity u -
              mobiusCriticalTwoSidedRapidity v)) p) ^ 2
          ∂(balancedLaw
              (twoPointLawPos (mobiusCriticalTwoSidedRapidity u -
                mobiusCriticalTwoSidedRapidity v))
              (twoPointLawNeg (mobiusCriticalTwoSidedRapidity u -
                mobiusCriticalTwoSidedRapidity v)) ⊗ₘ signForget)
          = (mobiusCriticalTwoSidedCayleyDiscrepancy u v) ^ 2
      ∧ coherenceWork
            (twoPointLawPos (mobiusCriticalTwoSidedRapidity u -
              mobiusCriticalTwoSidedRapidity v))
            (twoPointLawNeg (mobiusCriticalTwoSidedRapidity u -
              mobiusCriticalTwoSidedRapidity v)) / 4
          + (mobiusCriticalTwoSidedUnitHardyGram u v) ^ 2 = 1 := by
  have hc : mobiusCriticalTwoSidedCayleyDiscrepancy u v
      = Real.tanh (mobiusCriticalTwoSidedRapidity u - mobiusCriticalTwoSidedRapidity v) :=
    mobiusCriticalTwoSidedCayleyDiscrepancy_eq_tanh_rapidity_sub hu hv
  have hjulia := sq_mobiusCriticalTwoSidedCayleyDiscrepancy_add_sq_unitHardyGram hu hv
  refine ⟨?_, ?_, ?_⟩
  · rw [coherenceWork_twoPoint, hc]
  · rw [integral_sq_informationCurrent_twoPoint, hc]
  · rw [coherenceWork_twoPoint, ← hc]
    linarith

end

end RHTower.HedenmalmThetaSource
