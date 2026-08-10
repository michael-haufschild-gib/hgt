import GaloisForLFunctions.HTGeometry.AbelianZetaGas.DepthLadder

/-!
# The two-observable response of the abelian zeta gas

Tilting the zeta-Gibbs law by `|A|^{-(σ'-σ)}·|soc A|^{-(τ'-τ)}` moves the parameters from `θ` to
`θ'`, so the expectation of the tilt is the ratio of the two zero-occupation constants — equivalently
the ratio of the two zeta partition functions.  This is (GAS.6) on the exact convergence chamber:
both parameter points must lie in it, which is precisely the card's coupled condition
`Re(σ+u) > 0`, `Re(σ+u+v) > 1`.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped ENNReal

noncomputable section

namespace AbelianZetaConvergentParameters

/-- The tilt observable carrying `θ` to `θ'`. -/
def gasTilt (θ θ' : AbelianZetaConvergentParameters) (A : AbelianZetaGroupClass) : ℝ :=
  (A.order : ℝ) ^ (-(θ'.sigma - θ.sigma)) * (A.socleOrder : ℝ) ^ (-(θ'.tau - θ.tau))

theorem gasTilt_nonneg (θ θ' : AbelianZetaConvergentParameters) (A : AbelianZetaGroupClass) :
    0 ≤ gasTilt θ θ' A := by
  rw [gasTilt]
  positivity

theorem twoObservableWeight_nonneg (θ : AbelianZetaParameters) (A : AbelianZetaGroupClass) :
    0 ≤ abelianZetaTwoObservableWeight θ A := by
  rw [abelianZetaTwoObservableWeight]
  positivity

/-- The tilt carries the Gibbs weight of `θ` to the Gibbs weight of `θ'`. -/
theorem twoObservableWeight_mul_gasTilt (θ θ' : AbelianZetaConvergentParameters)
    (A : AbelianZetaGroupClass) :
    abelianZetaTwoObservableWeight θ.toAbelianZetaParameters A * gasTilt θ θ' A
      = abelianZetaTwoObservableWeight θ'.toAbelianZetaParameters A := by
  have hord : (0 : ℝ) < (A.order : ℝ) := by exact_mod_cast A.order_pos
  have hsoc : (0 : ℝ) < (A.socleOrder : ℝ) := by exact_mod_cast A.socleOrder_pos
  rw [abelianZetaTwoObservableWeight, abelianZetaTwoObservableWeight, gasTilt]
  calc (A.order : ℝ) ^ (-θ.sigma) * (A.socleOrder : ℝ) ^ (-θ.tau)
        * ((A.order : ℝ) ^ (-(θ'.sigma - θ.sigma)) * (A.socleOrder : ℝ) ^ (-(θ'.tau - θ.tau)))
      = ((A.order : ℝ) ^ (-θ.sigma) * (A.order : ℝ) ^ (-(θ'.sigma - θ.sigma)))
        * ((A.socleOrder : ℝ) ^ (-θ.tau) * (A.socleOrder : ℝ) ^ (-(θ'.tau - θ.tau))) := by ring
    _ = (A.order : ℝ) ^ (-θ.sigma + -(θ'.sigma - θ.sigma))
        * (A.socleOrder : ℝ) ^ (-θ.tau + -(θ'.tau - θ.tau)) := by
        rw [← Real.rpow_add hord, ← Real.rpow_add hsoc]
    _ = (A.order : ℝ) ^ (-θ'.sigma) * (A.socleOrder : ℝ) ^ (-θ'.tau) := by
        congr 2 <;> ring

/-- The two-observable response: the expectation of the tilt under the zeta-Gibbs law of `θ`. -/
def gasResponse (θ θ' : AbelianZetaConvergentParameters) : ℝ≥0∞ :=
  ∑' A : AbelianZetaGroupClass,
    abelianZetaClassMass θ.toAbelianZetaParameters A * ENNReal.ofReal (gasTilt θ θ' A)

/-- **(GAS.6).**  The two-observable response is the ratio of the zero-occupation constants. -/
theorem gasResponse_eq (θ θ' : AbelianZetaConvergentParameters) :
    gasResponse θ θ' = θ.ennNormalizer * θ'.ennNormalizer⁻¹ := by
  have hterm : ∀ A : AbelianZetaGroupClass,
      abelianZetaClassMass θ.toAbelianZetaParameters A * ENNReal.ofReal (gasTilt θ θ' A)
        = θ.ennNormalizer
          * ENNReal.ofReal (abelianZetaTwoObservableWeight θ'.toAbelianZetaParameters A) := by
    intro A
    rw [θ.classMass_eq_ennNormalizer_mul_twoObservableWeight A, mul_assoc,
      ← ENNReal.ofReal_mul (twoObservableWeight_nonneg _ A),
      twoObservableWeight_mul_gasTilt θ θ' A]
  rw [gasResponse, tsum_congr hterm, ENNReal.tsum_mul_left,
    θ'.tsum_twoObservableWeight_eq_ennNormalizer_inv]

/-- **(GAS.6), cleared form.**  The response times the tilted normalizer is the base normalizer. -/
theorem gasResponse_mul_ennNormalizer (θ θ' : AbelianZetaConvergentParameters) :
    gasResponse θ θ' * θ'.ennNormalizer = θ.ennNormalizer := by
  have hne : θ'.ennNormalizer ≠ 0 := by
    rw [ennNormalizer, ne_eq, ENNReal.coe_eq_zero]
    intro h0
    apply θ'.complexNormalizer_ne_zero
    rw [← θ'.coe_nnNormalizer_eq_complexNormalizer, h0]
    simp
  have htop : θ'.ennNormalizer ≠ ⊤ := by
    rw [ennNormalizer]
    exact ENNReal.coe_ne_top
  rw [gasResponse_eq, mul_assoc, ENNReal.inv_mul_cancel hne htop, mul_one]

theorem ennNormalizer_ne_zero (θ : AbelianZetaConvergentParameters) : θ.ennNormalizer ≠ 0 := by
  rw [ennNormalizer, ne_eq, ENNReal.coe_eq_zero]
  intro h0
  apply θ.complexNormalizer_ne_zero
  rw [← θ.coe_nnNormalizer_eq_complexNormalizer, h0]
  simp

theorem gasResponse_ne_top (θ θ' : AbelianZetaConvergentParameters) :
    gasResponse θ θ' ≠ ⊤ := by
  rw [gasResponse_eq]
  refine ENNReal.mul_ne_top ?_ ?_
  · rw [ennNormalizer]
    exact ENNReal.coe_ne_top
  · exact ENNReal.inv_ne_top.mpr (ennNormalizer_ne_zero θ')

theorem zetaPartition_ne_zero (θ : AbelianZetaConvergentParameters) : θ.zetaPartition ≠ 0 := by
  rw [θ.zetaPartition_eq_complexNormalizer_inv]
  exact inv_ne_zero θ.complexNormalizer_ne_zero

/-- **(GAS.6), zeta form.**  The two-observable response is the ratio of the zeta partition
functions of the two parameter points. -/
theorem gasResponse_toReal_mul_zetaPartition (θ θ' : AbelianZetaConvergentParameters) :
    ((gasResponse θ θ').toReal : ℂ) * θ.zetaPartition = θ'.zetaPartition := by
  have hmul := gasResponse_mul_ennNormalizer θ θ'
  have hreal := congrArg ENNReal.toReal hmul
  rw [ENNReal.toReal_mul, ennNormalizer, ennNormalizer, ENNReal.coe_toReal,
    ENNReal.coe_toReal] at hreal
  have hcomplex : ((gasResponse θ θ').toReal : ℂ) * (θ'.nnNormalizer : ℂ)
      = (θ.nnNormalizer : ℂ) := by
    exact_mod_cast congrArg (fun x : ℝ => (x : ℂ)) hreal
  rw [θ.coe_nnNormalizer_eq_complexNormalizer, θ'.coe_nnNormalizer_eq_complexNormalizer,
    θ.complexNormalizer_eq_zetaPartition_inv, θ'.complexNormalizer_eq_zetaPartition_inv] at hcomplex
  field_simp at hcomplex
  rw [div_eq_div_iff (zetaPartition_ne_zero θ') (zetaPartition_ne_zero θ), one_mul] at hcomplex
  exact hcomplex

end AbelianZetaConvergentParameters

end

end GaloisForLFunctions.HTGeometry
