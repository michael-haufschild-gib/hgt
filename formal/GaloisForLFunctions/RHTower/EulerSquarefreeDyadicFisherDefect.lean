import GaloisForLFunctions.RHTower.EulerSquarefreeDyadicFisherTangent

/-!
# The canonical isometry, the exact Fisher-connection defect, and its vanishing

`dyadic-squarefree-euler-fock-source-factorization`, §4–§5, equations `(15)`–`(23)`.

* `(15)` — `‖χ_E‖² = ‖χ_sq‖² + ‖r‖²`, the orthogonal splitting of the critical Fisher energy;
* `(17)`–`(18)` — the canonical linear isometry `V_σ x = U*(x ⊗ e_{2σ})`, with `V_σ s_σ = e_σ`
  and `‖χ_E − V_σ χ_sq‖ = ‖r‖`;
* `(21)` — the exact transport of the polarized rank-two connection;
* `(23)` — the exact Hilbert–Schmidt defect law `‖X_E − V_σ X_sq V_σ*‖²_HS = 16 ε² Var_{2σ}`;
* `(16)` — the defect tends to zero as `σ → 1⁺`.
-/

open Complex Set Filter Topology
open scoped InnerProductSpace

noncomputable section

namespace RHTower

open GaloisForLFunctions.HTGeometry ContinuousLinearMap InnerProductSpace

/-! ## Norms of elementary tensors -/

theorem normSq_lpTensor {ι κ : Type*} (x : lp (fun _ : ι => ℂ) 2)
    (y : lp (fun _ : κ => ℂ) 2) : ‖lpTensor x y‖ ^ 2 = ‖x‖ ^ 2 * ‖y‖ ^ 2 := by
  have hx : Summable (fun i : ι => ‖x i‖ ^ (2 : ℕ)) := by
    have h := (memℓp_gen_iff (p := 2) (E := fun _ : ι => ℂ) (by norm_num)).mp (lp.memℓp x)
    refine h.congr fun i => ?_
    rw [← Real.rpow_natCast ‖x i‖ 2]
    norm_num
  have hy : Summable (fun k : κ => ‖y k‖ ^ (2 : ℕ)) := by
    have h := (memℓp_gen_iff (p := 2) (E := fun _ : κ => ℂ) (by norm_num)).mp (lp.memℓp y)
    refine h.congr fun k => ?_
    rw [← Real.rpow_natCast ‖y k‖ 2]
    norm_num
  have hxa : Summable (fun i : ι => ‖‖x i‖ ^ (2 : ℕ)‖) := by
    refine hx.congr fun i => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hya : Summable (fun k : κ => ‖‖y k‖ ^ (2 : ℕ)‖) := by
    refine hy.congr fun k => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  rw [lp_two_norm_sq_eq_tsum, lp_two_norm_sq_eq_tsum, lp_two_norm_sq_eq_tsum,
    tsum_mul_tsum_of_summable_norm hxa hya]
  refine tsum_congr fun q => ?_
  rw [lpTensor_apply, norm_mul, mul_pow]

theorem norm_lpTensor {ι κ : Type*} (x : lp (fun _ : ι => ℂ) 2)
    (y : lp (fun _ : κ => ℂ) 2) : ‖lpTensor x y‖ = ‖x‖ * ‖y‖ := by
  have h := normSq_lpTensor x y
  have h' : ‖lpTensor x y‖ ^ 2 = (‖x‖ * ‖y‖) ^ 2 := by rw [h, mul_pow]
  have hnn : (0 : ℝ) ≤ ‖x‖ * ‖y‖ := by positivity
  rw [← Real.sqrt_sq (norm_nonneg (lpTensor x y)), h', Real.sqrt_sq hnn]

theorem lpTensor_add_left {ι κ : Type*} (x x' : lp (fun _ : ι => ℂ) 2)
    (y : lp (fun _ : κ => ℂ) 2) :
    lpTensor (x + x') y = lpTensor x y + lpTensor x' y := by
  refine lp.ext (funext fun q => ?_)
  simp [lpTensor, add_mul]

theorem lpTensor_smul_left {ι κ : Type*} (a : ℂ) (x : lp (fun _ : ι => ℂ) 2)
    (y : lp (fun _ : κ => ℂ) 2) :
    lpTensor (a • x) y = a • lpTensor x y := by
  refine lp.ext (funext fun q => ?_)
  simp [lpTensor, mul_assoc]

/-- Tensoring on the right by a unit vector is a linear isometry. -/
def lpTensorRight {ι κ : Type*} (y : lp (fun _ : κ => ℂ) 2) (hy : ‖y‖ = 1) :
    lp (fun _ : ι => ℂ) 2 →ₗᵢ[ℂ] lp (fun _ : ι × κ => ℂ) 2 where
  toFun x := lpTensor x y
  map_add' := fun x x' => lpTensor_add_left x x' y
  map_smul' := fun a x => lpTensor_smul_left a x y
  norm_map' := fun x => by
    show ‖lpTensor x y‖ = ‖x‖
    rw [norm_lpTensor, hy, mul_one]

@[simp] theorem lpTensorRight_apply {ι κ : Type*} (y : lp (fun _ : κ => ℂ) 2) (hy : ‖y‖ = 1)
    (x : lp (fun _ : ι => ℂ) 2) : lpTensorRight (ι := ι) y hy x = lpTensor x y := rfl

/-! ## The canonical isometry `V_σ` `(17)` -/

/-- **Equation (17).**  `V_σ x = U*(x ⊗ e_{2σ})`, the canonical linear, pointed, source-defined
isometry of the squarefree source into the Euler source. -/
def dyadicSquarefreeEmbed {σ : ℝ} (hσ2 : 1 < 2 * σ) :
    lp (fun _ : SquarefreePNat => ℂ) 2 →ₗᵢ[ℂ] EulerPositiveL2 :=
  (dyadicSquarefreeSignedUnitary.symm.toLinearIsometry).comp
    (lpTensorRight (ι := SquarefreePNat) (eulerPointedState hσ2)
      (norm_eulerPointedState hσ2))

theorem dyadicSquarefreeEmbed_apply {σ : ℝ} (hσ2 : 1 < 2 * σ)
    (x : lp (fun _ : SquarefreePNat => ℂ) 2) :
    dyadicSquarefreeEmbed hσ2 x
      = dyadicSquarefreeSignedUnitary.symm (lpTensor x (eulerPointedState hσ2)) := rfl

theorem dyadicSquarefreeSignedUnitary_embed {σ : ℝ} (hσ2 : 1 < 2 * σ)
    (x : lp (fun _ : SquarefreePNat => ℂ) 2) :
    dyadicSquarefreeSignedUnitary (dyadicSquarefreeEmbed hσ2 x)
      = lpTensor x (eulerPointedState hσ2) := by
  rw [dyadicSquarefreeEmbed_apply, LinearIsometryEquiv.apply_symm_apply]

/-- **Equation (18a).**  `V_σ s_σ = e_σ`. -/
theorem dyadicSquarefreeEmbed_squarefreePointedState {σ : ℝ} (hσ : 1 < σ) (hσ2 : 1 < 2 * σ) :
    dyadicSquarefreeEmbed hσ2 (squarefreePointedState hσ) = eulerPointedState hσ := by
  rw [dyadicSquarefreeEmbed_apply, ← dyadicSquarefreeSignedUnitary_eq_tensor hσ hσ2,
    LinearIsometryEquiv.symm_apply_apply]

/-- **Equation (18b).**  The tangent defect of the canonical isometry is exactly the
strict-right residual tangent. -/
theorem norm_eulerCenteredTangent_sub_embed (c : ℝ) {σ : ℝ} (hσ : 1 < σ) (hσ2 : 1 < 2 * σ) :
    ‖eulerCenteredTangent c hσ - dyadicSquarefreeEmbed hσ2 (squarefreeCenteredTangent c hσ)‖
      = ‖eulerCenteredTangent (2 * c) hσ2‖ := by
  have hU : dyadicSquarefreeSignedUnitary
      (eulerCenteredTangent c hσ
        - dyadicSquarefreeEmbed hσ2 (squarefreeCenteredTangent c hσ))
      = lpTensor (squarefreePointedState hσ) (eulerCenteredTangent (2 * c) hσ2) := by
    rw [map_sub, dyadicSignedUnitary_eulerCenteredTangent c hσ hσ2,
      dyadicSquarefreeSignedUnitary_embed]
    abel
  have hnorm := congrArg norm hU
  rw [LinearIsometryEquiv.norm_map] at hnorm
  rw [hnorm, norm_lpTensor, norm_squarefreePointedState hσ, one_mul]

/-! ## The orthogonal splitting `(15)` -/

/-- **Equation (15).**  `‖χ_E‖² = ‖χ_sq‖² + ‖r‖²`. -/
theorem normSq_eulerCenteredTangent_split (c : ℝ) {σ : ℝ} (hσ : 1 < σ) (hσ2 : 1 < 2 * σ) :
    ‖eulerCenteredTangent c hσ‖ ^ 2
      = ‖squarefreeCenteredTangent c hσ‖ ^ 2 + ‖eulerCenteredTangent (2 * c) hσ2‖ ^ 2 := by
  rw [normSq_eulerCenteredTangent, normSq_squarefreeCenteredTangent,
    normSq_eulerCenteredTangent, eulerLogVariance_split hσ]
  ring

/-! ## The polarized connection and its exact defect -/

theorem unitaryPush_rankOne {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] (u : H ≃ₗᵢ[ℂ] K) (x y : H) :
    unitaryPush u (rankOne ℂ x y) = rankOne ℂ (u x) (u y) := by
  refine ContinuousLinearMap.ext fun z => ?_
  simp only [unitaryPush_apply, rankOne_apply, map_smul]
  congr 1
  have h := LinearIsometryEquiv.inner_map_map u y (u.symm z)
  rw [LinearIsometryEquiv.apply_symm_apply] at h
  exact h.symm

theorem unitaryPush_pointedFisherConnection {H K : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (u : H ≃ₗᵢ[ℂ] K) (psi chi : H) :
    unitaryPush u (pointedFisherConnection psi chi)
      = pointedFisherConnection (u psi) (u chi) := by
  rw [pointedFisherConnection, pointedFisherConnection, unitaryPush_smul, unitaryPush_add,
    unitaryPush_rankOne, unitaryPush_rankOne]

theorem pointedFisherConnection_add_tangent {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (psi chi chi' : H) :
    pointedFisherConnection psi (chi + chi')
      = pointedFisherConnection psi chi + pointedFisherConnection psi chi' := by
  refine ContinuousLinearMap.ext fun z => ?_
  simp only [pointedFisherConnection, add_apply, smul_apply, rankOne_apply, inner_add_left,
    add_smul, smul_add]
  abel

theorem pointedFisherConnection_sub_tangent {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (psi chi chi' : H) :
    pointedFisherConnection psi chi - pointedFisherConnection psi chi'
      = pointedFisherConnection psi (chi - chi') := by
  have h := pointedFisherConnection_add_tangent psi (chi - chi') chi'
  rw [sub_add_cancel] at h
  rw [h]
  abel

/-- **Equation (21).**  The exact transport of the polarized rank-two Fisher connection: under the
signed arithmetic unitary it becomes the sum of the squarefree connection tensored with the
residual state projector and the squarefree state projector tensored with the residual
connection, both written as pointed connections of elementary tensors. -/
theorem unitaryPush_fisherConnection_split (c : ℝ) {σ : ℝ} (hσ : 1 < σ) (hσ2 : 1 < 2 * σ) :
    unitaryPush dyadicSquarefreeSignedUnitary
        (pointedFisherConnection (eulerPointedState hσ) (eulerCenteredTangent c hσ))
      = pointedFisherConnection
          (lpTensor (squarefreePointedState hσ) (eulerPointedState hσ2))
          (lpTensor (squarefreeCenteredTangent c hσ) (eulerPointedState hσ2))
        + pointedFisherConnection
          (lpTensor (squarefreePointedState hσ) (eulerPointedState hσ2))
          (lpTensor (squarefreePointedState hσ) (eulerCenteredTangent (2 * c) hσ2)) := by
  rw [unitaryPush_pointedFisherConnection, dyadicSquarefreeSignedUnitary_eq_tensor hσ hσ2,
    dyadicSignedUnitary_eulerCenteredTangent c hσ hσ2, pointedFisherConnection_add_tangent]

/-- **Equation (22)–(23).**  The Hilbert–Schmidt defect between the Euler Fisher connection and
the transported squarefree Fisher connection is exactly the strict-right residual energy. -/
theorem hsNormSq_fisherConnection_defect (c : ℝ) {σ : ℝ} (hσ : 1 < σ) (hσ2 : 1 < 2 * σ) :
    hsNormSq
        (pointedFisherConnection (eulerPointedState hσ) (eulerCenteredTangent c hσ)
          - pointedFisherConnection (eulerPointedState hσ)
              (dyadicSquarefreeEmbed hσ2 (squarefreeCenteredTangent c hσ)))
      = ‖eulerCenteredTangent (2 * c) hσ2‖ ^ 2 := by
  have horthE := inner_eulerPointedState_eulerCenteredTangent c hσ
  have horthS := inner_squarefreePointedState_squarefreeCenteredTangent c hσ
  have hembed : (inner ℂ (eulerPointedState hσ)
      (dyadicSquarefreeEmbed hσ2 (squarefreeCenteredTangent c hσ)) : ℂ) = 0 := by
    rw [← dyadicSquarefreeEmbed_squarefreePointedState hσ hσ2,
      LinearIsometry.inner_map_map]
    exact horthS
  have horth : (inner ℂ (eulerPointedState hσ)
      (eulerCenteredTangent c hσ
        - dyadicSquarefreeEmbed hσ2 (squarefreeCenteredTangent c hσ)) : ℂ) = 0 := by
    rw [inner_sub_right, horthE, hembed, sub_zero]
  rw [pointedFisherConnection_sub_tangent,
    hsNormSq_pointedFisherConnection_of_unit_of_orthogonal _ _
      (norm_eulerPointedState hσ) horth,
    norm_eulerCenteredTangent_sub_embed c hσ hσ2]

/-! ## The residual energy vanishes at the critical boundary `(16)` -/

/-- The card's strict-right residual energy `‖r_σ‖² = 16 ε² Var_{2σ}(log m)`, `ε = σ − 1`. -/
def criticalResidualEnergy (σ : ℝ) : ℝ := 16 * (σ - 1) ^ 2 * eulerLogVariance (2 * σ)

theorem normSq_criticalResidualTangent {σ : ℝ} (hσ2 : 1 < 2 * σ) :
    ‖eulerCenteredTangent (2 * (-2 * (σ - 1))) hσ2‖ ^ 2 = criticalResidualEnergy σ := by
  rw [normSq_eulerCenteredTangent, criticalResidualEnergy]
  ring

theorem one_le_eulerMass {σ : ℝ} (hσ : 1 < σ) : 1 ≤ eulerMass σ := by
  have hs := summable_pnat_rpow hσ
  have hle : ((1 : ℕ+) : ℝ) ^ (-σ) ≤ eulerMass σ :=
    hs.le_tsum 1 (fun n _ => le_of_lt (by positivity))
  simpa using hle

theorem eulerLogPowMass_nonneg (k : ℕ) {σ : ℝ} (hσ : 1 < σ) : 0 ≤ eulerLogPowMass k σ :=
  tsum_nonneg fun n => logpow_rpow_nonneg k n

theorem eulerLogPowMass_two_antitone {σ : ℝ} (hσ : 1 < σ) (hle : 2 ≤ 2 * σ) :
    eulerLogPowMass 2 (2 * σ) ≤ eulerLogPowMass 2 2 := by
  have hσ2 : 1 < 2 * σ := by linarith
  refine Summable.tsum_le_tsum (fun n => ?_) (summable_pnat_logpow_rpow 2 hσ2)
    (summable_pnat_logpow_rpow 2 (by norm_num : (1 : ℝ) < 2))
  have hn : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast n.property
  have hexp : (n : ℝ) ^ (-(2 * σ)) ≤ (n : ℝ) ^ (-(2 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hn (by linarith)
  have hlog : 0 ≤ Real.log (n : ℝ) ^ 2 := by positivity
  exact mul_le_mul_of_nonneg_left hexp hlog

/-- On `(1, 3/2]` the residual variance is bounded by a fixed constant. -/
theorem eulerLogVariance_le_const {σ : ℝ} (hσ : 1 < σ) :
    eulerLogVariance (2 * σ) ≤ eulerLogPowMass 2 2 := by
  have hσ2 : 1 < 2 * σ := by linarith
  have hM : 1 ≤ eulerMass (2 * σ) := one_le_eulerMass hσ2
  have hMpos : 0 < eulerMass (2 * σ) := by linarith
  have hSM : 0 ≤ eulerLogPowMass 2 (2 * σ) := eulerLogPowMass_nonneg 2 hσ2
  have hdiv : eulerLogPowMass 2 (2 * σ) / eulerMass (2 * σ) ≤ eulerLogPowMass 2 (2 * σ) := by
    rw [div_le_iff₀ hMpos]
    nlinarith
  have hmono : eulerLogPowMass 2 (2 * σ) ≤ eulerLogPowMass 2 2 :=
    eulerLogPowMass_two_antitone hσ (by linarith)
  have hmean : 0 ≤ (eulerLogMean (2 * σ)) ^ 2 := by positivity
  rw [eulerLogVariance]
  linarith

/-- **Equation (16).**  The strict-right residual energy tends to zero as `σ → 1⁺`, so the
canonical isometry `V_σ` is an asymptotic isometry of the critical Fisher tangents. -/
theorem tendsto_criticalResidualEnergy :
    Tendsto criticalResidualEnergy (𝓝[>] (1 : ℝ)) (𝓝 0) := by
  have hbound : Tendsto (fun σ : ℝ => 16 * (σ - 1) ^ 2 * eulerLogPowMass 2 2)
      (𝓝[>] (1 : ℝ)) (𝓝 0) := by
    have hcont : Continuous (fun σ : ℝ => 16 * (σ - 1) ^ 2 * eulerLogPowMass 2 2) := by
      fun_prop
    have h : Tendsto (fun σ : ℝ => 16 * (σ - 1) ^ 2 * eulerLogPowMass 2 2) (𝓝[>] (1 : ℝ))
        (𝓝 (16 * ((1 : ℝ) - 1) ^ 2 * eulerLogPowMass 2 2)) :=
      (hcont.tendsto (1 : ℝ)).mono_left nhdsWithin_le_nhds
    simpa using h
  refine squeeze_zero' ?_ ?_ hbound
  · filter_upwards [self_mem_nhdsWithin] with σ hσ
    have hσ' : (1 : ℝ) < σ := hσ
    have hvar : 0 ≤ eulerLogVariance (2 * σ) :=
      eulerLogVariance_nonneg (by linarith : (1 : ℝ) < 2 * σ)
    rw [criticalResidualEnergy]
    positivity
  · filter_upwards [self_mem_nhdsWithin] with σ hσ
    have hσ' : (1 : ℝ) < σ := hσ
    have hle := eulerLogVariance_le_const hσ'
    have hsq : (0 : ℝ) ≤ 16 * (σ - 1) ^ 2 := by positivity
    rw [criticalResidualEnergy]
    exact mul_le_mul_of_nonneg_left hle hsq

end RHTower
