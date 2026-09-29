import GaloisForLFunctions.HTGeometry.CayleyCollisionColligation

/-!
# The Hodge collision record of the exponential clock pair

For `μ(dx) = e^{-x} dx` and the pair law `μ ⊗ μ`, the Cayley collision colligation has
normalizer `Z = 8/105`, so its oriented state is the Hodge collision amplitude
`Ω_H = √(105/8) δ(1 - δ²)`, and:

* **(A)** `‖Ω_H‖ = 1` and `⟪Ω_H, F(λ) Ω_H⟫ = ∫ F dBeta(3/2, 3)` for every bounded measurable `F`;
* **(B)** the observability map `(O f)_n = E₀ Sⁿ f` is an isometry, with the operator telescope
  `∑_{n < N} S*ⁿ E₀* E₀ Sⁿ + S*ᴺ Sᴺ = 1`;
* the survival and exit masses are `‖Sⁿ Ω_H‖² = m_n = 105/((2n+3)(2n+5)(2n+7))` and
  `‖e_n‖² = w_n = 630/((2n+3)(2n+5)(2n+7)(2n+9))`, with `e_n = √(105/8) δⁿ⁺¹ κ`;
* **(C)** the record `𝖳 = ⊕ₙ |e_n⟩⟨e_n|` is positive, self-adjoint, nuclear, with
  `tr 𝖳 = ‖𝖳‖₁ = 1`, `‖𝖳‖ = w_0 = 2/3`, tail traces `m_n`, integral kernel
  `1_{n=k} e_n(z) conj(e_n(z'))`, and signed section `sign(t) 𝖳`;
* **(orientation)** the swap `J` gives `J Ω_H = -Ω_H`, `J S J = -S`, `J E₀ J = E₀`,
  `J e_n = (-1)ⁿ⁺¹ e_n`, `(1 ⊗ J) 𝖳 (1 ⊗ J) = 𝖳`, while the `(n, k)` block of the lifted pure state
  `|O Ω_H⟩⟨O Ω_H|` changes by `(-1)ⁿ⁺ᵏ`.
-/

open MeasureTheory Filter Topology Set ProbabilityTheory ContinuousLinearMap
open scoped ENNReal NNReal ComplexConjugate InnerProductSpace

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open _root_.RHTower

local instance isProbabilityMeasure_expMeasure_one_record : IsProbabilityMeasure (expMeasure 1) :=
  isProbabilityMeasure_expMeasure one_pos

local instance factOneLeTwoRecord : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩

/-! ## Swap orientation for a symmetric pair law -/

section Swap

variable {ν : Measure (ℝ × ℝ)} (hswap : MeasurePreserving Prod.swap ν ν)

/-- The swap `J f = f ∘ swap`. -/
def pairSwap : Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 ν := compL2 hswap

include hswap in
theorem pairSwap_coeFn_of_ae {f : Lp ℂ 2 ν} {F : ℝ × ℝ → ℂ} (h : (f : ℝ × ℝ → ℂ) =ᵐ[ν] F) :
    (pairSwap hswap f : ℝ × ℝ → ℂ) =ᵐ[ν] F ∘ Prod.swap :=
  (compL2_coeFn hswap f).trans (h.comp_tendsto hswap.quasiMeasurePreserving.tendsto_ae)

theorem pairSwap_comp_pairSwap : pairSwap hswap ∘L pairSwap hswap = ContinuousLinearMap.id ℂ _ :=
  compL2_comp_compL2 hswap hswap (Eventually.of_forall fun z => Prod.swap_swap z)

theorem adjoint_pairSwap : adjoint (pairSwap hswap) = pairSwap hswap := by
  have hiso : adjoint (pairSwap hswap) ∘L pairSwap hswap = 1 :=
    (ContinuousLinearMap.norm_map_iff_adjoint_comp_self _).mp (norm_compL2_apply hswap)
  calc adjoint (pairSwap hswap)
      = adjoint (pairSwap hswap) ∘L (pairSwap hswap ∘L pairSwap hswap) := by
        rw [pairSwap_comp_pairSwap, comp_id]
    _ = pairSwap hswap := by rw [← comp_assoc, hiso, one_def, id_comp]

/-- `J M_φ J = M_{φ ∘ swap}`. -/
theorem pairSwap_conj_contractionMul {φ : ℝ × ℝ → ℝ} (hφ : Measurable φ)
    (hb : ∀ z, |φ z| ≤ 1) :
    pairSwap hswap ∘L contractionMul ν hφ hb ∘L pairSwap hswap
      = contractionMul ν (hφ.comp measurable_swap) (fun z => hb z.swap) := by
  ext1 f
  refine Lp.ext ?_
  have h1 := pairSwap_coeFn_of_ae hswap (contractionMul_coeFn ν hφ hb (pairSwap hswap f))
  have h2 : (fun z => (φ z : ℂ) * ((pairSwap hswap f : Lp ℂ 2 ν) : ℝ × ℝ → ℂ) z) ∘ Prod.swap
      =ᵐ[ν] fun z => (φ z.swap : ℂ) * (f : ℝ × ℝ → ℂ) z := by
    filter_upwards [pairSwap_coeFn_of_ae hswap (f := f) (F := (f : ℝ × ℝ → ℂ)) EventuallyEq.rfl
      |>.comp_tendsto hswap.quasiMeasurePreserving.tendsto_ae] with z hz
    simp only [Function.comp_apply] at hz ⊢
    rw [hz, Prod.swap_swap]
  filter_upwards [h1, h2, contractionMul_coeFn ν (hφ.comp measurable_swap) (fun z => hb z.swap) f]
    with z hz1 hz2 hz3
  rw [comp_apply, comp_apply, hz1, hz2, hz3]
  rfl

theorem contractionMul_neg {φ : ℝ × ℝ → ℝ} (hφ : Measurable φ) (hb : ∀ z, |φ z| ≤ 1) :
    contractionMul ν hφ.neg (fun z => by rw [Pi.neg_apply, abs_neg]; exact hb z)
      = -contractionMul ν hφ hb := by
  ext1 f
  refine Lp.ext ?_
  filter_upwards [contractionMul_coeFn ν hφ.neg
      (fun z => by rw [Pi.neg_apply, abs_neg]; exact hb z) f,
    contractionMul_coeFn ν hφ hb f, Lp.coeFn_neg (contractionMul ν hφ hb f)] with z h1 h2 h3
  rw [neg_apply, h1, h3]
  simp only [Pi.neg_apply]
  rw [h2]
  push_cast
  ring

/-- **(CCRHD.17a).**  `J S J = -S`. -/
theorem pairSwap_conj_collisionSurvival :
    pairSwap hswap ∘L collisionSurvival ν ∘L pairSwap hswap = -collisionSurvival ν := by
  rw [collisionSurvival, pairSwap_conj_contractionMul, ← contractionMul_neg]
  exact contractionMul_congr ν _ _ _ _ (Eventually.of_forall fun z => by
    simp only [Function.comp_apply, Pi.neg_apply]
    exact pairContrast_swap z)

/-- **(CCRHD.17a).**  `J E₀ J = E₀`. -/
theorem pairSwap_conj_collisionExit :
    pairSwap hswap ∘L collisionExit ν ∘L pairSwap hswap = collisionExit ν := by
  rw [collisionExit, pairSwap_conj_contractionMul]
  exact contractionMul_congr ν _ _ _ _ (Eventually.of_forall fun z => pairCoherence_swap z)

variable [IsFiniteMeasure ν]

/-- **(CCRHD.17a).**  `J e_n = (-1)ⁿ⁺¹ e_n`; the case `J Ω = -Ω` is `pairSwap_collisionState`. -/
theorem pairSwap_collisionExitVector (n : ℕ) :
    pairSwap hswap (collisionExitVector ν n) = ((-1 : ℂ) ^ (n + 1)) • collisionExitVector ν n := by
  refine Lp.ext ?_
  filter_upwards [pairSwap_coeFn_of_ae hswap (collisionExitVector_coeFn ν n),
    Lp.coeFn_smul ((-1 : ℂ) ^ (n + 1)) (collisionExitVector ν n),
    collisionExitVector_coeFn ν n] with z h1 h2 h3
  rw [h1, h2, Pi.smul_apply, h3, Function.comp_apply, collisionAmplitude, collisionAmplitude,
    pairCoherence_swap, pairContrast_swap, collisionProfile_swap, smul_eq_mul]
  push_cast
  ring

theorem pairSwap_collisionState :
    pairSwap hswap (collisionState ν) = -collisionState ν := by
  refine Lp.ext ?_
  filter_upwards [pairSwap_coeFn_of_ae hswap (collisionState_coeFn ν),
    Lp.coeFn_neg (collisionState ν), collisionState_coeFn ν] with z h1 h2 h3
  rw [h1, h2, Pi.neg_apply, h3, Function.comp_apply, collisionAmplitude, collisionAmplitude,
    collisionProfile_swap]
  push_cast
  ring

/-- The lifted swap `1 ⊗ J` on `ℓ²(ℕ; L²(ν))`. -/
def historySwap : HistoryL2 (Lp ℂ 2 ν) →L[ℂ] HistoryL2 (Lp ℂ 2 ν) :=
  historyMap (fun _ => 1) (fun _ => norm_one.le) (pairSwap hswap)

omit [IsFiniteMeasure ν] in
theorem adjoint_historySwap : adjoint (historySwap hswap) = historySwap hswap := by
  rw [historySwap, adjoint_historyMap, adjoint_pairSwap]
  exact historyMap_congr _ _ (funext fun _ => map_one _) _

theorem norm_neg_one_pow (n : ℕ) : ‖(-1 : ℂ) ^ (n + 1)‖ = 1 := by
  rw [norm_pow, norm_neg, norm_one, one_pow]

variable (hν : ∀ᵐ z ∂ν, 0 < z.1 ∧ 0 < z.2)

/-- **(CCRHD.17a).**  `(1 ⊗ J) 𝖳 (1 ⊗ J) = 𝖳`: every diagonal block loses its sign. -/
theorem historySwap_conj_collisionRecord :
    historySwap hswap ∘L collisionRecord ν hν ∘L historySwap hswap = collisionRecord ν hν := by
  have hsum : Summable fun n => ‖pairSwap hswap (collisionExitVector ν n)‖ ^ 2 :=
    (summable_norm_collisionExitVector_sq ν hν).congr fun n => by
      rw [pairSwap, norm_compL2_apply]
  have hsum' : Summable fun n => ‖((-1 : ℂ) ^ (n + 1)) • collisionExitVector ν n‖ ^ 2 :=
    (summable_norm_collisionExitVector_sq ν hν).congr fun n => by
      rw [norm_smul, norm_neg_one_pow, one_mul]
  calc historySwap hswap ∘L collisionRecord ν hν ∘L historySwap hswap
      = historySwap hswap ∘L collisionRecord ν hν ∘L adjoint (historySwap hswap) := by
        rw [adjoint_historySwap]
    _ = recordOp (fun n => pairSwap hswap (collisionExitVector ν n)) hsum :=
        recordOp_conj_historyMap (collisionExitVector ν)
          (summable_norm_collisionExitVector_sq ν hν) (pairSwap hswap) hsum
    _ = recordOp (fun n => ((-1 : ℂ) ^ (n + 1)) • collisionExitVector ν n) hsum' :=
        recordOp_congr _ _ _ (funext fun n => pairSwap_collisionExitVector hswap n)
    _ = collisionRecord ν hν :=
        recordOp_phase _ _ (fun n => norm_neg_one_pow n) hsum'

omit [IsFiniteMeasure ν] in
theorem historySwap_single (k : ℕ) (y : Lp ℂ 2 ν) :
    historySwap hswap (lp.single 2 k y) = lp.single 2 k (pairSwap hswap y) := by
  rw [historySwap, historyMap_single, one_smul]

/-- **(CCRHD.17a), cross-grade coherence.**  The `(n, k)` block of the lifted pure state
`|O Ω⟩⟨O Ω|` changes by `(-1)ⁿ⁺ᵏ` under `1 ⊗ J`. -/
theorem inner_historySwap_conj_rankOne (n k : ℕ) (x y : Lp ℂ 2 ν) :
    ⟪(lp.single 2 n x : HistoryL2 (Lp ℂ 2 ν)), (historySwap hswap ∘L
        historyRankOne (collisionObservability ν hν (collisionState ν)) ∘L historySwap hswap)
        (lp.single 2 k y)⟫_ℂ
      = (-1 : ℂ) ^ (n + k) * ⟪(lp.single 2 n x : HistoryL2 (Lp ℂ 2 ν)),
          historyRankOne (collisionObservability ν hν (collisionState ν)) (lp.single 2 k y)⟫_ℂ := by
  rw [comp_apply, comp_apply, ← adjoint_inner_left, adjoint_historySwap, historySwap_single,
    historySwap_single, inner_single_historyRankOne_single, inner_single_historyRankOne_single,
    collisionObservability_state, collisionObservability_state, ← adjoint_inner_right,
    adjoint_pairSwap, pairSwap_collisionExitVector, ← adjoint_inner_left, adjoint_pairSwap,
    pairSwap_collisionExitVector, inner_smul_right, inner_smul_left]
  simp only [map_pow, map_neg, map_one]
  ring

end Swap

/-! ## The exponential clock pair -/

section ExpPair

/-- The unit exponential clock-pair law `μ ⊗ μ`. -/
abbrev expPairLaw : Measure (ℝ × ℝ) := (expMeasure 1).prod (expMeasure 1)

theorem pairContrast_ae_eq :
    ∀ᵐ z ∂expPairLaw, pairContrast z = cayleyContrast z.1 z.2 := by
  filter_upwards [ae_pos_expPair] with z hz
  exact pairContrast_of_pos hz.1 hz.2

theorem collisionProfile_sq_eq (z : ℝ × ℝ) :
    collisionProfile z ^ 2 = 8 / 105 * hodgeCollisionAmplitude (pairContrast z) ^ 2 := by
  rw [hodgeCollisionAmplitude_sq, collisionProfile]
  ring

/-- `Z = ∬ δ²(1 - δ²)² dμ dμ = 8/105`. -/
theorem collisionMass_expPair : collisionMass expPairLaw = 8 / 105 := by
  rw [collisionMass]
  simp_rw [collisionProfile_sq_eq]
  rw [integral_const_mul]
  have h : ∫ z, hodgeCollisionAmplitude (pairContrast z) ^ 2 ∂expPairLaw = 1 := by
    rw [← integral_hodgeCollision_sq]
    refine integral_congr_ae ?_
    filter_upwards [pairContrast_ae_eq] with z hz
    rw [hz]
  rw [h, mul_one]

/-- The collision amplitude of `μ ⊗ μ` is the Hodge amplitude `√(105/8) δ(1 - δ²)`. -/
theorem collisionAmplitude_expPair (z : ℝ × ℝ) :
    collisionAmplitude expPairLaw z = hodgeCollisionAmplitude (pairContrast z) := by
  rw [collisionAmplitude, collisionMass_expPair, hodgeCollisionAmplitude, collisionProfile,
    ← Real.sqrt_inv, inv_div]

/-- The Hodge collision state `Ω_H ∈ L²(μ ⊗ μ)`. -/
abbrev hodgeCollisionState : Lp ℂ 2 expPairLaw := collisionState expPairLaw

theorem hodgeCollisionState_coeFn :
    (hodgeCollisionState : ℝ × ℝ → ℂ) =ᵐ[expPairLaw]
      fun z => (hodgeCollisionAmplitude (cayleyContrast z.1 z.2) : ℂ) := by
  filter_upwards [collisionState_coeFn expPairLaw, pairContrast_ae_eq] with z h1 h2
  rw [h1, collisionAmplitude_expPair, h2]

theorem collisionMass_expPair_pos : 0 < collisionMass expPairLaw := by
  rw [collisionMass_expPair]
  norm_num

/-- **Theorem CCRHD-A.**  `‖Ω_H‖ = 1`. -/
theorem norm_hodgeCollisionState : ‖hodgeCollisionState‖ = 1 :=
  norm_collisionState expPairLaw collisionMass_expPair_pos

theorem norm_ofReal_le_of_abs_le {r C : ℝ} (h : |r| ≤ C) : ‖(r : ℂ)‖ ≤ C := by
  rw [Complex.norm_real, Real.norm_eq_abs]
  exact h

theorem measurable_ofReal_comp_contrast_sq {F : ℝ → ℝ} (hF : Measurable F) :
    Measurable fun z : ℝ × ℝ => ((F (pairContrast z ^ 2) : ℝ) : ℂ) :=
  Complex.measurable_ofReal.comp (hF.comp (measurable_pairContrast.pow_const 2))

/-- **Theorem CCRHD-A, (CCRHD.3).**  `⟪Ω_H, F(λ) Ω_H⟫ = ∫₀¹ F(a) (105/16) a^{1/2}(1 - a)² da`. -/
theorem inner_hodgeCollisionState_functionalCalculus {F : ℝ → ℝ} (hF : Measurable F) {C : ℝ}
    (hC0 : 0 ≤ C) (hC : ∀ a, |F a| ≤ C) :
    ⟪hodgeCollisionState, lpBoundedMulCLM (p := 2) (μ := expPairLaw)
        (φ := fun z => ((F (pairContrast z ^ 2) : ℝ) : ℂ))
        (measurable_ofReal_comp_contrast_sq hF) hC0 (fun _ => norm_ofReal_le_of_abs_le (hC _))
        hodgeCollisionState⟫_ℂ
      = ((∫ a, F a ∂phaseBetaLaw : ℝ) : ℂ) := by
  rw [L2.inner_def, ← integral_hodgeCollision_sq_mul hF (fun a _ => hC a),
    ← integral_complex_ofReal]
  refine integral_congr_ae ?_
  filter_upwards [lpBoundedMulCLM_coeFn (p := 2) (μ := expPairLaw)
    (measurable_ofReal_comp_contrast_sq hF) hC0 (fun _ => norm_ofReal_le_of_abs_le (hC _))
    hodgeCollisionState,
    hodgeCollisionState_coeFn, pairContrast_ae_eq] with z h1 h2 h3
  rw [h1, h2, h3, RCLike.inner_apply, Complex.conj_ofReal]
  push_cast
  ring

/-- **(CCRHD.10).**  `‖Sⁿ Ω_H‖² = m_n = E[λⁿ] = 105/((2n+3)(2n+5)(2n+7))`. -/
theorem norm_survival_pow_hodgeCollisionState_sq (n : ℕ) :
    ‖(collisionSurvival expPairLaw ^ n) hodgeCollisionState‖ ^ 2 = PrimeHodgeHistory.m n := by
  rw [norm_collisionSurvival_pow_state_sq, collisionMass_expPair, ← homotopyEnergy_eq_m,
    homotopyEnergy_eq_beta_moment,
    ← integral_hodgeCollision_sq_mul (F := fun a => a ^ n) (measurable_id.pow_const n) (C := 1)
      (fun a ha => by
        rw [abs_of_nonneg (pow_nonneg ha.1 n)]
        exact pow_le_one₀ ha.1 ha.2.le),
    ← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [pairContrast_ae_eq] with z hz
  rw [collisionProfile_sq_eq, hz]
  ring

/-- **(CCRHD.10).**  `‖e_n‖² = w_n = 630/((2n+3)(2n+5)(2n+7)(2n+9))`. -/
theorem norm_hodgeExitVector_sq (n : ℕ) :
    ‖collisionExitVector expPairLaw n‖ ^ 2 = PrimeHodgeHistory.w n := by
  rw [norm_collisionExitVector_sq, norm_survival_pow_hodgeCollisionState_sq,
    norm_survival_pow_hodgeCollisionState_sq, PrimeHodgeHistory.w]

/-- **(CCRHD.17).**  `e_n = √(105/8) δⁿ⁺¹ κ`. -/
theorem hodgeExitVector_coeFn (n : ℕ) :
    (collisionExitVector expPairLaw n : ℝ × ℝ → ℂ) =ᵐ[expPairLaw]
      fun z => ((Real.sqrt (105 / 8) * cayleyContrast z.1 z.2 ^ (n + 1) *
        wallCubicKernel z.1 z.2 : ℝ) : ℂ) := by
  filter_upwards [collisionExitVector_coeFn expPairLaw n, ae_pos_expPair] with z h1 hz
  rw [h1]
  congr 1
  obtain ⟨-, -, h3⟩ := cayley_pair_identities hz.1 hz.2
  have hδ : pairContrast z = cayleyContrast z.1 z.2 := pairContrast_of_pos hz.1 hz.2
  have hg := pairCoherence_sq z
  rw [collisionAmplitude_expPair, hodgeCollisionAmplitude, h3, ← hδ]
  rw [pairCoherence] at hg ⊢
  rw [show Real.sqrt (1 - pairContrast z ^ 2) ^ 3
      = Real.sqrt (1 - pairContrast z ^ 2) * Real.sqrt (1 - pairContrast z ^ 2) ^ 2 by ring, hg]
  ring

theorem hν_expPair : ∀ᵐ z ∂expPairLaw, 0 < z.1 ∧ 0 < z.2 := ae_pos_expPair

/-- **(CCRHD.12).**  The Hodge collision record `𝖳 = ⊕ₙ |e_n⟩⟨e_n|`. -/
abbrev hodgeCollisionRecord : HistoryL2 (Lp ℂ 2 expPairLaw) →L[ℂ] HistoryL2 (Lp ℂ 2 expPairLaw) :=
  collisionRecord expPairLaw hν_expPair

/-- **Theorem CCRHD-C.**  `𝖳 ≥ 0`, `𝖳* = 𝖳`, `𝖳 ∈ S₁`, `tr 𝖳 = ‖𝖳‖₁ = 1`, `‖𝖳‖ = w_0 = 2/3 < 1`,
and `tr((Q_n ⊗ 1) 𝖳) = m_n`. -/
theorem hodgeCollisionRecord_nuclear :
    hodgeCollisionRecord.IsPositive ∧ MemSchattenClass 1 hodgeCollisionRecord ∧
      adjoint hodgeCollisionRecord = hodgeCollisionRecord ∧
      opTrace hodgeCollisionRecord = 1 ∧
      traceNorm (HistoryL2 (Lp ℂ 2 expPairLaw)) hodgeCollisionRecord = 1 ∧
      ‖hodgeCollisionRecord‖ = 2 / 3 ∧
      ∀ n, opTrace (historyTailProjection n ∘L hodgeCollisionRecord)
        = (PrimeHodgeHistory.m n : ℂ) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := collisionRecord_nuclear hν_expPair collisionMass_expPair_pos
  refine ⟨h1, h2, h3, h4, h5, ?_, fun n => ?_⟩
  · rw [norm_collisionRecord, norm_hodgeExitVector_sq, PrimeHodgeHistory.w_zero]
  · rw [opTrace_historyTail_collisionRecord, norm_survival_pow_hodgeCollisionState_sq]

/-- **(CCRHD.13).**  The integral kernel `𝖳((n; z), (k; z')) = 1_{n=k} e_n(z) conj(e_n(z'))`. -/
theorem hodgeCollisionRecord_apply_coeFn (f : HistoryL2 (Lp ℂ 2 expPairLaw)) (n : ℕ) :
    ((hodgeCollisionRecord f n : Lp ℂ 2 expPairLaw) : ℝ × ℝ → ℂ) =ᵐ[expPairLaw]
      fun z => (∫ z', conj ((collisionExitVector expPairLaw n : ℝ × ℝ → ℂ) z') *
          ((f n : Lp ℂ 2 expPairLaw) : ℝ × ℝ → ℂ) z' ∂expPairLaw) *
        (collisionExitVector expPairLaw n : ℝ × ℝ → ℂ) z := by
  rw [hodgeCollisionRecord, collisionRecord, recordOp_apply, L2.inner_def]
  filter_upwards [Lp.coeFn_smul (∫ a, ⟪(collisionExitVector expPairLaw n : ℝ × ℝ → ℂ) a,
    ((f n : Lp ℂ 2 expPairLaw) : ℝ × ℝ → ℂ) a⟫_ℂ ∂expPairLaw) (collisionExitVector expPairLaw n)]
    with z hz
  rw [hz, Pi.smul_apply, smul_eq_mul]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun a => ?_)
  simp only [RCLike.inner_apply]
  ring

/-- **(CCRHD.15a).**  The signed section `𝖳(t) = sign(t) 𝖳` has `tr 𝖳(t) = sign t` and is odd. -/
theorem hodgeCollisionRecord_signed (t : ℝ) :
    opTrace (((Real.sign t : ℝ) : ℂ) • hodgeCollisionRecord) = ((Real.sign t : ℝ) : ℂ) ∧
      ((Real.sign (-t) : ℝ) : ℂ) • hodgeCollisionRecord
        = -(((Real.sign t : ℝ) : ℂ) • hodgeCollisionRecord) := by
  refine ⟨?_, ?_⟩
  · rw [GaloisForLFunctions.HTGeometry.opTrace_smul, (hodgeCollisionRecord_nuclear).2.2.2.1,
      mul_one]
  · rw [Real.sign_neg, Complex.ofReal_neg, neg_smul]

/-- **Theorem CCRHD-B.**  The observability map of the exponential pair is an isometry and the
operator telescope holds. -/
theorem hodgeCollision_observability :
    (∀ f, ‖collisionObservability expPairLaw hν_expPair f‖ = ‖f‖) ∧
      (∀ N, ∑ n ∈ Finset.range N, adjoint (collisionSurvival expPairLaw ^ n) ∘L
          adjoint (collisionExit expPairLaw) ∘L collisionExit expPairLaw ∘L
            collisionSurvival expPairLaw ^ n
          + adjoint (collisionSurvival expPairLaw ^ N) ∘L collisionSurvival expPairLaw ^ N
        = ContinuousLinearMap.id ℂ _) ∧
      ∀ f, Tendsto (fun N => (collisionSurvival expPairLaw ^ N) f) atTop (𝓝 0) :=
  ⟨(collisionObservability_isometry expPairLaw hν_expPair).1,
    colligation_telescope (collision_colligation expPairLaw),
    collision_stable expPairLaw hν_expPair⟩

/-- The swap is measure-preserving for `μ ⊗ μ`. -/
theorem measurePreserving_swap_expPair : MeasurePreserving Prod.swap expPairLaw expPairLaw :=
  Measure.measurePreserving_swap

end ExpPair

end GaloisForLFunctions.HTGeometry
