import GaloisForLFunctions.HTGeometry.GraphActionFiltration
import GaloisForLFunctions.HTGeometry.BurnolHalfLineWeightedShift
import GaloisForLFunctions.RHTower.BurnolBaseGraphCapArea
import GaloisForLFunctions.RHTower.RoutePPrimitiveBurnolApertureDampingSemigroup

/-!
# The Burnol aperture damping filtration of the all-prime graph cap

The forward weighted translation `(S_c f)(t) = t/(t+c) f(t+c)` is a contraction semigroup on the
half-line `L²` space with `S_0 = I`.  Every primitive window feature is an eigenvector,
**(BGAF.8)** `S_c f_{pe,κ} = e^{-c(λ_pe + iκ)} f_{pe,κ}` with `λ_pe` the primitive log frequency.
Hence for `A_c = S_c A_base`

**(BGAF.9)** `‖A_c‖²_HS = ∑ e^{-2cλ_pe} w_pe → 0`,

and the abstract filtration theorem gives **(BGAF.10)**: `E_base` is antitone, `E_base(c) → 0`, and the
total action is `E_base(0) < 1`.  For every finite packet the Gram loss between two damping times is
the damped conjugate of the hard-boundary and tail-cocycle defect Grams **(BGAF.11)**.
-/

open MeasureTheory Set Filter Topology ContinuousLinearMap Complex
open scoped NNReal InnerProductSpace
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

local instance burnolFilterFactTwoNeTop : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩

local instance burnolFilterIndexMeasurableSpace : MeasurableSpace RoutePPrimitiveIndex := ⊤

/-! ## The damping semigroup -/

theorem burnolWeightedShift_zero : burnolWeightedShift 0 = 1 := by
  refine ContinuousLinearMap.ext fun f => Lp.ext ?_
  filter_upwards [burnolWeightedShift_coeFn 0 f, ae_restrict_mem measurableSet_Ioi] with t h1 ht
  rw [h1, one_apply_eq_self]
  have ht' : (0 : ℝ) < t := ht
  simp [ht'.ne']

theorem burnolWeightedShift_add (h c : ℝ≥0) :
    burnolWeightedShift (h + c) = burnolWeightedShift h ∘L burnolWeightedShift c :=
  (burnolWeightedShift_comp h c).symm

/-- **(BGAF.8)** Every primitive window feature is an eigenvector of the damping semigroup. -/
theorem burnolWeightedShift_windowFeatureLp (c : ℝ≥0) (pe : Nat.Primes × ℕ) (κ : ℝ) :
    burnolWeightedShift c (routePPrimitiveBurnolWindowFeatureLp pe κ) =
      Complex.exp (-(((c : ℝ) : ℂ) * ((xiGammaEulerPrimitiveLogFrequency pe : ℂ) + I * (κ : ℂ)))) •
        routePPrimitiveBurnolWindowFeatureLp pe κ := by
  have hmem := memLp_routePBurnolHalfLine (continuous_routePPrimitiveBurnolWindowFeature pe κ)
    (integrableOn_norm_sq_routePPrimitiveBurnolWindowFeature pe κ)
  have hcoe : (routePPrimitiveBurnolWindowFeatureLp pe κ : ℝ → ℂ) =ᵐ[volume.restrict (Ioi 0)]
      routePPrimitiveBurnolWindowFeature pe κ := hmem.coeFn_toLp
  refine Lp.ext ?_
  have h2 := (quasiMeasurePreserving_add_right_Ioi c.coe_nonneg).ae_eq_comp hcoe
  filter_upwards [burnolWeightedShift_coeFn c (routePPrimitiveBurnolWindowFeatureLp pe κ), h2,
    Lp.coeFn_smul (Complex.exp (-(((c : ℝ) : ℂ) *
      ((xiGammaEulerPrimitiveLogFrequency pe : ℂ) + I * (κ : ℂ)))))
      (routePPrimitiveBurnolWindowFeatureLp pe κ), hcoe,
    ae_restrict_mem measurableSet_Ioi] with t e1 e2 e3 e4 ht
  simp only [Function.comp_apply] at e2
  rw [e1, e3, Pi.smul_apply, e2, e4, smul_eq_mul]
  have := routePBurnolForwardDampingShift_primitiveFeature (c := (c : ℝ)) c.coe_nonneg ht pe κ
  rw [routePBurnolForwardDampingShift] at this
  exact this

/-- **(BGAF.8)** on the zero-clock columns of `A_base`: `S_c f_pe = e^{-cλ_pe} f_pe`. -/
theorem burnolWeightedShift_baseField (c : ℝ≥0) (pe : RoutePPrimitiveIndex) :
    burnolWeightedShift c (routePPrimitiveBurnolBaseField pe) =
      ((Real.exp (-((c : ℝ) * xiGammaEulerPrimitiveLogFrequency pe)) : ℝ) : ℂ) •
        routePPrimitiveBurnolBaseField pe := by
  rw [routePPrimitiveBurnolBaseField, burnolWeightedShift_windowFeatureLp]
  congr 1
  push_cast
  ring_nf

/-! ## Hilbert–Schmidt extinction of the damped synthesis -/

/-- A bounded operator after Bochner synthesis is the synthesis of the transformed field. -/
theorem comp_l2Synthesis {X : Type*} [MeasurableSpace X] {μ : Measure X} {H G : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (L : H →L[ℂ] G) (u : Lp H 2 μ) : L ∘L l2Synthesis μ u = l2Synthesis μ (L.compLp u) := by
  ext f
  rw [comp_apply, l2Synthesis_apply, l2Synthesis_apply]
  have hint : Integrable (fun x => f x • u x) μ :=
    memLp_one_iff_integrable.mp ((Lp.memLp u).smul (Lp.memLp f))
  rw [← L.integral_comp_comm hint]
  refine integral_congr_ae ?_
  filter_upwards [L.coeFn_compLp u] with x hx
  rw [hx, map_smul]

/-- **(BGAF.9)** `‖S_c A_base‖²_HS = ∑ e^{-2cλ_pe} w_pe`. -/
theorem hsNormSq_burnolDampedBase (c : ℝ≥0) :
    hsNormSq (burnolWeightedShift c ∘L routePPrimitiveBurnolBaseSynthesis) =
      ∑' pe : RoutePPrimitiveIndex,
        Real.exp (-(2 * (c : ℝ) * xiGammaEulerPrimitiveLogFrequency pe)) *
          routePPrimitiveBaseCauchyCubicWeight pe := by
  rw [routePPrimitiveBurnolBaseSynthesis, comp_l2Synthesis, hsNormSq_l2Synthesis_eq_norm_sq,
    HTGeometry.norm_l2_sq_eq_integral_norm_sq]
  have hpt : ∀ pe : RoutePPrimitiveIndex,
      ‖burnolWeightedShift c (routePPrimitiveBurnolBaseField pe)‖ ^ 2 =
        Real.exp (-(2 * (c : ℝ) * xiGammaEulerPrimitiveLogFrequency pe)) *
          routePPrimitiveBaseCauchyCubicWeight pe := by
    intro pe
    rw [burnolWeightedShift_baseField, norm_smul, Complex.norm_real, Real.norm_of_nonneg
      (Real.exp_pos _).le, mul_pow, norm_sq_routePPrimitiveBurnolBaseField, ← Real.exp_nat_mul]
    congr 2
    push_cast
    ring
  have hint : Integrable (fun pe : RoutePPrimitiveIndex =>
      ‖burnolWeightedShift c (routePPrimitiveBurnolBaseField pe)‖ ^ 2) Measure.count := by
    refine integrable_norm_sq_routePPrimitiveBurnolBaseField.mono' (by fun_prop)
      (Eventually.of_forall fun pe => ?_)
    rw [Real.norm_of_nonneg (sq_nonneg _), hpt, ← norm_sq_routePPrimitiveBurnolBaseField pe]
    have h1 : Real.exp (-(2 * (c : ℝ) * xiGammaEulerPrimitiveLogFrequency pe)) ≤ 1 := by
      rw [Real.exp_le_one_iff, neg_nonpos]
      have := xiGammaEulerPrimitiveLogFrequency_pos pe
      positivity
    exact mul_le_of_le_one_left (sq_nonneg _) h1
  calc ∫ pe, ‖((burnolWeightedShift c).compLp routePPrimitiveBurnolBaseFieldLp) pe‖ ^ 2
        ∂Measure.count
      = ∫ pe, ‖burnolWeightedShift c (routePPrimitiveBurnolBaseField pe)‖ ^ 2 ∂Measure.count := by
        apply integral_congr_ae
        filter_upwards [(burnolWeightedShift c).coeFn_compLp routePPrimitiveBurnolBaseFieldLp,
          memLp_two_routePPrimitiveBurnolBaseField.coeFn_toLp] with pe h1 h2
        rw [h1]
        exact congrArg (fun z => ‖burnolWeightedShift c z‖ ^ 2) h2
    _ = ∑' pe, ‖burnolWeightedShift c (routePPrimitiveBurnolBaseField pe)‖ ^ 2 := by
        rw [integral_countable hint]
        simp
    _ = _ := tsum_congr hpt

/-- **(BGAF.9)** `‖S_c A_base‖²_HS → 0` as `c → ∞`: dominated convergence, every `λ_pe > 0`. -/
theorem tendsto_hsNormSq_burnolDampedBase :
    Tendsto (fun c : ℝ≥0 => hsNormSq (burnolWeightedShift c ∘L routePPrimitiveBurnolBaseSynthesis))
      atTop (𝓝 0) := by
  simp_rw [hsNormSq_burnolDampedBase]
  have hw : ∀ pe, 0 ≤ routePPrimitiveBaseCauchyCubicWeight pe := fun pe => by
    rw [← norm_sq_routePPrimitiveBurnolBaseField pe]
    positivity
  rw [show (0 : ℝ) = ∑' pe : RoutePPrimitiveIndex, (0 : ℝ) from tsum_zero.symm]
  refine tendsto_tsum_of_dominated_convergence summable_routePPrimitiveBaseCauchyCubicWeight
    (fun pe => ?_) (Eventually.of_forall fun c pe => ?_)
  · have hlam := xiGammaEulerPrimitiveLogFrequency_pos pe
    have h1 : Tendsto (fun c : ℝ≥0 => -(2 * (c : ℝ) * xiGammaEulerPrimitiveLogFrequency pe))
        atTop atBot := by
      have hc : Tendsto (fun c : ℝ≥0 => (c : ℝ)) atTop atTop := NNReal.tendsto_coe_atTop.2 tendsto_id
      have h2 : Tendsto (fun c : ℝ≥0 => 2 * (c : ℝ) * xiGammaEulerPrimitiveLogFrequency pe) atTop atTop := by
        have := (hc.const_mul_atTop (by norm_num : (0 : ℝ) < 2)).atTop_mul_const hlam
        simpa [mul_assoc] using this
      exact tendsto_neg_atTop_atBot.comp h2
    have h3 := (Real.tendsto_exp_atBot.comp h1).mul_const (routePPrimitiveBaseCauchyCubicWeight pe)
    simpa using h3
  · rw [Real.norm_of_nonneg (mul_nonneg (Real.exp_pos _).le (hw pe))]
    have h1 : Real.exp (-(2 * (c : ℝ) * xiGammaEulerPrimitiveLogFrequency pe)) ≤ 1 := by
      rw [Real.exp_le_one_iff, neg_nonpos]
      have := xiGammaEulerPrimitiveLogFrequency_pos pe
      positivity
    exact mul_le_of_le_one_left (hw pe) h1

/-! ## The filtration -/

/-- `E_base(c)`: the determinant-line area of the cap of `S_c A_base`. -/
abbrev burnolGraphAction : ℝ≥0 → ℝ :=
  graphAction routePPrimitiveBurnolBaseSynthesis_isHilbertSchmidt burnolWeightedShift

/-- **(BGAF.10)** The Burnol action filtration: `E_base` is nonnegative and antitone, tends to zero,
starts at the cap area `E_base(0) < 1`, and the interval actions are nonnegative, additive, and have
total mass `E_base(0) < 1`. -/
theorem burnolGraphAction_filtration :
    Antitone burnolGraphAction ∧ (∀ c, 0 ≤ burnolGraphAction c) ∧
      Tendsto burnolGraphAction atTop (𝓝 0) ∧ burnolGraphAction 0 = burnolBaseCapArea ∧
      burnolBaseCapArea < 1 ∧
      (∀ c d : ℝ≥0, c ≤ d → 0 ≤ intervalAction routePPrimitiveBurnolBaseSynthesis_isHilbertSchmidt
        burnolWeightedShift c d) ∧
      Tendsto (fun d => intervalAction routePPrimitiveBurnolBaseSynthesis_isHilbertSchmidt
        burnolWeightedShift 0 d) atTop (𝓝 burnolBaseCapArea) := by
  have hsemi := burnolWeightedShift_add
  have hcon := norm_burnolWeightedShift_le
  have htot := tendsto_intervalAction_total routePPrimitiveBurnolBaseSynthesis_isHilbertSchmidt
    burnolWeightedShift tendsto_hsNormSq_burnolDampedBase burnolWeightedShift_zero
  have h0 : burnolGraphAction 0 = burnolBaseCapArea := by
    have hc1 : burnolWeightedShift 0 ∘L routePPrimitiveBurnolBaseSynthesis =
        routePPrimitiveBurnolBaseSynthesis := by
      rw [burnolWeightedShift_zero]
      ext x
      simp
    exact graphCapArea_congr hc1 _ _
  obtain ⟨-, -, -, hlt, hb⟩ := burnolBaseCapArea_lt_one
  exact ⟨graphAction_antitone _ _ hsemi hcon,
    fun c => (graphAction_spec routePPrimitiveBurnolBaseSynthesis_isHilbertSchmidt _ c).2.1,
    tendsto_graphAction _ _ tendsto_hsNormSq_burnolDampedBase, h0, hlt.trans hb,
    fun c d hcd => intervalAction_nonneg _ _ hsemi hcon hcd, htot.1⟩

/-! ## The packet Gram loss -/

/-- The transported channel of the corpus colligation is the damping semigroup. -/
theorem colligationVector_zero (c : ℝ≥0) (pe : Nat.Primes × ℕ) (κ : ℝ) :
    routePPrimitiveBurnolApertureColligationVector c c.coe_nonneg pe κ 0 =
      burnolWeightedShift c (routePPrimitiveBurnolWindowFeatureLp pe κ) := by
  have hmem := memLp_routePBurnolHalfLine (continuous_routePPrimitiveBurnolWindowFeature pe κ)
    (integrableOn_norm_sq_routePPrimitiveBurnolWindowFeature pe κ)
  have hcoe : (routePPrimitiveBurnolWindowFeatureLp pe κ : ℝ → ℂ) =ᵐ[volume.restrict (Ioi 0)]
      routePPrimitiveBurnolWindowFeature pe κ := hmem.coeFn_toLp
  have hch : routePPrimitiveBurnolApertureColligationVector c c.coe_nonneg pe κ 0 =
      (memLp_routePBurnolForwardDampingShift c.coe_nonneg
        (continuous_routePPrimitiveBurnolWindowFeature pe κ)
        (integrableOn_norm_sq_routePPrimitiveBurnolWindowFeature pe κ)).toLp
        (routePBurnolForwardDampingShift c (routePPrimitiveBurnolWindowFeature pe κ)) := rfl
  rw [hch]
  refine Lp.ext ?_
  have h2 := (quasiMeasurePreserving_add_right_Ioi c.coe_nonneg).ae_eq_comp hcoe
  filter_upwards [MemLp.coeFn_toLp (memLp_routePBurnolForwardDampingShift c.coe_nonneg
      (continuous_routePPrimitiveBurnolWindowFeature pe κ)
      (integrableOn_norm_sq_routePPrimitiveBurnolWindowFeature pe κ)),
    burnolWeightedShift_coeFn c (routePPrimitiveBurnolWindowFeatureLp pe κ), h2] with t e1 e2 e3
  simp only [Function.comp_apply] at e3
  rw [e1, e2, e3]
  rfl

/-- The damping eigenvalue of a packet member. -/
def packetDamping {N : ℕ} (c : ℝ≥0) (pe : Fin N → Nat.Primes × ℕ) (κ : Fin N → ℝ) (i : Fin N) : ℂ :=
  Complex.exp (-(((c : ℝ) : ℂ) * ((xiGammaEulerPrimitiveLogFrequency (pe i) : ℂ) + I * (κ i : ℂ))))

/-- **(BGAF.11) The packet Gram loss.**  For every finite packet and damping times `c ≤ h + c`, the
loss `Gram(S_c f) - Gram(S_{h+c} f)` is the damped conjugate `D* (B_h + T_h) D` of the hard-boundary
and tail-cocycle defect Grams at step `h`, all off-diagonal prime/depth/clock entries included. -/
theorem dampedPacketGram_sub {N : ℕ} (c h : ℝ≥0) (pe : Fin N → Nat.Primes × ℕ) (κ : Fin N → ℝ) :
    Matrix.gram ℂ (fun i => burnolWeightedShift c (routePPrimitiveBurnolWindowFeatureLp (pe i) (κ i))) -
        Matrix.gram ℂ (fun i =>
          burnolWeightedShift (h + c) (routePPrimitiveBurnolWindowFeatureLp (pe i) (κ i))) =
      (Matrix.diagonal (packetDamping c pe κ)).conjTranspose *
        (routePPrimitiveBurnolApertureChannelGramMatrix h h.coe_nonneg 1 pe κ +
          routePPrimitiveBurnolApertureChannelGramMatrix h h.coe_nonneg 2 pe κ) *
        Matrix.diagonal (packetDamping c pe κ) := by
  have hsum := routePPrimitiveBurnolWindowGramMatrix_eq_sum_channelGrams (h : ℝ) h.coe_nonneg pe κ
  rw [routePPrimitiveBurnolWindowGramMatrix_eq_gram_L2] at hsum
  have hdef : Matrix.gram ℂ (fun i => routePPrimitiveBurnolWindowFeatureLp (pe i) (κ i)) -
      routePPrimitiveBurnolApertureChannelGramMatrix h h.coe_nonneg 0 pe κ =
      routePPrimitiveBurnolApertureChannelGramMatrix h h.coe_nonneg 1 pe κ +
        routePPrimitiveBurnolApertureChannelGramMatrix h h.coe_nonneg 2 pe κ := by
    rw [hsum]
    abel
  rw [← hdef]
  ext i j
  rw [Matrix.mul_diagonal, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul]
  simp only [Matrix.sub_apply, Matrix.gram_apply,
    routePPrimitiveBurnolApertureChannelGramMatrix, colligationVector_zero, Pi.star_apply]
  rw [burnolWeightedShift_add, comp_apply, comp_apply, burnolWeightedShift_windowFeatureLp,
    burnolWeightedShift_windowFeatureLp, map_smul, map_smul]
  simp only [inner_smul_left, inner_smul_right, packetDamping, RCLike.star_def]
  ring

end

end RHTower
