import GaloisForLFunctions.BlackHoleRingdown.TheCosineFamilyOfTheHorizon

/-!
# General data on the modular horizon

Every `f ∈ L²(PSL₂(ℤ)\ℍ)` is `f = m 𝟙 + f_E + f_c`, with `f_E` in the closure of the fields of compact pulses and `f_c` cuspidal,
the three parts mutually orthogonal. The proof takes the corpus decomposition of `L²` into the Eisenstein space and the
cuspidal space, and reduces the generators of the Eisenstein space to pulses: a smooth height profile `ψ` is the profile at
time `0` of the pulse `e^{-S/2} ψ(e^S)`, smooth profiles are dense, and the incomplete Eisenstein series depends continuously on
its profile.

The wave evolution of general data is
`U(τ) f = m cosh(τ/2) 𝟙 + C_E(τ) f_E + C_c(τ) f_c`,
and it is contractive on the orthogonal complement of the constants.
-/

open Complex MeasureTheory Set Filter Topology ModularGroup EisensteinSeries
open scoped ContDiff InnerProductSpace ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.BlackHoleRingdown

open GaloisForLFunctions.RHTower.DeckPointPair GaloisForLFunctions.HTGeometry
  GaloisForLFunctions.RHTower.MaassFiniteDeckDirichlet GaloisForLFunctions.RHTower.MaassCongruenceL2
  GaloisForLFunctions.RHTower.SelbergMaassCongruenceTrace

/-! ### Smooth profiles -/

/-- Smooth approximation of a height profile. -/
theorem exists_smooth_approx (ψ : HeightProfile) {ε : ℝ} (hε : 0 < ε) :
    ∃ ψ' : HeightProfile, ContDiff ℝ ∞ ψ'.toFun ∧ ψ.lower / 2 ≤ ψ'.lower ∧
      ψ'.upper ≤ ψ.upper + 1 ∧ ∀ y, ‖ψ'.toFun y - ψ.toFun y‖ ≤ ε := by
  have hcs : HasCompactSupport ψ.toFun :=
    HasCompactSupport.intro isCompact_Icc fun y hy => ψ.eq_zero_of_not_mem_Icc hy
  obtain ⟨δ, hδ, hδε⟩ := Metric.uniformContinuous_iff.1
    (hcs.uniformContinuous_of_continuous ψ.continuous) ε hε
  set r : ℝ := min δ (min (ψ.lower / 2) 1)
  have hr : 0 < r := lt_min hδ (lt_min (half_pos ψ.lower_pos) one_pos)
  let φ : ContDiffBump (0 : ℝ) := ⟨r / 2, r, half_pos hr, half_lt_self hr⟩
  set f : ℝ → ℂ := convolution (φ.normed volume) ψ.toFun (ContinuousLinearMap.lsmul ℝ ℝ) volume
  have hf : ContDiff ℝ ∞ f := by
    have h := (φ.hasCompactSupport_normed (μ := volume)).contDiff_convolution_left
      (ContinuousLinearMap.lsmul ℝ ℝ) (φ.contDiff_normed (n := ⊤)) (μ := volume)
      ψ.continuous.locallyIntegrable
    exact h
  have hsupp : ∀ y, f y ≠ 0 → ψ.lower - r < y ∧ y < ψ.upper + r := fun y hy => by
    have h := support_convolution_subset (ContinuousLinearMap.lsmul ℝ ℝ) (μ := volume)
      (f := φ.normed volume) (g := ψ.toFun) hy
    rw [φ.support_normed_eq] at h
    obtain ⟨u, hu, t, ht, rfl⟩ := h
    have hu' : |u| < r := by simpa using hu
    have ht' : t ∈ Icc ψ.lower ψ.upper := by
      by_contra h'
      exact ht (ψ.eq_zero_of_not_mem_Icc h')
    constructor <;> linarith [abs_lt.1 hu', ht'.1, ht'.2]
  have hr2 : r ≤ ψ.lower / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hr1 : r ≤ 1 := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨⟨f, ψ.lower - r, ψ.upper + r, by linarith [ψ.lower_pos], by linarith [ψ.lower_le_upper],
    hf.continuous, fun y hy => ?_, fun y hy => ?_⟩, hf, by simp; linarith, by simp; linarith,
    fun y => ?_⟩
  · by_contra h; linarith [(hsupp y h).1]
  · by_contra h; linarith [(hsupp y h).2]
  · rw [← dist_eq_norm]
    refine φ.dist_normed_convolution_le ψ.continuous.aestronglyMeasurable fun x hx => ?_
    exact (hδε (lt_of_lt_of_le (Metric.mem_ball.1 hx) (min_le_left _ _))).le

/-- The pulse of a smooth height profile. -/
def pulseOfProfile (ψ : HeightProfile) (hψ : ContDiff ℝ ∞ ψ.toFun) : CompactPulse where
  toFun S := Complex.exp (-(1 / 2 : ℂ) * (S : ℂ)) * ψ.toFun (Real.exp S)
  smooth := ((contDiff_const.mul Complex.ofRealCLM.contDiff).cexp).mul (hψ.comp Real.contDiff_exp)
  compact := by
    refine HasCompactSupport.intro (isCompact_Icc (a := Real.log ψ.lower) (b := Real.log ψ.upper))
      fun S hS => ?_
    have hne : Real.exp S ∉ Icc ψ.lower ψ.upper := fun h => hS
      ⟨(Real.log_le_iff_le_exp ψ.lower_pos).mpr h.1,
        (Real.le_log_iff_exp_le (ψ.lower_pos.trans_le ψ.lower_le_upper)).mpr h.2⟩
    rw [ψ.eq_zero_of_not_mem_Icc hne, mul_zero]

theorem pulseF_pulseOfProfile (ψ : HeightProfile) (hψ : ContDiff ℝ ∞ ψ.toFun) (y : ℝ) :
    pulseF (pulseOfProfile ψ hψ) 0 y = ψ.toFun y := by
  by_cases hy : 0 < y
  · have hE : Real.exp (0 + Real.log y) = y := by rw [zero_add, Real.exp_log hy]
    change ((Real.sqrt y : ℝ) : ℂ) * (Complex.exp (-(1 / 2 : ℂ) * ((0 + Real.log y : ℝ) : ℂ)) *
      ψ.toFun (Real.exp (0 + Real.log y))) = _
    rw [hE]
    have hexp : Complex.exp (-(1 / 2 : ℂ) * ((0 + Real.log y : ℝ) : ℂ)) = (((Real.sqrt y)⁻¹ : ℝ) : ℂ) := by
      have h2 : (Real.sqrt y)⁻¹ = Real.exp (-(1 / 2) * Real.log y) := by
        rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hy, ← Real.exp_neg]
        congr 1
        ring
      rw [h2, Complex.ofReal_exp]
      congr 1
      push_cast
      ring
    rw [hexp, ← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ (Real.sqrt_pos.mpr hy).ne']
    simp
  · have hlow : y < ψ.lower := lt_of_le_of_lt (not_lt.mp hy) ψ.lower_pos
    rw [ψ.eq_zero_of_lt y hlow, pulseF, Real.sqrt_eq_zero_of_nonpos (not_lt.mp hy)]
    simp

/-! ### The projection off the constants -/

/-- The squared norm of the constant. -/
def onesNorm : ℝ := ‖onesL2 0‖ ^ 2

theorem onesNorm_pos : 0 < onesNorm := by
  have h1 := inner_onesL2_self 0
  have hV : ⟪onesVec 0, onesVec 0⟫_ℂ ≠ 0 := by
    rw [Ne, inner_self_eq_zero]
    exact onesVec_ne_zero 0
  have hne : ⟪onesL2 0, onesL2 0⟫_ℂ ≠ 0 := by
    rw [h1]
    refine mul_ne_zero ?_ hV
    exact_mod_cast (by positivity : Real.pi / 3 ≠ 0)
  have h0 : onesL2 0 ≠ 0 := fun h => hne (by rw [h]; simp)
  have : 0 < ‖onesL2 0‖ := norm_pos_iff.mpr h0
  rw [onesNorm]
  positivity

/-- The projection off the constants. -/
def offMean : DeckL2 0 →L[ℂ] DeckL2 0 :=
  ContinuousLinearMap.id ℂ (DeckL2 0) -
    (innerSL ℂ (onesL2 0)).smulRight (((onesNorm : ℝ) : ℂ)⁻¹ • onesL2 0)

theorem offMean_apply (x : DeckL2 0) :
    offMean x = x - ⟪onesL2 0, x⟫_ℂ • (((onesNorm : ℝ) : ℂ)⁻¹ • onesL2 0) := rfl

theorem offMean_ones : offMean (onesL2 0) = 0 := by
  have hne : ((onesNorm : ℝ) : ℂ) ≠ 0 := by exact_mod_cast onesNorm_pos.ne'
  have hin : ⟪onesL2 0, onesL2 0⟫_ℂ = ((onesNorm : ℝ) : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K, onesNorm]
    push_cast
    rfl
  rw [offMean_apply, hin, smul_smul, mul_inv_cancel₀ hne, one_smul, sub_self]

theorem inner_ones_pulseL2 (h : CompactPulse) (τ : ℝ) : ⟪onesL2 0, pulseL2 h τ 0⟫_ℂ = 0 := by
  rw [← inner_conj_symm, inner_pulseL2_ones, map_zero]

theorem offMean_pulseL2 (h : CompactPulse) (τ : ℝ) : offMean (pulseL2 h τ 0) = pulseL2 h τ 0 := by
  rw [offMean_apply, inner_ones_pulseL2, zero_smul, sub_zero]

/-- An incomplete Eisenstein series with the constant vector is a field plus a constant. -/
theorem incEisL2_eq_pulse (ψ : HeightProfile) (hψ : ContDiff ℝ ∞ ψ.toFun) :
    incEisL2 ψ (onesVec 0) = pulseL2 (pulseOfProfile ψ hψ) 0 0 +
      (2 * meanCoefficient (pulseOfProfile ψ hψ) * Complex.exp (((0 : ℝ) : ℂ) / 2)) • onesL2 0 := by
  rw [pulseL2, sub_add_cancel]
  refine toDeckL2_congr _ _ (Eventually.of_forall fun z => ?_)
  change incEis ψ.toFun _ z = incEis (pulseF (pulseOfProfile ψ hψ) 0) _ z
  congr 1
  funext y
  exact (pulseF_pulseOfProfile ψ hψ y).symm

/-- **The generators reduce to the channel.** -/
theorem offMean_incEisL2_mem (ψ : HeightProfile) :
    offMean (incEisL2 ψ (onesVec 0)) ∈ horizonChannel := by
  have hclosed : IsClosed {x : DeckL2 0 | offMean x ∈ horizonChannel} :=
    isClosed_horizonChannel.preimage offMean.continuous
  have hmem : incEisL2 ψ (onesVec 0) ∈ closure {x : DeckL2 0 | offMean x ∈ horizonChannel} := by
    obtain ⟨C, hC, hL⟩ := exists_norm_incEisL2_sub_le (N := 0) (a := ψ.lower / 2) (b := ψ.upper + 1)
      (half_pos ψ.lower_pos)
    refine Metric.mem_closure_iff.mpr fun ε hε => ?_
    set δ : ℝ := ε / (2 * ((C + 1) * (‖onesVec 0‖ + 1))) with hδ
    have hδ0 : 0 < δ := by positivity
    obtain ⟨ψ', hs, hl, hu, happ⟩ := exists_smooth_approx ψ hδ0
    refine ⟨incEisL2 ψ' (onesVec 0), ?_, ?_⟩
    · change offMean (incEisL2 ψ' (onesVec 0)) ∈ horizonChannel
      rw [incEisL2_eq_pulse ψ' hs, map_add, map_smul, offMean_ones, smul_zero, add_zero, offMean_pulseL2]
      have h1 := fieldAt_mem 0 (ofPulse (pulseOfProfile ψ' hs))
      exact h1
    · rw [dist_eq_norm]
      have hb := hL ψ ψ' (by linarith [ψ.lower_pos]) (by linarith) hl hu δ hδ0.le
        (fun y => by rw [norm_sub_rev]; exact happ y) (onesVec 0)
      refine hb.trans_lt ?_
      have hn := norm_nonneg (onesVec 0)
      have hp : 0 < (C + 1) * (‖onesVec 0‖ + 1) := by positivity
      have h3 : C * (δ * ‖onesVec 0‖) ≤ (C + 1) * (‖onesVec 0‖ + 1) * δ := by
        have : C * ‖onesVec 0‖ ≤ (C + 1) * (‖onesVec 0‖ + 1) := by nlinarith
        calc C * (δ * ‖onesVec 0‖) = (C * ‖onesVec 0‖) * δ := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_right this hδ0.le
      have h4 : (C + 1) * (‖onesVec 0‖ + 1) * δ = ε / 2 := by
        rw [hδ]
        field_simp
      linarith
  have := closure_minimal (subset_refl _) hclosed hmem
  exact this

/-- Every vector of the level-one deck space is a multiple of the constant vector. -/
theorem eq_smul_onesVec (v : DeckSpace 0) : ∃ c : ℂ, v = c • onesVec 0 := by
  refine ⟨v (QuotientGroup.mk 1), ?_⟩
  ext q
  rw [Subsingleton.elim q (QuotientGroup.mk 1)]
  simp [onesVec_apply]

theorem incEisL2_smul_ones (ψ : HeightProfile) (c : ℂ) :
    incEisL2 ψ (c • onesVec 0) = c • incEisL2 ψ (onesVec 0) := by
  apply Lp.ext
  filter_upwards [incEisL2_coeFn ψ (c • onesVec 0), Lp.coeFn_smul c (incEisL2 ψ (onesVec 0)),
    incEisL2_coeFn ψ (onesVec 0)] with z a1 a2 a3
  rw [a1, a2, Pi.smul_apply, a3]
  have h := incEis_add_smul ψ c 0 (onesVec 0) 0 z
  simpa using h

/-- **The Eisenstein space is the constants plus the channel.** -/
theorem offMean_mem_of_eisSpace {x : DeckL2 0} (hx : x ∈ eisSpace 0) : offMean x ∈ horizonChannel := by
  have hspan : Submodule.span ℂ (eisGen 0) ≤ horizonChannel.comap offMean.toLinearMap := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨ψ, -, v, -, rfl⟩
    obtain ⟨c, rfl⟩ := eq_smul_onesVec v
    change offMean (incEisL2 ψ (c • onesVec 0)) ∈ horizonChannel
    rw [incEisL2_smul_ones, map_smul]
    exact horizonChannel.smul_mem _ (offMean_incEisL2_mem ψ)
  have hclosed : IsClosed ((horizonChannel.comap offMean.toLinearMap : Submodule ℂ (DeckL2 0)) : Set (DeckL2 0)) :=
    isClosed_horizonChannel.preimage offMean.continuous
  exact Submodule.topologicalClosure_minimal _ hspan hclosed hx

theorem mem_deckCentralFixedL2_zero (f : DeckL2 0) : f ∈ deckCentralFixedL2 0 := by
  rw [deckCentralFixedL2, LinearMap.mem_ker]
  have hc : ∀ v : DeckSpace 0, deckCentralCoeff 0 v = v := fun v => by
    ext q
    change finiteRegularUnitary _ v q = v q
    rw [finiteRegularUnitary_apply, Subsingleton.elim (q * _) q]
  have h1 : deckCentralL2 0 f = f := by
    apply Lp.ext
    filter_upwards [ContinuousLinearMap.coeFn_compLpL (deckCentralCoeff 0) f] with z hz
    rw [deckCentralL2, hz]
    exact hc _
  change deckCentralL2 0 f - f = 0
  rw [h1, sub_self]

/-- The channel lies in the Eisenstein space. -/
theorem horizonChannel_le_eisSpace : horizonChannel ≤ eisSpace 0 := by
  refine Submodule.topologicalClosure_minimal _ ?_ isClosed_eisSpace
  rintro _ ⟨f, rfl⟩
  change incEisL2 _ _ - _ • _ ∈ eisSpace 0
  exact (eisSpace 0).sub_mem (incEisL2_mem_eisSpace _ (deckRho_onesVec _))
    ((eisSpace 0).smul_mem _ onesL2_mem_eisSpace)

theorem inner_channel_cusp {x c : DeckL2 0} (hx : x ∈ horizonChannel) (hc : c ∈ cuspidalL2Closure 0) :
    ⟪x, c⟫_ℂ = 0 :=
  ((mem_cuspidalL2Closure_iff_eisSpace c).mp hc).2 x (horizonChannel_le_eisSpace hx)

theorem inner_channel_ones {x : DeckL2 0} (hx : x ∈ horizonChannel) : ⟪x, onesL2 0⟫_ℂ = 0 := by
  refine horizonChannel_induction (P := fun x => ⟪x, onesL2 0⟫_ℂ = 0)
    (isClosed_eq (continuous_id.inner continuous_const) continuous_const) (fun f => ?_) hx
  exact inner_pulseL2_ones (toPulse f) 0 0

/-- **General horizon data.**  Every `f ∈ L²` is a constant plus an element of the channel plus a cuspidal part. -/
theorem exists_horizon_decomposition (f : DeckL2 0) :
    ∃ (m : ℂ) (fE fc : DeckL2 0), f = m • onesL2 0 + fE + fc ∧ fE ∈ horizonChannel ∧
      fc ∈ cuspidalL2Closure 0 := by
  set P := (eisSpace 0).starProjection f with hP
  have hPm : P ∈ eisSpace 0 := (eisSpace 0).starProjection_apply_mem _
  have hc : f - P ∈ cuspidalL2Closure 0 := by
    rw [mem_cuspidalL2Closure_iff_eisSpace]
    refine ⟨mem_deckCentralFixedL2_zero _, fun g hg => ?_⟩
    exact ((eisSpace 0).mem_orthogonal _).1 ((eisSpace 0).sub_starProjection_mem_orthogonal _) g hg
  refine ⟨⟪onesL2 0, P⟫_ℂ * ((onesNorm : ℝ) : ℂ)⁻¹, offMean P, f - P, ?_, offMean_mem_of_eisSpace hPm, hc⟩
  rw [offMean_apply, smul_smul]
  abel

/-! ### The evolution -/

/-- **The wave evolution of general horizon data.** -/
def horizonWave (τ : ℝ) (m : ℂ) (fE : DeckL2 0) (fc : CuspidalL2 0) : DeckL2 0 :=
  ((Real.cosh (τ / 2) : ℂ) * m) • onesL2 0 + channelCos τ fE + (cuspCosine τ fc : DeckL2 0)

theorem horizonWave_zero (m : ℂ) {fE : DeckL2 0} (hE : fE ∈ horizonChannel) (fc : CuspidalL2 0) :
    horizonWave 0 m fE fc = m • onesL2 0 + fE + (fc : DeckL2 0) := by
  rw [horizonWave, channelCos_zero hE, cuspCosine_zero]
  simp

/-- **Contractivity on the orthogonal complement of the constants.** -/
theorem norm_channel_add_cusp_le (τ : ℝ) {fE : DeckL2 0} (hE : fE ∈ horizonChannel) (fc : CuspidalL2 0) :
    ‖channelCos τ fE + (cuspCosine τ fc : DeckL2 0)‖ ≤ ‖fE + (fc : DeckL2 0)‖ := by
  have hE' := channelCos_mem τ hE
  have h1 := @norm_add_sq ℂ _ _ _ _ (channelCos τ fE) (cuspCosine τ fc : DeckL2 0)
  have h2 := @norm_add_sq ℂ _ _ _ _ fE (fc : DeckL2 0)
  rw [inner_channel_cusp hE' (cuspCosine τ fc).2] at h1
  rw [inner_channel_cusp hE fc.2] at h2
  have hb1 := pow_le_pow_left₀ (norm_nonneg _) (norm_channelCos_le τ fE) 2
  have hb2 : ‖((cuspCosine τ fc : CuspidalL2 0) : DeckL2 0)‖ ^ 2 ≤ ‖(fc : DeckL2 0)‖ ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) (norm_cuspCosine_le τ fc) 2
  have hsq : ‖channelCos τ fE + (cuspCosine τ fc : DeckL2 0)‖ ^ 2 ≤ ‖fE + (fc : DeckL2 0)‖ ^ 2 := by
    rw [h1, h2]
    simp only [map_zero, mul_zero, add_zero]
    linarith
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp hsq

end GaloisForLFunctions.BlackHoleRingdown

end
