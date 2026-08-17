import GaloisForLFunctions.RHTower.ProlateSmallApertureDeflatedSpectrum

/-!
# Moment deflation as finite-rank spectral factorization

The all-rung residual blocks are connected here to the undeflated Fourier
operator.  The zeroth residual is the identity, the `k`th residual synthesis is
exactly postcomposition of the full synthesis by orthogonal moment deflation,
and the complementary low-moment synthesis has rectangular rank at most `k`.
Thus the `k`th approximation number of the full block is bounded by the norm of
its `k`th residual.

Combining this exact finite-rank factorization with the rank-one limit proves
that every deflated norm has sharp positive order `|c|^k`, and gives the first
all-rung small-aperture upper bound for approximation numbers of the undeflated
operator.  Matching lower bounds—and the parity-reduced identification with
ordered even Slepian branches—remain the hierarchical min--max frontier.
-/

open MeasureTheory Filter Topology Set Complex

noncomputable section

namespace RHTower

open GaloisForLFunctions.HTGeometry

attribute [local instance] Measure.Subtype.measureSpace

theorem apertureMomentSpan_zero : apertureMomentSpan 0 = ⊥ := by
  rw [apertureMomentSpan]
  simp

theorem apertureMomentResidual_zero :
    apertureMomentResidual 0 = ContinuousLinearMap.id ℂ UnitApertureL2 := by
  apply ContinuousLinearMap.ext
  intro f
  rw [apertureMomentResidual_apply]
  have hproj : (apertureMomentSpan 0).starProjection f = 0 := by
    apply (Submodule.mem_bot ℂ).mp
    rw [← apertureMomentSpan_zero]
    exact Submodule.starProjection_apply_mem _ _
  rw [hproj]
  simp

theorem apertureMomentFourierField_zero_apply (c : ℝ)
    (x : UnitPhysicalInterval) :
    apertureMomentFourierField 0 c x =
      apertureFourierL2 1 (c * (x : ℝ)) := by
  rw [apertureMomentFourierField_apply, apertureMomentResidual_zero]
  rfl

theorem apertureMomentFourierField_eq_residual (k : ℕ) (c : ℝ) :
    apertureMomentFourierField k c =
      (apertureMomentResidual k).compLeftContinuous ℂ UnitPhysicalInterval
        (apertureMomentFourierField 0 c) := by
  apply ContinuousMap.ext
  intro x
  rw [apertureMomentFourierField_apply]
  change apertureMomentResidual k (apertureFourierL2 1 (c * (x : ℝ))) =
    apertureMomentResidual k (apertureMomentFourierField 0 c x)
  rw [apertureMomentFourierField_zero_apply]

theorem apertureMomentFourierSynthesis_eq_residual_comp
    (k : ℕ) (c : ℝ) :
    apertureMomentFourierSynthesis k c =
      apertureMomentResidual k ∘L apertureMomentFourierSynthesis 0 c := by
  apply ContinuousLinearMap.ext
  intro f
  rw [apertureMomentFourierSynthesis, apertureMomentSynthesisMap_apply,
    apertureMomentFourierSynthesis, apertureMomentSynthesisMap_apply,
    l2Synthesis_apply, ContinuousLinearMap.comp_apply, l2Synthesis_apply]
  have hk : (apertureMomentFourierFieldL2 k c :
      UnitPhysicalInterval → UnitApertureL2) =ᵐ[volume]
      fun x => apertureMomentFourierField k c x := by
    exact ContinuousMap.coeFn_toLp
      (𝕜 := ℂ) (p := (2 : ENNReal))
      (μ := (volume : Measure UnitPhysicalInterval))
      (apertureMomentFourierField k c)
  have h0 : (apertureMomentFourierFieldL2 0 c :
      UnitPhysicalInterval → UnitApertureL2) =ᵐ[volume]
      fun x => apertureMomentFourierField 0 c x := by
    exact ContinuousMap.coeFn_toLp
      (𝕜 := ℂ) (p := (2 : ENNReal))
      (μ := (volume : Measure UnitPhysicalInterval))
      (apertureMomentFourierField 0 c)
  have hpoint :
      (fun x => f x • apertureMomentFourierFieldL2 k c x) =ᵐ[volume]
      fun x => apertureMomentResidual k
        (f x • apertureMomentFourierFieldL2 0 c x) := by
    filter_upwards [hk, h0] with x hxk hx0
    rw [hxk, hx0, apertureMomentFourierField_eq_residual]
    simp
  have hint : Integrable
      (fun x => f x • apertureMomentFourierFieldL2 0 c x)
      (volume : Measure UnitPhysicalInterval) := by
    exact memLp_one_iff_integrable.mp
      ((Lp.memLp (apertureMomentFourierFieldL2 0 c)).smul (Lp.memLp f))
  exact (integral_congr_ae hpoint).trans
    ((apertureMomentResidual k).integral_comp_comm hint)

/-- Low-moment output retained before the `k`th deflation. -/
noncomputable def apertureMomentProjectionSynthesis (k : ℕ) (c : ℝ) :
    UnitPhysicalScalarL2 →L[ℂ] UnitApertureL2 :=
  (apertureMomentSpan k).starProjection ∘L
    apertureMomentFourierSynthesis 0 c

theorem hasRectRankLE_apertureMomentProjectionSynthesis
    (k : ℕ) (c : ℝ) :
    HasRectRankLE (apertureMomentProjectionSynthesis k c) k := by
  classical
  let v : Fin k → UnitApertureL2 :=
    fun i => apertureComplexMonomialL2 1 (i : ℕ)
  let V : Submodule ℂ UnitApertureL2 := Submodule.span ℂ (Set.range v)
  have hfinite : (Set.range v).Finite := Set.finite_range v
  have hdim : Module.finrank ℂ V ≤ k := by
    change Module.finrank ℂ (Submodule.span ℂ (Set.range v)) ≤ k
    refine (finrank_span_le_card (R := ℂ) (Set.range v)).trans ?_
    rw [Set.toFinset_range]
    exact Finset.card_image_le.trans (by simp)
  refine ⟨V, FiniteDimensional.span_of_finite ℂ hfinite, hdim, ?_⟩
  intro f
  change (apertureMomentSpan k).starProjection
      (apertureMomentFourierSynthesis 0 c f) ∈ V
  change (apertureMomentSpan k).starProjection
      (apertureMomentFourierSynthesis 0 c f) ∈ apertureMomentSpan k
  exact Submodule.starProjection_apply_mem _ _

theorem apertureMomentFourierSynthesis_sub_projection_eq
    (k : ℕ) (c : ℝ) :
    apertureMomentFourierSynthesis 0 c -
      apertureMomentProjectionSynthesis k c =
        apertureMomentFourierSynthesis k c := by
  calc
    apertureMomentFourierSynthesis 0 c -
        apertureMomentProjectionSynthesis k c =
        apertureMomentResidual k ∘L apertureMomentFourierSynthesis 0 c := by
      apply ContinuousLinearMap.ext
      intro f
      rw [sub_apply, apertureMomentProjectionSynthesis,
        ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
        apertureMomentResidual_apply]
    _ = apertureMomentFourierSynthesis k c :=
      (apertureMomentFourierSynthesis_eq_residual_comp k c).symm

/-- The `k`th approximation number of the full Fourier block is controlled by
the norm of its `k`-moment deflation. -/
theorem rectApproxNumber_apertureMomentFourierSynthesis_zero_le_deflated
    (k : ℕ) (c : ℝ) :
    rectApproxNumber (apertureMomentFourierSynthesis 0 c) k ≤
      ‖apertureMomentFourierSynthesis k c‖ := by
  have h := rectApproxNumber_le
    (apertureMomentFourierSynthesis 0 c) k
    (apertureMomentProjectionSynthesis k c)
    (hasRectRankLE_apertureMomentProjectionSynthesis k c)
  rwa [apertureMomentFourierSynthesis_sub_projection_eq] at h

/-- Exact leading order of the norm of every moment-deflated block. -/
theorem tendsto_norm_apertureMomentFourierSynthesis_div_abs_pow
    (k : ℕ) :
    Tendsto (fun c : ℝ =>
      ‖apertureMomentFourierSynthesis k c‖ / |c| ^ k)
      (𝓝[≠] (0 : ℝ))
      (𝓝 ‖apertureMomentLeadingSynthesis k‖) := by
  have h := tendsto_rectApproxNumber_zero_normalizedApertureMomentSynthesis k
  have heq : ∀ᶠ c : ℝ in 𝓝[≠] (0 : ℝ),
      rectApproxNumber (normalizedApertureMomentSynthesis k c) 0 =
        ‖apertureMomentFourierSynthesis k c‖ / |c| ^ k := by
    filter_upwards [self_mem_nhdsWithin] with c hc0
    have hc : c ≠ 0 := by simpa using hc0
    rw [rectApproxNumber_zero_eq_norm, normalizedApertureMomentSynthesis,
      norm_smul, Real.norm_eq_abs, abs_inv, abs_pow]
    rw [inv_mul_eq_div]
  exact h.congr' heq

/-- Quantitative all-rung upper spectral order for the undeflated block: its
`k`th approximation number is eventually at most the sharp deflated leading
constant plus any positive margin, times `|c|^k`. -/
theorem eventually_rectApproxNumber_full_le_leading_mul_abs_pow
    (k : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ c : ℝ in 𝓝[≠] (0 : ℝ),
      rectApproxNumber (apertureMomentFourierSynthesis 0 c) k ≤
        (‖apertureMomentLeadingSynthesis k‖ + ε) * |c| ^ k := by
  have hnorm :=
    (tendsto_norm_apertureMomentFourierSynthesis_div_abs_pow k).eventually_lt_const
      (lt_add_of_pos_right _ hε)
  filter_upwards [hnorm, self_mem_nhdsWithin] with c hcNorm hc0
  have hc : c ≠ 0 := by simpa using hc0
  have hpow : 0 < |c| ^ k := pow_pos (abs_pos.mpr hc) k
  have hscaled : ‖apertureMomentFourierSynthesis k c‖ <
      (‖apertureMomentLeadingSynthesis k‖ + ε) * |c| ^ k := by
    apply (div_lt_iff₀ hpow).mp
    simpa [mul_comm] using hcNorm
  exact (rectApproxNumber_apertureMomentFourierSynthesis_zero_le_deflated k c).trans
    hscaled.le

end RHTower

