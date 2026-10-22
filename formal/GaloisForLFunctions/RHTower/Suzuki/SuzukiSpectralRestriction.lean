import GaloisForLFunctions.RHTower.Suzuki.SuzukiFGammaBasis

noncomputable section

/-!
# Restriction to the spectrum

With `{F_γ}` an orthonormal basis of `K(Θ_ξ)`, the map sending an element of the model space to its
values on the spectrum is an isometric isomorphism onto the weighted sequence space with weights
`π m_γ` — the Clark weights `2π/|Θ'(γ)|`.  This is the Makarov--Poltoratski isometry for `Θ_ξ`, and
Lemma 5.3 of the source.

The value at a spectral point is not read off an analytic continuation but from the basis expansion
itself: `F_σ` vanishes at every spectral point except its own, where it equals `(π m_σ)^{-1/2}`, so
the expansion `Σ_σ ⟪F_σ, F⟫ F_σ` has exactly one surviving term at each `γ_ρ`.  Above the axis the
same expansion converges to the Cauchy transform `⟪k_w, F⟫`, so the two descriptions are the
boundary and interior faces of one function.

Isometry is Parseval; injectivity is completeness; surjectivity is the inverse of the basis
representation.
-/

open MeasureTheory Set Complex Filter Topology
open GaloisForLFunctions.HTGeometry

namespace RHTower

/-- The Clark weight `π m_γ` of a spectral point. -/
def suzukiClarkWeight (ρ : XiDivisorSupport) : ℝ := Real.pi * (xiSupportMult ρ : ℝ)

theorem suzukiClarkWeight_pos (ρ : XiDivisorSupport) : 0 < suzukiClarkWeight ρ := by
  have hm : (0 : ℝ) < (xiSupportMult ρ : ℝ) := by
    exact_mod_cast xiSupportMult_pos ρ
  have := Real.pi_pos
  unfold suzukiClarkWeight
  positivity

/-- The restriction of a model-space element to the spectrum: `S_F(γ) = F(γ)`. -/
def suzukiRestriction (hRH : RiemannHypothesis) (F : Lp ℂ 2 (volume : Measure ℝ))
    (ρ : XiDivisorSupport) : ℂ :=
  (inner ℂ (suzukiFGammaFamily hRH ρ) F : ℂ)
    / ((Real.sqrt (suzukiClarkWeight ρ) : ℝ) : ℂ)

theorem inner_eq_sqrt_mul_suzukiRestriction (hRH : RiemannHypothesis)
    (F : Lp ℂ 2 (volume : Measure ℝ)) (ρ : XiDivisorSupport) :
    (inner ℂ (suzukiFGammaFamily hRH ρ) F : ℂ)
      = ((Real.sqrt (suzukiClarkWeight ρ) : ℝ) : ℂ) * suzukiRestriction hRH F ρ := by
  have hpos := suzukiClarkWeight_pos ρ
  have hne : ((Real.sqrt (suzukiClarkWeight ρ) : ℝ) : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]
    exact ne_of_gt (Real.sqrt_pos.mpr hpos)
  rw [suzukiRestriction, mul_div_cancel₀ _ hne]

/-- **Lemma 5.3, the norm identity.**  The restriction map is isometric onto the weighted
sequence space: `‖F‖² = Σ_γ π m_γ |F(γ)|²`.  This is the Makarov--Poltoratski isometry for
`Θ_ξ`, obtained here from Parseval for `{F_γ}`. -/
theorem hasSum_suzukiClarkWeight_normSq_restriction (hRH : RiemannHypothesis)
    {F : Lp ℂ 2 (volume : Measure ℝ)} (hF : F ∈ suzukiModelSpace) :
    HasSum (fun ρ : XiDivisorSupport =>
      suzukiClarkWeight ρ * ‖suzukiRestriction hRH F ρ‖ ^ (2 : ℕ)) (‖F‖ ^ (2 : ℕ)) := by
  have hbase := hasSum_normSq_inner_suzukiFGammaFamily hRH hF
  refine hbase.congr_fun ?_
  intro ρ
  have hpos := suzukiClarkWeight_pos ρ
  rw [inner_eq_sqrt_mul_suzukiRestriction hRH F ρ, norm_mul, mul_pow, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt (le_of_lt hpos)]

/-! ## The restriction map really is evaluation at the spectrum -/

theorem suzukiFGammaFun_at_spectrum (hRH : RiemannHypothesis) (σ ρ : XiDivisorSupport) :
    suzukiFGammaFun (xiRealSpectralPointSupport σ) (xiSupportMult σ)
        (((xiRealSpectralPointSupport ρ : ℝ) : ℂ))
      = if ρ = σ then ((Real.sqrt (suzukiClarkWeight σ) : ℝ) : ℂ)⁻¹ else 0 := by
  by_cases h : ρ = σ
  · subst h
    rw [if_pos rfl, suzukiFGammaFun_self (xiSupportMult_pos ρ)
      (analyticOrderAt_xiRealSpectralPointSupport hRH ρ)]
    rw [suzukiClarkWeight, mul_comm]
    push_cast
    rw [one_div]
  · rw [if_neg h]
    refine suzukiFGammaFun_eq_zero_of_ne _ (XiC_xiRealSpectralPointSupport hRH σ)
      (XiC_xiRealSpectralPointSupport hRH ρ) ?_
    intro hc
    exact h (xiRealSpectralPointSupport_injective hRH (by exact_mod_cast hc))

/-- **The restriction map is the pointwise value of the basis expansion at a spectral point.**
All but one term of the expansion vanish there. -/
theorem hasSum_expansion_at_spectrum (hRH : RiemannHypothesis)
    (F : Lp ℂ 2 (volume : Measure ℝ)) (ρ : XiDivisorSupport) :
    HasSum (fun σ : XiDivisorSupport =>
        (inner ℂ (suzukiFGammaFamily hRH σ) F : ℂ)
          * suzukiFGammaFun (xiRealSpectralPointSupport σ) (xiSupportMult σ)
              (((xiRealSpectralPointSupport ρ : ℝ) : ℂ)))
      (suzukiRestriction hRH F ρ) := by
  have hzero : ∀ σ : XiDivisorSupport, σ ≠ ρ →
      (inner ℂ (suzukiFGammaFamily hRH σ) F : ℂ)
        * suzukiFGammaFun (xiRealSpectralPointSupport σ) (xiSupportMult σ)
            (((xiRealSpectralPointSupport ρ : ℝ) : ℂ)) = 0 := by
    intro σ hσ
    rw [suzukiFGammaFun_at_spectrum hRH σ ρ, if_neg (fun h => hσ h.symm), mul_zero]
  have hval : (inner ℂ (suzukiFGammaFamily hRH ρ) F : ℂ)
      * suzukiFGammaFun (xiRealSpectralPointSupport ρ) (xiSupportMult ρ)
          (((xiRealSpectralPointSupport ρ : ℝ) : ℂ))
      = suzukiRestriction hRH F ρ := by
    rw [suzukiFGammaFun_at_spectrum hRH ρ ρ, if_pos rfl, suzukiRestriction, div_eq_mul_inv]
  rw [← hval]
  exact hasSum_single ρ hzero

/-- **The basis expansion converges pointwise above the axis to the Cauchy transform.** -/
theorem hasSum_expansion_upper (hRH : RiemannHypothesis)
    {F : Lp ℂ 2 (volume : Measure ℝ)} (hF : F ∈ suzukiModelSpace) {w : ℂ} (hw : 0 < w.im) :
    HasSum (fun σ : XiDivisorSupport =>
        (inner ℂ (suzukiFGammaFamily hRH σ) F : ℂ)
          * suzukiFGammaFun (xiRealSpectralPointSupport σ) (xiSupportMult σ) w)
      (inner ℂ ((memLp_suzukiModelKernel hRH hw).toLp _) F : ℂ) := by
  set Kw : ↥(suzukiModelSpace : Submodule ℂ (Lp ℂ 2 (volume : Measure ℝ))) :=
    ⟨(memLp_suzukiModelKernel hRH hw).toLp _,
      suzukiModelKernel_mem_suzukiModelSpace hRH hw⟩ with hKw
  set Fv : ↥(suzukiModelSpace : Submodule ℂ (Lp ℂ 2 (volume : Measure ℝ))) := ⟨F, hF⟩ with hFv
  have hb := (suzukiFGammaHilbertBasis hRH).hasSum_inner_mul_inner Kw Fv
  have hcoe := coe_suzukiFGammaHilbertBasis hRH
  refine hb.congr_fun ?_
  intro σ
  rw [hcoe]
  have h1 : (inner ℂ Kw (suzukiFGammaVec hRH σ) : ℂ)
      = suzukiFGammaFun (xiRealSpectralPointSupport σ) (xiSupportMult σ) w :=
    inner_suzukiModelKernel_suzukiFGammaFamily hRH hw σ
  have h2 : (inner ℂ (suzukiFGammaVec hRH σ) Fv : ℂ)
      = (inner ℂ (suzukiFGammaFamily hRH σ) F : ℂ) := rfl
  rw [h1, h2, mul_comm]


/-! ## Surjectivity of the restriction map -/

/-- **Lemma 5.3, surjectivity.**  Every weighted square-summable sequence on the spectrum is the
restriction of an element of the model space. -/
theorem exists_suzukiRestriction_eq (hRH : RiemannHypothesis) {a : XiDivisorSupport → ℂ}
    (ha : Summable (fun ρ : XiDivisorSupport => suzukiClarkWeight ρ * ‖a ρ‖ ^ (2 : ℕ))) :
    ∃ F : Lp ℂ 2 (volume : Measure ℝ), F ∈ suzukiModelSpace ∧
      suzukiRestriction hRH F = a := by
  set c : XiDivisorSupport → ℂ :=
    fun ρ => ((Real.sqrt (suzukiClarkWeight ρ) : ℝ) : ℂ) * a ρ with hc
  have hcnorm : ∀ ρ, ‖c ρ‖ ^ (2 : ℕ) = suzukiClarkWeight ρ * ‖a ρ‖ ^ (2 : ℕ) := by
    intro ρ
    have hpos := suzukiClarkWeight_pos ρ
    rw [hc]
    rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt (le_of_lt hpos)]
  have hsum : Summable (fun ρ => ‖c ρ‖ ^ (2 : ℕ)) := by
    refine ha.congr ?_
    intro ρ
    exact (hcnorm ρ).symm
  have hmem : Memℓp c 2 := by
    refine memℓp_gen ?_
    simpa using hsum
  set f : lp (fun _ : XiDivisorSupport => ℂ) 2 := ⟨c, hmem⟩ with hf
  set Fv : ↥(suzukiModelSpace : Submodule ℂ (Lp ℂ 2 (volume : Measure ℝ))) :=
    (suzukiFGammaHilbertBasis hRH).repr.symm f with hFv
  refine ⟨(Fv : Lp ℂ 2 (volume : Measure ℝ)), Fv.2, ?_⟩
  funext ρ
  have hrepr : ((suzukiFGammaHilbertBasis hRH).repr Fv) = f := by
    rw [hFv, LinearIsometryEquiv.apply_symm_apply]
  have hval : (inner ℂ (suzukiFGammaFamily hRH ρ)
      ((Fv : Lp ℂ 2 (volume : Measure ℝ))) : ℂ) = c ρ := by
    have h1 := (suzukiFGammaHilbertBasis hRH).repr_apply_apply Fv ρ
    rw [hrepr] at h1
    rw [coe_suzukiFGammaHilbertBasis] at h1
    exact h1.symm
  have hpos := suzukiClarkWeight_pos ρ
  have hne : ((Real.sqrt (suzukiClarkWeight ρ) : ℝ) : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]
    exact ne_of_gt (Real.sqrt_pos.mpr hpos)
  rw [suzukiRestriction, hval, hc]
  field_simp


/-- **Lemma 5.3, injectivity.**  The restriction map separates the model space. -/
theorem suzukiRestriction_inj (hRH : RiemannHypothesis) {F G : Lp ℂ 2 (volume : Measure ℝ)}
    (hF : F ∈ suzukiModelSpace) (hG : G ∈ suzukiModelSpace)
    (h : suzukiRestriction hRH F = suzukiRestriction hRH G) : F = G := by
  have hsub : F - G = 0 := by
    refine eq_zero_of_forall_inner_suzukiFGammaFamily hRH (Submodule.sub_mem _ hF hG) ?_
    intro ρ
    rw [inner_sub_right, inner_eq_sqrt_mul_suzukiRestriction hRH F ρ,
      inner_eq_sqrt_mul_suzukiRestriction hRH G ρ, congrFun h ρ, sub_self]
  exact sub_eq_zero.mp hsub

/-- **Lemma 5.3 on `V(0)`.**  Transporting the isometry through the Fourier transform, the mass of
`ψ ∈ V(0)` is the weighted spectral mass of the restriction of `𝖥ψ`.  (The constant is the one for
the unitary Fourier transform; Suzuki's `2‖ψ‖²` reflects his `‖ψ̂‖² = 2π‖ψ‖²` convention.) -/
theorem hasSum_suzukiClarkWeight_normSq_restriction_suzukiV0 (hRH : RiemannHypothesis)
    {ψ : Lp ℂ 2 (volume : Measure ℝ)} (hψ : ψ ∈ suzukiV0) :
    HasSum (fun ρ : XiDivisorSupport => suzukiClarkWeight ρ *
        ‖suzukiRestriction hRH ((MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ) ψ) ρ‖ ^ (2 : ℕ))
      (‖ψ‖ ^ (2 : ℕ)) := by
  have hmem : ((MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ) ψ) ∈ suzukiModelSpace := by
    rw [← map_fourier_suzukiV0]
    exact ⟨ψ, hψ, rfl⟩
  have hnorm : ‖((MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ) ψ)‖ = ‖ψ‖ :=
    (MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ).norm_map ψ
  have h := hasSum_suzukiClarkWeight_normSq_restriction hRH hmem
  rwa [hnorm] at h


end RHTower
