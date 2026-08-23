import GaloisForLFunctions.RHTower.SuzukiPHatBasisCoefficient
import GaloisForLFunctions.RHTower.SuzukiWeilNormZero
import GaloisForLFunctions.RHTower.SuzukiWeilPropOneThree
import GaloisForLFunctions.RHTower.SuzukiTestSpectralDensity
import GaloisForLFunctions.RHTower.SuzukiSpectralRestriction

noncomputable section

/-!
# `K_0` is the model space

The source's unconditionally defined Hilbert space `K_0` — the `L²`-closure of the span of the
transforms `𝒫̂_{Dψ}` — is the model space `K(Θ_ξ)` under the Riemann hypothesis.  This is the
second half of Theorem 5.6.

The inclusion is equation (3.8): each transform is an energy-kernel series, hence lies in the closed
span of the `F_γ`.  The reverse is density.  Pairing a model-space element `G` against the
transforms and expanding both in the orthonormal basis turns orthogonality into
`Σ_γ m_γ conj(ψ̂(γ)) G(γ) = 0` for every test function; replacing `ψ` by its pointwise conjugate
puts this in the form of the spectral density theorem, which forces `G(γ) = 0` for every `γ`, and
the restriction map is injective on the model space.
-/

open MeasureTheory Set Complex Filter Topology

namespace RHTower

theorem suzukiTestDeriv_continuous (ψ : SuzukiTest) : Continuous (suzukiTestDeriv ψ) := by
  have h : ContDiff ℝ 1 (ψ : ℝ → ℂ) := ψ.smooth.of_le (by simp)
  exact h.continuous_deriv (by norm_num)

theorem suzukiTestDeriv_hasCompactSupport (ψ : SuzukiTest) :
    HasCompactSupport (suzukiTestDeriv ψ) := by
  obtain ⟨a, ha, hsupp⟩ := ψ.exists_aperture
  refine HasCompactSupport.of_support_subset_isCompact (K := Icc (-a) a) isCompact_Icc ?_
  intro t ht
  by_contra hmem
  have hzero : (ψ : ℝ → ℂ) =ᶠ[nhds t] fun _ : ℝ => (0 : ℂ) := by
    have hopen : IsOpen ((Icc (-a) a)ᶜ) := isClosed_Icc.isOpen_compl
    filter_upwards [hopen.mem_nhds hmem] with s hs
    by_contra hne
    exact hs (hsupp hne)
  have hd : deriv (ψ : ℝ → ℂ) t = 0 := by
    rw [hzero.deriv_eq]
    exact deriv_const t 0
  exact ht hd

/-- The transform of `Dψ` as an `L²` element. -/
def suzukiPHatLp (ψ : SuzukiTest) : Lp ℂ 2 (volume : Measure ℝ) :=
  (memLp_suzukiPHat_of_compactSupport (suzukiTestDeriv_continuous ψ)
    (suzukiTestDeriv_hasCompactSupport ψ)).toLp _

theorem coeFn_suzukiPHatLp (ψ : SuzukiTest) :
    ((suzukiPHatLp ψ : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ)
      =ᵐ[volume] fun x : ℝ => suzukiPHat (suzukiTestDeriv ψ) ((x : ℝ) : ℂ) :=
  (memLp_suzukiPHat_of_compactSupport (suzukiTestDeriv_continuous ψ)
    (suzukiTestDeriv_hasCompactSupport ψ)).coeFn_toLp

/-- **The transform lies in the model space, with the spectral values of `ψ` as coefficients.** -/
theorem suzukiPHatLp_mem_and_inner (hRH : RiemannHypothesis) (ψ : SuzukiTest) :
    suzukiPHatLp ψ ∈ suzukiModelSpace ∧
      ∀ ρ : XiDivisorSupport, (inner ℂ (suzukiFGammaFamily hRH ρ) (suzukiPHatLp ψ) : ℂ)
        = I * ((Real.sqrt (Real.pi * (xiSupportMult ρ : ℝ)) : ℝ) : ℂ)
          * suzukiEntireFourier (ψ : ℝ → ℂ) ((xiRealSpectralPointSupport ρ : ℝ) : ℂ) := by
  obtain ⟨a, ha, hsupp⟩ := ψ.exists_aperture
  obtain ⟨S, hSmem, hStend, hSae⟩ := exists_suzukiPHat_lp hRH
    ((ψ.toCompactTest hsupp).toDerivativeZeroMean)
  have hfun : (fun t : ℝ => (((ψ.toCompactTest hsupp).toDerivativeZeroMean) : ℝ → ℂ) t)
      = suzukiTestDeriv ψ := by
    funext t
    rw [SuzukiSmoothCompactTest.coe_toDerivativeZeroMean]
    rfl
  have heq : S = suzukiPHatLp ψ := by
    refine MeasureTheory.Lp.ext ?_
    refine hSae.trans ?_
    rw [hfun]
    exact (coeFn_suzukiPHatLp ψ).symm
  rw [← heq]
  exact ⟨hSmem, fun ρ =>
    inner_suzukiFGammaFamily_suzukiPHat hRH ha.le ψ hsupp hStend ρ⟩

/-- The reflection of a test function. -/
def suzukiTestReflect (ψ : SuzukiTest) : SuzukiTest :=
  ⟨fun x => (ψ : ℝ → ℂ) (-x), by
    refine ⟨ψ.smooth.comp contDiff_neg, ?_⟩
    exact ψ.hasCompactSupport.comp_homeomorph (Homeomorph.neg ℝ)⟩

theorem suzukiTestSpectral_reflect (hRH : RiemannHypothesis) (ψ : SuzukiTest)
    (ρ : XiDivisorSupport) :
    suzukiTestSpectral (suzukiTestReflect ψ) ρ
      = suzukiEntireFourier (ψ : ℝ → ℂ) ((xiRealSpectralPointSupport ρ : ℝ) : ℂ) := by
  have hreal : xiSpectralPointSupport ρ = ((xiRealSpectralPointSupport ρ : ℝ) : ℂ) :=
    (ofReal_xiRealSpectralPointSupport hRH ρ).symm
  rw [suzukiTestSpectral, hreal, suzukiEntireFourier, suzukiEntireFourier]
  rw [← MeasureTheory.integral_neg_eq_self
    (fun x : ℝ => (ψ : ℝ → ℂ) x
      * Complex.exp (I * ((xiRealSpectralPointSupport ρ : ℝ) : ℂ) * (x : ℂ)))]
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards with x
  show (ψ : ℝ → ℂ) (-x)
      * Complex.exp (I * (-((xiRealSpectralPointSupport ρ : ℝ) : ℂ)) * (x : ℂ))
    = (ψ : ℝ → ℂ) (-x)
      * Complex.exp (I * ((xiRealSpectralPointSupport ρ : ℝ) : ℂ) * ((-x : ℝ) : ℂ))
  congr 2
  push_cast
  ring

theorem surjective_suzukiTestReflect : Function.Surjective suzukiTestReflect := by
  intro ψ
  refine ⟨suzukiTestReflect ψ, ?_⟩
  refine Subtype.ext ?_
  funext x
  show (ψ : ℝ → ℂ) (- -x) = (ψ : ℝ → ℂ) x
  rw [neg_neg]


/-- The pointwise conjugate of a test function. -/
def suzukiTestConj (ψ : SuzukiTest) : SuzukiTest :=
  ⟨fun x => (starRingEnd ℂ) ((ψ : ℝ → ℂ) x), by
    refine ⟨Complex.conjCLE.contDiff.comp ψ.smooth, ?_⟩
    exact ψ.hasCompactSupport.comp_left (g := fun z : ℂ => (starRingEnd ℂ) z) (by simp)⟩

theorem suzukiTestSpectral_conj (hRH : RiemannHypothesis) (ψ : SuzukiTest)
    (ρ : XiDivisorSupport) :
    suzukiTestSpectral (suzukiTestConj ψ) ρ
      = (starRingEnd ℂ)
        (suzukiEntireFourier (ψ : ℝ → ℂ) ((xiRealSpectralPointSupport ρ : ℝ) : ℂ)) := by
  have hreal : xiSpectralPointSupport ρ = ((xiRealSpectralPointSupport ρ : ℝ) : ℂ) :=
    (ofReal_xiRealSpectralPointSupport hRH ρ).symm
  rw [suzukiTestSpectral, hreal, suzukiEntireFourier, suzukiEntireFourier, ← integral_conj]
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards with x
  show (starRingEnd ℂ) ((ψ : ℝ → ℂ) x)
      * Complex.exp (I * (-((xiRealSpectralPointSupport ρ : ℝ) : ℂ)) * (x : ℂ))
    = (starRingEnd ℂ) ((ψ : ℝ → ℂ) x
        * Complex.exp (I * ((xiRealSpectralPointSupport ρ : ℝ) : ℂ) * (x : ℂ)))
  rw [map_mul, ← Complex.exp_conj]
  have hc : (starRingEnd ℂ) (I * ((xiRealSpectralPointSupport ρ : ℝ) : ℂ) * (x : ℂ))
      = I * (-((xiRealSpectralPointSupport ρ : ℝ) : ℂ)) * (x : ℂ) := by
    simp
  rw [hc]

theorem surjective_suzukiTestConj : Function.Surjective suzukiTestConj := by
  intro ψ
  refine ⟨suzukiTestConj ψ, ?_⟩
  refine Subtype.ext ?_
  funext x
  show (starRingEnd ℂ) ((starRingEnd ℂ) ((ψ : ℝ → ℂ) x)) = (ψ : ℝ → ℂ) x
  rw [Complex.conj_conj]


section

variable [hRHf : Fact RiemannHypothesis]

/-- **Density of the transforms.**  An element of the model space orthogonal to every transform
vanishes. -/
theorem eq_zero_of_inner_suzukiPHatLp {G : Lp ℂ 2 (volume : Measure ℝ)}
    (hG : G ∈ suzukiModelSpace)
    (h : ∀ ψ : SuzukiTest, (inner ℂ (suzukiPHatLp ψ) G : ℂ) = 0) : G = 0 := by
  have hRH := hRHf.out
  have hpi := Real.pi_pos
  set A : XiDivisorSupport → ℂ := fun ρ => (starRingEnd ℂ) (suzukiRestriction hRH G ρ) with hA
  have hmnn : ∀ ρ : XiDivisorSupport, (0 : ℝ) ≤ (xiSupportMult ρ : ℝ) :=
    fun ρ => Nat.cast_nonneg _
  have hsum : Summable (fun ρ : XiDivisorSupport => (xiSupportMult ρ : ℝ) * ‖A ρ‖ ^ 2) := by
    have hbase := ((hasSum_suzukiClarkWeight_normSq_restriction hRH hG).summable).mul_left
      (1 / Real.pi)
    refine hbase.congr fun ρ => ?_
    rw [suzukiClarkWeight, hA]
    simp only [RCLike.norm_conj]
    field_simp
  have hsqmul : ∀ ρ : XiDivisorSupport,
      ((Real.sqrt (Real.pi * (xiSupportMult ρ : ℝ)) : ℝ) : ℂ)
        * ((Real.sqrt (suzukiClarkWeight ρ) : ℝ) : ℂ)
      = ((Real.pi : ℝ) : ℂ) * ((xiSupportMult ρ : ℝ) : ℂ) := by
    intro ρ
    rw [suzukiClarkWeight, ← Complex.ofReal_mul, Real.mul_self_sqrt (by positivity)]
    push_cast
    ring
  have hne : (-I * ((Real.pi : ℝ) : ℂ)) ≠ 0 := by
    refine mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) ?_
    simp [Real.pi_ne_zero]
  have horth : ∀ χ : SuzukiTest,
      (∑' ρ : XiDivisorSupport,
        ((xiSupportMult ρ : ℝ) : ℂ) * (starRingEnd ℂ) (A ρ)
          * suzukiTestSpectral χ ρ) = 0 := by
    intro χ
    obtain ⟨ψ, rfl⟩ := surjective_suzukiTestConj χ
    obtain ⟨hmem, hcoef⟩ := suzukiPHatLp_mem_and_inner hRH ψ
    set X : ↥(suzukiModelSpace : Submodule ℂ (Lp ℂ 2 (volume : Measure ℝ))) :=
      ⟨suzukiPHatLp ψ, hmem⟩ with hX
    set Y : ↥(suzukiModelSpace : Submodule ℂ (Lp ℂ 2 (volume : Measure ℝ))) :=
      ⟨G, hG⟩ with hY
    have hb := (suzukiFGammaHilbertBasis hRH).tsum_inner_mul_inner X Y
    have hXY : (inner ℂ X Y : ℂ) = 0 := h ψ
    rw [hXY] at hb
    have hfactor : ∀ ρ : XiDivisorSupport,
        (inner ℂ X ((suzukiFGammaHilbertBasis hRH) ρ) : ℂ)
          * (inner ℂ ((suzukiFGammaHilbertBasis hRH) ρ) Y : ℂ)
        = (-I * ((Real.pi : ℝ) : ℂ))
          * (((xiSupportMult ρ : ℝ) : ℂ) * (starRingEnd ℂ) (A ρ)
            * suzukiTestSpectral (suzukiTestConj ψ) ρ) := by
      intro ρ
      have h1 : (inner ℂ ((suzukiFGammaHilbertBasis hRH) ρ) X : ℂ)
          = I * ((Real.sqrt (Real.pi * (xiSupportMult ρ : ℝ)) : ℝ) : ℂ)
            * suzukiEntireFourier (ψ : ℝ → ℂ)
                ((xiRealSpectralPointSupport ρ : ℝ) : ℂ) := by
        rw [coe_suzukiFGammaHilbertBasis]
        exact hcoef ρ
      have hleft : (inner ℂ X ((suzukiFGammaHilbertBasis hRH) ρ) : ℂ)
          = (starRingEnd ℂ) (I * ((Real.sqrt (Real.pi * (xiSupportMult ρ : ℝ)) : ℝ) : ℂ)
            * suzukiEntireFourier (ψ : ℝ → ℂ)
                ((xiRealSpectralPointSupport ρ : ℝ) : ℂ)) := by
        rw [← h1]
        exact (inner_conj_symm (𝕜 := ℂ) X ((suzukiFGammaHilbertBasis hRH) ρ)).symm
      have hright : (inner ℂ ((suzukiFGammaHilbertBasis hRH) ρ) Y : ℂ)
          = ((Real.sqrt (suzukiClarkWeight ρ) : ℝ) : ℂ) * suzukiRestriction hRH G ρ := by
        rw [coe_suzukiFGammaHilbertBasis]
        exact inner_eq_sqrt_mul_suzukiRestriction hRH G ρ
      rw [hleft, hright, map_mul, map_mul, Complex.conj_I, Complex.conj_ofReal,
        suzukiTestSpectral_conj hRH ψ ρ, hA]
      simp only [Complex.conj_conj]
      have hkey := hsqmul ρ
      linear_combination (-I * (starRingEnd ℂ) (suzukiEntireFourier (ψ : ℝ → ℂ)
        ((xiRealSpectralPointSupport ρ : ℝ) : ℂ)) * suzukiRestriction hRH G ρ) * hkey
    rw [tsum_congr hfactor, tsum_mul_left] at hb
    exact (mul_eq_zero.mp hb).resolve_left hne
  have hAzero := eq_zero_of_orthogonal_suzukiTestSpectral hRH hsum horth
  have hrest : suzukiRestriction hRH G = suzukiRestriction hRH 0 := by
    funext ρ
    have h0 := hAzero ρ
    rw [hA] at h0
    have : suzukiRestriction hRH G ρ = 0 := by
      have := congrArg (starRingEnd ℂ) h0
      rwa [Complex.conj_conj, map_zero] at this
    rw [this, suzukiRestriction]
    simp
  exact suzukiRestriction_inj hRH hG (Submodule.zero_mem _) hrest

/-- **`K_0`**: the `L²`-closure of the span of the transforms. -/
def suzukiKZero : Submodule ℂ (Lp ℂ 2 (volume : Measure ℝ)) :=
  (Submodule.span ℂ (Set.range suzukiPHatLp)).topologicalClosure

omit hRHf in
theorem suzukiPHatLp_mem_suzukiKZero (ψ : SuzukiTest) : suzukiPHatLp ψ ∈ suzukiKZero :=
  Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨ψ, rfl⟩)

omit hRHf in
theorem suzukiKZero_le_suzukiModelSpace (hRH : RiemannHypothesis) :
    suzukiKZero ≤ suzukiModelSpace := by
  refine Submodule.topologicalClosure_minimal _ ?_ isClosed_suzukiModelSpace
  refine Submodule.span_le.mpr ?_
  rintro S ⟨ψ, rfl⟩
  exact (suzukiPHatLp_mem_and_inner hRH ψ).1

/-- **Theorem 5.6, `K_0 = K(Θ)`.**  The unconditional Hilbert space `K_0` is the model space. -/
theorem suzukiKZero_eq_suzukiModelSpace : suzukiKZero = suzukiModelSpace := by
  have hRH := hRHf.out
  refine le_antisymm (suzukiKZero_le_suzukiModelSpace hRH) ?_
  haveI : CompleteSpace (suzukiKZero : Submodule ℂ (Lp ℂ 2 (volume : Measure ℝ))) :=
    (Submodule.isClosed_topologicalClosure _).completeSpace_coe
  intro G hG
  set P : Lp ℂ 2 (volume : Measure ℝ) := suzukiKZero.starProjection G with hP
  have hPmem : P ∈ suzukiKZero := suzukiKZero.starProjection_apply_mem G
  have hPmodel : P ∈ suzukiModelSpace := suzukiKZero_le_suzukiModelSpace hRH hPmem
  have hdiffmem : G - P ∈ suzukiModelSpace := Submodule.sub_mem _ hG hPmodel
  have hperp : G - P ∈ suzukiKZeroᗮ := suzukiKZero.sub_starProjection_mem_orthogonal G
  have hzero : G - P = 0 := by
    refine eq_zero_of_inner_suzukiPHatLp hdiffmem ?_
    intro ψ
    exact Submodule.mem_orthogonal _ _ |>.mp hperp _ (suzukiPHatLp_mem_suzukiKZero ψ)
  have : G = P := sub_eq_zero.mp hzero
  rw [this]
  exact hPmem


end

end RHTower

