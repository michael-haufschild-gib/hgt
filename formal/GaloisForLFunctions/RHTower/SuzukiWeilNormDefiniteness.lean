import GaloisForLFunctions.RHTower.SuzukiWeilFiberVanishing
import GaloisForLFunctions.HTGeometry.CompactFourierIntegrableEntire

/-!
# Suzuki, Lemma 3.2: definiteness of the norm

Masatoshi Suzuki, arXiv:2301.00421v3, Lemma 3.2 (`lem_301`): eq. (3.9),
`‖psi‖_0 = pi^{-1/2} ‖Phat_{D psi}‖_{L^(2 : ℕ)}`, defines a norm on the test space.  Homogeneity and the
triangle inequality are formal consequences of linearity of `Phat_D`; the content is definiteness,
proved here as `eq_zero_of_suzukiPHat_D_ae_zero`.

The chain, all unconditional:

* a.e. vanishing of the transform, plus continuity of the ray series off the divisor, gives
  vanishing of the ray series at every admissible *real* point (the archimedean factor
  `i(1 + Theta^#)/2 = i A/E^#` is nonzero there);
* `suzukiPHatRaySum_eq_zero_off_divisor` carries that to the whole divisor complement;
* the corpus's `xiWeilFiberSum_eq_zero_of_re_xiCauchyTransform_eq_zero_on_ball`, reached through
  `xiCauchyTransform_suzukiRayVector`, kills every multiplicity fibre sum; since the ray numerator
  depends only on the spectral point, each numerator vanishes;
* `integral_expSlope_mul_conj_D` turns that into `compactFourier (conj psi) (-gamma) = 0` at every
  zero of `xi(1/2 - iz)`;
* `suzuki_lemma_two_one` (Su22 Lemma 2.1) forces the compact Fourier transform to vanish
  identically, and `ae_eq_zero_of_compactFourier_vanishing` then kills `psi`.

The exponential-type input `suzuki_lemma_two_one` needs is the Paley-Wiener bound
`norm_compactFourier_le`.
-/

open Complex Filter Topology MeasureTheory Set
open GaloisForLFunctions.RHTower

namespace RHTower
noncomputable section

/-! ## From a.e. vanishing on the line to the ray coefficients -/

theorem eq_zero_of_ae_zero_of_continuousAt {f : ℝ → ℂ} (hae : ∀ᵐ x : ℝ, f x = 0)
    {x₀ : ℝ} (hc : ContinuousAt f x₀) : f x₀ = 0 := by
  by_contra hne
  have hev : ∀ᶠ x in 𝓝 x₀, f x ≠ 0 := hc.eventually_ne hne
  have hnull : volume {x : ℝ | f x ≠ 0} = 0 := by
    have := (MeasureTheory.ae_iff (p := fun x : ℝ => f x = 0)).mp hae
    simpa using this
  have hmem : {x : ℝ | f x ≠ 0} ∈ 𝓝 x₀ := hev
  have hpos : 0 < volume {x : ℝ | f x ≠ 0} := by
    obtain ⟨s, hs, hopen, hx₀⟩ := mem_nhds_iff.mp hmem
    refine lt_of_lt_of_le ?_ (measure_mono hs)
    exact hopen.measure_pos volume ⟨x₀, hx₀⟩
  rw [hnull] at hpos
  exact lt_irrefl 0 hpos

theorem halfFactor_eq {x : ℝ} (hx : XiC ((x : ℝ) : ℂ) ≠ 0) :
    I * (1 + suzukiThetaSharp ((x : ℝ) : ℂ)) / 2
      = I * (XiC ((x : ℝ) : ℂ) / xiHedenmalmDeBrangesESharp ((x : ℝ) : ℂ)) := by
  have hE := xiHedenmalmDeBrangesESharp_ofReal_ne_zero hx
  have hadd := xiHedenmalmDeBrangesE_add_sharp (((x : ℝ) : ℂ))
  rw [suzukiThetaSharp]
  field_simp
  linear_combination hadd

theorem halfFactor_ne_zero {x : ℝ} (hx : XiC ((x : ℝ) : ℂ) ≠ 0) :
    I * (1 + suzukiThetaSharp ((x : ℝ) : ℂ)) / 2 ≠ 0 := by
  rw [halfFactor_eq hx]
  exact mul_ne_zero Complex.I_ne_zero
    (div_ne_zero hx (xiHedenmalmDeBrangesESharp_ofReal_ne_zero hx))

/-- From a.e. vanishing of the transform on the line, the ray series vanishes at every admissible
real point. -/
theorem suzukiPHatRaySum_eq_zero_ofReal {φ : ℝ → ℂ} (hφm : Measurable φ) (hφ : Integrable φ)
    {T : ℝ} (hsupp : ∀ t : ℝ, T < |t| → φ t = 0)
    (hae : ∀ᵐ x : ℝ, suzukiPHat φ ((x : ℝ) : ℂ) = 0)
    {x : ℝ} (hx : XiC ((x : ℝ) : ℂ) ≠ 0) :
    (∑' q : XiZeroCopy, suzukiPHatRayTerm φ ((x : ℝ) : ℂ) q) = 0 := by
  have hRae : ∀ᵐ y : ℝ, (∑' q : XiZeroCopy, suzukiPHatRayTerm φ ((y : ℝ) : ℂ) q) = 0 := by
    filter_upwards [hae, ae_ne_zero_and_XiC_ne_zero] with y hy hy2
    have hconj : suzukiPHatConj φ ((y : ℝ) : ℂ) = 0 := by
      have h1 := suzukiPHat_ofReal_eq_conj φ y
      rw [hy] at h1
      have := congrArg (starRingEnd ℂ) h1.symm
      simpa using this
    rw [suzukiPHatConj_eq_tsum hφm hφ hsupp] at hconj
    exact (mul_eq_zero.mp hconj).resolve_left (halfFactor_ne_zero hy2.2)
  refine eq_zero_of_ae_zero_of_continuousAt hRae ?_
  have hd : DifferentiableAt ℂ
      (fun z : ℂ => ∑' q : XiZeroCopy, suzukiPHatRayTerm φ z q) ((x : ℝ) : ℂ) :=
    differentiableAt_suzukiPHatRaySum hφ hsupp hx
  exact hd.continuousAt.comp Complex.continuous_ofReal.continuousAt

end
end RHTower

namespace RHTower
noncomputable section
open Complex Filter Topology MeasureTheory Set
open GaloisForLFunctions.RHTower
open GaloisForLFunctions.HTGeometry

/-! ## From the fibre sums to the ray numerators -/

theorem suzukiRayVectorFun_eq_zero_of_fiberSum {φ : ℝ → ℂ} (q : XiZeroCopy)
    (h : xiWeilFiberSum (suzukiRayVectorFun φ) q.1 = 0) : suzukiRayVectorFun φ q = 0 := by
  have hconst : ∀ p ∈ xiZeroCopyFiber q.1,
      suzukiRayVectorFun φ p = suzukiRayVectorFun φ q := by
    intro p hp
    rw [mem_xiZeroCopyFiber] at hp
    rw [suzukiRayVectorFun, suzukiRayVectorFun, xiSpectralPoint_eq_support,
      xiSpectralPoint_eq_support, hp]
  rw [xiWeilFiberSum, Finset.sum_congr rfl hconst, Finset.sum_const] at h
  have hcard : (xiZeroCopyFiber q.1).card ≠ 0 := by
    refine Finset.card_ne_zero_of_mem (a := q) ?_
    exact mem_xiZeroCopyFiber.mpr rfl
  rcases smul_eq_zero.mp h with hc | hc
  · exact absurd hc hcard
  · exact hc

/-- The exponential-slope numerator vanishes at every spectral point. -/
theorem integral_expSlope_eq_zero_of_fiberSum {φ : ℝ → ℂ} (q : XiZeroCopy)
    (h : xiWeilFiberSum (suzukiRayVectorFun φ) q.1 = 0) :
    (∫ t : ℝ, (Complex.exp (-(I * xiSpectralPoint q * (t : ℂ))) - 1)
      * (starRingEnd ℂ) (φ t)) = 0 := by
  have h0 := suzukiRayVectorFun_eq_zero_of_fiberSum q h
  rw [suzukiRayVectorFun] at h0
  have h1 : (∫ t : ℝ, (Complex.exp (-(I * xiSpectralPoint q * (t : ℂ))) - 1)
      * (starRingEnd ℂ) (φ t)) / xiSpectralPoint q = 0 := by
    have := congrArg (starRingEnd ℂ) h0
    simpa using this
  exact (div_eq_zero_iff.mp h1).resolve_right (xiSpectralPoint_ne_zero q)

end
end RHTower

namespace RHTower
noncomputable section
open Complex Filter Topology MeasureTheory Set
open GaloisForLFunctions.RHTower
open GaloisForLFunctions.HTGeometry

/-! ## Suzuki, Lemma 3.2 -/

theorem suzukiD_supp {ψ : ℝ → ℂ} {T : ℝ} (hsupp : ∀ t : ℝ, T < |t| → ψ t = 0) :
    ∀ t : ℝ, T < |t| → suzukiD ψ t = 0 := by
  intro t ht
  rw [suzukiD, deriv_eq_zero_of_supp hsupp ht, mul_zero]

theorem continuous_suzukiD {ψ : ℝ → ℂ} (hψ : ContDiff ℝ 1 ψ) : Continuous (suzukiD ψ) := by
  have hc : Continuous (deriv ψ) := hψ.continuous_deriv (by norm_num)
  unfold suzukiD
  fun_prop

theorem integrable_suzukiD {ψ : ℝ → ℂ} (hψ : ContDiff ℝ 1 ψ) {T : ℝ}
    (hsupp : ∀ t : ℝ, T < |t| → ψ t = 0) : Integrable (suzukiD ψ) :=
  (continuous_suzukiD hψ).integrable_of_hasCompactSupport
    (hasCompactSupport_of_supp (suzukiD_supp hsupp))

theorem xi_eq_XiC (z : ℂ) : xi (1 / 2 - I * z) = XiC z := by
  have h1 : XiC (-z) = xi (1 / 2 + (-z) * I) := rfl
  rw [XiC_neg] at h1
  rw [h1]
  congr 1
  ring

theorem compactFourier_conj_eq_zero_of_fiberSum {ψ : ℝ → ℂ} (hψ : ContDiff ℝ 1 ψ) {T : ℝ}
    (hT : 0 ≤ T) (hsupp : ∀ t : ℝ, T < |t| → ψ t = 0)
    (hfib : ∀ ρ : XiDivisorSupport,
      xiWeilFiberSum (suzukiRayVectorFun (suzukiD ψ)) ρ = 0) (q : XiZeroCopy) :
    compactFourier (fun t => (starRingEnd ℂ) (ψ t)) (-(T + 1)) (T + 1)
      (-(xiSpectralPoint q)) = 0 := by
  have h0 := integral_expSlope_eq_zero_of_fiberSum (φ := suzukiD ψ) q (hfib q.1)
  rw [integral_expSlope_mul_conj_D hT hψ hsupp (xiSpectralPoint q)] at h0
  have hI : (∫ t : ℝ, Complex.exp (-(I * xiSpectralPoint q * (t : ℂ)))
      * (starRingEnd ℂ) (ψ t)) = 0 :=
    (mul_eq_zero.mp h0).resolve_left (xiSpectralPoint_ne_zero q)
  have hsupp2 : ∀ t : ℝ, T < |t| →
      (starRingEnd ℂ) (ψ t) * Complex.exp (I * (-(xiSpectralPoint q) * (t : ℂ))) = 0 := by
    intro t ht
    rw [hsupp t ht, map_zero, zero_mul]
  have hall : ∀ t : ℝ,
      (starRingEnd ℂ) (ψ t) * Complex.exp (I * (-(xiSpectralPoint q) * (t : ℂ)))
        = Complex.exp (-(I * xiSpectralPoint q * (t : ℂ))) * (starRingEnd ℂ) (ψ t) := by
    intro t
    rw [show I * (-(xiSpectralPoint q) * (t : ℂ)) = -(I * xiSpectralPoint q * (t : ℂ)) by ring]
    ring
  rw [compactFourier, ← integral_eq_intervalIntegral_of_supp hT hsupp2, ← hI]
  exact integral_congr_ae (Filter.Eventually.of_forall hall)

/-- **Suzuki, Lemma 3.2 (definiteness).**  If the transform of `Dψ` vanishes almost everywhere on
the line, then `ψ` vanishes identically.  This is the only nontrivial half of the assertion that
`‖ψ‖₀ = π^{-1/2}‖𝒫̂_{Dψ}‖_{L²}` is a norm. -/
theorem eq_zero_of_suzukiPHat_D_ae_zero {ψ : ℝ → ℂ} (hψ : ContDiff ℝ 1 ψ) {T : ℝ} (hT : 0 ≤ T)
    (hsupp : ∀ t : ℝ, T < |t| → ψ t = 0)
    (hae : ∀ᵐ x : ℝ, suzukiPHat (suzukiD ψ) ((x : ℝ) : ℂ) = 0) : ψ = 0 := by
  have hφm : Measurable (suzukiD ψ) := (continuous_suzukiD hψ).measurable
  have hφ : Integrable (suzukiD ψ) := integrable_suzukiD hψ hsupp
  have hφs : ∀ t : ℝ, T < |t| → suzukiD ψ t = 0 := suzukiD_supp hsupp
  have hray : ∀ x : ℝ, XiC ((x : ℝ) : ℂ) ≠ 0 →
      (∑' q : XiZeroCopy, suzukiPHatRayTerm (suzukiD ψ) ((x : ℝ) : ℂ) q) = 0 :=
    fun x hx => suzukiPHatRaySum_eq_zero_ofReal hφm hφ hφs hae hx
  have hfib : ∀ ρ : XiDivisorSupport,
      xiWeilFiberSum (suzukiRayVectorFun (suzukiD ψ)) ρ = 0 :=
    fun ρ => xiWeilFiberSum_suzukiRayVectorFun_eq_zero hφ hφs hray ρ
  set g : ℝ → ℂ := fun t => (starRingEnd ℂ) (ψ t) with hg
  set a : ℝ := -(T + 1) with ha
  set b : ℝ := T + 1 with hb
  have hab : a ≤ b := by rw [ha, hb]; linarith
  set F : ℂ → ℂ := fun w => compactFourier g a b (-w) with hF
  have hgint : IntervalIntegrable g volume a b := by
    have hc : Continuous g := by
      rw [hg]
      exact Complex.continuous_conj.comp (hψ.continuous)
    exact hc.intervalIntegrable a b
  have hFdiff : Differentiable ℂ F := by
    have h1 := differentiable_compactFourier_of_integrable hgint
    exact fun w => (h1 (-w)).comp w (differentiable_neg w)
  obtain ⟨M, hM⟩ := (isCompact_uIcc (a := a) (b := b)).exists_bound_of_continuousOn
    (by
      have hc : Continuous g := by
        rw [hg]
        exact Complex.continuous_conj.comp (hψ.continuous)
      exact hc.continuousOn)
  have hMuIoc : ∀ x ∈ Set.uIoc a b, ‖g x‖ ≤ M := by
    intro x hx
    exact hM x (Set.uIoc_subset_uIcc hx)
  have hFtype : ∃ A C : ℝ, 0 ≤ A ∧ 1 ≤ C ∧ ∀ z : ℂ, ‖F z‖ ≤ C * Real.exp (A * ‖z‖) := by
    refine ⟨max |a| |b|, max 1 (M * (b - a)), le_trans (abs_nonneg a) (le_max_left _ _),
      le_max_left _ _, fun z => ?_⟩
    have hbase := norm_compactFourier_le hab hMuIoc (-z)
    have him : |(-z).im| ≤ ‖z‖ := by
      rw [Complex.neg_im, abs_neg]
      exact Complex.abs_im_le_norm z
    have hAnn : (0 : ℝ) ≤ max |a| |b| := le_trans (abs_nonneg a) (le_max_left _ _)
    have hexp : Real.exp (max |a| |b| * |(-z).im|) ≤ Real.exp (max |a| |b| * ‖z‖) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left him hAnn)
    have hMnn : (0 : ℝ) ≤ M := le_trans (norm_nonneg (g a)) (hM a left_mem_uIcc)
    have hba : (0 : ℝ) ≤ b - a := by linarith
    calc ‖F z‖ ≤ M * Real.exp (max |a| |b| * |(-z).im|) * (b - a) := hbase
      _ ≤ M * Real.exp (max |a| |b| * ‖z‖) * (b - a) := by
          have := mul_le_mul_of_nonneg_left hexp hMnn
          nlinarith [Real.exp_pos (max |a| |b| * ‖z‖), hba]
      _ = (M * (b - a)) * Real.exp (max |a| |b| * ‖z‖) := by ring
      _ ≤ max 1 (M * (b - a)) * Real.exp (max |a| |b| * ‖z‖) := by
          exact mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_pos _).le
  have hvalues : ∀ z : ℂ, xi (1 / 2 - I * z) = 0 → F z = 0 := by
    intro z hz
    rw [xi_eq_XiC] at hz
    obtain ⟨q, hq⟩ := (XiC_eq_zero_iff_exists_xiZeroCopy z).mp hz
    rw [hF, ← hq]
    exact compactFourier_conj_eq_zero_of_fiberSum hψ hT hsupp hfib q
  have hFzero := suzuki_lemma_two_one hFdiff 0 hFtype hvalues
  have hGzero : ∀ z : ℂ, compactFourier g a b z = 0 := by
    intro z
    have := congrFun hFzero (-z)
    rw [hF] at this
    simpa using this
  have hgcont : Continuous g := by
    rw [hg]
    exact Complex.continuous_conj.comp hψ.continuous
  have hgsupp : ∀ t : ℝ, T < |t| → g t = 0 := by
    intro t ht
    simp only [hg]
    rw [hsupp t ht, map_zero]
  have hgIcc : ∀ x : ℝ, x ∉ Set.Icc a b → g x = 0 := by
    intro x hx
    refine hgsupp x ?_
    by_contra hc
    push_neg at hc
    have hb2 := abs_le.mp hc
    exact hx ⟨by rw [ha]; linarith [hb2.1], by rw [hb]; linarith [hb2.2]⟩
  have hgae : g =ᵐ[volume] 0 :=
    ae_eq_zero_of_compactFourier_vanishing hab
      (hgcont.integrable_of_hasCompactSupport (hasCompactSupport_of_supp hgsupp))
      hgIcc (t₀ := 0) (r := 1) one_pos
      (Filter.Eventually.of_forall fun t => hGzero ((t : ℝ) : ℂ))
  funext x
  have hψae : ∀ᵐ y : ℝ, ψ y = 0 := by
    filter_upwards [hgae] with y hy
    have : (starRingEnd ℂ) (ψ y) = 0 := hy
    simpa using this
  exact eq_zero_of_ae_zero_of_continuousAt hψae
    ((hψ.continuous).continuousAt)

end
end RHTower

