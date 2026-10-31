import GaloisForLFunctions.RHTower.ThetaCusp.SourceActions.SpectralEisensteinSourceFamily
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMPWWeakSourceMassPositivity
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMPWOpticalCTPParity
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMPWCompletedCTPOriginalCapLiftBridge
import GaloisForLFunctions.RHTower.SeamStripRamification
import GaloisForLFunctions.RHTower.ZetaXiZeroCorrespondence

/-!
# The PW-B optical criterion on the zero-independent source family

On every member of the spectral Eisenstein source family the weak optical Ward law holds,
both branch response masses are strictly positive, and the crossed optical flux is
`-16 (Re s - 1/2) Im s` times their product. Hence on the whole nonreal strip the optical
quantity vanishes exactly on the critical line. Since the family is built from `s` alone,
no law valid on the whole family can force optical extinction: it fails at `s = 3/4 + i`.

The zero condition enters only through the arithmetic of a different member: `s` is a Xi zero
exactly when the half-parameter Eisenstein series `E*(·, s/2)` loses its upper Weyl power
(coefficient `Λ(s)`), its lower coefficient `Λ(s - 1)` being nonzero on the whole strip. The
PW-B criterion is therefore equivalent to "one-sided half-parameter cusp implies critical",
which is the Riemann hypothesis.
-/

open Complex Set Filter Topology MeasureTheory UpperHalfPlane ModularGroup
open scoped InnerProductSpace

namespace RHTower.PWBSpectralSource
open D4BMModularCore (energyDomain embedding embedding_injective embedding_dense)
open D4BMGlobalAngularResponse (scalar coordinates angularMeasure)
open D4BMQuadraticMixedSource (physical_parameter_im)

noncomputable section
set_option autoImplicit false

/-! ## Weak optical Ward law on the family -/

/-- Finite-energy mass of one weak response. -/
def weakSourceMass (s : SpectralSite) (b : Bool) : ℝ :=
  ‖embedding (weakResponse s b)‖ ^ (2 : ℕ)

/-- Imaginary pairing of a weak response with its forcing. -/
def weakSourceFlux (s : SpectralSite) (b : Bool) : ℝ :=
  (inner ℂ (embedding (weakResponse s b)) (forcingVector s b)).im

/-- Crossed optical flux of the two physical branches. -/
def crossedOpticalFlux (s : SpectralSite) : ℝ :=
  weakSourceFlux s true * weakSourceMass s false + weakSourceFlux s false * weakSourceMass s true

@[simp] theorem weakSourceMass_site (q : XiZeroCopy) (b : Bool) :
    weakSourceMass (site q) b = D4BMModularCore.weakSourceMass q b := rfl

@[simp] theorem weakSourceFlux_site (q : XiZeroCopy) (b : Bool) :
    weakSourceFlux (site q) b = D4BMModularCore.weakSourceFlux q b := rfl

/-- At every zero location the family's crossed flux is the PW-B optical quantity. -/
@[simp] theorem crossedOpticalFlux_site (q : XiZeroCopy) :
    crossedOpticalFlux (site q) = D4BMPWOpticalCTPParity.crossedOpticalFlux q := rfl

/-- Testing the weak equation against the response itself: `flux = -Im L · mass`. -/
theorem weakSourceFlux_eq (s : SpectralSite) (b : Bool) :
    weakSourceFlux s b = -(parameter s b).im * weakSourceMass s b := by
  let h := weakResponse s b
  have he := weakResponse_spec s b h
  have hh : (inner ℂ h h).im = 0 := by
    simpa using! inner_self_im (𝕜 := ℂ) h
  have hj : (inner ℂ (embedding h) (embedding h)).im = 0 := by
    simpa using! inner_self_im (𝕜 := ℂ) (embedding h)
  have hjr : (inner ℂ (embedding h) (embedding h)).re = ‖embedding h‖ ^ (2 : ℕ) := by
    simpa using! inner_self_eq_norm_sq (𝕜 := ℂ) (embedding h)
  have hi := congrArg Complex.im he
  rw [Complex.sub_im, Complex.mul_im, Complex.neg_im, hh, hj, hjr] at hi
  simp only [Complex.sub_im, Complex.one_im, zero_sub, mul_zero, zero_add] at hi
  dsimp [weakSourceFlux, weakSourceMass, h]
  linarith

/-- The crossed flux is the centered displacement times both response masses. -/
theorem crossedOpticalFlux_eq (s : SpectralSite) :
    crossedOpticalFlux s =
      -16 * ((s.1.re - 1/2) * s.1.im) * (weakSourceMass s true * weakSourceMass s false) := by
  have hp := physical_parameter_im s.1
  have ht : (parameter s true).im = (8 * s.1.re - 10) * s.1.im := hp.1
  have hf : (parameter s false).im = (8 * s.1.re + 2) * s.1.im := hp.2
  rw [crossedOpticalFlux, weakSourceFlux_eq, weakSourceFlux_eq, ht, hf]
  ring

/-! ## Strict positivity of both response masses at every site -/

private theorem two_cpow_nonzero_on_low (s A B : ℂ) (hs : 2*s ≠ 1)
    (hAB : A ≠ 0 ∨ B ≠ 0) :
    ∃ y : ℝ, 1 < y ∧ y < 2 ∧ A*(y:ℂ)^s+B*(y:ℂ)^(1-s) ≠ 0 := by
  by_contra h
  push Not at h
  let y : ℝ := 3/2
  have hy : 0 < y := by norm_num [y]
  have hy1 : 1 < y := by norm_num [y]
  have hy2 : y < 2 := by norm_num [y]
  have hzero : A*(y:ℂ)^s+B*(y:ℂ)^(1-s) = 0 := h y hy1 hy2
  have hlocal : (fun t : ℝ => A*(t:ℂ)^s+B*(t:ℂ)^(1-s)) =ᶠ[𝓝 y] (fun _ => 0) := by
    filter_upwards [((isOpen_Ioo).mem_nhds ⟨hy1,hy2⟩)] with t ht
    exact h t ht.1 ht.2
  have hderiv := ((GaloisForLFunctions.RHTower.hasDerivAt_cpow_ofReal (w := s) hy).const_mul A).add
    ((GaloisForLFunctions.RHTower.hasDerivAt_cpow_ofReal (w := 1-s) hy).const_mul B)
  have hd0 : A*(s*(y:ℂ)^(s-1))+B*((1-s)*(y:ℂ)^((1-s)-1))=0 := by
    have he := hderiv.congr_of_eventuallyEq hlocal.symm
    exact he.unique (hasDerivAt_const y 0)
  have hyc : (y:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hy.ne'
  have hpow1 : (y:ℂ)^(s-1)*(y:ℂ)=(y:ℂ)^s := by
    calc
      _ = (y:ℂ)^(s-1)*(y:ℂ)^1 := by rw [Complex.cpow_one]
      _ = (y:ℂ)^((s-1)+1) := (Complex.cpow_add _ _ hyc).symm
      _ = _ := by congr 1; ring
  have hpow2 : (y:ℂ)^((1-s)-1)*(y:ℂ)=(y:ℂ)^(1-s) := by
    calc
      _ = (y:ℂ)^((1-s)-1)*(y:ℂ)^1 := by rw [Complex.cpow_one]
      _ = (y:ℂ)^(((1-s)-1)+1) := (Complex.cpow_add _ _ hyc).symm
      _ = _ := by congr 1; ring
  have hd1 : A*s*(y:ℂ)^s+B*(1-s)*(y:ℂ)^(1-s)=0 := by
    calc
      _ = A*s*((y:ℂ)^(s-1)*(y:ℂ)) + B*(1-s)*((y:ℂ)^((1-s)-1)*(y:ℂ)) := by
        rw [hpow1,hpow2]
      _ = (A*(s*(y:ℂ)^(s-1))+B*((1-s)*(y:ℂ)^((1-s)-1)))*(y:ℂ) := by ring
      _ = 0 := by rw [hd0]; ring
  have hdiff : (2*s-1)*(A*(y:ℂ)^s)=0 := by
    linear_combination hd1 - (1-s)*hzero
  have hAu : A*(y:ℂ)^s=0 := (mul_eq_zero.mp hdiff).resolve_left (sub_ne_zero.mpr hs)
  have hBu : B*(y:ℂ)^(1-s)=0 := by simpa [hAu] using hzero
  have hA0 : A = 0 := (mul_eq_zero.mp hAu).resolve_right
    (Complex.cpow_ne_zero_iff.mpr (.inl hyc))
  have hB0 : B = 0 := (mul_eq_zero.mp hBu).resolve_right
    (Complex.cpow_ne_zero_iff.mpr (.inl hyc))
  exact hAB.elim (fun hA => hA hA0) (fun hB => hB hB0)

/-- `Λ(w) ≠ 0` whenever `Re w < 0` and `w` is nonreal (functional equation into `Re > 1`). -/
private theorem lambda_ne_zero_of_re_neg {w : ℂ} (hw : w.re < 0) (hwi : w.im ≠ 0) :
    reflectedCompletedLambda w ≠ 0 := by
  have hw0 : w ≠ 0 := by intro h; exact hwi (by rw [h]; rfl)
  have he : reflectedCompletedLambda w = completedRiemannZeta w := by
    rw [reflectedCompletedLambda, riemannZeta_def_of_ne_zero hw0]
    field_simp [gammaR_ne_zero_of_im_ne hwi]
  have hr : 1 < (1 - w).re := by simp; linarith
  have hti : (1 - w).im ≠ 0 := by simpa using hwi
  have ht0 : 1 - w ≠ 0 := by intro h; exact hti (by rw [h]; rfl)
  rw [he, ← completedRiemannZeta_one_sub w]
  intro h
  apply riemannZeta_ne_zero_of_one_lt_re hr
  rw [riemannZeta_def_of_ne_zero ht0, h, zero_div]

/-- The cusp-subtracted forcing never vanishes on the spectral domain: below height two it is
the squared Eisenstein series, whose horizontal mean `Λ(2s)y^s + Λ(2s-1)y^{1-s}` is nonzero. -/
theorem forcingVector_ne_zero (s : SpectralSite) (b : Bool) : forcingVector s b ≠ 0 := by
  obtain ⟨hre0, hre1, him⟩ := s.2
  have hAB : reflectedCompletedLambda (2 * s.1) ≠ 0 ∨
      reflectedCompletedLambda (2 * s.1 - 1) ≠ 0 := by
    by_cases hleft : s.1.re < 1/2
    · right
      apply lambda_ne_zero_of_re_neg
      · simp; linarith
      · simpa using him
    · left
      have hge : 1/2 ≤ s.1.re := le_of_not_gt hleft
      have htwo : (2 * s.1).re = 2 * s.1.re := by norm_num [Complex.mul_re]
      unfold reflectedCompletedLambda
      apply mul_ne_zero
      · apply Complex.Gammaℝ_ne_zero_of_re_pos
        rw [htwo]
        linarith
      · apply riemannZeta_ne_zero_of_one_le_re
        rw [htwo]
        linarith
  have hs : 2 * s.1 ≠ 1 := by
    intro h
    have hi := congrArg Complex.im h
    norm_num [Complex.mul_im] at hi
    exact him (by linarith)
  obtain ⟨y, hy1, hy2, hpr⟩ := two_cpow_nonzero_on_low s.1
    (reflectedCompletedLambda (2*s.1)) (reflectedCompletedLambda (2*s.1-1)) hs hAB
  have hy : 0 < y := by linarith
  intro hF
  have hae : (fun z : UpperHalfPlane => forcing s b (coordinates z)) =ᵐ[angularMeasure]
      (0 : UpperHalfPlane → ℂ) := by
    have h := forcingVector_coe s b
    rw [hF] at h
    exact h.symm.trans (Lp.coeFn_zero ℂ 2 angularMeasure)
  have haeFdo : (fun z : UpperHalfPlane => forcing s b (coordinates z)) =ᵐ[volume.restrict fdo]
      (0 : UpperHalfPlane → ℂ) := by
    change (fun z : UpperHalfPlane => forcing s b (coordinates z)) =ᵐ[volume.restrict fd]
      (0 : UpperHalfPlane → ℂ) at hae
    exact ae_restrict_of_ae_restrict_of_subset fdo_subset_fd hae
  have hcoords : Continuous coordinates := by
    apply continuous_pi
    intro i
    fin_cases i
    · exact UpperHalfPlane.continuous_re
    · exact UpperHalfPlane.continuous_im
  have hc : Continuous (fun z : UpperHalfPlane => forcing s b (coordinates z)) :=
    (forcing_continuousOn s b).comp_continuous hcoords (fun z => z.im_pos)
  have hpoint := Measure.eqOn_open_of_ae_eq haeFdo isOpen_fdo hc.continuousOn continuousOn_const
  have hparam : parameter s b ≠ 0 := neg_ne_zero.mp (cusp_denominators s b).2.1
  have hscalar (x : ℝ) (hx : x ∈ Ioo (-1/2 : ℝ) (1/2)) : scalar (center s) ![x,y] = 0 := by
    let z : UpperHalfPlane := ⟨⟨x,y⟩, by simpa using hy⟩
    have hzfdo : z ∈ fdo := by
      change 1 < Complex.normSq (⟨x,y⟩:ℂ) ∧ |x| < 1/2
      constructor
      · change 1 < x*x+y*y
        nlinarith [sq_nonneg x]
      · rcases hx with ⟨hxl,hxr⟩
        exact abs_lt.mpr ⟨by nlinarith,hxr⟩
    have hz := hpoint hzfdo
    have he : forcing s b ![x,y] = 0 := by simpa [z,coordinates] using hz
    rw [forcing_low s b _ hy2] at he
    have hp2 : parameter s b / 2 ≠ 0 := div_ne_zero hparam (by norm_num)
    exact sq_eq_zero_iff.mp ((mul_eq_zero.mp he).resolve_left hp2)
  have hmean0 : D4BMCuspProjection.mean (fun x => scalar (center s) ![x,y]) = 0 := by
    change (∫ x in Ioc (-1/2:ℝ) (1/2), scalar (center s) ![x,y]) = 0
    rw [integral_Ioc_eq_integral_Ioo]
    apply integral_eq_zero_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    exact hscalar x hx
  rw [D4BMJointSource.mean_scalar (center s) hy] at hmean0
  apply hpr
  rw [← hmean0]
  have hm : 2 * center s = 2 * s.1 - 1 := by unfold center; ring
  simp only [D4BMGlobalAngularResponse.principal, d4BMCompletedEisensteinCuspConstantPart,
    d4BMCompletedEisensteinCuspConstantTerm, d4BMCompletedEisensteinCuspConstantMaassFactor,
    d4BMCompletedEisensteinCuspConstantCoefficient, d4BMCompletedEisensteinCuspWeylExponent,
    d4BMCuspSign, mul_one, Matrix.cons_val_one, Matrix.cons_val_zero, hm]
  norm_num [center]
  ring_nf

/-- Both weak responses carry strictly positive mass at every spectral site. -/
theorem weakSourceMass_pos (s : SpectralSite) (b : Bool) : 0 < weakSourceMass s b := by
  have hforcing := forcingVector_ne_zero s b
  have hresp : embedding (weakResponse s b) ≠ 0 := by
    intro hz
    have hr : weakResponse s b = 0 := embedding_injective (by simpa using hz)
    have horth : ∀ v, inner ℂ (embedding v) (forcingVector s b) = 0 := by
      intro v
      have he := weakResponse_spec s b v
      have hn : -inner ℂ (embedding v) (forcingVector s b) = 0 := by
        simpa [hr] using he.symm
      exact neg_eq_zero.mp hn
    exact hforcing (embedding_dense.eq_zero_of_inner_right ℂ (by
      rintro w ⟨v,rfl⟩
      exact horth v))
  exact pow_pos (norm_pos_iff.mpr hresp) 2

/-! ## Classification of optical extinction on the family -/

/-- **Optical classification.** On the zero-independent family, optical extinction holds
exactly on the critical line. -/
theorem crossedOpticalFlux_eq_zero_iff (s : SpectralSite) :
    crossedOpticalFlux s = 0 ↔ s.1.re = 1/2 := by
  have hM : weakSourceMass s true * weakSourceMass s false ≠ 0 :=
    (mul_pos (weakSourceMass_pos s true) (weakSourceMass_pos s false)).ne'
  have hi : s.1.im ≠ 0 := s.2.2.2
  rw [crossedOpticalFlux_eq]
  constructor
  · intro h
    have h1 : (s.1.re - 1/2) * s.1.im = 0 := by
      have := mul_eq_zero.mp h
      rcases this with h' | h'
      · have : (-16 : ℝ) * ((s.1.re - 1/2) * s.1.im) = 0 := h'
        linarith
      · exact absurd h' hM
    have h2 := (mul_eq_zero.mp h1).resolve_right hi
    linarith
  · intro h
    rw [h]
    ring

/-- The member at `3/4 + i`, which lies off the critical line. -/
def offLineSite : SpectralSite :=
  ⟨3/4 + Complex.I, by norm_num, by norm_num, by norm_num⟩

/-- **Family-uniform no-go.** No law holding on every member of the family forces optical
extinction: the off-line member has nonzero crossed flux. -/
theorem no_familyUniform_optical_extinction (P : SpectralSite → Prop) (hP : ∀ s, P s)
    (hext : ∀ s, P s → crossedOpticalFlux s = 0) : False := by
  have h := (crossedOpticalFlux_eq_zero_iff offLineSite).mp (hext _ (hP _))
  norm_num [offLineSite] at h

/-- Any extinction law on the family is supported on the critical line. -/
theorem extinctionLaw_support_critical (P : SpectralSite → Prop)
    (hext : ∀ s, P s → crossedOpticalFlux s = 0) (s : SpectralSite) (hs : P s) :
    s.1.re = 1/2 :=
  (crossedOpticalFlux_eq_zero_iff s).mp (hext s hs)

/-- The fixed-grade PW partner imbalance at every member equals the crossed optical flux
after the forced ordinate and mass normalization. -/
theorem pwImbalance_crossedOpticalFlux (s : SpectralSite) (k : ℕ) :
    4 * (k + 1 : ℝ) ^ (2 : ℕ) *
        ((schwarzschildParikhWilczekFirstWindingBorelGrowthRatio s.1 k).re -
          (schwarzschildParikhWilczekFirstWindingBorelGrowthRatio (1 - s.1) k).re) *
        s.1.im * (weakSourceMass s true * weakSourceMass s false) =
      -(2 * (k : ℝ) + 1) * crossedOpticalFlux s := by
  rw [schwarzschildParikhWilczekFirstWindingBorelGrowthRatio_re_sub_partner,
    crossedOpticalFlux_eq]
  have hk : (k + 1 : ℝ) ≠ 0 := by positivity
  field_simp
  ring

/-! ## Comparison with the completed ordered current -/

/-- **Optical extinction forces current balance, defects retained.** At every zero location
and every cutoff, vanishing of the family's optical quantity forces the real part of the
completed ordered current, written as twice the native cap functional plus both
full-minus-native lift defects, to vanish. The comparison is an implication through the
critical-line classification, so it needs no calibration constant across amplitudes or
reflection parities. -/
theorem currentBalance_of_opticalExtinction (q : XiZeroCopy) (X k : ℝ)
    (h : crossedOpticalFlux (site q) = 0) :
    (2 * pwbOriginalNativeCapFunctional q 1 X k +
      D4BMLiteralCyclicPeierlsLiftDefect.causalSourceLiftDefect q true true false 1 1 X k +
      D4BMLiteralCyclicPeierlsLiftDefect.causalSourceLiftDefect q false true false 1 1 X k).re =
      0 := by
  have hline : (q.1 : ℂ).re = 1/2 := (crossedOpticalFlux_eq_zero_iff (site q)).mp h
  exact pwb_original_cap_lift_re_balance_on_critical q
    (by simpa only [deningerDivisorThetaEigen] using hline) X k

/-! ## Where the zero condition enters: the half-parameter cusp -/

/-- Eisenstein parameter of the half-parameter member `E*(·, s/2)`. -/
def halfCenter (s : SpectralSite) : ℂ := s.1/2 - 1/2

theorem halfUpperCoefficient_eq (s : SpectralSite) :
    d4BMCompletedEisensteinCuspConstantCoefficient (halfCenter s) true =
      reflectedCompletedLambda s.1 := by
  simp only [d4BMCompletedEisensteinCuspConstantCoefficient, halfCenter, if_true]
  congr 1
  ring

/-- The lower Weyl coefficient `Λ(s - 1)` of `E*(·, s/2)` never vanishes on the strip. -/
theorem halfLowerCoefficient_ne_zero (s : SpectralSite) :
    d4BMCompletedEisensteinCuspConstantCoefficient (halfCenter s) false ≠ 0 := by
  have he : d4BMCompletedEisensteinCuspConstantCoefficient (halfCenter s) false =
      reflectedCompletedLambda (s.1 - 1) := by
    simp only [d4BMCompletedEisensteinCuspConstantCoefficient, halfCenter, Bool.false_eq_true,
      if_false]
    congr 1
    ring
  rw [he]
  apply lambda_ne_zero_of_re_neg
  · simp; linarith [s.2.2.1]
  · simpa using s.2.2.2

/-- On the strip, `s` is a Xi zero exactly when the upper Weyl power of `E*(·, s/2)` vanishes. -/
theorem xi_eq_zero_iff_halfUpperCoefficient (s : SpectralSite) :
    xi s.1 = 0 ↔ d4BMCompletedEisensteinCuspConstantCoefficient (halfCenter s) true = 0 := by
  rw [halfUpperCoefficient_eq, xi_zero_iff_zeta_zero_of_mem_strip s.2.1 s.2.2.1,
    reflectedCompletedLambda]
  have hg : Complex.Gammaℝ s.1 ≠ 0 := Complex.Gammaℝ_ne_zero_of_re_pos s.2.1
  constructor
  · intro h; rw [h, mul_zero]
  · intro h; exact (mul_eq_zero.mp h).resolve_left hg

/-- The zero locations are exactly the sites whose half-parameter member has a one-sided cusp. -/
theorem exists_site_eq_iff_halfUpperCoefficient (s : SpectralSite) :
    (∃ q : XiZeroCopy, site q = s) ↔
      d4BMCompletedEisensteinCuspConstantCoefficient (halfCenter s) true = 0 := by
  rw [← xi_eq_zero_iff_halfUpperCoefficient]
  constructor
  · rintro ⟨q, rfl⟩
    exact xi_eq_zero_of_mem_divisor_support q.1
  · intro h
    let ρ : XiDivisorSupport := ⟨s.1, mem_xi_divisor_support_of_eq_zero h⟩
    have hpos : 0 < Int.toNat ((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ)) := by
      have := xi_divisor_pos_on_support ρ
      omega
    exact ⟨⟨ρ, ⟨0, hpos⟩⟩, Subtype.ext rfl⟩

/-- **The PW-B criterion in source terms.** Optical extinction at every Xi zero copy holds
exactly when every site with a one-sided half-parameter cusp is critical. -/
theorem optical_extinction_at_zeros_iff_halfCusp_critical :
    (∀ q : XiZeroCopy, D4BMPWOpticalCTPParity.crossedOpticalFlux q = 0) ↔
      ∀ s : SpectralSite,
        d4BMCompletedEisensteinCuspConstantCoefficient (halfCenter s) true = 0 → s.1.re = 1/2 := by
  constructor
  · intro h s hs
    obtain ⟨q, rfl⟩ := (exists_site_eq_iff_halfUpperCoefficient s).mpr hs
    exact (crossedOpticalFlux_eq_zero_iff (site q)).mp (h q)
  · intro h q
    rw [← crossedOpticalFlux_site, crossedOpticalFlux_eq_zero_iff]
    exact h (site q) ((exists_site_eq_iff_halfUpperCoefficient (site q)).mp ⟨q, rfl⟩)

/-- The one-sided half-parameter cusp criterion is the Riemann hypothesis. -/
theorem riemannHypothesis_iff_halfCusp_critical :
    RiemannHypothesis ↔ ∀ s : SpectralSite,
      d4BMCompletedEisensteinCuspConstantCoefficient (halfCenter s) true = 0 → s.1.re = 1/2 := by
  rw [riemannHypothesis_iff_xi_zero_re_eq_half]
  constructor
  · intro h s hs
    exact h s.1 ((xi_eq_zero_iff_halfUpperCoefficient s).mpr hs)
  · intro h ρ hρ
    let r : XiDivisorSupport := ⟨ρ, mem_xi_divisor_support_of_eq_zero hρ⟩
    let s : SpectralSite := ⟨ρ, (xi_divisor_support_re_mem_open_unit r).1,
      (xi_divisor_support_re_mem_open_unit r).2, xi_divisor_support_im_ne_zero r⟩
    exact h s ((xi_eq_zero_iff_halfUpperCoefficient s).mp hρ)

end
end RHTower.PWBSpectralSource

#print axioms RHTower.PWBSpectralSource.crossedOpticalFlux_eq_zero_iff
#print axioms RHTower.PWBSpectralSource.no_familyUniform_optical_extinction
#print axioms RHTower.PWBSpectralSource.optical_extinction_at_zeros_iff_halfCusp_critical
#print axioms RHTower.PWBSpectralSource.riemannHypothesis_iff_halfCusp_critical
#print axioms RHTower.PWBSpectralSource.currentBalance_of_opticalExtinction
