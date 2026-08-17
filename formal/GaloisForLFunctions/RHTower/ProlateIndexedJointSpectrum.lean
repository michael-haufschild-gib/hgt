import GaloisForLFunctions.RHTower.ProlateBandTopParityContinuation
import GaloisForLFunctions.RHTower.L2FourierUncertainty
import GaloisForLFunctions.RHTower.SoninEulerTripleShellOverlap
import GaloisForLFunctions.RHTower.ProlateGlobalBandEigen
import GaloisForLFunctions.HTGeometry.GreedyCourantFischer
import GaloisForLFunctions.HTGeometry.OrthonormalTrialSpan

/-!
# Live indexed prolate spectrum and global cross-rung ordering

The abstract signed greedy spectrum of the compressed Fourier block permits dead stages and
repeated absolute values.  Neither can occur for the actual prolate operator.  Bounded-support
Fourier uniqueness makes the compressed transform injective on its time-limited carrier, while
an infinite orthonormal shell family lives inside every positive aperture.  Consequently every
greedy stage is live and normalized.

To remove possible absolute-value collisions, real Slepian eigenspace simplicity is complexified
without choosing phases.  Equal squared signed values make the two smooth unit-band extensions,
then their physical sources and original `L²` modes, proportional.  Greedy orthogonality rules
that out.  Thus the actual squared finite-Fourier spectrum is globally strictly decreasing at
every positive aperture.
-/

noncomputable section

open MeasureTheory Set ContinuousLinearMap
open scoped InnerProduct InnerProductSpace

namespace RHTower

/-- The compressed Fourier transform is injective on its time-limited carrier. -/
theorem evenTimeBandFourier_injective_on_timeLimited
    {a : ℝ} (ha : 0 < a) {f : evenSubspace}
    (hf : f ∈ evenTimeLimitedSubspace a)
    (hTf : evenTimeBandFourier a f = 0) :
    f = 0 := by
  have hfix : evenIndicatorCutoff a f = f :=
    (mem_evenTimeLimitedSubspace_iff a f).mp hf
  have hsupp : ∀ᵐ x ∂volume, x ∉ Icc (-a) a →
      (((f : evenSubspace) : SoninL2) : ℝ → ℂ) x = 0 := by
    have hfixL2 := congrArg (fun z : evenSubspace => (z : SoninL2)) hfix
    change indicatorCutoff (centralInterval a) (measurableSet_centralInterval a)
        (f : SoninL2) = (f : SoninL2) at hfixL2
    filter_upwards [indicatorCutoff_ae (centralInterval a)
      (measurableSet_centralInterval a) (f : SoninL2)] with x hx hout
    rw [hfixL2] at hx
    simpa [centralInterval, hout] using hx
  have hcutFourier :
      evenIndicatorCutoff a (evenFourierTransform f) = 0 := by
    rw [evenTimeBandFourier_eq_mul] at hTf
    change evenIndicatorCutoff a
      (evenFourierTransform (evenIndicatorCutoff a f)) = 0 at hTf
    rwa [hfix] at hTf
  have hcutFourierL2 :
      indicatorCutoff (centralInterval a) (measurableSet_centralInterval a)
          (fourierUnitary (f : SoninL2)) = 0 := by
    exact congrArg (fun z : evenSubspace => (z : SoninL2)) hcutFourier
  have hFzero : ∀ᵐ w ∂volume, w ∈ Ioo (-a) a →
      (((fourierUnitary (f : SoninL2) : SoninL2) : ℝ → ℂ) w = 0) := by
    have hzero := Lp.eq_zero_iff_ae_eq_zero.mp hcutFourierL2
    filter_upwards [indicatorCutoff_ae (centralInterval a)
        (measurableSet_centralInterval a) (fourierUnitary (f : SoninL2)),
      hzero] with w hcut hzeroW hw
    have hwmem : w ∈ centralInterval a := ⟨hw.1.le, hw.2.le⟩
    rw [hcut, Set.indicator_of_mem hwmem] at hzeroW
    exact hzeroW
  have hfzero : (f : SoninL2) = 0 :=
    l2_eq_zero_of_bounded_support_fourier_vanishes_on_Ioo
      (f : SoninL2) hsupp (by linarith) hFzero
  exact Subtype.ext hfzero

/-- Every positive aperture contains an infinite orthonormal family of time-limited even shells. -/
theorem orthonormal_timeLimitedShells {a : ℝ} (ha : 0 < a) :
    Orthonormal ℂ (evenShellVectorEven (a / 2) a (by linarith)) := by
  exact evenShellVectorEven_orthonormal (a / 2) a (by linarith) (by linarith)

theorem timeLimitedShell_mem {a : ℝ} (ha : 0 < a) (n : ℕ) :
    evenShellVectorEven (a / 2) a (by linarith) n ∈
      evenTimeLimitedSubspace a := by
  rw [mem_evenTimeLimitedSubspace_iff]
  exact evenIndicatorCutoff_evenShellVectorEven_of_le
    (a / 2) a a (by linarith) le_rfl n

/-- Every greedy signed rung of the actual compressed Fourier block is live at every positive
aperture. -/
theorem evenProlateSignedValue_ne_zero
    {a : ℝ} (ha : 0 < a) (n : ℕ) :
    evenProlateSignedValue a n ≠ 0 := by
  intro hvalue
  let g : Fin (n + 1) → evenSubspace := fun i =>
    evenShellVectorEven (a / 2) a (by linarith) i
  let V : Submodule ℂ evenSubspace := Submodule.span ℂ (Set.range g)
  have hg : Orthonormal ℂ g :=
    (orthonormal_timeLimitedShells ha).comp Fin.val Fin.val_injective
  have hdim : n < Module.finrank ℂ V := by
    rw [show Module.finrank ℂ V = n + 1 by
      exact ContinuousLinearMap.finrank_span_orthonormal hg]
    omega
  obtain ⟨x, hxV, hxne, hxorth⟩ :=
    ContinuousLinearMap.exists_mem_ne_zero_orthogonal_of_finrank_lt
      V (evenProlateSignedMode a) n hdim
  have hVtime : V ≤ evenTimeLimitedSubspace a := by
    apply Submodule.span_le.mpr
    rintro y ⟨i, rfl⟩
    exact timeLimitedShell_mem ha i
  have hxtime : x ∈ evenTimeLimitedSubspace a := hVtime hxV
  let y : evenSubspace := ((‖x‖ : ℂ))⁻¹ • x
  have hynorm : ‖y‖ = 1 := by
    exact norm_smul_inv_norm hxne
  have hyorth : ∀ m < n,
      inner ℂ (evenProlateSignedMode a m) y = 0 := by
    intro m hm
    simp [y, hxorth m hm]
  have hytime : y ∈ evenTimeLimitedSubspace a :=
    (evenTimeLimitedSubspace a).smul_mem _ hxtime
  have habs := ContinuousLinearMap.abs_sgVal
    (isCompactOperator_evenTimeBandFourier a ha)
    (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
      (adjoint_evenTimeBandFourier a)) n
  have hsup : ContinuousLinearMap.orthSup (evenTimeBandFourier a)
      (evenProlateSignedMode a) n = 0 := by
    change ContinuousLinearMap.orthSup (evenTimeBandFourier a)
      (ContinuousLinearMap.sgVec (evenTimeBandFourier a)) n = 0
    rw [← habs]
    change |evenProlateSignedValue a n| = 0
    exact abs_eq_zero.mpr hvalue
  have hbound := ContinuousLinearMap.le_orthSup (evenTimeBandFourier a)
    (evenProlateSignedMode a) n (by simp [hynorm]) hyorth
  rw [hsup] at hbound
  have hTy : evenTimeBandFourier a y = 0 := by
    apply norm_eq_zero.mp
    exact le_antisymm hbound (norm_nonneg _)
  have hyzero := evenTimeBandFourier_injective_on_timeLimited ha hytime hTy
  rw [hyzero, norm_zero] at hynorm
  exact zero_ne_one hynorm

theorem evenProlateSignedMode_norm_one
    {a : ℝ} (ha : 0 < a) (n : ℕ) :
    ‖evenProlateSignedMode a n‖ = 1 := by
  rcases evenProlateSignedMode_norm_zero_or_one a n with hzero | hone
  · exact False.elim ((evenProlateSignedValue_ne_zero ha n)
      (ContinuousLinearMap.sgVal_zero_of_dead hzero))
  · exact hone

/-- Continuous real Slepian eigenfunctions at one live eigenvalue are globally proportional. -/
theorem continuous_real_bandEigen_proportional
    {c lam : ℝ} (hc : 0 < c) (hlam : lam ≠ 0)
    {Phi Psi : ℝ → ℝ} (hPhi : Continuous Phi) (hPsi : Continuous Psi)
    (hPhiNe : Phi ≠ 0)
    (hPhiEig : ∀ x : ℝ, bandTransform c Phi x = lam * Phi x)
    (hPsiEig : ∀ x : ℝ, bandTransform c Psi x = lam * Psi x) :
    ∃ s : ℝ, ∀ x : ℝ, Psi x = s * Phi x := by
  let f : GaloisForLFunctions.RHTower.RealIntervalL2 (-1 : ℝ) 1 :=
    GaloisForLFunctions.RHTower.bandClass Phi hPhi
  let g : GaloisForLFunctions.RHTower.RealIntervalL2 (-1 : ℝ) 1 :=
    GaloisForLFunctions.RHTower.bandClass Psi hPsi
  have hfEig : GaloisForLFunctions.RHTower.bandOperatorL2 c f = lam • f := by
    rw [show f = GaloisForLFunctions.RHTower.bandClass Phi hPhi from rfl,
      GaloisForLFunctions.RHTower.bandOperatorL2_bandClass]
    have hclass :
        GaloisForLFunctions.RHTower.bandClass (bandTransform c Phi)
            (GaloisForLFunctions.RHTower.continuous_bandTransform c hPhi) =
          GaloisForLFunctions.RHTower.bandClass (fun x => lam * Phi x)
            (continuous_const.mul hPhi) := by
      apply Lp.ext
      filter_upwards [GaloisForLFunctions.RHTower.coeFn_bandClass (bandTransform c Phi)
          (GaloisForLFunctions.RHTower.continuous_bandTransform c hPhi),
        GaloisForLFunctions.RHTower.coeFn_bandClass (fun x => lam * Phi x)
          (continuous_const.mul hPhi)]
          with x hx₁ hx₂
      rw [hx₁, hx₂, hPhiEig]
    rw [hclass, GaloisForLFunctions.RHTower.bandClass_smul]
  have hgEig : GaloisForLFunctions.RHTower.bandOperatorL2 c g = lam • g := by
    rw [show g = GaloisForLFunctions.RHTower.bandClass Psi hPsi from rfl,
      GaloisForLFunctions.RHTower.bandOperatorL2_bandClass]
    have hclass :
        GaloisForLFunctions.RHTower.bandClass (bandTransform c Psi)
            (GaloisForLFunctions.RHTower.continuous_bandTransform c hPsi) =
          GaloisForLFunctions.RHTower.bandClass (fun x => lam * Psi x)
            (continuous_const.mul hPsi) := by
      apply Lp.ext
      filter_upwards [GaloisForLFunctions.RHTower.coeFn_bandClass (bandTransform c Psi)
          (GaloisForLFunctions.RHTower.continuous_bandTransform c hPsi),
        GaloisForLFunctions.RHTower.coeFn_bandClass (fun x => lam * Psi x)
          (continuous_const.mul hPsi)]
          with x hx₁ hx₂
      rw [hx₁, hx₂, hPsiEig]
    rw [hclass, GaloisForLFunctions.RHTower.bandClass_smul]
  have hfNe : f ≠ 0 := by
    intro hfzero
    apply hPhiNe
    have hrec := eigenExtension_bandClass_eq_self_of_bandEigen
      hlam hPhi hPhiEig
    rw [← hrec]
    change eigenExtensionLinearMap c lam f = 0
    rw [hfzero, map_zero]
  obtain ⟨s, hgf⟩ := bandOperatorL2_eigenvectors_proportional
    hc hlam hfEig hfNe hgEig
  refine ⟨s, fun x => ?_⟩
  have hPhiRec := congrFun
    (eigenExtension_bandClass_eq_self_of_bandEigen hlam hPhi hPhiEig) x
  have hPsiRec := congrFun
    (eigenExtension_bandClass_eq_self_of_bandEigen hlam hPsi hPsiEig) x
  calc
    Psi x = GaloisForLFunctions.RHTower.eigenExtension c lam g x := hPsiRec.symm
    _ = GaloisForLFunctions.RHTower.eigenExtension c lam (s • f) x := by rw [hgf]
    _ = s * GaloisForLFunctions.RHTower.eigenExtension c lam f x :=
      GaloisForLFunctions.RHTower.eigenExtension_smul c lam s f x
    _ = s * Phi x := by rw [hPhiRec]

/-- The complexification of a live real Slepian eigenspace is still one complex line. -/
theorem continuous_complex_bandEigen_proportional
    {c lam : ℝ} (hc : 0 < c) (hlam : lam ≠ 0)
    {q r : ℝ → ℂ} (hq : Continuous q) (hr : Continuous r) (hqNe : q ≠ 0)
    (hqReEig : ∀ x : ℝ,
      bandTransform c (fun t => (q t).re) x = lam * (q x).re)
    (hqImEig : ∀ x : ℝ,
      bandTransform c (fun t => (q t).im) x = lam * (q x).im)
    (hrReEig : ∀ x : ℝ,
      bandTransform c (fun t => (r t).re) x = lam * (r x).re)
    (hrImEig : ∀ x : ℝ,
      bandTransform c (fun t => (r t).im) x = lam * (r x).im) :
    ∃ z : ℂ, ∀ x : ℝ, r x = z * q x := by
  have hqRe : Continuous fun x => (q x).re := Complex.continuous_re.comp hq
  have hqIm : Continuous fun x => (q x).im := Complex.continuous_im.comp hq
  have hrRe : Continuous fun x => (r x).re := Complex.continuous_re.comp hr
  have hrIm : Continuous fun x => (r x).im := Complex.continuous_im.comp hr
  by_cases hqReNe : (fun x => (q x).re) ≠ 0
  · obtain ⟨u, hu⟩ := continuous_real_bandEigen_proportional
      hc hlam hqRe hqIm hqReNe hqReEig hqImEig
    obtain ⟨v, hv⟩ := continuous_real_bandEigen_proportional
      hc hlam hqRe hrRe hqReNe hqReEig hrReEig
    obtain ⟨w, hw⟩ := continuous_real_bandEigen_proportional
      hc hlam hqRe hrIm hqReNe hqReEig hrImEig
    let alpha : ℂ := 1 + Complex.I * (u : ℂ)
    let beta : ℂ := (v : ℂ) + Complex.I * (w : ℂ)
    have halpha : alpha ≠ 0 := by
      intro hzero
      have hre := congrArg Complex.re hzero
      simp [alpha] at hre
    refine ⟨beta * alpha⁻¹, fun x => ?_⟩
    have hqDecomp : q x = alpha * ((q x).re : ℂ) := by
      apply Complex.ext
      · simp [alpha]
      · simp [alpha, hu x]
    have hrDecomp : r x = beta * ((q x).re : ℂ) := by
      apply Complex.ext
      · simp [beta, hv x]
      · simp [beta, hw x]
    calc
      r x = beta * ((q x).re : ℂ) := hrDecomp
      _ = (beta * alpha⁻¹) * (alpha * ((q x).re : ℂ)) := by field_simp
      _ = (beta * alpha⁻¹) * q x := by rw [← hqDecomp]
  · have hqReZero : (fun x => (q x).re) = 0 := not_ne_iff.mp hqReNe
    have hqImNe : (fun x => (q x).im) ≠ 0 := by
      intro hqImZero
      apply hqNe
      funext x
      apply Complex.ext
      · exact congrFun hqReZero x
      · exact congrFun hqImZero x
    obtain ⟨v, hv⟩ := continuous_real_bandEigen_proportional
      hc hlam hqIm hrRe hqImNe hqImEig hrReEig
    obtain ⟨w, hw⟩ := continuous_real_bandEigen_proportional
      hc hlam hqIm hrIm hqImNe hqImEig hrImEig
    let beta : ℂ := (v : ℂ) + Complex.I * (w : ℂ)
    refine ⟨beta * Complex.I⁻¹, fun x => ?_⟩
    have hqDecomp : q x = Complex.I * ((q x).im : ℂ) := by
      apply Complex.ext
      · simpa using congrFun hqReZero x
      · simp
    have hrDecomp : r x = beta * ((q x).im : ℂ) := by
      apply Complex.ext
      · simp [beta, hv x]
      · simp [beta, hw x]
    calc
      r x = beta * ((q x).im : ℂ) := hrDecomp
      _ = (beta * Complex.I⁻¹) * (Complex.I * ((q x).im : ℂ)) := by field_simp
      _ = (beta * Complex.I⁻¹) * q x := by rw [← hqDecomp]

/-- Equal squared signed values force the corresponding global unit-band extensions onto one
complex line. -/
theorem evenProlateSignedUnitExtension_proportional_of_sq_eq
    {a : ℝ} (ha : 0 < a) {m n : ℕ}
    (hsq : evenProlateSignedValue a m ^ 2 =
      evenProlateSignedValue a n ^ 2) :
    ∃ z : ℂ, ∀ x : ℝ,
      evenProlateSignedUnitExtension a n (evenProlateSignedValue_ne_zero ha n) x =
        z * evenProlateSignedUnitExtension a m
          (evenProlateSignedValue_ne_zero ha m) x := by
  let hm := evenProlateSignedValue_ne_zero ha m
  let hn := evenProlateSignedValue_ne_zero ha n
  let q : ℝ → ℂ := evenProlateSignedUnitExtension a m hm
  let r : ℝ → ℂ := evenProlateSignedUnitExtension a n hn
  have hqNe : q ≠ 0 := by
    obtain ⟨x, hx, hxne⟩ :=
      exists_rescaled_evenProlateSignedPointwiseSource_ne_zero ha m hm
    intro hzero
    have hxzero := congrFun hzero x
    change evenProlateSignedUnitExtension a m hm x = 0 at hxzero
    rw [evenProlateSignedUnitExtension_eq_source ha m hm hx] at hxzero
    exact hxne hxzero
  have hc : 0 < 2 * Real.pi * a ^ 2 := by positivity
  have hlam : evenProlateSignedValue a m ^ 2 ≠ 0 := pow_ne_zero 2 hm
  obtain ⟨z, hz⟩ := continuous_complex_bandEigen_proportional hc hlam
    (continuous_evenProlateSignedUnitExtension a m hm)
    (continuous_evenProlateSignedUnitExtension a n hn) hqNe
    (bandTransform_evenProlateSignedUnitExtension_re_global ha hm)
    (bandTransform_evenProlateSignedUnitExtension_im_global ha hm)
    (fun x => by
      rw [hsq]
      exact bandTransform_evenProlateSignedUnitExtension_re_global ha hn x)
    (fun x => by
      rw [hsq]
      exact bandTransform_evenProlateSignedUnitExtension_im_global ha hn x)
  exact ⟨z, hz⟩

/-- Equal squared values force the normalized physical pointwise sources to agree up to one
complex scalar almost everywhere. -/
theorem evenProlateSignedPointwiseSource_ae_proportional_of_sq_eq
    {a : ℝ} (ha : 0 < a) {m n : ℕ}
    (hsq : evenProlateSignedValue a m ^ 2 =
      evenProlateSignedValue a n ^ 2) :
    ∃ z : ℂ,
      evenProlateSignedPointwiseSource a n (evenProlateSignedValue_ne_zero ha n)
        =ᵐ[volume] fun y => z *
          evenProlateSignedPointwiseSource a m (evenProlateSignedValue_ne_zero ha m) y := by
  let hm := evenProlateSignedValue_ne_zero ha m
  let hn := evenProlateSignedValue_ne_zero ha n
  obtain ⟨z, hz⟩ :=
    evenProlateSignedUnitExtension_proportional_of_sq_eq ha hsq
  refine ⟨z, ?_⟩
  filter_upwards [Ioo_ae_eq_Icc] with y hy
  by_cases hycc : y ∈ Icc (-a) a
  · have hyoo : y ∈ Ioo (-a) a := hy.mpr hycc
    have ht : y / a ∈ Ioo (-1 : ℝ) 1 := by
      constructor
      · exact (lt_div_iff₀ ha).mpr (by linarith [hyoo.1])
      · exact (div_lt_iff₀ ha).mpr (by simpa using hyoo.2)
    have hzAt := hz (y / a)
    rw [evenProlateSignedUnitExtension_eq_source ha n hn ht,
      evenProlateSignedUnitExtension_eq_source ha m hm ht,
      mul_div_cancel₀ y ha.ne'] at hzAt
    exact hzAt
  · rw [evenProlateSignedPointwiseSource_eq_zero_of_not_mem_Icc
        (n := n) ha.le hn hycc,
      evenProlateSignedPointwiseSource_eq_zero_of_not_mem_Icc
        (n := m) ha.le hm hycc, mul_zero]

/-- Equal squared signed values force the original physical modes onto one complex line. -/
theorem evenProlateSignedMode_proportional_of_sq_eq
    {a : ℝ} (ha : 0 < a) {m n : ℕ}
    (hsq : evenProlateSignedValue a m ^ 2 =
      evenProlateSignedValue a n ^ 2) :
    ∃ z : ℂ, evenProlateSignedMode a n = z • evenProlateSignedMode a m := by
  let hm := evenProlateSignedValue_ne_zero ha m
  let hn := evenProlateSignedValue_ne_zero ha n
  obtain ⟨z, hsource⟩ :=
    evenProlateSignedPointwiseSource_ae_proportional_of_sq_eq ha hsq
  refine ⟨z, ?_⟩
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [ae_eq_evenProlateSignedPointwiseSource a ha.le n hn,
    ae_eq_evenProlateSignedPointwiseSource a ha.le m hm, hsource,
    Lp.coeFn_smul z
      (((evenProlateSignedMode a m : evenSubspace) : SoninL2))]
      with x hnSource hmSource hprop hsmul
  rw [← hnSource, hprop, hmSource]
  exact hsmul.symm

/-- The squared signed prolate spectrum is simple at every positive aperture. -/
theorem evenProlateSignedValue_sq_injective {a : ℝ} (ha : 0 < a) :
    Function.Injective (fun n => evenProlateSignedValue a n ^ 2) := by
  intro m n hsq
  by_contra hmn
  obtain ⟨z, hmode⟩ := evenProlateSignedMode_proportional_of_sq_eq ha hsq
  have horth := evenProlateSignedMode_orthogonal_of_ne a hmn
  rw [hmode] at horth
  have hz : z = 0 := by
    have hzOr : z = 0 ∨ evenProlateSignedMode a m = 0 := by
      simpa [inner_smul_right, inner_self_eq_norm_sq_to_K] using horth
    rcases hzOr with hz | hmzero
    · exact hz
    · have hmnorm := evenProlateSignedMode_norm_one ha m
      rw [hmzero, norm_zero] at hmnorm
      exact False.elim (zero_ne_one hmnorm)
  have hnzero : evenProlateSignedMode a n = 0 := by rw [hmode, hz, zero_smul]
  have hnnorm := evenProlateSignedMode_norm_one ha n
  rw [hnzero, norm_zero] at hnnorm
  exact zero_ne_one hnnorm

/-- Global cross-rung ordering of the actual squared finite-Fourier spectrum. -/
theorem evenProlateSignedValue_sq_strictAnti {a : ℝ} (ha : 0 < a) :
    StrictAnti (fun n => evenProlateSignedValue a n ^ 2) := by
  have hant : Antitone (fun n => evenProlateSignedValue a n ^ 2) := by
    intro m n hmn
    change evenProlateSignedValue a n ^ 2 ≤ evenProlateSignedValue a m ^ 2
    rw [← evenProlateConcentrationValue_eq_signedValue_sq a ha m,
      ← evenProlateConcentrationValue_eq_signedValue_sq a ha n]
    exact evenProlateConcentrationValue_antitone a hmn
  exact hant.strictAnti_of_injective (evenProlateSignedValue_sq_injective ha)

end RHTower
