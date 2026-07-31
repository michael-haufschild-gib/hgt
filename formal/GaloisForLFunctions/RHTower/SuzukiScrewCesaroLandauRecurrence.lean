import GaloisForLFunctions.RHTower.XiWaveTraceCofinalQuadrature
import GaloisForLFunctions.RHTower.XiWeilPolarization
import GaloisForLFunctions.RHTower.SuzukiScrewCesaroCurvatureRecurrence

/-!
# Cofinal sign change of the curvature-centered Suzuki screw primitive

Counted with analytic multiplicity, the Xi zero ordinates again form an admissible wave
spectrum. Its constant-weight wave trace is exactly the curvature-centered primitive
`h(A) = ∑ sin (gamma A) / gamma ^ 3` of Suzuki's screw profile.

The Landau recurrence therefore applies: `h` is neither eventually nonnegative nor eventually
nonpositive, so the initial screw average crosses the central Xi curvature strictly in both
directions at arbitrarily large apertures.
-/

open Complex Filter MeasureTheory Set Topology
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

/-- The Xi zero ordinates with analytic multiplicity as an admissible wave spectrum. -/
def xiCopyWaveSpectrum : WaveSpectrum XiZeroCopy where
  gamma := xiSpectralPoint
  invol := xiZeroCopyLineConjEquiv
  gamma_invol := xiSpectralPoint_lineConj
  lower := xiHeightLowerBound
  lower_pos := xiHeightLowerBound_pos
  lower_le := fun q => by
    rw [xiSpectralPoint_eq_support]
    exact xiWaveSpectrum.lower_le q.1
  width := 1 / 2
  width_nonneg := by norm_num
  im_le := fun q => by
    rw [xiSpectralPoint_eq_support]
    exact xiWaveSpectrum.im_le q.1
  summable_inv_sq := by
    refine xiSpectralPoint_inv_sq_summable.congr (fun q => ?_)
    rw [one_div, ← inv_pow]

theorem xiCopyWaveSpectrum_locallyFinite : xiCopyWaveSpectrum.IsLocallyFiniteSpectrum := by
  intro R
  have hbase : {ρ : XiDivisorSupport | ‖xiSpectralPointSupport ρ‖ ≤ R}.Finite :=
    xiWaveSpectrum_locallyFinite R
  have hcover : {q : XiZeroCopy | ‖xiCopyWaveSpectrum.gamma q‖ ≤ R} ⊆
      ⋃ ρ ∈ {ρ : XiDivisorSupport | ‖xiSpectralPointSupport ρ‖ ≤ R},
        (Set.range (Sigma.mk ρ) : Set XiZeroCopy) := by
    intro q hq
    refine Set.mem_biUnion (show q.1 ∈ {ρ : XiDivisorSupport |
      ‖xiSpectralPointSupport ρ‖ ≤ R} from hq) ?_
    exact ⟨q.2, rfl⟩
  exact Set.Finite.subset (hbase.biUnion (fun ρ _ => Set.finite_range _)) hcover

theorem xiCopyWaveSpectrum_re_ne_zero (q : XiZeroCopy) :
    (xiCopyWaveSpectrum.gamma q).re ≠ 0 := by
  show (xiSpectralPoint q).re ≠ 0
  rw [xiSpectralPoint_eq_support]
  exact xiWaveSpectrum_re_ne_zero q.1

theorem xiCopyWaveSpectrum_squares_infinite :
    (Set.range fun q : XiZeroCopy => xiCopyWaveSpectrum.gamma q ^ 2).Infinite := by
  refine xiWaveSpectrum_squares_infinite.mono ?_
  rintro _ ⟨ρ, rfl⟩
  have hmult : 0 < Int.toNat ((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ)) := by
    have := xi_divisor_pos_on_support ρ
    omega
  exact ⟨⟨ρ, ⟨0, hmult⟩⟩, rfl⟩

/-- The constant-weight wave trace of the multiplicity divisor is the curvature-centered
screw primitive. -/
theorem xiCopyWaveSpectrum_waveTrace_one (A : ℝ) :
    xiCopyWaveSpectrum.waveTrace 1 A =
      ∑' q : XiZeroCopy,
        Complex.sin (xiSpectralPoint q * A) / xiSpectralPoint q ^ 3 := by
  refine tsum_congr fun q => ?_
  show Complex.sin (xiSpectralPoint q * A) *
      Polynomial.aeval ((xiSpectralPoint q ^ 2)⁻¹) (1 : Polynomial ℝ) /
      xiSpectralPoint q ^ 3 = _
  simp

/-- **Cofinal two-sided sign change of the curvature-centered screw primitive.** For every
aperture bound there are strictly larger apertures at which the primitive is negative and at
which it is positive. No Riemann hypothesis, simplicity, or rational-independence premise is
used. -/
theorem xiScrewPrimitive_cofinal_sign_change (A0 : ℝ) :
    (∃ A, A0 < A ∧ xiCopyWaveSpectrum.realWaveTrace 1 A < 0) ∧
      ∃ A, A0 < A ∧ 0 < xiCopyWaveSpectrum.realWaveTrace 1 A :=
  ⟨cofinalWaveSignEscape xiCopyWaveSpectrum xiCopyWaveSpectrum_locallyFinite
      xiCopyWaveSpectrum_re_ne_zero xiCopyWaveSpectrum_squares_infinite 1 one_ne_zero A0,
    exists_pos_realWaveTrace xiCopyWaveSpectrum xiCopyWaveSpectrum_locallyFinite
      xiCopyWaveSpectrum_re_ne_zero xiCopyWaveSpectrum_squares_infinite one_ne_zero A0⟩

/-! ## The screw profile as a constant-weight wave trace -/

/-- Cosine coordinate of one Xi zero copy. -/
def xiScrewCosTerm (t : ℝ) (q : XiZeroCopy) : ℂ :=
  Complex.cos (xiSpectralPoint q * t) / xiSpectralPoint q ^ 2

/-- The centered curvature constant of the Xi screw divisor. -/
def xiScrewCurvature : ℝ := -(∑' q : XiZeroCopy, (xiSpectralPoint q ^ 2)⁻¹).re

theorem summable_xiSpectralPoint_invSq :
    Summable (fun q : XiZeroCopy => (xiSpectralPoint q ^ 2)⁻¹) := by
  refine Summable.of_norm (xiSpectralPoint_inv_sq_summable.congr (fun q => ?_))
  rw [norm_inv, norm_pow, one_div]

theorem norm_xiScrewCosTerm_le (t : ℝ) (q : XiZeroCopy) :
    ‖xiScrewCosTerm t q‖ ≤ Real.exp (|t| / 2) * (1 / ‖xiSpectralPoint q‖ ^ 2) := by
  rw [xiScrewCosTerm, norm_div, norm_pow]
  have hg : 0 < ‖xiSpectralPoint q‖ := lt_of_lt_of_le xiCopyWaveSpectrum.lower_pos
    (xiCopyWaveSpectrum.lower_le q)
  have hcos : ‖Complex.cos (xiSpectralPoint q * t)‖ ≤ Real.exp (|t| / 2) := by
    refine le_trans (norm_ccos_le_exp_abs_im _) (Real.exp_le_exp.mpr ?_)
    have him : (xiSpectralPoint q * (t : ℂ)).im = (xiSpectralPoint q).im * t := by
      simp [Complex.mul_im]
    rw [him, abs_mul]
    have hw : |(xiSpectralPoint q).im| ≤ 1 / 2 := xiCopyWaveSpectrum.im_le q
    nlinarith [abs_nonneg t, abs_nonneg (xiSpectralPoint q).im]
  rw [div_le_iff₀ (by positivity)]
  calc ‖Complex.cos (xiSpectralPoint q * t)‖
      ≤ Real.exp (|t| / 2) := hcos
    _ = Real.exp (|t| / 2) * (1 / ‖xiSpectralPoint q‖ ^ 2) * ‖xiSpectralPoint q‖ ^ 2 := by
        field_simp

theorem summable_xiScrewCosTerm (t : ℝ) : Summable (xiScrewCosTerm t) :=
  Summable.of_norm_bounded (xiSpectralPoint_inv_sq_summable.mul_left _)
    (fun q => norm_xiScrewCosTerm_le t q)

theorem xiScrewDivisorTerm_eq (t : ℝ) (q : XiZeroCopy) :
    xiScrewDivisorTerm t q = (xiSpectralPoint q ^ 2)⁻¹ - xiScrewCosTerm t q := by
  have hne : xiSpectralPoint q ≠ 0 := xiSpectralPoint_ne_zero q
  have hcosh : Complex.cosh ((t : ℂ) * (Complex.I * xiSpectralPoint q)) =
      Complex.cos (xiSpectralPoint q * (t : ℂ)) := by
    rw [show (t : ℂ) * (Complex.I * xiSpectralPoint q) =
      (xiSpectralPoint q * (t : ℂ)) * Complex.I by ring]
    exact Complex.cosh_mul_I _
  have hsq : (Complex.I * xiSpectralPoint q) ^ 2 = -(xiSpectralPoint q ^ 2) := by
    rw [mul_pow, Complex.I_sq]
    ring
  rw [xiScrewDivisorTerm, hcosh, hsq, xiScrewCosTerm]
  field_simp
  ring

theorem xiScrewDivisor_eq (t : ℝ) :
    xiScrewDivisor t =
      (∑' q : XiZeroCopy, (xiSpectralPoint q ^ 2)⁻¹) - ∑' q : XiZeroCopy, xiScrewCosTerm t q := by
  rw [xiScrewDivisor]
  rw [show (fun q : XiZeroCopy => xiScrewDivisorTerm t q) =
    fun q : XiZeroCopy => (xiSpectralPoint q ^ 2)⁻¹ - xiScrewCosTerm t q from
      funext (xiScrewDivisorTerm_eq t)]
  exact Summable.tsum_sub summable_xiSpectralPoint_invSq (summable_xiScrewCosTerm t)

/-- The curvature-centered screw profile is the real part of the cosine divisor sum. -/
theorem xiSuzukiScrewProfile_sub_curvature (t : ℝ) :
    xiSuzukiScrewProfile t - xiScrewCurvature =
      (∑' q : XiZeroCopy, xiScrewCosTerm t q).re := by
  rw [xiSuzukiScrewProfile, xiScrewDivisor_eq, xiScrewCurvature, Complex.sub_re]
  ring

/-! ## Termwise integration to the wave trace -/

theorem continuous_xiScrewCosTerm (q : XiZeroCopy) :
    Continuous (fun t : ℝ => xiScrewCosTerm t q) := by
  unfold xiScrewCosTerm
  fun_prop

theorem continuous_xiScrewCosSum :
    Continuous (fun t : ℝ => ∑' q : XiZeroCopy, xiScrewCosTerm t q) := by
  rw [continuous_iff_continuousAt]
  intro t0
  have h1 : -(|t0| + 1) < t0 := by have := neg_abs_le t0; linarith
  have h2 : t0 < |t0| + 1 := by have := le_abs_self t0; linarith
  refine ContinuousOn.continuousAt ?_ (Icc_mem_nhds h1 h2)
  refine continuousOn_tsum
    (u := fun q : XiZeroCopy =>
      Real.exp ((|t0| + 1) / 2) * (1 / ‖xiSpectralPoint q‖ ^ 2))
    (fun q => (continuous_xiScrewCosTerm q).continuousOn)
    (xiSpectralPoint_inv_sq_summable.mul_left _) (fun q t ht => ?_)
  refine le_trans (norm_xiScrewCosTerm_le t q) ?_
  have habs : |t| ≤ |t0| + 1 := abs_le.mpr ⟨ht.1, ht.2⟩
  exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by linarith)) (by positivity)

theorem continuous_xiSuzukiScrewProfile : Continuous xiSuzukiScrewProfile := by
  have hrepr : xiSuzukiScrewProfile =
      fun t : ℝ => xiScrewCurvature + (∑' q : XiZeroCopy, xiScrewCosTerm t q).re := by
    funext t
    have h := xiSuzukiScrewProfile_sub_curvature t
    linarith
  rw [hrepr]
  exact continuous_const.add (Complex.continuous_re.comp continuous_xiScrewCosSum)

theorem integral_xiScrewCosTerm (A : ℝ) (q : XiZeroCopy) :
    (∫ t in (0 : ℝ)..A, xiScrewCosTerm t q) =
      Complex.sin (xiSpectralPoint q * A) / xiSpectralPoint q ^ 3 := by
  have hne : xiSpectralPoint q ≠ 0 := xiSpectralPoint_ne_zero q
  have hderiv : ∀ t : ℝ, HasDerivAt
      (fun u : ℝ => Complex.sin (xiSpectralPoint q * (u : ℂ)) / xiSpectralPoint q ^ 3)
      (xiScrewCosTerm t q) t := by
    intro t
    have h1 : HasDerivAt (fun u : ℝ => (xiSpectralPoint q * (u : ℂ))) (xiSpectralPoint q) t := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := t)).const_mul (xiSpectralPoint q)
    have h2 : HasDerivAt (fun u : ℝ => Complex.sin (xiSpectralPoint q * (u : ℂ)))
        (xiSpectralPoint q * Complex.cos (xiSpectralPoint q * (t : ℂ))) t := by
      have h := (Complex.hasDerivAt_sin (xiSpectralPoint q * (t : ℂ))).scomp t h1
      simpa [Function.comp_def, mul_comm] using h
    have h3 := h2.div_const (xiSpectralPoint q ^ 3)
    have hval : xiScrewCosTerm t q =
        xiSpectralPoint q * Complex.cos (xiSpectralPoint q * (t : ℂ)) /
          xiSpectralPoint q ^ 3 := by
      show Complex.cos (xiSpectralPoint q * (t : ℂ)) / xiSpectralPoint q ^ 2 = _
      field_simp
    rw [hval]
    exact h3
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hderiv t)
    ((continuous_xiScrewCosTerm q).intervalIntegrable 0 A)]
  simp

theorem summable_integral_norm_xiScrewCosTerm {A : ℝ} (hA : 0 ≤ A) :
    Summable fun q : XiZeroCopy => ∫ t in Ioc (0 : ℝ) A, ‖xiScrewCosTerm t q‖ := by
  refine Summable.of_nonneg_of_le (fun q => integral_nonneg fun t => norm_nonneg _)
    (fun q => ?_) (xiSpectralPoint_inv_sq_summable.mul_left (A * Real.exp (A / 2)))
  have hbnd : ∀ t ∈ Ioc (0 : ℝ) A,
      ‖xiScrewCosTerm t q‖ ≤ Real.exp (A / 2) * (1 / ‖xiSpectralPoint q‖ ^ 2) := by
    intro t ht
    refine le_trans (norm_xiScrewCosTerm_le t q) ?_
    have habs : |t| ≤ A := by rw [abs_of_pos ht.1]; exact ht.2
    exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by linarith)) (by positivity)
  have hint : IntegrableOn (fun t : ℝ => ‖xiScrewCosTerm t q‖) (Ioc (0 : ℝ) A) :=
    ((continuous_xiScrewCosTerm q).norm).integrableOn_Ioc
  have hconstint : IntegrableOn
      (fun _ : ℝ => Real.exp (A / 2) * (1 / ‖xiSpectralPoint q‖ ^ 2)) (Ioc (0 : ℝ) A) :=
    (continuous_const).integrableOn_Ioc
  refine le_trans (setIntegral_mono_on hint hconstint measurableSet_Ioc hbnd) (le_of_eq ?_)
  rw [setIntegral_const, smul_eq_mul]
  have hvol : volume.real (Ioc (0 : ℝ) A) = A := by
    rw [MeasureTheory.measureReal_def, Real.volume_Ioc, ENNReal.toReal_ofReal (by linarith)]
    ring
  rw [hvol]
  ring

/-- **Curvature-centered primitive is the constant-weight wave trace.** -/
theorem suzukiCurvatureCenteredPrimitive_eq_realWaveTrace {A : ℝ} (hA : 0 ≤ A) :
    suzukiCurvatureCenteredPrimitive xiSuzukiScrewProfile xiScrewCurvature A =
      xiCopyWaveSpectrum.realWaveTrace 1 A := by
  have hsum := hasSum_integral_of_summable_integral_norm
    (F := fun q : XiZeroCopy => fun t : ℝ => xiScrewCosTerm t q)
    (μ := volume.restrict (Ioc (0 : ℝ) A))
    (fun q => (continuous_xiScrewCosTerm q).integrableOn_Ioc)
    (summable_integral_norm_xiScrewCosTerm hA)
  have hterm : ∀ q : XiZeroCopy, (∫ t in Ioc (0 : ℝ) A, xiScrewCosTerm t q) =
      Complex.sin (xiSpectralPoint q * A) / xiSpectralPoint q ^ 3 := by
    intro q
    rw [← intervalIntegral.integral_of_le hA]
    exact integral_xiScrewCosTerm A q
  simp_rw [hterm] at hsum
  have hcplx : (∫ t in Ioc (0 : ℝ) A, ∑' q : XiZeroCopy, xiScrewCosTerm t q) =
      ∑' q : XiZeroCopy, Complex.sin (xiSpectralPoint q * A) / xiSpectralPoint q ^ 3 :=
    hsum.tsum_eq.symm
  have hintegrable : IntegrableOn
      (fun t : ℝ => ∑' q : XiZeroCopy, xiScrewCosTerm t q) (Ioc (0 : ℝ) A) :=
    continuous_xiScrewCosSum.integrableOn_Ioc
  rw [suzukiCurvatureCenteredPrimitive]
  simp_rw [xiSuzukiScrewProfile_sub_curvature]
  rw [intervalIntegral.integral_of_le hA]
  have hre : (∫ t in Ioc (0 : ℝ) A, (∑' q : XiZeroCopy, xiScrewCosTerm t q).re) =
      (∫ t in Ioc (0 : ℝ) A, ∑' q : XiZeroCopy, xiScrewCosTerm t q).re := by
    simpa using integral_re hintegrable
  rw [hre, hcplx, WaveSpectrum.realWaveTrace, xiCopyWaveSpectrum_waveTrace_one]

/-- **Cofinal two-sided crossing of the Suzuki screw Cesaro average.** The initial screw average
crosses the central Xi curvature strictly in both directions at arbitrarily large apertures. No
Riemann hypothesis, simplicity, or rational-independence premise is used. -/
theorem xiScrewCesaroMean_cofinallyCrosses :
    CofinallyCrosses (suzukiScrewCesaroMean xiSuzukiScrewProfile) xiScrewCurvature := by
  refine (cofinallyCrosses_suzukiScrewCesaroMean_iff_centeredPrimitive
    (fun A => continuous_xiSuzukiScrewProfile.intervalIntegrable 0 A)).mpr ⟨?_, ?_⟩
  · intro A0
    obtain ⟨A, hA, hneg⟩ := (xiScrewPrimitive_cofinal_sign_change (max A0 0)).1
    refine ⟨A, hA, ?_⟩
    rw [suzukiCurvatureCenteredPrimitive_eq_realWaveTrace
      (le_of_lt (lt_of_le_of_lt (le_max_right A0 0) hA))]
    exact hneg
  · intro A0
    obtain ⟨A, hA, hpos⟩ := (xiScrewPrimitive_cofinal_sign_change (max A0 0)).2
    refine ⟨A, hA, ?_⟩
    rw [suzukiCurvatureCenteredPrimitive_eq_realWaveTrace
      (le_of_lt (lt_of_le_of_lt (le_max_right A0 0) hA))]
    exact hpos

end

end RHTower
