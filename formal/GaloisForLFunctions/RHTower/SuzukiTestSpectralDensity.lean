import GaloisForLFunctions.RHTower.SuzukiWeilHilbert
import GaloisForLFunctions.HTGeometry.ExponentialSeriesUniqueness
import GaloisForLFunctions.RHTower.SuzukiCauchyGram

noncomputable section

/-!
# Density of the spectral values of test functions

The map sending a test function to its Fourier values on the spectrum has dense range in the
weighted sequence space.  Translating a test function multiplies its spectral values by the
characters `e^{-iγt}`, so a sequence orthogonal to every test function produces an absolutely
convergent exponential series vanishing for every real time; uniqueness of exponential-series
coefficients kills each term separately.  The modulated bump `e^{iγx} χ(x)` has spectral value the
mass of `χ` at the frequency `γ`, so no term can be discarded, and the sequence is zero.
-/

open MeasureTheory Set Complex Filter Topology
open GaloisForLFunctions.HTGeometry

namespace RHTower

/-- The spectral values of a test function, indexed by the support of the Xi divisor. -/
def suzukiTestSpectral (ψ : SuzukiTest) (ρ : XiDivisorSupport) : ℂ :=
  suzukiEntireFourier (ψ : ℝ → ℂ) (-xiSpectralPointSupport ρ)

theorem suzukiTestFourier_eq_spectral (ψ : SuzukiTest) (q : XiZeroCopy) :
    suzukiTestFourier ψ q = suzukiTestSpectral ψ q.1 := by
  rw [suzukiTestFourier, suzukiTestSpectral, xiSpectralPoint_eq_support]

/-- The translate of a test function. -/
def suzukiTestTranslate (t : ℝ) (ψ : SuzukiTest) : SuzukiTest :=
  ⟨fun x => (ψ : ℝ → ℂ) (x - t), by
    refine ⟨ψ.smooth.comp (contDiff_id.sub contDiff_const), ?_⟩
    exact ψ.hasCompactSupport.comp_homeomorph (Homeomorph.subRight t)⟩

@[simp] theorem coe_suzukiTestTranslate (t : ℝ) (ψ : SuzukiTest) :
    ((suzukiTestTranslate t ψ : SuzukiTest) : ℝ → ℂ) = fun x => (ψ : ℝ → ℂ) (x - t) := rfl

theorem suzukiTestSpectral_translate (hRH : RiemannHypothesis) (t : ℝ) (ψ : SuzukiTest)
    (ρ : XiDivisorSupport) :
    suzukiTestSpectral (suzukiTestTranslate t ψ) ρ
      = Complex.exp (I * (-((xiRealSpectralPointSupport ρ : ℝ)) : ℂ) * (t : ℂ))
        * suzukiTestSpectral ψ ρ := by
  have hreal : xiSpectralPointSupport ρ = ((xiRealSpectralPointSupport ρ : ℝ) : ℂ) :=
    (ofReal_xiRealSpectralPointSupport hRH ρ).symm
  set z : ℂ := -((xiRealSpectralPointSupport ρ : ℝ) : ℂ) with hz
  rw [suzukiTestSpectral, suzukiTestSpectral, hreal, ← hz, suzukiEntireFourier,
    suzukiEntireFourier]
  have hstep : (∫ x : ℝ, ((suzukiTestTranslate t ψ : SuzukiTest) : ℝ → ℂ) x
        * Complex.exp (I * z * (x : ℂ)))
      = ∫ y : ℝ, (ψ : ℝ → ℂ) y * Complex.exp (I * z * ((y + t : ℝ) : ℂ)) := by
    have hbase := MeasureTheory.integral_sub_right_eq_self (μ := (volume : Measure ℝ))
      (fun y : ℝ => (ψ : ℝ → ℂ) y * Complex.exp (I * z * ((y + t : ℝ) : ℂ))) t
    rw [← hbase]
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards with x
    show (ψ : ℝ → ℂ) (x - t) * Complex.exp (I * z * (x : ℂ))
      = (ψ : ℝ → ℂ) (x - t) * Complex.exp (I * z * ((x - t + t : ℝ) : ℂ))
    congr 2
    push_cast
    ring
  rw [hstep, ← MeasureTheory.integral_const_mul]
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards with y
  rw [show ((y + t : ℝ) : ℂ) = (y : ℂ) + (t : ℂ) by push_cast; ring]
  rw [show I * z * ((y : ℂ) + (t : ℂ)) = I * z * (t : ℂ) + I * z * (y : ℂ) by ring,
    Complex.exp_add]
  ring

/-! ## A test function that does not vanish at a prescribed frequency -/

/-- A fixed smooth bump on the line. -/
def suzukiBump : ContDiffBump (0 : ℝ) := ⟨1, 2, one_pos, one_lt_two⟩

/-- The modulated bump: a test function whose Fourier transform at `-γ` is the mass of the
bump. -/
def suzukiModulatedBump (γ : ℝ) : SuzukiTest :=
  ⟨fun x => Complex.exp (I * (γ : ℂ) * (x : ℂ)) * ((suzukiBump x : ℝ) : ℂ), by
    constructor
    · refine ContDiff.mul ?_ ?_
      · refine Complex.contDiff_exp.comp ?_
        have hb : ContDiff ℝ (⊤ : ℕ∞) (fun x : ℝ => ((x : ℝ) : ℂ)) :=
          Complex.ofRealCLM.contDiff
        exact (contDiff_const (c := I * (γ : ℂ))).mul hb
      · exact Complex.ofRealCLM.contDiff.comp suzukiBump.contDiff
    · refine HasCompactSupport.mul_left ?_
      exact suzukiBump.hasCompactSupport.comp_left (g := fun r : ℝ => ((r : ℝ) : ℂ)) (by simp)⟩

theorem suzukiEntireFourier_suzukiModulatedBump (γ : ℝ) :
    suzukiEntireFourier ((suzukiModulatedBump γ : SuzukiTest) : ℝ → ℂ)
        (-((γ : ℝ) : ℂ))
      = ((∫ x : ℝ, (suzukiBump x : ℝ) : ℝ) : ℂ) := by
  rw [suzukiEntireFourier]
  have hfun : ∀ x : ℝ, ((suzukiModulatedBump γ : SuzukiTest) : ℝ → ℂ) x
      * Complex.exp (I * (-((γ : ℝ) : ℂ)) * (x : ℂ)) = (((suzukiBump x : ℝ)) : ℂ) := by
    intro x
    show Complex.exp (I * (γ : ℂ) * (x : ℂ)) * ((suzukiBump x : ℝ) : ℂ)
        * Complex.exp (I * (-((γ : ℝ) : ℂ)) * (x : ℂ)) = (((suzukiBump x : ℝ)) : ℂ)
    rw [show Complex.exp (I * (γ : ℂ) * (x : ℂ)) * ((suzukiBump x : ℝ) : ℂ)
        * Complex.exp (I * (-((γ : ℝ) : ℂ)) * (x : ℂ))
      = (((suzukiBump x : ℝ)) : ℂ) * (Complex.exp (I * (γ : ℂ) * (x : ℂ))
        * Complex.exp (I * (-((γ : ℝ) : ℂ)) * (x : ℂ))) by ring]
    rw [← Complex.exp_add]
    rw [show I * (γ : ℂ) * (x : ℂ) + I * (-((γ : ℝ) : ℂ)) * (x : ℂ) = 0 by ring]
    rw [Complex.exp_zero, mul_one]
  rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hfun)]
  exact integral_ofReal

theorem suzukiTestSpectral_suzukiModulatedBump_ne_zero (hRH : RiemannHypothesis)
    (ρ : XiDivisorSupport) :
    suzukiTestSpectral (suzukiModulatedBump (xiRealSpectralPointSupport ρ)) ρ ≠ 0 := by
  have hreal : xiSpectralPointSupport ρ = ((xiRealSpectralPointSupport ρ : ℝ) : ℂ) :=
    (ofReal_xiRealSpectralPointSupport hRH ρ).symm
  rw [suzukiTestSpectral, hreal, suzukiEntireFourier_suzukiModulatedBump]
  simp only [ne_eq, Complex.ofReal_eq_zero]
  exact ne_of_gt suzukiBump.integral_pos


/-! ## The spectral values of the test space are dense -/

theorem hasSum_mult_normSq_suzukiTestSpectral (hRH : RiemannHypothesis) (ψ : SuzukiTest) :
    HasSum (fun ρ : XiDivisorSupport =>
      (xiSupportMult ρ : ℝ) * ‖suzukiTestSpectral ψ ρ‖ ^ 2) ((suzukiWeilInner ψ ψ).re) := by
  have hbase : HasSum (fun q : XiZeroCopy => ‖suzukiTestSpectral ψ q.1‖ ^ 2)
      ((suzukiWeilInner ψ ψ).re) := by
    refine (hasSum_normSq_suzukiTestFourier hRH ψ).congr_fun ?_
    intro q
    rw [suzukiTestFourier_eq_spectral]
  refine hbase.sigma ?_
  intro ρ
  have hfin := hasSum_fintype (fun _i : Fin (xiSupportMult ρ) =>
    ‖suzukiTestSpectral ψ ρ‖ ^ 2)
  have hsum : (∑ _i : Fin (xiSupportMult ρ), ‖suzukiTestSpectral ψ ρ‖ ^ 2)
      = (xiSupportMult ρ : ℝ) * ‖suzukiTestSpectral ψ ρ‖ ^ 2 := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [hsum] at hfin
  exact hfin

theorem summable_mult_normSq_suzukiTestSpectral (hRH : RiemannHypothesis) (ψ : SuzukiTest) :
    Summable (fun ρ : XiDivisorSupport =>
      (xiSupportMult ρ : ℝ) * ‖suzukiTestSpectral ψ ρ‖ ^ 2) :=
  (hasSum_mult_normSq_suzukiTestSpectral hRH ψ).summable

/-- **Density of the spectral values of test functions.**  A weighted square-summable sequence on
the spectrum orthogonal to every test function is zero.  Translating the test function multiplies
its spectral values by the characters `e^{-iγt}`, so uniqueness of exponential-series coefficients
kills each term separately, and the modulated bump has a nonzero value at any prescribed
frequency. -/
theorem eq_zero_of_orthogonal_suzukiTestSpectral (hRH : RiemannHypothesis)
    {a : XiDivisorSupport → ℂ}
    (ha : Summable (fun ρ : XiDivisorSupport => (xiSupportMult ρ : ℝ) * ‖a ρ‖ ^ 2))
    (h : ∀ ψ : SuzukiTest,
      (∑' ρ : XiDivisorSupport,
        ((xiSupportMult ρ : ℝ) : ℂ) * (starRingEnd ℂ) (a ρ) * suzukiTestSpectral ψ ρ) = 0) :
    ∀ ρ, a ρ = 0 := by
  have hinj : Function.Injective
      (fun ρ : XiDivisorSupport => -(xiRealSpectralPointSupport ρ)) := by
    intro ρ σ hρσ
    exact xiRealSpectralPointSupport_injective hRH (neg_injective hρσ)
  intro ρ₀
  set ψ : SuzukiTest := suzukiModulatedBump (xiRealSpectralPointSupport ρ₀) with hψ
  set c : XiDivisorSupport → ℂ := fun ρ =>
    ((xiSupportMult ρ : ℝ) : ℂ) * (starRingEnd ℂ) (a ρ) * suzukiTestSpectral ψ ρ with hc
  have hcnorm : ∀ ρ, ‖c ρ‖ ≤ ((xiSupportMult ρ : ℝ) * ‖a ρ‖ ^ 2
      + (xiSupportMult ρ : ℝ) * ‖suzukiTestSpectral ψ ρ‖ ^ 2) / 2 := by
    intro ρ
    have hm : (0 : ℝ) ≤ (xiSupportMult ρ : ℝ) := Nat.cast_nonneg _
    rw [hc, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hm, RCLike.norm_conj]
    nlinarith [sq_nonneg (‖a ρ‖ - ‖suzukiTestSpectral ψ ρ‖), norm_nonneg (a ρ),
      norm_nonneg (suzukiTestSpectral ψ ρ)]
  have hcsum : Summable (fun ρ => ‖c ρ‖) := by
    refine Summable.of_nonneg_of_le (fun ρ => norm_nonneg _) hcnorm ?_
    exact ((ha.add (summable_mult_normSq_suzukiTestSpectral hRH ψ)).div_const 2)
  have hzero : ∀ t : ℝ, (∑' ρ : XiDivisorSupport,
      c ρ * Complex.exp (I * ((-(xiRealSpectralPointSupport ρ) : ℝ) : ℂ) * (t : ℂ))) = 0 := by
    intro t
    have hval := h (suzukiTestTranslate t ψ)
    rw [← hval]
    refine tsum_congr fun ρ => ?_
    rw [suzukiTestSpectral_translate hRH t ψ ρ, hc]
    push_cast
    ring
  have hczero := fun ρ => GaloisForLFunctions.HTGeometry.coeff_eq_zero_of_tsum_cis_eq_zero
    hinj hcsum hzero ρ
  have hne : suzukiTestSpectral ψ ρ₀ ≠ 0 :=
    suzukiTestSpectral_suzukiModulatedBump_ne_zero hRH ρ₀
  have hmne : (((xiSupportMult ρ₀ : ℝ)) : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero, Nat.cast_eq_zero]
    exact ne_of_gt (xiSupportMult_pos ρ₀)
  have h0 := hczero ρ₀
  rw [hc] at h0
  have hconj : (starRingEnd ℂ) (a ρ₀) = 0 := by
    rcases mul_eq_zero.mp h0 with h1 | h1
    · exact (mul_eq_zero.mp h1).resolve_left hmne
    · exact absurd h1 hne
  have := congrArg (starRingEnd ℂ) hconj
  rwa [Complex.conj_conj, map_zero] at this


end RHTower
