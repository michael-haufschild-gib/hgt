import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.OriginDegreeDoesNotDescendThroughPoissonBoundaries
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FlowInvariantMeyerMajorantsForceCriticality
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.SmoothFiniteReadingKernels

/-!
# Invariant origin mass does not control the original Weil trace

The positive origin sharp-square degree is invariant under centered flow.
On compact smooth sources it is exactly the ordinary source mass. Unit-mass
Weil energy is unbounded at every positive aperture, so no finite nonlinear
function of origin mass can majorize the original mixed trace.
-/

noncomputable section
open Complex MeasureTheory Filter Set RHTower Zeta23
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri

/-- The positive square mass read by origin evaluation of the actual source product. -/
def meyerOriginSquareMass (g : DeningerMeyerStrongLogTarget) : ℝ :=
  (meyerOriginDegree (deningerMeyerSourceConvolution g (deningerMeyerSourceSharp g))).re

theorem meyerOriginSquareMass_eq_integral (g : DeningerMeyerStrongLogTarget) :
    meyerOriginSquareMass g = ∫ t : ℝ, Real.exp t * Complex.normSq (g.val t) := by
  rw [meyerOriginSquareMass, meyerOriginDegree_sharp_square, Complex.ofReal_re]

theorem meyerOriginSquareMass_nonneg (g : DeningerMeyerStrongLogTarget) :
    0 ≤ meyerOriginSquareMass g := by
  rw [meyerOriginSquareMass_eq_integral]
  exact integral_nonneg fun t => mul_nonneg (Real.exp_pos t).le (Complex.normSq_nonneg _)

theorem meyerOriginSquareMass_eq_zero_iff (g : DeningerMeyerStrongLogTarget) :
    meyerOriginSquareMass g = 0 ↔ g = 0 := meyerOriginDegree_sharp_square_eq_zero_iff g

/-- Strict source positivity and centered-flow invariance hold together without RH. -/
theorem meyerOriginSquareMass_centered_flow (c : ℝ) (g : DeningerMeyerStrongLogTarget) :
    meyerOriginSquareMass (deningerMeyerStrongLogCenteredFlow c g) = meyerOriginSquareMass g := by
  rw [meyerOriginSquareMass, meyerSourceConvolution_centered_flow_sharp]
  rfl

/-- The compact Meyer embedding preserves exactly the original real source mass. -/
theorem meyerOriginSquareMass_compact_real {r : ℝ} (k : SuzukiSmoothCompactTest r)
    (f : ℝ → ℝ) (hk : (k : ℝ → ℂ) = cx f) :
    meyerOriginSquareMass (deningerWeilConvolutionSource k) = ∫ t : ℝ, f t ^ 2 := by
  rw [meyerOriginSquareMass_eq_integral]
  apply integral_congr_ae
  filter_upwards [] with t
  have he : Complex.exp (-(t : ℂ) / 2) = ((Real.exp (-t / 2) : ℝ) : ℂ) := by
    rw [Complex.ofReal_exp]
    congr 1
    push_cast
    ring
  have hexp : Real.exp t * Real.exp (-t / 2) ^ 2 = 1 := by
    rw [pow_two, ← Real.exp_add, ← Real.exp_add,
      show t + (-t / 2 + -t / 2) = 0 by ring, Real.exp_zero]
  change Real.exp t * Complex.normSq (Complex.exp (-(t : ℂ) / 2) * k t) = _
  rw [he, show k t = (f t : ℂ) from congrFun hk t,
    Complex.normSq_mul, Complex.normSq_ofReal, Complex.normSq_ofReal]
  calc
    _ = (Real.exp t * Real.exp (-t / 2) ^ 2) * f t ^ 2 := by ring
    _ = _ := by rw [hexp, one_mul]

/-- Every positive aperture contains unit-origin-mass smooth sources of arbitrarily large trace. -/
theorem exists_meyer_compact_unit_originMass_trace_gt {r : ℝ} (hr : 0 < r) (M : ℝ) :
    ∃ k : SuzukiSmoothCompactTest r,
      meyerOriginSquareMass (deningerWeilConvolutionSource k) = 1 ∧
      M < meyerSourceTrace (deningerWeilConvolutionSource k) (deningerWeilConvolutionSource k) := by
  obtain ⟨f, hfd, hm, _, hW⟩ := exists_smooth_realTestAt_unit_mass_in_ker_weilPair_gt hr M
    (0 : realTestsAt r →ₗ[ℝ] ℝ)
  let k : SuzukiSmoothCompactTest r :=
    { toFun := cx f.1.1
      smooth := Complex.ofRealCLM.contDiff.comp hfd
      support_subset := by
        intro t ht
        apply f.2
        apply subset_tsupport f.1.1
        intro hz
        apply ht
        change (f.1.1 t : ℂ) = 0
        rw [hz, Complex.ofReal_zero] }
  have ht : meyerSourceTrace (deningerWeilConvolutionSource k)
      (deningerWeilConvolutionSource k) = weilPair f.1.1 f.1.1 := by
    rw [meyerSourceTrace, deningerWeilConvolutionSource_pair_trace]
    change (zetaZeroConfig.W (cx f.1.1) (cx f.1.1)).re = _
    rw [zeta_W_eq_weilFullFunctional_mixed (cx_contDiff f.1.2.1) (cx_hasCompactSupport f.1.2.2)
      (cx_contDiff f.1.2.1) (cx_hasCompactSupport f.1.2.2)]
    rfl
  refine ⟨k, ?_, ?_⟩
  · rw [meyerOriginSquareMass_compact_real k f.1.1 rfl]
    exact hm
  · rw [ht]
    exact hW

/-- Even arbitrary nonlinear postprocessing of origin mass cannot bound the original mixed trace. -/
theorem meyerOriginMass_function_not_trace_majorant (F : ℝ → ℝ) :
    ¬ ∀ g h : DeningerMeyerStrongLogTarget,
      meyerSourceTrace g h ^ 2 ≤ F (meyerOriginSquareMass g) * F (meyerOriginSquareMass h) := by
  intro hb
  obtain ⟨k, hm, hW⟩ := exists_meyer_compact_unit_originMass_trace_gt
    (by norm_num : (0 : ℝ) < 1) (|F 1| + 1)
  have h := hb (deningerWeilConvolutionSource k) (deningerWeilConvolutionSource k)
  rw [hm] at h
  nlinarith only [h, hW, abs_nonneg (F 1), sq_abs (F 1)]

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
