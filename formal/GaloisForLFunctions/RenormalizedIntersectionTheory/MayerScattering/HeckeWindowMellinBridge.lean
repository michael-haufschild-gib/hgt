import GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScattering.LewisHeckeEisensteinEigenvalue
import GaloisForLFunctions.WindowTowerOfSpecZ.TheSymmetriesOfTheTower
import GaloisForLFunctions.CohomologyOfWindowsOfSpecZ.WindowNaiveHeights
import GaloisForLFunctions.ArithmeticPolarization.HeckeInvarianceOfTheCollidedPolarizationIsRH
import GaloisForLFunctions.RHTower.WeilMarkovOddSectorTrivialZeroSquares

/-!
# The Mellin correspondence from window shifts to source Hecke periods

The actual four-branch Hecke operator, minus identity, realizes the untruncated adjoint shift
into the next window. This correspondence scales the complete Weil form by two. The two
window embeddings are exchanged by Serre reflection; neither individual embedding commutes
with reflection at a fixed stage. Evaluation of the normalized source period at `1` recovers
the Mellin coefficient and hence the complete explicit formula.
-/

noncomputable section
open Complex Set MeasureTheory Zeta23
open scoped ComplexConjugate
open GaloisForLFunctions
open CohomologyOfWindowsOfSpecZ WindowTowerOfSpecZ SpacingScaleHarmonicAnalysis
open ArithmeticPolarization RenormalizedIntersectionTheory

namespace GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScattering

/-- The first-prime adjoint shift, without truncation, into the longer window. -/
def heckeWindowPull (H : ℝ → ℝ) : ℝ → ℝ := fun u => Real.sqrt 2 * H (u + Real.log 2)

/-- The companion inclusion, with the same degree normalization. -/
def heckeWindowPush (H : ℝ → ℝ) : ℝ → ℝ := fun u => Real.sqrt 2 * H u

theorem heckeWindowPull_mem {A : ℝ} {H : ℝ → ℝ} (hH : IsWindowTest A H) :
    IsWindowTest (A + Real.log 2) (heckeWindowPull H) := by
  refine ⟨contDiff_const.mul (hH.contDiff.comp (contDiff_id.add contDiff_const)), ?_⟩
  intro u hu
  change Real.sqrt 2 * H (u + Real.log 2) = 0
  rw [hH.vanish _ (fun hm => hu ⟨by linarith [hm.1], by
    linarith [hm.2, Real.log_pos (by norm_num : (1 : ℝ) < 2)]⟩), mul_zero]

theorem heckeWindowPush_mem {A : ℝ} {H : ℝ → ℝ} (hH : IsWindowTest A H) :
    IsWindowTest (A + Real.log 2) (heckeWindowPush H) := by
  refine ⟨contDiff_const.mul hH.contDiff, ?_⟩
  intro u hu
  change Real.sqrt 2 * H u = 0
  rw [hH.vanish _ (fun hm => hu ⟨by
    linarith [hm.1, Real.log_pos (by norm_num : (1 : ℝ) < 2)], hm.2⟩), mul_zero]

/-- On a supported test the expanded-stage adjoint has no cutoff loss. -/
theorem heckeWindowPull_eq_adjointShift {A : ℝ} {H : ℝ → ℝ}
    (hH : H ∈ windowSupported A) :
    heckeWindowPull H = fun u => Real.sqrt 2 * adjointShift (A + Real.log 2) (Real.log 2) H u := by
  funext u
  unfold heckeWindowPull adjointShift
  by_cases hu : u ∈ Ici (-(A + Real.log 2))
  · rw [indicator_of_mem hu]
  · rw [indicator_of_notMem hu, hH _ (fun hm => hu (by
      change -(A + Real.log 2) ≤ u
      linarith [hm.1])), mul_zero]

/-- Serre reflection exchanges the shifted and unshifted stage embeddings. -/
theorem windowInvolution_heckeWindowPull (A : ℝ) (H : ℝ → ℝ) :
    windowInvolution (A + Real.log 2) (heckeWindowPull H) =
      heckeWindowPush (windowInvolution A H) := by
  funext u
  simp only [windowInvolution, heckeWindowPull, heckeWindowPush]
  congr 2
  ring

theorem windowInvolution_heckeWindowPush (A : ℝ) (H : ℝ → ℝ) :
    windowInvolution (A + Real.log 2) (heckeWindowPush H) =
      heckeWindowPull (windowInvolution A H) := by
  funext u
  simp only [windowInvolution, heckeWindowPull, heckeWindowPush]
  congr 2
  ring

/-- The source correspondence preserves every term of Weil's form, with degree two. -/
theorem weilQuad_heckeWindowPull (H : ℝ → ℝ) :
    weilQuad (heckeWindowPull H) = 2 * weilQuad H := by
  unfold heckeWindowPull
  rw [weilQuad_const_mul, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have ht := weilQuad_translate H (-Real.log 2)
  simpa only [sub_neg_eq_add] using congrArg (fun q : ℝ => 2 * q) ht

theorem weilQuad_heckeWindowPush (H : ℝ → ℝ) :
    weilQuad (heckeWindowPush H) = 2 * weilQuad H := by
  unfold heckeWindowPush
  rw [weilQuad_const_mul, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

private theorem sqrt_two_exp_factor (s : ℂ) :
    (Real.sqrt 2 : ℂ) * Complex.exp ((2 * s - 1 / 2) * (-Real.log 2 : ℝ)) =
      2 * (2 : ℂ) ^ (-(2 * s)) := by
  have hsqrt : Real.sqrt 2 = Real.exp (Real.log 2 / 2) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    congr 1
    ring
  rw [hsqrt, Complex.ofReal_exp, Complex.cpow_def_of_ne_zero (by norm_num : (2 : ℂ) ≠ 0)]
  have hlog : (Real.log 2 : ℂ) = Complex.log 2 :=
    Complex.ofReal_log (by norm_num : (0 : ℝ) ≤ 2)
  calc
    Complex.exp ((Real.log 2 / 2 : ℝ) : ℂ) *
        Complex.exp ((2 * s - 1 / 2) * (-Real.log 2 : ℝ)) =
        Complex.exp (Complex.log 2 + Complex.log 2 * (-(2 * s))) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      rw [hlog]
      ring
    _ = 2 * Complex.exp (Complex.log 2 * (-(2 * s))) := by
      rw [Complex.exp_add, Complex.exp_log (by norm_num : (2 : ℂ) ≠ 0)]

/-- The Mellin multiplier is the source Hecke eigenvalue minus identity. -/
theorem tr_heckeWindowPull (H : ℝ → ℝ) (s : ℂ) :
    tr (fun u => (heckeWindowPull H u : ℂ)) (2 * s) =
      (2 * (2 : ℂ) ^ (-(2 * s))) * tr (fun u => (H u : ℂ)) (2 * s) := by
  have hfun : (fun u => (heckeWindowPull H u : ℂ)) = fun u =>
      (Real.sqrt 2 : ℂ) * ArithmeticPolarization.translate (-Real.log 2) (fun v => (H v : ℂ)) u := by
    funext u
    simp only [heckeWindowPull, ArithmeticPolarization.translate, sub_neg_eq_add, Complex.ofReal_mul]
  rw [hfun, tr, paperFT_const_mul]
  change (Real.sqrt 2 : ℂ) * tr (ArithmeticPolarization.translate (-Real.log 2) (fun u => (H u : ℂ))) (2 * s) = _
  rw [tr_translate, ← mul_assoc, sqrt_two_exp_factor]

/-- Mellin coefficients represented by actual normalized Eisenstein Lewis periods. -/
def windowMellinPeriod (H : ℝ → ℝ) (s : ℂ) (a : ℝ) : ℂ :=
  (tr (fun u => (H u : ℂ)) (2 * s) / eisensteinLewisPeriod s 1) * eisensteinLewisPeriod s a

theorem windowMellinPeriod_one (H : ℝ → ℝ) {s : ℂ} (hs0 : 0 < s.re)
    (hs1 : s.re < 1 / 2) :
    windowMellinPeriod H s 1 = tr (fun u => (H u : ℂ)) (2 * s) := by
  exact div_mul_cancel₀ _ (eisensteinLewisPeriod_one_ne_zero hs0 hs1)

/-- Window reflection acts on Mellin data by the reflected parameter and an exponential twist. -/
theorem tr_windowInvolution (A : ℝ) (H : ℝ → ℝ) (z : ℂ) :
    tr (fun u => (windowInvolution A H u : ℂ)) z =
      Complex.exp (-(A : ℂ) * (z - 1 / 2)) * tr (fun u => (H u : ℂ)) (1 - z) := by
  have ht : (fun u => (windowInvolution A H u : ℂ)) =
      ArithmeticPolarization.translate (-A) (fe (fun u => (H u : ℂ))) := by
    funext u
    simp only [windowInvolution, ArithmeticPolarization.translate, fe]
    congr 2
    ring
  rw [ht, tr_translate, tr_fe]
  congr 2
  push_cast
  ring

/-- The reflected period coefficient changes spectral parameter; it is not fixed-parameter
modular inversion on the period variable. -/
theorem windowMellinPeriod_reflection_one (A : ℝ) (H : ℝ → ℝ) {s : ℂ}
    (hs0 : 0 < s.re) (hs1 : s.re < 1 / 2) :
    windowMellinPeriod (windowInvolution A H) s 1 =
      Complex.exp (-(A : ℂ) * (2 * s - 1 / 2)) *
        windowMellinPeriod H (1 / 2 - s) 1 := by
  have hr0 : 0 < (1 / 2 - s).re := by simp; linarith
  have hr1 : (1 / 2 - s).re < 1 / 2 := by simp; linarith
  rw [windowMellinPeriod_one _ hs0 hs1, windowMellinPeriod_one _ hr0 hr1,
    tr_windowInvolution]
  congr 2
  ring

private theorem tr_real_conj (H : ℝ → ℝ) (z : ℂ) :
    tr (fun u => (H u : ℂ)) (conj z) = conj (tr (fun u => (H u : ℂ)) z) := by
  rw [tr_eq, tr_eq, ← integral_conj]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  dsimp only
  rw [map_mul, Complex.conj_ofReal, ← Complex.exp_conj]
  congr 2
  simp only [map_mul, map_sub, map_div₀, map_one, map_ofNat, Complex.conj_ofReal]

/-- On real window data, Serre reflection is the conjugate-linear, exponentially twisted
Riemann–Mayer parameter reflection. This identifies the exact additional operations. -/
theorem windowMellinPeriod_krein_reflection_one (A : ℝ) (H : ℝ → ℝ) {s : ℂ}
    (hs0 : 0 < s.re) (hs1 : s.re < 1 / 2) :
    windowMellinPeriod (windowInvolution A H) s 1 =
      Complex.exp (-(A : ℂ) * (2 * s - 1 / 2)) *
        conj (windowMellinPeriod H (riemannMayerReflect s) 1) := by
  have hr0 : 0 < (riemannMayerReflect s).re := by rw [riemannMayerReflect_re]; linarith
  have hr1 : (riemannMayerReflect s).re < 1 / 2 := by rw [riemannMayerReflect_re]; linarith
  rw [windowMellinPeriod_one _ hs0 hs1, windowMellinPeriod_one _ hr0 hr1,
    tr_windowInvolution, ← tr_real_conj]
  congr 2
  simp only [riemannMayerReflect, map_mul, map_sub, map_div₀, map_one, map_ofNat,
    Complex.conj_conj]
  ring

/-- The four actual Hecke branches realize the expanded-stage adjoint shift. -/
theorem lewisHeckeT2_windowMellinPeriod (H : ℝ → ℝ) {s : ℂ}
    (hs0 : 0 < s.re) (hs1 : s.re < 1 / 2) {a : ℝ} (ha : 0 < a) :
    lewisHeckeT2 s (windowMellinPeriod H s) a - windowMellinPeriod H s a =
      windowMellinPeriod (heckeWindowPull H) s a := by
  have he := eisensteinLewisPeriod_hecke hs0 hs1 ha
  have hlin (c : ℂ) :
      lewisHeckeT2 s (fun x : ℝ => c * eisensteinLewisPeriod s x) a =
        c * lewisHeckeT2 s (fun x : ℝ => eisensteinLewisPeriod s x) a := by
    simp only [lewisHeckeT2]
    ring
  unfold windowMellinPeriod
  rw [hlin, he, tr_heckeWindowPull]
  ring

/-- The normalized periods recover the complete zero-side Weil form, including multiplicity.
No positivity or critical-line restriction enters the correspondence. -/
theorem weilQuad_eq_windowMellinPeriod {H : ℝ → ℝ} (hH : ContDiff ℝ 2 H)
    (hc : HasCompactSupport H) :
    weilQuad H = (∑' ρ : zetaZeroConfig.carrier, (zetaZeroConfig.mult ρ : ℂ) *
      windowMellinPeriod H ((ρ : ℂ) / 2) 1 *
      conj (windowMellinPeriod H ((1 - conj (ρ : ℂ)) / 2) 1)).re := by
  have hHc : ContDiff ℝ 2 (fun u => (H u : ℂ)) := Complex.ofRealCLM.contDiff.comp hH
  have hcc : HasCompactSupport (fun u => (H u : ℂ)) := hc.comp_left Complex.ofReal_zero
  rw [weilQuad, ← _root_.RHTower.zetaZeroConfig_W_eq_weilFullFunctional_bilinear hHc hcc hHc hcc]
  congr 1
  rw [ZeroConfig.W]
  refine tsum_congr fun ρ => ?_
  have hr : IsNontrivialZero (ρ : ℂ) := ρ.2
  have h0 : 0 < ((ρ : ℂ) / 2).re := by simp; linarith [hr.2.1]
  have h1 : ((ρ : ℂ) / 2).re < 1 / 2 := by simp; linarith [hr.2.2]
  have hr0 : 0 < ((1 - conj (ρ : ℂ)) / 2).re := by simp; linarith [hr.2.2]
  have hr1 : ((1 - conj (ρ : ℂ)) / 2).re < 1 / 2 := by simp; linarith [hr.2.1]
  rw [windowMellinPeriod_one H h0 h1, windowMellinPeriod_one H hr0 hr1,
    show 2 * ((ρ : ℂ) / 2) = ρ by ring,
    show 2 * ((1 - conj (ρ : ℂ)) / 2) = 1 - conj (ρ : ℂ) by ring,
    ZeroConfig.Wsummand, paperFT_conj_gammaOf]
  rfl

#print axioms lewisHeckeT2_windowMellinPeriod
#print axioms weilQuad_heckeWindowPull
#print axioms weilQuad_eq_windowMellinPeriod
#print axioms windowInvolution_heckeWindowPull
#print axioms heckeWindowPull_eq_adjointShift
#print axioms windowMellinPeriod_reflection_one
#print axioms windowMellinPeriod_krein_reflection_one

end GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScattering
