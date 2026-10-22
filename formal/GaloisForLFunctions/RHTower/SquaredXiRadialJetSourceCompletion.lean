import GaloisForLFunctions.RHTower.SquaredXiSourceJetRHWiring
import GaloisForLFunctions.RHTower.CompletedRadialSourcePolynomial
import GaloisForLFunctions.RHTower.CCM.CCMSharpPrimeWindowContinuation
import GaloisForLFunctions.RHTower.EulerGammaCoPoissonDividedLogJetWeld
import GaloisForLFunctions.RHTower.VonMangoldtThreeFourOneSeries
import GaloisForLFunctions.HTGeometry.SampledSmallSmooth

/-!
# Completion of the squared-Xi reverse-Bessel source alignment

This module closes the interfaces between the previously separate complex source split, real
radial-jet identity, pole-filled zeta coordinate, and Chebyshev--Stieltjes prime source.  It proves
that the actual completed source jet is the real part of the sign-aligned complex polynomial, that
its prime part is exactly the positive reverse-Bessel von Mangoldt series, and that the polar/Euler
pair remains grouped as the logarithmic derivative of the pole-filled zeta function.
-/

open Complex Filter MeasureTheory Set ArithmeticFunction LSeries
open scoped LSeries.notation

namespace RHTower

noncomputable section

/-- Real trace of the logarithmic derivative of the pole-filled zeta function. -/
def regularizedZetaRayLogDeriv (s : ℝ) : ℝ :=
  (logDeriv regularizedRiemannZeta (s : ℂ)).re

/-- Away from the filled point, the regularized coordinate is exactly the pole plus the ordinary
zeta logarithmic derivative. -/
theorem regularizedZetaRayLogDeriv_eq {s : ℝ} (hs : 1 < s) :
    regularizedZetaRayLogDeriv s =
      1 / (s - 1) + deriv realZetaSeries s / realZetaSeries s := by
  have hs1 : (s : ℂ) ≠ 1 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  have hz : riemannZeta (s : ℂ) ≠ 0 :=
    riemannZeta_ne_zero_of_one_lt_re (by simpa using hs)
  rw [regularizedZetaRayLogDeriv, logDeriv_regularizedRiemannZeta_eq hs1 hz,
    Complex.add_re]
  have hpole : ((1 : ℂ) / ((s : ℂ) - 1)).re = 1 / (s - 1) := by
    have hne : s - 1 ≠ 0 := by linarith
    have hcast : (1 : ℂ) / ((s : ℂ) - 1) = ((1 / (s - 1) : ℝ) : ℂ) := by
      push_cast
      field_simp
    rw [hcast, Complex.ofReal_re]
  have hzeta : (zetaLogDeriv (s : ℂ)).re =
      deriv realZetaSeries s / realZetaSeries s := by
    rw [zetaLogDeriv]
    exact (realZetaLogDeriv_eq hs).symm
  rw [hpole, hzeta]

/-- Cancellation-preserving form of the completed logarithmic derivative. -/
theorem xiRayLogDeriv_eq_archimedean_add_regularized {s : ℝ} (hs : 1 < s) :
    xiRayLogDeriv s = archimedeanRayLogDeriv s + regularizedZetaRayLogDeriv s := by
  rw [xiRayLogDeriv_split hs, regularizedZetaRayLogDeriv_eq hs]

theorem contDiffAt_regularizedZetaRayLogDeriv {s : ℝ} (hs : 1 < s)
    (n : WithTop ℕ∞) : ContDiffAt ℝ n regularizedZetaRayLogDeriv s := by
  have h := (contDiffAt_poleTerm hs n).add (contDiffAt_realZetaLogDeriv hs n)
  refine h.congr_of_eventuallyEq ?_
  filter_upwards [Ioi_mem_nhds hs] with y hy
  exact regularizedZetaRayLogDeriv_eq hy

/-- The pole-filled logarithmic derivative is smooth through `s = 1`; the polar and Euler pieces
are never separated at the filled point. -/
theorem contDiffAt_regularizedZetaRayLogDeriv_one (n : WithTop ℕ∞) :
    ContDiffAt ℝ n regularizedZetaRayLogDeriv 1 := by
  have hopen : IsOpen {z : ℂ | regularizedRiemannZeta z ≠ 0} :=
    isOpen_ne.preimage differentiable_regularizedRiemannZeta.continuous
  have hdiff : DifferentiableOn ℂ (logDeriv regularizedRiemannZeta)
      {z : ℂ | regularizedRiemannZeta z ≠ 0} := by
    change DifferentiableOn ℂ (fun z => deriv regularizedRiemannZeta z /
      regularizedRiemannZeta z) {z : ℂ | regularizedRiemannZeta z ≠ 0}
    intro z hz
    have ha : AnalyticAt ℂ regularizedRiemannZeta z :=
      differentiable_regularizedRiemannZeta.analyticAt z
    have hd : DifferentiableAt ℂ (deriv regularizedRiemannZeta) z :=
      ha.deriv.differentiableAt
    exact (hd.div (differentiable_regularizedRiemannZeta z) hz).differentiableWithinAt
  exact GaloisForLFunctions.HTGeometry.contDiffAt_re_comp_ofReal hopen hdiff
    (by simp [regularizedRiemannZeta_one]) n

/-- The actual completed source jet is the real alternating radial jet of `xi'/xi`. -/
theorem completedSourceJet_eq_radialJet (n : ℕ) (w : ℝ) :
    completedSourceJet n w = radialJet n (1 / 2 + w) xiRayLogDeriv := by
  rw [completedSourceJet, radialJet]
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- Exact pole-filled-zeta decomposition of the completed source jet. -/
theorem completedSourceJet_eq_archimedean_add_regularized
    (n : ℕ) {w : ℝ} (hw : 1 / 2 < w) :
    completedSourceJet n w =
      radialJet n (1 / 2 + w) archimedeanRayLogDeriv +
        radialJet n (1 / 2 + w) regularizedZetaRayLogDeriv := by
  have hs : 1 < (1 / 2 + w : ℝ) := by linarith
  rw [completedSourceJet_eq_radialJet]
  have hEq : xiRayLogDeriv =ᶠ[nhds (1 / 2 + w)]
      fun s => archimedeanRayLogDeriv s + regularizedZetaRayLogDeriv s := by
    filter_upwards [Ioi_mem_nhds hs] with s hs'
    exact xiRayLogDeriv_eq_archimedean_add_regularized hs'
  rw [radialJet_congr_of_eventuallyEq hEq,
    radialJet_add (fun k => contDiffAt_archimedeanRayLogDeriv hs (k : ℕ))
      (fun k => contDiffAt_regularizedZetaRayLogDeriv hs (k : ℕ))]

/-- Exact cancellation-preserving Chebyshev--Stieltjes form of the completed source jet. -/
theorem completedSourceJet_eq_archimedean_add_discrepancy
    (n : ℕ) {w : ℝ} (hw : 1 / 2 < w) :
    completedSourceJet n w =
      radialJet n (1 / 2 + w) archimedeanRayLogDeriv +
        ((∫ x in Ioi (1 : ℝ), radialBesselKernel n (1 / 2 + w) x) -
          ∫ x, radialBesselKernel n (1 / 2 + w) x ∂chebyshevPsiStieltjes.measure) := by
  have hs : 1 < (1 / 2 + w : ℝ) := by linarith
  rw [completedSourceJet_eq_radialJet, radialJet_xiRayLogDeriv hs]

/-- The complete reverse-Bessel von Mangoldt source is strictly positive on the convergence ray. -/
theorem reverseBesselVonMangoldtSource_pos {n : ℕ} {s : ℝ} (hs : 1 < s) :
    0 < ∑' m : ℕ, (vonMangoldt m : ℝ) * radialBesselKernel n s (m : ℝ) := by
  rw [← sum_radialJetWeight_vonMangoldtLogSeries hs]
  apply Finset.sum_pos'
  · intro j hj
    have hjn : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    have hb : (0 : ℝ) < (squaredRadialJetWeight n j : ℝ) := by
      exact_mod_cast squaredRadialJetWeight_pos n j hjn
    have hw : 0 < (s - 1 / 2) ^ j := pow_pos (by linarith) j
    exact (mul_pos (mul_pos hb hw) (vonMangoldtLogSeries_pos hs)).le
  · refine ⟨0, by simp, ?_⟩
    simp only [pow_zero, mul_one]
    exact mul_pos (by exact_mod_cast squaredRadialJetWeight_pos n 0 (Nat.zero_le n))
      (vonMangoldtLogSeries_pos hs)

/-- The logarithmically weighted complex von Mangoldt L-series restricts to the literal real
von Mangoldt log-moment series. -/
theorem re_LSeries_logMul_vonMangoldt_real (j : ℕ) {s : ℝ} (hs : 1 < s) :
    (LSeries (LSeries.logMul^[j] ↗Λ) (s : ℂ)).re = vonMangoldtLogSeries j s := by
  have habs : abscissaOfAbsConv (LSeries.logMul^[j] ↗Λ) < s := by
    rw [LSeries.absicssaOfAbsConv_logPowMul]
    exact lt_of_le_of_lt abscissaOfAbsConv_vonMangoldt_le (by exact_mod_cast hs)
  have hsum : LSeriesSummable (LSeries.logMul^[j] ↗Λ) (s : ℂ) :=
    LSeriesSummable_of_abscissaOfAbsConv_lt_re (by simpa using habs)
  rw [LSeries, vonMangoldtLogSeries]
  rw [← (Complex.hasSum_re hsum.hasSum).tsum_eq]
  apply tsum_congr
  intro m
  by_cases hm : m = 0
  · subst m
    simp [LSeries.term]
  · have hterm : LSeries.term (LSeries.logMul^[j] ↗Λ) (s : ℂ) m =
        (Complex.log m) ^ j * LSeries.term ↗Λ (s : ℂ) m := by
      rw [LSeries.term_of_ne_zero hm, LSeries.term_of_ne_zero hm,
        logMul_iterate_vonMangoldt]
      ring
    rw [hterm, ← Complex.natCast_log, ← Complex.ofReal_pow, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
      re_lseries_term_vonMangoldt_real (Nat.pos_of_ne_zero hm) s]
    ring

/-- The complex prime polynomial is exactly the literal reverse-Bessel von Mangoldt source on the
real convergence ray. -/
theorem squaredXiPrimeJetPolynomial_re_eq (n : ℕ) {w : ℝ} (hw : 1 / 2 < w) :
    (squaredXiPrimeJetPolynomial n (w : ℂ)).re =
      ∑' m : ℕ, (vonMangoldt m : ℝ) * radialBesselKernel n (1 / 2 + w) (m : ℝ) := by
  have hs : 1 < (1 / 2 + w : ℝ) := by linarith
  rw [squaredXiPrimeJetPolynomial, ← Complex.reCLM_apply, map_sum]
  change (∑ j ∈ Finset.range (n + 1),
      ((squaredRadialJetWeight n j : ℂ) * (w : ℂ) ^ j *
        LSeries (LSeries.logMul^[j] ↗Λ) ((1 / 2 : ℂ) + (w : ℂ))).re) = _
  rw [← sum_radialJetWeight_vonMangoldtLogSeries hs]
  apply Finset.sum_congr rfl
  intro j hj
  have harg : ((1 / 2 : ℂ) + (w : ℂ)) = ((1 / 2 + w : ℝ) : ℂ) := by push_cast; ring
  rw [harg]
  have hL := re_LSeries_logMul_vonMangoldt_real j hs
  have hcoeff : (squaredRadialJetWeight n j : ℂ) * (w : ℂ) ^ j =
      (((squaredRadialJetWeight n j : ℝ) * w ^ j : ℝ) : ℂ) := by push_cast; ring
  rw [hcoeff, Complex.mul_re]
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, hL]
  ring

/-- Strict positivity of the prime polynomial; the prime sign in the completed source split is
therefore strictly negative. -/
theorem squaredXiPrimeJetPolynomial_re_pos (n : ℕ) {w : ℝ} (hw : 1 / 2 < w) :
    0 < (squaredXiPrimeJetPolynomial n (w : ℂ)).re := by
  rw [squaredXiPrimeJetPolynomial_re_eq n hw]
  exact reverseBesselVonMangoldtSource_pos (by linarith)

theorem contDiff_xiLogDeriv_comp_ofReal :
    ContDiff ℝ (⊤ : ℕ∞) (fun x : ℝ => xiLogDeriv (x : ℂ)) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  have hxi : AnalyticAt ℂ xi (x : ℂ) := xi_differentiable.analyticAt _
  have hlog : AnalyticAt ℂ xiLogDeriv (x : ℂ) := by
    change AnalyticAt ℂ (fun z => deriv xi z / xi z) (x : ℂ)
    exact hxi.deriv.div hxi (xi_ofReal_ne_zero x)
  exact (hlog.contDiffAt.restrict_scalars ℝ).comp x
    Complex.ofRealCLM.contDiff.contDiffAt

/-- Real iterated derivatives of the Xi logarithmic derivative agree with the real parts of the
complex derivatives on the Euler ray. -/
theorem iteratedDeriv_xiRayLogDeriv_eq_re (j : ℕ) {s : ℝ} (hs : 1 < s) :
    iteratedDeriv j xiRayLogDeriv s = (iteratedDeriv j xiLogDeriv (s : ℂ)).re := by
  have hclm := HTGeometry.iteratedDeriv_clm_comp Complex.reCLM j
    contDiff_xiLogDeriv_comp_ofReal
  have han : ∀ t : ℝ, 1 < t → AnalyticAt ℂ xiLogDeriv (t : ℂ) := by
    intro t ht
    have hxi : AnalyticAt ℂ xi (t : ℂ) := xi_differentiable.analyticAt _
    change AnalyticAt ℂ (fun z => deriv xi z / xi z) (t : ℂ)
    exact hxi.deriv.div hxi (xi_ofReal_ne_zero t)
  have hrestr := HTGeometry.iteratedDeriv_comp_ofReal_of_analyticAt
    (T := 1) j han s hs
  change iteratedDeriv j (fun x : ℝ => Complex.reCLM (xiLogDeriv (x : ℂ))) s = _
  rw [congrFun hclm s, hrestr]
  rfl

/-- The actual real completed source jet is exactly the real part of the complex sign-aligned
polynomial. -/
theorem completedSourceJet_eq_re_alternatingJetPolynomial
    (n : ℕ) {w : ℝ} (hw : 1 / 2 < w) :
    completedSourceJet n w = (squaredXiAlternatingJetPolynomial n (w : ℂ)).re := by
  have hs : 1 < (1 / 2 + w : ℝ) := by linarith
  rw [completedSourceJet, squaredXiAlternatingJetPolynomial, ← Complex.reCLM_apply, map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have harg : ((1 / 2 : ℂ) + (w : ℂ)) = ((1 / 2 + w : ℝ) : ℂ) := by push_cast; ring
  rw [harg]
  have hjet := iteratedDeriv_xiRayLogDeriv_eq_re j hs
  have hcoeff : (squaredRadialJetWeight n j : ℂ) * (w : ℂ) ^ j * (-1 : ℂ) ^ j =
      (((squaredRadialJetWeight n j : ℝ) * w ^ j * (-1 : ℝ) ^ j : ℝ) : ℂ) := by
    push_cast
    ring
  rw [hcoeff]
  simp only [Complex.reCLM_apply]
  rw [Complex.mul_re]
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, ← hjet]
  ring

/-- End-to-end source-alignment theorem for the actual completed source jet. -/
theorem completedSourceJet_eq_rationalGamma_sub_prime
    (n : ℕ) {w : ℝ} (hw : 1 / 2 < w) :
    completedSourceJet n w =
      (squaredXiAlternatingRationalGammaJetPolynomial n (w : ℂ)).re -
        (squaredXiPrimeJetPolynomial n (w : ℂ)).re := by
  have hs : 1 < (1 / 2 + w : ℝ) := by linarith
  rw [completedSourceJet_eq_re_alternatingJetPolynomial n hw,
    squaredXiAlternatingJetPolynomial_eq_rationalGamma_sub_prime n (by simpa using hs)]
  simp

end

end RHTower
