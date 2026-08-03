import GaloisForLFunctions.RHTower.CCMRationalPeriodicWeightedPoisson
import GaloisForLFunctions.RHTower.DeningerMeyerLogSchwartzLanding

/-!
# All-derivative strong decay for periodic rational CCM traces

The finite-adèlic restriction of a Bruhat factor is periodic on a rational
lattice.  The corresponding archimedean trace is therefore

`Θ_{w,f}(a) = ∑' n : ℤ, w(n mod M) f(an)`.

This file proves the analytic statement required by the strong CCM target:
after writing `a = exp t`, every logarithmic derivative decays faster than
every exponential at both ends.  At the positive end this follows from a
uniform Schwartz majorant.  At the negative end we differentiate the exact
weighted Poisson identity.  The conjugate Euler operator `A = -(1 + E)` then
acts on the Fourier-side Schwartz source.  Thus no unproved assertion that
Euler differentiation preserves the Fourier zero mode is used.

The hypotheses are exactly the two weighted endpoint cancellations

`w(0) f(0) = 0`,  `(∑ r, w r) (𝓕 f)(0) = 0`.

No positivity, spectral premise, numerical computation, or Riemann-hypothesis
assumption occurs.
-/

noncomputable section

open Complex Filter Function Set Topology
open scoped ContDiff FourierTransform SchwartzMap
open RHTower

namespace GaloisForLFunctions
namespace RHTower

/-- Periodic weighted rational trace in logarithmic radius. -/
def ccmRationalPeriodicWeightedLogTrace
    (M : ℕ) [NeZero M] (w : Fin M → ℂ)
    (f : CCMRationalArchimedeanSchwartz) (t : ℝ) : ℂ :=
  ccmRationalPeriodicWeightedTrace M w f (Real.exp t)

private theorem ccmRationalBoundedWeightedEuler_term_bound
    (v : ℤ → ℂ) (B : ℝ) (hv : ∀ n, ‖v n‖ ≤ B)
    (f : CCMRationalArchimedeanSchwartz) (T : ℝ) (n : ℤ)
    {t : ℝ} (ht : T < t) :
    ‖v n *
        RHTower.deningerMeyerEulerCLM f
          (Real.exp t * (n : ℝ))‖ ≤
      (B *
          SchwartzMap.seminorm ℂ 2 0
            (RHTower.deningerMeyerEulerCLM f) /
            Real.exp T ^ 2) *
        ccmRationalArchimedeanPSeriesKernel 0 n := by
  by_cases hn : n = 0
  · subst n
    simp [RHTower.deningerMeyerEulerCLM_zero,
      ccmRationalArchimedeanPSeriesKernel]
  let g := RHTower.deningerMeyerEulerCLM f
  let S := SchwartzMap.seminorm ℂ 2 0 g
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  have hT : 0 < Real.exp T := Real.exp_pos T
  have het : Real.exp T < Real.exp t := Real.exp_lt_exp.mpr ht
  have harg : Real.exp t * (n : ℝ) ≠ 0 :=
    mul_ne_zero (Real.exp_ne_zero t) hnR
  have hsem :=
    SchwartzMap.norm_pow_mul_le_seminorm ℂ g 2
      (Real.exp t * (n : ℝ))
  have hden : 0 < ‖Real.exp t * (n : ℝ)‖ ^ 2 :=
    pow_pos (norm_pos_iff.mpr harg) _
  have hgraw :
      ‖g (Real.exp t * (n : ℝ))‖ ≤
        S / ‖Real.exp t * (n : ℝ)‖ ^ 2 := by
    apply (le_div_iff₀ hden).2
    simpa [S, mul_comm] using hsem
  have hS : 0 ≤ S := by positivity
  have hdenle :
      Real.exp T ^ 2 * (n : ℝ) ^ 2 ≤
        ‖Real.exp t * (n : ℝ)‖ ^ 2 := by
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos t),
      mul_pow, sq_abs]
    have hsquare : Real.exp T ^ 2 ≤ Real.exp t ^ 2 := by
      nlinarith [Real.exp_pos T, Real.exp_pos t]
    exact mul_le_mul_of_nonneg_right hsquare (sq_nonneg (n : ℝ))
  have hminor : 0 < Real.exp T ^ 2 * (n : ℝ) ^ 2 :=
    mul_pos (sq_pos_of_pos hT) (sq_pos_of_ne_zero hnR)
  have hg :
      ‖g (Real.exp t * (n : ℝ))‖ ≤
        S / (Real.exp T ^ 2 * (n : ℝ) ^ 2) :=
    hgraw.trans (div_le_div_of_nonneg_left hS hminor hdenle)
  have hB : 0 ≤ B := (norm_nonneg (v 0)).trans (hv 0)
  rw [norm_mul]
  calc
    ‖v n‖ *
        ‖g (Real.exp t * (n : ℝ))‖ ≤
        B * ‖g (Real.exp t * (n : ℝ))‖ :=
      mul_le_mul_of_nonneg_right (hv n) (norm_nonneg _)
    _ ≤ B * (S / (Real.exp T ^ 2 * (n : ℝ) ^ 2)) :=
      mul_le_mul_of_nonneg_left hg hB
    _ = (B * S / Real.exp T ^ 2) *
        ccmRationalArchimedeanPSeriesKernel 0 n := by
      rw [ccmRationalArchimedeanPSeriesKernel, if_neg hn,
        ccmRationalArchimedeanDecayExponent]
      norm_num
      ring

private theorem hasDerivAt_ccmRationalBoundedWeightedLogSummand
    (v : ℤ → ℂ)
    (f : CCMRationalArchimedeanSchwartz) (n : ℤ) (t : ℝ) :
    HasDerivAt
      (fun s : ℝ =>
        v n * f (Real.exp s * (n : ℝ)))
      (v n *
        RHTower.deningerMeyerEulerCLM f
          (Real.exp t * (n : ℝ))) t := by
  have harg :
      HasDerivAt (fun s : ℝ => Real.exp s * (n : ℝ))
        (Real.exp t * (n : ℝ)) t :=
    (Real.hasDerivAt_exp t).mul_const (n : ℝ)
  have hf := (f.hasDerivAt (Real.exp t * (n : ℝ))).scomp t harg
  have hf' :
      HasDerivAt (fun s : ℝ => f (Real.exp s * (n : ℝ)))
        (RHTower.deningerMeyerEulerCLM f
          (Real.exp t * (n : ℝ))) t := by
    simpa only [Function.comp_apply,
      RHTower.deningerMeyerEulerCLM_apply,
      Complex.real_smul, Complex.ofReal_mul,
      Complex.ofReal_exp, Complex.ofReal_intCast] using hf
  exact hf'.const_mul (v n)

/-- Bounded weighted lattice trace in logarithmic radius. -/
def ccmRationalBoundedWeightedLogTrace
    (v : ℤ → ℂ) (f : CCMRationalArchimedeanSchwartz) (t : ℝ) : ℂ :=
  ccmRationalBoundedWeightedLatticeTrace v f (Real.exp t)

private theorem hasDerivAt_ccmRationalBoundedWeightedLogTrace
    (v : ℤ → ℂ) (B : ℝ) (hv : ∀ n, ‖v n‖ ≤ B)
    (f : CCMRationalArchimedeanSchwartz) (t : ℝ) :
    HasDerivAt (ccmRationalBoundedWeightedLogTrace v f)
      (ccmRationalBoundedWeightedLogTrace v
        (RHTower.deningerMeyerEulerCLM f) t) t := by
  change HasDerivAt
    (fun z : ℝ => ∑' n : ℤ, v n * f (Real.exp z * (n : ℝ)))
    (∑' n : ℤ, v n * RHTower.deningerMeyerEulerCLM f
      (Real.exp t * (n : ℝ))) t
  let T := t - 1
  let C := B * SchwartzMap.seminorm ℂ 2 0
      (RHTower.deningerMeyerEulerCLM f) / Real.exp T ^ 2
  let u : ℤ → ℝ := fun n =>
    C * ccmRationalArchimedeanPSeriesKernel 0 n
  have hu : Summable u :=
    (ccmRationalArchimedeanPSeriesKernel_summable 0).mul_left C
  have hTt : T < t := by dsimp [T]; linarith
  have hsum0 : Summable (fun n : ℤ =>
      v n * f (Real.exp t * (n : ℝ))) :=
    ccmRationalBoundedWeightedLatticeTrace_summable
      v B hv f (Real.exp_ne_zero t)
  exact hasDerivAt_tsum_of_isPreconnected
    (g := fun (n : ℤ) (s : ℝ) =>
      v n * f (Real.exp s * (n : ℝ)))
    (g' := fun (n : ℤ) (s : ℝ) =>
      v n * RHTower.deningerMeyerEulerCLM f
        (Real.exp s * (n : ℝ)))
    (t := Ioi T) (y₀ := t) (y := t)
    hu isOpen_Ioi isPreconnected_Ioi
    (fun n s _ =>
      hasDerivAt_ccmRationalBoundedWeightedLogSummand v f n s)
    (fun n s hs => by
      simpa [u, C] using
        ccmRationalBoundedWeightedEuler_term_bound v B hv f T n hs)
    hTt hsum0 hTt

/-- Exact first logarithmic derivative of a periodic weighted trace. -/
theorem hasDerivAt_ccmRationalPeriodicWeightedLogTrace
    (M : ℕ) [NeZero M] (w : Fin M → ℂ)
    (f : CCMRationalArchimedeanSchwartz) (t : ℝ) :
    HasDerivAt (ccmRationalPeriodicWeightedLogTrace M w f)
      (ccmRationalPeriodicWeightedLogTrace M w
        (RHTower.deningerMeyerEulerCLM f) t) t := by
  change HasDerivAt
    (ccmRationalBoundedWeightedLogTrace
      (fun n => w (ccmRationalPeriodicResidue M n)) f)
    (ccmRationalBoundedWeightedLogTrace
      (fun n => w (ccmRationalPeriodicResidue M n))
      (RHTower.deningerMeyerEulerCLM f) t) t
  exact hasDerivAt_ccmRationalBoundedWeightedLogTrace
    (fun n => w (ccmRationalPeriodicResidue M n))
    (ccmRationalPeriodicWeightNorm M w)
    (fun n => Finset.single_le_sum
      (fun r _ => norm_nonneg (w r)) (Finset.mem_univ _)) f t

theorem deriv_ccmRationalPeriodicWeightedLogTrace
    (M : ℕ) [NeZero M] (w : Fin M → ℂ)
    (f : CCMRationalArchimedeanSchwartz) :
    deriv (ccmRationalPeriodicWeightedLogTrace M w f) =
      ccmRationalPeriodicWeightedLogTrace M w
        (RHTower.deningerMeyerEulerCLM f) := by
  funext t
  exact (hasDerivAt_ccmRationalPeriodicWeightedLogTrace M w f t).deriv

/-- Every logarithmic derivative is the trace of the corresponding Euler
iterate. -/
theorem iteratedDeriv_ccmRationalPeriodicWeightedLogTrace
    (M : ℕ) [NeZero M] (w : Fin M → ℂ)
    (f : CCMRationalArchimedeanSchwartz) (k : ℕ) :
    iteratedDeriv k (ccmRationalPeriodicWeightedLogTrace M w f) =
      ccmRationalPeriodicWeightedLogTrace M w
        (RHTower.deningerMeyerEulerIterate k f) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [iteratedDeriv_succ, ih,
        deriv_ccmRationalPeriodicWeightedLogTrace,
        RHTower.deningerMeyerEulerIterate_succ]

/-- Periodic weighted logarithmic trace is smooth for every Schwartz source. -/
theorem contDiff_ccmRationalPeriodicWeightedLogTrace
    (M : ℕ) [NeZero M] (w : Fin M → ℂ)
    (f : CCMRationalArchimedeanSchwartz) :
    ContDiff ℝ ∞ (ccmRationalPeriodicWeightedLogTrace M w f) := by
  rw [contDiff_infty]
  intro N
  apply contDiff_of_differentiable_iteratedDeriv
  intro k _
  rw [iteratedDeriv_ccmRationalPeriodicWeightedLogTrace]
  exact fun t =>
    (hasDerivAt_ccmRationalPeriodicWeightedLogTrace M w
      (RHTower.deningerMeyerEulerIterate k f) t).differentiableAt

/-- Fourier-side weighted trace appearing in periodic Poisson reflection. -/
def ccmRationalPeriodicDualLogTrace
    (M : ℕ) [NeZero M] (w : Fin M → ℂ)
    (g : CCMRationalArchimedeanSchwartz) (t : ℝ) : ℂ :=
  ccmRationalBoundedWeightedLatticeTrace
    (ccmRationalPeriodicFourierCoefficient M w) g
    (Real.exp (-t) * (M : ℝ)⁻¹)

/-- Exact periodic weighted Poisson reflection in logarithmic radius. -/
theorem ccmRationalPeriodicWeightedLogTrace_reflection
    (M : ℕ) [NeZero M] (w : Fin M → ℂ)
    (f : CCMRationalArchimedeanSchwartz) (t : ℝ) :
    ccmRationalPeriodicWeightedLogTrace M w f t =
      ((Real.exp (-t) * (M : ℝ)⁻¹ : ℝ) : ℂ) *
        ccmRationalPeriodicDualLogTrace M w (𝓕 f) t := by
  have h := ccmRationalPeriodicWeightedTrace_poisson_as_boundedWeightedTrace
    M w f (Real.exp_pos t)
  rw [ccmRationalPeriodicWeightedLogTrace]
  rw [h]
  congr 2
  · norm_cast
    rw [Real.exp_neg]
    field_simp
  · rw [ccmRationalPeriodicDualLogTrace]
    congr 2
    rw [Real.exp_neg]
    field_simp

private theorem ccmRationalBoundedWeightedLogTrace_reflectedEuler
    (v : ℤ → ℂ) (g : CCMRationalArchimedeanSchwartz) (a : ℝ) :
    ccmRationalBoundedWeightedLatticeTrace v
        (RHTower.deningerMeyerReflectedEulerCLM g) a =
      -(ccmRationalBoundedWeightedLatticeTrace v g a +
        ccmRationalBoundedWeightedLatticeTrace v
          (RHTower.deningerMeyerEulerCLM g) a) := by
  rw [ccmRationalBoundedWeightedLatticeTrace,
    ccmRationalBoundedWeightedLatticeTrace,
    ccmRationalBoundedWeightedLatticeTrace]
  rw [← tsum_add]
  · apply tsum_congr
    intro n
    rw [RHTower.deningerMeyerReflectedEulerCLM_apply,
      RHTower.deningerMeyerEulerCLM_apply]
    ring
  · exact ccmRationalBoundedWeightedLatticeTrace_summable
      v (ccmRationalPeriodicWeightNorm 1 (fun _ => 0))
      (fun n => by simp [ccmRationalPeriodicWeightNorm]) g
      (by assumption)
  · exact ccmRationalBoundedWeightedLatticeTrace_summable
      v (ccmRationalPeriodicWeightNorm 1 (fun _ => 0))
      (fun n => by simp [ccmRationalPeriodicWeightNorm])
      (RHTower.deningerMeyerEulerCLM g) (by assumption)

end RHTower
end GaloisForLFunctions
