import GaloisForLFunctions.RHTower.CCM.CCMRationalPeriodicWeightedPoisson
import GaloisForLFunctions.RHTower.Deninger.DeningerMeyerLogSchwartzLanding

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
    simp [ccmRationalArchimedeanPSeriesKernel]
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
    change HasDerivAt
      (f ∘ fun s : ℝ => Real.exp s * (n : ℝ))
      (RHTower.deningerMeyerEulerCLM f
        (Real.exp t * (n : ℝ))) t
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
  ccmRationalBoundedWeightedLogTrace
    (ccmRationalPeriodicFourierCoefficient M w) g
    (-t - Real.log (M : ℝ))

theorem ccmRationalPeriodicDualLogTrace_eq
    (M : ℕ) [NeZero M] (w : Fin M → ℂ)
    (g : CCMRationalArchimedeanSchwartz) (t : ℝ) :
    ccmRationalPeriodicDualLogTrace M w g t =
      ccmRationalBoundedWeightedLatticeTrace
        (ccmRationalPeriodicFourierCoefficient M w) g
        (Real.exp (-t) * (M : ℝ)⁻¹) := by
  have hM : 0 < (M : ℝ) := by exact_mod_cast Nat.pos_of_neZero M
  rw [ccmRationalPeriodicDualLogTrace,
    ccmRationalBoundedWeightedLogTrace]
  congr 2
  rw [Real.exp_sub, Real.exp_neg, Real.exp_log hM,
    div_eq_mul_inv]

/-- Exact periodic weighted Poisson reflection in logarithmic radius. -/
theorem ccmRationalPeriodicWeightedLogTrace_reflection
    (M : ℕ) [NeZero M] (w : Fin M → ℂ)
    (f : CCMRationalArchimedeanSchwartz) (t : ℝ) :
    ccmRationalPeriodicWeightedLogTrace M w f t =
      ((Real.exp (-t) * (M : ℝ)⁻¹ : ℝ) : ℂ) *
        ccmRationalPeriodicDualLogTrace M w (𝓕 f) t := by
  have h := ccmRationalPeriodicWeightedTrace_poisson_as_boundedWeightedTrace
    M w f (Real.exp_pos t)
  have hscale :
      (Real.exp t * (M : ℝ))⁻¹ =
        Real.exp (-t) * (M : ℝ)⁻¹ := by
    rw [Real.exp_neg, mul_inv_rev]
    exact mul_comm _ _
  rw [ccmRationalPeriodicWeightedLogTrace, h,
    ccmRationalPeriodicDualLogTrace_eq, hscale]

private theorem ccmRationalBoundedWeightedLogTrace_reflectedEuler
    (v : ℤ → ℂ) (B : ℝ) (hv : ∀ n, ‖v n‖ ≤ B)
    (g : CCMRationalArchimedeanSchwartz) {a : ℝ} (ha : a ≠ 0) :
    ccmRationalBoundedWeightedLatticeTrace v
        (RHTower.deningerMeyerReflectedEulerCLM g) a =
      -(ccmRationalBoundedWeightedLatticeTrace v g a +
        ccmRationalBoundedWeightedLatticeTrace v
          (RHTower.deningerMeyerEulerCLM g) a) := by
  have hg := ccmRationalBoundedWeightedLatticeTrace_summable
    v B hv g ha
  have hE := ccmRationalBoundedWeightedLatticeTrace_summable
    v B hv (RHTower.deningerMeyerEulerCLM g) ha
  rw [ccmRationalBoundedWeightedLatticeTrace,
    ccmRationalBoundedWeightedLatticeTrace,
    ccmRationalBoundedWeightedLatticeTrace]
  calc
    (∑' n : ℤ, v n *
        RHTower.deningerMeyerReflectedEulerCLM g (a * (n : ℝ))) =
        ∑' n : ℤ, -(v n * g (a * (n : ℝ)) +
          v n * RHTower.deningerMeyerEulerCLM g (a * (n : ℝ))) := by
      apply tsum_congr
      intro n
      rw [RHTower.deningerMeyerReflectedEulerCLM_apply,
        RHTower.deningerMeyerEulerCLM_apply]
      ring
    _ = -(∑' n : ℤ, (v n * g (a * (n : ℝ)) +
          v n * RHTower.deningerMeyerEulerCLM g (a * (n : ℝ)))) := by
      rw [tsum_neg]
    _ = -((∑' n : ℤ, v n * g (a * (n : ℝ))) +
          ∑' n : ℤ,
            v n * RHTower.deningerMeyerEulerCLM g (a * (n : ℝ))) := by
      rw [hg.tsum_add hE]

private theorem hasDerivAt_ccmRationalPeriodicDualLogTrace
    (M : ℕ) [NeZero M] (w : Fin M → ℂ)
    (g : CCMRationalArchimedeanSchwartz) (t : ℝ) :
    HasDerivAt (ccmRationalPeriodicDualLogTrace M w g)
      (-ccmRationalPeriodicDualLogTrace M w
        (RHTower.deningerMeyerEulerCLM g) t) t := by
  let s : ℝ := -t - Real.log (M : ℝ)
  have hbase := hasDerivAt_ccmRationalBoundedWeightedLogTrace
    (ccmRationalPeriodicFourierCoefficient M w)
    (ccmRationalPeriodicWeightNorm M w)
    (norm_ccmRationalPeriodicFourierCoefficient_le M w) g s
  have hs : HasDerivAt
      (fun z : ℝ => -z - Real.log (M : ℝ)) (-1) t := by
    simpa using (hasDerivAt_neg t).sub_const (Real.log (M : ℝ))
  have hcomp := hbase.scomp t hs
  have hcomp' :
      HasDerivAt
        (ccmRationalBoundedWeightedLogTrace
          (ccmRationalPeriodicFourierCoefficient M w) g ∘
            fun z : ℝ => -z - Real.log (M : ℝ))
        (-ccmRationalBoundedWeightedLogTrace
          (ccmRationalPeriodicFourierCoefficient M w)
          (RHTower.deningerMeyerEulerCLM g) s) t :=
    hcomp.congr_deriv (by
      simp only [Complex.real_smul, Complex.ofReal_neg,
        Complex.ofReal_one, neg_mul, one_mul])
  change HasDerivAt
    (ccmRationalBoundedWeightedLogTrace
      (ccmRationalPeriodicFourierCoefficient M w) g ∘
        fun z : ℝ => -z - Real.log (M : ℝ))
    (-ccmRationalBoundedWeightedLogTrace
      (ccmRationalPeriodicFourierCoefficient M w)
      (RHTower.deningerMeyerEulerCLM g)
      (-t - Real.log (M : ℝ))) t
  simpa only [s] using hcomp'

private theorem ccmRationalPeriodicDualLogTrace_reflectedEuler
    (M : ℕ) [NeZero M] (w : Fin M → ℂ)
    (g : CCMRationalArchimedeanSchwartz) (t : ℝ) :
    ccmRationalPeriodicDualLogTrace M w
        (RHTower.deningerMeyerReflectedEulerCLM g) t =
      -(ccmRationalPeriodicDualLogTrace M w g t +
        ccmRationalPeriodicDualLogTrace M w
          (RHTower.deningerMeyerEulerCLM g) t) := by
  rw [ccmRationalPeriodicDualLogTrace_eq,
    ccmRationalPeriodicDualLogTrace_eq,
    ccmRationalPeriodicDualLogTrace_eq]
  apply ccmRationalBoundedWeightedLogTrace_reflectedEuler
    (ccmRationalPeriodicFourierCoefficient M w)
    (ccmRationalPeriodicWeightNorm M w)
    (norm_ccmRationalPeriodicFourierCoefficient_le M w)
  exact mul_ne_zero (Real.exp_ne_zero (-t)) (inv_ne_zero (by
    exact_mod_cast Nat.ne_of_gt (Nat.pos_of_neZero M)))

/-- Fourier-side reflection function whose derivatives are controlled by the
reflected Euler operator. -/
def ccmRationalPeriodicWeightedLogReflection
    (M : ℕ) [NeZero M] (w : Fin M → ℂ)
    (g : CCMRationalArchimedeanSchwartz) (t : ℝ) : ℂ :=
  ((Real.exp (-t) * (M : ℝ)⁻¹ : ℝ) : ℂ) *
    ccmRationalPeriodicDualLogTrace M w g t

theorem hasDerivAt_ccmRationalPeriodicWeightedLogReflection
    (M : ℕ) [NeZero M] (w : Fin M → ℂ)
    (g : CCMRationalArchimedeanSchwartz) (t : ℝ) :
    HasDerivAt (ccmRationalPeriodicWeightedLogReflection M w g)
      (ccmRationalPeriodicWeightedLogReflection M w
        (RHTower.deningerMeyerReflectedEulerCLM g) t) t := by
  have hcR : HasDerivAt
      (fun s : ℝ => Real.exp (-s) * (M : ℝ)⁻¹)
      (-Real.exp (-t) * (M : ℝ)⁻¹) t := by
    have hneg : HasDerivAt (fun s : ℝ => -s) (-1) t :=
      hasDerivAt_neg t
    have hexp : HasDerivAt (fun s : ℝ => Real.exp (-s))
        (-Real.exp (-t)) t := by
      have hraw := (Real.hasDerivAt_exp (-t)).scomp t hneg
      change HasDerivAt (Real.exp ∘ fun s : ℝ => -s)
        (-Real.exp (-t)) t
      simpa using hraw
    exact hexp.mul_const (M : ℝ)⁻¹
  have hc : HasDerivAt
      (fun s : ℝ => ((Real.exp (-s) * (M : ℝ)⁻¹ : ℝ) : ℂ))
      ((-Real.exp (-t) * (M : ℝ)⁻¹ : ℝ) : ℂ) t :=
    hcR.ofReal_comp
  have hdual := hasDerivAt_ccmRationalPeriodicDualLogTrace M w g t
  have hmul := hc.mul hdual
  have hcoef :
      ((-Real.exp (-t) * (M : ℝ)⁻¹ : ℝ) : ℂ) *
          ccmRationalPeriodicDualLogTrace M w g t +
        ((Real.exp (-t) * (M : ℝ)⁻¹ : ℝ) : ℂ) *
          -ccmRationalPeriodicDualLogTrace M w
            (RHTower.deningerMeyerEulerCLM g) t =
        ((Real.exp (-t) * (M : ℝ)⁻¹ : ℝ) : ℂ) *
          ccmRationalPeriodicDualLogTrace M w
            (RHTower.deningerMeyerReflectedEulerCLM g) t := by
    rw [ccmRationalPeriodicDualLogTrace_reflectedEuler]
    push_cast
    ring
  apply (hmul.congr_deriv hcoef).congr_of_eventuallyEq
  exact Filter.Eventually.of_forall fun _ => rfl

theorem deriv_ccmRationalPeriodicWeightedLogReflection
    (M : ℕ) [NeZero M] (w : Fin M → ℂ)
    (g : CCMRationalArchimedeanSchwartz) :
    deriv (ccmRationalPeriodicWeightedLogReflection M w g) =
      ccmRationalPeriodicWeightedLogReflection M w
        (RHTower.deningerMeyerReflectedEulerCLM g) := by
  funext t
  exact (hasDerivAt_ccmRationalPeriodicWeightedLogReflection M w g t).deriv

theorem iteratedDeriv_ccmRationalPeriodicWeightedLogReflection
    (M : ℕ) [NeZero M] (w : Fin M → ℂ)
    (g : CCMRationalArchimedeanSchwartz) (k : ℕ) :
    iteratedDeriv k (ccmRationalPeriodicWeightedLogReflection M w g) =
      ccmRationalPeriodicWeightedLogReflection M w
        (RHTower.deningerMeyerReflectedEulerIterate k g) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [iteratedDeriv_succ, ih,
        deriv_ccmRationalPeriodicWeightedLogReflection,
        RHTower.deningerMeyerReflectedEulerIterate_succ]

/-- Exact all-order differentiated weighted Poisson reflection. -/
theorem ccmRationalPeriodicWeightedEulerIterate_reflection
    (M : ℕ) [NeZero M] (w : Fin M → ℂ)
    (f : CCMRationalArchimedeanSchwartz) (k : ℕ) (t : ℝ) :
    ccmRationalPeriodicWeightedLogTrace M w
        (RHTower.deningerMeyerEulerIterate k f) t =
      ccmRationalPeriodicWeightedLogReflection M w
        (RHTower.deningerMeyerReflectedEulerIterate k (𝓕 f)) t := by
  have hfun :
      ccmRationalPeriodicWeightedLogTrace M w f =
        ccmRationalPeriodicWeightedLogReflection M w (𝓕 f) := by
    funext s
    simpa [ccmRationalPeriodicWeightedLogReflection] using
      ccmRationalPeriodicWeightedLogTrace_reflection M w f s
  calc
    ccmRationalPeriodicWeightedLogTrace M w
        (RHTower.deningerMeyerEulerIterate k f) t =
        iteratedDeriv k
          (ccmRationalPeriodicWeightedLogTrace M w f) t := by
      rw [iteratedDeriv_ccmRationalPeriodicWeightedLogTrace]
    _ = iteratedDeriv k
        (ccmRationalPeriodicWeightedLogReflection M w (𝓕 f)) t := by
      rw [hfun]
    _ = ccmRationalPeriodicWeightedLogReflection M w
        (RHTower.deningerMeyerReflectedEulerIterate k (𝓕 f)) t := by
      rw [iteratedDeriv_ccmRationalPeriodicWeightedLogReflection]

private theorem ccmRationalBoundedWeightedLogTrace_isBigO_atTop
    (v : ℤ → ℂ) (B : ℝ) (hv : ∀ n, ‖v n‖ ≤ B)
    (f : CCMRationalArchimedeanSchwartz)
    (hzero : v 0 * f 0 = 0) (a : ℝ) :
    ccmRationalBoundedWeightedLogTrace v f =O[atTop]
      fun t : ℝ => Real.exp t ^ (-a) := by
  let N : ℕ := ⌈max a 0⌉₊
  let p : ℕ := ccmRationalArchimedeanDecayExponent N
  let C : ℝ := B * ccmRationalArchimedeanDecayConstant f N
  have hB : 0 ≤ B := (norm_nonneg (v 0)).trans (hv 0)
  have hC : 0 ≤ C := mul_nonneg hB
    (ccmRationalArchimedeanDecayConstant_nonneg f N)
  have hap : a ≤ (p : ℝ) := by
    have hceil : max a 0 ≤ (N : ℝ) := Nat.le_ceil _
    have hNp : (N : ℝ) ≤ (p : ℝ) := by
      have hnat : N ≤ ccmRationalArchimedeanDecayExponent N := by
        simp [ccmRationalArchimedeanDecayExponent]
        omega
      exact_mod_cast hnat
    exact (le_max_left a 0).trans (hceil.trans hNp)
  refine (Asymptotics.IsBigOWith.of_bound (c := C) ?_).isBigO
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  have hx : 1 ≤ Real.exp t := Real.one_le_exp ht
  have hlarge := ccmRationalBoundedWeightedLatticeTrace_large_bound
    v B hv f hzero N (Real.exp_pos t)
  have hlarge' :
      ‖ccmRationalBoundedWeightedLogTrace v f t‖ ≤
        C / Real.exp t ^ p := by
    simpa [ccmRationalBoundedWeightedLogTrace, C, p] using hlarge
  have hrpow :
      Real.exp t ^ (-(p : ℝ)) ≤ Real.exp t ^ (-a) :=
    Real.rpow_le_rpow_of_exponent_le hx (neg_le_neg hap)
  have hrewrite :
      C / Real.exp t ^ p = C * Real.exp t ^ (-(p : ℝ)) := by
    rw [div_eq_mul_inv, ← Real.rpow_natCast,
      ← Real.rpow_neg (Real.exp_pos t).le]
  rw [show ‖Real.exp t ^ (-a)‖ = Real.exp t ^ (-a) by
    rw [Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (Real.exp_pos t).le _)]]
  exact hlarge'.trans_eq hrewrite |>.trans
    (mul_le_mul_of_nonneg_left hrpow hC)

private theorem ccmRationalEulerIterate_weighted_zero
    (M : ℕ) [NeZero M] (w : Fin M → ℂ)
    (f : CCMRationalArchimedeanSchwartz)
    (hphysical : w 0 * f 0 = 0) (k : ℕ) :
    w 0 * RHTower.deningerMeyerEulerIterate k f 0 = 0 := by
  cases k with
  | zero => simpa using hphysical
  | succ k =>
      rw [RHTower.deningerMeyerEulerIterate_succ,
        RHTower.deningerMeyerEulerCLM_zero, mul_zero]

private theorem ccmRationalReflectedEulerIterate_weighted_zero
    (M : ℕ) [NeZero M] (w : Fin M → ℂ)
    (g : CCMRationalArchimedeanSchwartz)
    (hdual : (∑ r : Fin M, w r) * g 0 = 0) (k : ℕ) :
    ccmRationalPeriodicFourierCoefficient M w 0 *
        RHTower.deningerMeyerReflectedEulerIterate k g 0 = 0 := by
  rw [ccmRationalPeriodicFourierCoefficient_zero]
  induction k with
  | zero => simpa using hdual
  | succ k ih =>
      rw [RHTower.deningerMeyerReflectedEulerIterate_succ,
        RHTower.deningerMeyerReflectedEulerCLM_apply]
      simp only [Complex.ofReal_zero, zero_mul, add_zero]
      simpa using neg_eq_zero.mpr ih

private theorem iteratedDeriv_ccmRationalPeriodicWeightedLogTrace_isBigO_atTop
    (M : ℕ) [NeZero M] (w : Fin M → ℂ)
    (f : CCMRationalArchimedeanSchwartz)
    (hphysical : w 0 * f 0 = 0) (k : ℕ) (a : ℝ) :
    iteratedDeriv k (ccmRationalPeriodicWeightedLogTrace M w f) =O[atTop]
      fun t : ℝ => Real.exp t ^ (-a) := by
  rw [iteratedDeriv_ccmRationalPeriodicWeightedLogTrace]
  apply ccmRationalBoundedWeightedLogTrace_isBigO_atTop
    (fun n => w (ccmRationalPeriodicResidue M n))
    (ccmRationalPeriodicWeightNorm M w)
    (fun n => Finset.single_le_sum
      (fun r _ => norm_nonneg (w r)) (Finset.mem_univ _))
    (RHTower.deningerMeyerEulerIterate k f)
  simpa [ccmRationalPeriodicResidue_zero] using
    ccmRationalEulerIterate_weighted_zero M w f hphysical k

private theorem iteratedDeriv_ccmRationalPeriodicWeightedLogTrace_isBigO_atBot
    (M : ℕ) [NeZero M] (w : Fin M → ℂ)
    (f : CCMRationalArchimedeanSchwartz)
    (hdual : (∑ r : Fin M, w r) * (𝓕 f) 0 = 0)
    (k : ℕ) (b : ℝ) :
    iteratedDeriv k (ccmRationalPeriodicWeightedLogTrace M w f) =O[atBot]
      fun t : ℝ => Real.exp t ^ b := by
  let N : ℕ := ⌈max (b + 1) 0⌉₊
  let p : ℕ := ccmRationalArchimedeanDecayExponent N
  let q : ℕ := p - 1
  let Ff : CCMRationalArchimedeanSchwartz := 𝓕 f
  let g := RHTower.deningerMeyerReflectedEulerIterate k Ff
  let B := ccmRationalPeriodicWeightNorm M w
  let C := B * ccmRationalArchimedeanDecayConstant g N * (M : ℝ) ^ q
  have hM : 0 < (M : ℝ) := by exact_mod_cast Nat.pos_of_neZero M
  have hpgt : 1 < p := ccmRationalArchimedeanDecayExponent_gt_one N
  have hpq : p = q + 1 := by dsimp [q]; omega
  have hbq : b ≤ (q : ℝ) := by
    have hceil : max (b + 1) 0 ≤ (N : ℝ) := Nat.le_ceil _
    have hNq : (N : ℝ) ≤ (q : ℝ) := by
      have hnat : N ≤ ccmRationalArchimedeanDecayExponent N - 1 := by
        simp [ccmRationalArchimedeanDecayExponent]
        omega
      exact_mod_cast hnat
    linarith [le_max_left (b + 1) 0, hceil.trans hNq]
  have hB : 0 ≤ B := by
    exact Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hC : 0 ≤ C := mul_nonneg
    (mul_nonneg hB (ccmRationalArchimedeanDecayConstant_nonneg g N))
    (pow_nonneg hM.le _)
  rw [iteratedDeriv_ccmRationalPeriodicWeightedLogTrace]
  refine (Asymptotics.IsBigOWith.of_bound (c := C) ?_).isBigO
  filter_upwards [eventually_le_atBot (0 : ℝ)] with t ht
  let s : ℝ := Real.exp (-t) * (M : ℝ)⁻¹
  have hs : 0 < s := mul_pos (Real.exp_pos (-t)) (inv_pos.mpr hM)
  have hzero :
      ccmRationalPeriodicFourierCoefficient M w 0 * g 0 = 0 := by
    exact ccmRationalReflectedEulerIterate_weighted_zero
      M w Ff (by simpa [Ff] using hdual) k
  have hlarge := ccmRationalBoundedWeightedLatticeTrace_large_bound
    (ccmRationalPeriodicFourierCoefficient M w) B
    (norm_ccmRationalPeriodicFourierCoefficient_le M w)
    g hzero N hs
  have href := ccmRationalPeriodicWeightedEulerIterate_reflection
    M w f k t
  have href' :
      ccmRationalPeriodicWeightedLogTrace M w
          (RHTower.deningerMeyerEulerIterate k f) t =
        (s : ℂ) * ccmRationalBoundedWeightedLatticeTrace
          (ccmRationalPeriodicFourierCoefficient M w) g s := by
    simpa [ccmRationalPeriodicWeightedLogReflection,
      ccmRationalPeriodicDualLogTrace_eq, s, g, Ff] using href
  have hraw :
      ‖ccmRationalPeriodicWeightedLogTrace M w
          (RHTower.deningerMeyerEulerIterate k f) t‖ ≤
        s * (B * ccmRationalArchimedeanDecayConstant g N / s ^ p) := by
    rw [href', norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hs]
    exact mul_le_mul_of_nonneg_left hlarge hs.le
  have heq :
      s * (B * ccmRationalArchimedeanDecayConstant g N / s ^ p) =
        C * Real.exp t ^ q := by
    let D := B * ccmRationalArchimedeanDecayConstant g N
    have hs0 : s ≠ 0 := ne_of_gt hs
    have hscale :
        s = (Real.exp t * (M : ℝ))⁻¹ := by
      dsimp [s]
      rw [Real.exp_neg, mul_inv_rev]
      ac_rfl
    calc
      s * (B * ccmRationalArchimedeanDecayConstant g N / s ^ p) =
          D / s ^ q := by
        dsimp [D]
        rw [hpq, pow_succ]
        field_simp
      _ = D * (Real.exp t * (M : ℝ)) ^ q := by
        rw [hscale, inv_pow, div_inv_eq_mul]
      _ = C * Real.exp t ^ q := by
        dsimp [C, D]
        rw [mul_pow]
        ring
  have hpow : Real.exp t ^ q ≤ Real.exp t ^ b := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_ge
      (Real.exp_pos t) (Real.exp_le_one_iff.mpr ht) hbq
  rw [show ‖Real.exp t ^ b‖ = Real.exp t ^ b by
    rw [Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (Real.exp_pos t).le b)]]
  exact hraw.trans_eq heq |>.trans
    (mul_le_mul_of_nonneg_left hpow hC)

/-- **Periodic weighted strong-log theorem.**  The two endpoint products are
the exact and sufficient cancellations for all logarithmic derivatives to lie
in Meyer's all-weight target. -/
theorem ccmRationalPeriodicWeightedLogTrace_strongLogDecay
    (M : ℕ) [NeZero M] (w : Fin M → ℂ)
    (f : CCMRationalArchimedeanSchwartz)
    (hphysical : w 0 * f 0 = 0)
    (hdual : (∑ r : Fin M, w r) * (𝓕 f) 0 = 0) :
    RHTower.DeningerMeyerStrongLogDecay
      (ccmRationalPeriodicWeightedLogTrace M w f) where
  smooth := contDiff_ccmRationalPeriodicWeightedLogTrace M w f
  decayTop :=
    iteratedDeriv_ccmRationalPeriodicWeightedLogTrace_isBigO_atTop
      M w f hphysical
  decayBot :=
    iteratedDeriv_ccmRationalPeriodicWeightedLogTrace_isBigO_atBot
      M w f hdual

end RHTower
end GaloisForLFunctions
