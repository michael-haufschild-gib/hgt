import GaloisForLFunctions.RHTower.CriticalContinuousChebyshevDivisorLaplaceWeld
import GaloisForLFunctions.RHTower.ZetaLogDerivResidue
import GaloisForLFunctions.RHTower.Sieve.ZetaResidueUnitRectanglePeeling

/-!
# A finite oscillation of the prime error locates the zeros

Suppose `ψ(x) − x = Σ_{ω∈S} d(ω) x^{β+iω} + O(x^{σ₀})`.  With `Z(s) = (s−1)ζ(s)`, the Mellin transform
of the remainder `R` is holomorphic on `Re s > σ₀`, and on `Re s > max(1, β)` the Abel formula
`−ζ'/ζ(s) = s ∫₁^∞ ψ(t) t^{−s−1} dt` gives

`−Z'/Z(s) = 1 + Σ_ω d(ω) s/(s − β − iω) + s ∫₁^∞ R(t) t^{−s−1} dt`.

Clearing denominators with `P(s) = Π_ω (s − β − iω)` gives `−P Z' = Z Q` with `Q` holomorphic, valid on
all of `Re s > σ₀` by the identity theorem.  Two consequences:

* a zero of `Z` with `Re ρ > σ₀` is a zero of `P`, by comparing analytic orders
  (`eq_of_zeta_eq_zero_of_expansion`);
* a nonzero coefficient forces a zero, by evaluating at `β + iω`
  (`zeta_eq_zero_of_coeff_ne_zero`).
-/

open Complex Filter Topology MeasureTheory Set Asymptotics
open ArithmeticFunction (vonMangoldt)

namespace GaloisForLFunctions.ZeroConfigurationGeometry

noncomputable section

open RHTower

/-- The prime error minus a complex oscillation. -/
def oscillationError (β : ℝ) (S : Finset ℝ) (d : ℝ → ℂ) (x : ℝ) : ℂ :=
  ((Chebyshev.psi x - x : ℝ) : ℂ) - ∑ ω ∈ S, d ω * (x : ℂ) ^ ((β : ℂ) + I * ω)

/-- The error cut off to `x > 1`: its Mellin transform is the integral over `(1, ∞)`. -/
def oscillationRemainder (β : ℝ) (S : Finset ℝ) (d : ℝ → ℂ) : ℝ → ℂ :=
  (Ioi (1 : ℝ)).indicator (oscillationError β S d)

theorem locallyIntegrableOn_oscillationError (β : ℝ) (S : Finset ℝ) (d : ℝ → ℂ) :
    LocallyIntegrableOn (oscillationError β S d) (Ioi 0) := by
  have hψ : LocallyIntegrableOn (fun x : ℝ => (Chebyshev.psi x : ℂ)) (Ioi 0) :=
    ((Chebyshev.psi_mono.locallyIntegrable (μ := volume)).locallyIntegrableOn _).mono
      (Complex.measurable_ofReal.comp Chebyshev.psi_mono.measurable).aestronglyMeasurable
      (ae_of_all _ fun x => by simp)
  have hx : LocallyIntegrableOn (fun x : ℝ => ((x : ℝ) : ℂ)) (Ioi 0) :=
    (Complex.continuous_ofReal.continuousOn).locallyIntegrableOn measurableSet_Ioi
  have hsum : LocallyIntegrableOn
      (fun x : ℝ => ∑ ω ∈ S, d ω * (x : ℂ) ^ ((β : ℂ) + I * ω)) (Ioi 0) := by
    refine ContinuousOn.locallyIntegrableOn ?_ measurableSet_Ioi
    refine continuousOn_finsetSum _ fun ω _ => continuousOn_const.mul ?_
    intro x hx
    have hx' : (x : ℂ) ∈ slitPlane := Complex.ofReal_mem_slitPlane.mpr hx
    refine ContinuousAt.continuousWithinAt ?_
    exact (Complex.continuous_ofReal.continuousAt).cpow continuousAt_const hx'
  have h := (hψ.sub hx).sub hsum
  refine h.congr (ae_of_all _ fun x => ?_)
  simp only [oscillationError, Pi.sub_apply]
  push_cast
  ring

theorem locallyIntegrableOn_oscillationRemainder (β : ℝ) (S : Finset ℝ) (d : ℝ → ℂ) :
    LocallyIntegrableOn (oscillationRemainder β S d) (Ioi 0) := by
  intro x hx
  rcases locallyIntegrableOn_oscillationError β S d x hx with ⟨t, ht, hint⟩
  exact ⟨t, ht, hint.indicator measurableSet_Ioi⟩

section Expansion

variable {β σ₀ C x₀ : ℝ} {S : Finset ℝ} {d : ℝ → ℂ}

theorem oscillationRemainder_isBigO_atTop
    (hb : ∀ x, x₀ ≤ x → ‖oscillationError β S d x‖ ≤ C * x ^ σ₀) :
    oscillationRemainder β S d =O[atTop] (fun x : ℝ => x ^ (-(-σ₀))) := by
  refine IsBigO.of_bound C ?_
  filter_upwards [eventually_ge_atTop x₀, eventually_gt_atTop (1 : ℝ)] with x hx h1
  have hmem : x ∈ Ioi (1 : ℝ) := h1
  rw [oscillationRemainder, indicator_of_mem hmem, neg_neg,
    Real.norm_of_nonneg (Real.rpow_nonneg (by linarith) _)]
  exact hb x hx

theorem oscillationRemainder_isBigO_zero (β : ℝ) (S : Finset ℝ) (d : ℝ → ℂ) (b : ℝ) :
    oscillationRemainder β S d =O[𝓝[>] 0] (fun x : ℝ => x ^ (-b)) := by
  refine (isBigO_zero _ _).congr' ?_ EventuallyEq.rfl
  have hmem : Iio (1 : ℝ) ∈ 𝓝[>] (0 : ℝ) := mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds one_pos)
  filter_upwards [hmem] with x hx
  have hnot : x ∉ Ioi (1 : ℝ) := fun h => lt_asymm (show (1 : ℝ) < x from h) (show x < 1 from hx)
  rw [oscillationRemainder, indicator_of_notMem hnot]

theorem differentiableAt_mellin_oscillationRemainder
    (hb : ∀ x, x₀ ≤ x → ‖oscillationError β S d x‖ ≤ C * x ^ σ₀) {s : ℂ} (hs : σ₀ < s.re) :
    DifferentiableAt ℂ (fun w => mellin (oscillationRemainder β S d) (-w)) s := by
  have h : DifferentiableAt ℂ (mellin (oscillationRemainder β S d)) (-s) :=
    mellin_differentiableAt_of_isBigO_rpow (a := -σ₀) (b := (-s).re - 1)
      (locallyIntegrableOn_oscillationRemainder β S d) (oscillationRemainder_isBigO_atTop hb)
      (by simpa using hs) (oscillationRemainder_isBigO_zero β S d _) (by linarith)
  exact DifferentiableAt.comp (g := mellin (oscillationRemainder β S d)) (f := fun w : ℂ => -w) s h
    (differentiable_neg s)

theorem criticalCumulative_vonMangoldt_eq_psi (t : ℝ) :
    criticalCumulative (fun n => vonMangoldt n) t = Chebyshev.psi t := by
  rw [criticalCumulative, Chebyshev.psi_eq_sum_Icc]

/-- **The Abel formula with the oscillation removed.**  For `Re s > max(1, β)`:
`s ∫ R t^{−s−1} = −ζ'/ζ(s) − s/(s−1) − Σ_ω d(ω) s/(s − β − iω)`. -/
theorem mul_mellin_oscillationRemainder {s : ℂ} (h1 : 1 < s.re) (hβ : β < s.re) :
    s * mellin (oscillationRemainder β S d) (-s) =
      LSeries (fun n => (vonMangoldt n : ℂ)) s - s / (s - 1)
        - ∑ ω ∈ S, d ω * (s / (s - ((β : ℂ) + I * ω))) := by
  have hm : mellin (oscillationRemainder β S d) (-s)
      = ∫ t in Ioi (1 : ℝ), (t : ℂ) ^ (-s - 1) * oscillationError β S d t := by
    rw [mellin]
    have hfun : (fun t : ℝ => (t : ℂ) ^ (-s - 1) • oscillationRemainder β S d t)
        = (Ioi (1 : ℝ)).indicator
            (fun t : ℝ => (t : ℂ) ^ (-s - 1) * oscillationError β S d t) := by
      funext t
      by_cases ht : t ∈ Ioi (1 : ℝ) <;> simp [oscillationRemainder, ht]
    rw [hfun, setIntegral_indicator measurableSet_Ioi,
      inter_eq_right.mpr (Ioi_subset_Ioi zero_le_one)]
  have hpt : ∀ t ∈ Ioi (1 : ℝ), (t : ℂ) ^ (-s - 1) * oscillationError β S d t
      = (criticalCumulative (fun n => vonMangoldt n) t : ℂ) * (t : ℂ) ^ (-(s + 1))
        - (t : ℂ) ^ (-s)
        - ∑ ω ∈ S, d ω * (t : ℂ) ^ ((β : ℂ) + I * ω - s - 1) := by
    intro t ht
    have ht0 : (t : ℂ) ≠ 0 := by
      exact_mod_cast (ne_of_gt (lt_trans one_pos ht))
    have e1 : (t : ℂ) ^ (-s) = (t : ℂ) ^ (-s - 1) * (t : ℂ) := by
      have h := Complex.cpow_add (x := (t : ℂ)) (-s - 1) 1 ht0
      rwa [Complex.cpow_one, show -s - 1 + 1 = -s by ring] at h
    have e2 : ∀ ω : ℝ, (t : ℂ) ^ ((β : ℂ) + I * ω - s - 1)
        = (t : ℂ) ^ ((β : ℂ) + I * ω) * (t : ℂ) ^ (-s - 1) := by
      intro ω
      rw [← Complex.cpow_add _ _ ht0]
      congr 1
      ring
    rw [oscillationError, criticalCumulative_vonMangoldt_eq_psi, e1,
      show -(s + 1) = -s - 1 by ring, Finset.sum_congr rfl fun ω _ => by rw [e2 ω],
      mul_sub, Finset.mul_sum]
    push_cast
    rw [mul_sub]
    congr 1
    · ring
    · refine Finset.sum_congr rfl fun ω _ => ?_
      ring
  have hre1 : (-s).re < -1 := by
    simp only [Complex.neg_re]
    linarith
  have hre2 : ∀ ω : ℝ, ((β : ℂ) + I * ω - s - 1).re < -1 := by
    intro ω
    simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
      Complex.I_im, Complex.ofReal_im, Complex.one_re]
    linarith
  have hi0 := integrableOn_criticalCumulative_mul_cpow h1
  have hi1 : IntegrableOn (fun t : ℝ => (t : ℂ) ^ (-s)) (Ioi 1) :=
    integrableOn_Ioi_cpow_of_lt hre1 one_pos
  have hi2 : ∀ ω ∈ S, Integrable
      (fun t : ℝ => d ω * (t : ℂ) ^ ((β : ℂ) + I * ω - s - 1)) (volume.restrict (Ioi 1)) :=
    fun ω _ => (integrableOn_Ioi_cpow_of_lt (hre2 ω) one_pos).const_mul _
  have hA : ∫ t in Ioi (1 : ℝ), (t : ℂ) ^ (-s) = 1 / (s - 1) := by
    rw [integral_Ioi_cpow_of_lt hre1 one_pos, ofReal_one, one_cpow,
      show -s + 1 = -(s - 1) by ring, neg_div_neg_eq]
  have hB : ∀ ω : ℝ, ∫ t in Ioi (1 : ℝ), d ω * (t : ℂ) ^ ((β : ℂ) + I * ω - s - 1)
      = d ω * (1 / (s - ((β : ℂ) + I * ω))) := by
    intro ω
    rw [integral_const_mul, integral_Ioi_cpow_of_lt (hre2 ω) one_pos, ofReal_one, one_cpow,
      show (β : ℂ) + I * ω - s - 1 + 1 = -(s - ((β : ℂ) + I * ω)) by ring, neg_div_neg_eq]
  have hint : ∫ t in Ioi (1 : ℝ), (t : ℂ) ^ (-s - 1) * oscillationError β S d t
      = (∫ t in Ioi (1 : ℝ), (criticalCumulative (fun n => vonMangoldt n) t : ℂ) *
            (t : ℂ) ^ (-(s + 1)))
        - 1 / (s - 1) - ∑ ω ∈ S, d ω * (1 / (s - ((β : ℂ) + I * ω))) := by
    rw [setIntegral_congr_fun measurableSet_Ioi hpt,
      integral_sub (hi0.sub hi1) (integrable_finset_sum _ hi2), integral_sub hi0 hi1,
      integral_finset_sum _ hi2, hA]
    congr 1
    exact Finset.sum_congr rfl fun ω _ => hB ω
  rw [hm, hint, vonMangoldtLSeries_eq_mul_integral_criticalCumulative h1, mul_sub, mul_sub,
    Finset.mul_sum]
  congr 1
  · congr 1
    ring
  · refine Finset.sum_congr rfl fun ω _ => ?_
    ring

/-- The denominator polynomial `P(s) = Π_ω (s − β − iω)`. -/
def oscillationDenominator (β : ℝ) (S : Finset ℝ) (s : ℂ) : ℂ :=
  ∏ ω ∈ S, (s - ((β : ℂ) + I * ω))

/-- The numerator `Q` of the logarithmic derivative of `Z`. -/
def oscillationNumerator (β : ℝ) (S : Finset ℝ) (d : ℝ → ℂ) (s : ℂ) : ℂ :=
  oscillationDenominator β S s * (1 + s * mellin (oscillationRemainder β S d) (-s))
    + ∑ ω ∈ S, d ω * s * ∏ μ ∈ S.erase ω, (s - ((β : ℂ) + I * μ))

theorem differentiable_oscillationDenominator (β : ℝ) (S : Finset ℝ) :
    Differentiable ℂ (oscillationDenominator β S) :=
  Differentiable.fun_finsetProd fun _ _ => differentiable_id.sub_const _

theorem differentiableAt_oscillationNumerator
    (hb : ∀ x, x₀ ≤ x → ‖oscillationError β S d x‖ ≤ C * x ^ σ₀) {s : ℂ} (hs : σ₀ < s.re) :
    DifferentiableAt ℂ (oscillationNumerator β S d) s := by
  refine ((differentiable_oscillationDenominator β S s).mul
    ((differentiableAt_const _).add
      (differentiableAt_id.mul (differentiableAt_mellin_oscillationRemainder hb hs)))).add ?_
  refine DifferentiableAt.fun_sum fun ω _ => ?_
  exact ((differentiableAt_const _).mul differentiableAt_id).mul
    ((Differentiable.fun_finsetProd fun _ _ => differentiable_id.sub_const _) s)

/-- **The clearing identity on the far right.** -/
theorem neg_mul_deriv_eq_of_right {s : ℂ} (h1 : 1 < s.re) (hβ : β < s.re) :
    -(oscillationDenominator β S s * deriv zetaResidueUnit s)
      = zetaResidueUnit s * oscillationNumerator β S d s := by
  have hs1 : s ≠ 1 := fun h => by
    rw [h, Complex.one_re] at h1
    exact lt_irrefl _ h1
  have hs1' : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  have hζ : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_le_re h1.le
  have hZ : zetaResidueUnit s = (s - 1) * riemannZeta s :=
    (zetaResidueUnit_eventuallyEq hs1).eq_of_nhds
  have hdZ : deriv zetaResidueUnit s = riemannZeta s + (s - 1) * deriv riemannZeta s := by
    rw [(zetaResidueUnit_eventuallyEq hs1).deriv_eq]
    have h : HasDerivAt (fun z => (z - 1) * riemannZeta z)
        (1 * riemannZeta s + (s - 1) * deriv riemannZeta s) s :=
      ((hasDerivAt_id s).sub_const 1).mul (differentiableAt_riemannZeta hs1).hasDerivAt
    rw [h.deriv, one_mul]
  have hL : LSeries (fun n => (vonMangoldt n : ℂ)) s = -deriv riemannZeta s / riemannZeta s :=
    ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div h1
  have hne : ∀ ω : ℝ, s - ((β : ℂ) + I * ω) ≠ 0 := by
    intro ω h
    have := congrArg Complex.re h
    simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
      Complex.I_im, Complex.ofReal_im, Complex.zero_re] at this
    linarith
  have hPe : ∀ ω ∈ S, ∏ μ ∈ S.erase ω, (s - ((β : ℂ) + I * μ))
      = oscillationDenominator β S s / (s - ((β : ℂ) + I * ω)) := by
    intro ω hω
    rw [oscillationDenominator, ← Finset.mul_prod_erase S _ hω, mul_div_cancel_left₀ _ (hne ω)]
  have hsum : ∑ ω ∈ S, d ω * s * ∏ μ ∈ S.erase ω, (s - ((β : ℂ) + I * μ))
      = oscillationDenominator β S s * ∑ ω ∈ S, d ω * (s / (s - ((β : ℂ) + I * ω))) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun ω hω => ?_
    rw [hPe ω hω]
    ring
  rw [oscillationNumerator, hsum, mul_mellin_oscillationRemainder h1 hβ, hL, hZ, hdZ]
  generalize oscillationDenominator β S s = P
  generalize (∑ ω ∈ S, d ω * (s / (s - ((β : ℂ) + I * ω)))) = B
  generalize deriv riemannZeta s = z'
  field_simp
  ring

/-- **The clearing identity on `Re s > σ₀`**, by the identity theorem. -/
theorem neg_mul_deriv_eq
    (hb : ∀ x, x₀ ≤ x → ‖oscillationError β S d x‖ ≤ C * x ^ σ₀) {s : ℂ} (hs : σ₀ < s.re) :
    -(oscillationDenominator β S s * deriv zetaResidueUnit s)
      = zetaResidueUnit s * oscillationNumerator β S d s := by
  set U : Set ℂ := {w | σ₀ < w.re} with hU
  have hUo : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  set F : ℂ → ℂ := fun w => -(oscillationDenominator β S w * deriv zetaResidueUnit w)
      - zetaResidueUnit w * oscillationNumerator β S d w with hF
  have hFd : DifferentiableOn ℂ F U := by
    intro w hw
    refine DifferentiableAt.differentiableWithinAt ?_
    refine (((differentiable_oscillationDenominator β S w).mul ?_).neg).sub
      ((analyticAt_zetaResidueUnit w).differentiableAt.mul
        (differentiableAt_oscillationNumerator hb hw))
    exact (analyticAt_zetaResidueUnit w).deriv.differentiableAt
  have hFa : AnalyticOnNhd ℂ F U := hFd.analyticOnNhd hUo
  set r : ℝ := max (max 1 β) σ₀ + 1 with hr
  have hr1 : 1 < r := by
    have := le_max_left (max 1 β) σ₀
    have := le_max_left 1 β
    rw [hr]
    linarith
  have hrβ : β < r := by
    have := le_max_left (max 1 β) σ₀
    have := le_max_right 1 β
    rw [hr]
    linarith
  have hrσ : σ₀ < r := by
    have := le_max_right (max 1 β) σ₀
    rw [hr]
    linarith
  have hz₀ : (r : ℂ) ∈ U := by simpa [hU] using hrσ
  have hV : {w : ℂ | 1 < w.re ∧ β < w.re} ∈ 𝓝 (r : ℂ) := by
    refine (IsOpen.inter (isOpen_lt continuous_const Complex.continuous_re)
      (isOpen_lt continuous_const Complex.continuous_re)).mem_nhds ?_
    simpa using ⟨hr1, hrβ⟩
  have hev : F =ᶠ[𝓝 (r : ℂ)] 0 := by
    filter_upwards [hV] with w hw
    simp only [hF, Pi.zero_apply]
    rw [neg_mul_deriv_eq_of_right hw.1 hw.2, sub_self]
  have hEq := hFa.eqOn_zero_of_preconnected_of_eventuallyEq_zero
    (convex_halfSpace_re_gt σ₀).isPreconnected hz₀ hev
  have h0 : F s = 0 := hEq hs
  exact sub_eq_zero.mp h0

/-- **Zero location.**  Every zero right of `σ₀` is of the form `β + iω`, `ω ∈ S`: otherwise the
clearing identity makes the order of `Z'` at least the order of `Z`. -/
theorem eq_of_zeta_eq_zero_of_expansion
    (hb : ∀ x, x₀ ≤ x → ‖oscillationError β S d x‖ ≤ C * x ^ σ₀) {ρ : ℂ} (hρ : σ₀ < ρ.re)
    (hρ1 : ρ ≠ 1) (hζ : riemannZeta ρ = 0) : ∃ ω ∈ S, ρ = (β : ℂ) + I * ω := by
  by_contra hne
  push Not at hne
  have hP : oscillationDenominator β S ρ ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun ω hω => sub_ne_zero.mpr (hne ω hω)
  have hZ0 : zetaResidueUnit ρ = 0 := by
    rw [(zetaResidueUnit_eventuallyEq hρ1).eq_of_nhds, hζ, mul_zero]
  have hZa := analyticAt_zetaResidueUnit ρ
  have hdZa : AnalyticAt ℂ (deriv zetaResidueUnit) ρ := hZa.deriv
  have hPa : AnalyticAt ℂ (oscillationDenominator β S) ρ :=
    (differentiable_oscillationDenominator β S).analyticAt ρ
  have hUo : IsOpen {w : ℂ | σ₀ < w.re} := isOpen_lt continuous_const Complex.continuous_re
  have hQa : AnalyticAt ℂ (oscillationNumerator β S d) ρ := by
    have hd : DifferentiableOn ℂ (oscillationNumerator β S d) {w : ℂ | σ₀ < w.re} :=
      fun w hw => (differentiableAt_oscillationNumerator hb hw).differentiableWithinAt
    exact hd.analyticOnNhd hUo ρ hρ
  have hev : (fun w => oscillationDenominator β S w * deriv zetaResidueUnit w)
      =ᶠ[𝓝 ρ] -(zetaResidueUnit * oscillationNumerator β S d) := by
    filter_upwards [hUo.mem_nhds hρ] with w hw
    have h := neg_mul_deriv_eq hb (s := w) hw
    simp only [Pi.neg_apply, Pi.mul_apply]
    rw [← h, neg_neg]
  have hord := analyticOrderAt_congr hev
  have hleft : analyticOrderAt (fun w => oscillationDenominator β S w * deriv zetaResidueUnit w) ρ
      = analyticOrderAt (deriv zetaResidueUnit) ρ := by
    have h := analyticOrderAt_mul (𝕜 := ℂ) hPa hdZa
    have hP0 : analyticOrderAt (oscillationDenominator β S) ρ = 0 :=
      hPa.analyticOrderAt_eq_zero.mpr hP
    rw [hP0, zero_add] at h
    exact h
  have hright : analyticOrderAt (-(zetaResidueUnit * oscillationNumerator β S d)) ρ
      = analyticOrderAt zetaResidueUnit ρ + analyticOrderAt (oscillationNumerator β S d) ρ := by
    rw [analyticOrderAt_neg, analyticOrderAt_mul hZa hQa]
  have hstep : analyticOrderAt (deriv zetaResidueUnit) ρ + 1 = analyticOrderAt zetaResidueUnit ρ := by
    have h := hZa.analyticOrderAt_deriv_add_one
    simpa [hZ0] using h
  have htop : analyticOrderAt zetaResidueUnit ρ ≠ ⊤ := Sieve.zetaResidueUnit_order_ne_top ρ
  rw [hleft, hright] at hord
  rw [hord] at hstep
  generalize analyticOrderAt zetaResidueUnit ρ = m at hstep htop
  generalize analyticOrderAt (oscillationNumerator β S d) ρ = q at hstep
  induction m using ENat.recTopCoe with
  | top => exact htop rfl
  | coe m =>
    induction q using ENat.recTopCoe with
    | top => simp at hstep
    | coe q =>
      norm_cast at hstep
      omega

/-- **Forced zero.**  A nonzero coefficient at `ω₀` forces `ζ(β + iω₀) = 0`: at `s₀ = β + iω₀` the
clearing identity reads `0 = Z(s₀) d(ω₀) s₀ Π_{μ≠ω₀} i(ω₀ − μ)`. -/
theorem zeta_eq_zero_of_coeff_ne_zero
    (hb : ∀ x, x₀ ≤ x → ‖oscillationError β S d x‖ ≤ C * x ^ σ₀) {ω₀ : ℝ} (hω₀ : ω₀ ∈ S)
    (hd : d ω₀ ≠ 0) (hσβ : σ₀ < β) (hβ0 : 0 < β) :
    riemannZeta ((β : ℂ) + I * ω₀) = 0 := by
  set s₀ : ℂ := (β : ℂ) + I * ω₀ with hs₀
  have hre : s₀.re = β := by simp [hs₀]
  have hs₀0 : s₀ ≠ 0 := fun h => by
    rw [h, Complex.zero_re] at hre
    linarith
  have hP : oscillationDenominator β S s₀ = 0 :=
    Finset.prod_eq_zero hω₀ (sub_self _)
  have hQ : oscillationNumerator β S d s₀
      = d ω₀ * s₀ * ∏ μ ∈ S.erase ω₀, (s₀ - ((β : ℂ) + I * μ)) := by
    rw [oscillationNumerator, hP, zero_mul, zero_add]
    refine Finset.sum_eq_single ω₀ (fun ω hω hne => ?_) (fun h => absurd hω₀ h)
    have hmem : ω₀ ∈ S.erase ω := Finset.mem_erase.mpr ⟨hne.symm, hω₀⟩
    rw [Finset.prod_eq_zero hmem (sub_self _), mul_zero]
  have hQ0 : oscillationNumerator β S d s₀ ≠ 0 := by
    rw [hQ]
    refine mul_ne_zero (mul_ne_zero hd hs₀0) (Finset.prod_ne_zero_iff.mpr fun μ hμ => ?_)
    have hμne : μ ≠ ω₀ := (Finset.mem_erase.mp hμ).1
    intro h
    have him := congrArg Complex.im h
    simp only [hs₀, Complex.sub_im, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
      Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.zero_im] at him
    apply hμne
    linarith
  have hid := neg_mul_deriv_eq hb (s := s₀) (by rw [hre]; exact hσβ)
  rw [hP, zero_mul, neg_zero] at hid
  have hZ0 : zetaResidueUnit s₀ = 0 := by
    rcases mul_eq_zero.mp hid.symm with h | h
    · exact h
    · exact absurd h hQ0
  have hs₀1 : s₀ ≠ 1 := fun h => by
    rw [h, zetaResidueUnit_one] at hZ0
    exact one_ne_zero hZ0
  rw [(zetaResidueUnit_eventuallyEq hs₀1).eq_of_nhds] at hZ0
  exact (mul_eq_zero.mp hZ0).resolve_left (sub_ne_zero.mpr hs₀1)

end Expansion

end

end GaloisForLFunctions.ZeroConfigurationGeometry
