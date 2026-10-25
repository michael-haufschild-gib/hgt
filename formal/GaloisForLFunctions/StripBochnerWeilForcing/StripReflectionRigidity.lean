import GaloisForLFunctions.StripBochnerWeilForcing.CollectivePoleRepulsion
import GaloisForLFunctions.RHTower.RefundedComplexStray
import GaloisForLFunctions.RHTower.HardyTheorem
import GaloisForLFunctions.RHTower.LandauAbscissaWitnesses
import GaloisForLFunctions.RHTower.LaplaceAbscissaExists
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Reference-Free Strip Reflection Rigidity and the Exact `κ = 1` vs `κ ≥ 2` Phase Transition

Direct coupling of multiplicative positivity (`Re(−F'/F) ≥ 0` / positive-definite vertical sections)
with functional-equation reflection `Λ(1 − s) = Λ(s)` across the critical strip `0 < Re s < 1`
— **without** subtracting any reference function such as `ξ'/ξ` — exposes an exact pole-order phase
transition at `κ = 1`:

1. **Reference-free critical-strip reflection law (`completedPositiveSystem_strip_reflection`,
   `completedPositiveSystem_strip_reflection_digamma`)**: for the canonical meromorphic continuation
   `F_ext(s) = Λ(s) / ((s(s − 1))^κ Γ_ℝ(s)^d)` of any `CompletedPositiveSystem κ d F Λ`, at every
   `s` in `0 < Re s < 1` with `Λ(s) ≠ 0`, both the `κ`-pole rational term and `logDeriv Λ` cancel
   identically under `s ↔ 1 − s`, leaving pure archimedean reflection
   `(−logDeriv F_ext(s)) + (−logDeriv F_ext(1 − s)) = d(logDeriv Γ_ℝ(s) + logDeriv Γ_ℝ(1 − s))`.
2. **Exact `κ ≥ 2` off-critical realizations (`exists_completedPositiveSystem_two_real_offCritical`,
   `exists_completedPositiveSystem_two_complex_offCritical`)**: already at `(κ, d) = (2, 1)`,
   `CompletedPositiveSystem 2 1` unconditionally admits both real off-critical pairs `β, 1 − β` for
   every `β ∈ (0, 1) \ {1/2}` and genuinely complex off-critical quartets `1/2 ± a ± i γ₀` (`0 < a ≤ 1/4`,
   with `γ₀ > 0` supplied unconditionally by Hardy's theorem). Hence `κ = 1` is the unique pole
   order at which critical-line forcing is not false.
3. **Reference-free impossibility of entire `κ = 0` Laplace-positive completions
   (`no_entire_laplace_completed_system`)**: archimedean reflection negativity at `s = 1/2`
   (`Re(logDeriv Γ_ℝ(1/2)) < 0`) combined with Landau continuation along `(0, ∞)` rules out every
   nonzero entire `Λ(1 − s) = ε Λ(s)` (`ε ≠ 0`) satisfying `−logDeriv Λ + d logDeriv Γ_ℝ = laplaceReal ν`
   on a right ray, with no finite-order assumption on `Λ`.
4. **Universal archimedean real-zero budget (`real_zero_archimedean_budget`)**: evaluating Hadamard
   positivity against `Re(logDeriv Γ_ℝ(2)) = (−γ − log π)/2 < −5/6` proves for every
   `CompletedPositiveSystem κ d F Λ` and every finite set `X ⊂ (1/2, 1]` of off-central real points
   `4 ord_{1/2}(Λ) + 8 ∑_{x ∈ X} ord_x(Λ) + 5 d < 9 κ`. This forces `5 d < 9 κ` (ruling out `κ = 0`
   and forcing `d = 1` whenever `κ = 1`) and eliminates all real zeros on `ℝ` (both Siegel-type zeros
   in `(0, 1) \ {1/2}` and central vanishing at `s = 1/2`) in every `CompletedPositiveSystem 1 d F Λ`.
-/

open Complex Filter Topology Set MeasureTheory Finset
open GaloisForLFunctions.EntireZeroDivisor
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace GaloisForLFunctions.StripBochnerWeilForcing

open MultiplicativePositivityGeometry
open RHTower RHTower.CompletionZeroPairs RHTower.WeilLineIntegral
open scoped ENNReal

/-! ### 1. Reference-free critical-strip reflection identity -/

/-- Canonical pole-and-Gamma-stripped meromorphic continuation of `F` from `{Re s > 1}` to
`{Re s > 0} \ {1}`: `extFactor κ d Λ s = Λ(s) / ((s(s − 1))^κ Γ_ℝ(s)^d)`. -/
def CompletedPositiveSystem.extFactor (κ d : ℕ) (Λ : ℂ → ℂ) (s : ℂ) : ℂ :=
  Λ s / ((s * (s - 1)) ^ κ * Complex.Gammaℝ s ^ d)

namespace CompletedPositiveSystem

theorem extFactor_eq_of_one_lt_re {κ d : ℕ} {F Λ : ℂ → ℂ}
    (hS : CompletedPositiveSystem κ d F Λ) {s : ℂ} (hs : 1 < s.re) :
    extFactor κ d Λ s = F s := by
  unfold extFactor
  rw [hS.completed_eq s hs]
  have hs0 : s ≠ 0 := fun h => by rw [h, Complex.zero_re] at hs; linarith
  have hs1 : s - 1 ≠ 0 := sub_ne_zero.mpr fun h => by rw [h, Complex.one_re] at hs; linarith
  have hΓ : Complex.Gammaℝ s ≠ 0 := Complex.Gammaℝ_ne_zero_of_re_pos (by linarith)
  exact mul_div_cancel_left₀ (F s)
    (mul_ne_zero (pow_ne_zero κ (mul_ne_zero hs0 hs1)) (pow_ne_zero d hΓ))

/-- Logarithmic derivative of `extFactor κ d Λ` at any `s` with `Re s > 0`, `s ≠ 1`, and
`Λ(s) ≠ 0`. -/
theorem neg_logDeriv_extFactor_eq (κ d : ℕ) {Λ : ℂ → ℂ} (hΛ : Differentiable ℂ Λ)
    {s : ℂ} (hs0_re : 0 < s.re) (hs1 : s ≠ 1) (hΛs : Λ s ≠ 0) :
    -logDeriv (extFactor κ d Λ) s =
      (κ : ℂ) * (1 / s + 1 / (s - 1)) + (d : ℂ) * logDeriv Complex.Gammaℝ s - logDeriv Λ s := by
  have hs0 : s ≠ 0 := fun h => by rw [h, Complex.zero_re] at hs0_re; linarith
  have hs1' : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  have hq0 : s * (s - 1) ≠ 0 := mul_ne_zero hs0 hs1'
  have hΓ0 : Complex.Gammaℝ s ≠ 0 := Complex.Gammaℝ_ne_zero_of_re_pos hs0_re
  have hqd : DifferentiableAt ℂ (fun w : ℂ => w * (w - 1)) s :=
    differentiableAt_id.mul (differentiableAt_id.sub_const 1)
  have hΓd : DifferentiableAt ℂ Complex.Gammaℝ s :=
    GaloisForLFunctions.differentiableAt_Gammaℝ hs0_re
  unfold extFactor
  rw [logDeriv_div (f := Λ) (g := fun w => (w * (w - 1)) ^ κ * Complex.Gammaℝ w ^ d) s
        hΛs (mul_ne_zero (pow_ne_zero κ hq0) (pow_ne_zero d hΓ0))
        (hΛ s) ((hqd.fun_pow κ).mul (hΓd.fun_pow d)),
      logDeriv_mul (f := fun w => (w * (w - 1)) ^ κ) (g := fun w => Complex.Gammaℝ w ^ d) s
        (pow_ne_zero κ hq0) (pow_ne_zero d hΓ0) (hqd.fun_pow κ) (hΓd.fun_pow d),
      logDeriv_fun_pow hqd κ, logDeriv_fun_pow hΓd d]
  have hq_ld : logDeriv (fun w : ℂ => w * (w - 1)) s = 1 / s + 1 / (s - 1) := by
    have hsub : DifferentiableAt ℂ (fun w : ℂ => w - 1) s := differentiableAt_id.sub_const 1
    rw [logDeriv_mul (f := fun w : ℂ => w) (g := fun w : ℂ => w - 1) s hs0 hs1'
      differentiableAt_id hsub]
    congr 1
    · rw [logDeriv_apply, deriv_id'', one_div]
    · rw [logDeriv_apply, deriv_sub_const, deriv_id'', one_div]
  rw [hq_ld]
  ring

end CompletedPositiveSystem

/-- **Reference-free critical-strip reflection identity.** In any `CompletedPositiveSystem κ d F Λ`,
at every point `s` in the open critical strip `0 < Re s < 1` with `Λ(s) ≠ 0`, both the `κ`-pole
rational contribution and `logDeriv Λ` cancel identically under `s ↔ 1 − s` without subtracting any
reference `ξ'/ξ`. -/
theorem completedPositiveSystem_strip_reflection {κ d : ℕ} {F Λ : ℂ → ℂ}
    (hS : CompletedPositiveSystem κ d F Λ) {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1)
    (hΛs : Λ s ≠ 0) :
    (-logDeriv (CompletedPositiveSystem.extFactor κ d Λ) s) +
      (-logDeriv (CompletedPositiveSystem.extFactor κ d Λ) (1 - s)) =
      (d : ℂ) * (logDeriv Complex.Gammaℝ s + logDeriv Complex.Gammaℝ (1 - s)) := by
  have hs_ne1 : s ≠ 1 := fun h => by rw [h, Complex.one_re] at hs1; linarith
  have h1s_re : 0 < (1 - s).re := by simp; linarith
  have h1s_ne1 : 1 - s ≠ 1 := fun h => by
    have := congrArg Complex.re h; simp at this; linarith
  have hΛ1s : Λ (1 - s) ≠ 0 := by rwa [hS.sym_Λ]
  rw [CompletedPositiveSystem.neg_logDeriv_extFactor_eq κ d hS.entire_Λ hs0 hs_ne1 hΛs,
      CompletedPositiveSystem.neg_logDeriv_extFactor_eq κ d hS.entire_Λ h1s_re h1s_ne1 hΛ1s]
  have hlogΛ : logDeriv Λ (1 - s) = -logDeriv Λ s :=
    RHTower.CompletionZeroPairs.logDeriv_one_sub hS.entire_Λ one_ne_zero
      (fun w => by rw [hS.sym_Λ w, one_mul]) s
  have hpole : (1 / s + 1 / (s - 1)) + (1 / (1 - s) + 1 / ((1 - s) - 1)) = 0 := by
    have h1 : (1 - s) - 1 = -s := by ring
    have h2 : 1 - s = -(s - 1) := by ring
    rw [h1, h2, one_div_neg_eq_neg_one_div, one_div_neg_eq_neg_one_div]
    ring
  rw [hlogΛ]
  linear_combination (κ : ℂ) * hpole

/-- Digamma form of the reference-free critical-strip reflection identity on `0 < Re s < 1`. -/
theorem completedPositiveSystem_strip_reflection_digamma {κ d : ℕ} {F Λ : ℂ → ℂ}
    (hS : CompletedPositiveSystem κ d F Λ) {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1)
    (hΛs : Λ s ≠ 0) :
    (-logDeriv (CompletedPositiveSystem.extFactor κ d Λ) s) +
      (-logDeriv (CompletedPositiveSystem.extFactor κ d Λ) (1 - s)) =
      ((d : ℂ) / 2) *
        (Complex.digamma (s / 2) + Complex.digamma ((1 - s) / 2) -
          2 * ((Real.log Real.pi : ℝ) : ℂ)) := by
  have h1s_re : 0 < (1 - s).re := by simp; linarith
  rw [completedPositiveSystem_strip_reflection hS hs0 hs1 hΛs,
      RHTower.logDeriv_Gammaℝ_digamma hs0,
      RHTower.logDeriv_Gammaℝ_digamma h1s_re]
  ring

/-! ### 2. Exact `κ ≥ 2` off-critical realizations inside `CompletedPositiveSystem 2 1` -/

private theorem re_one_div_eq_laplace_cos' (a b : ℝ) (ha : 0 < a) :
    (1 / ((a : ℂ) + (b : ℂ) * I)).re =
      ∫ t : ℝ in Ioi 0, Real.exp (-a * t) * Real.cos (b * t) := by
  set w : ℂ := -((a : ℂ) + (b : ℂ) * I)
  have hw_re : w.re < 0 := by simp [w]; linarith
  have hint_c : IntegrableOn (fun t : ℝ => Complex.exp (w * t)) (Ioi 0) :=
    integrableOn_exp_mul_complex_Ioi hw_re 0
  have hval := integral_exp_mul_complex_Ioi hw_re 0
  have hrhs_eq : -Complex.exp (w * (0 : ℝ)) / w = 1 / ((a : ℂ) + (b : ℂ) * I) := by
    rw [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
    dsimp only [w]
    rw [div_neg, neg_div, neg_neg]
  rw [hrhs_eq] at hval
  have hre_int : (∫ t : ℝ in Ioi 0, Complex.exp (w * t)).re =
      ∫ t : ℝ in Ioi 0, (Complex.exp (w * t)).re :=
    (Complex.reCLM.integral_comp_comm hint_c).symm
  rw [← hval, hre_int]
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  have hw_t_re : (w * (t : ℂ)).re = -a * t := by simp [w]
  have hw_t_im : (w * (t : ℂ)).im = -(b * t) := by simp [w]
  rw [Complex.exp_re, hw_t_re, hw_t_im, Real.cos_neg]

/-- General Laplace–Bochner positivity criterion: any profile `φ(u) = ∫_{(0,∞)} w(t) cos(tu) dt`
with continuous `w ≥ 0` on `(0, ∞)` dominated by `C e^{−a t}` (`a > 0`) is even positive definite. -/
private theorem isEvenPosDef_of_laplace_cos_nonneg {w φ : ℝ → ℝ} {C a : ℝ}
    (ha : 0 < a) (_hC : 0 ≤ C) (hw_cont : Continuous w)
    (hw_nn : ∀ t : ℝ, 0 < t → 0 ≤ w t)
    (hw_le : ∀ t : ℝ, 0 < t → w t ≤ C * Real.exp (-a * t))
    (hφ : ∀ u : ℝ, φ u = ∫ t : ℝ in Ioi 0, w t * Real.cos (t * u)) :
    IsEvenPosDef φ := by
  have hint_dom : IntegrableOn (fun t : ℝ => C * Real.exp (-a * t)) (Ioi 0) :=
    (integrableOn_exp_mul_Ioi (by linarith) 0).const_mul C
  have hint_ker : ∀ u : ℝ,
      IntegrableOn (fun t : ℝ => w t * Real.cos (t * u)) (Ioi 0) := by
    intro u
    refine Integrable.mono' hint_dom
      ((Continuous.aestronglyMeasurable (by fun_prop)).restrict) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    change 0 < t at ht
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hw_nn t ht)]
    exact (mul_le_of_le_one_right (hw_nn t ht) (Real.abs_cos_le_one _)).trans (hw_le t ht)
  refine ⟨fun u => ?_, fun n x c => ?_⟩
  · rw [hφ (-u), hφ u]
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    rw [mul_neg, Real.cos_neg]
  · have hsum_int : ∑ i, ∑ j, c i * c j * φ (x i - x j) =
        ∫ t : ℝ in Ioi 0, w t * ∑ i, ∑ j, c i * c j * Real.cos (t * (x i - x j)) := by
      simp_rw [hφ, ← integral_const_mul]
      have h1 : ∀ i : Fin n,
          ∑ j : Fin n, ∫ t : ℝ in Ioi 0, c i * c j * (w t * Real.cos (t * (x i - x j))) =
          ∫ t : ℝ in Ioi 0, ∑ j : Fin n, c i * c j * (w t * Real.cos (t * (x i - x j))) :=
        fun i => (integral_finsetSum Finset.univ fun j _ =>
          (hint_ker (x i - x j)).const_mul (c i * c j)).symm
      simp_rw [h1]
      rw [← integral_finsetSum Finset.univ fun i _ =>
        integrable_finsetSum Finset.univ fun j _ =>
          (hint_ker (x i - x j)).const_mul (c i * c j)]
      refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
      simp_rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [hsum_int]
    refine integral_nonneg_of_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    change 0 < t at ht
    refine mul_nonneg (hw_nn t ht) ?_
    rw [gram_cos_eq]
    positivity

private theorem isEvenPosDef_add' {φ ψ : ℝ → ℝ} (hφ : IsEvenPosDef φ) (hψ : IsEvenPosDef ψ) :
    IsEvenPosDef (fun u => φ u + ψ u) where
  even u := by rw [hφ.even, hψ.even]
  posDef n x c := by
    have h : (∑ i, ∑ j, c i * c j * (φ (x i - x j) + ψ (x i - x j))) =
        (∑ i, ∑ j, c i * c j * φ (x i - x j)) + ∑ i, ∑ j, c i * c j * ψ (x i - x j) := by
      simp_rw [mul_add, Finset.sum_add_distrib]
    rw [h]
    exact add_nonneg (hφ.posDef n x c) (hψ.posDef n x c)

/-- Symmetric quadratic `(s − β)(s − (1 − β))` realizing a real zero pair in `(0, 1)`. -/
def realPairPoly (β : ℝ) (s : ℂ) : ℂ :=
  (s - (β : ℂ)) * (s - ((1 - β : ℝ) : ℂ))

/-- Uncompleted rational twist `(s − β)(s − (1 − β)) / (s(s − 1))` spending one unit of pole
budget. -/
def realPairFactor (β : ℝ) (s : ℂ) : ℂ :=
  realPairPoly β s / (s * (s - 1))

private theorem isEvenPosDef_realPairFactor {β σ : ℝ}
    (hβ0 : 0 < β) (hβ1 : β < 1) (hσ : 1 < σ) :
    IsEvenPosDef (fun u : ℝ =>
      (-logDeriv (realPairFactor β) ((σ : ℂ) + (u : ℂ) * I)).re) := by
  let w : ℝ → ℝ := fun t =>
    Real.exp (-σ * t) * (Real.exp (β * t) - 1) * (Real.exp ((1 - β) * t) - 1)
  refine isEvenPosDef_of_laplace_cos_nonneg (w := w) (a := σ - 1) (C := 2)
    (by linarith) (by norm_num) (by dsimp only [w]; fun_prop)
    (fun t ht => ?_) (fun t ht => ?_) (fun u => ?_)
  · have h1 : 0 ≤ Real.exp (β * t) - 1 :=
      sub_nonneg.mpr (Real.one_le_exp (by nlinarith))
    have h2 : 0 ≤ Real.exp ((1 - β) * t) - 1 :=
      sub_nonneg.mpr (Real.one_le_exp (by nlinarith))
    exact mul_nonneg (mul_nonneg (Real.exp_pos _).le h1) h2
  · have hexp_expand : w t =
        Real.exp (-(σ - 1) * t) + Real.exp (-σ * t) -
          Real.exp (-(σ - β) * t) - Real.exp (-(σ - (1 - β)) * t) := by
      dsimp only [w]
      have e1 : -σ * t + β * t + (1 - β) * t = -(σ - 1) * t := by ring
      have e2 : -σ * t + β * t = -(σ - β) * t := by ring
      have e3 : -σ * t + (1 - β) * t = -(σ - (1 - β)) * t := by ring
      calc Real.exp (-σ * t) * (Real.exp (β * t) - 1) * (Real.exp ((1 - β) * t) - 1)
          = Real.exp (-σ * t) * Real.exp (β * t) * Real.exp ((1 - β) * t) +
              Real.exp (-σ * t) -
              Real.exp (-σ * t) * Real.exp (β * t) -
              Real.exp (-σ * t) * Real.exp ((1 - β) * t) := by ring
        _ = Real.exp (-(σ - 1) * t) + Real.exp (-σ * t) -
              Real.exp (-(σ - β) * t) - Real.exp (-(σ - (1 - β)) * t) := by
            rw [← Real.exp_add, ← Real.exp_add, e1, ← Real.exp_add, e2, ← Real.exp_add, e3]
    rw [hexp_expand]
    have hle_exp : Real.exp (-σ * t) ≤ Real.exp (-(σ - 1) * t) :=
      Real.exp_le_exp.mpr (by nlinarith)
    linarith [Real.exp_pos (-(σ - β) * t), Real.exp_pos (-(σ - (1 - β)) * t)]
  · set s : ℂ := (σ : ℂ) + (u : ℂ) * I with hs_def
    have hs : 1 < s.re := by simp [hs_def]; exact hσ
    have hs0 : s ≠ 0 := fun h => by rw [h, Complex.zero_re] at hs; linarith
    have hs1 : s - 1 ≠ 0 := sub_ne_zero.mpr fun h => by rw [h, Complex.one_re] at hs; linarith
    have hn1 : s - (β : ℂ) ≠ 0 := fun h => by
      have := congrArg Complex.re h; simp [hs_def] at this; linarith
    have hn2 : s - ((1 - β : ℝ) : ℂ) ≠ 0 := fun h => by
      have := congrArg Complex.re h; simp [hs_def] at this; linarith
    have hd_lin : ∀ c : ℂ, logDeriv (fun z : ℂ => z - c) s = 1 / (s - c) := fun c => by
      rw [logDeriv_apply, deriv_sub_const, deriv_id'', one_div]
    have hld : -logDeriv (realPairFactor β) s =
        1 / s + 1 / (s - 1) - 1 / (s - (β : ℂ)) - 1 / (s - ((1 - β : ℝ) : ℂ)) := by
      unfold realPairFactor realPairPoly
      rw [logDeriv_div
            (f := fun z : ℂ => (z - (β : ℂ)) * (z - ((1 - β : ℝ) : ℂ)))
            (g := fun z : ℂ => z * (z - 1))
            s (mul_ne_zero hn1 hn2) (mul_ne_zero hs0 hs1)
            ((differentiableAt_id.sub_const (β : ℂ)).mul
              (differentiableAt_id.sub_const ((1 - β : ℝ) : ℂ)))
            (differentiableAt_id.mul (differentiableAt_id.sub_const (1 : ℂ))),
          logDeriv_mul
            (f := fun z : ℂ => z - (β : ℂ))
            (g := fun z : ℂ => z - ((1 - β : ℝ) : ℂ))
            s hn1 hn2
            (differentiableAt_id.sub_const (β : ℂ))
            (differentiableAt_id.sub_const ((1 - β : ℝ) : ℂ)),
          logDeriv_mul
            (f := fun z : ℂ => z)
            (g := fun z : ℂ => z - 1)
            s hs0 hs1 differentiableAt_id (differentiableAt_id.sub_const (1 : ℂ)),
          hd_lin, hd_lin, hd_lin]
      have hid' : logDeriv (fun z : ℂ => z) s = 1 / s := by
        rw [logDeriv_apply, deriv_id'', one_div]
      rw [hid']
      ring
    have e1 : s - 1 = (((σ - 1 : ℝ) : ℂ) + (u : ℂ) * I) := by rw [hs_def]; push_cast; ring
    have e2 : s - (β : ℂ) = (((σ - β : ℝ) : ℂ) + (u : ℂ) * I) := by rw [hs_def]; push_cast; ring
    have e3 : s - ((1 - β : ℝ) : ℂ) = (((σ - (1 - β) : ℝ) : ℂ) + (u : ℂ) * I) := by
      rw [hs_def]; push_cast; ring
    rw [hld, e1, e2, e3, hs_def, Complex.sub_re, Complex.sub_re, Complex.add_re,
        re_one_div_eq_laplace_cos' σ u (by linarith),
        re_one_div_eq_laplace_cos' (σ - 1) u (by linarith),
        re_one_div_eq_laplace_cos' (σ - β) u (by linarith),
        re_one_div_eq_laplace_cos' (σ - (1 - β)) u (by linarith)]
    have hint : ∀ a' : ℝ, 0 < a' →
        IntegrableOn (fun t : ℝ => Real.exp (-a' * t) * Real.cos (u * t)) (Ioi 0) := by
      intro a' ha'
      refine Integrable.mono' (integrableOn_exp_mul_Ioi (by linarith) 0)
        ((Continuous.aestronglyMeasurable (by fun_prop)).restrict)
        (Eventually.of_forall fun t => ?_)
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
      exact mul_le_of_le_one_right (Real.exp_pos _).le (Real.abs_cos_le_one _)
    have hi0 := hint σ (by linarith)
    have hi1 := hint (σ - 1) (by linarith)
    have hi2 := hint (σ - β) (by linarith)
    have hi3 := hint (σ - (1 - β)) (by linarith)
    rw [← integral_add hi0 hi1, ← integral_sub (hi0.add hi1) hi2,
        ← integral_sub ((hi0.add hi1).sub hi2) hi3]
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    dsimp only [w]
    have c1 : -σ * t + β * t + (1 - β) * t = -(σ - 1) * t := by ring
    have c2 : -σ * t + β * t = -(σ - β) * t := by ring
    have c3 : -σ * t + (1 - β) * t = -(σ - (1 - β)) * t := by ring
    have hexp : Real.exp (-σ * t) * (Real.exp (β * t) - 1) * (Real.exp ((1 - β) * t) - 1) =
        Real.exp (-σ * t) + Real.exp (-(σ - 1) * t) -
          Real.exp (-(σ - β) * t) - Real.exp (-(σ - (1 - β)) * t) := by
      calc Real.exp (-σ * t) * (Real.exp (β * t) - 1) * (Real.exp ((1 - β) * t) - 1)
          = Real.exp (-σ * t) * Real.exp (β * t) * Real.exp ((1 - β) * t) +
              Real.exp (-σ * t) -
              Real.exp (-σ * t) * Real.exp (β * t) -
              Real.exp (-σ * t) * Real.exp ((1 - β) * t) := by ring
        _ = Real.exp (-σ * t) + Real.exp (-(σ - 1) * t) -
              Real.exp (-(σ - β) * t) - Real.exp (-(σ - (1 - β)) * t) := by
            rw [← Real.exp_add, ← Real.exp_add, c1, ← Real.exp_add, c2, ← Real.exp_add, c3]
            ring
    rw [hexp, mul_comm t u]
    ring

/-- **Exact `κ = 2` obstruction (real off-critical pairs).** For every `β ∈ (0, 1)` with `β ≠ 1/2`,
twisting `ζ` by `(s − β)(s − (1 − β)) / (s(s − 1))` yields a genuine `CompletedPositiveSystem 2 1`
whose completion vanishes at the off-critical real points `β` and `1 − β`. -/
theorem exists_completedPositiveSystem_two_real_offCritical {β : ℝ}
    (hβ0 : 0 < β) (hβ1 : β < 1) (hβ_half : β ≠ 1 / 2) :
    ∃ F Λ : ℂ → ℂ,
      CompletedPositiveSystem 2 1 F Λ ∧
      Λ (β : ℂ) = 0 ∧ Λ (((1 - β : ℝ) : ℂ)) = 0 ∧ ((β : ℂ).re ≠ 1 / 2) := by
  have hζ := completedPositiveSystem_riemannZeta
  let F : ℂ → ℂ := fun s => riemannZeta s * realPairFactor β s
  let Λ : ℂ → ℂ := fun s => 2 * RHTower.xi s * realPairPoly β s
  have hpoly_order : OrderOneEnvelope (realPairPoly β) := by
    have hid := RHTower.orderOneEnvelope_id
    have h1 : OrderOneEnvelope (fun s : ℂ => s - (β : ℂ)) :=
      (hid.add (orderOneEnvelope_const (-(β : ℂ)))).congr fun s => by ring
    have h2 : OrderOneEnvelope (fun s : ℂ => s - ((1 - β : ℝ) : ℂ)) :=
      (hid.add (orderOneEnvelope_const (-((1 - β : ℝ) : ℂ)))).congr fun s => by ring
    exact h1.mul h2
  have hrf_nz : ∀ s : ℂ, 1 < s.re → realPairFactor β s ≠ 0 := by
    intro s hs
    have hs0 : s ≠ 0 := fun h => by rw [h, Complex.zero_re] at hs; linarith
    have hs1 : s - 1 ≠ 0 := sub_ne_zero.mpr fun h => by rw [h, Complex.one_re] at hs; linarith
    have hn1 : s - (β : ℂ) ≠ 0 := fun h => by
      have := congrArg Complex.re h; simp at this; linarith
    have hn2 : s - ((1 - β : ℝ) : ℂ) ≠ 0 := fun h => by
      have := congrArg Complex.re h; simp at this; linarith
    exact div_ne_zero (mul_ne_zero hn1 hn2) (mul_ne_zero hs0 hs1)
  have hrf_diffOn : DifferentiableOn ℂ (realPairFactor β) {s : ℂ | 1 < s.re} := by
    intro s hs
    change 1 < s.re at hs
    have hs0 : s ≠ 0 := fun h => by rw [h, Complex.zero_re] at hs; linarith
    have hs1 : s - 1 ≠ 0 := sub_ne_zero.mpr fun h => by rw [h, Complex.one_re] at hs; linarith
    have hpd : DifferentiableAt ℂ (realPairPoly β) s := by unfold realPairPoly; fun_prop
    have hdd : DifferentiableAt ℂ (fun z : ℂ => z * (z - 1)) s := by fun_prop
    exact (hpd.div hdd (mul_ne_zero hs0 hs1)).differentiableWithinAt
  refine ⟨F, Λ, ?_, ?_, ?_, by rw [Complex.ofReal_re]; exact hβ_half⟩
  · refine
      { degree_pos := le_rfl
        diffOn_F := hζ.diffOn_F.mul hrf_diffOn
        ne_zero_F := fun s hs => mul_ne_zero (hζ.ne_zero_F s hs) (hrf_nz s hs)
        posDef_neg_logDeriv := ?_
        entire_Λ := hζ.entire_Λ.mul (by unfold realPairPoly; fun_prop)
        orderOne_Λ := hζ.orderOne_Λ.mul hpoly_order
        sym_Λ := fun s => by
          dsimp only [Λ]
          rw [hζ.sym_Λ]
          congr 1
          unfold realPairPoly
          push_cast
          ring
        conj_Λ := fun s => by
          dsimp only [Λ]
          rw [map_mul, hζ.conj_Λ]
          congr 1
          unfold realPairPoly
          simp only [map_mul, map_sub, Complex.conj_ofReal]
        completed_eq := fun s hs => by
          have hs0 : s ≠ 0 := fun h => by rw [h, Complex.zero_re] at hs; linarith
          have hs1 : s - 1 ≠ 0 := sub_ne_zero.mpr fun h => by rw [h, Complex.one_re] at hs; linarith
          dsimp only [Λ, F]
          unfold realPairFactor
          have hmul : (s * (s - 1)) * (realPairPoly β s / (s * (s - 1))) = realPairPoly β s :=
            mul_div_cancel₀ _ (mul_ne_zero hs0 hs1)
          calc 2 * RHTower.xi s * realPairPoly β s =
                (s * (s - 1)) ^ 1 * Complex.Gammaℝ s ^ 1 * riemannZeta s * realPairPoly β s := by
                  rw [hζ.completed_eq s hs]
            _ = (s * (s - 1)) ^ 2 * Complex.Gammaℝ s ^ 1 *
                  (riemannZeta s * (realPairPoly β s / (s * (s - 1)))) := by
                rw [← hmul]; ring }
    intro σ hσ
    have hopen : IsOpen {w : ℂ | 1 < w.re} := isOpen_lt continuous_const Complex.continuous_re
    have heq : (fun u : ℝ => (-logDeriv F ((σ : ℂ) + (u : ℂ) * I)).re) =
        fun u : ℝ => (-logDeriv riemannZeta ((σ : ℂ) + (u : ℂ) * I)).re +
          (-logDeriv (realPairFactor β) ((σ : ℂ) + (u : ℂ) * I)).re := by
      funext u
      set s : ℂ := (σ : ℂ) + (u : ℂ) * I
      have hs : 1 < s.re := by simp [s]; exact hσ
      rw [logDeriv_mul (f := riemannZeta) (g := realPairFactor β) s
            (hζ.ne_zero_F s hs) (hrf_nz s hs)
            ((hζ.diffOn_F s hs).differentiableAt (hopen.mem_nhds hs))
            ((hrf_diffOn s hs).differentiableAt (hopen.mem_nhds hs)),
          neg_add, Complex.add_re]
    rw [heq]
    exact isEvenPosDef_add' (hζ.posDef_neg_logDeriv hσ) (isEvenPosDef_realPairFactor hβ0 hβ1 hσ)
  · dsimp only [Λ]
    unfold realPairPoly
    simp
  · dsimp only [Λ]
    unfold realPairPoly
    simp

private theorem refundCriticalFactor_eq_linear_mul (γ : ℝ) (s : ℂ) :
    RHTower.refundCriticalFactor γ s =
      (s - (1 / 2 + (γ : ℂ) * I)) * (s - (1 / 2 - (γ : ℂ) * I)) := by
  unfold RHTower.refundCriticalFactor
  have hI : (I : ℂ) ^ 2 = -1 := I_sq
  calc (s - 1 / 2) ^ 2 + (γ : ℂ) ^ 2
      = (s - 1 / 2) ^ 2 - ((γ : ℂ) * I) ^ 2 := by rw [mul_pow, hI]; ring
    _ = (s - (1 / 2 + (γ : ℂ) * I)) * (s - (1 / 2 - (γ : ℂ) * I)) := by ring

private theorem exists_xi_critical_quotient {γ : ℝ} (hγ_pos : 0 < γ) (hXiγ : RHTower.Xi γ = 0) :
    ∃ g : ℂ → ℂ, Differentiable ℂ g ∧
      ∀ s : ℂ, RHTower.refundCriticalFactor γ s * g s = RHTower.xi s := by
  let zPlus : ℂ := 1 / 2 + (γ : ℂ) * I
  let zMinus : ℂ := 1 / 2 - (γ : ℂ) * I
  have hz_ne : zMinus ≠ zPlus := fun h => by
    have := congrArg Complex.im h; simp [zPlus, zMinus] at this; linarith
  have hxi_plus : RHTower.xi zPlus = 0 := by
    have hz0 : zPlus ≠ 0 := fun h => by
      have := congrArg Complex.re h; simp [zPlus] at this
    have hz1 : zPlus ≠ 1 := fun h => by
      have := congrArg Complex.re h; simp [zPlus] at this
    rw [RHTower.xi_eq_half_mul hz0 hz1,
        show zPlus = 1 / 2 + (γ : ℂ) * I from rfl,
        RHTower.completedRiemannZeta_critical_eq_Xi γ, hXiγ]
    simp
  have hxi_minus : RHTower.xi zMinus = 0 := by
    have hconj : starRingEnd ℂ zPlus = zMinus := by
      dsimp only [zPlus, zMinus]
      simp only [map_add, map_div₀, map_one, map_ofNat, map_mul, Complex.conj_ofReal,
        Complex.conj_I]
      ring
    rw [← hconj, RHTower.xi_conj, hxi_plus, map_zero]
  let g₁ : ℂ → ℂ := dslope RHTower.xi zPlus
  have hg₁_diff : Differentiable ℂ g₁ := by
    rw [← differentiableOn_univ]
    exact (Complex.differentiableOn_dslope Filter.univ_mem).mpr
      RHTower.xi_differentiable.differentiableOn
  have hg₁_eq : ∀ s : ℂ, (s - zPlus) * g₁ s = RHTower.xi s := fun s => by
    have h := sub_smul_dslope RHTower.xi zPlus s
    rwa [hxi_plus, sub_zero, smul_eq_mul] at h
  have hg₁_minus : g₁ zMinus = 0 := by
    have h := hg₁_eq zMinus
    rw [hxi_minus] at h
    exact (mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr hz_ne)
  let g₂ : ℂ → ℂ := dslope g₁ zMinus
  have hg₂_diff : Differentiable ℂ g₂ := by
    rw [← differentiableOn_univ]
    exact (Complex.differentiableOn_dslope Filter.univ_mem).mpr hg₁_diff.differentiableOn
  refine ⟨g₂, hg₂_diff, fun s => ?_⟩
  have h := sub_smul_dslope g₁ zMinus s
  rw [hg₁_minus, sub_zero, smul_eq_mul] at h
  rw [refundCriticalFactor_eq_linear_mul γ s]
  change (s - zPlus) * (s - zMinus) * g₂ s = RHTower.xi s
  rw [mul_assoc, h, hg₁_eq s]

private def complexQuartetTwist (a γ : ℝ) (s : ℂ) : ℂ :=
  RHTower.refundQuartic a γ s / ((s * (s - 1)) * RHTower.refundCriticalFactor γ s)

private theorem isEvenPosDef_complexQuartetTwist {a γ σ : ℝ}
    (ha0 : 0 < a) (ha : a ≤ 1 / 4) (hσ : 1 < σ) :
    IsEvenPosDef (fun u : ℝ =>
      (-logDeriv (complexQuartetTwist a γ) ((σ : ℂ) + (u : ℂ) * I)).re) := by
  let w : ℝ → ℝ := fun t => Real.exp (-σ * t) * RHTower.refundDensity a γ t
  refine isEvenPosDef_of_laplace_cos_nonneg (w := w) (a := σ - 1) (C := 8)
    (by linarith) (by norm_num) (by dsimp only [w]; unfold RHTower.refundDensity; fun_prop)
    (fun t ht => mul_nonneg (Real.exp_pos _).le (RHTower.refundDensity_nonneg ha0.le ha ht.le))
    (fun t ht => ?_) (fun u => ?_)
  · dsimp only [w]
    unfold RHTower.refundDensity
    have he0 : (1 : ℝ) ≤ Real.exp t := Real.one_le_exp ht.le
    have heh : Real.exp (t / 2) ≤ Real.exp t := Real.exp_le_exp.mpr (by linarith)
    have hea1 : Real.exp ((1 / 2 + a) * t) ≤ Real.exp t := Real.exp_le_exp.mpr (by nlinarith)
    have hea2 : Real.exp ((1 / 2 - a) * t) ≤ Real.exp t := Real.exp_le_exp.mpr (by nlinarith)
    have hc_lo : -1 ≤ Real.cos (γ * t) := Real.neg_one_le_cos _
    have hc_hi : Real.cos (γ * t) ≤ 1 := Real.cos_le_one _
    have hdens_le : (Real.exp t + 1) + 2 * Real.exp (t / 2) * Real.cos (γ * t) -
        2 * Real.cos (γ * t) * (Real.exp ((1 / 2 + a) * t) + Real.exp ((1 / 2 - a) * t)) ≤
        8 * Real.exp t := by
      have t1 : 2 * Real.exp (t / 2) * Real.cos (γ * t) ≤ 2 * Real.exp (t / 2) := by
        nlinarith [Real.exp_pos (t / 2), hc_hi]
      have t2 : -2 * (Real.exp ((1 / 2 + a) * t) + Real.exp ((1 / 2 - a) * t)) ≤
          2 * Real.cos (γ * t) *
            (Real.exp ((1 / 2 + a) * t) + Real.exp ((1 / 2 - a) * t)) := by
        nlinarith [Real.exp_pos ((1 / 2 + a) * t), Real.exp_pos ((1 / 2 - a) * t), hc_lo]
      linarith
    calc Real.exp (-σ * t) * ((Real.exp t + 1) + 2 * Real.exp (t / 2) * Real.cos (γ * t) -
          2 * Real.cos (γ * t) * (Real.exp ((1 / 2 + a) * t) + Real.exp ((1 / 2 - a) * t)))
        ≤ Real.exp (-σ * t) * (8 * Real.exp t) :=
          mul_le_mul_of_nonneg_left hdens_le (Real.exp_pos _).le
      _ = 8 * (Real.exp (-σ * t) * Real.exp t) := by ring
      _ = 8 * Real.exp (-(σ - 1) * t) := by rw [← Real.exp_add]; congr 2; ring
  · set s : ℂ := (σ : ℂ) + (u : ℂ) * I with hs_def
    have hs : 1 < s.re := by simp [hs_def]; exact hσ
    have hs0 : s ≠ 0 := fun h => by rw [h, Complex.zero_re] at hs; linarith
    have hs1 : s - 1 ≠ 0 := sub_ne_zero.mpr fun h => by rw [h, Complex.one_re] at hs; linarith
    let zPlus : ℂ := 1 / 2 + (γ : ℂ) * I
    let zMinus : ℂ := 1 / 2 - (γ : ℂ) * I
    have hp_ne : s - zPlus ≠ 0 := fun h => by
      have := congrArg Complex.re h; simp [hs_def, zPlus] at this; linarith
    have hm_ne : s - zMinus ≠ 0 := fun h => by
      have := congrArg Complex.re h; simp [hs_def, zMinus] at this; linarith
    let r1 : ℂ := 1 / 2 + (a : ℂ) + (γ : ℂ) * I
    let r2 : ℂ := 1 / 2 - (a : ℂ) - (γ : ℂ) * I
    let r3 : ℂ := 1 / 2 + (a : ℂ) - (γ : ℂ) * I
    let r4 : ℂ := 1 / 2 - (a : ℂ) + (γ : ℂ) * I
    have hr1 : s - r1 ≠ 0 := fun h => by
      have := congrArg Complex.re h; simp [hs_def, r1] at this; linarith
    have hr2 : s - r2 ≠ 0 := fun h => by
      have := congrArg Complex.re h; simp [hs_def, r2] at this; linarith
    have hr3 : s - r3 ≠ 0 := fun h => by
      have := congrArg Complex.re h; simp [hs_def, r3] at this; linarith
    have hr4 : s - r4 ≠ 0 := fun h => by
      have := congrArg Complex.re h; simp [hs_def, r4] at this; linarith
    have hd_lin : ∀ c : ℂ, logDeriv (fun z : ℂ => z - c) s = 1 / (s - c) := fun c => by
      rw [logDeriv_apply, deriv_sub_const, deriv_id'', one_div]
    have htwist_eq : complexQuartetTwist a γ = fun z : ℂ =>
        ((z - r1) * (z - r2) * ((z - r3) * (z - r4))) /
          ((z * (z - 1)) * ((z - zPlus) * (z - zMinus))) := by
      funext z
      unfold complexQuartetTwist
      rw [refundCriticalFactor_eq_linear_mul γ z]
      rfl
    have hld : -logDeriv (complexQuartetTwist a γ) s =
        (1 / s + 1 / (s - 1)) + (1 / (s - zPlus) + 1 / (s - zMinus)) -
          ((1 / (s - r1) + 1 / (s - r3)) + (1 / (s - r4) + 1 / (s - r2))) := by
      have d1 : DifferentiableAt ℂ (fun z : ℂ => z - r1) s := differentiableAt_id.sub_const r1
      have d2 : DifferentiableAt ℂ (fun z : ℂ => z - r2) s := differentiableAt_id.sub_const r2
      have d3 : DifferentiableAt ℂ (fun z : ℂ => z - r3) s := differentiableAt_id.sub_const r3
      have d4 : DifferentiableAt ℂ (fun z : ℂ => z - r4) s := differentiableAt_id.sub_const r4
      have ds1 : DifferentiableAt ℂ (fun z : ℂ => z - 1) s :=
        differentiableAt_id.sub_const (1 : ℂ)
      have dp : DifferentiableAt ℂ (fun z : ℂ => z - zPlus) s :=
        differentiableAt_id.sub_const zPlus
      have dm : DifferentiableAt ℂ (fun z : ℂ => z - zMinus) s :=
        differentiableAt_id.sub_const zMinus
      rw [htwist_eq,
          logDeriv_div
            (f := fun z : ℂ => (z - r1) * (z - r2) * ((z - r3) * (z - r4)))
            (g := fun z : ℂ => (z * (z - 1)) * ((z - zPlus) * (z - zMinus)))
            s (mul_ne_zero (mul_ne_zero hr1 hr2) (mul_ne_zero hr3 hr4))
            (mul_ne_zero (mul_ne_zero hs0 hs1) (mul_ne_zero hp_ne hm_ne))
            ((d1.mul d2).mul (d3.mul d4))
            ((differentiableAt_id.mul ds1).mul (dp.mul dm)),
          logDeriv_mul
            (f := fun z : ℂ => (z - r1) * (z - r2))
            (g := fun z : ℂ => (z - r3) * (z - r4))
            s (mul_ne_zero hr1 hr2) (mul_ne_zero hr3 hr4) (d1.mul d2) (d3.mul d4),
          logDeriv_mul (f := fun z : ℂ => z - r1) (g := fun z : ℂ => z - r2) s hr1 hr2 d1 d2,
          logDeriv_mul (f := fun z : ℂ => z - r3) (g := fun z : ℂ => z - r4) s hr3 hr4 d3 d4,
          logDeriv_mul
            (f := fun z : ℂ => z * (z - 1))
            (g := fun z : ℂ => (z - zPlus) * (z - zMinus))
            s (mul_ne_zero hs0 hs1) (mul_ne_zero hp_ne hm_ne)
            (differentiableAt_id.mul ds1) (dp.mul dm),
          logDeriv_mul (f := fun z : ℂ => z) (g := fun z : ℂ => z - 1) s hs0 hs1
            differentiableAt_id ds1,
          logDeriv_mul (f := fun z : ℂ => z - zPlus) (g := fun z : ℂ => z - zMinus)
            s hp_ne hm_ne dp dm,
          hd_lin, hd_lin, hd_lin, hd_lin, hd_lin, hd_lin, hd_lin]
      have hid' : logDeriv (fun z : ℂ => z) s = 1 / s := by
        rw [logDeriv_apply, deriv_id'', one_div]
      rw [hid']
      ring
    have hpair_int : ∀ α : ℝ, 0 < α →
        (1 / (((α : ℝ) : ℂ) + ((u - γ : ℝ) : ℂ) * I) +
          1 / (((α : ℝ) : ℂ) + ((u + γ : ℝ) : ℂ) * I)).re =
          ∫ t : ℝ in Ioi 0,
            (2 * Real.exp (-α * t) * Real.cos (γ * t)) * Real.cos (t * u) := by
      intro α hα
      have hi : ∀ b : ℝ,
          IntegrableOn (fun t : ℝ => Real.exp (-α * t) * Real.cos (b * t)) (Ioi 0) := by
        intro b
        refine Integrable.mono' (integrableOn_exp_mul_Ioi (by linarith) 0)
          ((Continuous.aestronglyMeasurable (by fun_prop)).restrict)
          (Eventually.of_forall fun t => ?_)
        rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
        exact mul_le_of_le_one_right (Real.exp_pos _).le (Real.abs_cos_le_one _)
      rw [Complex.add_re, re_one_div_eq_laplace_cos' α (u - γ) hα,
          re_one_div_eq_laplace_cos' α (u + γ) hα, ← integral_add (hi (u - γ)) (hi (u + γ))]
      refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
      rw [sub_mul, add_mul, Real.cos_sub, Real.cos_add, mul_comm t u]
      ring
    have es1 : s - 1 = (((σ - 1 : ℝ) : ℂ) + (u : ℂ) * I) := by rw [hs_def]; push_cast; ring
    have ezp : s - zPlus = (((σ - 1 / 2 : ℝ) : ℂ) + ((u - γ : ℝ) : ℂ) * I) := by
      rw [hs_def]; dsimp only [zPlus]; push_cast; ring
    have ezm : s - zMinus = (((σ - 1 / 2 : ℝ) : ℂ) + ((u + γ : ℝ) : ℂ) * I) := by
      rw [hs_def]; dsimp only [zMinus]; push_cast; ring
    have er1 : s - r1 = (((σ - (1 / 2 + a) : ℝ) : ℂ) + ((u - γ : ℝ) : ℂ) * I) := by
      rw [hs_def]; dsimp only [r1]; push_cast; ring
    have er3 : s - r3 = (((σ - (1 / 2 + a) : ℝ) : ℂ) + ((u + γ : ℝ) : ℂ) * I) := by
      rw [hs_def]; dsimp only [r3]; push_cast; ring
    have er4 : s - r4 = (((σ - (1 / 2 - a) : ℝ) : ℂ) + ((u - γ : ℝ) : ℂ) * I) := by
      rw [hs_def]; dsimp only [r4]; push_cast; ring
    have er2 : s - r2 = (((σ - (1 / 2 - a) : ℝ) : ℂ) + ((u + γ : ℝ) : ℂ) * I) := by
      rw [hs_def]; dsimp only [r2]; push_cast; ring
    rw [hld, es1, ezp, ezm, er1, er3, er4, er2, hs_def,
        Complex.sub_re, Complex.add_re, Complex.add_re, Complex.add_re,
        re_one_div_eq_laplace_cos' σ u (by linarith),
        re_one_div_eq_laplace_cos' (σ - 1) u (by linarith),
        hpair_int (σ - 1 / 2) (by linarith),
        hpair_int (σ - (1 / 2 + a)) (by linarith),
        hpair_int (σ - (1 / 2 - a)) (by linarith)]
    have hi_single : ∀ α : ℝ, 0 < α →
        IntegrableOn (fun t : ℝ => Real.exp (-α * t) * Real.cos (u * t)) (Ioi 0) := by
      intro α hα
      refine Integrable.mono' (integrableOn_exp_mul_Ioi (by linarith) 0)
        ((Continuous.aestronglyMeasurable (by fun_prop)).restrict)
        (Eventually.of_forall fun t => ?_)
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
      exact mul_le_of_le_one_right (Real.exp_pos _).le (Real.abs_cos_le_one _)
    have hi_pair : ∀ α : ℝ, 0 < α → IntegrableOn
        (fun t : ℝ => (2 * Real.exp (-α * t) * Real.cos (γ * t)) * Real.cos (t * u)) (Ioi 0) := by
      intro α hα
      refine Integrable.mono' ((integrableOn_exp_mul_Ioi (by linarith) 0).const_mul 2)
        ((Continuous.aestronglyMeasurable (by fun_prop)).restrict)
        (Eventually.of_forall fun t => ?_)
      rw [Real.norm_eq_abs, abs_mul, abs_mul]
      have h1 : |2 * Real.exp (-α * t)| = 2 * Real.exp (-α * t) :=
        abs_of_pos (by positivity)
      rw [h1]
      have h2 : 2 * Real.exp (-α * t) * |Real.cos (γ * t)| ≤ 2 * Real.exp (-α * t) :=
        mul_le_of_le_one_right (by positivity) (Real.abs_cos_le_one _)
      exact (mul_le_of_le_one_right (by positivity) (Real.abs_cos_le_one _)).trans h2
    have i0 := hi_single σ (by linarith)
    have i1 := hi_single (σ - 1) (by linarith)
    have ip0 := hi_pair (σ - 1 / 2) (by linarith)
    have ip1 := hi_pair (σ - (1 / 2 + a)) (by linarith)
    have ip2 := hi_pair (σ - (1 / 2 - a)) (by linarith)
    rw [← integral_add i0 i1, ← integral_add (i0.add i1) ip0,
        ← integral_add ip1 ip2, ← integral_sub ((i0.add i1).add ip0) (ip1.add ip2)]
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    dsimp only [w]
    unfold RHTower.refundDensity
    have c1 : -σ * t + t = -(σ - 1) * t := by ring
    have c2 : -σ * t + t / 2 = -(σ - 1 / 2) * t := by ring
    have c3 : -σ * t + (1 / 2 + a) * t = -(σ - (1 / 2 + a)) * t := by ring
    have c4 : -σ * t + (1 / 2 - a) * t = -(σ - (1 / 2 - a)) * t := by ring
    have hexp : Real.exp (-σ * t) *
          ((Real.exp t + 1) + 2 * Real.exp (t / 2) * Real.cos (γ * t) -
            2 * Real.cos (γ * t) *
              (Real.exp ((1 / 2 + a) * t) + Real.exp ((1 / 2 - a) * t))) =
        Real.exp (-σ * t) + Real.exp (-(σ - 1) * t) +
          2 * Real.exp (-(σ - 1 / 2) * t) * Real.cos (γ * t) -
          (2 * Real.exp (-(σ - (1 / 2 + a)) * t) * Real.cos (γ * t) +
            2 * Real.exp (-(σ - (1 / 2 - a)) * t) * Real.cos (γ * t)) := by
      calc Real.exp (-σ * t) *
            ((Real.exp t + 1) + 2 * Real.exp (t / 2) * Real.cos (γ * t) -
              2 * Real.cos (γ * t) *
                (Real.exp ((1 / 2 + a) * t) + Real.exp ((1 / 2 - a) * t)))
          = Real.exp (-σ * t) + (Real.exp (-σ * t) * Real.exp t) +
              2 * (Real.exp (-σ * t) * Real.exp (t / 2)) * Real.cos (γ * t) -
              (2 * (Real.exp (-σ * t) * Real.exp ((1 / 2 + a) * t)) * Real.cos (γ * t) +
                2 * (Real.exp (-σ * t) * Real.exp ((1 / 2 - a) * t)) * Real.cos (γ * t)) := by
            ring
        _ = _ := by
            rw [← Real.exp_add, c1, ← Real.exp_add, c2, ← Real.exp_add, c3, ← Real.exp_add, c4]
    rw [hexp, mul_comm t u]
    ring

/-- **Exact `κ = 2` obstruction (genuinely complex off-critical quartets).** For every
`a ∈ (0, 1/4]`, cancelling an unconditional critical zero pair `1/2 ± i γ₀` of `ξ` (`γ₀ > 0` from
Hardy's theorem) and inserting the quartet `1/2 ± a ± i γ₀` produces a genuine
`CompletedPositiveSystem 2 1` with a nonreal off-critical zero at `1/2 + a + i γ₀`. -/
theorem exists_completedPositiveSystem_two_complex_offCritical {a : ℝ}
    (ha0 : 0 < a) (ha : a ≤ 1 / 4) :
    ∃ (F Λ : ℂ → ℂ) (ρ : ℂ),
      CompletedPositiveSystem 2 1 F Λ ∧
      Λ ρ = 0 ∧ ρ.re ≠ 1 / 2 ∧ 0 < ρ.im := by
  obtain ⟨γ, hγ_pos, hXiγ⟩ := RHTower.exists_Xi_zero_gt 0
  obtain ⟨g₂, hg₂_diff, hg₂_eq⟩ := exists_xi_critical_quotient hγ_pos hXiγ
  have hζ := completedPositiveSystem_riemannZeta
  let F : ℂ → ℂ := fun s => riemannZeta s * complexQuartetTwist a γ s
  let Λ : ℂ → ℂ := fun s => 2 * g₂ s * RHTower.refundQuartic a γ s
  let ρ : ℂ := 1 / 2 + (a : ℂ) + (γ : ℂ) * I
  have hcrit_nz_of_re_ne : ∀ s : ℂ, s.re ≠ 1 / 2 → RHTower.refundCriticalFactor γ s ≠ 0 := by
    intro s hs h0
    rw [refundCriticalFactor_eq_linear_mul] at h0
    rcases mul_eq_zero.mp h0 with h1 | h2
    · apply hs; have := congrArg Complex.re h1; simp at this; linarith
    · apply hs; have := congrArg Complex.re h2; simp at this; linarith
  have hquartic_nz_of_gt : ∀ s : ℂ, 1 < s.re → RHTower.refundQuartic a γ s ≠ 0 := by
    intro s hs
    unfold RHTower.refundQuartic
    have n1 : s - (1 / 2 + (a : ℂ) + (γ : ℂ) * I) ≠ 0 := fun h => by
      have := congrArg Complex.re h; simp at this; linarith
    have n2 : s - (1 / 2 - (a : ℂ) - (γ : ℂ) * I) ≠ 0 := fun h => by
      have := congrArg Complex.re h; simp at this; linarith
    have n3 : s - (1 / 2 + (a : ℂ) - (γ : ℂ) * I) ≠ 0 := fun h => by
      have := congrArg Complex.re h; simp at this; linarith
    have n4 : s - (1 / 2 - (a : ℂ) + (γ : ℂ) * I) ≠ 0 := fun h => by
      have := congrArg Complex.re h; simp at this; linarith
    exact mul_ne_zero (mul_ne_zero n1 n2) (mul_ne_zero n3 n4)
  have htwist_nz : ∀ s : ℂ, 1 < s.re → complexQuartetTwist a γ s ≠ 0 := by
    intro s hs
    have hs0 : s ≠ 0 := fun h => by rw [h, Complex.zero_re] at hs; linarith
    have hs1 : s - 1 ≠ 0 := sub_ne_zero.mpr fun h => by rw [h, Complex.one_re] at hs; linarith
    exact div_ne_zero (hquartic_nz_of_gt s hs)
      (mul_ne_zero (mul_ne_zero hs0 hs1) (hcrit_nz_of_re_ne s (by linarith)))
  have htwist_diffOn : DifferentiableOn ℂ (complexQuartetTwist a γ) {s : ℂ | 1 < s.re} := by
    intro s hs
    change 1 < s.re at hs
    have hs0 : s ≠ 0 := fun h => by rw [h, Complex.zero_re] at hs; linarith
    have hs1 : s - 1 ≠ 0 := sub_ne_zero.mpr fun h => by rw [h, Complex.one_re] at hs; linarith
    have hqd : DifferentiableAt ℂ (RHTower.refundQuartic a γ) s := by
      unfold RHTower.refundQuartic; fun_prop
    have hdd : DifferentiableAt ℂ
        (fun z : ℂ => (z * (z - 1)) * RHTower.refundCriticalFactor γ z) s := by
      unfold RHTower.refundCriticalFactor; fun_prop
    exact (hqd.div hdd
      (mul_ne_zero (mul_ne_zero hs0 hs1) (hcrit_nz_of_re_ne s (by linarith)))).differentiableWithinAt
  have hΛ_entire : Differentiable ℂ Λ :=
    (hg₂_diff.const_mul 2).mul (by unfold RHTower.refundQuartic; fun_prop)
  have hquartic_order : OrderOneEnvelope (RHTower.refundQuartic a γ) := by
    have hid := RHTower.orderOneEnvelope_id
    have lin : ∀ c : ℂ, OrderOneEnvelope (fun s : ℂ => s - c) := fun c =>
      (hid.add (orderOneEnvelope_const (-c))).congr fun s => by ring
    exact ((lin _).mul (lin _)).mul ((lin _).mul (lin _))
  have hΛ_order : OrderOneEnvelope Λ := by
    have hprod_ord : OrderOneEnvelope (fun s => 2 * RHTower.xi s * RHTower.refundQuartic a γ s) :=
      hζ.orderOne_Λ.mul hquartic_order
    obtain ⟨C₁, hC₁, hgrow₁⟩ := hprod_ord
    have hcomp_ball : IsCompact (Metric.closedBall (1 / 2 : ℂ) (γ + 1)) :=
      isCompact_closedBall _ _
    obtain ⟨B₀, hB₀⟩ := hcomp_ball.exists_bound_of_continuousOn hΛ_entire.continuous.continuousOn
    obtain ⟨C₂, hC₂0, hC₂⟩ := RHTower.CompletionGrowth.le_exp_envelope
      (A := max B₀ 0) (M := 0) le_rfl 0
    set C : ℝ := C₁ + C₂ + 1
    refine ⟨C, by positivity, fun s => ?_⟩
    have hmono : ∀ C' : ℝ, C' ≤ C →
        Real.exp (C' * (1 + ‖s‖) * Real.log (2 + ‖s‖)) ≤ Real.exp (orderOneWeight C s) := by
      intro C' hC'
      rw [orderOneWeight, Real.exp_le_exp]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC' (by positivity))
        (Real.log_nonneg (by linarith [norm_nonneg s]))
    by_cases hmem : s ∈ Metric.closedBall (1 / 2 : ℂ) (γ + 1)
    · have hb1 : ‖Λ s‖ ≤ max B₀ 0 := (hB₀ s hmem).trans (le_max_left _ _)
      have hb2 := hC₂ ‖s‖ (norm_nonneg s)
      simp only [pow_zero, mul_one, zero_mul, Real.exp_zero] at hb2
      exact (hb1.trans hb2).trans (hmono C₂ (by simp only [C]; linarith))
    · rw [Metric.mem_closedBall, dist_eq_norm, not_le] at hmem
      have hzp : 1 ≤ ‖s - (1 / 2 + (γ : ℂ) * I)‖ := by
        have htri : ‖s - 1 / 2‖ ≤ ‖s - (1 / 2 + (γ : ℂ) * I)‖ + ‖(1 / 2 + (γ : ℂ) * I) - 1 / 2‖ := by
          have := norm_add_le (s - (1 / 2 + (γ : ℂ) * I)) ((1 / 2 + (γ : ℂ) * I) - 1 / 2)
          rwa [sub_add_sub_cancel] at this
        have hzim : ‖(1 / 2 + (γ : ℂ) * I) - 1 / 2‖ = γ := by
          rw [add_sub_cancel_left, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
              Real.norm_eq_abs, abs_of_pos hγ_pos]
        linarith
      have hzm : 1 ≤ ‖s - (1 / 2 - (γ : ℂ) * I)‖ := by
        have htri : ‖s - 1 / 2‖ ≤ ‖s - (1 / 2 - (γ : ℂ) * I)‖ + ‖(1 / 2 - (γ : ℂ) * I) - 1 / 2‖ := by
          have := norm_add_le (s - (1 / 2 - (γ : ℂ) * I)) ((1 / 2 - (γ : ℂ) * I) - 1 / 2)
          rwa [sub_add_sub_cancel] at this
        have hzim : ‖(1 / 2 - (γ : ℂ) * I) - 1 / 2‖ = γ := by
          have he : (1 / 2 - (γ : ℂ) * I) - 1 / 2 = -((γ : ℂ) * I) := by ring
          rw [he, norm_neg, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
              Real.norm_eq_abs, abs_of_pos hγ_pos]
        linarith
      have hcf_ge1 : 1 ≤ ‖RHTower.refundCriticalFactor γ s‖ := by
        rw [refundCriticalFactor_eq_linear_mul γ s, norm_mul]
        nlinarith
      have hg₂_le : ‖g₂ s‖ ≤ ‖RHTower.xi s‖ := by
        rw [← hg₂_eq s, norm_mul]
        nlinarith [norm_nonneg (g₂ s)]
      have hΛ_le : ‖Λ s‖ ≤ ‖2 * RHTower.xi s * RHTower.refundQuartic a γ s‖ := by
        dsimp only [Λ]
        rw [norm_mul, norm_mul, norm_mul, norm_mul]
        gcongr
      exact (hΛ_le.trans (hgrow₁ s)).trans (hmono C₁ (by simp only [C]; linarith))
  have hΛ_sym_off : ∀ s : ℂ, s.re ≠ 1 / 2 → Λ (1 - s) = Λ s := by
    intro s hs
    have hcf : RHTower.refundCriticalFactor γ s ≠ 0 := hcrit_nz_of_re_ne s hs
    apply mul_left_cancel₀ hcf
    dsimp only [Λ]
    calc RHTower.refundCriticalFactor γ s * (2 * g₂ (1 - s) * RHTower.refundQuartic a γ (1 - s))
        = 2 * (RHTower.refundCriticalFactor γ (1 - s) * g₂ (1 - s)) *
            RHTower.refundQuartic a γ (1 - s) := by
            rw [RHTower.refundCriticalFactor_reflect]; ring
      _ = 2 * RHTower.xi (1 - s) * RHTower.refundQuartic a γ (1 - s) := by rw [hg₂_eq]
      _ = 2 * RHTower.xi s * RHTower.refundQuartic a γ s := by
            rw [RHTower.xi_one_sub, RHTower.refundQuartic_reflect]
      _ = RHTower.refundCriticalFactor γ s * (2 * g₂ s * RHTower.refundQuartic a γ s) := by
            rw [← hg₂_eq s]; ring
  have hΛ_sym : ∀ s : ℂ, Λ (1 - s) = Λ s := by
    intro s
    by_cases hs : s.re = 1 / 2
    · have hseq_lim : Tendsto (fun n : ℕ => s + 1 / ((n : ℂ) + 1)) atTop (𝓝 (s + 0)) :=
        tendsto_const_nhds.add tendsto_one_div_add_atTop_nhds_zero_nat
      rw [add_zero] at hseq_lim
      have hlhs : Tendsto (fun n : ℕ => Λ (1 - (s + 1 / ((n : ℂ) + 1)))) atTop (𝓝 (Λ (1 - s))) :=
        (hΛ_entire.continuous.comp (continuous_const.sub continuous_id)).tendsto s |>.comp hseq_lim
      have hrhs : Tendsto (fun n : ℕ => Λ (s + 1 / ((n : ℂ) + 1))) atTop (𝓝 (Λ s)) :=
        (hΛ_entire.continuous.tendsto s).comp hseq_lim
      refine tendsto_nhds_unique hlhs (hrhs.congr fun n => (hΛ_sym_off _ ?_).symm)
      have hre : (s + 1 / ((n : ℂ) + 1)).re = 1 / 2 + 1 / ((n : ℝ) + 1) := by
        have hc : (1 / ((n : ℂ) + 1)) = (((1 / ((n : ℝ) + 1) : ℝ) : ℂ)) := by push_cast; rfl
        rw [hc, Complex.add_re, hs, Complex.ofReal_re]
      rw [hre]
      have hpos : 0 < 1 / ((n : ℝ) + 1) := by positivity
      linarith
    · exact hΛ_sym_off s hs
  have hΛ_conj_off : ∀ s : ℂ, s.re ≠ 1 / 2 → Λ (starRingEnd ℂ s) = starRingEnd ℂ (Λ s) := by
    intro s hs
    have hcf_conj : RHTower.refundCriticalFactor γ (starRingEnd ℂ s) ≠ 0 :=
      hcrit_nz_of_re_ne _ (by rw [Complex.conj_re]; exact hs)
    apply mul_left_cancel₀ hcf_conj
    have hcf_map : RHTower.refundCriticalFactor γ (starRingEnd ℂ s) =
        starRingEnd ℂ (RHTower.refundCriticalFactor γ s) := by
      unfold RHTower.refundCriticalFactor
      simp only [map_add, map_pow, map_sub, map_div₀, map_one, map_ofNat, Complex.conj_ofReal]
    have hq_map : RHTower.refundQuartic a γ (starRingEnd ℂ s) =
        starRingEnd ℂ (RHTower.refundQuartic a γ s) := by
      unfold RHTower.refundQuartic
      simp only [map_mul, map_sub, map_add, map_div₀, map_one, map_ofNat, Complex.conj_ofReal,
        Complex.conj_I]
      ring
    dsimp only [Λ]
    calc RHTower.refundCriticalFactor γ (starRingEnd ℂ s) *
          (2 * g₂ (starRingEnd ℂ s) * RHTower.refundQuartic a γ (starRingEnd ℂ s))
        = 2 * (RHTower.refundCriticalFactor γ (starRingEnd ℂ s) * g₂ (starRingEnd ℂ s)) *
            RHTower.refundQuartic a γ (starRingEnd ℂ s) := by ring
      _ = 2 * RHTower.xi (starRingEnd ℂ s) * RHTower.refundQuartic a γ (starRingEnd ℂ s) := by
            rw [hg₂_eq]
      _ = starRingEnd ℂ (2 * RHTower.xi s * RHTower.refundQuartic a γ s) := by
            rw [RHTower.xi_conj, hq_map, map_mul, map_mul, map_ofNat]
      _ = starRingEnd ℂ (RHTower.refundCriticalFactor γ s *
            (2 * g₂ s * RHTower.refundQuartic a γ s)) := by
            rw [← hg₂_eq s]; congr 1; ring
      _ = RHTower.refundCriticalFactor γ (starRingEnd ℂ s) *
            starRingEnd ℂ (2 * g₂ s * RHTower.refundQuartic a γ s) := by
            rw [map_mul, ← hcf_map]
  have hΛ_conj : ∀ s : ℂ, Λ (starRingEnd ℂ s) = starRingEnd ℂ (Λ s) := by
    intro s
    by_cases hs : s.re = 1 / 2
    · have hseq_lim : Tendsto (fun n : ℕ => s + 1 / ((n : ℂ) + 1)) atTop (𝓝 (s + 0)) :=
        tendsto_const_nhds.add tendsto_one_div_add_atTop_nhds_zero_nat
      rw [add_zero] at hseq_lim
      have hlhs : Tendsto (fun n : ℕ => Λ (starRingEnd ℂ (s + 1 / ((n : ℂ) + 1)))) atTop
          (𝓝 (Λ (starRingEnd ℂ s))) :=
        (hΛ_entire.continuous.comp Complex.continuous_conj).tendsto s |>.comp hseq_lim
      have hrhs : Tendsto (fun n : ℕ => starRingEnd ℂ (Λ (s + 1 / ((n : ℂ) + 1)))) atTop
          (𝓝 (starRingEnd ℂ (Λ s))) :=
        (Complex.continuous_conj.comp hΛ_entire.continuous).tendsto s |>.comp hseq_lim
      refine tendsto_nhds_unique hlhs (hrhs.congr fun n => (hΛ_conj_off _ ?_).symm)
      have hre : (s + 1 / ((n : ℂ) + 1)).re = 1 / 2 + 1 / ((n : ℝ) + 1) := by
        have hc : (1 / ((n : ℂ) + 1)) = (((1 / ((n : ℝ) + 1) : ℝ) : ℂ)) := by push_cast; rfl
        rw [hc, Complex.add_re, hs, Complex.ofReal_re]
      rw [hre]
      have hpos : 0 < 1 / ((n : ℝ) + 1) := by positivity
      linarith
    · exact hΛ_conj_off s hs
  have hoff := RHTower.refund_offCriticalLine (gam := γ) ha0.ne' hγ_pos.ne'
  refine ⟨F, Λ, ρ, ?_, ?_, hoff.2.1, by simp [ρ, hγ_pos]⟩
  · refine
      { degree_pos := le_rfl
        diffOn_F := hζ.diffOn_F.mul htwist_diffOn
        ne_zero_F := fun s hs => mul_ne_zero (hζ.ne_zero_F s hs) (htwist_nz s hs)
        posDef_neg_logDeriv := ?_
        entire_Λ := hΛ_entire
        orderOne_Λ := hΛ_order
        sym_Λ := hΛ_sym
        conj_Λ := hΛ_conj
        completed_eq := fun s hs => by
          have hs0 : s ≠ 0 := fun h => by rw [h, Complex.zero_re] at hs; linarith
          have hs1 : s - 1 ≠ 0 := sub_ne_zero.mpr fun h => by rw [h, Complex.one_re] at hs; linarith
          have hcf : RHTower.refundCriticalFactor γ s ≠ 0 := hcrit_nz_of_re_ne s (by linarith)
          dsimp only [Λ, F]
          have hxi_eq := hζ.completed_eq s hs
          apply mul_left_cancel₀ hcf
          have hden : (s * (s - 1)) * RHTower.refundCriticalFactor γ s ≠ 0 :=
            mul_ne_zero (mul_ne_zero hs0 hs1) hcf
          have hmul : (s * (s - 1)) * RHTower.refundCriticalFactor γ s *
              complexQuartetTwist a γ s = RHTower.refundQuartic a γ s :=
            mul_div_cancel₀ (RHTower.refundQuartic a γ s) hden
          calc RHTower.refundCriticalFactor γ s * (2 * g₂ s * RHTower.refundQuartic a γ s)
              = 2 * (RHTower.refundCriticalFactor γ s * g₂ s) * RHTower.refundQuartic a γ s := by
                  ring
            _ = (2 * RHTower.xi s) * RHTower.refundQuartic a γ s := by rw [hg₂_eq]
            _ = (s * (s - 1)) ^ 1 * Complex.Gammaℝ s ^ 1 * riemannZeta s *
                  RHTower.refundQuartic a γ s := by rw [hxi_eq]
            _ = RHTower.refundCriticalFactor γ s *
                  ((s * (s - 1)) ^ 2 * Complex.Gammaℝ s ^ 1 *
                    (riemannZeta s * complexQuartetTwist a γ s)) := by
                  rw [← hmul]; ring }
    intro σ hσ
    have hopen : IsOpen {w : ℂ | 1 < w.re} := isOpen_lt continuous_const Complex.continuous_re
    have heq : (fun u : ℝ => (-logDeriv F ((σ : ℂ) + (u : ℂ) * I)).re) =
        fun u : ℝ => (-logDeriv riemannZeta ((σ : ℂ) + (u : ℂ) * I)).re +
          (-logDeriv (complexQuartetTwist a γ) ((σ : ℂ) + (u : ℂ) * I)).re := by
      funext u
      set s : ℂ := (σ : ℂ) + (u : ℂ) * I
      have hs : 1 < s.re := by simp [s]; exact hσ
      rw [logDeriv_mul (f := riemannZeta) (g := complexQuartetTwist a γ) s
            (hζ.ne_zero_F s hs) (htwist_nz s hs)
            ((hζ.diffOn_F s hs).differentiableAt (hopen.mem_nhds hs))
            ((htwist_diffOn s hs).differentiableAt (hopen.mem_nhds hs)),
          neg_add, Complex.add_re]
    rw [heq]
    exact isEvenPosDef_add' (hζ.posDef_neg_logDeriv hσ) (isEvenPosDef_complexQuartetTwist ha0 ha hσ)
  · dsimp only [Λ, ρ]
    rw [hoff.1, mul_zero]

/-! ### 3. Reference-free impossibility of entire `κ = 0` Laplace-positive completions -/

private theorem frequently_eq_of_eventually_nhdsNE_real' {f g : ℂ → ℂ} {t₀ : ℝ}
    (h : ∀ᶠ t : ℝ in 𝓝[≠] t₀, f (t : ℂ) = g (t : ℂ)) :
    ∃ᶠ z : ℂ in 𝓝[≠] (t₀ : ℂ), f z = g z := by
  rw [Filter.frequently_iff]
  intro U hU
  obtain ⟨r, hr, hrU⟩ := Metric.mem_nhdsWithin_iff.mp hU
  obtain ⟨ε, hε, hεh⟩ := Metric.eventually_nhds_iff.mp (eventually_nhdsWithin_iff.mp h)
  set d := min r ε / 2
  have hd : 0 < d := by positivity
  have hdr : d < r := by have := min_le_left r ε; simp only [d]; linarith
  have hdε : d < ε := by have := min_le_right r ε; simp only [d]; linarith
  refine ⟨((t₀ + d : ℝ) : ℂ), hrU ⟨?_, ?_⟩, hεh ?_ ?_⟩
  · rw [Metric.mem_ball, dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_eq_abs, add_sub_cancel_left, abs_of_pos hd]
    exact hdr
  · rw [mem_compl_singleton_iff, Ne, Complex.ofReal_inj]
    linarith
  · rw [Real.dist_eq, add_sub_cancel_left, abs_of_pos hd]
    exact hdε
  · rw [mem_compl_singleton_iff]
    linarith

private theorem ne_zero_of_entire_linear_ode' {E W : ℂ → ℂ} {t₀ : ℝ}
    (hE : Differentiable ℂ E) (hE_nz : ∃ z₀, E z₀ ≠ 0)
    (hW : AnalyticAt ℂ W (t₀ : ℂ))
    (heq : ∀ᶠ t : ℝ in 𝓝[≠] t₀, deriv E (t : ℂ) = W (t : ℂ) * E (t : ℂ)) :
    E (t₀ : ℂ) ≠ 0 := by
  intro h0
  set z₀ : ℂ := (t₀ : ℂ) with hz₀
  have hEan : AnalyticOnNhd ℂ E univ := hE.differentiableOn.analyticOnNhd isOpen_univ
  obtain ⟨z₁, hz₁⟩ := hE_nz
  have hntop : analyticOrderAt E z₀ ≠ ⊤ :=
    hEan.analyticOrderAt_ne_top_of_isPreconnected isPreconnected_univ (mem_univ z₁) (mem_univ z₀)
      (by rw [(hEan z₁ (mem_univ z₁)).analyticOrderAt_eq_zero.mpr hz₁]; exact ENat.zero_ne_top)
  have hne0 : analyticOrderAt E z₀ ≠ 0 := fun hz =>
    ((hEan z₀ (mem_univ z₀)).analyticOrderAt_eq_zero.mp hz) h0
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp hntop
  have hm_pos : 1 ≤ m := by
    rcases eq_or_ne m 0 with rfl | hm0
    · exact absurd hm.symm hne0
    · omega
  obtain ⟨g, hgan, hg0, hEg₀⟩ := (hEan z₀ (mem_univ z₀)).analyticOrderAt_eq_natCast.mp hm.symm
  have hEg : ∀ᶠ z in 𝓝 z₀, E z = (z - z₀) ^ m * g z := by
    filter_upwards [hEg₀] with z hz
    simpa only [smul_eq_mul] using hz
  have hdE_an : AnalyticAt ℂ (deriv E) z₀ := (hEan z₀ (mem_univ z₀)).deriv
  have hWE_an : AnalyticAt ℂ (fun z => W z * E z) z₀ := hW.mul (hEan z₀ (mem_univ z₀))
  have hEqC : deriv E =ᶠ[𝓝 z₀] fun z => W z * E z :=
    (hdE_an.frequently_eq_iff_eventually_eq hWE_an).mp (frequently_eq_of_eventually_nhdsNE_real' heq)
  have hderiv_g : ∀ᶠ z in 𝓝 z₀, AnalyticAt ℂ g z := hgan.eventually_analyticAt
  have hd_local : ∀ᶠ z in 𝓝 z₀,
      deriv E z = (z - z₀) ^ (m - 1) * ((m : ℂ) * g z + (z - z₀) * deriv g z) := by
    obtain ⟨U, hU_sub, hU_open, hz₀U⟩ := eventually_nhds_iff.mp (hEg.and hderiv_g)
    filter_upwards [hU_open.mem_nhds hz₀U] with z hzU
    have hev : E =ᶠ[𝓝 z] fun w => (w - z₀) ^ m * g w := by
      filter_upwards [hU_open.mem_nhds hzU] with w hwU
      exact (hU_sub w hwU).1
    have hgz : DifferentiableAt ℂ g z := (hU_sub z hzU).2.differentiableAt
    have hd1 : HasDerivAt (fun w : ℂ => (w - z₀) ^ m)
        ((m : ℂ) * (z - z₀) ^ (m - 1)) z := by
      have h := ((hasDerivAt_id' z).sub_const z₀).fun_pow m
      rwa [mul_one] at h
    have hd2 : HasDerivAt (fun w : ℂ => (w - z₀) ^ m * g w)
        ((m : ℂ) * (z - z₀) ^ (m - 1) * g z + (z - z₀) ^ m * deriv g z) z :=
      hd1.mul hgz.hasDerivAt
    rw [hev.deriv_eq, hd2.deriv]
    have hpow : (z - z₀) ^ m = (z - z₀) ^ (m - 1) * (z - z₀) := by
      conv_lhs => rw [← Nat.sub_add_cancel hm_pos, pow_succ]
    rw [hpow]
    ring
  have hcancel : ∀ᶠ z in 𝓝[≠] z₀,
      (m : ℂ) * g z + (z - z₀) * deriv g z = (z - z₀) * W z * g z := by
    filter_upwards [nhdsWithin_le_nhds (hEqC.and (hd_local.and hEg)),
      self_mem_nhdsWithin] with z ⟨h1, h2, h3⟩ hz
    have hsub0 : z - z₀ ≠ 0 := sub_ne_zero.mpr hz
    have hpow : (z - z₀) ^ m = (z - z₀) ^ (m - 1) * (z - z₀) := by
      conv_lhs => rw [← Nat.sub_add_cancel hm_pos, pow_succ]
    rw [h2, h3, hpow] at h1
    have h1' : (z - z₀) ^ (m - 1) * ((m : ℂ) * g z + (z - z₀) * deriv g z) =
        (z - z₀) ^ (m - 1) * ((z - z₀) * W z * g z) := by linear_combination h1
    exact mul_left_cancel₀ (pow_ne_zero _ hsub0) h1'
  have hlhs : Tendsto (fun z => (m : ℂ) * g z + (z - z₀) * deriv g z)
      (𝓝[≠] z₀) (𝓝 ((m : ℂ) * g z₀)) := by
    have hc : ContinuousAt (fun z => (m : ℂ) * g z + (z - z₀) * deriv g z) z₀ :=
      (continuousAt_const.mul hgan.continuousAt).add
        ((continuousAt_id.sub continuousAt_const).mul hgan.deriv.continuousAt)
    simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
  have hrhs : Tendsto (fun z => (z - z₀) * W z * g z) (𝓝[≠] z₀) (𝓝 0) := by
    have hc : ContinuousAt (fun z => (z - z₀) * W z * g z) z₀ :=
      ((continuousAt_id.sub continuousAt_const).mul hW.continuousAt).mul hgan.continuousAt
    simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
  have hnb : (𝓝[≠] z₀).NeBot := mem_closure_iff_nhdsWithin_neBot.mp (by simp)
  have hm0 := tendsto_nhds_unique (hlhs.congr' hcancel) hrhs
  have hm_ne : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  exact mul_ne_zero hm_ne hg0 hm0

private theorem ne_zero_at_endpoint_of_nonneg_logDeriv_analytic {E A : ℂ → ℂ} {c : ℝ}
    (hE : Differentiable ℂ E) (hE_nz : ∃ z₀, E z₀ ≠ 0)
    (hAan : AnalyticAt ℂ A (c : ℂ))
    (hnonneg : ∀ᶠ t : ℝ in 𝓝[>] c, 0 ≤ (-logDeriv E (t : ℂ) + A (t : ℂ)).re) :
    E (c : ℂ) ≠ 0 := by
  intro h0
  set z₀ : ℂ := (c : ℂ) with hz₀
  have hEan : AnalyticOnNhd ℂ E univ := hE.differentiableOn.analyticOnNhd isOpen_univ
  obtain ⟨z₁, hz₁⟩ := hE_nz
  have hntop : analyticOrderAt E z₀ ≠ ⊤ :=
    hEan.analyticOrderAt_ne_top_of_isPreconnected isPreconnected_univ (mem_univ z₁) (mem_univ z₀)
      (by rw [(hEan z₁ (mem_univ z₁)).analyticOrderAt_eq_zero.mpr hz₁]; exact ENat.zero_ne_top)
  have hne0 : analyticOrderAt E z₀ ≠ 0 := fun hz =>
    ((hEan z₀ (mem_univ z₀)).analyticOrderAt_eq_zero.mp hz) h0
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp hntop
  have hm_pos : 1 ≤ m := by
    rcases eq_or_ne m 0 with rfl | hm0
    · exact absurd hm.symm hne0
    · omega
  obtain ⟨g, hgan, hg0, hEg₀⟩ := (hEan z₀ (mem_univ z₀)).analyticOrderAt_eq_natCast.mp hm.symm
  have hEg : ∀ᶠ z in 𝓝 z₀, E z = (z - z₀) ^ m * g z := by
    filter_upwards [hEg₀] with z hz
    simpa only [smul_eq_mul] using hz
  have hlog : ∀ᶠ z in 𝓝[≠] z₀, logDeriv E z = (m : ℂ) / (z - z₀) + logDeriv g z := by
    have hgnz : ∀ᶠ z in 𝓝 z₀, g z ≠ 0 := hgan.continuousAt.eventually_ne hg0
    have hgan' : ∀ᶠ z in 𝓝 z₀, AnalyticAt ℂ g z := hgan.eventually_analyticAt
    obtain ⟨U, hU_sub, hU_open, hz₀U⟩ := eventually_nhds_iff.mp (hEg.and (hgnz.and hgan'))
    filter_upwards [nhdsWithin_le_nhds (hU_open.mem_nhds hz₀U), self_mem_nhdsWithin] with z hzU hz
    have hev : E =ᶠ[𝓝 z] fun w => (w - z₀) ^ m * g w := by
      filter_upwards [hU_open.mem_nhds hzU] with w hwU
      exact (hU_sub w hwU).1
    have hsub0 : z - z₀ ≠ 0 := sub_ne_zero.mpr hz
    have hgz0 : g z ≠ 0 := (hU_sub z hzU).2.1
    have hgd : DifferentiableAt ℂ g z := (hU_sub z hzU).2.2.differentiableAt
    have hsub : DifferentiableAt ℂ (fun w : ℂ => w - z₀) z := differentiableAt_id.sub_const z₀
    have hle1 : logDeriv E z = logDeriv (fun w => (w - z₀) ^ m * g w) z := by
      rw [logDeriv_apply, logDeriv_apply, hev.deriv_eq, hev.eq_of_nhds]
    rw [hle1, logDeriv_mul (f := fun w => (w - z₀) ^ m) (g := g) z (pow_ne_zero m hsub0) hgz0
      (hsub.fun_pow m) hgd, logDeriv_fun_pow hsub m]
    congr 1
    rw [logDeriv_apply, deriv_sub_const, deriv_id'', one_div, div_eq_mul_inv]
  have hgan_ld : AnalyticAt ℂ (logDeriv g) z₀ := hgan.deriv.div hgan hg0
  have ht_ne : Tendsto (fun t : ℝ => (t : ℂ)) (𝓝[>] c) (𝓝[≠] z₀) :=
    (RHTower.tendsto_ofReal_nhdsNE c).mono_left (nhdsWithin_mono c fun _ (ht : c < _) => ne_of_gt ht)
  have hlim : Tendsto
      (fun t : ℝ => (t - c) * (-logDeriv E (t : ℂ) + A (t : ℂ)).re)
      (𝓝[>] c) (𝓝 (-(m : ℝ))) := by
    have hrem : Tendsto (fun t : ℝ => (-logDeriv g (t : ℂ) + A (t : ℂ)).re)
        (𝓝 c) (𝓝 (-logDeriv g z₀ + A z₀).re) := by
      have hc1 : ContinuousAt (fun z : ℂ => (-logDeriv g z + A z).re) z₀ :=
        Complex.continuous_re.continuousAt.comp (hgan_ld.neg.add hAan).continuousAt
      exact hc1.tendsto.comp
        (by simpa only [hz₀] using (Complex.continuous_ofReal.continuousAt (x := c)).tendsto)
    have hsub0 : Tendsto (fun t : ℝ => t - c) (𝓝[>] c) (𝓝 0) := by
      have hc2 : ContinuousAt (fun t : ℝ => t - c) c := continuousAt_id.sub continuousAt_const
      simpa only [sub_self] using hc2.tendsto.mono_left nhdsWithin_le_nhds
    have hprod : Tendsto
        (fun t : ℝ => -(m : ℝ) + (t - c) * (-logDeriv g (t : ℂ) + A (t : ℂ)).re)
        (𝓝[>] c) (𝓝 (-(m : ℝ) + 0 * (-logDeriv g z₀ + A z₀).re)) :=
      tendsto_const_nhds.add (hsub0.mul (hrem.mono_left nhdsWithin_le_nhds))
    simp only [zero_mul, add_zero] at hprod
    refine hprod.congr' ?_
    filter_upwards [ht_ne.eventually hlog, self_mem_nhdsWithin] with t ht htc
    change c < t at htc
    have htc0 : t - c ≠ 0 := sub_ne_zero.mpr (ne_of_gt htc)
    have hcast : ((m : ℂ) / ((t : ℂ) - z₀)).re = (m : ℝ) / (t - c) := by
      have he : (t : ℂ) - z₀ = ((t - c : ℝ) : ℂ) := by rw [hz₀]; push_cast; ring
      have hd : (m : ℂ) / (((t - c : ℝ) : ℂ)) = (((m : ℝ) / (t - c) : ℝ) : ℂ) := by push_cast; rfl
      rw [he, hd, Complex.ofReal_re]
    rw [ht]
    have hre : (-((m : ℂ) / ((t : ℂ) - z₀) + logDeriv g (t : ℂ)) + A (t : ℂ)).re =
        -((m : ℝ) / (t - c)) + (-logDeriv g (t : ℂ) + A (t : ℂ)).re := by
      rw [neg_add, add_assoc, Complex.add_re, Complex.neg_re, hcast]
    rw [hre, mul_add]
    congr 1
    field_simp [htc0]
  have hge0 : ∀ᶠ t : ℝ in 𝓝[>] c, 0 ≤ (t - c) * (-logDeriv E (t : ℂ) + A (t : ℂ)).re := by
    filter_upwards [hnonneg, self_mem_nhdsWithin] with t ht htc
    change c < t at htc
    exact mul_nonneg (by linarith) ht
  have hnb : (𝓝[>] c).NeBot := nhdsWithin_Ioi_neBot le_rfl
  have hle0 : (0 : ℝ) ≤ -(m : ℝ) := ge_of_tendsto hlim hge0
  have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm_pos
  linarith

/-- Strict archimedean reflection negativity at the symmetry center `s = 1/2`:
`Re(logDeriv Γ_ℝ(1/2)) < 0`. -/
theorem re_logDeriv_Gammaℝ_half_neg :
    (logDeriv Complex.Gammaℝ (1 / 2 : ℂ)).re < 0 := by
  have hG := RHTower.logDeriv_Gammaℝ_digamma (s := (1 / 2 : ℂ)) (by norm_num)
  have hz : (1 / 2 : ℂ) / 2 = (1 / 4 : ℂ) := by norm_num
  rw [hz] at hG
  have hne0 : ∀ m : ℕ, (1 / 4 : ℂ) ≠ -(m : ℂ) := by
    intro m hm; have := congrArg Complex.re hm; simp at this
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m; linarith
  have hne1 : ∀ m : ℕ, (1 / 4 : ℂ) + 1 ≠ -(m : ℂ) := by
    intro m hm; have := congrArg Complex.re hm; simp at this
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m; linarith
  have hd1 := congrArg Complex.re (Complex.digamma_apply_add_one (1 / 4 : ℂ) hne0)
  have hd2 := congrArg Complex.re (Complex.digamma_apply_add_one ((1 / 4 : ℂ) + 1) hne1)
  rw [Complex.add_re] at hd1 hd2
  have hi1 : ((1 / 4 : ℂ)⁻¹).re = 4 := by norm_num
  have hi2 : (((1 / 4 : ℂ) + 1)⁻¹).re = 4 / 5 := by norm_num
  rw [hi1] at hd1
  rw [hi2] at hd2
  set w : ℂ := (1 / 4 : ℂ) + 1 + 1
  have hw_eq : w = ((9 / 4 : ℝ) : ℂ) := by dsimp [w]; push_cast; ring
  have hw_norm : ‖w‖ = 9 / 4 := by
    rw [hw_eq, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by norm_num)]
  have hstir := norm_digamma_sub_log_le_of_re_pos (z := w) (by rw [hw_eq]; norm_num)
    (by rw [hw_eq]; norm_num)
  have hle : (Complex.digamma w - Complex.log w).re ≤ 3 / ‖w‖ :=
    (Complex.re_le_norm _).trans hstir
  rw [Complex.sub_re, Complex.log_re, hw_norm] at hle
  have hlog94 : Real.log (9 / 4 : ℝ) ≤ 5 / 4 := by
    linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 9 / 4 by norm_num)]
  have hpi : 0 < Real.log Real.pi := Real.log_pos (by linarith [Real.pi_gt_three])
  rw [hG]
  simp only [Complex.sub_re, Complex.div_ofNat_re, Complex.ofReal_re]
  linarith

/-- **Reference-free impossibility of entire (`κ = 0`) Laplace-positive completions.** Let `d ≥ 1`,
`ν` be a Borel measure on `ℝ` with `laplaceMass ν σ₁ ≠ ⊤`, and `Λ` be a nonzero entire function
satisfying `Λ(1 − s) = ε Λ(s)` (`ε ≠ 0`). Then `Λ` cannot satisfy `Λ(σ) ≠ 0` and
`−logDeriv Λ(σ) + d logDeriv Γ_ℝ(σ) = laplaceReal ν σ` along `(σ₁, ∞)` (even without any
finite-order hypothesis on `Λ`). -/
theorem no_entire_laplace_completed_system {d : ℕ} (hd : 1 ≤ d) {ν : Measure ℝ} {σ₁ : ℝ}
    (hconv₁ : laplaceMass ν σ₁ ≠ ⊤)
    {Λ : ℂ → ℂ} (hΛ : Differentiable ℂ Λ) (hΛ_nz : ∃ z₀, Λ z₀ ≠ 0)
    {ε : ℂ} (hε : ε ≠ 0) (hsym : ∀ s, Λ (1 - s) = ε * Λ s)
    (hΛ_ray : ∀ σ : ℝ, σ₁ < σ → Λ (σ : ℂ) ≠ 0)
    (hagree : ∀ σ : ℝ, σ₁ < σ →
      -logDeriv Λ (σ : ℂ) + (d : ℂ) * logDeriv Complex.Gammaℝ (σ : ℂ) =
        ((laplaceReal ν σ : ℝ) : ℂ)) :
    False := by
  have hΛan : AnalyticOnNhd ℂ Λ univ := hΛ.differentiableOn.analyticOnNhd isOpen_univ
  have hΓ_diffOn : DifferentiableOn ℂ Complex.Gammaℝ {z : ℂ | 0 < z.re} := fun z hz =>
    (GaloisForLFunctions.differentiableAt_Gammaℝ hz).differentiableWithinAt
  have hAan : ∀ t : ℝ, 0 < t →
      AnalyticAt ℂ (fun z => (d : ℂ) * logDeriv Complex.Gammaℝ z) (t : ℂ) := by
    intro t ht
    have hopen : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const Complex.continuous_re
    have hΓan : AnalyticAt ℂ Complex.Gammaℝ (t : ℂ) :=
      hΓ_diffOn.analyticAt (hopen.mem_nhds (by simpa using ht))
    exact analyticAt_const.mul
      (hΓan.deriv.div hΓan (Complex.Gammaℝ_ne_zero_of_re_pos (by simpa using ht)))
  -- Propagate along `(c, ∞)` whenever `c ≥ 0` and `complexLaplace ν` is holomorphic on `Re z > c`.
  have hpropagate : ∀ c : ℝ, 0 ≤ c →
      DifferentiableOn ℂ (complexLaplace ν) {z : ℂ | c < z.re} →
      ∀ t : ℝ, c < t →
        Λ (t : ℂ) ≠ 0 ∧
          -logDeriv Λ (t : ℂ) + (d : ℂ) * logDeriv Complex.Gammaℝ (t : ℂ) =
            ((laplaceReal ν t : ℝ) : ℂ) := by
    intro c hc0 hCLdiff
    set W : ℂ → ℂ := fun z => (d : ℂ) * logDeriv Complex.Gammaℝ z - complexLaplace ν z with hWdef
    have hWan : ∀ t : ℝ, c < t → AnalyticAt ℂ W (t : ℂ) := by
      intro t ht
      have hopen : IsOpen {z : ℂ | c < z.re} := isOpen_lt continuous_const Complex.continuous_re
      have hCL : AnalyticAt ℂ (complexLaplace ν) (t : ℂ) :=
        hCLdiff.analyticAt (hopen.mem_nhds (by simpa using ht))
      exact (hAan t (lt_of_le_of_lt hc0 ht)).sub hCL
    have hode_all : ∀ t : ℝ, c < t → deriv Λ (t : ℂ) = W (t : ℂ) * Λ (t : ℂ) := by
      have h1 : AnalyticOnNhd ℝ (fun t : ℝ => deriv Λ (t : ℂ)) (Ioi c) :=
        fun t _ => RHTower.analyticAt_ofReal_comp (hΛan (t : ℂ) (mem_univ _)).deriv
      have h2 : AnalyticOnNhd ℝ (fun t : ℝ => W (t : ℂ) * Λ (t : ℂ)) (Ioi c) :=
        fun t ht => RHTower.analyticAt_ofReal_comp ((hWan t ht).mul (hΛan (t : ℂ) (mem_univ _)))
      set t₁ : ℝ := max c σ₁ + 1 with ht₁def
      have ht₁c : c < t₁ := by rw [ht₁def]; linarith [le_max_left c σ₁]
      have ht₁s : σ₁ < t₁ := by rw [ht₁def]; linarith [le_max_right c σ₁]
      have hev : (fun t : ℝ => deriv Λ (t : ℂ)) =ᶠ[𝓝 t₁]
          fun t : ℝ => W (t : ℂ) * Λ (t : ℂ) := by
        filter_upwards [isOpen_Ioi.mem_nhds ht₁s] with t ht
        change σ₁ < t at ht
        have hag := hagree t ht
        rw [← complexLaplace_ofReal] at hag
        have hld : logDeriv Λ (t : ℂ) = W (t : ℂ) := by
          rw [hWdef]; linear_combination -hag
        rw [logDeriv_apply] at hld
        exact (div_eq_iff (hΛ_ray t ht)).mp hld
      exact fun t ht => h1.eqOn_of_preconnected_of_eventuallyEq h2 isPreconnected_Ioi ht₁c hev ht
    intro t ht
    have hΛt0 : Λ (t : ℂ) ≠ 0 := by
      refine ne_zero_of_entire_linear_ode' hΛ hΛ_nz (hWan t ht) ?_
      filter_upwards [nhdsWithin_le_nhds (isOpen_Ioi.mem_nhds ht)] with y hy
      exact hode_all y hy
    refine ⟨hΛt0, ?_⟩
    have hld : logDeriv Λ (t : ℂ) = W (t : ℂ) := by
      rw [logDeriv_apply, div_eq_iff hΛt0]; exact hode_all t ht
    rw [hld]; dsimp only [W]; rw [complexLaplace_ofReal]; ring
  -- Step A: `laplaceMass ν σ ≠ ⊤` for all `σ > 0`.
  have hfin_pos : ∀ σ : ℝ, 0 < σ → laplaceMass ν σ ≠ ⊤ := by
    intro σ₀ hσ₀ htop
    obtain ⟨c, hc⟩ := exists_isAbscissa ⟨σ₁, hconv₁⟩ ⟨σ₀, htop⟩
    have hc_pos : 0 < c := by
      by_contra hle
      exact hc.1 σ₀ (lt_of_le_of_lt (not_lt.mp hle) hσ₀) htop
    have hray := hpropagate c hc_pos.le (differentiableOn_complexLaplace hc)
    have hnonneg : ∀ᶠ t : ℝ in 𝓝[>] c,
        0 ≤ (-logDeriv Λ (t : ℂ) + (d : ℂ) * logDeriv Complex.Gammaℝ (t : ℂ)).re := by
      filter_upwards [self_mem_nhdsWithin] with t ht
      change c < t at ht
      rw [(hray t ht).2, Complex.ofReal_re]
      exact integral_nonneg fun _ => (Real.exp_pos _).le
    have hΛc : Λ (c : ℂ) ≠ 0 :=
      ne_zero_at_endpoint_of_nonneg_logDeriv_analytic hΛ hΛ_nz (hAan c hc_pos) hnonneg
    have hΦan : AnalyticAt ℂ
        (fun z => -logDeriv Λ z + (d : ℂ) * logDeriv Complex.Gammaℝ z) (c : ℂ) :=
      ((hΛan (c : ℂ) (mem_univ _)).deriv.div (hΛan (c : ℂ) (mem_univ _)) hΛc).neg.add
        (hAan c hc_pos)
    obtain ⟨δ, hδ, hball⟩ := hΦan.exists_ball_analyticOnNhd
    exact false_of_analyticAt_abscissa hc hδ hball (fun σ hσ _ => (hray σ hσ).2)
  -- Step B: `ν + volume` has abscissa `0`, so `complexLaplace ν` is holomorphic on `Re z > 0`.
  have hc_sum : IsAbscissa (ν + volume) 0 := by
    have hmass : ∀ σ : ℝ, laplaceMass (ν + volume) σ = laplaceMass ν σ + laplaceMass volume σ := by
      intro σ; unfold laplaceMass; rw [Measure.restrict_add, lintegral_add_measure]
    exact ⟨fun σ hσ => by
        rw [hmass σ]; exact ENNReal.add_ne_top.mpr ⟨hfin_pos σ hσ, isAbscissa_volume_zero.1 σ hσ⟩,
      fun σ hσ => by rw [hmass σ, isAbscissa_volume_zero.2 σ hσ, add_top]⟩
  have hCL_pos : DifferentiableOn ℂ (complexLaplace ν) {z : ℂ | 0 < z.re} := by
    refine ((differentiableOn_complexLaplace hc_sum).sub
      (differentiableOn_complexLaplace isAbscissa_volume_zero)).congr fun z hz => ?_
    change 0 < z.re at hz
    have hi_sum := integrable_cexp_of_gt_abscissa hc_sum hz
    rw [Measure.restrict_add] at hi_sum
    have hi_nu : Integrable (fun u : ℝ => Complex.exp (-z * (u : ℂ)))
        (ν.restrict (Ioi (0 : ℝ))) := hi_sum.left_of_add_measure
    have hi_vol := integrable_cexp_of_gt_abscissa isAbscissa_volume_zero hz
    simp only [Pi.sub_apply, complexLaplace]
    rw [Measure.restrict_add, integral_add_measure hi_nu hi_vol]
    ring
  have hhalf := (hpropagate 0 le_rfl hCL_pos (1 / 2) (by norm_num)).2
  have hlogΛ_half : logDeriv Λ (1 / 2 : ℂ) = 0 := by
    have hodd := RHTower.CompletionZeroPairs.logDeriv_one_sub hΛ hε hsym (1 / 2 : ℂ)
    have hsub : (1 : ℂ) - (1 / 2 : ℂ) = (1 / 2 : ℂ) := by norm_num
    rw [hsub] at hodd
    linear_combination hodd / 2
  have hcast_half : (((1 / 2 : ℝ) : ℂ)) = (1 / 2 : ℂ) := by norm_num
  rw [hcast_half, hlogΛ_half, neg_zero, zero_add] at hhalf
  have hre_eq := congrArg Complex.re hhalf
  rw [← Complex.ofReal_natCast, Complex.re_ofReal_mul, Complex.ofReal_re] at hre_eq
  have hl_nn : 0 ≤ laplaceReal ν (1 / 2) := integral_nonneg fun _ => (Real.exp_pos _).le
  have hd_pos : (0 : ℝ) < d := by exact_mod_cast hd
  have hneg : (d : ℝ) * (logDeriv Complex.Gammaℝ (1 / 2 : ℂ)).re < 0 :=
    mul_neg_of_pos_of_neg hd_pos re_logDeriv_Gammaℝ_half_neg
  linarith

/-! ### 4. Universal archimedean real-zero budget and simple-pole real-line nonvanishing -/

/-- Strict archimedean bound at `s = 2`: `Re(logDeriv Γ_ℝ(2)) = (−γ − log π) / 2 < −5 / 6`. -/
theorem re_logDeriv_Gammaℝ_two_lt :
    (logDeriv Complex.Gammaℝ 2).re < -5 / 6 := by
  have hG := RHTower.logDeriv_Gammaℝ_digamma (s := (2 : ℂ)) (by norm_num)
  have hz : (2 : ℂ) / 2 = 1 := by norm_num
  rw [hz, Complex.digamma_one] at hG
  have hre : (logDeriv Complex.Gammaℝ 2).re =
      (-Real.eulerMascheroniConstant - Real.log Real.pi) / 2 := by
    rw [hG]
    simp only [Complex.sub_re, Complex.div_ofNat_re, Complex.neg_re, Complex.ofReal_re]
    ring
  rw [hre]
  -- Lower bound `γ > 0.545` from `eulerMascheroniSeq 15 < γ` (`15 + 1 = 2^4`).
  have hγ_seq := Real.eulerMascheroniSeq_lt_eulerMascheroniConstant 15
  rw [Real.eulerMascheroniSeq] at hγ_seq
  have hh15 : (3.318 : ℝ) < (harmonic 15 : ℝ) := by norm_num
  have hlog16 : Real.log ((15 : ℕ) + 1 : ℝ) = 4 * Real.log 2 := by
    rw [show ((15 : ℕ) + 1 : ℝ) = 2 ^ (4 : ℕ) by norm_num, Real.log_pow]
    push_cast; ring
  rw [hlog16] at hγ_seq
  have hγ_gt : (0.545 : ℝ) < Real.eulerMascheroniConstant := by
    linarith [Real.log_two_lt_d9, hh15, hγ_seq]
  -- Lower bound `log π > 1.134` from `1 − e/π ≤ log(π/e) = log π − 1`.
  have hpi_pos : 0 < Real.pi := Real.pi_pos
  have he_pos : 0 < Real.exp 1 := Real.exp_pos 1
  have hlog_pie := Real.one_sub_inv_le_log_of_pos (show 0 < Real.pi / Real.exp 1 by positivity)
  have hlog_split : Real.log (Real.pi / Real.exp 1) = Real.log Real.pi - 1 := by
    rw [Real.log_div hpi_pos.ne' he_pos.ne', Real.log_exp]
  have hinv_pie : (Real.pi / Real.exp 1)⁻¹ < (2.718282 : ℝ) / (3.1415 : ℝ) := by
    rw [inv_div]
    have he_lt : Real.exp 1 < 2.718282 := by linarith [Real.exp_one_lt_d9]
    have hpi_gt : (3.1415 : ℝ) < Real.pi := Real.pi_gt_d4
    calc Real.exp 1 / Real.pi < 2.718282 / Real.pi :=
          div_lt_div_of_pos_right he_lt hpi_pos
      _ < 2.718282 / 3.1415 :=
          div_lt_div_of_pos_left (by norm_num) (by norm_num) hpi_gt
  have hlog_pi_gt : (1.134 : ℝ) < Real.log Real.pi := by
    linarith [hlog_pie, hlog_split, hinv_pie]
  linarith

/-- **Universal archimedean real-zero budget.** For any `CompletedPositiveSystem κ d F Λ` and any
finite set `X ⊂ (1/2, 1]` of off-central real points,
`4 ord_{1/2}(Λ) + 8 ∑_{x ∈ X} ord_x(Λ) + 5 d < 9 κ`. -/
theorem real_zero_archimedean_budget {κ d : ℕ} {F Λ : ℂ → ℂ}
    (hS : CompletedPositiveSystem κ d F Λ) (X : Finset ℝ)
    (hX : ∀ x ∈ X, 1 / 2 < x ∧ x ≤ 1) :
    4 * (analyticOrderAt Λ (1 / 2 : ℂ)).toNat +
      8 * (∑ x ∈ X, (analyticOrderAt Λ (x : ℂ)).toNat) + 5 * d < 9 * κ := by
  classical
  -- Step 1: Upper bound `Re(logDeriv Λ 2) < (3/2) κ - (5/6) d` from positivity at `σ = 2`.
  have hpos2 : 0 ≤ (-logDeriv F (2 : ℂ)).re := by
    have hpd := (hS.posDef_neg_logDeriv (σ := 2) (by norm_num)).posDef 1 (fun _ => 0) (fun _ => 1)
    simpa using hpd
  have hdecomp := congrArg Complex.re (hS.neg_logDeriv_F_eq (s := 2) (by norm_num))
  have hre2 : ((κ : ℂ) * (1 / (2 : ℂ) + 1 / ((2 : ℂ) - 1)) +
      (d : ℂ) * logDeriv Complex.Gammaℝ 2 - logDeriv Λ 2).re =
      (3 / 2 : ℝ) * (κ : ℝ) + (d : ℝ) * (logDeriv Complex.Gammaℝ 2).re - (logDeriv Λ 2).re := by
    rw [Complex.sub_re, Complex.add_re, ← Complex.ofReal_natCast, Complex.re_ofReal_mul,
        ← Complex.ofReal_natCast, Complex.re_ofReal_mul]
    have hp : (1 / (2 : ℂ) + 1 / ((2 : ℂ) - 1)).re = 3 / 2 := by norm_num
    rw [hp]
    ring
  rw [hre2] at hdecomp
  have hd_pos : (0 : ℝ) < d := by exact_mod_cast hS.degree_pos
  have hd_arch : (d : ℝ) * (logDeriv Complex.Gammaℝ 2).re < -(5 / 6 : ℝ) * (d : ℝ) := by
    have := mul_lt_mul_of_pos_left re_logDeriv_Gammaℝ_two_lt hd_pos
    linarith
  have hΛ2_lt : (logDeriv Λ 2).re < (3 / 2 : ℝ) * (κ : ℝ) - (5 / 6 : ℝ) * (d : ℝ) := by
    linarith
  -- Step 2: Lower bound `Re(logDeriv Λ 2)` from Hadamard zero-pair copies at `1/2` and `X ∪ (1 - X)`.
  set f : ℂ → ℂ := fun z => Λ (z + 2) with hfdef
  have hfd : Differentiable ℂ f := hS.entire_Λ.comp (differentiable_id.add_const 2)
  have hf : AnalyticOnNhd ℂ f univ := hfd.differentiableOn.analyticOnNhd isOpen_univ
  obtain ⟨C, hC, hgrow⟩ := hS.orderOne_Λ
  have hsum_c : HasSum (fun q : ZeroCopy f =>
      (1 / 2 : ℂ) * gPair (zeroCopyPoint f q + 2) 2) (logDeriv Λ 2) :=
    hasSum_logDeriv_zeroPairs hS.entire_Λ one_ne_zero
      (fun w => by rw [hS.sym_Λ w, one_mul]) hC.le
      (fun w => by simpa only [orderOneWeight] using hgrow w)
      hS.two_ne_zero hS.two_ne_zero
  set term : ZeroCopy f → ℝ := fun q => ((1 / 2 : ℂ) * gPair (zeroCopyPoint f q + 2) 2).re
  have hsum_re : HasSum term (logDeriv Λ 2).re := hsum_c.mapL Complex.reCLM
  have hterm_nn : ∀ q : ZeroCopy f, 0 ≤ term q := by
    intro q
    have hzq0 : Λ (zeroCopyPoint f q + 2) = 0 := by simpa [hfdef] using apply_zeroCopyPoint hf q
    obtain ⟨h0, h1⟩ := hS.zero_re_mem_Icc hzq0
    simp only [term, gPair]
    have ha : 0 ≤ (1 / ((2 : ℂ) - (zeroCopyPoint f q + 2))).re := by
      rw [one_div, Complex.inv_re, Complex.sub_re]
      have h2re : (2 : ℂ).re = 2 := by norm_num
      exact div_nonneg (by rw [h2re]; linarith) (Complex.normSq_nonneg _)
    have hb : 0 ≤ (1 / ((2 : ℂ) - (1 - (zeroCopyPoint f q + 2)))).re := by
      rw [one_div, Complex.inv_re, Complex.sub_re, Complex.sub_re]
      have h2re : (2 : ℂ).re = 2 := by norm_num
      have h1re : (1 : ℂ).re = 1 := by norm_num
      exact div_nonneg (by rw [h2re, h1re]; linarith) (Complex.normSq_nonneg _)
    have he : ((1 / 2 : ℂ) * (1 / ((2 : ℂ) - (zeroCopyPoint f q + 2)) +
        1 / ((2 : ℂ) - (1 - (zeroCopyPoint f q + 2))))).re =
        ((1 / ((2 : ℂ) - (zeroCopyPoint f q + 2))).re +
          (1 / ((2 : ℂ) - (1 - (zeroCopyPoint f q + 2)))).re) / 2 := by
      have : (1 / 2 : ℂ) * (1 / ((2 : ℂ) - (zeroCopyPoint f q + 2)) +
          1 / ((2 : ℂ) - (1 - (zeroCopyPoint f q + 2)))) =
          (1 / ((2 : ℂ) - (zeroCopyPoint f q + 2)) +
            1 / ((2 : ℂ) - (1 - (zeroCopyPoint f q + 2)))) / 2 := by ring
      rw [this, Complex.div_ofNat_re, Complex.add_re]
    linarith
  have hdiv_toNat : ∀ w : ℂ,
      ((MeromorphicOn.divisor f univ) (w - 2)).toNat = (analyticOrderAt Λ w).toNat := by
    intro w
    have hg_an : AnalyticAt ℂ (fun z : ℂ => z + 2) (w - 2) := by fun_prop
    have hg_d : deriv (fun z : ℂ => z + 2) (w - 2) ≠ 0 := by
      rw [((hasDerivAt_id' (w - 2)).add_const 2).deriv]; exact one_ne_zero
    have hcomp := analyticOrderAt_comp_of_deriv_ne_zero (f := Λ) hg_an hg_d
    have hfeq : Λ ∘ (fun z : ℂ => z + 2) = f := rfl
    rw [hfeq, sub_add_cancel] at hcomp
    rw [divisor_univ_eq_analyticOrder hf, hcomp]
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp (hS.orderAt_ne_top w)
    rw [← hn]; simp
  -- Opaque divisor-copy witness so analytic arithmetic never unfolds `MeromorphicOn.divisor`.
  obtain ⟨allCopiesAt, hall_pt, hall_card, hall_disj⟩ :
      ∃ allCopiesAt : ℂ → Finset (ZeroCopy f),
        (∀ w : ℂ, ∀ q ∈ allCopiesAt w, zeroCopyPoint f q + 2 = w) ∧
        (∀ w : ℂ, (allCopiesAt w).card = (analyticOrderAt Λ w).toNat) ∧
        (∀ w₁ w₂ : ℂ, w₁ ≠ w₂ → Disjoint (allCopiesAt w₁) (allCopiesAt w₂)) := by
    let cAt : ℂ → Finset (ZeroCopy f) := fun w =>
      if hw : w - 2 ∈ (MeromorphicOn.divisor f univ).support then
        Finset.univ.map ⟨fun j : Fin ((MeromorphicOn.divisor f univ) (w - 2)).toNat =>
          ⟨⟨w - 2, hw⟩, j⟩, fun j₁ j₂ heq => by
            simp only [Sigma.mk.injEq, heq_eq_eq] at heq
            exact heq.2⟩
      else ∅
    have hc_pt : ∀ w : ℂ, ∀ q ∈ cAt w, zeroCopyPoint f q + 2 = w := by
      intro w q hq
      dsimp only [cAt] at hq
      split_ifs at hq with hw
      · obtain ⟨j, _, rfl⟩ := Finset.mem_map.mp hq
        change (w - 2) + 2 = w
        ring
      · exact absurd hq (Finset.notMem_empty _)
    have hc_card : ∀ w : ℂ, (cAt w).card = (analyticOrderAt Λ w).toNat := by
      intro w
      dsimp only [cAt]
      split_ifs with hw
      · rw [Finset.card_map, Finset.card_univ, Fintype.card_fin, hdiv_toNat]
      · symm
        rw [← hdiv_toNat]
        by_contra hne
        have hpos : 0 < ((MeromorphicOn.divisor f univ) (w - 2)).toNat := Nat.pos_of_ne_zero hne
        apply hw
        rw [Function.mem_support]
        intro hz0
        rw [hz0] at hpos
        simp at hpos
    have hc_disj : ∀ w₁ w₂ : ℂ, w₁ ≠ w₂ → Disjoint (cAt w₁) (cAt w₂) := by
      intro w₁ w₂ hne
      rw [Finset.disjoint_left]
      intro q h1 h2
      exact hne ((hc_pt w₁ q h1).symm.trans (hc_pt w₂ q h2))
    exact ⟨cAt, hc_pt, hc_card, hc_disj⟩
  -- Central copies at `1/2` and paired real copies `{x, 1 - x}` for `x ∈ X`, extracted opaquely.
  obtain ⟨S_tot, htot_bound⟩ :
      ∃ S_tot : Finset (ZeroCopy f),
        (2 / 3 : ℝ) * ((analyticOrderAt Λ (1 / 2 : ℂ)).toNat : ℝ) +
          (4 / 3 : ℝ) * (∑ x ∈ X, ((analyticOrderAt Λ (x : ℂ)).toNat : ℝ)) ≤
            ∑ q ∈ S_tot, term q := by
    let pairCopies : ℝ → Finset (ZeroCopy f) := fun x =>
      allCopiesAt (x : ℂ) ∪ allCopiesAt (1 - (x : ℂ))
    have hhalf_disj_pair : ∀ x ∈ X, Disjoint (allCopiesAt (1 / 2 : ℂ)) (pairCopies x) := by
      intro x hx
      obtain ⟨hx_gt, _⟩ := hX x hx
      rw [Finset.disjoint_union_right]
      refine ⟨hall_disj _ _ (fun h => ?_), hall_disj _ _ (fun h => ?_)⟩
      · have := congrArg Complex.re h; simp at this; linarith
      · have := congrArg Complex.re h; simp at this; linarith
    have hpair_disj : ∀ x ∈ X, ∀ y ∈ X, x ≠ y → Disjoint (pairCopies x) (pairCopies y) := by
      intro x hx y hy hxy
      obtain ⟨hx_gt, _⟩ := hX x hx
      obtain ⟨hy_gt, _⟩ := hX y hy
      simp only [pairCopies, Finset.disjoint_union_left, Finset.disjoint_union_right]
      refine ⟨⟨hall_disj _ _ (Complex.ofReal_ne_ofReal.mpr hxy), hall_disj _ _ (fun h => ?_)⟩,
              ⟨hall_disj _ _ (fun h => ?_), hall_disj _ _ (fun h => ?_)⟩⟩
      · have := congrArg Complex.re h; simp at this; linarith
      · have := congrArg Complex.re h; simp at this; linarith
      · apply hxy; have := congrArg Complex.re h; simp at this; linarith
    have hsum_half : ((2 / 3 : ℝ) * ((analyticOrderAt Λ (1 / 2 : ℂ)).toNat : ℝ)) ≤
        ∑ q ∈ allCopiesAt (1 / 2 : ℂ), term q := by
      have hpt_val : ∀ q ∈ allCopiesAt (1 / 2 : ℂ), term q = 2 / 3 := by
        intro q hq
        rw [show term q = ((1 / 2 : ℂ) * gPair (zeroCopyPoint f q + 2) 2).re from rfl,
            hall_pt _ q hq]
        unfold gPair
        norm_num
      rw [Finset.sum_congr rfl hpt_val, Finset.sum_const, hall_card, nsmul_eq_mul, mul_comm]
    have hsum_pair : ∀ x ∈ X,
        (4 / 3 : ℝ) * ((analyticOrderAt Λ (x : ℂ)).toNat : ℝ) ≤ ∑ q ∈ pairCopies x, term q := by
      intro x hx
      obtain ⟨hx_gt, hx_le⟩ := hX x hx
      have hne_x : (x : ℂ) ≠ 1 - (x : ℂ) := fun h => by
        have := congrArg Complex.re h; simp at this; linarith
      dsimp only [pairCopies]
      rw [Finset.sum_union (hall_disj _ _ hne_x)]
      have hval1 : ∀ q ∈ allCopiesAt (x : ℂ),
          term q = (1 / (2 - x) + 1 / (1 + x)) / 2 := by
        intro q hq
        rw [show term q = ((1 / 2 : ℂ) * gPair (zeroCopyPoint f q + 2) 2).re from rfl,
            hall_pt _ q hq]
        unfold gPair
        have e1 : (2 : ℂ) - (x : ℂ) = (((2 - x : ℝ) : ℂ)) := by push_cast; ring
        have e2 : (2 : ℂ) - (1 - (x : ℂ)) = (((1 + x : ℝ) : ℂ)) := by push_cast; ring
        have ec : (1 / 2 : ℂ) * (1 / (((2 - x : ℝ) : ℂ)) + 1 / (((1 + x : ℝ) : ℂ))) =
            ((((1 / (2 - x) + 1 / (1 + x)) / 2 : ℝ) : ℂ)) := by push_cast; ring
        rw [e1, e2, ec, Complex.ofReal_re]
      have hval2 : ∀ q ∈ allCopiesAt (1 - (x : ℂ)),
          term q = (1 / (2 - x) + 1 / (1 + x)) / 2 := by
        intro q hq
        rw [show term q = ((1 / 2 : ℂ) * gPair (zeroCopyPoint f q + 2) 2).re from rfl,
            hall_pt _ q hq]
        unfold gPair
        rw [sub_sub_cancel]
        have e1 : (2 : ℂ) - (1 - (x : ℂ)) = (((1 + x : ℝ) : ℂ)) := by push_cast; ring
        have e2 : (2 : ℂ) - (x : ℂ) = (((2 - x : ℝ) : ℂ)) := by push_cast; ring
        have ec : (1 / 2 : ℂ) * (1 / (((1 + x : ℝ) : ℂ)) + 1 / (((2 - x : ℝ) : ℂ))) =
            ((((1 / (2 - x) + 1 / (1 + x)) / 2 : ℝ) : ℂ)) := by push_cast; ring
        rw [e1, e2, ec, Complex.ofReal_re]
      rw [Finset.sum_congr rfl hval1, Finset.sum_congr rfl hval2,
          Finset.sum_const, Finset.sum_const, hall_card, hall_card,
          hS.orderAt_one_sub (x : ℂ), nsmul_eq_mul, nsmul_eq_mul]
      have hge43 : (4 / 3 : ℝ) ≤ 1 / (2 - x) + 1 / (1 + x) := by
        have hp1 : 0 < 2 - x := by linarith
        have hp2 : 0 < 1 + x := by linarith
        rw [div_add_div _ _ hp1.ne' hp2.ne', div_le_div_iff₀ (by norm_num) (mul_pos hp1 hp2)]
        nlinarith [sq_nonneg (x - 1 / 2)]
      have hord_nn : (0 : ℝ) ≤ ((analyticOrderAt Λ (x : ℂ)).toNat : ℝ) := Nat.cast_nonneg _
      nlinarith
    refine ⟨allCopiesAt (1 / 2 : ℂ) ∪ X.biUnion pairCopies, ?_⟩
    have hdisj_tot : Disjoint (allCopiesAt (1 / 2 : ℂ)) (X.biUnion pairCopies) :=
      Finset.disjoint_biUnion_right.mpr fun x hx => hhalf_disj_pair x hx
    rw [Finset.sum_union hdisj_tot,
        Finset.sum_biUnion (fun x hx y hy hxy => hpair_disj x hx y hy hxy)]
    have hX_sum_le : (4 / 3 : ℝ) * (∑ x ∈ X, ((analyticOrderAt Λ (x : ℂ)).toNat : ℝ)) ≤
        ∑ x ∈ X, ∑ q ∈ pairCopies x, term q := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun x hx => hsum_pair x hx
    linarith [hsum_half, hX_sum_le]
  have htot_le : ∑ q ∈ S_tot, term q ≤ (logDeriv Λ 2).re :=
    sum_le_hasSum S_tot (fun q _ => hterm_nn q) hsum_re
  have hreal_ineq :
      4 * ((analyticOrderAt Λ (1 / 2 : ℂ)).toNat : ℝ) +
        8 * (∑ x ∈ X, ((analyticOrderAt Λ (x : ℂ)).toNat : ℝ)) + 5 * (d : ℝ) <
      9 * (κ : ℝ) := by
    linarith [htot_bound, htot_le, hΛ2_lt]
  have hcast_ineq :
      (((4 * (analyticOrderAt Λ (1 / 2 : ℂ)).toNat +
          8 * (∑ x ∈ X, (analyticOrderAt Λ (x : ℂ)).toNat) + 5 * d : ℕ) : ℝ)) <
      (((9 * κ : ℕ) : ℝ)) := by
    push_cast
    exact hreal_ineq
  exact Nat.cast_lt.mp hcast_ineq

/-- **Degree–pole inequality (`5 d < 9 κ`).** Every `CompletedPositiveSystem κ d F Λ` satisfies
`5 * d < 9 * κ`, generalizing the conductor-one Minkowski–Odlyzko degree bound to arbitrary
positive systems without Euler products. -/
theorem five_mul_degree_lt_nine_mul_poleOrder {κ d : ℕ} {F Λ : ℂ → ℂ}
    (hS : CompletedPositiveSystem κ d F Λ) :
    5 * d < 9 * κ := by
  have h := real_zero_archimedean_budget hS ∅ (fun _ hx => absurd hx (Finset.notMem_empty _))
  simp only [Finset.sum_empty, mul_zero, add_zero] at h
  omega

/-- **Forced pole (`κ ≥ 1`).** No `CompletedPositiveSystem 0 d F Λ` exists for any `d ≥ 1`. -/
theorem not_completedPositiveSystem_zero {d : ℕ} {F Λ : ℂ → ℂ}
    (hS : CompletedPositiveSystem 0 d F Λ) : False := by
  have h := five_mul_degree_lt_nine_mul_poleOrder hS
  have hd := hS.degree_pos
  omega

/-- **Simple-pole degree rigidity.** Every simple-pole `CompletedPositiveSystem 1 d F Λ` forces
archimedean degree `d = 1`. -/
theorem degree_eq_one_of_completedPositiveSystem_one {d : ℕ} {F Λ : ℂ → ℂ}
    (hS : CompletedPositiveSystem 1 d F Λ) : d = 1 := by
  have h := five_mul_degree_lt_nine_mul_poleOrder hS
  have hd := hS.degree_pos
  omega

/-- **Complete real-line nonvanishing at simple pole (`κ = 1`).** In every
`CompletedPositiveSystem 1 d F Λ`, `Λ(x) ≠ 0` for all `x ∈ ℝ` — eliminating both Siegel-type zeros
on `(0, 1) \ {1/2}` and central vanishing at `s = 1/2`. -/
theorem ne_zero_ofReal_of_completedPositiveSystem_one {d : ℕ} {F Λ : ℂ → ℂ}
    (hS : CompletedPositiveSystem 1 d F Λ) (x : ℝ) :
    Λ (x : ℂ) ≠ 0 := by
  intro hx0
  have hd := hS.degree_pos
  obtain ⟨h0, h1⟩ := hS.zero_re_mem_Icc hx0
  simp only [Complex.ofReal_re] at h0 h1
  rcases lt_trichotomy x (1 / 2) with hlt | rfl | hgt
  · have hsym0 : Λ (((1 - x : ℝ) : ℂ)) = 0 := by
      have he : (((1 - x : ℝ) : ℂ)) = 1 - (x : ℂ) := by push_cast; ring
      rw [he, hS.sym_Λ, hx0]
    have hm1 := hS.one_le_order_toNat_of_eq_zero hsym0
    have hbud := real_zero_archimedean_budget hS {1 - x} (fun y hy => by
      rw [Finset.mem_singleton.mp hy]; exact ⟨by linarith, by linarith⟩)
    simp only [Finset.sum_singleton] at hbud
    omega
  · have hcast : (((1 / 2 : ℝ) : ℂ)) = (1 / 2 : ℂ) := by norm_num
    rw [hcast] at hx0
    have hm1 := hS.one_le_order_toNat_of_eq_zero hx0
    have hbud := real_zero_archimedean_budget hS ∅ (fun _ h => absurd h (Finset.notMem_empty _))
    simp only [Finset.sum_empty, mul_zero, add_zero] at hbud
    omega
  · have hm1 := hS.one_le_order_toNat_of_eq_zero hx0
    have hbud := real_zero_archimedean_budget hS {x} (fun y hy => by
      rw [Finset.mem_singleton.mp hy]; exact ⟨hgt, h1⟩)
    simp only [Finset.sum_singleton] at hbud
    omega

end GaloisForLFunctions.StripBochnerWeilForcing
