import GaloisForLFunctions.RHTower.WeilArchReLevyPoleForm
import GaloisForLFunctions.HTGeometry.ThetaSumPeriodParseval

/-!
# Prime-blind positivity for separated narrow bumps

Fix a real `C²` bump `φ` supported in `[−δ/2, δ/2]`, real amplitudes `a_j` and centres `x_j`
(`j < N`), and put

`f(u) = Σ_j a_j φ(u − x_j)`   (`bumpSum`).

Assume the centres are `s`-separated (`|x_i − x_j| ≥ s > 2δ`) and that every difference
`x_i − x_j` (`i ≠ j`) stays at distance more than `δ` from every `log n`, `n ≥ 2`.  If also
`δ < log 2`, then `f ⋆ f̃` vanishes at every `±log n` (`weilTest_bumpSum_log_eq_zero`): the test
is prime-blind by its support geometry, not by cancellation.

**Theorem** (`exists_le_weilArchRe_bumpSum`).  For configurations of span `< log(2/δ)` (in
particular support-blind ones, `abs_sub_lt_log_of_geometry'`) the pole and archimedean part of the
Weil functional is nonnegative once `δ` is small in terms of `s` alone, whatever the number of
bumps:

`W_∞(f ⋆ f̃) ≥ ‖f‖² (A(0) + e^{−s/2} log((s − δ)/δ) − 2√2 e^{δ/2} N √δ)`

(`le_weilArchRe_bumpSum`), with `A(0) = EF.gammaBracket 0`.  The support length of `f` is
unbounded (up to `log(2/δ)`) and the amplitudes have arbitrary signs.  Combined with blindness:
`exists_primeBlind_nonneg_bumpSum`.

Proof (Lévy form `weilArchRe_eq_levy_pole`, `W_∞ = A(0)‖f‖² + ∫_0^∞ ω(x)‖f − f(·+x)‖² dx + 2P`).
* *Lévy energy.*  For `δ < x < s − δ` no bump meets a translate of another, so
  `‖f − f(·+x)‖² = 2‖f‖²`, and `ω(x) ≥ e^{−x/2}/(2x)` gives at least
  `‖f‖² e^{−s/2} log((s−δ)/δ)`.
* *Geometry.*  Every difference `d ≥ log(2/δ)` lies within `δ` of `log ⌊e^d⌋`, so blindness by
  support forces `|x_i − x_j| < log(2/δ)` (`abs_sub_lt_log_of_geometry`).
* *Pole.*  `P = (∫ f e^{u/2})(∫ f e^{−u/2}) = c₊c₋ Σ_{i,j} a_i a_j e^{(x_i − x_j)/2}` with
  `|c_±| ≤ e^{δ/4}‖φ‖₁` and `‖φ‖₁² ≤ δ‖φ‖₂²`.  The exponentials are at most `√(2/δ)`, so
  `|2P| ≤ 2√2 e^{δ/2} N √δ ‖f‖²`.
* *Packing.*  `s`-separated centres in an interval of length `log(2/δ)` number at most
  `1 + log(2/δ)/s` (`card_le_one_add_div_of_separated`), so the pole loss is
  `O(√δ log(1/δ)) ‖f‖²` against a Lévy gain of order `log(1/δ) ‖f‖²`.

Reading: tests that are prime-blind by support geometry carry a logarithmic margin
`log(1/δ)`.  So any test violating prime-blind positivity must be blind by cancellation at the
nodes, with bumps wide relative to the local node spacing.
-/

open Complex MeasureTheory Set Filter Topology
open scoped ComplexConjugate FourierTransform
open Zeta23

noncomputable section

namespace RHTower.SeparatedBump

open WeilLevyPole

variable {N : ℕ}

/-- The bump configuration `f(u) = Σ_j a_j φ(u − x_j)`. -/
def bumpSum (φ : ℝ → ℝ) (a x : Fin N → ℝ) (u : ℝ) : ℝ := ∑ j, a j * φ (u - x j)

/-! ## Support bookkeeping -/

theorem abs_le_of_ne_zero {φ : ℝ → ℝ} {δ : ℝ} (hφs : ∀ u, δ / 2 < |u| → φ u = 0) {u : ℝ}
    (hu : φ u ≠ 0) : |u| ≤ δ / 2 := by
  by_contra h
  exact hu (hφs u (not_le.mp h))

/-- Two translates whose centres are more than `δ` apart have disjoint supports. -/
theorem mul_translate_eq_zero {φ : ℝ → ℝ} {δ : ℝ} (hφs : ∀ u, δ / 2 < |u| → φ u = 0) {p q : ℝ}
    (hpq : δ < |p - q|) (u : ℝ) : φ (u - p) * φ (u - q) = 0 := by
  by_contra h
  rcases mul_ne_zero_iff.mp h with ⟨h1, h2⟩
  have e1 := abs_le_of_ne_zero hφs h1
  have e2 := abs_le_of_ne_zero hφs h2
  have : |p - q| ≤ δ := by
    calc |p - q| = |(u - q) - (u - p)| := by ring_nf
      _ ≤ |u - q| + |u - p| := abs_sub _ _
      _ ≤ δ := by linarith
  linarith

/-- A function vanishing outside `[−R, R]` has compact support. -/
theorem hasCompactSupport_of_abs_gt {g : ℝ → ℝ} {R : ℝ} (hg : ∀ u, R < |u| → g u = 0) :
    HasCompactSupport g :=
  HasCompactSupport.intro (isCompact_Icc (a := -R) (b := R)) fun u hu =>
    hg u (not_le.mp fun h => hu (mem_Icc.mpr (abs_le.mp h)))

theorem hasCompactSupport_of_abs {φ : ℝ → ℝ} {δ : ℝ} (hφs : ∀ u, δ / 2 < |u| → φ u = 0) :
    HasCompactSupport φ :=
  hasCompactSupport_of_abs_gt hφs

/-- A translate `φ(· − c)` vanishes outside `[−(|c| + δ/2), |c| + δ/2]`. -/
theorem translate_eq_zero {φ : ℝ → ℝ} {δ : ℝ} (hφs : ∀ u, δ / 2 < |u| → φ u = 0) (c : ℝ) {u : ℝ}
    (hu : |c| + δ / 2 < |u|) : φ (u - c) = 0 := by
  refine hφs _ ?_
  have := abs_sub_abs_le_abs_sub u c
  linarith

theorem contDiff_bumpSum {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ) (a x : Fin N → ℝ) :
    ContDiff ℝ 2 (bumpSum φ a x) := by
  have e : bumpSum φ a x = fun u => ∑ j ∈ Finset.univ, a j * φ (u - x j) := rfl
  rw [e]
  refine ContDiff.sum fun j _ => ?_
  have h1 : ContDiff ℝ 2 fun u : ℝ => u - x j := contDiff_id.sub contDiff_const
  exact contDiff_const.mul (hφ.comp h1)

/-- The configuration vanishes outside `[−R, R]`, `R = Σ_j |x_j| + δ/2`. -/
theorem bumpSum_eq_zero {φ : ℝ → ℝ} {δ : ℝ} (hφs : ∀ u, δ / 2 < |u| → φ u = 0)
    (a x : Fin N → ℝ) {u : ℝ} (hu : (∑ j, |x j|) + δ / 2 < |u|) : bumpSum φ a x u = 0 := by
  unfold bumpSum
  refine Finset.sum_eq_zero fun j _ => ?_
  have hj : |x j| ≤ ∑ i, |x i| :=
    Finset.single_le_sum (f := fun i => |x i|) (fun i _ => abs_nonneg _) (Finset.mem_univ j)
  rw [translate_eq_zero hφs (x j) (by linarith), mul_zero]

theorem hasCompactSupport_bumpSum {φ : ℝ → ℝ} {δ : ℝ} (hφs : ∀ u, δ / 2 < |u| → φ u = 0)
    (a x : Fin N → ℝ) : HasCompactSupport (bumpSum φ a x) :=
  hasCompactSupport_of_abs_gt fun _ hu => bumpSum_eq_zero hφs a x hu

/-! ## The square and its translates -/

/-- Pointwise, the square of a separated configuration has no cross terms. -/
theorem bumpSum_sq {φ : ℝ → ℝ} {δ s : ℝ} (hφs : ∀ u, δ / 2 < |u| → φ u = 0) (hδs : δ < s)
    {a x : Fin N → ℝ} (hsep : ∀ i j, i ≠ j → s ≤ |x i - x j|) (u : ℝ) :
    bumpSum φ a x u ^ 2 = ∑ j, a j ^ 2 * φ (u - x j) ^ 2 := by
  unfold bumpSum
  rw [sq, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i]
  · ring
  · intro j _ hji
    have := mul_translate_eq_zero hφs (p := x i) (q := x j) (lt_of_lt_of_le hδs (hsep i j
      (Ne.symm hji))) u
    calc a i * φ (u - x i) * (a j * φ (u - x j)) = a i * a j * (φ (u - x i) * φ (u - x j)) := by
          ring
      _ = 0 := by rw [this, mul_zero]
  · intro h; exact absurd (Finset.mem_univ i) h

theorem integral_bumpSum_sq {φ : ℝ → ℝ} {δ s : ℝ} (hφ : ContDiff ℝ 2 φ)
    (hφs : ∀ u, δ / 2 < |u| → φ u = 0) (hδs : δ < s) {a x : Fin N → ℝ}
    (hsep : ∀ i j, i ≠ j → s ≤ |x i - x j|) :
    ∫ u, bumpSum φ a x u ^ 2 = (∑ j, a j ^ 2) * ∫ u, φ u ^ 2 := by
  have hint : ∀ j : Fin N, Integrable fun u => a j ^ 2 * φ (u - x j) ^ 2 := fun j => by
    have h1 : Continuous fun u => a j ^ 2 * φ (u - x j) ^ 2 := by
      have := hφ.continuous; fun_prop
    refine h1.integrable_of_hasCompactSupport
      (hasCompactSupport_of_abs_gt (R := |x j| + δ / 2) fun u hu => ?_)
    rw [translate_eq_zero hφs (x j) hu]
    ring
  simp_rw [bumpSum_sq (a := a) hφs hδs hsep]
  rw [integral_finsetSum _ fun j _ => hint j, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_const_mul]
  congr 1
  exact integral_sub_right_eq_self (fun u => φ u ^ 2) (x j)

/-- In the Lévy window `δ < t < s − δ` a configuration never meets its own translate. -/
theorem bumpSum_mul_bumpSum_add_eq_zero {φ : ℝ → ℝ} {δ s t : ℝ}
    (hφs : ∀ u, δ / 2 < |u| → φ u = 0) (hδ : 0 < δ) {a x : Fin N → ℝ}
    (hsep : ∀ i j, i ≠ j → s ≤ |x i - x j|) (ht1 : δ < t) (ht2 : t < s - δ) (u : ℝ) :
    bumpSum φ a x u * bumpSum φ a x (u + t) = 0 := by
  unfold bumpSum
  rw [Finset.sum_mul_sum]
  refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
  have hsub : u + t - x j = u - (x j - t) := by ring
  rw [hsub]
  have hfar : δ < |x i - (x j - t)| := by
    by_cases hij : i = j
    · subst hij
      rw [show x i - (x i - t) = t by ring, abs_of_pos (by linarith)]
      exact ht1
    · have h := hsep i j hij
      have h2 : |x i - x j| - t ≤ |x i - (x j - t)| := by
        have := abs_sub_abs_le_abs_sub (x i - x j) (-t)
        rw [abs_neg, abs_of_pos (by linarith : (0 : ℝ) < t)] at this
        calc |x i - x j| - t ≤ |x i - x j - -t| := this
          _ = |x i - (x j - t)| := by ring_nf
      linarith
  have := mul_translate_eq_zero hφs hfar u
  calc a i * φ (u - x i) * (a j * φ (u - (x j - t)))
      = a i * a j * (φ (u - x i) * φ (u - (x j - t))) := by ring
    _ = 0 := by rw [this, mul_zero]

theorem integral_sub_translate_sq {φ : ℝ → ℝ} {δ s t : ℝ} (hφ : ContDiff ℝ 2 φ)
    (hφs : ∀ u, δ / 2 < |u| → φ u = 0) (hδ : 0 < δ) {a x : Fin N → ℝ}
    (hsep : ∀ i j, i ≠ j → s ≤ |x i - x j|) (ht1 : δ < t) (ht2 : t < s - δ) :
    ∫ u, (bumpSum φ a x u - bumpSum φ a x (u + t)) ^ 2 = 2 * ∫ u, bumpSum φ a x u ^ 2 := by
  have hf := (contDiff_bumpSum hφ a x).continuous
  set R : ℝ := (∑ j, |x j|) + δ / 2 with hR
  have hi1 : Integrable fun u => bumpSum φ a x u ^ 2 := by
    refine (hf.pow 2).integrable_of_hasCompactSupport
      (hasCompactSupport_of_abs_gt (R := R) fun u hu => ?_)
    show bumpSum φ a x u ^ 2 = 0
    rw [bumpSum_eq_zero hφs a x hu]
    ring
  have hi2 : Integrable fun u => bumpSum φ a x (u + t) ^ 2 := by
    refine ((hf.comp (continuous_id.add continuous_const)).pow 2).integrable_of_hasCompactSupport
      (hasCompactSupport_of_abs_gt (R := R + |t|) fun u hu => ?_)
    have h : R < |u + t| := by
      have := abs_sub_abs_le_abs_sub u (-t)
      rw [abs_neg, sub_neg_eq_add] at this
      linarith
    show bumpSum φ a x (u + t) ^ 2 = 0
    rw [bumpSum_eq_zero hφs a x h]
    ring
  have hpt : ∀ u, (bumpSum φ a x u - bumpSum φ a x (u + t)) ^ 2 =
      bumpSum φ a x u ^ 2 + bumpSum φ a x (u + t) ^ 2 := fun u => by
    have h0 := bumpSum_mul_bumpSum_add_eq_zero (a := a) hφs hδ hsep ht1 ht2 u
    have e : (bumpSum φ a x u - bumpSum φ a x (u + t)) ^ 2 =
        bumpSum φ a x u ^ 2 + bumpSum φ a x (u + t) ^ 2 -
          2 * (bumpSum φ a x u * bumpSum φ a x (u + t)) := by ring
    rw [e, h0]
    ring
  simp_rw [hpt]
  rw [integral_add hi1 hi2, integral_add_right_eq_self (fun u => bumpSum φ a x u ^ 2) t]
  ring

/-! ## The Lévy energy -/

theorem archLevyDensity_ge {x : ℝ} (hx : 0 < x) :
    Real.exp (-x / 2) / (2 * x) ≤ archLevyDensity x := by
  unfold archLevyDensity
  have h1 : 1 - Real.exp (-2 * x) ≤ 2 * x := by
    have := Real.add_one_le_exp (-2 * x); linarith
  have h2 : 0 < 1 - Real.exp (-2 * x) := by
    have : Real.exp (-2 * x) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    linarith
  exact div_le_div_of_nonneg_left (Real.exp_pos _).le h2 h1

theorem continuousOn_archLevyDensity : ContinuousOn archLevyDensity (Ioi 0) := by
  intro x hx
  have hx : 0 < x := hx
  have h2 : 1 - Real.exp (-2 * x) ≠ 0 := by
    have : Real.exp (-2 * x) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    linarith
  have hc : ContinuousAt (fun x : ℝ => Real.exp (-x / 2) / (1 - Real.exp (-2 * x))) x :=
    ContinuousAt.div (f := fun x : ℝ => Real.exp (-x / 2))
      (g := fun x : ℝ => 1 - Real.exp (-2 * x)) (by fun_prop) (by fun_prop) h2
  exact hc.continuousWithinAt

/-- `∫_δ^{s−δ} ω ≥ ½ e^{−s/2} log((s − δ)/δ)`. -/
theorem integral_archLevyDensity_ge {δ s : ℝ} (hδ : 0 < δ) (hδs : 2 * δ < s) :
    Real.exp (-s / 2) / 2 * Real.log ((s - δ) / δ) ≤ ∫ x in δ..(s - δ), archLevyDensity x := by
  have hle : δ ≤ s - δ := by linarith
  have hint1 : IntervalIntegrable (fun x : ℝ => Real.exp (-s / 2) / 2 * x⁻¹) volume δ (s - δ) := by
    refine (continuousOn_const.mul (continuousOn_inv₀.mono fun x hx => ?_)).intervalIntegrable
    rw [uIcc_of_le hle] at hx
    exact (by linarith [hx.1] : x ≠ 0)
  have hint2 : IntervalIntegrable archLevyDensity volume δ (s - δ) := by
    refine (continuousOn_archLevyDensity.mono fun x hx => ?_).intervalIntegrable
    rw [uIcc_of_le hle] at hx
    exact (lt_of_lt_of_le hδ hx.1 : 0 < x)
  have hmono := intervalIntegral.integral_mono_on hle hint1 hint2 fun x hx => by
    have hx0 : 0 < x := lt_of_lt_of_le hδ hx.1
    have hxs : x ≤ s := by linarith [hx.2]
    have h1 := archLevyDensity_ge hx0
    have h2 : Real.exp (-s / 2) ≤ Real.exp (-x / 2) := Real.exp_le_exp.mpr (by linarith)
    have h3 : Real.exp (-s / 2) / 2 * x⁻¹ ≤ Real.exp (-x / 2) / (2 * x) := by
      rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
      have : x⁻¹ * x = 1 := inv_mul_cancel₀ hx0.ne'
      nlinarith [Real.exp_pos (-s / 2)]
    linarith
  rw [intervalIntegral.integral_const_mul, integral_inv_of_pos hδ (by linarith)] at hmono
  exact hmono

/-! ## Finiteness of the Lévy energy -/

theorem lintegral_levy_ne_top {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    (∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal (archLevyDensity x * ∫ u, (f u - f (u + x)) ^ 2)) ≠
      ⊤ := by
  set F : ℝ → ℂ := fun u => (f u : ℂ) with hFdef
  have hFc : Continuous F := Complex.continuous_ofReal.comp hf.continuous
  have hFcs : HasCompactSupport F := hfc.comp_left Complex.ofReal_zero
  have hF2 : ContDiff ℝ 2 F := Complex.ofRealCLM.contDiff.comp hf
  have hF1 : Integrable F := hFc.integrable_of_hasCompactSupport hFcs
  have hFL2 : MemLp F 2 := hFc.memLp_of_hasCompactSupport hFcs
  have hk : ∀ z : ℂ, paperFT (EF.weilTest F F) z = paperFT F z * conj (paperFT F (conj z)) :=
    EF.paperFT_weilTest hFc hFc hFcs hFcs
  have hreal : ∀ r : ℝ, paperFT (EF.weilTest F F) r * (EF.gammaBracket r : ℂ) =
      ((‖paperFT F r‖ ^ 2 * EF.gammaBracket r : ℝ) : ℂ) := fun r => by
    rw [hk, Complex.conj_ofReal, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast
    ring
  have hintC := LebesgueAtomWeil.integrable_paperFT_weilTest_mul_gammaBracket hF2 hFcs hF2 hFcs
  have hintR : Integrable fun r : ℝ => ‖paperFT F r‖ ^ 2 * EF.gammaBracket r := by
    refine hintC.re.congr (Eventually.of_forall fun r => ?_)
    show (paperFT (EF.weilTest F F) r * (EF.gammaBracket r : ℂ)).re = _
    rw [hreal, Complex.ofReal_re]
  have hint : Integrable fun ξ : ℝ => gammaHardyPhaseRate (2 * Real.pi * ξ) * ‖𝓕 F ξ‖ ^ 2 := by
    have h := (hintR.comp_mul_left' (R := -(2 * Real.pi)) (by
      have := Real.pi_pos; intro h; linarith)).div_const 2
    refine h.congr (Eventually.of_forall fun ξ => ?_)
    simp only
    rw [fourier_eq_paperFT_neg_two_pi_mul, gammaBracket_eq_two_mul_gammaHardyPhaseRate,
      show -(2 * Real.pi) * ξ = -(2 * Real.pi * ξ) by ring, gammaHardyPhaseRate_neg]
    ring
  have h := lintegral_archLevyDirichlet_ne_top hF1 hFL2 hint
  have hlev : (∫⁻ x in Ioi (0 : ℝ),
      ENNReal.ofReal (archLevyDensity x * ∫ u : ℝ, ‖F u - F (u + x)‖ ^ 2)) =
      ∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal (archLevyDensity x * ∫ u : ℝ, (f u - f (u + x)) ^ 2) := by
    refine lintegral_congr fun x => ?_
    congr 3
    funext u
    simp only [hFdef]
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  rwa [hlev] at h

/-- **Lévy energy of a separated configuration.**  The Lévy term is at least
`2‖f‖² ∫_δ^{s−δ} ω`. -/
theorem levy_ge {φ : ℝ → ℝ} {δ s : ℝ} (hφ : ContDiff ℝ 2 φ)
    (hφs : ∀ u, δ / 2 < |u| → φ u = 0) (hδ : 0 < δ) (hδs : 2 * δ < s) {a x : Fin N → ℝ}
    (hsep : ∀ i j, i ≠ j → s ≤ |x i - x j|) :
    2 * (∫ u, bumpSum φ a x u ^ 2) * ∫ t in δ..(s - δ), archLevyDensity t ≤
      (∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (archLevyDensity t *
        ∫ u, (bumpSum φ a x u - bumpSum φ a x (u + t)) ^ 2)).toReal := by
  set f := bumpSum φ a x with hfdef
  have hle : δ ≤ s - δ := by linarith
  have hfin := lintegral_levy_ne_top (contDiff_bumpSum hφ a x) (hasCompactSupport_bumpSum hφs a x)
  have hE : 0 ≤ ∫ u, f u ^ 2 := integral_nonneg fun u => sq_nonneg _
  have hcont : ContinuousOn archLevyDensity (Icc δ (s - δ)) :=
    continuousOn_archLevyDensity.mono fun t ht => (lt_of_lt_of_le hδ ht.1 : 0 < t)
  have hintIoo : IntegrableOn (fun t => 2 * (∫ u, f u ^ 2) * archLevyDensity t) (Ioo δ (s - δ)) :=
    ((hcont.integrableOn_Icc).mono_set Ioo_subset_Icc_self).const_mul _
  have hnn : ∀ t ∈ Ioo δ (s - δ), 0 ≤ 2 * (∫ u, f u ^ 2) * archLevyDensity t := fun t ht =>
    mul_nonneg (by positivity) (archLevyDensity_pos (lt_trans hδ ht.1)).le
  -- the restriction to the Lévy window
  have hrestr : ENNReal.ofReal (∫ t in Ioo δ (s - δ), 2 * (∫ u, f u ^ 2) * archLevyDensity t) ≤
      ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (archLevyDensity t * ∫ u, (f u - f (u + t)) ^ 2) := by
    rw [ofReal_integral_eq_lintegral_ofReal hintIoo
      ((ae_restrict_iff' measurableSet_Ioo).mpr (Eventually.of_forall hnn))]
    calc ∫⁻ t in Ioo δ (s - δ), ENNReal.ofReal (2 * (∫ u, f u ^ 2) * archLevyDensity t)
        = ∫⁻ t in Ioo δ (s - δ), ENNReal.ofReal (archLevyDensity t *
            ∫ u, (f u - f (u + t)) ^ 2) := by
          refine setLIntegral_congr_fun measurableSet_Ioo fun t ht => ?_
          rw [hfdef, integral_sub_translate_sq (a := a) hφ hφs hδ hsep ht.1 ht.2]
          ring_nf
      _ ≤ ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (archLevyDensity t *
            ∫ u, (f u - f (u + t)) ^ 2) :=
          lintegral_mono_set fun t ht => (lt_trans hδ ht.1 : 0 < t)
  have hval : (∫ t in Ioo δ (s - δ), 2 * (∫ u, f u ^ 2) * archLevyDensity t) =
      2 * (∫ u, f u ^ 2) * ∫ t in δ..(s - δ), archLevyDensity t := by
    rw [integral_const_mul, intervalIntegral.integral_of_le hle, integral_Ioc_eq_integral_Ioo]
  have h := ENNReal.toReal_mono hfin hrestr
  rwa [ENNReal.toReal_ofReal (setIntegral_nonneg measurableSet_Ioo hnn), hval] at h

/-! ## Geometry of support blindness -/

/-- Every `d ≥ log(2/δ)` lies within `δ` of `log n` for some `n ≥ 2`. -/
theorem exists_log_near {δ d : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) (hd : Real.log (2 / δ) ≤ d) :
    ∃ n : ℕ, 2 ≤ n ∧ |d - Real.log n| < δ := by
  set y := Real.exp d with hy
  have hy0 : 0 < y := Real.exp_pos d
  have hy2 : 2 / δ ≤ y := by
    rw [hy]
    calc 2 / δ = Real.exp (Real.log (2 / δ)) := (Real.exp_log (by positivity)).symm
      _ ≤ Real.exp d := Real.exp_le_exp.mpr hd
  have hδy : 2 ≤ y * δ := by rwa [div_le_iff₀ hδ] at hy2
  have hy2' : 2 < y := by nlinarith
  set n := ⌊y⌋₊ with hn
  have hnle : (n : ℝ) ≤ y := Nat.floor_le hy0.le
  have hnlt : y < n + 1 := Nat.lt_floor_add_one y
  have hn2 : 2 ≤ n := Nat.le_floor (by push_cast; linarith)
  have hn2' : (2 : ℝ) ≤ n := by exact_mod_cast hn2
  have hnpos : (0 : ℝ) < n := by linarith
  refine ⟨n, hn2, ?_⟩
  have hlog1 : Real.log n ≤ d := by
    rw [← Real.log_exp d]
    exact Real.log_le_log hnpos hnle
  have h1 : d - Real.log n = Real.log (y / n) := by
    rw [Real.log_div hy0.ne' hnpos.ne', hy, Real.log_exp]
  have h2 : Real.log (y / n) ≤ y / n - 1 := Real.log_le_sub_one_of_pos (by positivity)
  have h3 : y / n - 1 < 1 / n := by
    rw [div_sub_one hnpos.ne', div_lt_div_iff_of_pos_right hnpos]
    linarith
  have h4 : 1 / (n : ℝ) ≤ 2 / y := by
    rw [div_le_div_iff₀ hnpos hy0]
    linarith
  have h5 : 2 / y ≤ δ := by
    rw [div_le_iff₀ hy0]
    linarith
  rw [abs_of_nonneg (by linarith)]
  linarith

/-- **Blindness by support bounds the span.**  If every difference stays more than `δ` away from
every `log n`, then all differences are below `log(2/δ)`. -/
theorem abs_sub_lt_log_of_geometry {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) {x : Fin N → ℝ}
    (hgeom : ∀ i j, i ≠ j → ∀ n : ℕ, 2 ≤ n → δ < |x i - x j - Real.log n|) {i j : Fin N}
    (hij : i ≠ j) : |x i - x j| < Real.log (2 / δ) := by
  by_contra hcon
  rw [not_lt] at hcon
  rcases le_total 0 (x i - x j) with h | h
  · rw [abs_of_nonneg h] at hcon
    obtain ⟨n, hn, hclose⟩ := exists_log_near hδ hδ1 hcon
    exact absurd (hgeom i j hij n hn) (not_lt.mpr hclose.le)
  · rw [abs_of_nonpos h] at hcon
    obtain ⟨n, hn, hclose⟩ := exists_log_near (d := x j - x i) hδ hδ1 (by linarith)
    exact absurd (hgeom j i (Ne.symm hij) n hn) (not_lt.mpr hclose.le)

/-- Support blindness bounds every difference, the diagonal included. -/
theorem abs_sub_lt_log_of_geometry' {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) {x : Fin N → ℝ}
    (hgeom : ∀ i j, i ≠ j → ∀ n : ℕ, 2 ≤ n → δ < |x i - x j - Real.log n|) (i j : Fin N) :
    |x i - x j| < Real.log (2 / δ) := by
  by_cases hij : i = j
  · subst hij
    rw [sub_self, abs_zero]
    exact Real.log_pos (by rw [lt_div_iff₀ hδ]; linarith)
  · exact abs_sub_lt_log_of_geometry hδ hδ1 hgeom hij

/-! ## The pole term -/

theorem integral_translate_mul_exp {φ : ℝ → ℝ} (c κ : ℝ) :
    ∫ u, φ (u - c) * Real.exp (κ * u) = Real.exp (κ * c) * ∫ v, φ v * Real.exp (κ * v) := by
  have h := integral_sub_right_eq_self (μ := volume) (fun v => φ v * Real.exp (κ * (v + c))) c
  simp only [sub_add_cancel] at h
  rw [h, ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun v => ?_)
  simp only
  rw [mul_add, Real.exp_add]
  ring

theorem integral_bumpSum_mul_exp {φ : ℝ → ℝ} {δ : ℝ} (hφ : ContDiff ℝ 2 φ)
    (hφs : ∀ u, δ / 2 < |u| → φ u = 0) (a x : Fin N → ℝ) (κ : ℝ) :
    ∫ u, bumpSum φ a x u * Real.exp (κ * u) =
      (∑ j, a j * Real.exp (κ * x j)) * ∫ v, φ v * Real.exp (κ * v) := by
  have hint : ∀ j : Fin N, Integrable fun u => a j * φ (u - x j) * Real.exp (κ * u) := fun j => by
    have h1 : Continuous fun u => a j * φ (u - x j) * Real.exp (κ * u) := by
      have := hφ.continuous; fun_prop
    refine h1.integrable_of_hasCompactSupport
      (hasCompactSupport_of_abs_gt (R := |x j| + δ / 2) fun u hu => ?_)
    show a j * φ (u - x j) * Real.exp (κ * u) = 0
    rw [translate_eq_zero hφs (x j) hu]
    ring
  unfold bumpSum
  simp_rw [Finset.sum_mul]
  rw [integral_finsetSum _ fun j _ => hint j]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [show (fun u => a j * φ (u - x j) * Real.exp (κ * u)) =
      fun u => a j * (φ (u - x j) * Real.exp (κ * u)) by funext u; ring,
    integral_const_mul, integral_translate_mul_exp]
  ring

theorem abs_integral_mul_exp_le {φ : ℝ → ℝ} {δ : ℝ} (hφ : ContDiff ℝ 2 φ)
    (hφs : ∀ u, δ / 2 < |u| → φ u = 0) {κ : ℝ} (hκ : |κ| ≤ 1 / 2) :
    |∫ v, φ v * Real.exp (κ * v)| ≤ Real.exp (δ / 4) * ∫ v, |φ v| := by
  have hφc := hasCompactSupport_of_abs hφs
  have hi : Integrable fun v => |φ v| :=
    (hφ.continuous.abs).integrable_of_hasCompactSupport hφc.abs
  rw [← integral_const_mul]
  refine (abs_integral_le_integral_abs).trans (integral_mono_of_nonneg
    (Eventually.of_forall fun v => abs_nonneg _) (hi.const_mul _)
    (Eventually.of_forall fun v => ?_))
  simp only
  by_cases hv : φ v = 0
  · simp [hv]
  · have hvl := abs_le_of_ne_zero hφs hv
    rw [abs_mul, abs_of_pos (Real.exp_pos _), mul_comm]
    refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ?_) (abs_nonneg _)
    calc κ * v ≤ |κ * v| := le_abs_self _
      _ = |κ| * |v| := abs_mul _ _
      _ ≤ 1 / 2 * (δ / 2) := mul_le_mul hκ hvl (abs_nonneg _) (by norm_num)
      _ = δ / 4 := by ring

/-- `‖φ‖₁² ≤ δ ‖φ‖₂²` for `φ` supported in `[−δ/2, δ/2]`. -/
theorem sq_integral_abs_le {φ : ℝ → ℝ} {δ : ℝ} (hφ : ContDiff ℝ 2 φ)
    (hφs : ∀ u, δ / 2 < |u| → φ u = 0) (hδ : 0 < δ) :
    (∫ v, |φ v|) ^ 2 ≤ δ * ∫ v, φ v ^ 2 := by
  have hout : ∀ v ∉ Icc (-(δ / 2)) (δ / 2), φ v = 0 := fun v hv =>
    hφs v (not_le.mp fun h => hv (mem_Icc.mpr (abs_le.mp h)))
  have e1 : ∫ v, |φ v| = ∫ v in (-(δ / 2))..(δ / 2), |φ v| := by
    rw [intervalIntegral.integral_of_le (by linarith), ← integral_Icc_eq_integral_Ioc,
      setIntegral_eq_integral_of_forall_compl_eq_zero fun v hv => by rw [hout v hv, abs_zero]]
  have e2 : ∫ v, φ v ^ 2 = ∫ v in (-(δ / 2))..(δ / 2), |φ v| ^ 2 := by
    rw [intervalIntegral.integral_of_le (by linarith), ← integral_Icc_eq_integral_Ioc,
      setIntegral_eq_integral_of_forall_compl_eq_zero fun v hv => by rw [hout v hv]; simp]
    exact integral_congr_ae (Eventually.of_forall fun v => (sq_abs _).symm)
  rw [e1, e2]
  have h := GaloisForLFunctions.HTGeometry.sq_integral_le_mul_integral_sq
    (g := fun v => |φ v|) (a := -(δ / 2)) (b := δ / 2) (by linarith)
    hφ.continuous.abs.continuousOn
  rwa [show δ / 2 - -(δ / 2) = δ by ring] at h

/-- **The pole term of a separated configuration.**  If every `e^{(x_i − x_j)/2}` is at most `B`,
the pole term is at most `2 e^{δ/2} B δ N ‖f‖²`. -/
theorem abs_pole_le_of_exp_le {φ : ℝ → ℝ} {δ s : ℝ} (hφ : ContDiff ℝ 2 φ)
    (hφs : ∀ u, δ / 2 < |u| → φ u = 0) (hδ : 0 < δ) (hδs : δ < s)
    {a x : Fin N → ℝ} (hsep : ∀ i j, i ≠ j → s ≤ |x i - x j|) {B : ℝ} (hB0 : 0 ≤ B)
    (hexp : ∀ i j : Fin N, Real.exp (1 / 2 * x i) * Real.exp (-1 / 2 * x j) ≤ B) :
    |2 * ∫ p : ℝ × ℝ, bumpSum φ a x p.1 * bumpSum φ a x p.2 * Real.cosh ((p.1 - p.2) / 2)| ≤
      2 * Real.exp (δ / 2) * (B * δ) * N * ∫ u, bumpSum φ a x u ^ 2 := by
  set f := bumpSum φ a x with hfdef
  have hfc := hasCompactSupport_bumpSum hφs a x
  have hf := (contDiff_bumpSum hφ a x).continuous
  rw [integral_prod_cosh_eq hfc hf]
  have hp := integral_bumpSum_mul_exp hφ hφs a x (1 / 2)
  have hm := integral_bumpSum_mul_exp hφ hφs a x (-1 / 2)
  have e1 : (∫ u, f u * Real.exp (u / 2)) = ∫ u, f u * Real.exp (1 / 2 * u) := by
    congr 1; funext u; ring_nf
  have e2 : (∫ u, f u * Real.exp (-u / 2)) = ∫ u, f u * Real.exp (-1 / 2 * u) := by
    congr 1; funext u; ring_nf
  rw [e1, e2, hp, hm]
  set cp := ∫ v, φ v * Real.exp (1 / 2 * v) with hcp
  set cm := ∫ v, φ v * Real.exp (-1 / 2 * v) with hcm
  set L := ∫ v, |φ v| with hL
  have hcp' : |cp| ≤ Real.exp (δ / 4) * L := abs_integral_mul_exp_le hφ hφs (by norm_num)
  have hcm' : |cm| ≤ Real.exp (δ / 4) * L := abs_integral_mul_exp_le hφ hφs (by norm_num)
  have hL0 : 0 ≤ L := integral_nonneg fun v => abs_nonneg _
  have hS : |(∑ j, a j * Real.exp (1 / 2 * x j)) * ∑ j, a j * Real.exp (-1 / 2 * x j)| ≤
      B * (∑ j, |a j|) ^ 2 := by
    rw [Finset.sum_mul_sum, sq, Finset.sum_mul_sum, Finset.mul_sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [Finset.mul_sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [show a i * Real.exp (1 / 2 * x i) * (a j * Real.exp (-1 / 2 * x j)) =
        a i * a j * (Real.exp (1 / 2 * x i) * Real.exp (-1 / 2 * x j)) by ring, abs_mul,
      abs_mul, abs_of_pos (by positivity : 0 < Real.exp (1 / 2 * x i) * Real.exp (-1 / 2 * x j))]
    have := hexp i j
    calc |a i| * |a j| * (Real.exp (1 / 2 * x i) * Real.exp (-1 / 2 * x j))
        ≤ |a i| * |a j| * B :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = B * (|a i| * |a j|) := by ring
  have hCS : (∑ j, |a j|) ^ 2 ≤ N * ∑ j, a j ^ 2 := by
    have := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin N))) (f := fun j => |a j|)
    simpa [Finset.card_univ, Fintype.card_fin, sq_abs] using this
  have hL2 := sq_integral_abs_le hφ hφs hδ
  have hE : ∫ u, f u ^ 2 = (∑ j, a j ^ 2) * ∫ u, φ u ^ 2 :=
    integral_bumpSum_sq hφ hφs hδs hsep
  have hA0 : 0 ≤ ∑ j, a j ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg _
  have hφ0 : 0 ≤ ∫ u, φ u ^ 2 := integral_nonneg fun u => sq_nonneg _
  -- assemble
  have hexp2 : Real.exp (δ / 4) * Real.exp (δ / 4) = Real.exp (δ / 2) := by
    rw [← Real.exp_add]; ring_nf
  calc |2 * ((∑ j, a j * Real.exp (1 / 2 * x j)) * cp *
        ((∑ j, a j * Real.exp (-1 / 2 * x j)) * cm))|
      = 2 * (|cp| * |cm|) * |(∑ j, a j * Real.exp (1 / 2 * x j)) *
          ∑ j, a j * Real.exp (-1 / 2 * x j)| := by
        rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_mul, abs_two]; ring
    _ ≤ 2 * ((Real.exp (δ / 4) * L) * (Real.exp (δ / 4) * L)) *
          (B * (N * ∑ j, a j ^ 2)) := by
        gcongr
        exact hS.trans (mul_le_mul_of_nonneg_left hCS hB0)
    _ = 2 * Real.exp (δ / 2) * B * N * (∑ j, a j ^ 2) * L ^ 2 := by
        rw [← hexp2]; ring
    _ ≤ 2 * Real.exp (δ / 2) * B * N * (∑ j, a j ^ 2) *
          (δ * ∫ v, φ v ^ 2) := by gcongr
    _ = 2 * Real.exp (δ / 2) * (B * δ) * N * ((∑ j, a j ^ 2) *
          ∫ v, φ v ^ 2) := by ring
    _ = 2 * Real.exp (δ / 2) * (B * δ) * N * ∫ u, f u ^ 2 := by rw [hE]

/-- **The pole term of a configuration of span `< log(2/δ)` is `O(N √δ ‖f‖²)`.** -/
theorem abs_pole_le {φ : ℝ → ℝ} {δ s : ℝ} (hφ : ContDiff ℝ 2 φ)
    (hφs : ∀ u, δ / 2 < |u| → φ u = 0) (hδ : 0 < δ) (hδs : δ < s)
    {a x : Fin N → ℝ} (hsep : ∀ i j, i ≠ j → s ≤ |x i - x j|)
    (hspan : ∀ i j, |x i - x j| < Real.log (2 / δ)) :
    |2 * ∫ p : ℝ × ℝ, bumpSum φ a x p.1 * bumpSum φ a x p.2 * Real.cosh ((p.1 - p.2) / 2)| ≤
      2 * Real.exp (δ / 2) * Real.sqrt (2 * δ) * N * ∫ u, bumpSum φ a x u ^ 2 := by
  have hexp : ∀ i j : Fin N, Real.exp (1 / 2 * x i) * Real.exp (-1 / 2 * x j) ≤
      Real.sqrt (2 / δ) := by
    intro i j
    rw [← Real.exp_add]
    have h2 : 1 / 2 * x i + -1 / 2 * x j ≤ Real.log (2 / δ) / 2 := by
      have := le_abs_self (x i - x j)
      linarith [hspan i j]
    calc Real.exp (1 / 2 * x i + -1 / 2 * x j) ≤ Real.exp (Real.log (2 / δ) / 2) :=
          Real.exp_le_exp.mpr h2
      _ = Real.sqrt (2 / δ) := by
          rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos (by positivity)]
          ring_nf
  have hsqrt : Real.sqrt (2 / δ) * δ = Real.sqrt (2 * δ) := by
    rw [show 2 * δ = (2 / δ) * δ ^ 2 by field_simp, Real.sqrt_mul (by positivity),
      Real.sqrt_sq hδ.le]
  have h := abs_pole_le_of_exp_le (a := a) hφ hφs hδ hδs hsep (by positivity) hexp
  rwa [hsqrt] at h

/-! ## Positivity -/

/-- **Lévy gain against the pole.**  For an `s`-separated configuration of bumps of width `δ`,
`(A(0) + e^{−s/2} log((s − δ)/δ)) ‖f‖² − |2P| ≤ W_∞(f ⋆ f̃)`, whatever the geometry. -/
theorem levy_sub_abs_pole_le_weilArchRe {φ : ℝ → ℝ} {δ s : ℝ} (hφ : ContDiff ℝ 2 φ)
    (hφs : ∀ u, δ / 2 < |u| → φ u = 0) (hδ : 0 < δ) (hδs : 2 * δ < s)
    {a x : Fin N → ℝ} (hsep : ∀ i j, i ≠ j → s ≤ |x i - x j|) :
    (EF.gammaBracket 0 + Real.exp (-s / 2) * Real.log ((s - δ) / δ)) *
        (∫ u, bumpSum φ a x u ^ 2) -
      |2 * ∫ p : ℝ × ℝ, bumpSum φ a x p.1 * bumpSum φ a x p.2 * Real.cosh ((p.1 - p.2) / 2)| ≤
      WeilOneSided.weilArchRe (EF.weilTest (fun u => (bumpSum φ a x u : ℂ))
        (fun u => (bumpSum φ a x u : ℂ))) := by
  rw [weilArchRe_eq_levy_pole (contDiff_bumpSum hφ a x) (hasCompactSupport_bumpSum hφs a x)]
  have hlev := levy_ge (a := a) hφ hφs hδ hδs hsep
  have hint := integral_archLevyDensity_ge hδ hδs
  have hE : 0 ≤ ∫ u, bumpSum φ a x u ^ 2 := integral_nonneg fun u => sq_nonneg _
  have h1 : Real.exp (-s / 2) * Real.log ((s - δ) / δ) * ∫ u, bumpSum φ a x u ^ 2 ≤
      2 * (∫ u, bumpSum φ a x u ^ 2) * ∫ t in δ..(s - δ), archLevyDensity t := by
    have := mul_le_mul_of_nonneg_left hint (by positivity : (0 : ℝ) ≤ 2 * ∫ u, bumpSum φ a x u ^ 2)
    nlinarith
  have h2 := neg_abs_le (2 * ∫ p : ℝ × ℝ, bumpSum φ a x p.1 * bumpSum φ a x p.2 *
    Real.cosh ((p.1 - p.2) / 2))
  nlinarith

/-- **Quantitative positivity for separated narrow bumps of span `< log(2/δ)`.** -/
theorem le_weilArchRe_bumpSum {φ : ℝ → ℝ} {δ s : ℝ} (hφ : ContDiff ℝ 2 φ)
    (hφs : ∀ u, δ / 2 < |u| → φ u = 0) (hδ : 0 < δ) (hδs : 2 * δ < s)
    {a x : Fin N → ℝ} (hsep : ∀ i j, i ≠ j → s ≤ |x i - x j|)
    (hspan : ∀ i j, |x i - x j| < Real.log (2 / δ)) :
    (EF.gammaBracket 0 + Real.exp (-s / 2) * Real.log ((s - δ) / δ) -
        2 * Real.exp (δ / 2) * Real.sqrt (2 * δ) * N) * ∫ u, bumpSum φ a x u ^ 2 ≤
      WeilOneSided.weilArchRe (EF.weilTest (fun u => (bumpSum φ a x u : ℂ))
        (fun u => (bumpSum φ a x u : ℂ))) := by
  have h := levy_sub_abs_pole_le_weilArchRe (a := a) hφ hφs hδ hδs hsep
  have hpole := abs_pole_le (a := a) hφ hφs hδ (by linarith) hsep hspan
  nlinarith

/-- **Packing.**  A finite family of `s`-separated points whose mutual distances stay below `L`
has at most `1 + L/s` members. -/
theorem card_le_one_add_div_of_separated {ι : Type*} (T : Finset ι) (x : ι → ℝ) {s L : ℝ}
    (hs : 0 < s) (hL : 0 ≤ L) (hsep : ∀ i ∈ T, ∀ j ∈ T, i ≠ j → s ≤ |x i - x j|)
    (hdiam : ∀ i ∈ T, ∀ j ∈ T, i ≠ j → |x i - x j| < L) : (T.card : ℝ) ≤ 1 + L / s := by
  rcases T.eq_empty_or_nonempty with rfl | hT
  · simp only [Finset.card_empty, CharP.cast_eq_zero]
    positivity
  obtain ⟨i₀, hi₀T, hi₀⟩ := Finset.exists_min_image T x hT
  have hnn : ∀ i ∈ T, 0 ≤ (x i - x i₀) / s := fun i hi =>
    div_nonneg (sub_nonneg.mpr (hi₀ i hi)) hs.le
  have hmaps : Set.MapsTo (fun i => ⌊(x i - x i₀) / s⌋₊) T (Finset.range (⌊L / s⌋₊ + 1)) := by
    intro i hi
    simp only [Finset.coe_range, Set.mem_Iio, Nat.lt_succ_iff]
    refine Nat.floor_le_floor (div_le_div_of_nonneg_right ?_ hs.le)
    by_cases h : i = i₀
    · rw [h, sub_self]
      exact hL
    · have hlt := hdiam i hi i₀ hi₀T h
      rw [abs_of_nonneg (sub_nonneg.mpr (hi₀ i hi))] at hlt
      exact hlt.le
  have hinj : Set.InjOn (fun i => ⌊(x i - x i₀) / s⌋₊) T := by
    intro i hi j hj hij
    by_contra hne
    have a1 := Nat.lt_floor_add_one ((x i - x i₀) / s)
    have a2 := Nat.floor_le (hnn j hj)
    have a3 := Nat.lt_floor_add_one ((x j - x i₀) / s)
    have a4 := Nat.floor_le (hnn i hi)
    simp only at hij
    rw [hij] at a1 a4
    have h1 : (x i - x j) / s < 1 := by
      have : (x i - x i₀) / s - (x j - x i₀) / s < 1 := by linarith
      rwa [← sub_div, show x i - x i₀ - (x j - x i₀) = x i - x j by ring] at this
    have h2 : (x j - x i) / s < 1 := by
      have : (x j - x i₀) / s - (x i - x i₀) / s < 1 := by linarith
      rwa [← sub_div, show x j - x i₀ - (x i - x i₀) = x j - x i by ring] at this
    rw [div_lt_one hs] at h1 h2
    have := hsep i hi j hj hne
    have := abs_sub_lt_iff.mpr ⟨h1, h2⟩
    linarith
  have hcard := Finset.card_le_card_of_injOn _ hmaps hinj
  rw [Finset.card_range] at hcard
  have hfl := Nat.floor_le (div_nonneg hL hs.le)
  have : (T.card : ℝ) ≤ (⌊L / s⌋₊ : ℝ) + 1 := by exact_mod_cast hcard
  linarith

/-- **Packing** for an indexed configuration. -/
theorem natCast_le_one_add_div_of_separated {x : Fin N → ℝ} {s L : ℝ} (hs : 0 < s)
    (hL : 0 ≤ L) (hsep : ∀ i j, i ≠ j → s ≤ |x i - x j|)
    (hdiam : ∀ i j, i ≠ j → |x i - x j| < L) : (N : ℝ) ≤ 1 + L / s := by
  have h := card_le_one_add_div_of_separated Finset.univ x hs hL (fun i _ j _ => hsep i j)
    fun i _ j _ => hdiam i j
  rwa [Finset.card_univ, Fintype.card_fin] at h

/-- **Positivity for separated narrow bumps of span `< log(2/δ)`, uniformly in the number of
bumps.**  For every separation `s > 0` there is `δ₀ > 0` such that for all `0 < δ < δ₀` every
configuration of any number of bumps of width `δ`, `s`-separated and of span `< log(2/δ)`, has
nonnegative pole and archimedean energy.  There are at most `1 + log(2/δ)/s` centres, so the pole
loss is `O(√δ log(1/δ))`. -/
theorem exists_le_weilArchRe_bumpSum {s : ℝ} (hs : 0 < s) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ → ∀ (N : ℕ) (φ : ℝ → ℝ) (a x : Fin N → ℝ),
      ContDiff ℝ 2 φ → (∀ u, δ / 2 < |u| → φ u = 0) →
      (∀ i j, i ≠ j → s ≤ |x i - x j|) →
      (∀ i j, |x i - x j| < Real.log (2 / δ)) →
      0 ≤ WeilOneSided.weilArchRe (EF.weilTest (fun u => (bumpSum φ a x u : ℂ))
        (fun u => (bumpSum φ a x u : ℂ))) := by
  set C : ℝ := |EF.gammaBracket 0| + 1 with hC
  set e : ℝ := Real.exp (-s / 2) with he
  set ε : ℝ := min (1 / 4) (s * e / 8) with hε
  set M : ℝ := 2 * (C * Real.exp (s / 2) - Real.log (s / 4)) with hM
  set δ₀ : ℝ := min (min (1 / 2) (s / 4)) (min (ε ^ 2 / 2) (2 * Real.exp (-M))) with hδ₀
  have he0 : 0 < e := Real.exp_pos _
  have hε0 : 0 < ε := lt_min (by norm_num) (by positivity)
  have hδ₀pos : 0 < δ₀ := by positivity
  refine ⟨δ₀, hδ₀pos, fun δ hδ hδlt N φ a x hφ hφs hsep hspan => ?_⟩
  have hd1 : δ < 1 / 2 := lt_of_lt_of_le hδlt ((min_le_left _ _).trans (min_le_left _ _))
  have hd2 : δ < s / 4 := lt_of_lt_of_le hδlt ((min_le_left _ _).trans (min_le_right _ _))
  have hd3 : δ < ε ^ 2 / 2 := lt_of_lt_of_le hδlt ((min_le_right _ _).trans (min_le_left _ _))
  have hd4 : δ < 2 * Real.exp (-M) :=
    lt_of_lt_of_le hδlt ((min_le_right _ _).trans (min_le_right _ _))
  have key := le_weilArchRe_bumpSum (a := a) hφ hφs hδ (by linarith) hsep hspan
  refine le_trans ?_ key
  refine mul_nonneg ?_ (integral_nonneg fun u => sq_nonneg _)
  have h2δ : 1 ≤ 2 / δ := by rw [le_div_iff₀ hδ]; linarith
  set Lg : ℝ := Real.log (2 / δ) with hLg
  have hLg0 : 0 ≤ Lg := Real.log_nonneg h2δ
  -- packing
  have hN : (N : ℝ) ≤ 1 + Lg / s :=
    natCast_le_one_add_div_of_separated hs hLg0 hsep fun i j _ => hspan i j
  -- the logarithmic gain
  have hLgM : M ≤ Lg := by
    have h1 : Real.exp M ≤ 2 / δ := by
      rw [le_div_iff₀ hδ]
      have hm : Real.exp (-M) * Real.exp M = 1 := by
        rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
      have hpos := Real.exp_pos M
      nlinarith
    have := Real.log_le_log (Real.exp_pos _) h1
    rwa [Real.log_exp] at this
  have hsδ : 0 < s - δ := by linarith
  have hgain : Lg + Real.log (s / 4) ≤ Real.log ((s - δ) / δ) := by
    rw [hLg, ← Real.log_mul (by positivity) (by positivity)]
    refine Real.log_le_log (by positivity) ?_
    rw [show 2 / δ * (s / 4) = s / 2 / δ by ring]
    gcongr
    linarith
  -- the pole loss
  have hκ : 2 * Real.exp (δ / 2) * Real.sqrt (2 * δ) ≤ 4 * ε := by
    have hexp : Real.exp (δ / 2) ≤ 2 := by
      have hl2 : δ / 2 ≤ Real.log 2 := by have := Real.log_two_gt_d9; linarith
      calc Real.exp (δ / 2) ≤ Real.exp (Real.log 2) := Real.exp_le_exp.mpr hl2
        _ = 2 := Real.exp_log (by norm_num)
    have hsq : Real.sqrt (2 * δ) ≤ ε := by
      rw [show ε = Real.sqrt (ε ^ 2) from (Real.sqrt_sq hε0.le).symm]
      exact Real.sqrt_le_sqrt (by linarith)
    have h0 := Real.sqrt_nonneg (2 * δ)
    calc 2 * Real.exp (δ / 2) * Real.sqrt (2 * δ) ≤ 2 * 2 * ε := by gcongr
      _ = 4 * ε := by ring
  set κ : ℝ := 2 * Real.exp (δ / 2) * Real.sqrt (2 * δ) with hκdef
  have hκ0 : 0 ≤ κ := by positivity
  have hε1 : ε ≤ 1 / 4 := min_le_left _ _
  have hε2 : ε ≤ s * e / 8 := min_le_right _ _
  have hloss : κ * N ≤ 1 + e / 2 * Lg := by
    have h1 : κ * N ≤ κ * (1 + Lg / s) := mul_le_mul_of_nonneg_left hN hκ0
    have h2 : κ * (Lg / s) ≤ e / 2 * Lg := by
      rw [mul_div_assoc', div_le_iff₀ hs]
      have hκs : κ ≤ s * e / 2 := by linarith
      calc κ * Lg ≤ s * e / 2 * Lg := mul_le_mul_of_nonneg_right hκs hLg0
        _ = e / 2 * Lg * s := by ring
    have h3 : κ * (1 + Lg / s) = κ + κ * (Lg / s) := by ring
    linarith
  have hE : e * Real.exp (s / 2) = 1 := by
    rw [he, ← Real.exp_add, show -s / 2 + s / 2 = 0 by ring, Real.exp_zero]
  have h3 : C ≤ e * Lg / 2 + e * Real.log (s / 4) := by
    have hle : C * Real.exp (s / 2) ≤ Lg / 2 + Real.log (s / 4) := by linarith
    calc C = e * (C * Real.exp (s / 2)) := by rw [mul_left_comm, hE, mul_one]
      _ ≤ e * (Lg / 2 + Real.log (s / 4)) := mul_le_mul_of_nonneg_left hle he0.le
      _ = e * Lg / 2 + e * Real.log (s / 4) := by ring
  have h4 : e * Lg + e * Real.log (s / 4) ≤ e * Real.log ((s - δ) / δ) := by
    rw [← mul_add]
    exact mul_le_mul_of_nonneg_left hgain he0.le
  have hg := neg_abs_le (EF.gammaBracket 0)
  nlinarith

/-! ## Blindness -/

theorem weilTest_ofReal_apply (f : ℝ → ℝ) (y : ℝ) :
    EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ)) y =
      ∫ u, ((f u * f (u - y) : ℝ) : ℂ) := by
  rw [EF.weilTest, convolution_def]
  simp only [ContinuousLinearMap.mul_apply', EF.tilde, neg_sub, Complex.conj_ofReal]
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  push_cast
  ring

theorem bumpSum_mul_bumpSum_sub_eq_zero {φ : ℝ → ℝ} {δ : ℝ} (hφs : ∀ u, δ / 2 < |u| → φ u = 0)
    {a x : Fin N → ℝ} {y : ℝ} (hy : ∀ i j, δ < |x i - x j - y|) (u : ℝ) :
    bumpSum φ a x u * bumpSum φ a x (u - y) = 0 := by
  unfold bumpSum
  rw [Finset.sum_mul_sum]
  refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
  have hsub : u - y - x j = u - (y + x j) := by ring
  rw [hsub]
  have hfar : δ < |x i - (y + x j)| := by
    rw [show x i - (y + x j) = x i - x j - y by ring]
    exact hy i j
  have h0 := mul_translate_eq_zero hφs hfar u
  calc a i * φ (u - x i) * (a j * φ (u - (y + x j)))
      = a i * a j * (φ (u - x i) * φ (u - (y + x j))) := by ring
    _ = 0 := by rw [h0, mul_zero]

/-- **Blindness by support.**  If every difference stays more than `δ` from every `log n` and
`δ < log 2`, then `f ⋆ f̃` vanishes at every `±log n`, `n ≥ 2`. -/
theorem weilTest_bumpSum_log_eq_zero {φ : ℝ → ℝ} {δ : ℝ} (hφs : ∀ u, δ / 2 < |u| → φ u = 0)
    (hδ2 : δ < Real.log 2) {a x : Fin N → ℝ}
    (hgeom : ∀ i j, i ≠ j → ∀ n : ℕ, 2 ≤ n → δ < |x i - x j - Real.log n|) {n : ℕ}
    (hn : 2 ≤ n) :
    EF.weilTest (fun u => (bumpSum φ a x u : ℂ)) (fun u => (bumpSum φ a x u : ℂ))
        (Real.log n) = 0 ∧
      EF.weilTest (fun u => (bumpSum φ a x u : ℂ)) (fun u => (bumpSum φ a x u : ℂ))
        (-Real.log n) = 0 := by
  have hlog2 : Real.log 2 ≤ Real.log n :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hn)
  have hlogpos : δ < Real.log n := lt_of_lt_of_le hδ2 hlog2
  have hlogn : 0 < Real.log n := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
  constructor
  · rw [weilTest_ofReal_apply]
    have hz : ∀ u, bumpSum φ a x u * bumpSum φ a x (u - Real.log n) = 0 :=
      bumpSum_mul_bumpSum_sub_eq_zero hφs fun i j => by
        by_cases hij : i = j
        · subst hij
          rw [sub_self, zero_sub, abs_neg, abs_of_pos hlogn]
          exact hlogpos
        · exact hgeom i j hij n hn
    simp_rw [hz]
    simp
  · rw [weilTest_ofReal_apply]
    have hz : ∀ u, bumpSum φ a x u * bumpSum φ a x (u - -Real.log n) = 0 :=
      bumpSum_mul_bumpSum_sub_eq_zero hφs fun i j => by
        by_cases hij : i = j
        · subst hij
          rw [sub_self, zero_sub, neg_neg, abs_of_pos hlogn]
          exact hlogpos
        · have h := hgeom j i (Ne.symm hij) n hn
          rw [show x i - x j - -Real.log n = -(x j - x i - Real.log n) by ring, abs_neg]
          exact h
    simp_rw [hz]
    simp

/-- **Prime-blind positivity holds on support-blind separated narrow bumps.**  For every
separation `s > 0` there is `δ₀ > 0` such that every configuration of any number of bumps of
width `δ < δ₀`, `s`-separated and with every difference more than `δ` from every `log n`, is
prime-blind (`f ⋆ f̃` vanishes at every `±log n`) and has nonnegative pole and archimedean
energy. -/
theorem exists_primeBlind_nonneg_bumpSum {s : ℝ} (hs : 0 < s) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ → ∀ (N : ℕ) (φ : ℝ → ℝ) (a x : Fin N → ℝ),
      ContDiff ℝ 2 φ → (∀ u, δ / 2 < |u| → φ u = 0) →
      (∀ i j, i ≠ j → s ≤ |x i - x j|) →
      (∀ i j, i ≠ j → ∀ n : ℕ, 2 ≤ n → δ < |x i - x j - Real.log n|) →
      (∀ n : ℕ, 2 ≤ n →
        EF.weilTest (fun u => (bumpSum φ a x u : ℂ)) (fun u => (bumpSum φ a x u : ℂ))
          (Real.log n) = 0 ∧
        EF.weilTest (fun u => (bumpSum φ a x u : ℂ)) (fun u => (bumpSum φ a x u : ℂ))
          (-Real.log n) = 0) ∧
      0 ≤ WeilOneSided.weilArchRe (EF.weilTest (fun u => (bumpSum φ a x u : ℂ))
        (fun u => (bumpSum φ a x u : ℂ))) := by
  obtain ⟨δ₀, hδ₀, hpos⟩ := exists_le_weilArchRe_bumpSum hs
  refine ⟨min δ₀ (1 / 2), lt_min hδ₀ (by norm_num), fun δ hδ hδlt N φ a x hφ hφs hsep hgeom => ?_⟩
  have hδ2 : δ < Real.log 2 := by
    have := Real.log_two_gt_d9
    have := lt_of_lt_of_le hδlt (min_le_right _ _)
    linarith
  have hδ1 : δ < 1 := by linarith [lt_of_lt_of_le hδlt (min_le_right _ _)]
  exact ⟨fun n hn => weilTest_bumpSum_log_eq_zero hφs hδ2 hgeom hn,
    hpos δ hδ (lt_of_lt_of_le hδlt (min_le_left _ _)) N φ a x hφ hφs hsep
      (abs_sub_lt_log_of_geometry' hδ hδ1 hgeom)⟩

end RHTower.SeparatedBump

end
