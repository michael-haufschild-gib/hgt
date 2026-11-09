import GaloisForLFunctions.ArithmeticAuxiliaryDynamics.TheLedgerIsBlindToEveryZero
import GaloisForLFunctions.RHTower.ZetaStrongRecurrenceReceiver
import GaloisForLFunctions.HTGeometry.VitaliConvergence

/-!
# Returns are returns of the primes

Let `τ_j → ∞` be a sequence of return shifts of `ζ` on a disc in the upper quadrant, with vertical
translates locally bounded there. Then:

* **Propagation.** By Vitali and the identity theorem, `ζ(s + iτ_j) − ζ(s) → 0` on the whole quadrant,
  in particular on `Re s > 1`.
* **Returns of the primes.** Reading Dirichlet coefficients at large `Re s`, every phase returns:
  `n^{-iτ_j} → 1` for every `n ≥ 1`. So a return at a disc, wherever it is, is a simultaneous Kronecker
  return of all primes.
* **The price at the pole.** The translates converge to `ζ` on `Re s > 1`, and `ζ` has a pole. So they
  cannot stay bounded on any disc around `s = 1`: a return is paid by a spike of `ζ` near `1 + iτ_j`.

The whole-quadrant local boundedness premise is impossible when the shifts tend to positive
infinity: bounded reflected values and Gamma decay force a zero Vitali limit, contradicting
the uniform Euler lower bound. These implications are conditional; recurrence receivers
must use smaller domains or retain the conductor normalization.
-/

open Complex Filter Topology Metric Set
open GaloisForLFunctions.ArithmeticKreinLangerTheory

noncomputable section

namespace GaloisForLFunctions.ArithmeticAuxiliaryDynamics

/-- The upper quadrant, where every vertical translate of `ζ` is holomorphic. -/
def upperQuadrant : Set ℂ := {s | 0 < s.re ∧ 0 < s.im}

theorem isOpen_upperQuadrant : IsOpen upperQuadrant :=
  (isOpen_lt continuous_const continuous_re).inter (isOpen_lt continuous_const continuous_im)

theorem isPreconnected_upperQuadrant : IsPreconnected upperQuadrant :=
  ((convex_halfSpace_re_gt 0).inter (convex_halfSpace_im_gt 0)).isPreconnected

/-- The translates of `ζ` along `τ` are locally bounded on the upper quadrant. -/
def TranslatesLocallyBounded (τ : ℕ → ℝ) : Prop :=
  ∀ z ∈ upperQuadrant, ∃ R : ℝ, 0 < R ∧ ball z R ⊆ upperQuadrant ∧ ∃ C : ℝ,
    ∀ j, ∀ w ∈ ball z R, ‖riemannZeta (w + (τ j : ℂ) * I)‖ ≤ C

/-- `ζ(s + iτ_j)` tends to `ζ(s)` uniformly on a disc. -/
def ReturnsOnDisc (τ : ℕ → ℝ) (c : ℂ) (r : ℝ) : Prop :=
  ∀ ε > 0, ∀ᶠ j in atTop, τ j ∈ RHTower.zetaReturnSet (closedBall c r) ε

/-- The difference of a translate and `ζ`. -/
def translateDiff (τ : ℕ → ℝ) (j : ℕ) (s : ℂ) : ℂ :=
  riemannZeta (s + (τ j : ℂ) * I) - riemannZeta s

/-- The defect of the phase of `n + 1` at the shift `τ_j`. -/
def phaseDefect (τ : ℕ → ℝ) (j n : ℕ) : ℂ :=
  (((n : ℝ) + 1 : ℝ) : ℂ) ^ (-((τ j : ℂ) * I)) - 1

/-- The Dirichlet term of `ζ`. -/
def zetaTerm (w : ℂ) (n : ℕ) : ℂ := (((n : ℝ) + 1 : ℝ) : ℂ) ^ (-w)

theorem norm_zetaTerm (w : ℂ) (n : ℕ) : ‖zetaTerm w n‖ = ((n : ℝ) + 1) ^ (-w.re) := by
  rw [zetaTerm, Complex.norm_cpow_eq_rpow_re_of_pos (by positivity), Complex.neg_re]

theorem norm_phaseDefect_le (τ : ℕ → ℝ) (j n : ℕ) : ‖phaseDefect τ j n‖ ≤ 2 := by
  have h1 : ‖(((n : ℝ) + 1 : ℝ) : ℂ) ^ (-((τ j : ℂ) * I))‖ = 1 := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (by positivity)]
    simp
  have := norm_sub_le ((((n : ℝ) + 1 : ℝ) : ℂ) ^ (-((τ j : ℂ) * I))) 1
  rw [h1, norm_one] at this
  rw [phaseDefect]
  linarith

theorem summable_norm_zetaTerm {w : ℂ} (hw : 1 < w.re) : Summable fun n => ‖zetaTerm w n‖ := by
  simp_rw [norm_zetaTerm]
  have h := (summable_nat_add_iff 1).mpr (Real.summable_nat_rpow.mpr (by linarith : -w.re < -1))
  refine h.congr fun n => ?_
  push_cast
  rfl

theorem hasSum_zetaTerm {w : ℂ} (hw : 1 < w.re) : HasSum (zetaTerm w) (riemannZeta w) := by
  have hs := (summable_norm_zetaTerm hw).of_norm
  have heq : riemannZeta w = ∑' n, zetaTerm w n := by
    rw [zeta_eq_tsum_one_div_nat_add_one_cpow hw]
    refine tsum_congr fun n => ?_
    rw [zetaTerm, Complex.cpow_neg, one_div]
    push_cast
    rfl
  rw [heq]
  exact hs.hasSum

/-- A translate multiplies the Dirichlet term by the phase. -/
theorem zetaTerm_add (s : ℂ) (t : ℂ) (n : ℕ) :
    zetaTerm (s + t) n = zetaTerm s n * (((n : ℝ) + 1 : ℝ) : ℂ) ^ (-t) := by
  have hne : (((n : ℝ) + 1 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (by positivity : ((n : ℝ) + 1) ≠ 0)
  rw [zetaTerm, zetaTerm, neg_add, Complex.cpow_add _ _ hne]

/-- The difference of a translate is a Dirichlet series in the phase defects. -/
theorem hasSum_translateDiff (τ : ℕ → ℝ) (j : ℕ) {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun n => zetaTerm s n * phaseDefect τ j n) (translateDiff τ j s) := by
  have hre : 1 < (s + (τ j : ℂ) * I).re := by simpa using hs
  have h := (hasSum_zetaTerm hre).sub (hasSum_zetaTerm hs)
  have hfun : (fun n => zetaTerm s n * phaseDefect τ j n) =
      fun n => zetaTerm (s + (τ j : ℂ) * I) n - zetaTerm s n := by
    funext n
    rw [zetaTerm_add, phaseDefect]
    ring
  rw [hfun]
  exact h

/-- **Propagation.** A locally bounded return on a disc propagates to the whole quadrant. -/
theorem tendsto_translateDiff_zero {τ : ℕ → ℝ} (hτ : ∀ j, 0 ≤ τ j)
    (hbd : TranslatesLocallyBounded τ) {c : ℂ} {r : ℝ} (hr : 0 < r) (hc : c ∈ upperQuadrant)
    (hret : ReturnsOnDisc τ c r) {s : ℂ} (hs : s ∈ upperQuadrant) :
    Tendsto (fun j => translateDiff τ j s) atTop (𝓝 0) := by
  have hne1 : ∀ z ∈ upperQuadrant, z ≠ 1 := by
    intro z hz h
    have := hz.2
    rw [h] at this
    simp at this
  have hne2 : ∀ j, ∀ z ∈ upperQuadrant, z + (τ j : ℂ) * I ≠ 1 := by
    intro j z hz h
    have him : (z + (τ j : ℂ) * I).im = 1 * 0 := by rw [h]; simp
    have : (z + (τ j : ℂ) * I).im = z.im + τ j := by simp
    have h1 := hz.2
    have h2 := hτ j
    linarith
  have hdiff : ∀ j, DifferentiableOn ℂ (translateDiff τ j) upperQuadrant := by
    intro j z hz
    refine DifferentiableAt.differentiableWithinAt ?_
    refine DifferentiableAt.sub ?_ (differentiableAt_riemannZeta (hne1 z hz))
    exact (differentiableAt_riemannZeta (hne2 j z hz)).comp z
      (differentiableAt_id.add_const _)
  have hloc : ∀ z ∈ upperQuadrant, ∃ R : ℝ, 0 < R ∧ ball z R ⊆ upperQuadrant ∧ ∃ C : ℝ,
      ∀ j, ∀ w ∈ ball z R, ‖translateDiff τ j w‖ ≤ C := by
    intro z hz
    obtain ⟨R, hR, hsub, C, hC⟩ := hbd z hz
    have hcl : closedBall z (R / 2) ⊆ upperQuadrant :=
      (closedBall_subset_ball (by linarith)).trans hsub
    have hcont : ContinuousOn riemannZeta (closedBall z (R / 2)) := fun w hw =>
      (differentiableAt_riemannZeta (hne1 w (hcl hw))).continuousAt.continuousWithinAt
    obtain ⟨C', hC'⟩ := (isCompact_closedBall z (R / 2)).exists_bound_of_continuousOn hcont
    refine ⟨R / 2, by linarith, (ball_subset_ball (by linarith)).trans hsub, C + C', ?_⟩
    intro j w hw
    have h1 := hC j w (ball_subset_ball (by linarith) hw)
    have h2 := hC' w (ball_subset_closedBall hw)
    exact (norm_sub_le _ _).trans (add_le_add h1 h2)
  have hconv0 : ∀ z ∈ closedBall c r, Tendsto (fun j => translateDiff τ j z) atTop (𝓝 0) := by
    intro z hz
    rw [Metric.tendsto_atTop']
    intro ε hε
    obtain ⟨N, hN⟩ := eventually_atTop.mp (hret ε hε)
    refine ⟨N, fun j hj => ?_⟩
    rw [dist_zero_right]
    exact hN j hj.le z hz
  have hacc : ∃ᶠ z in 𝓝[≠] c, z ∈ closedBall c r :=
    (eventually_nhdsWithin_of_eventually_nhds (closedBall_mem_nhds c hr)).frequently
  obtain ⟨G, hGdiff, hG⟩ := HTGeometry.vitali_tendstoLocallyUniformlyOn_of_isPreconnected
    isPreconnected_upperQuadrant hdiff hloc hc hacc (fun z hz => ⟨0, hconv0 z hz⟩)
  have hGzero : EqOn G 0 upperQuadrant := by
    have hanal := hGdiff.analyticOnNhd isOpen_upperQuadrant
    refine hanal.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_upperQuadrant hc ?_
    have hmem : upperQuadrant ∈ 𝓝 c := isOpen_upperQuadrant.mem_nhds hc
    filter_upwards [closedBall_mem_nhds c hr, hmem] with z hz hzU
    exact tendsto_nhds_unique (hG.tendsto_at hzU) (hconv0 z hz)
  have hlim := hG.tendsto_at hs
  rwa [hGzero hs] at hlim

/-- The tail of the Dirichlet series beyond `N`, in the worst phase. -/
private lemma norm_tail_le {τ : ℕ → ℝ} {s : ℂ} (hs : 2 ≤ s.re) (j N : ℕ) :
    ‖∑' n, zetaTerm s (n + (N + 1)) * phaseDefect τ j (n + (N + 1))‖ ≤
      2 * ((N : ℝ) + 2) ^ (2 - s.re) := by
  have hbound : ∀ n, ‖zetaTerm s (n + (N + 1)) * phaseDefect τ j (n + (N + 1))‖ ≤
      2 * ((N : ℝ) + 2) ^ (2 - s.re) * realStep 1 (n + N) := by
    intro n
    have hm : ((n + (N + 1) : ℕ) : ℝ) + 1 = (n : ℝ) + N + 2 := by push_cast; ring
    rw [norm_mul, norm_zetaTerm, hm]
    have hx : (0 : ℝ) < (n : ℝ) + N + 2 := by positivity
    have hN2 : (0 : ℝ) < (N : ℝ) + 2 := by positivity
    have hle : (N : ℝ) + 2 ≤ (n : ℝ) + N + 2 := by
      have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    have hsplit : ((n : ℝ) + N + 2) ^ (-s.re) =
        ((n : ℝ) + N + 2) ^ (2 - s.re) * ((n : ℝ) + N + 2) ^ (-2 : ℝ) := by
      rw [← Real.rpow_add hx]
      congr 1
      ring
    have h1 : ((n : ℝ) + N + 2) ^ (2 - s.re) ≤ ((N : ℝ) + 2) ^ (2 - s.re) :=
      Real.rpow_le_rpow_of_nonpos hN2 hle (by linarith)
    have h2 : ((n : ℝ) + N + 2) ^ (-2 : ℝ) ≤ realStep 1 (n + N) := by
      rw [IsProducer.realStep_one, Real.rpow_neg hx.le, Real.rpow_two, ← one_div]
      have hcast : ((n + N : ℕ) : ℝ) = (n : ℝ) + N := by push_cast; ring
      rw [hcast]
      refine one_div_le_one_div_of_le (by positivity) ?_
      nlinarith
    have hp2 := norm_phaseDefect_le τ j (n + (N + 1))
    have hR := realStep_nonneg zero_le_one (n + N)
    rw [hsplit]
    calc _ ≤ (((N : ℝ) + 2) ^ (2 - s.re) * realStep 1 (n + N)) * 2 :=
          mul_le_mul (mul_le_mul h1 h2 (by positivity) (by positivity)) hp2 (norm_nonneg _)
            (by positivity)
      _ = _ := by ring
  have hsum : HasSum (fun n => 2 * ((N : ℝ) + 2) ^ (2 - s.re) * realStep 1 (n + N))
      (2 * ((N : ℝ) + 2) ^ (2 - s.re) * ((N : ℝ) + 1) ^ (-(1 : ℝ))) :=
    (hasSum_realStep_shift zero_lt_one N).mul_left _
  have hle := tsum_of_norm_bounded hsum hbound
  have hone : ((N : ℝ) + 1) ^ (-(1 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by
      have : (0 : ℝ) ≤ N := Nat.cast_nonneg N
      linarith) (by norm_num)
  have hpos : 0 ≤ 2 * ((N : ℝ) + 2) ^ (2 - s.re) := by positivity
  calc _ ≤ _ := hle
    _ ≤ 2 * ((N : ℝ) + 2) ^ (2 - s.re) * 1 := mul_le_mul_of_nonneg_left hone hpos
    _ = _ := mul_one _

/-- The decomposition isolating the phase at `N`. -/
private lemma norm_phase_le {τ : ℕ → ℝ} {s : ℂ} (hs : 2 ≤ s.re) (j N : ℕ) :
    ((N : ℝ) + 1) ^ (-s.re) * ‖phaseDefect τ j N‖ ≤
      ‖translateDiff τ j s‖ + ∑ n ∈ Finset.range N, ‖phaseDefect τ j n‖ +
        2 * ((N : ℝ) + 2) ^ (2 - s.re) := by
  have hs1 : 1 < s.re := by linarith
  have hsum := hasSum_translateDiff τ j hs1
  have hsummable := hsum.summable
  have hsplit := hsummable.sum_add_tsum_nat_add (N + 1)
  rw [hsum.tsum_eq, Finset.sum_range_succ] at hsplit
  have htail := norm_tail_le (τ := τ) hs j N
  set Tl := ∑' n, zetaTerm s (n + (N + 1)) * phaseDefect τ j (n + (N + 1)) with hTl
  have hfirst : ‖∑ n ∈ Finset.range N, zetaTerm s n * phaseDefect τ j n‖ ≤
      ∑ n ∈ Finset.range N, ‖phaseDefect τ j n‖ := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n _ => ?_)
    rw [norm_mul, norm_zetaTerm]
    have h1 : ((n : ℝ) + 1) ^ (-s.re) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by
        have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        linarith) (by linarith)
    calc _ ≤ 1 * ‖phaseDefect τ j n‖ := by gcongr
      _ = _ := one_mul _
  have hkey : zetaTerm s N * phaseDefect τ j N = translateDiff τ j s -
      ∑ n ∈ Finset.range N, zetaTerm s n * phaseDefect τ j n - Tl := by
    rw [← hsplit]
    ring
  have hnorm : ‖zetaTerm s N * phaseDefect τ j N‖ =
      ((N : ℝ) + 1) ^ (-s.re) * ‖phaseDefect τ j N‖ := by
    rw [norm_mul, norm_zetaTerm]
  rw [← hnorm, hkey]
  calc _ ≤ ‖translateDiff τ j s - ∑ n ∈ Finset.range N, zetaTerm s n * phaseDefect τ j n‖ + ‖Tl‖ :=
        norm_sub_le _ _
    _ ≤ ‖translateDiff τ j s‖ + ‖∑ n ∈ Finset.range N, zetaTerm s n * phaseDefect τ j n‖ + ‖Tl‖ := by
        gcongr
        exact norm_sub_le _ _
    _ ≤ _ := by linarith

/-- **Returns are returns of the primes.** A locally bounded return on a disc in the upper quadrant
makes every phase return: `(n + 1)^{-iτ_j} → 1`. -/
theorem tendsto_phaseDefect_zero {τ : ℕ → ℝ} (hτ : ∀ j, 0 ≤ τ j)
    (hbd : TranslatesLocallyBounded τ) {c : ℂ} {r : ℝ} (hr : 0 < r) (hc : c ∈ upperQuadrant)
    (hret : ReturnsOnDisc τ c r) (N : ℕ) :
    Tendsto (fun j => phaseDefect τ j N) atTop (𝓝 0) := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    rw [Metric.tendsto_atTop']
    intro ε hε
    have hA : (0 : ℝ) < (N : ℝ) + 1 := by positivity
    have hB : (0 : ℝ) < (N : ℝ) + 2 := by positivity
    have hratio0 : 0 ≤ ((N : ℝ) + 1) / ((N : ℝ) + 2) := by positivity
    have hratio1 : ((N : ℝ) + 1) / ((N : ℝ) + 2) < 1 := by
      rw [div_lt_one hB]
      linarith
    have hpow := tendsto_rpow_atTop_of_base_lt_one _ (by linarith) hratio1
    have hsmall : ∀ᶠ σ : ℝ in atTop,
        2 * ((N : ℝ) + 2) ^ 2 * (((N : ℝ) + 1) / ((N : ℝ) + 2)) ^ σ < ε / 2 := by
      have hlim := hpow.const_mul (2 * ((N : ℝ) + 2) ^ 2)
      rw [mul_zero] at hlim
      exact hlim.eventually (gt_mem_nhds (by positivity))
    obtain ⟨σ, hσ2, hσε⟩ := ((eventually_ge_atTop 2).and hsmall).exists
    set s : ℂ := (σ : ℂ) + I with hs
    have hsre : s.re = σ := by simp [hs]
    have hsim : s.im = 1 := by simp [hs]
    have hsU : s ∈ upperQuadrant := ⟨by rw [hsre]; linarith, by rw [hsim]; norm_num⟩
    have hF := tendsto_translateDiff_zero hτ hbd hr hc hret hsU
    have hS : Tendsto (fun j => ∑ n ∈ Finset.range N, ‖phaseDefect τ j n‖) atTop (𝓝 0) := by
      have := tendsto_finset_sum (Finset.range N) fun n hn =>
        (ih n (Finset.mem_range.mp hn)).norm
      simpa using this
    have hApow : 0 < ((N : ℝ) + 1) ^ σ := Real.rpow_pos_of_pos hA _
    have hcomb : Tendsto (fun j => ((N : ℝ) + 1) ^ σ *
        (‖translateDiff τ j s‖ + ∑ n ∈ Finset.range N, ‖phaseDefect τ j n‖)) atTop (𝓝 0) := by
      have := ((hF.norm).add hS).const_mul (((N : ℝ) + 1) ^ σ)
      simpa using this
    obtain ⟨J, hJ⟩ := eventually_atTop.mp (hcomb.eventually (gt_mem_nhds (half_pos hε)))
    refine ⟨J, fun j hj => ?_⟩
    rw [dist_zero_right]
    have hdecomp := norm_phase_le (τ := τ) (s := s) (by rw [hsre]; exact hσ2) j N
    rw [hsre] at hdecomp
    have hmul : ((N : ℝ) + 1) ^ σ * (((N : ℝ) + 1) ^ (-σ) * ‖phaseDefect τ j N‖) =
        ‖phaseDefect τ j N‖ := by
      rw [← mul_assoc, ← Real.rpow_add hA, add_neg_cancel, Real.rpow_zero, one_mul]
    have hmain := mul_le_mul_of_nonneg_left hdecomp hApow.le
    rw [hmul, mul_add] at hmain
    have htailid : ((N : ℝ) + 1) ^ σ * (2 * ((N : ℝ) + 2) ^ (2 - σ)) =
        2 * ((N : ℝ) + 2) ^ 2 * (((N : ℝ) + 1) / ((N : ℝ) + 2)) ^ σ := by
      rw [Real.div_rpow hA.le hB.le, sub_eq_add_neg, Real.rpow_add hB, Real.rpow_neg hB.le,
        Real.rpow_two]
      ring
    rw [htailid] at hmain
    have h1 := hJ j hj.le
    linarith

/-- On `Re s > 1` the translates converge to `ζ`, by dominated convergence in the phases. -/
theorem tendsto_translate_of_one_lt_re {τ : ℕ → ℝ} (hτ : ∀ j, 0 ≤ τ j)
    (hbd : TranslatesLocallyBounded τ) {c : ℂ} {r : ℝ} (hr : 0 < r) (hc : c ∈ upperQuadrant)
    (hret : ReturnsOnDisc τ c r) {s : ℂ} (hs : 1 < s.re) :
    Tendsto (fun j => riemannZeta (s + (τ j : ℂ) * I)) atTop (𝓝 (riemannZeta s)) := by
  have hdom := summable_norm_zetaTerm hs
  have hlim : Tendsto (fun j => ∑' n, zetaTerm s n * phaseDefect τ j n) atTop (𝓝 (∑' _n : ℕ, (0 : ℂ))) := by
    refine tendsto_tsum_of_dominated_convergence (bound := fun n => ‖zetaTerm s n‖ * 2)
      (hdom.mul_right 2) (fun n => ?_) (Eventually.of_forall fun j n => ?_)
    · have := (tendsto_phaseDefect_zero hτ hbd hr hc hret n).const_mul (zetaTerm s n)
      simpa using this
    · rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (norm_phaseDefect_le τ j n) (norm_nonneg _)
  rw [tsum_zero] at hlim
  have hdiff : Tendsto (fun j => translateDiff τ j s) atTop (𝓝 0) := by
    refine hlim.congr fun j => ?_
    exact (hasSum_translateDiff τ j hs).tsum_eq
  have := hdiff.add_const (riemannZeta s)
  rw [zero_add] at this
  refine this.congr fun j => ?_
  rw [translateDiff]
  ring

/-- **The price at the pole.** The translates along a return sequence are unbounded on every disc
around `s = 1`: a return is paid by a spike of `ζ` near `1 + iτ_j`. -/
theorem not_bounded_near_pole {τ : ℕ → ℝ} (hτ : ∀ j, 0 ≤ τ j)
    (hbd : TranslatesLocallyBounded τ) {c : ℂ} {r : ℝ} (hr : 0 < r) (hc : c ∈ upperQuadrant)
    (hret : ReturnsOnDisc τ c r) {δ C : ℝ} (hδ : 0 < δ) :
    ¬ ∀ᶠ j in atTop, ∀ w ∈ ball (1 : ℂ) δ, ‖riemannZeta (w + (τ j : ℂ) * I)‖ ≤ C := by
  intro hev
  -- The bound passes to the limit at every real point just right of the pole.
  have hbound : ∀ t : ℝ, 0 < t → t < δ → ‖riemannZeta ((1 : ℂ) + t)‖ ≤ C := by
    intro t ht htδ
    have hre : 1 < ((1 : ℂ) + t).re := by simpa using ht
    have hmem : (1 : ℂ) + t ∈ ball (1 : ℂ) δ := by
      rw [mem_ball_iff_norm, add_sub_cancel_left, Complex.norm_real, Real.norm_of_nonneg ht.le]
      exact htδ
    have hlim := (tendsto_translate_of_one_lt_re hτ hbd hr hc hret hre).norm
    refine le_of_tendsto hlim ?_
    filter_upwards [hev] with j hj
    exact hj _ hmem
  -- But `(s − 1) ζ(s) → 1`.
  have hres := riemannZeta_residue_one
  have hpath : Tendsto (fun t : ℝ => (1 : ℂ) + t) (𝓝[>] 0) (𝓝[≠] 1) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have : Tendsto (fun t : ℝ => (1 : ℂ) + t) (𝓝 0) (𝓝 ((1 : ℂ) + ((0 : ℝ) : ℂ))) :=
        (continuous_const.add Complex.continuous_ofReal).tendsto 0
      simpa using this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t ht
      have ht' : (0 : ℝ) < t := ht
      simp only [mem_compl_iff, mem_singleton_iff, add_eq_left]
      exact_mod_cast ht'.ne'
  have hcomp := hres.comp hpath
  have hzero : Tendsto (fun t : ℝ => (((1 : ℂ) + t - 1) * riemannZeta ((1 : ℂ) + t))) (𝓝[>] 0) (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hup : Tendsto (fun t : ℝ => |t| * max C 0) (𝓝[>] 0) (𝓝 0) := by
      have h0 : Tendsto (fun t : ℝ => |t|) (𝓝[>] 0) (𝓝 0) := by
        have := (continuous_abs.tendsto (0 : ℝ)).mono_left (nhdsWithin_le_nhds (s := Ioi 0))
        simpa using this
      simpa using h0.mul_const (max C 0)
    refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hup
    filter_upwards [Ioo_mem_nhdsGT hδ] with t ht
    rw [add_sub_cancel_left, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left ((hbound t ht.1 ht.2).trans (le_max_left _ _)) (abs_nonneg _)
  have hone := tendsto_nhds_unique hcomp hzero
  exact one_ne_zero hone

end GaloisForLFunctions.ArithmeticAuxiliaryDynamics
