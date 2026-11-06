import GaloisForLFunctions.ArithmeticInnerFunctionTheory.TheCrowdOfTheInnerField
import GaloisForLFunctions.HTGeometry.SimultaneousDirichlet
import GaloisForLFunctions.RHTower.DeBruijnNewmanNonnegative
import GaloisForLFunctions.RHTower.ZetaWeakRecurrenceLadderCollapse

/-!
# Can an inner factor be finite and nontrivial?

An inner factor can be finite and nontrivial on a datum only if the datum has no vertical recurrence.

* **The zero–one law of recurrence** (`zero_free_or_infinite_of_recurrent`). For an entire function with vertical
  returns on a strip, the zeros in the strip are absent or infinite. A zero is transported to arbitrarily large height.
* **Dirichlet polynomials recur** (`isVerticallyRecurrent_dirichletPoly`), by simultaneous Dirichlet approximation, and so do
  periodic data (`isVerticallyRecurrent_of_periodic`), so their inner factors have degree `0` or `∞`. This is the
  mechanism through which incommensurability of `log p` enters: `Π_p p^{iτ}` still returns to `1`.
* **Finite inner factors vanish at infinity** (`tendsto_innerField_of_finite`). If `ζ` had finitely many right zeros,
  then `I(σ + it) → 0` as `t → ∞`: `E` is asymptotically outer on every vertical line.
* **A vanishing field gives the zeros approach the line** (`exists_height_bound_of_tendsto_innerField`). If `I(σ + it) → 0` on every vertical
  line then for each `h > 0` only finitely high zeros lie right of `½ + h`. So vanishing of the inner
  field at infinity sits between RH and the split of RH into its two halves.
-/

open Complex Filter Topology Metric Set
open scoped Real ComplexConjugate

namespace GaloisForLFunctions.ArithmeticInnerFunctionTheory

open _root_.RHTower

noncomputable section

/-- Vertical returns on the set `U`: every closed disc in `U` returns within every `ε` beyond every height. -/
def IsVerticallyRecurrent (F : ℂ → ℂ) (U : Set ℂ) : Prop :=
  ∀ (c : ℂ) (r : ℝ), 0 < r → closedBall c r ⊆ U → ∀ ε > 0, ∀ T₀ : ℝ, ∃ τ : ℝ, T₀ ≤ τ ∧
    ∀ s ∈ closedBall c r, ‖F (s + τ * I) - F s‖ < ε

/-- A nonzero entire function has an isolating circle around each zero. -/
theorem exists_isolating_circle {F : ℂ → ℂ} (hF : Differentiable ℂ F) {x₀ : ℂ} (hx₀ : F x₀ ≠ 0) (ρ : ℂ)
    {R : ℝ} (hR : 0 < R) :
    ∃ r > 0, r ≤ R ∧ ∃ m > 0, ∀ z ∈ sphere ρ r, m ≤ ‖F z‖ := by
  have han : AnalyticAt ℂ F ρ := hF.analyticAt ρ
  have hne : ∀ᶠ z in 𝓝[≠] ρ, F z ≠ 0 := by
    refine han.eventually_eq_zero_or_eventually_ne_zero.resolve_left fun h => ?_
    have hzero := AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero (f := F) (U := univ)
      (fun z _ => hF.analyticAt z) isPreconnected_univ (mem_univ ρ) h
    exact hx₀ (hzero (mem_univ x₀))
  obtain ⟨r₁, hr₁, hball⟩ := Metric.eventually_nhds_iff.mp (eventually_nhdsWithin_iff.mp hne)
  set r := min (r₁ / 2) R with hr
  have hr0 : 0 < r := lt_min (by linarith) hR
  have hrr : r < r₁ := (min_le_left _ _).trans_lt (by linarith)
  have hsph : ∀ z ∈ sphere ρ r, F z ≠ 0 := by
    intro z hz
    have hd : dist z ρ = r := mem_sphere.mp hz
    have hzρ : z ≠ ρ := by
      intro h
      rw [h, dist_self] at hd
      linarith
    exact hball (by rw [hd]; exact hrr) hzρ
  obtain ⟨z₁, hz₁, hmin⟩ := (isCompact_sphere ρ r).exists_isMinOn
    (NormedSpace.sphere_nonempty.mpr hr0.le) (hF.continuous.norm.continuousOn)
  exact ⟨r, hr0, min_le_right _ _, ‖F z₁‖, norm_pos_iff.mpr (hsph z₁ hz₁), fun z hz => hmin hz⟩

/-- **Returns transport zeros.** -/
theorem exists_zero_far_of_recurrent {F : ℂ → ℂ} (hF : Differentiable ℂ F) {x₀ : ℂ} (hx₀ : F x₀ ≠ 0)
    {U : Set ℂ} (hR : IsVerticallyRecurrent F U) {ρ : ℂ} (hρ : F ρ = 0) {R : ℝ} (hR0 : 0 < R)
    (hU : closedBall ρ R ⊆ U) (T₀ : ℝ) :
    ∃ τ : ℝ, T₀ ≤ τ ∧ ∃ z ∈ ball ρ R, F (z + τ * I) = 0 := by
  obtain ⟨r, hr, hrR, m, hm, hmin⟩ := exists_isolating_circle hF hx₀ ρ hR0
  obtain ⟨τ, hτ, hclose⟩ := hR ρ r hr ((closedBall_subset_closedBall hrR).trans hU) (m / 2)
    (by linarith) T₀
  refine ⟨τ, hτ, ?_⟩
  have hdiff : DifferentiableOn ℂ (fun s => F (s + τ * I)) (closedBall ρ r) :=
    (hF.comp (differentiable_id.add_const _)).differentiableOn
  obtain ⟨z, hz, hz0⟩ := DeBruijn.exists_zero_of_norm_lt_sphere_on hr hdiff fun z hz => by
    have h1 := hclose ρ (mem_closedBall_self hr.le)
    rw [hρ, sub_zero] at h1
    have h2 := hclose z (sphere_subset_closedBall hz)
    have h3 := hmin z hz
    have h4 := norm_sub_norm_le (F z) (F (z + τ * I))
    rw [norm_sub_rev] at h4
    linarith
  exact ⟨z, ball_subset_ball hrR hz, hz0⟩

/-- A vertical strip. -/
def vStrip (a b : ℝ) : Set ℂ := {s | a < s.re ∧ s.re < b}

theorem exists_closedBall_subset_vStrip {a b : ℝ} {ρ : ℂ} (hρ : ρ ∈ vStrip a b) :
    ∃ R > 0, closedBall ρ R ⊆ vStrip a b := by
  have hR : 0 < min (ρ.re - a) (b - ρ.re) / 2 := by
    have := hρ.1
    have := hρ.2
    have : 0 < min (ρ.re - a) (b - ρ.re) := lt_min (by linarith) (by linarith)
    linarith
  refine ⟨_, hR, fun z hz => ?_⟩
  have hd : ‖z - ρ‖ ≤ min (ρ.re - a) (b - ρ.re) / 2 := by
    rwa [mem_closedBall, dist_eq_norm] at hz
  have hre := Complex.abs_re_le_norm (z - ρ)
  rw [Complex.sub_re] at hre
  have h1 := abs_le.mp (hre.trans hd)
  have h2 := min_le_left (ρ.re - a) (b - ρ.re)
  have h3 := min_le_right (ρ.re - a) (b - ρ.re)
  have hm : 0 < min (ρ.re - a) (b - ρ.re) := by linarith
  constructor <;> linarith [h1.1, h1.2]

/-- **The zero–one law.** The zeros of a recurrent entire function in a strip are absent or infinite. -/
theorem zero_free_or_infinite_of_recurrent {F : ℂ → ℂ} (hF : Differentiable ℂ F) {x₀ : ℂ}
    (hx₀ : F x₀ ≠ 0) {a b : ℝ} (hR : IsVerticallyRecurrent F (vStrip a b)) :
    (∀ s ∈ vStrip a b, F s ≠ 0) ∨ {s | s ∈ vStrip a b ∧ F s = 0}.Infinite := by
  by_contra hcon
  push Not at hcon
  obtain ⟨⟨ρ, hρ, hρ0⟩, hfin⟩ := hcon
  obtain ⟨M, hM⟩ : BddAbove (Complex.im '' {s | s ∈ vStrip a b ∧ F s = 0}) :=
    (hfin.image _).bddAbove
  obtain ⟨R, hR0, hU⟩ := exists_closedBall_subset_vStrip hρ
  obtain ⟨τ, hτ, z, hz, hz0⟩ := exists_zero_far_of_recurrent hF hx₀ hR hρ0 hR0 hU (M - ρ.im + R + 1)
  have hzs : z ∈ vStrip a b := hU (ball_subset_closedBall hz)
  have hzz : z + τ * I ∈ vStrip a b := by
    simpa [vStrip] using hzs
  have him : (z + τ * I).im ≤ M := hM ⟨_, ⟨hzz, hz0⟩, rfl⟩
  have hd : ‖z - ρ‖ < R := by rwa [mem_ball, dist_eq_norm] at hz
  have hi := Complex.abs_im_le_norm (z - ρ)
  rw [Complex.sub_im] at hi
  have h1 := abs_le.mp (hi.trans hd.le)
  simp at him
  linarith [h1.1]

/-- Periodic data recur. -/
theorem isVerticallyRecurrent_of_periodic {F : ℂ → ℂ} {P : ℝ} (hP : 0 < P)
    (hper : ∀ s, F (s + P * I) = F s) (U : Set ℂ) : IsVerticallyRecurrent F U := by
  intro c r _ _ ε hε T₀
  obtain ⟨n, hn⟩ := exists_nat_ge (T₀ / P)
  refine ⟨(n : ℝ) * P, by rwa [div_le_iff₀ hP] at hn, fun s _ => ?_⟩
  have hk : ∀ k : ℕ, F (s + ((k : ℝ) * P : ℝ) * I) = F s := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have e : s + (((k + 1 : ℕ) : ℝ) * P : ℝ) * I = (s + ((k : ℝ) * P : ℝ) * I) + P * I := by
        push_cast
        ring
      rw [e, hper, ih]
  rw [hk n, sub_self, norm_zero]
  exact hε

/-- A Dirichlet polynomial. -/
def dirichletPoly (S : Finset ℕ) (a : ℕ → ℂ) (s : ℂ) : ℂ := ∑ n ∈ S, a n * (n : ℂ) ^ (-s)

theorem differentiable_dirichletPoly (S : Finset ℕ) (hS : ∀ n ∈ S, 1 ≤ n) (a : ℕ → ℂ) :
    Differentiable ℂ (dirichletPoly S a) := by
  unfold dirichletPoly
  refine Differentiable.fun_sum fun n hn => ?_
  have hn0 : (n : ℂ) ≠ 0 := by
    have := hS n hn
    exact_mod_cast (by omega : n ≠ 0)
  exact (differentiable_const _).mul ((differentiable_id.neg).const_cpow (Or.inl hn0))

/-- **Dirichlet polynomials recur**, by simultaneous Dirichlet approximation of `τ log n / 2π`. -/
theorem isVerticallyRecurrent_dirichletPoly (S : Finset ℕ) (hS : ∀ n ∈ S, 1 ≤ n) (a : ℕ → ℂ)
    (U : Set ℂ) : IsVerticallyRecurrent (dirichletPoly S a) U := by
  intro c r _ _ ε hε T₀
  -- a uniform bound for the terms on the disc
  have hcont : ∀ n ∈ S, ContinuousOn (fun s : ℂ => ‖a n * (n : ℂ) ^ (-s)‖) (closedBall c r) := by
    intro n hn
    have hn0 : (n : ℂ) ≠ 0 := by
      have := hS n hn
      exact_mod_cast (by omega : n ≠ 0)
    exact ((continuous_const.mul (continuous_neg.const_cpow (Or.inl hn0))).norm).continuousOn
  have hB : ∃ B : ℝ, 0 ≤ B ∧ ∀ s ∈ closedBall c r, ∑ n ∈ S, ‖a n * (n : ℂ) ^ (-s)‖ ≤ B := by
    obtain ⟨B, hB⟩ := (isCompact_closedBall c r).exists_bound_of_continuousOn
      (continuousOn_finsetSum S hcont)
    refine ⟨|B|, abs_nonneg _, fun s hs => ?_⟩
    have := hB s hs
    rw [Real.norm_of_nonneg (Finset.sum_nonneg fun _ _ => norm_nonneg _)] at this
    exact this.trans (le_abs_self _)
  obtain ⟨B, hB0, hB⟩ := hB
  set τ₀ : ℝ := max T₀ 1 with hτ₀
  have hτ₀1 : 1 ≤ τ₀ := le_max_right _ _
  -- the accuracy of the phases
  obtain ⟨Q, hQ, hQε⟩ : ∃ Q : ℕ, 0 < Q ∧ 2 * π * B / Q < ε := by
    obtain ⟨Q, hQ⟩ := exists_nat_gt (2 * π * B / ε)
    have hQ0 : (0 : ℝ) < Q := lt_of_le_of_lt (by positivity) hQ
    refine ⟨Q, by exact_mod_cast hQ0, ?_⟩
    rw [div_lt_iff₀ hQ0]
    rw [div_lt_iff₀ hε] at hQ
    linarith
  set idx := S.equivFin with hidx
  obtain ⟨q, hq1, -, hq⟩ := GaloisForLFunctions.HTGeometry.exists_simultaneous_dirichlet
    (fun i : Fin S.card => τ₀ * Real.log ((idx.symm i : ℕ) : ℝ) / (2 * π)) hQ
  refine ⟨(q : ℝ) * τ₀, ?_, fun s hs => ?_⟩
  · have hq1' : (1 : ℝ) ≤ q := by exact_mod_cast hq1
    nlinarith [le_max_left T₀ 1]
  -- each phase is within `2π/Q` of one
  have hphase : ∀ n ∈ S, ‖(n : ℂ) ^ (-(((q : ℝ) * τ₀ : ℝ) * I)) - 1‖ ≤ 2 * π / Q := by
    intro n hn
    obtain ⟨p, hp⟩ := hq (idx ⟨n, hn⟩)
    have hn1 : (0 : ℝ) < n := by
      have := hS n hn
      exact_mod_cast (by omega : 0 < n)
    simp only [Equiv.symm_apply_apply] at hp
    set y : ℝ := (q : ℝ) * τ₀ * Real.log n with hy
    have hcpow : (n : ℂ) ^ (-(((q : ℝ) * τ₀ : ℝ) * I)) = Complex.exp ((-y : ℝ) * I) := by
      rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hn1.ne'), ← Complex.ofReal_natCast,
        ← Complex.ofReal_log hn1.le, hy]
      congr 1
      push_cast
      ring
    have hdiff : |y - p * (2 * π)| ≤ 2 * π / Q := by
      have e : y - p * (2 * π) = (2 * π) * ((q : ℝ) * (τ₀ * Real.log n / (2 * π)) - p) := by
        rw [hy]
        field_simp
      rw [e, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * π)]
      have h3 := mul_le_mul_of_nonneg_left hp.le (by positivity : (0 : ℝ) ≤ 2 * π)
      have e3 : 2 * π * (1 / (Q : ℝ)) = 2 * π / Q := by ring
      rwa [e3] at h3
    have hper : Complex.exp ((-y : ℝ) * I) = Complex.exp (((-(y - p * (2 * π)) : ℝ) : ℂ) * I) := by
      have e2 : ((-(y - p * (2 * π)) : ℝ) : ℂ) * I = ((-y : ℝ) : ℂ) * I + (p : ℂ) * (2 * π * I) := by
        push_cast
        ring
      rw [e2, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
    rw [hcpow, hper, mul_comm]
    refine (Real.norm_exp_I_mul_ofReal_sub_one_le (x := -(y - p * (2 * π)))).trans ?_
    rw [Real.norm_eq_abs, abs_neg]
    exact hdiff
  -- the sum of the phases
  have hsplit : dirichletPoly S a (s + ((q : ℝ) * τ₀ : ℝ) * I) - dirichletPoly S a s =
      ∑ n ∈ S, (a n * (n : ℂ) ^ (-s)) * ((n : ℂ) ^ (-(((q : ℝ) * τ₀ : ℝ) * I)) - 1) := by
    unfold dirichletPoly
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun n hn => ?_
    have hn0 : (n : ℂ) ≠ 0 := by
      have := hS n hn
      exact_mod_cast (by omega : n ≠ 0)
    rw [neg_add, Complex.cpow_add _ _ hn0]
    ring
  rw [hsplit]
  have hQ0 : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hle : ‖∑ n ∈ S, (a n * (n : ℂ) ^ (-s)) * ((n : ℂ) ^ (-(((q : ℝ) * τ₀ : ℝ) * I)) - 1)‖ ≤
      ∑ n ∈ S, ‖a n * (n : ℂ) ^ (-s)‖ * (2 * π / Q) := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n hn => ?_)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hphase n hn) (norm_nonneg _)
  rw [← Finset.sum_mul] at hle
  have hB2 := mul_le_mul_of_nonneg_right (hB s hs) (show 0 ≤ 2 * π / (Q : ℝ) by positivity)
  have e : B * (2 * π / (Q : ℝ)) = 2 * π * B / Q := by ring
  rw [e] at hB2
  exact lt_of_le_of_lt (hle.trans hB2) hQε

/-- **Dirichlet polynomials have inner degree `0` or `∞`** on every strip. -/
theorem dirichletPoly_zero_free_or_infinite (S : Finset ℕ) (hS : ∀ n ∈ S, 1 ≤ n) (a : ℕ → ℂ) {x₀ : ℂ}
    (hx₀ : dirichletPoly S a x₀ ≠ 0) (c d : ℝ) :
    (∀ s ∈ vStrip c d, dirichletPoly S a s ≠ 0) ∨
      {s | s ∈ vStrip c d ∧ dirichletPoly S a s = 0}.Infinite :=
  zero_free_or_infinite_of_recurrent (differentiable_dirichletPoly S hS a) hx₀
    (isVerticallyRecurrent_dirichletPoly S hS a _)

/-! ### Finite inner factors vanish at infinity -/

/-- The Green kernel from above: `G(w, ρ) ≤ 2xb/|ρ − w|²`. -/
theorem greenKernel_le {w ρ : ℂ} (hw : 1 / 2 < w.re) (hρ : 1 / 2 < ρ.re) (hne : ρ ≠ w) :
    greenKernel w ρ ≤ 2 * (w.re - 1 / 2) * (ρ.re - 1 / 2) / ‖ρ - w‖ ^ 2 := by
  have hB : 0 < ‖ρ - w‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  have hpol : ‖ρ + conj w - 1‖ ^ 2 = ‖ρ - w‖ ^ 2 + 4 * (w.re - 1 / 2) * (ρ.re - 1 / 2) := by
    rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply,
      Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.add_re, Complex.conj_re, Complex.one_re,
      Complex.sub_im, Complex.add_im, Complex.conj_im, Complex.one_im]
    ring
  have hApos : 0 < ‖ρ + conj w - 1‖ := norm_pos_iff.mpr (ne_zero_of_half_lt_re hw hρ)
  have hlog : Real.log (‖ρ + conj w - 1‖ ^ 2 / ‖ρ - w‖ ^ 2) ≤
      ‖ρ + conj w - 1‖ ^ 2 / ‖ρ - w‖ ^ 2 - 1 :=
    Real.log_le_sub_one_of_pos (by positivity)
  have hG : greenKernel w ρ = (1 / 2) * Real.log (‖ρ + conj w - 1‖ ^ 2 / ‖ρ - w‖ ^ 2) := by
    rw [greenKernel, ← div_pow, Real.log_pow]
    push_cast
    ring
  have hfrac : ‖ρ + conj w - 1‖ ^ 2 / ‖ρ - w‖ ^ 2 - 1 =
      4 * (w.re - 1 / 2) * (ρ.re - 1 / 2) / ‖ρ - w‖ ^ 2 := by
    rw [hpol]
    field_simp
    ring
  rw [hG]
  rw [hfrac] at hlog
  have e : 2 * (w.re - 1 / 2) * (ρ.re - 1 / 2) / ‖ρ - w‖ ^ 2 =
      (1 / 2) * (4 * (w.re - 1 / 2) * (ρ.re - 1 / 2) / ‖ρ - w‖ ^ 2) := by
    ring
  rw [e]
  linarith

/-- **A finite inner factor vanishes at infinity.** If `ζ` has finitely many right zeros, then
`I(σ + it) → 0` as `t → ∞`, for each `σ > ½`. -/
theorem tendsto_innerField_of_finite [Finite ZetaRightZero] {σ : ℝ} (hσ : 1 / 2 < σ) :
    Tendsto (fun t : ℝ => innerField ((σ : ℂ) + (t : ℂ) * I)) atTop (𝓝 0) := by
  classical
  haveI := Fintype.ofFinite ZetaRightZero
  have hne : ∀ᶠ t : ℝ in atTop, ∀ ρ : ZetaRightZero, (ρ : ℂ).im < t := by
    obtain ⟨M, hM⟩ := (Set.finite_range fun ρ : ZetaRightZero => (ρ : ℂ).im).bddAbove
    filter_upwards [eventually_gt_atTop M] with t ht ρ
    exact lt_of_le_of_lt (hM ⟨ρ, rfl⟩) ht
  have hre : ∀ t : ℝ, ((σ : ℂ) + (t : ℂ) * I).re = σ := fun t => by simp
  have him : ∀ t : ℝ, ((σ : ℂ) + (t : ℂ) * I).im = t := fun t => by simp
  have hval : ∀ᶠ t : ℝ in atTop, innerField ((σ : ℂ) + (t : ℂ) * I) =
      ∑ ρ : ZetaRightZero, zeroMult ρ * greenKernel ((σ : ℂ) + (t : ℂ) * I) ρ := by
    filter_upwards [hne] with t ht
    have h0 : zetaEntire ((σ : ℂ) + (t : ℂ) * I) ≠ 0 := by
      intro h
      have hz := zetaEntire_eq_zero_iff.mp h
      have := ht ⟨_, hz, by rw [hre]; exact hσ⟩
      simp only [him, lt_self_iff_false] at this
    exact ((hasSum_innerField (by rw [hre]; exact hσ) h0).unique (hasSum_fintype _))
  have hterm : ∀ ρ : ZetaRightZero, Tendsto
      (fun t : ℝ => zeroMult ρ * greenKernel ((σ : ℂ) + (t : ℂ) * I) ρ) atTop (𝓝 0) := by
    intro ρ
    have hb : 0 < (ρ : ℂ).re - 1 / 2 := by linarith [ρ.2.2]
    have hx : 0 < σ - 1 / 2 := by linarith
    have hmaj : Tendsto (fun t : ℝ => 2 * (σ - 1 / 2) * ((ρ : ℂ).re - 1 / 2) / (t - (ρ : ℂ).im) ^ 2)
        atTop (𝓝 0) := by
      refine tendsto_const_nhds.div_atTop ?_
      have h1 : Tendsto (fun t : ℝ => t - (ρ : ℂ).im) atTop atTop :=
        tendsto_atTop_add_const_right _ _ tendsto_id
      exact (tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp h1
    have hsq : Tendsto (fun t : ℝ => greenKernel ((σ : ℂ) + (t : ℂ) * I) ρ) atTop (𝓝 0) := by
      refine squeeze_zero' ?_ ?_ hmaj
      · filter_upwards [hne] with t ht
        have hneq : (ρ : ℂ) ≠ (σ : ℂ) + (t : ℂ) * I := by
          intro h
          have := ht ρ
          rw [h, him] at this
          exact lt_irrefl _ this
        exact (greenKernel_pos (by rw [hre]; exact hσ) ρ.2.2 hneq).le
      · filter_upwards [hne] with t ht
        have hneq : (ρ : ℂ) ≠ (σ : ℂ) + (t : ℂ) * I := by
          intro h
          have := ht ρ
          rw [h, him] at this
          exact lt_irrefl _ this
        refine (greenKernel_le (by rw [hre]; exact hσ) ρ.2.2 hneq).trans ?_
        rw [hre]
        have hd : 0 < t - (ρ : ℂ).im := sub_pos.mpr (ht ρ)
        have him2 := Complex.abs_im_le_norm ((ρ : ℂ) - ((σ : ℂ) + (t : ℂ) * I))
        rw [Complex.sub_im, him, abs_sub_comm, abs_of_pos hd] at him2
        have hsq2 : (t - (ρ : ℂ).im) ^ 2 ≤ ‖(ρ : ℂ) - ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2 :=
          pow_le_pow_left₀ hd.le him2 2
        exact div_le_div_of_nonneg_left (by positivity) (by positivity) hsq2
    simpa using hsq.const_mul (zeroMult ρ)
  have hs := tendsto_finsetSum (Finset.univ : Finset ZetaRightZero) (fun ρ _ => hterm ρ)
  simp only [Finset.sum_const_zero] at hs
  exact hs.congr' (hval.mono fun _ h => h.symm)

/-! ### A vanishing inner field -/

/-- The zeros lie in `Re s < 1`, so their depth is below `½`. -/
theorem ZetaRightZero.re_lt_one (ρ : ZetaRightZero) : (ρ : ℂ).re < 1 := by
  by_contra h
  exact riemannZeta_ne_zero_of_one_le_re (not_lt.mp h) ρ.2.1

theorem one_le_zeroMult (ρ : ZetaRightZero) : 1 ≤ zeroMult ρ := by
  have hp := zeroMult_pos ρ
  rw [zeroMult] at hp ⊢
  have : 0 < analyticOrderNatAt riemannZeta (ρ : ℂ) := by exact_mod_cast hp
  exact_mod_cast this

/-- **A vanishing field bounds the height of the deep zeros.** If `I(½ + h + it) → 0` as `t → ∞`, then the
zeros with `Re ρ ≥ ½ + h` have bounded height. -/
theorem exists_height_bound_of_tendsto_innerField {h : ℝ} (hh : 0 < h)
    (hT : Tendsto (fun t : ℝ => innerField (((1 / 2 + h : ℝ) : ℂ) + (t : ℂ) * I)) atTop (𝓝 0)) :
    ∃ T : ℝ, ∀ ρ : ZetaRightZero, 1 / 2 + h ≤ (ρ : ℂ).re → (ρ : ℂ).im < T := by
  have hc : (0 : ℝ) < 4 * h / 5 := by positivity
  obtain ⟨T, hT'⟩ := Filter.eventually_atTop.mp (hT.eventually (gt_mem_nhds hc))
  refine ⟨T, fun ρ hρ => ?_⟩
  by_contra hcon
  push Not at hcon
  have hw' : (1 / 2 : ℝ) < 1 / 2 + h := by linarith
  -- a nonzero point at height within `h` of `ρ`
  have hcount : {u : ℝ | zetaEntire (((1 / 2 + h : ℝ) : ℂ) + (((ρ : ℂ).im + u : ℝ) : ℂ) * I) = 0}.Countable := by
    have hinj : Function.Injective
        (fun u : ℝ => ((1 / 2 + h : ℝ) : ℂ) + (((ρ : ℂ).im + u : ℝ) : ℂ) * I) := by
      intro a b hab
      have := congrArg Complex.im hab
      simpa using this
    exact countable_setOf_zetaEntire_eq_zero.preimage hinj
  obtain ⟨u, hu, hu0⟩ : ∃ u ∈ Set.Icc 0 h,
      zetaEntire (((1 / 2 + h : ℝ) : ℂ) + (((ρ : ℂ).im + u : ℝ) : ℂ) * I) ≠ 0 := by
    by_contra hall
    push Not at hall
    have hsub : Set.Icc 0 h ⊆ {u : ℝ | zetaEntire (((1 / 2 + h : ℝ) : ℂ) +
        (((ρ : ℂ).im + u : ℝ) : ℂ) * I) = 0} := fun u hu => hall u hu
    have hcc := hcount.mono hsub
    have hm := hcc.measure_zero MeasureTheory.volume
    rw [Real.volume_Icc, ENNReal.ofReal_eq_zero] at hm
    linarith
  set w : ℂ := ((1 / 2 + h : ℝ) : ℂ) + (((ρ : ℂ).im + u : ℝ) : ℂ) * I with hw
  have hre : w.re = 1 / 2 + h := by simp [hw]
  have him : w.im = (ρ : ℂ).im + u := by simp [hw]
  have hne : (ρ : ℂ) ≠ w := by
    intro he
    apply hu0
    rw [← he, zetaEntire_eq_zero_iff]
    exact ρ.2.1
  have hb1 : (ρ : ℂ).re - 1 / 2 < 1 / 2 := by linarith [ρ.re_lt_one]
  have hb2 : h ≤ (ρ : ℂ).re - 1 / 2 := by linarith
  have hG := greenKernel_ge (w := w) (ρ := ρ) (by rw [hre]; exact hw') ρ.2.2 hne
  have hA : ‖(ρ : ℂ) + conj w - 1‖ ^ 2 ≤ 5 * ((ρ : ℂ).re - 1 / 2) ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.add_re, Complex.conj_re, Complex.one_re,
      Complex.sub_im, Complex.add_im, Complex.conj_im, Complex.one_im, sub_zero, hre, him]
    have hu1 := hu.1
    have hu2 := hu.2
    nlinarith
  have hApos : 0 < ‖(ρ : ℂ) + conj w - 1‖ ^ 2 :=
    pow_pos (norm_pos_iff.mpr (ne_zero_of_half_lt_re (by rw [hre]; exact hw') ρ.2.2)) 2
  have hGlow : 4 * h / 5 ≤ greenKernel w ρ := by
    refine le_trans ?_ hG
    rw [hre, div_le_div_iff₀ (by norm_num) hApos]
    have hb0 : 0 < (ρ : ℂ).re - 1 / 2 := by linarith
    have e1 : 1 / 2 + h - 1 / 2 = h := by ring
    rw [e1]
    have h3 : 4 * h * ‖(ρ : ℂ) + conj w - 1‖ ^ 2 ≤ 4 * h * (5 * ((ρ : ℂ).re - 1 / 2) ^ 2) :=
      mul_le_mul_of_nonneg_left hA (by positivity)
    nlinarith [mul_pos hh hb0]
  have hge : innerField w ≥ 4 * h / 5 := by
    have hsum := hasSum_innerField (w := w) (by rw [hre]; exact hw') hu0
    have hnn : ∀ a : ZetaRightZero, 0 ≤ zeroMult a * greenKernel w a := fun a => by
      refine mul_nonneg (zeroMult_pos a).le (greenKernel_pos (by rw [hre]; exact hw') a.2.2 ?_).le
      intro he
      apply hu0
      rw [← he, zetaEntire_eq_zero_iff]
      exact a.2.1
    have hle := sum_le_hasSum ({ρ} : Finset ZetaRightZero) (fun a _ => hnn a) hsum
    rw [Finset.sum_singleton] at hle
    have hm := one_le_zeroMult ρ
    have hGpos : 0 ≤ greenKernel w ρ := le_trans hc.le hGlow
    nlinarith
  have hlt := hT' ((ρ : ℂ).im + u) (by linarith [hu.1])
  exact absurd hlt (not_lt.mpr hge)

/-- **The split through the inner field.** RH holds iff `I(σ + it) → 0` on every vertical line and zeros recur:
vanishing of the field is the zeros-approach-the-line half, recurrence the one-off half. -/
theorem riemannHypothesis_iff_tendsto_innerField_and_recurrent :
    RiemannHypothesis ↔
      (∀ h : ℝ, 0 < h → Tendsto (fun t : ℝ => innerField (((1 / 2 + h : ℝ) : ℂ) + (t : ℂ) * I)) atTop (𝓝 0)) ∧
        ZetaZeroDiscWeaklyRecurrent := by
  constructor
  · intro hRH
    refine ⟨fun h hh => ?_, fun ρ₀ hρ₀ h1 _ => ?_⟩
    · refine tendsto_const_nhds.congr fun t => ?_
      have hw : 1 / 2 < (((1 / 2 + h : ℝ) : ℂ) + (t : ℂ) * I).re := by
        simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
          Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero]
        linarith
      have h0 : zetaEntire (((1 / 2 + h : ℝ) : ℂ) + (t : ℂ) * I) ≠ 0 := fun hz =>
        (riemannHypothesis_iff_riemannZeta_ne_zero_of_half_lt_re.mp hRH) _ hw
          (zetaEntire_eq_zero_iff.mp hz)
      exact ((riemannHypothesis_iff_innerField_eq_zero hw h0).mp hRH).symm
    · exact absurd hρ₀ ((riemannHypothesis_iff_riemannZeta_ne_zero_of_half_lt_re.mp hRH) ρ₀ h1)
  · rintro ⟨hfield, hrec⟩
    rw [riemannHypothesis_iff_riemannZeta_ne_zero_of_half_lt_re]
    intro ρ₀ h1 hz
    have h2 : ρ₀.re < 1 := by
      by_contra h
      exact riemannZeta_ne_zero_of_one_le_re (not_lt.mp h) hz
    set h : ℝ := (ρ₀.re - 1 / 2) / 2 with hh
    have hh0 : 0 < h := by rw [hh]; linarith
    obtain ⟨T, hT⟩ := exists_height_bound_of_tendsto_innerField hh0 (hfield h hh0)
    obtain ⟨w, hw0, hw1, hw2, -, hw4⟩ := exists_zeta_zero_far_of_zeroDiscWeaklyRecurrent hrec hz h1 h2
      hh0 T
    have := hT ⟨w, hw0, hw2⟩ (by
      change 1 / 2 + h ≤ w.re
      have : ρ₀.re - h = 1 / 2 + h := by rw [hh]; ring
      linarith)
    exact absurd hw4 (not_le.mpr this)

end

end GaloisForLFunctions.ArithmeticInnerFunctionTheory
