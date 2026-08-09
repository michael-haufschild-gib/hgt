import Mathlib

/-!
# Hadamard's lemma and smooth division by the coordinate

A smooth function vanishing at the origin is the coordinate times a smooth function.  The
Hadamard quotient is realized by the averaging operator

`(A_k G)(s) = ∫₀¹ t^k G(t s) dt`,

which preserves every finite order of differentiability: its derivative is `A_{k+1}(G')`.  Applying
it to the derivative of a smooth `h` gives `h(s) = h(0) + s · (A_0 h')(s)`.

As a consequence the exponential defect `e^{-Vs} − 1` factors as `s` times a smooth function which
is nowhere zero for `V > 0`, so division by it stays inside the smooth functions.  This is the
algebraic engine behind the classification of the fixed distributions of the multiplication
semigroup.
-/

namespace GaloisForLFunctions.HTGeometry.Interfinity

open MeasureTheory Set Filter Topology intervalIntegral

noncomputable section

/-- Smoothness of every finite order. -/
def IsSmoothReal (h : ℝ → ℝ) : Prop := ∀ n : ℕ, ContDiff ℝ n h

namespace IsSmoothReal

theorem continuous {h : ℝ → ℝ} (hh : IsSmoothReal h) : Continuous h := (hh 0).continuous

theorem differentiable {h : ℝ → ℝ} (hh : IsSmoothReal h) : Differentiable ℝ h :=
  (hh 1).differentiable (by norm_num)

theorem derivSmooth {h : ℝ → ℝ} (hh : IsSmoothReal h) : IsSmoothReal (deriv h) := by
  intro n
  have hn : ContDiff ℝ ((n : WithTop ℕ∞) + 1) h := by exact_mod_cast hh (n + 1)
  exact (contDiff_succ_iff_deriv.1 hn).2.2

theorem mul {h g : ℝ → ℝ} (hh : IsSmoothReal h) (hg : IsSmoothReal g) :
    IsSmoothReal (fun s => h s * g s) := fun n => (hh n).mul (hg n)

theorem div {h g : ℝ → ℝ} (hh : IsSmoothReal h) (hg : IsSmoothReal g) (hne : ∀ s, g s ≠ 0) :
    IsSmoothReal (fun s => h s / g s) := fun n => (hh n).div (hg n) hne

theorem neg {h : ℝ → ℝ} (hh : IsSmoothReal h) : IsSmoothReal (fun s => -h s) := fun n => (hh n).neg

end IsSmoothReal

theorem isSmoothReal_const (r : ℝ) : IsSmoothReal (fun _ : ℝ => r) := fun _ => contDiff_const

theorem isSmoothReal_id : IsSmoothReal (fun s : ℝ => s) := fun _ => contDiff_id

/-! ## The Hadamard averaging operator -/

/-- The Hadamard averaging operator `(A_k G)(s) = ∫₀¹ t^k G(t s) dt`. -/
def hadamardAvg (k : ℕ) (G : ℝ → ℝ) (s : ℝ) : ℝ := ∫ t in (0 : ℝ)..1, t ^ k * G (t * s)

theorem continuous_hadamardAvg (k : ℕ) {G : ℝ → ℝ} (hG : Continuous G) :
    Continuous (hadamardAvg k G) := by
  refine continuous_parametric_intervalIntegral_of_continuous ?_ continuous_const
  exact (continuous_snd.pow k).mul (hG.comp (continuous_snd.mul continuous_fst))

/-- The derivative of the Hadamard average raises the weight and differentiates the integrand. -/
theorem hasDerivAt_hadamardAvg (k : ℕ) {G : ℝ → ℝ} (hG : ContDiff ℝ 1 G) (s : ℝ) :
    HasDerivAt (hadamardAvg k G) (hadamardAvg (k + 1) (deriv G) s) s := by
  set R : ℝ := |s| + 1 with hRdef
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := -R) (b := R)).exists_bound_of_continuousOn
    (hG.continuous_deriv le_rfl).continuousOn
  have hGderiv : ∀ x : ℝ, HasDerivAt G (deriv G x) x := fun x =>
    (hG.differentiable (by norm_num) x).hasDerivAt
  have hstep : ∀ t x : ℝ, HasDerivAt (fun y : ℝ => t ^ k * G (t * y))
      (t ^ (k + 1) * deriv G (t * x)) x := by
    intro t x
    have hinner : HasDerivAt (fun y : ℝ => t * y) t x := by
      simpa using (hasDerivAt_id x).const_mul t
    have hcomp : HasDerivAt (fun y : ℝ => G (t * y)) (deriv G (t * x) * t) x :=
      (hGderiv (t * x)).comp x hinner
    have hmul := hcomp.const_mul (t ^ k)
    have heq : t ^ k * (deriv G (t * x) * t) = t ^ (k + 1) * deriv G (t * x) := by ring
    rwa [heq] at hmul
  have hmemR : ∀ t ∈ Ioc (0 : ℝ) 1, ∀ x ∈ Metric.ball s 1, t * x ∈ Icc (-R) R := by
    intro t ht x hx
    have hdist : |x - s| < 1 := by simpa [Real.dist_eq] using hx
    have hxle : |x| ≤ R := by
      have := abs_sub_abs_le_abs_sub x s
      rw [hRdef]
      linarith
    have ht0 : 0 ≤ t := ht.1.le
    have ht1 : t ≤ 1 := ht.2
    have habs : |t * x| ≤ R := by
      rw [abs_mul, abs_of_nonneg ht0]
      nlinarith [abs_nonneg x]
    exact abs_le.1 habs
  have hlip : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ uIoc (0 : ℝ) 1 →
      LipschitzOnWith (Real.nnabs M) (fun x : ℝ => t ^ k * G (t * x)) (Metric.ball s 1) := by
    filter_upwards with t ht
    rw [uIoc_of_le zero_le_one] at ht
    refine (convex_ball s 1).lipschitzOnWith_of_nnnorm_deriv_le
      (fun x _ => (hstep t x).differentiableAt) fun x hx => ?_
    rw [(hstep t x).deriv]
    have hb : ‖deriv G (t * x)‖ ≤ M := hM (t * x) (hmemR t ht x hx)
    have hM0 : 0 ≤ M := le_trans (norm_nonneg _) hb
    have ht0 : 0 ≤ t := ht.1.le
    have ht1 : t ≤ 1 := ht.2
    have htk : |t ^ (k + 1)| ≤ 1 := by
      rw [abs_pow, abs_of_nonneg ht0]
      exact pow_le_one₀ ht0 ht1
    have hbound : ‖t ^ (k + 1) * deriv G (t * x)‖ ≤ M := by
      rw [Real.norm_eq_abs, abs_mul]
      calc |t ^ (k + 1)| * |deriv G (t * x)| ≤ 1 * M := by
            refine mul_le_mul htk ?_ (abs_nonneg _) zero_le_one
            simpa [Real.norm_eq_abs] using hb
        _ = M := one_mul _
    rw [← NNReal.coe_le_coe]
    simpa [Real.coe_nnabs, abs_of_nonneg hM0] using hbound
  have hres := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_lip
    (F := fun (x : ℝ) (t : ℝ) => t ^ k * G (t * x))
    (F' := fun t : ℝ => t ^ (k + 1) * deriv G (t * s))
    (bound := fun _ => M) (s := Metric.ball s 1) (Metric.ball_mem_nhds s one_pos)
    (Eventually.of_forall fun x => ((continuous_id.pow k).mul
      (hG.continuous.comp (continuous_id.mul continuous_const))).aestronglyMeasurable)
    (((continuous_id.pow k).mul (hG.continuous.comp
      (continuous_id.mul continuous_const))).intervalIntegrable _ _)
    (((continuous_id.pow (k + 1)).mul ((hG.continuous_deriv le_rfl).comp
      (continuous_id.mul continuous_const))).aestronglyMeasurable)
    hlip intervalIntegrable_const
    (by filter_upwards with t _ using hstep t s)
  exact hres.2

theorem contDiff_hadamardAvg : ∀ (n k : ℕ) {G : ℝ → ℝ}, ContDiff ℝ n G →
    ContDiff ℝ n (hadamardAvg k G)
  | 0, k, G, hG => by
      have hG0 : ContDiff ℝ (0 : WithTop ℕ∞) G := by exact_mod_cast hG
      have hres : ContDiff ℝ (0 : WithTop ℕ∞) (hadamardAvg k G) :=
        contDiff_zero.2 (continuous_hadamardAvg k (contDiff_zero.1 hG0))
      exact_mod_cast hres
  | (n + 1), k, G, hG => by
      have hG1 : ContDiff ℝ 1 G := hG.of_le (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n))
      have hderiv : deriv (hadamardAvg k G) = hadamardAvg (k + 1) (deriv G) := by
        funext x
        exact (hasDerivAt_hadamardAvg k hG1 x).deriv
      have hGcast : ContDiff ℝ ((n : WithTop ℕ∞) + 1) G := by exact_mod_cast hG
      have hGd : ContDiff ℝ n (deriv G) := (contDiff_succ_iff_deriv.1 hGcast).2.2
      have hmain : ContDiff ℝ ((n : WithTop ℕ∞) + 1) (hadamardAvg k G) := by
        rw [contDiff_succ_iff_deriv]
        refine ⟨fun x => (hasDerivAt_hadamardAvg k hG1 x).differentiableAt, ?_, ?_⟩
        · intro hcon
          exact absurd hcon (by simp)
        · rw [hderiv]
          exact contDiff_hadamardAvg n (k + 1) hGd
      exact_mod_cast hmain

theorem isSmoothReal_hadamardAvg (k : ℕ) {G : ℝ → ℝ} (hG : IsSmoothReal G) :
    IsSmoothReal (hadamardAvg k G) := fun n => contDiff_hadamardAvg n k (hG n)

/-! ## Hadamard's lemma -/

/-- **Hadamard's lemma.**  A smooth function is its value at the origin plus the coordinate times
the Hadamard average of its derivative. -/
theorem hadamard_eq {h : ℝ → ℝ} (hh : IsSmoothReal h) (s : ℝ) :
    h s = h 0 + s * hadamardAvg 0 (deriv h) s := by
  have hchain : ∀ t : ℝ, HasDerivAt (fun u : ℝ => h (u * s)) (deriv h (t * s) * s) t := by
    intro t
    have hinner : HasDerivAt (fun u : ℝ => u * s) s t := by
      simpa using (hasDerivAt_id t).mul_const s
    exact (hh.differentiable (t * s)).hasDerivAt.comp t hinner
  have hderivEq : (deriv fun u : ℝ => h (u * s)) = fun t => deriv h (t * s) * s := by
    funext t
    exact (hchain t).deriv
  have hcont : Continuous fun t : ℝ => deriv h (t * s) * s :=
    ((hh.derivSmooth.continuous).comp (continuous_id.mul continuous_const)).mul continuous_const
  have hint : IntervalIntegrable (deriv fun u : ℝ => h (u * s)) volume 0 1 := by
    rw [hderivEq]
    exact hcont.intervalIntegrable _ _
  have hFTC : (∫ t in (0 : ℝ)..1, deriv (fun u : ℝ => h (u * s)) t) = h (1 * s) - h (0 * s) :=
    integral_deriv_eq_sub (fun x _ => (hchain x).differentiableAt) hint
  rw [hderivEq] at hFTC
  have hAvg : s * hadamardAvg 0 (deriv h) s = ∫ t in (0 : ℝ)..1, deriv h (t * s) * s := by
    rw [hadamardAvg, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun t _ => ?_
    simp only [pow_zero, one_mul]
    ring
  rw [hAvg, hFTC]
  simp

theorem hadamard_factor {h : ℝ → ℝ} (hh : IsSmoothReal h) :
    ∃ r : ℝ → ℝ, IsSmoothReal r ∧ ∀ s : ℝ, h s = h 0 + s * r s :=
  ⟨hadamardAvg 0 (deriv h), isSmoothReal_hadamardAvg 0 hh.derivSmooth, hadamard_eq hh⟩

/-! ## Smooth division by the exponential defect -/

theorem isSmoothReal_expNeg (V : ℝ) : IsSmoothReal fun s : ℝ => Real.exp (-(V * s)) := fun _ =>
  Real.contDiff_exp.comp (by fun_prop)

/-- The smooth cofactor of the exponential defect. -/
def expDefectFactor (V : ℝ) : ℝ → ℝ :=
  hadamardAvg 0 (deriv fun s : ℝ => Real.exp (-(V * s)))

theorem isSmoothReal_expDefectFactor (V : ℝ) : IsSmoothReal (expDefectFactor V) :=
  isSmoothReal_hadamardAvg 0 (isSmoothReal_expNeg V).derivSmooth

/-- **The exponential defect factors through the coordinate.** -/
theorem laplace_defect_factor (V s : ℝ) :
    Real.exp (-(V * s)) - 1 = s * expDefectFactor V s := by
  have h := hadamard_eq (isSmoothReal_expNeg V) s
  simp only [mul_zero, neg_zero, Real.exp_zero] at h
  rw [expDefectFactor]
  linarith

end

end GaloisForLFunctions.HTGeometry.Interfinity
