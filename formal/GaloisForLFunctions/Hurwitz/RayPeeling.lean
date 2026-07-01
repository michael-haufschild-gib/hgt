/-
# Ray peeling — boundary jumps of `cpow` across the negative cut

Components for the multi-ray binomial-singularity independence closing Hurwitz Lemma 1
(route in `Hurwitz/STATUS.md`): an analytic identity `Σ_t (1−tu)^σ·P_t(u) ≡ 0` off the real
cuts kills every `P_t`, ray by ray, via the boundary JUMP across the outermost cut — the
one-sided limits of `z^σ` onto the negative axis differ by the factor
`e^{iπσ}` vs `e^{−iπσ}`, distinct for `σ ∉ ℤ`, while all inner-ray terms are continuous
across that piece of the cut.  This file provides the analytic bricks:

* `tendsto_log_cut_upper` / `tendsto_log_cut_lower` — one-sided boundary values of `log`;
* `tendsto_cpow_cut_upper` / `tendsto_cpow_cut_lower` — `(x ± iy)^σ → (−x)^σ·e^{±iπσ}`, `x < 0`;
* `jump_factor_ne` — `e^{iπσ} ≠ e^{−iπσ}` for `σ ∉ ℤ`.
-/
import GaloisForLFunctions.Hurwitz.HurwitzZeta
import Mathlib.Order.Interval.Set.Infinite
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.Deriv.Polynomial

open Complex Filter Topology

namespace HurwitzRayPeeling

/-- The vertical approach path tends to its base point. -/
theorem tendsto_base {x : ℝ} :
    Tendsto (fun y : ℝ => (x : ℂ) + y * Complex.I) (𝓝[>] 0) (𝓝 (x : ℂ)) := by
  have hc : Continuous (fun y : ℝ => (x : ℂ) + y * Complex.I) := by fun_prop
  have := hc.tendsto 0
  simp only [Complex.ofReal_zero, zero_mul, add_zero] at this
  exact this.mono_left nhdsWithin_le_nhds

/-- The norm along the vertical approach tends to `−x` for `x < 0`. -/
theorem tendsto_norm_base {x : ℝ} (hx : x < 0) :
    Tendsto (fun y : ℝ => ‖(x : ℂ) + y * Complex.I‖) (𝓝[>] 0) (𝓝 (-x)) := by
  have h := (continuous_norm.tendsto ((x : ℂ))).comp tendsto_base
  have h4 : ‖(x : ℂ)‖ = -x := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_neg hx]
  rwa [h4] at h

/-- The complex log of `x + iy` tends to `log(−x) + iπ` as `y ↓ 0`, for `x < 0`. -/
theorem tendsto_log_cut_upper {x : ℝ} (hx : x < 0) :
    Tendsto (fun y : ℝ => Complex.log ((x : ℂ) + y * Complex.I)) (𝓝[>] 0)
      (𝓝 (((Real.log (-x) : ℝ) : ℂ) + Real.pi * Complex.I)) := by
  have hnorm : Tendsto (fun y : ℝ => Real.log ‖(x : ℂ) + y * Complex.I‖) (𝓝[>] 0)
      (𝓝 (Real.log (-x))) :=
    ((Real.continuousAt_log (by linarith)).tendsto).comp (tendsto_norm_base hx)
  have harg : Tendsto (fun y : ℝ => Complex.arg ((x : ℂ) + y * Complex.I)) (𝓝[>] 0)
      (𝓝 Real.pi) := by
    have hratio : Tendsto (fun y : ℝ => y / ‖(x : ℂ) + y * Complex.I‖) (𝓝[>] 0) (𝓝 0) := by
      have hy0 : Tendsto (fun y : ℝ => y) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
        tendsto_id.mono_left nhdsWithin_le_nhds
      have := hy0.div (tendsto_norm_base hx) (by linarith : (-x : ℝ) ≠ 0)
      simpa using this
    have hratio_neg : Tendsto (fun y : ℝ => -y / ‖(x : ℂ) + y * Complex.I‖) (𝓝[>] 0)
        (𝓝 0) := by
      have := hratio.neg
      rw [neg_zero] at this
      refine this.congr fun y => ?_
      rw [neg_div]
    have harcsin := (Real.continuous_arcsin.tendsto 0).comp hratio_neg
    rw [Real.arcsin_zero] at harcsin
    have hlim := harcsin.add_const Real.pi
    rw [zero_add] at hlim
    refine hlim.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with y hy
    rw [Complex.arg_of_re_neg_of_im_nonneg (by simpa using hx) (by simpa using hy.le)]
    have him : (-((x : ℂ) + y * Complex.I)).im = -y := by simp
    rw [him]
    rfl
  have h1 : Tendsto (fun y : ℝ => ((Real.log ‖(x : ℂ) + y * Complex.I‖ : ℝ) : ℂ))
      (𝓝[>] 0) (𝓝 ((Real.log (-x) : ℝ) : ℂ)) :=
    (Complex.continuous_ofReal.tendsto _).comp hnorm
  have h2 : Tendsto (fun y : ℝ => ((Complex.arg ((x : ℂ) + y * Complex.I) : ℝ) : ℂ))
      (𝓝[>] 0) (𝓝 ((Real.pi : ℝ) : ℂ)) :=
    (Complex.continuous_ofReal.tendsto _).comp harg
  have hsum := h1.add (h2.mul_const Complex.I)
  refine hsum.congr' ?_
  filter_upwards with y
  rfl

/-- The complex log of `x − iy` tends to `log(−x) − iπ` as `y ↓ 0`, for `x < 0`. -/
theorem tendsto_log_cut_lower {x : ℝ} (hx : x < 0) :
    Tendsto (fun y : ℝ => Complex.log ((x : ℂ) - y * Complex.I)) (𝓝[>] 0)
      (𝓝 (((Real.log (-x) : ℝ) : ℂ) - Real.pi * Complex.I)) := by
  have hconj : ∀ y : ℝ, (x : ℂ) - y * Complex.I = (starRingEnd ℂ) ((x : ℂ) + y * Complex.I) := by
    intro y
    simp [Complex.ext_iff]
  have hlogconj : ∀ y : ℝ, 0 < y →
      Complex.log ((x : ℂ) - y * Complex.I)
        = (starRingEnd ℂ) (Complex.log ((x : ℂ) + y * Complex.I)) := by
    intro y hy
    have harg : ((x : ℂ) + y * Complex.I).arg ≠ Real.pi := by
      rw [Ne, Complex.arg_eq_pi_iff]
      push Not
      intro _
      have : ((x : ℂ) + y * Complex.I).im = y := by simp
      rw [this]
      linarith
    rw [hconj y]
    exact Complex.log_conj _ harg
  have hup := tendsto_log_cut_upper hx
  have hcc := (continuous_conj.tendsto _).comp hup
  have hval : (starRingEnd ℂ) (((Real.log (-x) : ℝ) : ℂ) + Real.pi * Complex.I)
      = ((Real.log (-x) : ℝ) : ℂ) - Real.pi * Complex.I := by
    rw [map_add, Complex.conj_ofReal, map_mul, Complex.conj_I]
    have : (starRingEnd ℂ) ((Real.pi : ℝ) : ℂ) = ((Real.pi : ℝ) : ℂ) := Complex.conj_ofReal _
    rw [this]
    ring
  rw [hval] at hcc
  refine hcc.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with y hy
  exact (hlogconj y hy).symm

/-- **Upper boundary value of `z^σ` on the negative cut**: `(x+iy)^σ → (−x)^σ·e^{iπσ}` as
`y ↓ 0`, for `x < 0`. -/
theorem tendsto_cpow_cut_upper {x : ℝ} (hx : x < 0) (σ : ℂ) :
    Tendsto (fun y : ℝ => ((x : ℂ) + y * Complex.I) ^ σ) (𝓝[>] 0)
      (𝓝 ((((-x : ℝ) : ℂ)) ^ σ * Complex.exp (Real.pi * Complex.I * σ))) := by
  have hne : ∀ y : ℝ, ((x : ℂ) + y * Complex.I) ≠ 0 := by
    intro y h
    have := congrArg Complex.re h
    simp at this
    linarith
  have hnex : ((-x : ℝ) : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]
    linarith
  have hlim := (Complex.continuous_exp.tendsto _).comp
    ((tendsto_log_cut_upper hx).const_mul σ)
  have hval : Complex.exp (σ * (((Real.log (-x) : ℝ) : ℂ) + Real.pi * Complex.I))
      = (((-x : ℝ) : ℂ)) ^ σ * Complex.exp (Real.pi * Complex.I * σ) := by
    calc Complex.exp (σ * (((Real.log (-x) : ℝ) : ℂ) + Real.pi * Complex.I))
        = Complex.exp (Complex.log ((-x : ℝ) : ℂ) * σ)
            * Complex.exp (Real.pi * Complex.I * σ) := by
          rw [← Complex.exp_add, ← Complex.ofReal_log (by linarith : (0:ℝ) ≤ -x)]
          congr 1
          ring
      _ = (((-x : ℝ) : ℂ)) ^ σ * Complex.exp (Real.pi * Complex.I * σ) := by
          rw [Complex.cpow_def_of_ne_zero hnex]
  rw [← hval]
  refine hlim.congr' ?_
  filter_upwards with y
  simp only [Function.comp_apply]
  rw [Complex.cpow_def_of_ne_zero (hne y)]
  congr 1
  ring

/-- **Lower boundary value of `z^σ` on the negative cut**: `(x−iy)^σ → (−x)^σ·e^{−iπσ}` as
`y ↓ 0`, for `x < 0`. -/
theorem tendsto_cpow_cut_lower {x : ℝ} (hx : x < 0) (σ : ℂ) :
    Tendsto (fun y : ℝ => ((x : ℂ) - y * Complex.I) ^ σ) (𝓝[>] 0)
      (𝓝 ((((-x : ℝ) : ℂ)) ^ σ * Complex.exp (-(Real.pi * Complex.I * σ)))) := by
  have hne : ∀ y : ℝ, ((x : ℂ) - y * Complex.I) ≠ 0 := by
    intro y h
    have := congrArg Complex.re h
    simp at this
    linarith
  have hnex : ((-x : ℝ) : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]
    linarith
  have hlim := (Complex.continuous_exp.tendsto _).comp
    ((tendsto_log_cut_lower hx).const_mul σ)
  have hval : Complex.exp (σ * (((Real.log (-x) : ℝ) : ℂ) - Real.pi * Complex.I))
      = (((-x : ℝ) : ℂ)) ^ σ * Complex.exp (-(Real.pi * Complex.I * σ)) := by
    calc Complex.exp (σ * (((Real.log (-x) : ℝ) : ℂ) - Real.pi * Complex.I))
        = Complex.exp (Complex.log ((-x : ℝ) : ℂ) * σ)
            * Complex.exp (-(Real.pi * Complex.I * σ)) := by
          rw [← Complex.exp_add, ← Complex.ofReal_log (by linarith : (0:ℝ) ≤ -x)]
          congr 1
          ring
      _ = (((-x : ℝ) : ℂ)) ^ σ * Complex.exp (-(Real.pi * Complex.I * σ)) := by
          rw [Complex.cpow_def_of_ne_zero hnex]
  rw [← hval]
  refine hlim.congr' ?_
  filter_upwards with y
  simp only [Function.comp_apply]
  rw [Complex.cpow_def_of_ne_zero (hne y)]
  congr 1
  ring

/-- **The cut jump factor is nonzero off the integers**: `e^{iπσ} ≠ e^{−iπσ}` for `σ ∉ ℤ`. -/
theorem jump_factor_ne (σ : ℂ) (hσ : ∀ k : ℤ, σ ≠ (k : ℂ)) :
    Complex.exp (Real.pi * Complex.I * σ) ≠ Complex.exp (-(Real.pi * Complex.I * σ)) := by
  intro h
  have h2 : Complex.exp (2 * (Real.pi * Complex.I * σ)) = 1 := by
    rw [two_mul, Complex.exp_add]
    nth_rewrite 2 [h]
    rw [← Complex.exp_add,
      show Real.pi * Complex.I * σ + -(Real.pi * Complex.I * σ) = 0 from by ring,
      Complex.exp_zero]
  rw [Complex.exp_eq_one_iff] at h2
  obtain ⟨k, hk⟩ := h2
  apply hσ k
  have hfac : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
      Complex.I_ne_zero
  have hrearr : (2 * (Real.pi : ℂ) * Complex.I) * σ
      = (2 * (Real.pi : ℂ) * Complex.I) * (k : ℂ) := by
    linear_combination hk
  exact mul_left_cancel₀ hfac hrearr

end HurwitzRayPeeling

namespace HurwitzRayPeeling

/-- The mirrored vertical approach path tends to its base point. -/
theorem tendsto_base_lower {x : ℝ} :
    Tendsto (fun y : ℝ => (x : ℂ) - y * Complex.I) (𝓝[>] 0) (𝓝 (x : ℂ)) := by
  have hc : Continuous (fun y : ℝ => (x : ℂ) - y * Complex.I) := by fun_prop
  have := hc.tendsto 0
  simp only [Complex.ofReal_zero, zero_mul, sub_zero] at this
  exact this.mono_left nhdsWithin_le_nhds

/-- **The one-ray peel across the cut.**  If `v^σ·p(v) + g(v) = 0` off the real axis over a set
`S` of negative abscissae, and `g` has MATCHING one-sided boundary limits `G x` from above and
below at each `x ∈ S`, then `p` vanishes on `S`: the two boundary limits of the identity give
`(−x)^σ e^{±iπσ} p(x) + G x = 0`, and the jump factor is nonzero for `σ ∉ ℤ`. -/
theorem peel_on_slit {σ : ℂ} (hσ : ∀ k : ℤ, σ ≠ (k : ℂ)) (p : Polynomial ℂ) (g : ℂ → ℂ)
    (G : ℝ → ℂ) {S : Set ℝ} (hS : ∀ x ∈ S, x < 0)
    (hgup : ∀ x ∈ S, Tendsto (fun y : ℝ => g ((x : ℂ) + y * Complex.I)) (𝓝[>] 0) (𝓝 (G x)))
    (hgdn : ∀ x ∈ S, Tendsto (fun y : ℝ => g ((x : ℂ) - y * Complex.I)) (𝓝[>] 0) (𝓝 (G x)))
    (hrel : ∀ x ∈ S, ∀ y : ℝ, y ≠ 0 →
      ((x : ℂ) + y * Complex.I) ^ σ * p.eval ((x : ℂ) + y * Complex.I)
        + g ((x : ℂ) + y * Complex.I) = 0) :
    ∀ x ∈ S, p.eval ((x : ℂ)) = 0 := by
  intro x hx
  have hxneg : x < 0 := hS x hx
  have hnex : ((-x : ℝ) : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]
    linarith
  have hpowne : (((-x : ℝ) : ℂ)) ^ σ ≠ 0 := by
    rw [Complex.cpow_def_of_ne_zero hnex]
    exact Complex.exp_ne_zero _
  -- polynomial continuity along both paths
  have hpc : Continuous fun v : ℂ => p.eval v := by
    exact p.continuous_aeval
  have hpup : Tendsto (fun y : ℝ => p.eval ((x : ℂ) + y * Complex.I)) (𝓝[>] 0)
      (𝓝 (p.eval (x : ℂ))) := (hpc.tendsto _).comp tendsto_base
  have hpdn : Tendsto (fun y : ℝ => p.eval ((x : ℂ) - y * Complex.I)) (𝓝[>] 0)
      (𝓝 (p.eval (x : ℂ))) := (hpc.tendsto _).comp tendsto_base_lower
  -- the vanishing of the expression along both paths
  have hzup : Tendsto (fun y : ℝ =>
      ((x : ℂ) + y * Complex.I) ^ σ * p.eval ((x : ℂ) + y * Complex.I)
        + g ((x : ℂ) + y * Complex.I)) (𝓝[>] 0) (𝓝 0) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact (hrel x hx y (ne_of_gt hy)).symm
  have hzdn : Tendsto (fun y : ℝ =>
      ((x : ℂ) - y * Complex.I) ^ σ * p.eval ((x : ℂ) - y * Complex.I)
        + g ((x : ℂ) - y * Complex.I)) (𝓝[>] 0) (𝓝 0) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with y hy
    have h := hrel x hx (-y) (neg_ne_zero.mpr (ne_of_gt hy))
    have hpt : (x : ℂ) + (-y : ℝ) * Complex.I = (x : ℂ) - y * Complex.I := by
      push_cast
      ring
    rw [hpt] at h
    exact h.symm
  -- boundary limits of the expression
  have hlup : Tendsto (fun y : ℝ =>
      ((x : ℂ) + y * Complex.I) ^ σ * p.eval ((x : ℂ) + y * Complex.I)
        + g ((x : ℂ) + y * Complex.I)) (𝓝[>] 0)
      (𝓝 ((((-x : ℝ) : ℂ)) ^ σ * Complex.exp (Real.pi * Complex.I * σ) * p.eval (x : ℂ)
        + G x)) :=
    ((tendsto_cpow_cut_upper hxneg σ).mul hpup).add (hgup x hx)
  have hldn : Tendsto (fun y : ℝ =>
      ((x : ℂ) - y * Complex.I) ^ σ * p.eval ((x : ℂ) - y * Complex.I)
        + g ((x : ℂ) - y * Complex.I)) (𝓝[>] 0)
      (𝓝 ((((-x : ℝ) : ℂ)) ^ σ * Complex.exp (-(Real.pi * Complex.I * σ)) * p.eval (x : ℂ)
        + G x)) :=
    ((tendsto_cpow_cut_lower hxneg σ).mul hpdn).add (hgdn x hx)
  -- limit uniqueness on both sides
  have h1 : (((-x : ℝ) : ℂ)) ^ σ * Complex.exp (Real.pi * Complex.I * σ) * p.eval (x : ℂ)
      + G x = 0 := tendsto_nhds_unique hlup hzup
  have h2 : (((-x : ℝ) : ℂ)) ^ σ * Complex.exp (-(Real.pi * Complex.I * σ)) * p.eval (x : ℂ)
      + G x = 0 := tendsto_nhds_unique hldn hzdn
  -- subtract and use the jump
  have hsub : (((-x : ℝ) : ℂ)) ^ σ * p.eval (x : ℂ)
      * (Complex.exp (Real.pi * Complex.I * σ) - Complex.exp (-(Real.pi * Complex.I * σ)))
      = 0 := by
    linear_combination h1 - h2
  have hjump : Complex.exp (Real.pi * Complex.I * σ)
      - Complex.exp (-(Real.pi * Complex.I * σ)) ≠ 0 :=
    sub_ne_zero.mpr (jump_factor_ne σ hσ)
  rcases mul_eq_zero.mp hsub with h | h
  · rcases mul_eq_zero.mp h with h' | h'
    · exact absurd h' hpowne
    · exact h'
  · exact absurd h hjump

/-- **The one-ray peel kills the polynomial** when the abscissa set is infinite. -/
theorem peel_poly_eq_zero {σ : ℂ} (hσ : ∀ k : ℤ, σ ≠ (k : ℂ)) (p : Polynomial ℂ) (g : ℂ → ℂ)
    (G : ℝ → ℂ) {S : Set ℝ} (hS : ∀ x ∈ S, x < 0) (hSinf : S.Infinite)
    (hgup : ∀ x ∈ S, Tendsto (fun y : ℝ => g ((x : ℂ) + y * Complex.I)) (𝓝[>] 0) (𝓝 (G x)))
    (hgdn : ∀ x ∈ S, Tendsto (fun y : ℝ => g ((x : ℂ) - y * Complex.I)) (𝓝[>] 0) (𝓝 (G x)))
    (hrel : ∀ x ∈ S, ∀ y : ℝ, y ≠ 0 →
      ((x : ℂ) + y * Complex.I) ^ σ * p.eval ((x : ℂ) + y * Complex.I)
        + g ((x : ℂ) + y * Complex.I) = 0) :
    p = 0 := by
  apply Polynomial.eq_zero_of_infinite_isRoot
  have himg : (Set.range (fun x : ℝ => (x : ℂ)) ∩ {v | p.IsRoot v}).Infinite := by
    have hsub : (fun x : ℝ => (x : ℂ)) '' S ⊆ Set.range (fun x : ℝ => (x : ℂ)) ∩ {v | p.IsRoot v} := by
      rintro v ⟨x, hxS, rfl⟩
      exact ⟨Set.mem_range_self x, peel_on_slit hσ p g G hS hgup hgdn hrel x hxS⟩
    exact ((hSinf.image (fun a _ b _ hab => by exact_mod_cast hab)).mono hsub)
  exact himg.mono Set.inter_subset_right

end HurwitzRayPeeling


namespace HurwitzRayPeeling

/-- The off-axis set is infinite. -/
theorem offAxis_infinite : {u : ℂ | u.im ≠ 0}.Infinite := by
  apply Set.infinite_of_injective_forall_mem
    (f := fun n : ℕ => ((n : ℝ) + 1) * Complex.I)
  · intro m n hmn
    have h := congrArg Complex.im hmn
    simp at h
    exact_mod_cast h
  · intro n
    show ((((n : ℝ) + 1) : ℂ) * Complex.I).im ≠ 0
    simp
    positivity

/-- **The multi-ray kill.**  An off-axis identity `Σ_{t ≤ T} (1 − t·u)^σ·P_t(u) = 0` with
`σ ∉ ℤ` forces every coefficient polynomial to vanish: peel the outermost ray on an interval of
its cut coordinate (all inner rays are continuous across it), then recurse. -/
theorem multiRay_eq_zero {σ : ℂ} (hσ : ∀ k : ℤ, σ ≠ (k : ℂ)) :
    ∀ (T : ℕ) (P : ℕ → Polynomial ℂ),
      (∀ u : ℂ, u.im ≠ 0 →
        ∑ t ∈ Finset.range (T + 1), (1 - (t : ℂ) * u) ^ σ * (P t).eval u = 0) →
      ∀ t ≤ T, P t = 0 := by
  intro T
  induction T with
  | zero =>
    intro P hrel t ht
    have ht0 : t = 0 := by omega
    subst ht0
    apply Polynomial.eq_zero_of_infinite_isRoot
    refine offAxis_infinite.mono ?_
    intro u hu
    have h := hrel u hu
    simpa [Finset.sum_range_one, Complex.one_cpow] using h
  | succ T ih =>
    intro P hrel t ht
    have hTpos : (0 : ℝ) < (T : ℝ) + 1 := by positivity
    have hTcne : ((T : ℂ) + 1) ≠ 0 := by
      intro h
      have := congrArg Complex.re h
      simp at this
      linarith [Nat.cast_nonneg (α := ℝ) T]
    -- the affine cut coordinate: u = (1 − v)/(T+1)
    set aff : ℂ → ℂ := fun v => (1 - v) / ((T : ℂ) + 1) with haff
    have haff_real : ∀ x : ℝ, aff (x : ℂ) = (((1 - x) / ((T : ℝ) + 1) : ℝ) : ℂ) := by
      intro x
      rw [haff]
      push_cast
      ring
    have haff_im : ∀ v : ℂ, (aff v).im = -v.im / ((T : ℝ) + 1) := by
      intro v
      show ((1 - v) / ((T : ℂ) + 1)).im = -v.im / ((T : ℝ) + 1)
      have hTr : ((T : ℂ) + 1) = ((((T : ℝ) + 1) : ℝ) : ℂ) := by push_cast; ring
      rw [hTr, div_eq_mul_inv, ← Complex.ofReal_inv, Complex.mul_im]
      have h1 : ((((((T : ℝ) + 1))⁻¹ : ℝ)) : ℂ).im = 0 := Complex.ofReal_im _
      have h2 : ((((((T : ℝ) + 1))⁻¹ : ℝ)) : ℂ).re = (((T : ℝ) + 1))⁻¹ := Complex.ofReal_re _
      rw [h1, h2]
      simp [div_eq_mul_inv]
    set pT : Polynomial ℂ := (P (T + 1)).comp (Polynomial.C (((T : ℂ) + 1)⁻¹) *
      (1 - Polynomial.X)) with hpT
    have hpT_eval : ∀ v : ℂ, pT.eval v = (P (T + 1)).eval (aff v) := by
      intro v
      rw [hpT, Polynomial.eval_comp]
      congr 1
      rw [haff]
      simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_sub,
        Polynomial.eval_one, Polynomial.eval_X]
      field_simp
    set g : ℂ → ℂ := fun v =>
      ∑ t ∈ Finset.range (T + 1), (1 - (t : ℂ) * aff v) ^ σ * (P t).eval (aff v) with hg
    set S : Set ℝ := Set.Ioo (-(1 : ℝ)/((T : ℝ) + 1)) 0 with hS
    -- interior bases are positive on S
    have hbase_pos : ∀ x ∈ S, ∀ t ∈ Finset.range (T + 1),
        0 < 1 - (t : ℝ) * ((1 - x) / ((T : ℝ) + 1)) := by
      intro x hx t htmem
      have ht' : (t : ℝ) ≤ T := by
        exact_mod_cast Nat.lt_succ_iff.mp (Finset.mem_range.mp htmem)
      obtain ⟨hx1, hx2⟩ := hx
      have hTnn : (0 : ℝ) ≤ (T : ℝ) := Nat.cast_nonneg T
      have hu_nn : (0 : ℝ) ≤ (1 - x) / ((T : ℝ) + 1) :=
        div_nonneg (by linarith) hTpos.le
      have hu_ub : (1 - x) / ((T : ℝ) + 1) ≤ ((T : ℝ) + 2) / (((T : ℝ) + 1) * ((T : ℝ) + 1)) := by
        rw [div_le_div_iff₀ hTpos (by positivity)]
        have hneg1 : -1 < x * ((T : ℝ) + 1) := by
          have := (mul_lt_mul_of_pos_right hx1 hTpos)
          have hval : -(1 : ℝ)/((T : ℝ) + 1) * ((T : ℝ) + 1) = -1 := by
            field_simp
          linarith [hval ▸ this]
        nlinarith [mul_pos hTpos (by linarith : (0:ℝ) < x * ((T : ℝ) + 1) + 1)]
      have hprod : (t : ℝ) * ((1 - x) / ((T : ℝ) + 1))
          ≤ (T : ℝ) * (((T : ℝ) + 2) / (((T : ℝ) + 1) * ((T : ℝ) + 1))) :=
        mul_le_mul ht' hu_ub hu_nn hTnn
      have hlast : (T : ℝ) * (((T : ℝ) + 2) / (((T : ℝ) + 1) * ((T : ℝ) + 1))) < 1 := by
        rw [← mul_div_assoc, div_lt_one (by positivity)]
        nlinarith
      linarith
    -- path limits of g across S (continuity of each summand)
    have hgpath : ∀ x ∈ S, ∀ path : ℝ → ℂ, Tendsto path (𝓝[>] 0) (𝓝 ((x : ℂ))) →
        Tendsto (fun y : ℝ => g (path y)) (𝓝[>] 0) (𝓝 (g ((x : ℂ)))) := by
      intro x hx path hpath
      have hterms : ∀ t ∈ Finset.range (T + 1), ContinuousAt
          (fun v => (1 - (t : ℂ) * aff v) ^ σ * (P t).eval (aff v)) ((x : ℂ)) := by
        intro t htmem
        have haffc : ContinuousAt aff ((x : ℝ) : ℂ) := by
          rw [haff]
          fun_prop
        have hbasec : ContinuousAt (fun v => 1 - (t : ℂ) * aff v) ((x : ℝ) : ℂ) := by
          exact (continuousAt_const.sub (continuousAt_const.mul haffc))
        have hslit : (1 - (t : ℂ) * aff ((x : ℝ) : ℂ)) ∈ Complex.slitPlane := by
          rw [haff_real x]
          have hpt : (1 - (t : ℂ) * (((1 - x) / ((T : ℝ) + 1) : ℝ) : ℂ))
              = ((((1 : ℝ) - (t : ℝ) * ((1 - x) / ((T : ℝ) + 1))) : ℝ) : ℂ) := by
            push_cast
            ring
          rw [hpt]
          refine Or.inl ?_
          rw [Complex.ofReal_re]
          exact hbase_pos x hx t htmem
        refine ContinuousAt.mul ?_ ?_
        · exact ContinuousAt.cpow hbasec continuousAt_const hslit
        · exact ((P t).continuous_aeval.continuousAt).comp haffc
      have hsum := tendsto_finsetSum (Finset.range (T + 1))
        (fun t htmem => ((hterms t htmem).tendsto).comp hpath)
      exact hsum
    -- the peel
    have hpeel : pT = 0 := by
      refine peel_poly_eq_zero hσ pT g (fun x => g ((x : ℝ) : ℂ))
        (S := S) (fun x hx => hx.2) (Set.Ioo_infinite (by rw [neg_div]; exact neg_lt_zero.mpr (div_pos one_pos hTpos))) ?_ ?_ ?_
      · intro x hx
        exact hgpath x hx _ tendsto_base
      · intro x hx
        exact hgpath x hx _ tendsto_base_lower
      · intro x hx y hy
        set v : ℂ := (x : ℂ) + y * Complex.I with hv
        have hvim : v.im ≠ 0 := by
          rw [hv]
          simp
          exact hy
        have huim : (aff v).im ≠ 0 := by
          rw [haff_im v]
          intro h
          rcases div_eq_zero_iff.mp h with h' | h'
          · exact hvim (by linarith [neg_eq_zero.mp h'])
          · linarith
        have hmaster := hrel (aff v) huim
        rw [Finset.sum_range_succ] at hmaster
        have hlast : (1 - ((T + 1 : ℕ) : ℂ) * aff v) = v := by
          rw [haff]
          push_cast
          field_simp
          ring
        rw [hlast] at hmaster
        have hgv : g v = ∑ t ∈ Finset.range (T + 1),
            (1 - (t : ℂ) * aff v) ^ σ * (P t).eval (aff v) := by rw [hg]
        rw [← hpT_eval v, ← hgv] at hmaster
        linear_combination hmaster
    -- the outermost polynomial dies
    have hPtop : P (T + 1) = 0 := by
      rcases Polynomial.comp_eq_zero_iff.mp (hpT ▸ hpeel) with h | ⟨_, h⟩
      · exact h
      · exfalso
        have hdeg : (Polynomial.C (((T : ℂ) + 1)⁻¹) * (1 - Polynomial.X)).natDegree = 1 := by
          rw [Polynomial.natDegree_C_mul (inv_ne_zero hTcne)]
          have : (1 - Polynomial.X : Polynomial ℂ) = -(Polynomial.X - Polynomial.C 1) := by
            rw [Polynomial.C_1]
            ring
          rw [this, Polynomial.natDegree_neg, Polynomial.natDegree_X_sub_C]
        rw [h] at hdeg
        simp at hdeg
    -- recurse on the inner rays
    have hrel' : ∀ u : ℂ, u.im ≠ 0 →
        ∑ t ∈ Finset.range (T + 1), (1 - (t : ℂ) * u) ^ σ * (P t).eval u = 0 := by
      intro u hu
      have h := hrel u hu
      rw [Finset.sum_range_succ, hPtop] at h
      simpa using h
    rcases Nat.lt_succ_iff_lt_or_eq.mp (Nat.lt_succ_of_le ht) with h | h
    · exact ih P hrel' t (Nat.lt_succ_iff.mp h)
    · rw [h]
      exact hPtop

end HurwitzRayPeeling

namespace HurwitzRayPeeling

open Polynomial

/-- Reversal of a polynomial into the compactified coordinate `u = 1/n`. -/
noncomputable def revPoly (D : ℕ) (E : Polynomial ℂ) : Polynomial ℂ :=
  ∑ k ∈ Finset.range (D + 1), Polynomial.C (E.coeff k) * Polynomial.X ^ (D - k)

/-- Coefficients of the reversal. -/
theorem revPoly_coeff (D : ℕ) (E : Polynomial ℂ) {j : ℕ} (hj : j ≤ D) :
    (revPoly D E).coeff j = E.coeff (D - j) := by
  rw [revPoly, Polynomial.finsetSum_coeff]
  rw [Finset.sum_eq_single (D - j)]
  · rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_pos (by omega), mul_one]
  · intro k hk hkne
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg ?_, mul_zero]
    have hkD : k < D + 1 := Finset.mem_range.mp hk
    omega
  · intro h
    exact absurd (Finset.mem_range.mpr (by omega)) h

/-- The reversal vanishes iff the polynomial does (degrees within `D`). -/
theorem eq_zero_of_revPoly_eq_zero {D : ℕ} {E : Polynomial ℂ} (hdeg : E.natDegree ≤ D)
    (h : revPoly D E = 0) : E = 0 := by
  ext k
  rcases le_or_gt k D with hk | hk
  · have := revPoly_coeff D E (j := D - k) (by omega)
    rw [h, Polynomial.coeff_zero] at this
    have hDk : D - (D - k) = k := by omega
    rw [hDk] at this
    simp [this.symm]
  · rw [Polynomial.coeff_zero]
    exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)

/-- Evaluation of the reversal at `1/n` recovers the polynomial value at `n`. -/
theorem revPoly_eval_inv {D : ℕ} (E : Polynomial ℂ) {n : ℂ} (hn : n ≠ 0) :
    (revPoly D E).eval n⁻¹ * n ^ D = ∑ k ∈ Finset.range (D + 1), E.coeff k * n ^ k := by
  rw [revPoly, Polynomial.eval_finsetSum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hkD : k ≤ D := by
    have := Finset.mem_range.mp hk
    omega
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  have hpow : (n⁻¹) ^ (D - k) * n ^ D = n ^ k := by
    rw [inv_pow, inv_mul_eq_div, div_eq_iff (pow_ne_zero _ hn), ← pow_add]
    congr 1
    omega
  calc E.coeff k * (n⁻¹) ^ (D - k) * n ^ D
      = E.coeff k * ((n⁻¹) ^ (D - k) * n ^ D) := by ring
    _ = E.coeff k * n ^ k := by rw [hpow]

/-- Evaluation form when the degree is within the window. -/
theorem revPoly_eval_inv' {D : ℕ} {E : Polynomial ℂ} (hdeg : E.natDegree ≤ D) {n : ℂ}
    (hn : n ≠ 0) :
    (revPoly D E).eval n⁻¹ * n ^ D = E.eval n := by
  rw [revPoly_eval_inv E hn]
  rw [Polynomial.eval_eq_sum_range' (by omega : E.natDegree < D + 1)]

end HurwitzRayPeeling


namespace HurwitzRayPeeling

open Polynomial

/-- **The compactified kill: an eventual ℕ multi-ray shifted-power relation has zero
coefficients.**  Substituting `u = 1/n`, the relation becomes the vanishing of the analytic
function `G(u) = Σ_t (1−tu)^{−s}·(revPoly D (E t))(u)` at points accumulating at `0`; the
identity theorem on the cut complement extends it off the axis, and `multiRay_eq_zero` kills
every reversal, hence every coefficient polynomial. -/
theorem multiRay_nat_relation_kill {s : ℂ} (hs : ∀ k : ℤ, s ≠ (k : ℂ)) (T D : ℕ) (hT : 1 ≤ T)
    (E : ℕ → Polynomial ℂ) (hdeg : ∀ t, (E t).natDegree ≤ D) {M : ℕ}
    (hrel : ∀ n : ℕ, M ≤ n → T < n →
      ∑ t ∈ Finset.range (T + 1), (((n - t : ℕ) : ℂ)) ^ (-s) * (E t).eval ((n : ℂ)) = 0) :
    ∀ t ≤ T, E t = 0 := by
  classical
  have hσ : ∀ k : ℤ, -s ≠ (k : ℂ) := by
    intro k h
    apply hs (-k)
    push_cast
    linear_combination -h
  set G : ℂ → ℂ := fun u =>
    ∑ t ∈ Finset.range (T + 1), (1 - (t : ℂ) * u) ^ (-s) * (revPoly D (E t)).eval u with hG
  set Ω : Set ℂ := {u : ℂ | (1 - (T : ℂ) * u) ∈ Complex.slitPlane} with hΩ
  have hTne : ((T : ℂ)) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hcuts : ∀ u ∈ Ω, ∀ t ∈ Finset.range (T + 1), (1 - (t : ℂ) * u) ∈ Complex.slitPlane := by
    intro u hu t htmem
    rcases Nat.eq_zero_or_pos t with ht0 | htpos
    · subst ht0
      simp only [Nat.cast_zero, zero_mul, sub_zero]
      exact Complex.one_mem_slitPlane
    by_contra hnot
    rw [Complex.mem_slitPlane_iff] at hnot
    push Not at hnot
    obtain ⟨hre, him⟩ := hnot
    have hre' : (1 - (t : ℂ) * u).re = 1 - (t : ℝ) * u.re := by simp
    have him' : (1 - (t : ℂ) * u).im = -((t : ℝ) * u.im) := by simp
    rw [hre'] at hre
    rw [him'] at him
    have huim : u.im = 0 := by
      have htR : ((t : ℝ)) ≠ 0 := by
        exact_mod_cast Nat.pos_iff_ne_zero.mp htpos
      rcases mul_eq_zero.mp (neg_eq_zero.mp him) with h | h
      · exact absurd h htR
      · exact h
    have htT : (t : ℝ) ≤ (T : ℝ) := by
      exact_mod_cast Nat.lt_succ_iff.mp (Finset.mem_range.mp htmem)
    have htpos' : (0 : ℝ) < (t : ℝ) := by exact_mod_cast htpos
    have hxpos : 0 < u.re := by nlinarith
    have hTx : 1 ≤ (T : ℝ) * u.re := by nlinarith
    have hbad : (1 - (T : ℂ) * u) ∉ Complex.slitPlane := by
      rw [Complex.mem_slitPlane_iff]
      push Not
      constructor
      · have h1 : (1 - (T : ℂ) * u).re = 1 - (T : ℝ) * u.re := by simp
        rw [h1]
        linarith
      · have h1 : (1 - (T : ℂ) * u).im = -((T : ℝ) * u.im) := by simp
        rw [h1, huim]
        ring
    exact hbad hu
  have hΩo : IsOpen Ω := Complex.isOpen_slitPlane.preimage (by fun_prop)
  have h0Ω : (0 : ℂ) ∈ Ω := by
    show (1 - (T : ℂ) * 0) ∈ Complex.slitPlane
    simp only [mul_zero, sub_zero]
    exact Complex.one_mem_slitPlane
  have hΩc : IsPreconnected Ω := by
    have himg : Ω = (fun w : ℂ => (1 - w) / (T : ℂ)) '' Complex.slitPlane := by
      ext u
      constructor
      · intro hu
        refine ⟨1 - (T : ℂ) * u, hu, ?_⟩
        field_simp
        ring
      · rintro ⟨w, hw, rfl⟩
        show (1 - (T : ℂ) * ((1 - w) / (T : ℂ))) ∈ Complex.slitPlane
        have hval : (1 - (T : ℂ) * ((1 - w) / (T : ℂ))) = w := by
          field_simp
          ring
        rwa [hval]
    rw [himg]
    have hpc : IsPreconnected Complex.slitPlane :=
      (Complex.starConvex_one_slitPlane.isPathConnected
        Complex.one_mem_slitPlane).isConnected.isPreconnected
    exact hpc.image _ (by fun_prop : Continuous fun w : ℂ => (1 - w) / (T : ℂ)).continuousOn
  have hGan : AnalyticOnNhd ℂ G Ω := by
    rw [hG]
    apply DifferentiableOn.analyticOnNhd _ hΩo
    apply DifferentiableOn.fun_sum
    intro t htmem u hu
    apply DifferentiableAt.differentiableWithinAt
    refine DifferentiableAt.mul ?_
      ((revPoly D (E t)).differentiable.differentiableAt)
    exact DifferentiableAt.cpow_const (by fun_prop) (hcuts u hu t htmem)
  have hGz : ∀ n : ℕ, M ≤ n → T < n → G (((n : ℂ))⁻¹) = 0 := by
    intro n hMn hTn
    have hn0 : ((n : ℂ)) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hnR0 : ((n : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    show (∑ t ∈ Finset.range (T + 1),
      (1 - (t : ℂ) * ((n : ℂ))⁻¹) ^ (-s) * (revPoly D (E t)).eval (((n : ℂ))⁻¹)) = 0
    have hterm : ∀ t ∈ Finset.range (T + 1),
        (1 - (t : ℂ) * ((n : ℂ))⁻¹) ^ (-s) * (revPoly D (E t)).eval (((n : ℂ))⁻¹)
          = (((((n : ℝ)) : ℂ)) ^ (-s))⁻¹ * ((((n : ℂ)) ^ D)⁻¹)
            * (((((n - t : ℕ)) : ℂ)) ^ (-s) * (E t).eval ((n : ℂ))) := by
      intro t htmem
      have htn : t ≤ n := by
        have := Finset.mem_range.mp htmem
        omega
      have hnt_nn : (0 : ℝ) ≤ ((n - t : ℕ) : ℝ) / (n : ℝ) := by positivity
      have hn_nn : (0 : ℝ) ≤ (n : ℝ) := by positivity
      have hsplit := mul_cpow_ofReal_nonneg hnt_nn hn_nn (-s)
      have hAB : ((((n - t : ℕ) : ℝ) / (n : ℝ) : ℝ) : ℂ) * (((n : ℝ) : ℝ) : ℂ)
          = ((n - t : ℕ) : ℂ) := by
        push_cast
        field_simp
      rw [hAB] at hsplit
      have hratio : ((((n - t : ℕ) : ℝ) / (n : ℝ) : ℝ) : ℂ) = 1 - (t : ℂ) * ((n : ℂ))⁻¹ := by
        rw [Nat.cast_sub htn]
        push_cast
        field_simp
      rw [hratio] at hsplit
      have hnpow_ne : ((((n : ℝ)) : ℂ)) ^ (-s) ≠ 0 := by
        rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hn0)]
        exact Complex.exp_ne_zero _
      have hcut : (1 - (t : ℂ) * ((n : ℂ))⁻¹) ^ (-s)
          = (((n - t : ℕ)) : ℂ) ^ (-s) * (((((n : ℝ)) : ℂ)) ^ (-s))⁻¹ := by
        rw [hsplit, mul_assoc, mul_inv_cancel₀ hnpow_ne, mul_one]
      have hrev := revPoly_eval_inv' (hdeg t) hn0
      have hrev' : (revPoly D (E t)).eval (((n : ℂ))⁻¹)
          = (E t).eval ((n : ℂ)) * ((((n : ℂ)) ^ D)⁻¹) := by
        rw [← hrev]
        field_simp
      rw [hcut, hrev']
      ring
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, hrel n hMn hTn, mul_zero]
  -- the zeros accumulate at 0
  have hfreq : ∃ᶠ u in nhdsWithin 0 {(0 : ℂ)}ᶜ, G u = 0 := by
    have hrealseq : Filter.Tendsto (fun j : ℕ => (((j + (M + T + 1) : ℕ)) : ℝ)⁻¹)
        Filter.atTop (nhds 0) :=
      tendsto_natCast_atTop_atTop.inv_tendsto_atTop.comp (tendsto_add_atTop_nat (M + T + 1))
    have hcseq : Filter.Tendsto (fun j : ℕ => (((j + (M + T + 1) : ℕ)) : ℂ)⁻¹)
        Filter.atTop (nhds 0) := by
      have h1 := (Complex.continuous_ofReal.tendsto 0).comp hrealseq
      simp only [Function.comp_def, Complex.ofReal_zero] at h1
      refine h1.congr fun j => ?_
      rw [Complex.ofReal_inv, Complex.ofReal_natCast]
    have htend : Filter.Tendsto (fun j : ℕ => (((j + (M + T + 1) : ℕ)) : ℂ)⁻¹)
        Filter.atTop (nhdsWithin 0 {(0 : ℂ)}ᶜ) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨hcseq, Filter.Eventually.of_forall fun j => ?_⟩
      have hne : (((j + (M + T + 1) : ℕ)) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff, inv_eq_zero]
      exact hne
    exact htend.frequently ((Filter.Eventually.of_forall fun j =>
      hGz (j + (M + T + 1)) (by omega) (by omega)).frequently)
  -- identity theorem, off-axis restriction, and the kill
  have hGeq : Set.EqOn G 0 Ω :=
    hGan.eqOn_zero_of_preconnected_of_frequently_eq_zero hΩc h0Ω hfreq
  have hoff : ∀ u : ℂ, u.im ≠ 0 →
      ∑ t ∈ Finset.range (T + 1), (1 - (t : ℂ) * u) ^ (-s) * (revPoly D (E t)).eval u = 0 := by
    intro u hu
    have huΩ : u ∈ Ω := by
      show (1 - (T : ℂ) * u) ∈ Complex.slitPlane
      refine Or.inr ?_
      have h1 : (1 - (T : ℂ) * u).im = -((T : ℝ) * u.im) := by simp
      rw [h1]
      intro h
      rcases mul_eq_zero.mp (neg_eq_zero.mp h) with h' | h'
      · exact absurd h' (Nat.cast_ne_zero.mpr (by omega))
      · exact hu h'
    have := hGeq huΩ
    simpa [hG] using this
  have hrev0 := multiRay_eq_zero hσ T (fun t => revPoly D (E t)) hoff
  intro t ht
  exact eq_zero_of_revPoly_eq_zero (hdeg t) (hrev0 t ht)

end HurwitzRayPeeling
