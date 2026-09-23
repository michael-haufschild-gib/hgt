/-
The root-trace holonomy: ONE invariant of an annulus member — the endpoint ratio
of any continuous square-root trace along one interior circle — with TWO
computations of different type.

Order-linked: the holonomy equals the deck class of the slit-chart roots, hence
`(−1)^{total enclosed order}` for enclosed configurations — it consumes the
interior data.  Spectral: the holonomy is read by boundary pairings — the
double-period pairing of the extended trace against a finitely-periodic probe is
`(1 + holonomy)` times the single-period pairing, so odd holonomy makes the trace
orthogonal to EVERY periodic probe, while even holonomy pairs against its own
conjugate with strictly positive mass — it consumes circle integrals only.
Parity of the enclosed order thus becomes positivity of a boundary L²
functional.

The trace is built from the two slit-chart roots directly: the right-chart root
on the arc through the right port, switched at the top port to the
constant-adjusted left-chart root; the holonomy is then the ratio of the two
port ratios — the deck class on the nose.  No path lifting, no covering theory,
no argument principle.
-/
import GaloisForLFunctions.RHTower.CanonicalBranch

noncomputable section

namespace RHTower

open Complex Metric Set

/-! ### §1 The circle in the slit charts -/

theorem circleMap_sub_center_re (a : ℂ) (r θ : ℝ) :
    (circleMap a r θ - a).re = r * Real.cos θ := by
  simp [circleMap, Complex.exp_mul_I, Complex.mul_re, ← Complex.ofReal_cos,
    ← Complex.ofReal_sin]

theorem circleMap_sub_center_im (a : ℂ) (r θ : ℝ) :
    (circleMap a r θ - a).im = r * Real.sin θ := by
  simp [circleMap, Complex.exp_mul_I, Complex.mul_im, ← Complex.ofReal_cos,
    ← Complex.ofReal_sin]

theorem norm_circleMap_sub_center (a : ℂ) {r : ℝ} (hr : 0 < r) (θ : ℝ) :
    ‖circleMap a r θ - a‖ = r := by
  simp [circleMap, abs_of_pos hr]

theorem circleMap_pi_div_two (a : ℂ) (r : ℝ) :
    circleMap a r (Real.pi / 2) = a + (r : ℂ) * I := by
  rw [circleMap, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
    Real.cos_pi_div_two, Real.sin_pi_div_two]
  push_cast
  ring

theorem circleMap_neg_pi_div_two (a : ℂ) (r : ℝ) :
    circleMap a r (-(Real.pi / 2)) = a - (r : ℂ) * I := by
  rw [circleMap, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
    Real.cos_neg, Real.sin_neg, Real.cos_pi_div_two, Real.sin_pi_div_two]
  push_cast
  ring

theorem circleMap_three_pi_div_two (a : ℂ) (r : ℝ) :
    circleMap a r (3 * Real.pi / 2) = a - (r : ℂ) * I := by
  rw [circleMap, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
    show (3 * Real.pi / 2 : ℝ) = Real.pi + Real.pi / 2 by ring,
    Real.cos_add, Real.sin_add, Real.cos_pi, Real.sin_pi,
    Real.cos_pi_div_two, Real.sin_pi_div_two]
  push_cast
  ring

/-- The interior circle lies in the annulus. -/
theorem circleMap_mem_annulus {a : ℂ} {r₀ r R : ℝ} (h0 : 0 ≤ r₀) (hr₀ : r₀ < r)
    (hrR : r < R) (θ : ℝ) :
    circleMap a r θ ∈ ball a R \ closedBall a r₀ := by
  have hr : 0 < r := lt_of_le_of_lt h0 hr₀
  constructor
  · rw [mem_ball, dist_eq_norm, norm_circleMap_sub_center a hr]
    exact hrR
  · intro hmem
    rw [mem_closedBall, dist_eq_norm, norm_circleMap_sub_center a hr] at hmem
    exact absurd hmem (not_le.mpr hr₀)

/-- The right arc of the circle lies in the right slit chart. -/
theorem circleMap_mem_chartRA {a : ℂ} {r₀ r R : ℝ} (h0 : 0 ≤ r₀) (hr₀ : r₀ < r)
    (hrR : r < R) {θ : ℝ} (hθ : θ ∈ Icc (-(Real.pi / 2)) (Real.pi / 2)) :
    circleMap a r θ ∈ chartRA a r₀ R := by
  have hr : 0 < r := lt_of_le_of_lt h0 hr₀
  refine ⟨?_, circleMap_mem_annulus h0 hr₀ hrR θ⟩
  show circleMap a r θ - a ∈ Complex.slitPlane
  rw [Complex.mem_slitPlane_iff, circleMap_sub_center_re, circleMap_sub_center_im]
  have hcos : 0 ≤ Real.cos θ := Real.cos_nonneg_of_mem_Icc hθ
  rcases hcos.lt_or_eq with h | h
  · exact Or.inl (mul_pos hr h)
  · right
    have hpyth := Real.sin_sq_add_cos_sq θ
    rw [← h] at hpyth
    norm_num at hpyth
    intro hzero
    rcases mul_eq_zero.mp hzero with h' | h'
    · exact hr.ne' h'
    · rw [h'] at hpyth
      norm_num at hpyth

/-- The left arc of the circle lies in the left slit chart. -/
theorem circleMap_mem_chartLA {a : ℂ} {r₀ r R : ℝ} (h0 : 0 ≤ r₀) (hr₀ : r₀ < r)
    (hrR : r < R) {θ : ℝ} (hθ : θ ∈ Icc (Real.pi / 2) (3 * Real.pi / 2)) :
    circleMap a r θ ∈ chartLA a r₀ R := by
  have hr : 0 < r := lt_of_le_of_lt h0 hr₀
  refine ⟨?_, circleMap_mem_annulus h0 hr₀ hrR θ⟩
  show a - circleMap a r θ ∈ Complex.slitPlane
  have hre : (a - circleMap a r θ).re = -(r * Real.cos θ) := by
    rw [show a - circleMap a r θ = -(circleMap a r θ - a) by ring, Complex.neg_re,
      circleMap_sub_center_re]
  have him : (a - circleMap a r θ).im = -(r * Real.sin θ) := by
    rw [show a - circleMap a r θ = -(circleMap a r θ - a) by ring, Complex.neg_im,
      circleMap_sub_center_im]
  rw [Complex.mem_slitPlane_iff, hre, him]
  have hcos : Real.cos θ ≤ 0 :=
    Real.cos_nonpos_of_pi_div_two_le_of_le hθ.1 (by linarith [hθ.2, Real.pi_pos])
  rcases hcos.lt_or_eq with h | h
  · left
    have : 0 < r * (-Real.cos θ) := mul_pos hr (by linarith)
    linarith [this]
  · right
    have hpyth := Real.sin_sq_add_cos_sq θ
    rw [h] at hpyth
    norm_num at hpyth
    intro hzero
    have hs : r * Real.sin θ = 0 := by linarith [neg_eq_zero.mp hzero]
    rcases mul_eq_zero.mp hs with h' | h'
    · exact hr.ne' h'
    · rw [h'] at hpyth
      norm_num at hpyth

/-- The top port lies in both slit charts. -/
theorem top_port_mem_charts {a : ℂ} {r₀ r R : ℝ} (h0 : 0 ≤ r₀) (hr₀ : r₀ < r)
    (hrR : r < R) :
    a + (r : ℂ) * I ∈ chartRA a r₀ R ∧ a + (r : ℂ) * I ∈ chartLA a r₀ R := by
  have h := circleMap_mem_chartRA (a := a) h0 hr₀ hrR
    (θ := Real.pi / 2) ⟨by linarith [Real.pi_pos], le_refl _⟩
  have h' := circleMap_mem_chartLA (a := a) h0 hr₀ hrR
    (θ := Real.pi / 2) ⟨le_refl _, by linarith [Real.pi_pos]⟩
  rw [circleMap_pi_div_two] at h h'
  exact ⟨h, h'⟩

/-- The bottom port lies in both slit charts. -/
theorem bottom_port_mem_charts {a : ℂ} {r₀ r R : ℝ} (h0 : 0 ≤ r₀) (hr₀ : r₀ < r)
    (hrR : r < R) :
    a - (r : ℂ) * I ∈ chartRA a r₀ R ∧ a - (r : ℂ) * I ∈ chartLA a r₀ R := by
  have h := circleMap_mem_chartRA (a := a) h0 hr₀ hrR
    (θ := -(Real.pi / 2)) ⟨le_refl _, by linarith [Real.pi_pos]⟩
  have h' := circleMap_mem_chartLA (a := a) h0 hr₀ hrR
    (θ := 3 * Real.pi / 2) ⟨by linarith [Real.pi_pos], le_refl _⟩
  rw [circleMap_neg_pi_div_two] at h
  rw [circleMap_three_pi_div_two] at h'
  exact ⟨h, h'⟩

/-! ### §2 The root trace along the circle and its holonomy -/

/-- The one-period square-root trace along the interior circle: the right-chart
root on the arc through the right port, switched at the top port to the
constant-adjusted left-chart root. -/
noncomputable def rootTrace (G₁ G₂ : ℂ → ℂ) (a : ℂ) (r : ℝ) : ℝ → ℂ := fun θ =>
  if θ ≤ Real.pi / 2 then G₁ (circleMap a r θ)
  else G₁ (a + (r : ℂ) * I) / G₂ (a + (r : ℂ) * I) * G₂ (circleMap a r θ)

theorem rootTrace_left (G₁ G₂ : ℂ → ℂ) (a : ℂ) (r : ℝ) :
    rootTrace G₁ G₂ a r (-(Real.pi / 2)) = G₁ (a - (r : ℂ) * I) := by
  have hπ := Real.pi_pos
  show (if -(Real.pi / 2) ≤ Real.pi / 2 then _ else _) = _
  rw [if_pos (by linarith), circleMap_neg_pi_div_two]

theorem rootTrace_right (G₁ G₂ : ℂ → ℂ) (a : ℂ) (r : ℝ) :
    rootTrace G₁ G₂ a r (3 * Real.pi / 2)
      = G₁ (a + (r : ℂ) * I) / G₂ (a + (r : ℂ) * I) * G₂ (a - (r : ℂ) * I) := by
  have hπ := Real.pi_pos
  show (if 3 * Real.pi / 2 ≤ Real.pi / 2 then _ else _) = _
  rw [if_neg (by push Not; linarith), circleMap_three_pi_div_two]

/-- The trace is continuous across one full period. -/
theorem rootTrace_continuousOn {G₁ G₂ : ℂ → ℂ} {a : ℂ} {r₀ r R : ℝ}
    (h0 : 0 ≤ r₀) (hr₀ : r₀ < r) (hrR : r < R)
    (hG₁ : AnalyticOnNhd ℂ G₁ (chartRA a r₀ R))
    (hG₂ : AnalyticOnNhd ℂ G₂ (chartLA a r₀ R))
    (hG₂T : G₂ (a + (r : ℂ) * I) ≠ 0) :
    ContinuousOn (rootTrace G₁ G₂ a r)
      (Icc (-(Real.pi / 2)) (3 * Real.pi / 2)) := by
  have hπ := Real.pi_pos
  apply ContinuousOn.if
  · intro θ hθ
    have hfr : θ = Real.pi / 2 := by
      have h := hθ.2
      rw [show {x : ℝ | x ≤ Real.pi / 2} = Iic (Real.pi / 2) from rfl,
        frontier_Iic] at h
      exact h
    subst hfr
    rw [circleMap_pi_div_two, div_mul_cancel₀ _ hG₂T]
  · have hsub : Icc (-(Real.pi / 2)) (3 * Real.pi / 2) ∩
        closure {x : ℝ | x ≤ Real.pi / 2} ⊆ Icc (-(Real.pi / 2)) (Real.pi / 2) := by
      intro θ hθ
      have h2 : θ ∈ Iic (Real.pi / 2) := by
        have := hθ.2
        rwa [show {x : ℝ | x ≤ Real.pi / 2} = Iic (Real.pi / 2) from rfl,
          (isClosed_Iic).closure_eq] at this
      exact ⟨hθ.1.1, h2⟩
    refine ContinuousOn.mono ?_ hsub
    exact (hG₁.continuousOn.comp (continuous_circleMap a r).continuousOn
      fun θ hθ => circleMap_mem_chartRA h0 hr₀ hrR hθ)
  · have hsub : Icc (-(Real.pi / 2)) (3 * Real.pi / 2) ∩
        closure {x : ℝ | ¬x ≤ Real.pi / 2} ⊆ Icc (Real.pi / 2) (3 * Real.pi / 2) := by
      intro θ hθ
      have hset : {x : ℝ | ¬x ≤ Real.pi / 2} = Ioi (Real.pi / 2) := by
        ext x
        simp [not_le]
      have h2 : θ ∈ Ici (Real.pi / 2) := by
        have := hθ.2
        rwa [hset, closure_Ioi] at this
      exact ⟨h2, hθ.1.2⟩
    refine ContinuousOn.mono ?_ hsub
    exact continuousOn_const.mul
      (hG₂.continuousOn.comp (continuous_circleMap a r).continuousOn
        fun θ hθ => circleMap_mem_chartLA h0 hr₀ hrR hθ)

/-- The trace squares to the member along the whole period. -/
theorem rootTrace_sq {f G₁ G₂ : ℂ → ℂ} {a : ℂ} {r₀ r R : ℝ}
    (h0 : 0 ≤ r₀) (hr₀ : r₀ < r) (hrR : r < R)
    (hpG₁ : ∀ z ∈ chartRA a r₀ R, G₁ z ^ (2 : ℕ) = f z)
    (hpG₂ : ∀ z ∈ chartLA a r₀ R, G₂ z ^ (2 : ℕ) = f z)
    (hfT : f (a + (r : ℂ) * I) ≠ 0) :
    ∀ θ ∈ Icc (-(Real.pi / 2)) (3 * Real.pi / 2),
      rootTrace G₁ G₂ a r θ ^ (2 : ℕ) = f (circleMap a r θ) := by
  have hπ := Real.pi_pos
  intro θ hθ
  show (if θ ≤ Real.pi / 2 then _ else _) ^ (2 : ℕ) = _
  by_cases hcase : θ ≤ Real.pi / 2
  · rw [if_pos hcase]
    exact hpG₁ _ (circleMap_mem_chartRA h0 hr₀ hrR ⟨hθ.1, hcase⟩)
  · rw [if_neg hcase]
    have hεsq : (G₁ (a + (r : ℂ) * I) / G₂ (a + (r : ℂ) * I)) ^ (2 : ℕ) = 1 := by
      rw [div_pow, hpG₁ _ (top_port_mem_charts h0 hr₀ hrR).1,
        hpG₂ _ (top_port_mem_charts h0 hr₀ hrR).2, div_self hfT]
    rw [mul_pow, hεsq, one_mul]
    exact hpG₂ _ (circleMap_mem_chartLA h0 hr₀ hrR
      ⟨le_of_not_ge (fun h => hcase h), hθ.2⟩)

/-- **The holonomy identity**: the endpoint ratio of the trace is the deck class
at the circle's own vertical ports — by construction, with no continuation. -/
theorem rootTrace_holonomy {G₁ G₂ : ℂ → ℂ} {a : ℂ} {r : ℝ}
    (hG₂T : G₂ (a + (r : ℂ) * I) ≠ 0) (hG₁B : G₁ (a - (r : ℂ) * I) ≠ 0)
    (hG₂B : G₂ (a - (r : ℂ) * I) ≠ 0) :
    rootTrace G₁ G₂ a r (3 * Real.pi / 2)
      = deckClass G₁ G₂ (a + (r : ℂ) * I) (a - (r : ℂ) * I)
        * rootTrace G₁ G₂ a r (-(Real.pi / 2)) := by
  rw [rootTrace_left, rootTrace_right, deckClass]
  field_simp

/-! ### §3 Rigidity: every continuous trace carries the same holonomy -/

/-- A continuous function into `{1, −1}` is constant on a preconnected set. -/
theorem apply_eq_of_continuousOn_pm_one {q : ℝ → ℂ} {s : Set ℝ}
    (hs : IsPreconnected s) (hq : ContinuousOn q s)
    (hpm : ∀ x ∈ s, q x = 1 ∨ q x = -1) {x y : ℝ} (hx : x ∈ s) (hy : y ∈ s) :
    q x = q y := by
  by_contra hne
  have hre : ContinuousOn (fun t => (q t).re) s :=
    Complex.continuous_re.comp_continuousOn hq
  have key : ∀ u v : ℝ, u ∈ s → v ∈ s → q u = 1 → q v = -1 → False := by
    intro u v hu hv h1 h2
    have hmem : (0 : ℝ) ∈ Icc ((fun t => (q t).re) v) ((fun t => (q t).re) u) := by
      show (0 : ℝ) ∈ Icc (q v).re (q u).re
      rw [h1, h2]
      norm_num [Complex.one_re, Complex.neg_re]
    obtain ⟨t, hts, h0⟩ := hs.intermediate_value hv hu hre hmem
    have h0' : (q t).re = 0 := h0
    rcases hpm t hts with h' | h' <;> rw [h'] at h0' <;> norm_num at h0'
  rcases hpm x hx with h1 | h1 <;> rcases hpm y hy with h2 | h2
  · exact hne (by rw [h1, h2])
  · exact key x y hx hy h1 h2
  · exact key y x hy hx h2 h1
  · exact hne (by rw [h1, h2])

/-- **The invariant is well-defined**: EVERY continuous one-period square-root
trace along the circle has endpoint ratio equal to the deck class — the
holonomy does not depend on the chosen trace. -/
theorem continuous_trace_holonomy {f G₁ G₂ : ℂ → ℂ} {a : ℂ} {r₀ r R : ℝ}
    (h0 : 0 ≤ r₀) (hr₀ : r₀ < r) (hrR : r < R)
    (hG₁ : AnalyticOnNhd ℂ G₁ (chartRA a r₀ R))
    (hG₂ : AnalyticOnNhd ℂ G₂ (chartLA a r₀ R))
    (hpG₁ : ∀ z ∈ chartRA a r₀ R, G₁ z ^ (2 : ℕ) = f z)
    (hpG₂ : ∀ z ∈ chartLA a r₀ R, G₂ z ^ (2 : ℕ) = f z)
    (hf0 : ∀ z ∈ ball a R \ closedBall a r₀, f z ≠ 0)
    {U : ℝ → ℂ}
    (hUc : ContinuousOn U (Icc (-(Real.pi / 2)) (3 * Real.pi / 2)))
    (hUsq : ∀ θ ∈ Icc (-(Real.pi / 2)) (3 * Real.pi / 2),
      U θ ^ (2 : ℕ) = f (circleMap a r θ)) :
    U (3 * Real.pi / 2)
      = deckClass G₁ G₂ (a + (r : ℂ) * I) (a - (r : ℂ) * I)
        * U (-(Real.pi / 2)) := by
  have hπ := Real.pi_pos
  have hmemIcc : ∀ θ : ℝ, θ ∈ Icc (-(Real.pi / 2)) (3 * Real.pi / 2) →
      f (circleMap a r θ) ≠ 0 := fun θ _ =>
    hf0 _ (circleMap_mem_annulus h0 hr₀ hrR θ)
  have hfT : f (a + (r : ℂ) * I) ≠ 0 := by
    have := hf0 _ ((top_port_mem_charts h0 hr₀ hrR).1.2)
    exact this
  have hfB : f (a - (r : ℂ) * I) ≠ 0 := by
    have := hf0 _ ((bottom_port_mem_charts h0 hr₀ hrR).1.2)
    exact this
  have hG₂T : G₂ (a + (r : ℂ) * I) ≠ 0 := fun h => hfT (by
    rw [← hpG₂ _ (top_port_mem_charts h0 hr₀ hrR).2, h]; ring)
  have hG₁B : G₁ (a - (r : ℂ) * I) ≠ 0 := fun h => hfB (by
    rw [← hpG₁ _ (bottom_port_mem_charts h0 hr₀ hrR).1, h]; ring)
  have hG₂B : G₂ (a - (r : ℂ) * I) ≠ 0 := fun h => hfB (by
    rw [← hpG₂ _ (bottom_port_mem_charts h0 hr₀ hrR).2, h]; ring)
  have hSsq := rootTrace_sq h0 hr₀ hrR hpG₁ hpG₂ hfT
  have hS0 : ∀ θ ∈ Icc (-(Real.pi / 2)) (3 * Real.pi / 2),
      rootTrace G₁ G₂ a r θ ≠ 0 := by
    intro θ hθ h
    have := hSsq θ hθ
    rw [h] at this
    exact hmemIcc θ hθ (by rw [← this]; ring)
  have hScont := rootTrace_continuousOn h0 hr₀ hrR hG₁ hG₂ hG₂T
  have hq_cont : ContinuousOn (fun θ => U θ / rootTrace G₁ G₂ a r θ)
      (Icc (-(Real.pi / 2)) (3 * Real.pi / 2)) := hUc.div hScont hS0
  have hq_pm : ∀ θ ∈ Icc (-(Real.pi / 2)) (3 * Real.pi / 2),
      U θ / rootTrace G₁ G₂ a r θ = 1 ∨ U θ / rootTrace G₁ G₂ a r θ = -1 := by
    intro θ hθ
    have hsq1 : (U θ / rootTrace G₁ G₂ a r θ) ^ (2 : ℕ) = 1 := by
      rw [div_pow, hUsq θ hθ, hSsq θ hθ, div_self (hmemIcc θ hθ)]
    have hfac : (U θ / rootTrace G₁ G₂ a r θ - 1)
        * (U θ / rootTrace G₁ G₂ a r θ + 1) = 0 := by
      linear_combination hsq1
    rcases mul_eq_zero.mp hfac with h | h
    · exact Or.inl (sub_eq_zero.mp h)
    · exact Or.inr (eq_neg_of_add_eq_zero_left h)
  have hstart : -(Real.pi / 2) ∈ Icc (-(Real.pi / 2)) (3 * Real.pi / 2) :=
    ⟨le_refl _, by linarith⟩
  have hend : 3 * Real.pi / 2 ∈ Icc (-(Real.pi / 2)) (3 * Real.pi / 2) :=
    ⟨by linarith, le_refl _⟩
  have hconst := apply_eq_of_continuousOn_pm_one isPreconnected_Icc hq_cont hq_pm
    hend hstart
  have hUe : U (3 * Real.pi / 2)
      = U (-(Real.pi / 2)) / rootTrace G₁ G₂ a r (-(Real.pi / 2))
        * rootTrace G₁ G₂ a r (3 * Real.pi / 2) := by
    have h1 : U (3 * Real.pi / 2) / rootTrace G₁ G₂ a r (3 * Real.pi / 2)
        = U (-(Real.pi / 2)) / rootTrace G₁ G₂ a r (-(Real.pi / 2)) := hconst
    rw [← h1, div_mul_cancel₀ _ (hS0 _ hend)]
  rw [hUe, rootTrace_holonomy hG₂T hG₁B hG₂B]
  field_simp [hS0 _ hstart]

/-! ### §4 Computation 1 — the order side -/

theorem exp_two_pi_I_nat_div_two (N : ℕ) :
    Complex.exp (2 * (Real.pi : ℂ) * I * (N : ℂ) / 2) = (-1) ^ N := by
  rw [show 2 * (Real.pi : ℂ) * I * (N : ℂ) / 2
      = (N : ℂ) * ((Real.pi : ℂ) * I) by ring,
    Complex.exp_nat_mul, Complex.exp_pi_mul_I]

/-- A vertical point above the hole lies in the top overlap. -/
theorem vertical_mem_overlapTop {a : ℂ} {r₀ R c : ℝ} (h0 : 0 ≤ r₀) (hc : r₀ < c)
    (hcR : c < R) : a + (c : ℂ) * I ∈ overlapTop a r₀ R := by
  have hcpos : 0 < c := lt_of_le_of_lt h0 hc
  have hmem := circleMap_mem_annulus (a := a) h0 hc hcR (Real.pi / 2)
  rw [circleMap_pi_div_two] at hmem
  refine ⟨?_, hmem⟩
  show 0 < (a + (c : ℂ) * I - a).im
  rw [show a + (c : ℂ) * I - a = (c : ℂ) * I by ring, Complex.mul_im]
  simpa using hcpos

/-- A vertical point below the hole lies in the bottom overlap. -/
theorem vertical_mem_overlapBot {a : ℂ} {r₀ R c : ℝ} (h0 : 0 ≤ r₀) (hc : r₀ < c)
    (hcR : c < R) : a - (c : ℂ) * I ∈ overlapBot a r₀ R := by
  have hcpos : 0 < c := lt_of_le_of_lt h0 hc
  have hmem := circleMap_mem_annulus (a := a) h0 hc hcR (-(Real.pi / 2))
  rw [circleMap_neg_pi_div_two] at hmem
  refine ⟨?_, hmem⟩
  show (a - (c : ℂ) * I - a).im < 0
  rw [show a - (c : ℂ) * I - a = -((c : ℂ) * I) by ring, Complex.neg_im,
    Complex.mul_im]
  simpa using hcpos

/-- The deck class is the same at every pair of vertical ports: the port ratios
are constant on each overlap component. -/
theorem deckClass_vertical_port_indep {f G₁ G₂ : ℂ → ℂ} {a : ℂ} {r₀ R c c' : ℝ}
    (h0 : 0 ≤ r₀) (hc : r₀ < c) (hcR : c < R) (hc' : r₀ < c') (hc'R : c' < R)
    (hG₁ : AnalyticOnNhd ℂ G₁ (chartRA a r₀ R))
    (hG₂ : AnalyticOnNhd ℂ G₂ (chartLA a r₀ R))
    (hpG₁ : ∀ z ∈ chartRA a r₀ R, G₁ z ^ (2 : ℕ) = f z)
    (hpG₂ : ∀ z ∈ chartLA a r₀ R, G₂ z ^ (2 : ℕ) = f z)
    (hf0 : ∀ z ∈ ball a R \ closedBall a r₀, f z ≠ 0) :
    deckClass G₁ G₂ (a + (c : ℂ) * I) (a - (c : ℂ) * I)
      = deckClass G₁ G₂ (a + (c' : ℂ) * I) (a - (c' : ℂ) * I) := by
  have hfT : f (a + (c : ℂ) * I) ≠ 0 :=
    hf0 _ (vertical_mem_overlapTop h0 hc hcR).2
  have hfB : f (a - (c : ℂ) * I) ≠ 0 :=
    hf0 _ (vertical_mem_overlapBot h0 hc hcR).2
  have hfT' : f (a + (c' : ℂ) * I) ≠ 0 :=
    hf0 _ (vertical_mem_overlapTop h0 hc' hc'R).2
  have hfB' : f (a - (c' : ℂ) * I) ≠ 0 :=
    hf0 _ (vertical_mem_overlapBot h0 hc' hc'R).2
  have hG₂T' : G₂ (a + (c' : ℂ) * I) ≠ 0 := fun h => hfT' (by
    rw [← hpG₂ _ (top_port_mem_charts h0 hc' hc'R).2, h]; ring)
  have hG₂B' : G₂ (a - (c' : ℂ) * I) ≠ 0 := fun h => hfB' (by
    rw [← hpG₂ _ (bottom_port_mem_charts h0 hc' hc'R).2, h]; ring)
  obtain ⟨-, hEqT⟩ := pow_root_ratio (by norm_num : (0 : ℕ) < 2)
    (isOpen_overlapTop a r₀ R) (isPreconnected_overlapTop a h0)
    (fun z hz => hG₁ z (overlapTop_subset_chartRA a r₀ R hz))
    (fun z hz => hG₂ z (overlapTop_subset_chartLA a r₀ R hz))
    (fun z hz => hpG₁ z (overlapTop_subset_chartRA a r₀ R hz))
    (fun z hz => hpG₂ z (overlapTop_subset_chartLA a r₀ R hz))
    (vertical_mem_overlapTop h0 hc hcR) hfT
  obtain ⟨-, hEqB⟩ := pow_root_ratio (by norm_num : (0 : ℕ) < 2)
    (isOpen_overlapBot a r₀ R) (isPreconnected_overlapBot a h0)
    (fun z hz => hG₁ z (overlapBot_subset_chartRA a r₀ R hz))
    (fun z hz => hG₂ z (overlapBot_subset_chartLA a r₀ R hz))
    (fun z hz => hpG₁ z (overlapBot_subset_chartRA a r₀ R hz))
    (fun z hz => hpG₂ z (overlapBot_subset_chartLA a r₀ R hz))
    (vertical_mem_overlapBot h0 hc hcR) hfB
  have hT' : G₁ (a + (c' : ℂ) * I)
      = G₁ (a + (c : ℂ) * I) / G₂ (a + (c : ℂ) * I) * G₂ (a + (c' : ℂ) * I) :=
    hEqT (vertical_mem_overlapTop h0 hc' hc'R)
  have hB' : G₁ (a - (c' : ℂ) * I)
      = G₁ (a - (c : ℂ) * I) / G₂ (a - (c : ℂ) * I) * G₂ (a - (c' : ℂ) * I) :=
    hEqB (vertical_mem_overlapBot h0 hc' hc'R)
  have hratioT : G₁ (a + (c' : ℂ) * I) / G₂ (a + (c' : ℂ) * I)
      = G₁ (a + (c : ℂ) * I) / G₂ (a + (c : ℂ) * I) := by
    rw [hT', mul_div_cancel_right₀ _ hG₂T']
  have hratioB : G₁ (a - (c' : ℂ) * I) / G₂ (a - (c' : ℂ) * I)
      = G₁ (a - (c : ℂ) * I) / G₂ (a - (c : ℂ) * I) := by
    rw [hB', mul_div_cancel_right₀ _ hG₂B']
  rw [deckClass, deckClass, hratioT, hratioB]

/-- An enclosed configuration is nonvanishing on the annulus. -/
theorem enclosed_ne_zero_on_annulus' {ι : Type*} {s : Finset ι} {ρc : ι → ℂ}
    {m : ι → ℕ} {f h : ℂ → ℂ} {a : ℂ} {r₀ R : ℝ}
    (hρ : ∀ i ∈ s, ‖ρc i - a‖ ≤ r₀)
    (hh0 : ∀ z ∈ ball a R, h z ≠ 0)
    (hfact : ∀ z ∈ ball a R, f z = (∏ i ∈ s, (z - ρc i) ^ m i) * h z) :
    ∀ z ∈ ball a R \ closedBall a r₀, f z ≠ 0 := by
  intro z hz
  have hzb : z ∈ ball a R := hz.1
  have hzfar : r₀ < ‖z - a‖ := by
    have := hz.2
    rwa [mem_closedBall, dist_eq_norm, not_le] at this
  rw [hfact z hzb]
  refine mul_ne_zero ?_ (hh0 z hzb)
  rw [Finset.prod_ne_zero_iff]
  intro i hi
  apply pow_ne_zero
  rw [sub_ne_zero]
  intro heq
  exact absurd (hρ i hi) (not_le.mpr (heq ▸ hzfar))

/-- **Computation 1 — the order side of the invariant**: for an enclosed
configuration the holonomy of every continuous circle trace is the parity of
the total enclosed order.  This computation consumes the interior data. -/
theorem continuous_trace_holonomy_neg_one_pow {ι : Type*} (s : Finset ι)
    (ρc : ι → ℂ) (m : ι → ℕ) {f h G₁ G₂ : ℂ → ℂ} {a : ℂ} {r₀ r R : ℝ}
    (h0 : 0 ≤ r₀) (hr₀ : r₀ < r) (hrR : r < R)
    (hρ : ∀ i ∈ s, ‖ρc i - a‖ ≤ r₀)
    (hh : AnalyticOnNhd ℂ h (ball a R)) (hh0 : ∀ z ∈ ball a R, h z ≠ 0)
    (hfact : ∀ z ∈ ball a R, f z = (∏ i ∈ s, (z - ρc i) ^ m i) * h z)
    (hG₁ : AnalyticOnNhd ℂ G₁ (chartRA a r₀ R))
    (hG₂ : AnalyticOnNhd ℂ G₂ (chartLA a r₀ R))
    (hpG₁ : ∀ z ∈ chartRA a r₀ R, G₁ z ^ (2 : ℕ) = f z)
    (hpG₂ : ∀ z ∈ chartLA a r₀ R, G₂ z ^ (2 : ℕ) = f z)
    {U : ℝ → ℂ}
    (hUc : ContinuousOn U (Icc (-(Real.pi / 2)) (3 * Real.pi / 2)))
    (hUsq : ∀ θ ∈ Icc (-(Real.pi / 2)) (3 * Real.pi / 2),
      U θ ^ (2 : ℕ) = f (circleMap a r θ)) :
    U (3 * Real.pi / 2) = (-1) ^ (∑ i ∈ s, m i) * U (-(Real.pi / 2)) := by
  have hrR' : r₀ < R := lt_trans hr₀ hrR
  have hf0 := enclosed_ne_zero_on_annulus' hρ hh0 hfact
  rw [continuous_trace_holonomy h0 hr₀ hrR hG₁ hG₂ hpG₁ hpG₂ hf0 hUc hUsq]
  congr 1
  rw [deckClass_vertical_port_indep h0 hr₀ hrR
    (show r₀ < (r₀ + R) / 2 by linarith) (show (r₀ + R) / 2 < R by linarith)
    hG₁ hG₂ hpG₁ hpG₂ hf0,
    deckClass_multi_zero s ρc m h0 hrR' (by norm_num : (0 : ℕ) < 2) hρ hh hh0
      hfact hG₁ hG₂ hpG₁ hpG₂,
    show (∑ i ∈ s, ((m i : ℕ) : ℂ)) = ((∑ i ∈ s, m i : ℕ) : ℂ) by push_cast; ring]
  exact_mod_cast exp_two_pi_I_nat_div_two (∑ i ∈ s, m i)

/-! ### §5 Computation 2 — the spectral side: periodic probes read the holonomy -/

/-- The doubled trace: the one-period trace extended to a second period by the
holonomy factor. -/
noncomputable def doubledTrace (σ : ℂ) (U : ℝ → ℂ) : ℝ → ℂ := fun θ =>
  if θ ≤ 3 * Real.pi / 2 then U θ else σ * U (θ - 2 * Real.pi)

theorem doubledTrace_continuousOn {σ : ℂ} {U : ℝ → ℂ}
    (hUc : ContinuousOn U (Icc (-(Real.pi / 2)) (3 * Real.pi / 2)))
    (hhol : U (3 * Real.pi / 2) = σ * U (-(Real.pi / 2))) :
    ContinuousOn (doubledTrace σ U)
      (Icc (-(Real.pi / 2)) (3 * Real.pi / 2 + 2 * Real.pi)) := by
  have hπ := Real.pi_pos
  apply ContinuousOn.if
  · intro θ hθ
    have hfr : θ = 3 * Real.pi / 2 := by
      have h := hθ.2
      rw [show {x : ℝ | x ≤ 3 * Real.pi / 2} = Iic (3 * Real.pi / 2) from rfl,
        frontier_Iic] at h
      exact h
    subst hfr
    rw [show 3 * Real.pi / 2 - 2 * Real.pi = -(Real.pi / 2) by ring]
    exact hhol
  · refine ContinuousOn.mono hUc ?_
    intro θ hθ
    have h2 : θ ∈ Iic (3 * Real.pi / 2) := by
      have := hθ.2
      rwa [show {x : ℝ | x ≤ 3 * Real.pi / 2} = Iic (3 * Real.pi / 2) from rfl,
        isClosed_Iic.closure_eq] at this
    exact ⟨hθ.1.1, h2⟩
  · have hcomp : ContinuousOn (fun θ : ℝ => σ * U (θ - 2 * Real.pi))
        (Icc (3 * Real.pi / 2) (3 * Real.pi / 2 + 2 * Real.pi)) := by
      refine continuousOn_const.mul ?_
      refine hUc.comp (continuous_id.sub continuous_const).continuousOn ?_
      intro θ hθ
      constructor
      · have := hθ.1
        linarith
      · have := hθ.2
        linarith
    refine ContinuousOn.mono hcomp ?_
    intro θ hθ
    have hset : {x : ℝ | ¬x ≤ 3 * Real.pi / 2} = Ioi (3 * Real.pi / 2) := by
      ext x
      simp [not_le]
    have h2 : θ ∈ Ici (3 * Real.pi / 2) := by
      have := hθ.2
      rwa [hset, closure_Ioi] at this
    exact ⟨h2, hθ.1.2⟩

/-- **The pairing identity — the spectral computation of the invariant**: the
double-period pairing of the doubled trace against a finitely-periodic probe is
`(1 + holonomy)` times the single-period pairing.  This computation consumes
circle integrals only. -/
theorem doubledTrace_pairing {σ : ℂ} {U p : ℝ → ℂ}
    (hUc : ContinuousOn U (Icc (-(Real.pi / 2)) (3 * Real.pi / 2)))
    (hhol : U (3 * Real.pi / 2) = σ * U (-(Real.pi / 2)))
    (hp : ContinuousOn p (Icc (-(Real.pi / 2)) (3 * Real.pi / 2 + 2 * Real.pi)))
    (hper : ∀ θ ∈ Icc (-(Real.pi / 2)) (3 * Real.pi / 2),
      p (θ + 2 * Real.pi) = p θ) :
    ∫ θ in (-(Real.pi / 2))..(3 * Real.pi / 2 + 2 * Real.pi),
        doubledTrace σ U θ * p θ
      = (1 + σ) * ∫ θ in (-(Real.pi / 2))..(3 * Real.pi / 2), U θ * p θ := by
  have hπ := Real.pi_pos
  have hle1 : -(Real.pi / 2) ≤ 3 * Real.pi / 2 := by linarith
  have hle2 : (3 * Real.pi / 2 : ℝ) ≤ 3 * Real.pi / 2 + 2 * Real.pi := by linarith
  have huIcc1 : uIcc (-(Real.pi / 2)) (3 * Real.pi / 2)
      = Icc (-(Real.pi / 2)) (3 * Real.pi / 2) := uIcc_of_le hle1
  have huIcc2 : uIcc (3 * Real.pi / 2) (3 * Real.pi / 2 + 2 * Real.pi)
      = Icc (3 * Real.pi / 2) (3 * Real.pi / 2 + 2 * Real.pi) := uIcc_of_le hle2
  have hIccsub1 : Icc (-(Real.pi / 2)) (3 * Real.pi / 2)
      ⊆ Icc (-(Real.pi / 2)) (3 * Real.pi / 2 + 2 * Real.pi) := fun θ hθ =>
    ⟨hθ.1, by linarith [hθ.2]⟩
  have hIccsub2 : Icc (3 * Real.pi / 2) (3 * Real.pi / 2 + 2 * Real.pi)
      ⊆ Icc (-(Real.pi / 2)) (3 * Real.pi / 2 + 2 * Real.pi) := fun θ hθ =>
    ⟨by linarith [hθ.1], hθ.2⟩
  have hdc := doubledTrace_continuousOn hUc hhol
  have hEq1 : EqOn (fun θ => doubledTrace σ U θ * p θ) (fun θ => U θ * p θ)
      (uIcc (-(Real.pi / 2)) (3 * Real.pi / 2)) := by
    rw [huIcc1]
    intro θ hθ
    show (if θ ≤ 3 * Real.pi / 2 then U θ else σ * U (θ - 2 * Real.pi)) * p θ
      = U θ * p θ
    rw [if_pos hθ.2]
  have hEq2 : EqOn (fun θ => doubledTrace σ U θ * p θ)
      (fun θ => σ * (U (θ - 2 * Real.pi) * p (θ - 2 * Real.pi)))
      (uIcc (3 * Real.pi / 2) (3 * Real.pi / 2 + 2 * Real.pi)) := by
    rw [huIcc2]
    intro θ hθ
    show (if θ ≤ 3 * Real.pi / 2 then U θ else σ * U (θ - 2 * Real.pi)) * p θ
      = σ * (U (θ - 2 * Real.pi) * p (θ - 2 * Real.pi))
    have hpθ : p θ = p (θ - 2 * Real.pi) := by
      have h := hper (θ - 2 * Real.pi) ⟨by linarith [hθ.1], by linarith [hθ.2]⟩
      rw [show θ - 2 * Real.pi + 2 * Real.pi = θ by ring] at h
      exact h
    by_cases hcase : θ ≤ 3 * Real.pi / 2
    · have hθeq : θ = 3 * Real.pi / 2 := le_antisymm hcase hθ.1
      subst hθeq
      rw [if_pos hcase, hhol, hpθ,
        show 3 * Real.pi / 2 - 2 * Real.pi = -(Real.pi / 2) by ring]
      ring
    · rw [if_neg hcase, hpθ]
      ring
  have hi1 : IntervalIntegrable (fun θ => doubledTrace σ U θ * p θ)
      MeasureTheory.volume (-(Real.pi / 2)) (3 * Real.pi / 2) := by
    apply ContinuousOn.intervalIntegrable
    rw [huIcc1]
    exact (hdc.mono hIccsub1).mul (hp.mono hIccsub1)
  have hi2 : IntervalIntegrable (fun θ => doubledTrace σ U θ * p θ)
      MeasureTheory.volume (3 * Real.pi / 2) (3 * Real.pi / 2 + 2 * Real.pi) := by
    apply ContinuousOn.intervalIntegrable
    rw [huIcc2]
    exact (hdc.mono hIccsub2).mul (hp.mono hIccsub2)
  rw [← intervalIntegral.integral_add_adjacent_intervals hi1 hi2,
    intervalIntegral.integral_congr hEq1, intervalIntegral.integral_congr hEq2,
    intervalIntegral.integral_const_mul]
  have hshift : (∫ θ in (3 * Real.pi / 2)..(3 * Real.pi / 2 + 2 * Real.pi),
      U (θ - 2 * Real.pi) * p (θ - 2 * Real.pi))
      = ∫ θ in (-(Real.pi / 2))..(3 * Real.pi / 2), U θ * p θ := by
    simp only [sub_eq_add_neg]
    rw [intervalIntegral.integral_comp_add_right
      (fun θ => U θ * p θ) (-(2 * Real.pi)),
      show 3 * Real.pi / 2 + -(2 * Real.pi) = -(Real.pi / 2) by ring,
      show 3 * Real.pi / 2 + 2 * Real.pi + -(2 * Real.pi) = 3 * Real.pi / 2
        by ring]
  rw [hshift]
  ring

/-- **Odd holonomy is orthogonal to every periodic voice**: when the trace
returns with a sign flip, its doubled trace annihilates every finitely-periodic
probe. -/
theorem doubledTrace_pairing_eq_zero {U p : ℝ → ℂ}
    (hUc : ContinuousOn U (Icc (-(Real.pi / 2)) (3 * Real.pi / 2)))
    (hhol : U (3 * Real.pi / 2) = -U (-(Real.pi / 2)))
    (hp : ContinuousOn p (Icc (-(Real.pi / 2)) (3 * Real.pi / 2 + 2 * Real.pi)))
    (hper : ∀ θ ∈ Icc (-(Real.pi / 2)) (3 * Real.pi / 2),
      p (θ + 2 * Real.pi) = p θ) :
    ∫ θ in (-(Real.pi / 2))..(3 * Real.pi / 2 + 2 * Real.pi),
        doubledTrace (-1) U θ * p θ = 0 := by
  rw [doubledTrace_pairing hUc (by rw [neg_one_mul]; exact hhol) hp hper]
  norm_num

/-- **Even holonomy has strictly positive periodic mass**: the conjugated
doubled trace is itself an admissible periodic probe, and the pairing against
it is twice the single-period `L²` mass — nonzero. -/
theorem exists_periodic_probe_pairing_ne_zero {U : ℝ → ℂ}
    (hUc : ContinuousOn U (Icc (-(Real.pi / 2)) (3 * Real.pi / 2)))
    (hhol : U (3 * Real.pi / 2) = U (-(Real.pi / 2)))
    (hU0 : ∀ θ ∈ Icc (-(Real.pi / 2)) (3 * Real.pi / 2), U θ ≠ 0) :
    ∃ p : ℝ → ℂ,
      ContinuousOn p (Icc (-(Real.pi / 2)) (3 * Real.pi / 2 + 2 * Real.pi)) ∧
      (∀ θ ∈ Icc (-(Real.pi / 2)) (3 * Real.pi / 2),
        p (θ + 2 * Real.pi) = p θ) ∧
      ∫ θ in (-(Real.pi / 2))..(3 * Real.pi / 2 + 2 * Real.pi),
        doubledTrace 1 U θ * p θ ≠ 0 := by
  have hπ := Real.pi_pos
  have hhol1 : U (3 * Real.pi / 2) = (1 : ℂ) * U (-(Real.pi / 2)) := by
    rw [one_mul]
    exact hhol
  have hdc := doubledTrace_continuousOn hUc hhol1
  have hpcont : ContinuousOn (fun θ => (starRingEnd ℂ) (doubledTrace 1 U θ))
      (Icc (-(Real.pi / 2)) (3 * Real.pi / 2 + 2 * Real.pi)) :=
    Complex.continuous_conj.comp_continuousOn hdc
  have hpper : ∀ θ ∈ Icc (-(Real.pi / 2)) (3 * Real.pi / 2),
      (fun θ => (starRingEnd ℂ) (doubledTrace 1 U θ)) (θ + 2 * Real.pi)
        = (fun θ => (starRingEnd ℂ) (doubledTrace 1 U θ)) θ := by
    intro θ hθ
    have hval : doubledTrace 1 U (θ + 2 * Real.pi) = doubledTrace 1 U θ := by
      show (if θ + 2 * Real.pi ≤ 3 * Real.pi / 2 then U (θ + 2 * Real.pi)
          else 1 * U (θ + 2 * Real.pi - 2 * Real.pi))
        = if θ ≤ 3 * Real.pi / 2 then U θ else 1 * U (θ - 2 * Real.pi)
      rw [if_pos hθ.2]
      by_cases hc : θ + 2 * Real.pi ≤ 3 * Real.pi / 2
      · have hθeq : θ = -(Real.pi / 2) := le_antisymm (by linarith) hθ.1
        subst hθeq
        rw [if_pos hc, show -(Real.pi / 2) + 2 * Real.pi = 3 * Real.pi / 2
          by ring, hhol]
      · rw [if_neg hc, one_mul,
          show θ + 2 * Real.pi - 2 * Real.pi = θ by ring]
    show (starRingEnd ℂ) (doubledTrace 1 U (θ + 2 * Real.pi))
      = (starRingEnd ℂ) (doubledTrace 1 U θ)
    rw [hval]
  refine ⟨fun θ => (starRingEnd ℂ) (doubledTrace 1 U θ), hpcont, hpper, ?_⟩
  rw [doubledTrace_pairing hUc hhol1 hpcont hpper]
  have hmass : (∫ θ in (-(Real.pi / 2))..(3 * Real.pi / 2),
      U θ * (fun θ => (starRingEnd ℂ) (doubledTrace 1 U θ)) θ)
      = ((∫ θ in (-(Real.pi / 2))..(3 * Real.pi / 2),
          Complex.normSq (U θ) : ℝ) : ℂ) := by
    rw [← intervalIntegral.integral_ofReal]
    apply intervalIntegral.integral_congr
    intro θ hθ
    rw [uIcc_of_le (by linarith : -(Real.pi / 2) ≤ 3 * Real.pi / 2)] at hθ
    show U θ * (starRingEnd ℂ) (doubledTrace 1 U θ)
      = ((Complex.normSq (U θ) : ℝ) : ℂ)
    have hval : doubledTrace 1 U θ = U θ := by
      show (if θ ≤ 3 * Real.pi / 2 then U θ else _) = U θ
      rw [if_pos hθ.2]
    rw [hval, Complex.mul_conj]
  rw [hmass]
  have hpos : 0 < ∫ θ in (-(Real.pi / 2))..(3 * Real.pi / 2),
      Complex.normSq (U θ) := by
    apply intervalIntegral.intervalIntegral_pos_of_pos_on
    · apply ContinuousOn.intervalIntegrable
      rw [uIcc_of_le (by linarith : -(Real.pi / 2) ≤ 3 * Real.pi / 2)]
      exact Complex.continuous_normSq.comp_continuousOn hUc
    · intro θ hθ
      exact Complex.normSq_pos.mpr
        (hU0 θ ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩)
    · linarith
  intro hzero
  rw [mul_eq_zero] at hzero
  rcases hzero with h | h
  · norm_num at h
  · rw [Complex.ofReal_eq_zero] at h
    exact absurd h (ne_of_gt hpos)

/-! ### §6 The capstone: one invariant, two computations, non-vacuous agreement -/

/-- **The parity–spectrum dichotomy**: for a member with an enclosed
configuration and any continuous square-root trace along an interior circle,
EITHER the total enclosed order is even, the trace closes up, and its doubled
trace pairs strictly nontrivially against an explicit periodic probe — OR the
total order is odd, the trace returns with a sign flip, and its doubled trace
annihilates every finitely-periodic probe.  The order computation consumes the
interior configuration; the spectral computation consumes circle integrals
only: one invariant, two computations, non-vacuous agreement. -/
theorem trace_parity_spectral_dichotomy {ι : Type*} (s : Finset ι)
    (ρc : ι → ℂ) (m : ι → ℕ) {f h G₁ G₂ : ℂ → ℂ} {a : ℂ} {r₀ r R : ℝ}
    (h0 : 0 ≤ r₀) (hr₀ : r₀ < r) (hrR : r < R)
    (hρ : ∀ i ∈ s, ‖ρc i - a‖ ≤ r₀)
    (hh : AnalyticOnNhd ℂ h (ball a R)) (hh0 : ∀ z ∈ ball a R, h z ≠ 0)
    (hfact : ∀ z ∈ ball a R, f z = (∏ i ∈ s, (z - ρc i) ^ m i) * h z)
    (hG₁ : AnalyticOnNhd ℂ G₁ (chartRA a r₀ R))
    (hG₂ : AnalyticOnNhd ℂ G₂ (chartLA a r₀ R))
    (hpG₁ : ∀ z ∈ chartRA a r₀ R, G₁ z ^ (2 : ℕ) = f z)
    (hpG₂ : ∀ z ∈ chartLA a r₀ R, G₂ z ^ (2 : ℕ) = f z)
    {U : ℝ → ℂ}
    (hUc : ContinuousOn U (Icc (-(Real.pi / 2)) (3 * Real.pi / 2)))
    (hUsq : ∀ θ ∈ Icc (-(Real.pi / 2)) (3 * Real.pi / 2),
      U θ ^ (2 : ℕ) = f (circleMap a r θ)) :
    (Even (∑ i ∈ s, m i) ∧ U (3 * Real.pi / 2) = U (-(Real.pi / 2)) ∧
      ∃ p : ℝ → ℂ,
        ContinuousOn p (Icc (-(Real.pi / 2)) (3 * Real.pi / 2 + 2 * Real.pi)) ∧
        (∀ θ ∈ Icc (-(Real.pi / 2)) (3 * Real.pi / 2),
          p (θ + 2 * Real.pi) = p θ) ∧
        ∫ θ in (-(Real.pi / 2))..(3 * Real.pi / 2 + 2 * Real.pi),
          doubledTrace 1 U θ * p θ ≠ 0)
    ∨ (Odd (∑ i ∈ s, m i) ∧ U (3 * Real.pi / 2) = -U (-(Real.pi / 2)) ∧
      ∀ p : ℝ → ℂ,
        ContinuousOn p (Icc (-(Real.pi / 2)) (3 * Real.pi / 2 + 2 * Real.pi)) →
        (∀ θ ∈ Icc (-(Real.pi / 2)) (3 * Real.pi / 2),
          p (θ + 2 * Real.pi) = p θ) →
        ∫ θ in (-(Real.pi / 2))..(3 * Real.pi / 2 + 2 * Real.pi),
          doubledTrace (-1) U θ * p θ = 0) := by
  have hhol := continuous_trace_holonomy_neg_one_pow s ρc m h0 hr₀ hrR hρ hh hh0
    hfact hG₁ hG₂ hpG₁ hpG₂ hUc hUsq
  have hf0 := enclosed_ne_zero_on_annulus' hρ hh0 hfact
  have hU0 : ∀ θ ∈ Icc (-(Real.pi / 2)) (3 * Real.pi / 2), U θ ≠ 0 := by
    intro θ hθ hzero
    have := hUsq θ hθ
    rw [hzero] at this
    exact hf0 _ (circleMap_mem_annulus h0 hr₀ hrR θ) (by rw [← this]; ring)
  rcases Nat.even_or_odd (∑ i ∈ s, m i) with he | ho
  · left
    have hhol1 : U (3 * Real.pi / 2) = U (-(Real.pi / 2)) := by
      rw [hhol, he.neg_one_pow, one_mul]
    exact ⟨he, hhol1, exists_periodic_probe_pairing_ne_zero hUc hhol1 hU0⟩
  · right
    have hhol1 : U (3 * Real.pi / 2) = -U (-(Real.pi / 2)) := by
      rw [hhol, ho.neg_one_pow, neg_one_mul]
    exact ⟨ho, hhol1, fun p hp hper =>
      doubledTrace_pairing_eq_zero hUc hhol1 hp hper⟩

/-! ### §7 The invariant at an isolated zero, and transfer by circle domination -/

/-- **The invariant at an isolated zero**: every continuous square-root circle
trace around an isolated zero returns with the parity of the vanishing order. -/
theorem trace_holonomy_isolated_zero {f : ℂ → ℂ} {ρ : ℂ} {r₀ r R : ℝ}
    (h0 : 0 ≤ r₀) (hr₀ : r₀ < r) (hrR : r < R)
    (hf : AnalyticOnNhd ℂ f (ball ρ R))
    (hiso : ∀ z ∈ ball ρ R, z ≠ ρ → f z ≠ 0)
    {m : ℕ} (hm : analyticOrderAt f ρ = m)
    {G₁ G₂ : ℂ → ℂ}
    (hG₁ : AnalyticOnNhd ℂ G₁ (chartRA ρ r₀ R))
    (hG₂ : AnalyticOnNhd ℂ G₂ (chartLA ρ r₀ R))
    (hpG₁ : ∀ z ∈ chartRA ρ r₀ R, G₁ z ^ (2 : ℕ) = f z)
    (hpG₂ : ∀ z ∈ chartLA ρ r₀ R, G₂ z ^ (2 : ℕ) = f z)
    {U : ℝ → ℂ}
    (hUc : ContinuousOn U (Icc (-(Real.pi / 2)) (3 * Real.pi / 2)))
    (hUsq : ∀ θ ∈ Icc (-(Real.pi / 2)) (3 * Real.pi / 2),
      U θ ^ (2 : ℕ) = f (circleMap ρ r θ)) :
    U (3 * Real.pi / 2) = (-1) ^ m * U (-(Real.pi / 2)) := by
  have hR : 0 < R := lt_of_le_of_lt h0 (lt_trans hr₀ hrR)
  obtain ⟨h, hhan, hhρ, hfact, -⟩ := exists_peel isOpen_ball hf
    (mem_ball_self hR) hm
  have hh0 : ∀ z ∈ ball ρ R, h z ≠ 0 := by
    intro z hz
    by_cases hzρ : z = ρ
    · rw [hzρ]
      exact hhρ
    · intro hzero
      have hfz := hfact z hz
      rw [hzero, mul_zero] at hfz
      exact hiso z hz hzρ hfz
  have hres := continuous_trace_holonomy_neg_one_pow
    ({Unit.unit} : Finset Unit) (fun _ => ρ) (fun _ => m) h0 hr₀ hrR
    (fun i _ => by simpa using h0) hhan hh0
    (fun z hz => by simpa using hfact z hz)
    hG₁ hG₂ hpG₁ hpG₂ hUc hUsq
  simpa using hres

/-- **Holonomy transfer by circle domination**: if `g` deviates from `f` by
less than `‖f‖` pointwise on ONE circle, then continuous root traces of `f` and
`g` along that circle carry the SAME holonomy.  The invariant transfers on
boundary data alone — no interior information about `g` enters: the dominated
root ratio is confined to one component of the split cone, so its endpoints
cannot flip. -/
theorem holonomy_eq_of_circle_domination {f g : ℂ → ℂ} {a : ℂ} {r : ℝ}
    {U V : ℝ → ℂ} {σ τ : ℂ}
    (hUc : ContinuousOn U (Icc (-(Real.pi / 2)) (3 * Real.pi / 2)))
    (hVc : ContinuousOn V (Icc (-(Real.pi / 2)) (3 * Real.pi / 2)))
    (hUsq : ∀ θ ∈ Icc (-(Real.pi / 2)) (3 * Real.pi / 2),
      U θ ^ (2 : ℕ) = f (circleMap a r θ))
    (hVsq : ∀ θ ∈ Icc (-(Real.pi / 2)) (3 * Real.pi / 2),
      V θ ^ (2 : ℕ) = g (circleMap a r θ))
    (hdom : ∀ θ ∈ Icc (-(Real.pi / 2)) (3 * Real.pi / 2),
      ‖g (circleMap a r θ) - f (circleMap a r θ)‖ < ‖f (circleMap a r θ)‖)
    (hσ : U (3 * Real.pi / 2) = σ * U (-(Real.pi / 2)))
    (hτ : V (3 * Real.pi / 2) = τ * V (-(Real.pi / 2)))
    (hσpm : σ = 1 ∨ σ = -1) (hτpm : τ = 1 ∨ τ = -1) :
    τ = σ := by
  have hπ := Real.pi_pos
  have hstart : -(Real.pi / 2) ∈ Icc (-(Real.pi / 2)) (3 * Real.pi / 2) :=
    ⟨le_refl _, by linarith⟩
  have hend : 3 * Real.pi / 2 ∈ Icc (-(Real.pi / 2)) (3 * Real.pi / 2) :=
    ⟨by linarith, le_refl _⟩
  have hf0 : ∀ θ ∈ Icc (-(Real.pi / 2)) (3 * Real.pi / 2),
      f (circleMap a r θ) ≠ 0 := by
    intro θ hθ h
    have hd := hdom θ hθ
    rw [h, sub_zero, norm_zero] at hd
    exact absurd hd (not_lt.mpr (norm_nonneg _))
  have hU0 : ∀ θ ∈ Icc (-(Real.pi / 2)) (3 * Real.pi / 2), U θ ≠ 0 := by
    intro θ hθ h
    have := hUsq θ hθ
    rw [h] at this
    exact hf0 θ hθ (by rw [← this]; ring)
  have hre : ∀ θ ∈ Icc (-(Real.pi / 2)) (3 * Real.pi / 2),
      0 < (g (circleMap a r θ) / f (circleMap a r θ)).re := by
    intro θ hθ
    have h1 : ‖g (circleMap a r θ) / f (circleMap a r θ) - 1‖ < 1 := by
      rw [show g (circleMap a r θ) / f (circleMap a r θ) - 1
          = (g (circleMap a r θ) - f (circleMap a r θ)) / f (circleMap a r θ) by
        field_simp [hf0 θ hθ], norm_div,
        div_lt_one (norm_pos_iff.mpr (hf0 θ hθ))]
      exact hdom θ hθ
    have h3 : |(g (circleMap a r θ) / f (circleMap a r θ) - 1).re|
        ≤ ‖g (circleMap a r θ) / f (circleMap a r θ) - 1‖ :=
      Complex.abs_re_le_norm _
    have h4 : (g (circleMap a r θ) / f (circleMap a r θ)).re
        = 1 + (g (circleMap a r θ) / f (circleMap a r θ) - 1).re := by
      rw [Complex.sub_re, Complex.one_re]
      ring
    rw [h4]
    have h5 := neg_abs_le ((g (circleMap a r θ) / f (circleMap a r θ) - 1).re)
    linarith
  have hW0 : ∀ θ ∈ Icc (-(Real.pi / 2)) (3 * Real.pi / 2),
      (V θ / U θ).re ≠ 0 := by
    intro θ hθ hzero
    have hWsq : (V θ / U θ) ^ (2 : ℕ)
        = g (circleMap a r θ) / f (circleMap a r θ) := by
      rw [div_pow, hUsq θ hθ, hVsq θ hθ]
    have hcomp : (g (circleMap a r θ) / f (circleMap a r θ)).re
        = (V θ / U θ).re * (V θ / U θ).re - (V θ / U θ).im * (V θ / U θ).im := by
      rw [← hWsq, sq, Complex.mul_re]
    rw [hzero] at hcomp
    have hre' := hre θ hθ
    nlinarith [mul_self_nonneg ((V θ / U θ).im)]
  have hWc : ContinuousOn (fun θ => (V θ / U θ).re)
      (Icc (-(Real.pi / 2)) (3 * Real.pi / 2)) :=
    Complex.continuous_re.comp_continuousOn (hVc.div hUc hU0)
  have key : ∀ x y : ℝ, x ∈ Icc (-(Real.pi / 2)) (3 * Real.pi / 2) →
      y ∈ Icc (-(Real.pi / 2)) (3 * Real.pi / 2) →
      (V x / U x).re = -((V y / U y).re) → False := by
    intro x y hx hy hflip
    rcases lt_or_gt_of_ne (hW0 y hy) with hneg | hpos
    · have hmem : (0 : ℝ) ∈ Icc ((V y / U y).re) ((V x / U x).re) := by
        rw [hflip]
        constructor <;> linarith
      obtain ⟨t, ht, h0⟩ := isPreconnected_Icc.intermediate_value hy hx hWc hmem
      have h0' : (V t / U t).re = 0 := h0
      exact hW0 t ht h0'
    · have hmem : (0 : ℝ) ∈ Icc ((V x / U x).re) ((V y / U y).re) := by
        rw [hflip]
        constructor <;> linarith
      obtain ⟨t, ht, h0⟩ := isPreconnected_Icc.intermediate_value hx hy hWc hmem
      have h0' : (V t / U t).re = 0 := h0
      exact hW0 t ht h0'
  have hUs0 : U (-(Real.pi / 2)) ≠ 0 := hU0 _ hstart
  rcases hσpm with hσ1 | hσ1 <;> rcases hτpm with hτ1 | hτ1
  · rw [hσ1, hτ1]
  · exfalso
    have hflip : V (3 * Real.pi / 2) / U (3 * Real.pi / 2)
        = -(V (-(Real.pi / 2)) / U (-(Real.pi / 2))) := by
      rw [hσ, hτ, hσ1, hτ1]
      field_simp
    refine key _ _ hend hstart ?_
    rw [hflip, Complex.neg_re]
  · exfalso
    have hflip : V (3 * Real.pi / 2) / U (3 * Real.pi / 2)
        = -(V (-(Real.pi / 2)) / U (-(Real.pi / 2))) := by
      rw [hσ, hτ, hσ1, hτ1]
      field_simp
    refine key _ _ hend hstart ?_
    rw [hflip, Complex.neg_re]
  · rw [hσ1, hτ1]

end RHTower
