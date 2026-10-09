import GaloisForLFunctions.RHTower.WeilFullConeRiemannKernelRigidity

/-!
# Decay rate of Riemann's kernel on the tail

On `u ≥ ½ log 2`, Riemann's kernel `Φ(u) = Σ_n e^{u/2} R(n²e^{2u}) e^{-πn²e^{2u}}`,
`R(Y) = 4π²Y² - 6πY`, satisfies `Φ'(u) ≤ -πe^{2u} Φ(u)`. Termwise, the cusp derivative
`DR = R/2 + 2YR' - 2πYR` obeys `DR(Y) + πY R(Y) = -πY (4π²Y² - 24πY + 15) ≤ 0` for `Y ≥ 2`.

* `riemannKernelReal_le_mul_exp`: `Φ(t) ≤ Φ(s) e^{-πe^{2s}(t-s)}` for `½ log 2 ≤ s ≤ t`;
* `riemannKernelReal_antitoneOn`: `Φ` is antitone on `[½ log 2, ∞)`;
* `exists_riemannKernelReal_edge_min`: for all large `b`, `Φ(b) ≤ Φ(t)` whenever `|t| ≤ b`.
-/

open Real Filter Topology Set Polynomial

namespace RHTower

noncomputable section

theorem riemannCuspPoly_eq : riemannCuspPoly = C (4 * π ^ 2) * X ^ 2 - C (6 * π) * X := by
  apply Polynomial.funext
  intro Y
  rw [riemannCuspPoly_eval]
  simp

theorem cuspDeriv_riemannCuspPoly_eval (Y : ℝ) :
    (cuspDeriv riemannCuspPoly).eval Y =
      -(8 * π ^ 3 * Y ^ 3) + 30 * π ^ 2 * Y ^ 2 - 15 * π * Y := by
  rw [riemannCuspPoly_eq]
  simp only [cuspDeriv, eval_sub, eval_add, eval_mul, eval_C, eval_X, eval_pow,
    derivative_sub, derivative_mul, derivative_C, derivative_X_pow, derivative_X, zero_mul,
    zero_add, mul_one]
  push_cast
  ring

/-- `DR(Y) ≤ -πY R(Y)` for `Y ≥ 2`. -/
theorem cuspDeriv_riemannCuspPoly_eval_le {Y : ℝ} (hY : 2 ≤ Y) :
    (cuspDeriv riemannCuspPoly).eval Y ≤ -(π * Y) * riemannCuspPoly.eval Y := by
  rw [cuspDeriv_riemannCuspPoly_eval, riemannCuspPoly_eval]
  have hπ := Real.pi_gt_three
  have hz : 6 ≤ π * Y := by nlinarith
  have hq : 0 ≤ 4 * (π * Y) ^ 2 - 24 * (π * Y) + 15 := by nlinarith
  have hY0 : 0 ≤ π * Y := by linarith
  nlinarith [mul_nonneg hY0 hq]

theorem two_le_exp_two_mul {u : ℝ} (hu : Real.log 2 / 2 ≤ u) : 2 ≤ Real.exp (2 * u) := by
  have : Real.log 2 ≤ 2 * u := by linarith
  calc (2 : ℝ) = Real.exp (Real.log 2) := (Real.exp_log (by norm_num)).symm
    _ ≤ Real.exp (2 * u) := Real.exp_le_exp.mpr this

/-- Termwise: `D(term) ≤ -πe^{2u} · term` on `u ≥ ½ log 2`. -/
theorem cuspTerm_cuspDeriv_riemannCuspPoly_le {n : ℕ} (hn : 1 ≤ n) {u : ℝ}
    (hu : Real.log 2 / 2 ≤ u) :
    cuspTerm (cuspDeriv riemannCuspPoly) n u ≤
      -(π * Real.exp (2 * u)) * cuspTerm riemannCuspPoly n u := by
  have hE := two_le_exp_two_mul hu
  have hn1 : (1 : ℝ) ≤ (n : ℝ) ^ 2 := one_le_pow₀ (by exact_mod_cast hn)
  set Y : ℝ := (n : ℝ) ^ 2 * Real.exp (2 * u) with hYdef
  have hYE : Real.exp (2 * u) ≤ Y := by
    rw [hYdef]; nlinarith [Real.exp_pos (2 * u)]
  have hY2 : 2 ≤ Y := le_trans hE hYE
  have hR0 : 0 ≤ riemannCuspPoly.eval Y := by
    rw [riemannCuspPoly_eval]
    have hπ := Real.pi_gt_three
    have h1 : 0 ≤ 4 * π * Y - 6 := by nlinarith
    have h2 : 0 ≤ π * Y := by positivity
    nlinarith [mul_nonneg h1 h2]
  have hD := cuspDeriv_riemannCuspPoly_eval_le hY2
  have hstep : (cuspDeriv riemannCuspPoly).eval Y ≤
      -(π * Real.exp (2 * u)) * riemannCuspPoly.eval Y := by
    have : -(π * Y) * riemannCuspPoly.eval Y ≤ -(π * Real.exp (2 * u)) * riemannCuspPoly.eval Y := by
      have := mul_le_mul_of_nonneg_right hYE hR0
      nlinarith [Real.pi_pos]
    linarith
  unfold cuspTerm
  rw [← hYdef]
  have hpos : 0 < Real.exp (u / 2) * Real.exp (-π * Y) := by positivity
  calc Real.exp (u / 2) * (cuspDeriv riemannCuspPoly).eval Y * Real.exp (-π * Y)
      = (Real.exp (u / 2) * Real.exp (-π * Y)) * (cuspDeriv riemannCuspPoly).eval Y := by ring
    _ ≤ (Real.exp (u / 2) * Real.exp (-π * Y)) *
        (-(π * Real.exp (2 * u)) * riemannCuspPoly.eval Y) :=
        mul_le_mul_of_nonneg_left hstep hpos.le
    _ = _ := by ring

/-- `Φ'(u) ≤ -πe^{2u} Φ(u)` on `u ≥ ½ log 2`, in cusp-series form. -/
theorem cuspSeries_cuspDeriv_riemannCuspPoly_le {u : ℝ} (hu : Real.log 2 / 2 ≤ u) :
    cuspSeries (cuspDeriv riemannCuspPoly) u ≤
      -(π * Real.exp (2 * u)) * cuspSeries riemannCuspPoly u := by
  unfold cuspSeries
  rw [← tsum_mul_left]
  exact Summable.tsum_le_tsum
    (fun n => cuspTerm_cuspDeriv_riemannCuspPoly_le (Nat.succ_le_succ (Nat.zero_le n)) hu)
    (summable_cuspTerm _ u) ((summable_cuspTerm _ u).mul_left _)

/-- **Tail decay.** `Φ(t) ≤ Φ(s) e^{-πe^{2s}(t-s)}` for `½ log 2 ≤ s ≤ t`. -/
theorem cuspSeries_riemannCuspPoly_le_mul_exp {s t : ℝ} (hs : Real.log 2 / 2 ≤ s) (hst : s ≤ t) :
    cuspSeries riemannCuspPoly t ≤
      cuspSeries riemannCuspPoly s * Real.exp (-(π * Real.exp (2 * s) * (t - s))) := by
  set c : ℝ := π * Real.exp (2 * s) with hc
  set h : ℝ → ℝ := fun u => cuspSeries riemannCuspPoly u * Real.exp (c * u) with hh
  have hderiv : ∀ u, HasDerivAt h
      (cuspSeries (cuspDeriv riemannCuspPoly) u * Real.exp (c * u) +
        cuspSeries riemannCuspPoly u * (Real.exp (c * u) * c)) u := by
    intro u
    have h1 := hasDerivAt_cuspSeries riemannCuspPoly u
    have h2 : HasDerivAt (fun u : ℝ => Real.exp (c * u)) (Real.exp (c * u) * c) u := by
      have := ((hasDerivAt_id u).const_mul c).exp
      simpa using this
    exact h1.mul h2
  have hs0 : 0 ≤ s := le_trans (by positivity) hs
  have hanti : AntitoneOn h (Ici s) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici s)
    · exact fun u _ => (hderiv u).continuousAt.continuousWithinAt
    · exact fun u _ => (hderiv u).differentiableAt.differentiableWithinAt
    · intro u hu
      rw [interior_Ici] at hu
      have hu' : s < u := hu
      rw [(hderiv u).deriv]
      have hD := cuspSeries_cuspDeriv_riemannCuspPoly_le (le_trans hs hu'.le)
      have hpos := cuspSeries_riemannCuspPoly_pos (le_trans hs0 hu'.le)
      have hexp : Real.exp (2 * s) ≤ Real.exp (2 * u) := Real.exp_le_exp.mpr (by linarith)
      have hE := Real.exp_pos (c * u)
      have hcle : c ≤ π * Real.exp (2 * u) := by
        rw [hc]; exact mul_le_mul_of_nonneg_left hexp Real.pi_pos.le
      have : cuspSeries (cuspDeriv riemannCuspPoly) u + cuspSeries riemannCuspPoly u * c ≤ 0 := by
        nlinarith
      nlinarith
  have hle := hanti (self_mem_Ici) (show t ∈ Ici s from hst) hst
  simp only [hh] at hle
  have hEt := Real.exp_pos (c * t)
  rw [show -(c * (t - s)) = c * s - c * t by ring, Real.exp_sub]
  rw [mul_div_assoc', le_div_iff₀ hEt]
  exact hle

theorem riemannKernelReal_of_nonneg {t : ℝ} (ht : 0 ≤ t) :
    riemannKernelReal t = cuspSeries riemannCuspPoly t := by
  rw [riemannKernelReal, abs_of_nonneg ht]

/-- `Φ(t) ≤ Φ(s) e^{-πe^{2s}(t-s)}` for `½ log 2 ≤ s ≤ t`. -/
theorem riemannKernelReal_le_mul_exp {s t : ℝ} (hs : Real.log 2 / 2 ≤ s) (hst : s ≤ t) :
    riemannKernelReal t ≤ riemannKernelReal s * Real.exp (-(π * Real.exp (2 * s) * (t - s))) := by
  have hs0 : 0 ≤ s := le_trans (by positivity) hs
  rw [riemannKernelReal_of_nonneg hs0, riemannKernelReal_of_nonneg (le_trans hs0 hst)]
  exact cuspSeries_riemannCuspPoly_le_mul_exp hs hst

/-- `Φ` is antitone on `[½ log 2, ∞)`. -/
theorem riemannKernelReal_antitoneOn : AntitoneOn riemannKernelReal (Ici (Real.log 2 / 2)) := by
  intro s hs t ht hst
  have h := riemannKernelReal_le_mul_exp hs hst
  have hpos := riemannKernelReal_pos s
  have hexp : Real.exp (-(π * Real.exp (2 * s) * (t - s))) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    have : 0 ≤ π * Real.exp (2 * s) * (t - s) := by
      have := Real.exp_pos (2 * s)
      have : 0 ≤ t - s := by linarith
      positivity
    linarith
  calc riemannKernelReal t ≤ riemannKernelReal s * Real.exp (-(π * Real.exp (2 * s) * (t - s))) := h
    _ ≤ riemannKernelReal s * 1 := mul_le_mul_of_nonneg_left hexp hpos.le
    _ = riemannKernelReal s := mul_one _

/-- **The minimum on `[-b, b]` sits at the edge.** For all large `b`, `Φ(b) ≤ Φ(t)` whenever
`|t| ≤ b`. -/
theorem exists_riemannKernelReal_edge_min :
    ∃ b₀ : ℝ, 0 ≤ b₀ ∧ ∀ b : ℝ, b₀ ≤ b → ∀ t : ℝ, |t| ≤ b →
      riemannKernelReal b ≤ riemannKernelReal t := by
  set s₀ : ℝ := Real.log 2 / 2 with hs₀
  have hs₀0 : 0 ≤ s₀ := by positivity
  obtain ⟨t₀, ht₀, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr hs₀0)
    continuous_riemannKernelReal.continuousOn
  set m₀ : ℝ := riemannKernelReal t₀ with hm₀
  have hm₀pos : 0 < m₀ := riemannKernelReal_pos t₀
  have hlim : Tendsto (fun b : ℝ => riemannKernelReal s₀ *
      Real.exp (-(π * Real.exp (2 * s₀) * (b - s₀)))) atTop (𝓝 0) := by
    have hk : 0 < π * Real.exp (2 * s₀) := by positivity
    have h1 : Tendsto (fun b : ℝ => π * Real.exp (2 * s₀) * (b - s₀)) atTop atTop :=
      Tendsto.const_mul_atTop hk (tendsto_atTop_add_const_right _ _ tendsto_id)
    have h2 := (Real.tendsto_exp_neg_atTop_nhds_zero.comp h1).const_mul (riemannKernelReal s₀)
    rw [mul_zero] at h2
    exact h2
  obtain ⟨b₁, hb₁⟩ := Filter.eventually_atTop.mp (hlim.eventually (ge_mem_nhds hm₀pos))
  refine ⟨max s₀ b₁, le_trans hs₀0 (le_max_left _ _), fun b hb t ht => ?_⟩
  have hbs : s₀ ≤ b := le_trans (le_max_left _ _) hb
  have hbb : b₁ ≤ b := le_trans (le_max_right _ _) hb
  have heven : riemannKernelReal t = riemannKernelReal |t| := by
    simp [riemannKernelReal, abs_abs]
  rw [heven]
  rcases le_or_gt s₀ |t| with hts | hts
  · exact riemannKernelReal_antitoneOn hts hbs ht
  · have h1 : riemannKernelReal b ≤ riemannKernelReal s₀ *
        Real.exp (-(π * Real.exp (2 * s₀) * (b - s₀))) :=
      riemannKernelReal_le_mul_exp le_rfl hbs
    have h2 := hb₁ b hbb
    have h3 : m₀ ≤ riemannKernelReal |t| := hmin ⟨abs_nonneg t, hts.le⟩
    linarith

end

end RHTower
