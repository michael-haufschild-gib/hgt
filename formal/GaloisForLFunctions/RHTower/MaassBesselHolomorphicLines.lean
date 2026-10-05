import GaloisForLFunctions.RHTower.MaassBesselFunction
import GaloisForLFunctions.HTGeometry.ComplexC2Laplacian

/-!
# Holomorphic extension of the Maass function along curves

`K₀(w) = ∫₀^∞ e^{−w cosh t} dt` is holomorphic on `Re w > 0` with `|K₀(w)| ≤ K₀(Re w)`
(`kZeroC`).  Hence

`U(ξ, η) = 4 Σ g_n η^{1/2} K₀(2πnη) cos(2πnξ) + η^{1/2}(b + a log η)`

is holomorphic in `(ξ, η)` wherever `Re η > 2|Im ξ|`, and along any holomorphic curve
`ξ = X(s)`, `η = Y(s)` in that region `s ↦ U(X(s), Y(s))` is holomorphic
(`differentiableOn_maassC_comp`).  On real points `U(x, y) = u(x + iy)`.

Consequences:
* along every horizontal line, `x ↦ u(x + iy₀)` and `x ↦ u(−1/(x + iy₀))` are real-analytic
  (`analyticOnNhd_maassFun_line`, `analyticOnNhd_maassFun_inv_line`);
* the quarter equation is invariant under `z ↦ −1/z` (`quarterDefect_comp_inv`), by the
  conformal covariance of the Laplacian (`laplacian_holomorphic_comp`).
-/

open Complex Set Filter MeasureTheory
open scoped ContDiff

noncomputable section

namespace RHTower.MaassBesselSeries

open BesselKZero MaassAxisContinuation

variable {g : ℕ → ℂ}

/-! ## `K₀` at complex argument -/

/-- `K₀(w) = ∫₀^∞ e^{−w cosh t} dt`. -/
def kZeroC (w : ℂ) : ℂ := ∫ t in Ioi (0 : ℝ), cexp (-(w * (Real.cosh t : ℂ)))

theorem norm_kZeroC_integrand (w : ℂ) (t : ℝ) :
    ‖cexp (-(w * (Real.cosh t : ℂ)))‖ = kIntegrand 0 w.re t := by
  rw [Complex.norm_exp]
  simp [kIntegrand]

theorem integrableOn_kZeroC {w : ℂ} (hw : 0 < w.re) :
    IntegrableOn (fun t : ℝ => cexp (-(w * (Real.cosh t : ℂ)))) (Ioi 0) := by
  refine (integrableOn_kIntegrand 0 hw).mono' (by fun_prop) ?_
  exact Eventually.of_forall fun t => (norm_kZeroC_integrand w t).le

theorem norm_kZeroC_le {w : ℂ} (hw : 0 < w.re) : ‖kZeroC w‖ ≤ kMoment 0 w.re := by
  unfold kZeroC
  refine (MeasureTheory.norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  rw [kMoment_eq]
  exact setIntegral_congr_fun measurableSet_Ioi fun t _ => norm_kZeroC_integrand w t

theorem kZeroC_ofReal (r : ℝ) : kZeroC (r : ℂ) = (kMoment 0 r : ℂ) := by
  unfold kZeroC
  rw [kMoment_eq, ← integral_complex_ofReal]
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  simp [kIntegrand, Complex.ofReal_exp]

theorem differentiableOn_kZeroC : DifferentiableOn ℂ kZeroC {w : ℂ | 0 < w.re} := by
  intro w₀ hw₀
  have hw₀' : 0 < w₀.re := hw₀
  have hr : 0 < w₀.re / 2 := by positivity
  have hball : Metric.ball w₀ (w₀.re / 2) ∈ nhds w₀ := Metric.ball_mem_nhds w₀ hr
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (Ioi (0 : ℝ)))
    (F := fun w t => cexp (-(w * (Real.cosh t : ℂ))))
    (F' := fun w t => -(Real.cosh t : ℂ) * cexp (-(w * (Real.cosh t : ℂ))))
    (bound := fun t => kIntegrand 1 (w₀.re / 2) t) (x₀ := w₀) hball
    (Eventually.of_forall fun w => (by fun_prop : Continuous fun t : ℝ =>
      cexp (-(w * (Real.cosh t : ℂ)))).aestronglyMeasurable)
    (integrableOn_kZeroC hw₀') (by fun_prop : Continuous fun t : ℝ =>
      -(Real.cosh t : ℂ) * cexp (-(w₀ * (Real.cosh t : ℂ)))).aestronglyMeasurable
    ?_ (integrableOn_kIntegrand 1 hr) ?_
  · exact (key.2.differentiableAt).differentiableWithinAt
  · refine Eventually.of_forall fun t w hw => ?_
    have hwre : w₀.re / 2 < w.re := by
      have h := Metric.mem_ball.mp hw
      have := Complex.abs_re_le_norm (w - w₀)
      rw [Complex.sub_re] at this
      rw [dist_eq_norm] at h
      have h2 := abs_lt.mp (lt_of_le_of_lt this h)
      linarith [h2.1]
    rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.cosh_pos t), norm_kZeroC_integrand]
    unfold kIntegrand
    simp only [pow_zero, one_mul, pow_one]
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith [Real.one_le_cosh t]))
      (Real.cosh_pos t).le
  · refine Eventually.of_forall fun t w _ => ?_
    have := ((hasDerivAt_id w).mul_const (Real.cosh t : ℂ)).neg.cexp
    simpa [mul_comm] using this

/-! ## Elementary bounds -/

theorem norm_cos_le_exp_abs_im (z : ℂ) : ‖Complex.cos z‖ ≤ Real.exp |z.im| := by
  rw [Complex.cos]
  have h1 : ‖cexp (z * I)‖ = Real.exp (-z.im) := by rw [Complex.norm_exp]; simp
  have h2 : ‖cexp (-z * I)‖ = Real.exp z.im := by rw [Complex.norm_exp]; simp
  calc ‖(cexp (z * I) + cexp (-z * I)) / 2‖ ≤ (‖cexp (z * I)‖ + ‖cexp (-z * I)‖) / 2 := by
        rw [norm_div, show ‖(2 : ℂ)‖ = 2 by norm_num]
        exact div_le_div_of_nonneg_right (norm_add_le _ _) (by norm_num)
    _ = (Real.exp (-z.im) + Real.exp z.im) / 2 := by rw [h1, h2]
    _ ≤ Real.exp |z.im| := by
        have ha := Real.exp_le_exp.mpr (neg_le_abs z.im)
        have hb := Real.exp_le_exp.mpr (le_abs_self z.im)
        linarith

/-! ## The complexified Maass function -/

/-- The term `4 g_n η^{1/2} K₀(2πnη) cos(2πnξ)` (index `n + 1`). -/
def termC (g : ℕ → ℂ) (n : ℕ) (ξ η : ℂ) : ℂ :=
  4 * g (n + 1) * (η ^ (1 / 2 : ℂ) * kZeroC (2 * Real.pi * ((n + 1 : ℕ) : ℂ) * η) *
    Complex.cos (2 * Real.pi * ((n + 1 : ℕ) : ℂ) * ξ))

/-- `U(ξ, η)`. -/
def maassC (g : ℕ → ℂ) (a b : ℂ) (ξ η : ℂ) : ℂ :=
  (∑' n, termC g n ξ η) + η ^ (1 / 2 : ℂ) * (b + a * Complex.log η)

theorem norm_termC_le (hg : PolyGrowth g) {δ M : ℝ} (hδ : 0 < δ) :
    ∃ u : ℕ → ℝ, Summable u ∧ ∀ n ξ η, δ ≤ η.re → ‖η‖ ≤ M → |ξ.im| ≤ δ / 2 →
      ‖termC g n ξ η‖ ≤ u n := by
  obtain ⟨C, hC, A, hA⟩ := hg
  have hc : 0 < Real.pi * δ := by positivity
  set K : ℝ := Real.exp (2 * Real.pi * δ) * kMoment 0 (2 * Real.pi * δ) with hK
  refine ⟨fun n => 4 * C * 2 ^ A * (|M| + 1) * K *
      (((n + 1 : ℕ) : ℝ) ^ A * Real.exp (-(Real.pi * δ) * ((n + 1 : ℕ) : ℝ))),
    (summable_pow_mul_exp_neg A hc).mul_left _, fun n ξ η hre hM hξ => ?_⟩
  have hη0 : 0 < η.re := lt_of_lt_of_le hδ hre
  have hn1 : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
  -- the three factors
  have hpow : ‖η ^ (1 / 2 : ℂ)‖ ≤ |M| + 1 := by
    rw [Complex.norm_cpow_of_ne_zero (by intro h; rw [h] at hη0; simp at hη0)]
    simp only [show ((1 / 2 : ℂ)).re = 1 / 2 by norm_num, show ((1 / 2 : ℂ)).im = 0 by norm_num,
      mul_zero, Real.exp_zero, div_one]
    have hη : 0 < ‖η‖ := norm_pos_iff.mpr (by intro h; rw [h] at hη0; simp at hη0)
    calc ‖η‖ ^ (1 / 2 : ℝ) ≤ max ‖η‖ 1 := by
          rcases le_total ‖η‖ 1 with h | h
          · exact (Real.rpow_le_one hη.le h (by norm_num)).trans (le_max_right _ _)
          · exact (Real.rpow_le_self_of_one_le h (by norm_num)).trans (le_max_left _ _)
      _ ≤ |M| + 1 := max_le (hM.trans ((le_abs_self M).trans (by linarith))) (by
          linarith [abs_nonneg M])
  have hKn : ‖kZeroC (2 * Real.pi * ((n + 1 : ℕ) : ℂ) * η)‖ ≤
      K * Real.exp (-(2 * Real.pi * δ) * ((n + 1 : ℕ) : ℝ)) := by
    have hre' : (2 * Real.pi * ((n + 1 : ℕ) : ℂ) * η).re = 2 * Real.pi * ((n + 1 : ℕ) : ℝ) * η.re := by
      simp
    have hpos : 0 < (2 * Real.pi * ((n + 1 : ℕ) : ℂ) * η).re := by rw [hre']; positivity
    have hr₁ : 0 < 2 * Real.pi * δ := by positivity
    have hle : 2 * Real.pi * δ ≤ 2 * Real.pi * ((n + 1 : ℕ) : ℝ) * η.re := by
      have : δ ≤ ((n + 1 : ℕ) : ℝ) * η.re := by nlinarith
      nlinarith [Real.pi_pos]
    have hnr : 2 * Real.pi * δ * ((n + 1 : ℕ) : ℝ) ≤ 2 * Real.pi * ((n + 1 : ℕ) : ℝ) * η.re := by
      have := mul_le_mul_of_nonneg_left hre (by positivity : (0 : ℝ) ≤ 2 * Real.pi * ((n + 1 : ℕ) : ℝ))
      linarith
    calc ‖kZeroC (2 * Real.pi * ((n + 1 : ℕ) : ℂ) * η)‖
        ≤ kMoment 0 (2 * Real.pi * ((n + 1 : ℕ) : ℝ) * η.re) := by
          have := norm_kZeroC_le hpos; rwa [hre'] at this
      _ ≤ Real.exp (-(2 * Real.pi * ((n + 1 : ℕ) : ℝ) * η.re - 2 * Real.pi * δ)) *
            kMoment 0 (2 * Real.pi * δ) := kMoment_le_exp_mul 0 hr₁ hle
      _ ≤ (Real.exp (2 * Real.pi * δ) * Real.exp (-(2 * Real.pi * δ) * ((n + 1 : ℕ) : ℝ))) *
            kMoment 0 (2 * Real.pi * δ) := by
          refine mul_le_mul_of_nonneg_right ?_ (kMoment_nonneg _ _)
          rw [← Real.exp_add]
          exact Real.exp_le_exp.mpr (by linarith)
      _ = K * Real.exp (-(2 * Real.pi * δ) * ((n + 1 : ℕ) : ℝ)) := by rw [hK]; ring
  have hcos : ‖Complex.cos (2 * Real.pi * ((n + 1 : ℕ) : ℂ) * ξ)‖ ≤
      Real.exp (Real.pi * δ * ((n + 1 : ℕ) : ℝ)) := by
    refine (norm_cos_le_exp_abs_im _).trans (Real.exp_le_exp.mpr ?_)
    have : (2 * Real.pi * ((n + 1 : ℕ) : ℂ) * ξ).im = 2 * Real.pi * ((n + 1 : ℕ) : ℝ) * ξ.im := by
      simp
    rw [this, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi * ((n + 1 : ℕ) : ℝ))]
    have := mul_le_mul_of_nonneg_left hξ (by positivity : (0 : ℝ) ≤ 2 * Real.pi * ((n + 1 : ℕ) : ℝ))
    linarith
  have hg' : ‖g (n + 1)‖ ≤ C * 2 ^ A * ((n + 1 : ℕ) : ℝ) ^ A := by
    have h := hA (n + 1)
    have h2 : ((n + 1 : ℕ) : ℝ) + 1 ≤ 2 * ((n + 1 : ℕ) : ℝ) := by linarith
    calc ‖g (n + 1)‖ ≤ C * (((n + 1 : ℕ) : ℝ) + 1) ^ A := by simpa using h
      _ ≤ C * (2 * ((n + 1 : ℕ) : ℝ)) ^ A := by gcongr
      _ = C * 2 ^ A * ((n + 1 : ℕ) : ℝ) ^ A := by rw [mul_pow]; ring
  unfold termC
  rw [norm_mul, norm_mul, norm_mul, norm_mul, show ‖(4 : ℂ)‖ = 4 by norm_num]
  have hK0 : 0 ≤ K := by rw [hK]; have := kMoment_nonneg 0 (2 * Real.pi * δ); positivity
  calc 4 * ‖g (n + 1)‖ * (‖η ^ (1 / 2 : ℂ)‖ * ‖kZeroC (2 * Real.pi * ((n + 1 : ℕ) : ℂ) * η)‖ *
        ‖Complex.cos (2 * Real.pi * ((n + 1 : ℕ) : ℂ) * ξ)‖)
      ≤ 4 * (C * 2 ^ A * ((n + 1 : ℕ) : ℝ) ^ A) * ((|M| + 1) *
          (K * Real.exp (-(2 * Real.pi * δ) * ((n + 1 : ℕ) : ℝ))) *
          Real.exp (Real.pi * δ * ((n + 1 : ℕ) : ℝ))) := by
        gcongr
    _ = 4 * C * 2 ^ A * (|M| + 1) * K * (((n + 1 : ℕ) : ℝ) ^ A *
          (Real.exp (-(2 * Real.pi * δ) * ((n + 1 : ℕ) : ℝ)) *
            Real.exp (Real.pi * δ * ((n + 1 : ℕ) : ℝ)))) := by ring
    _ = _ := by
        rw [← Real.exp_add]
        congr 3
        ring

/-- **Holomorphy along curves.**  If `X, Y` are holomorphic on an open set `D` on which
`Re Y ≥ δ > 0`, `|Y| ≤ M` and `|Im X| ≤ δ/2`, then `s ↦ U(X(s), Y(s))` is holomorphic on `D`. -/
theorem differentiableOn_maassC_comp (hg : PolyGrowth g) (a b : ℂ) {X Y : ℂ → ℂ} {D : Set ℂ}
    (hD : IsOpen D) (hX : DifferentiableOn ℂ X D) (hY : DifferentiableOn ℂ Y D) {δ M : ℝ}
    (hδ : 0 < δ) (hYre : ∀ s ∈ D, δ ≤ (Y s).re) (hYM : ∀ s ∈ D, ‖Y s‖ ≤ M)
    (hXim : ∀ s ∈ D, |(X s).im| ≤ δ / 2) :
    DifferentiableOn ℂ (fun s => maassC g a b (X s) (Y s)) D := by
  obtain ⟨u, hu, hbd⟩ := norm_termC_le (g := g) (M := M) hg hδ
  have hslit : ∀ s ∈ D, Y s ∈ slitPlane := fun s hs =>
    Or.inl (lt_of_lt_of_le hδ (hYre s hs))
  have hterm : ∀ n, DifferentiableOn ℂ (fun s => termC g n (X s) (Y s)) D := by
    intro n s hs
    have hYs := (hY s hs).differentiableAt (hD.mem_nhds hs)
    have hXs := (hX s hs).differentiableAt (hD.mem_nhds hs)
    have hK : DifferentiableAt ℂ (fun s => kZeroC (2 * Real.pi * ((n + 1 : ℕ) : ℂ) * Y s)) s := by
      have hre : 0 < (2 * Real.pi * ((n + 1 : ℕ) : ℂ) * Y s).re := by
        have := lt_of_lt_of_le hδ (hYre s hs)
        simp; positivity
      have hlin : DifferentiableAt ℂ (fun s => (2 * Real.pi * ((n + 1 : ℕ) : ℂ)) * Y s) s :=
        hYs.const_mul _
      have hK0 : DifferentiableAt ℂ kZeroC ((2 * Real.pi * ((n + 1 : ℕ) : ℂ)) * Y s) :=
        (differentiableOn_kZeroC _ hre).differentiableAt
          ((isOpen_lt continuous_const continuous_re).mem_nhds hre)
      have hc : (fun s => kZeroC (2 * Real.pi * ((n + 1 : ℕ) : ℂ) * Y s)) =
          kZeroC ∘ (fun s => (2 * Real.pi * ((n + 1 : ℕ) : ℂ)) * Y s) := rfl
      rw [hc]
      exact hK0.comp s hlin
    unfold termC
    refine DifferentiableAt.differentiableWithinAt ?_
    exact (differentiableAt_const _).mul (((hYs.cpow_const (hslit s hs)).mul hK).mul
      ((hXs.const_mul _).ccos))
  have hsum : DifferentiableOn ℂ (fun s => ∑' n, termC g n (X s) (Y s)) D :=
    differentiableOn_tsum_of_summable_norm hu hterm hD fun n s hs =>
      hbd n (X s) (Y s) (hYre s hs) (hYM s hs) (hXim s hs)
  have hconst : DifferentiableOn ℂ (fun s => Y s ^ (1 / 2 : ℂ) * (b + a * Complex.log (Y s))) D := by
    intro s hs
    have hYs := (hY s hs).differentiableAt (hD.mem_nhds hs)
    refine DifferentiableAt.differentiableWithinAt ?_
    exact (hYs.cpow_const (hslit s hs)).mul ((differentiableAt_const _).add
      ((differentiableAt_const _).mul (hYs.clog (hslit s hs))))
  exact hsum.add hconst

/-! ## Real points -/

theorem termC_ofReal (n : ℕ) (x : ℝ) {y : ℝ} (hy : 0 < y) :
    termC g n (x : ℂ) (y : ℂ) = 4 * sterm g (1 / 2) 0 0 false n ((x : ℂ) + (y : ℂ) * I) := by
  unfold termC sterm bterm yPart xPart trigFun
  simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
    add_zero, add_im, mul_im, zero_add, Bool.false_eq_true, ↓reduceIte, pow_zero, one_mul]
  rw [show (2 * (Real.pi : ℂ) * ((n + 1 : ℕ) : ℂ) * (y : ℂ)) = ((2 * Real.pi * ((n + 1 : ℕ) : ℝ) * y : ℝ) : ℂ)
    by push_cast; ring, kZeroC_ofReal,
    show (2 * (Real.pi : ℂ) * ((n + 1 : ℕ) : ℂ) * (x : ℂ)) = ((2 * Real.pi * ((n + 1 : ℕ) : ℝ) * x : ℝ) : ℂ)
    by push_cast; ring, ← Complex.ofReal_cos, show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring,
    ← Complex.ofReal_cpow hy.le]
  push_cast
  ring

/-- `U(x, y) = u(x + iy)` for real `x` and `y > 0`. -/
theorem maassC_ofReal (a b : ℂ) (x : ℝ) {y : ℝ} (hy : 0 < y) :
    maassC g a b (x : ℂ) (y : ℂ) = maassFun g a b ((x : ℂ) + (y : ℂ) * I) := by
  unfold maassC maassFun cosSeries besselSeries constTerm sqrtPart sqrtLogPart
  simp only [termC_ofReal _ x hy, tsum_mul_left, add_im, ofReal_im, mul_im, ofReal_re, I_im,
    mul_one, I_re, mul_zero, add_zero, zero_add]
  rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring, ← Complex.ofReal_cpow hy.le,
    ← Complex.ofReal_log hy.le]
  push_cast
  ring

end RHTower.MaassBesselSeries
