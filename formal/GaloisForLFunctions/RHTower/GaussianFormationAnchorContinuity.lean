import GaloisForLFunctions.RHTower.GaussianEulerContinuumRelativeFormation

/-!
# Continuity of the Gaussian formation current in the anchor

For the zero-free Gaussian Euler–continuum formation `Φₓ`, the logarithmic derivative is
`logDeriv Φₓ = logDeriv h_∞ - Jₓ + Mₓ` on `Re s > 0`.  On the closed right half-plane `|n^{-s}| ≤ 1`
and `|u^{-s}| ≤ 1` for `u ≥ 1`, so the anchor variation is controlled uniformly in `s` by

`∑_n Λ(n) |e^{-πyn²} - e^{-πxn²}| + ∫₁^∞ |e^{-πyu²} - e^{-πxu²}| du`,

which tends to zero as `y → x > 0` by dominated convergence.  Hence `logDeriv Φ_y → logDeriv Φ_x`
uniformly on the whole open right half-plane.
-/

noncomputable section

open Complex Filter Topology Set MeasureTheory

namespace RHTower

theorem norm_natCast_cpow_neg_le_one {u : ℝ} (hu : 1 ≤ u) {s : ℂ} (hs : 0 ≤ s.re) :
    ‖(u : ℂ) ^ (-s)‖ ≤ 1 := by
  rw [GaloisForLFunctions.norm_cpow_neg_eq_rpow_re u (by linarith) s]
  exact Real.rpow_le_one_of_one_le_of_nonpos hu (by linarith)

/-- `∑ Λ(n) e^{-πyn²}` converges for `y > 0`. -/
theorem summable_vonMangoldt_mul_gaussian {y : ℝ} (hy : 0 < y) :
    Summable fun n : GaussianEulerIndex =>
      ArithmeticFunction.vonMangoldt n.1 * Real.exp (-Real.pi * y * (n.1 : ℝ) ^ 2) := by
  have hraw := GaloisForLFunctions.HTGeometry.summable_rpow_mul_exp_neg_rpow
    (A := 1) (c := Real.pi * y) (e := 2) (mul_pos Real.pi_pos hy) (by norm_num)
  have hbase := hraw.subtype (fun n : ℕ => 2 ≤ n)
  refine Summable.of_nonneg_of_le (fun n => mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
    (Real.exp_pos _).le) (fun n => ?_) hbase
  have hn0 : (0 : ℝ) ≤ n.1 := Nat.cast_nonneg _
  have hΛ : ArithmeticFunction.vonMangoldt n.1 ≤ (n.1 : ℝ) :=
    ArithmeticFunction.vonMangoldt_le_log.trans (Real.log_le_self hn0)
  change _ ≤ (n.1 : ℝ) ^ (1 : ℝ) * Real.exp (-(Real.pi * y * (n.1 : ℝ) ^ (2 : ℝ)))
  rw [Real.rpow_one, Real.rpow_two]
  have he : Real.exp (-Real.pi * y * (n.1 : ℝ) ^ 2) =
      Real.exp (-(Real.pi * y * (n.1 : ℝ) ^ 2)) := by ring_nf
  rw [he]
  exact mul_le_mul_of_nonneg_right hΛ (Real.exp_pos _).le

/-- Atomic anchor variation `∑ Λ(n) |e^{-πyn²} - e^{-πxn²}|`. -/
def gaussianAtomicAnchorVariation (x y : ℝ) : ℝ :=
  ∑' n : GaussianEulerIndex, ArithmeticFunction.vonMangoldt n.1 *
    |Real.exp (-Real.pi * y * (n.1 : ℝ) ^ 2) - Real.exp (-Real.pi * x * (n.1 : ℝ) ^ 2)|

theorem summable_atomicAnchorTerm {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    Summable fun n : GaussianEulerIndex => ArithmeticFunction.vonMangoldt n.1 *
      |Real.exp (-Real.pi * y * (n.1 : ℝ) ^ 2) - Real.exp (-Real.pi * x * (n.1 : ℝ) ^ 2)| := by
  refine Summable.of_nonneg_of_le (fun n => mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
    (abs_nonneg _)) (fun n => ?_) ((summable_vonMangoldt_mul_gaussian hy).add
      (summable_vonMangoldt_mul_gaussian hx))
  rw [← mul_add]
  refine mul_le_mul_of_nonneg_left ?_ ArithmeticFunction.vonMangoldt_nonneg
  refine (abs_sub _ _).trans ?_
  rw [abs_of_pos (Real.exp_pos _), abs_of_pos (Real.exp_pos _)]

/-- The atomic current moves by at most the atomic anchor variation, uniformly on `Re s ≥ 0`. -/
theorem norm_gaussianVonMangoldtCurrent_sub_le {x y : ℝ} (hx : 0 < x) (hy : 0 < y) {s : ℂ}
    (hs : 0 ≤ s.re) :
    ‖gaussianVonMangoldtCurrent y s - gaussianVonMangoldtCurrent x s‖ ≤
      gaussianAtomicAnchorVariation x y := by
  have hterm : ∀ (z : ℝ), 0 < z → Summable fun n : GaussianEulerIndex =>
      (ArithmeticFunction.vonMangoldt n.1 : ℂ) * (Real.exp (-Real.pi * z * (n.1 : ℝ) ^ 2) : ℂ) *
        (n.1 : ℂ) ^ (-s) := by
    intro z hz
    refine Summable.of_norm_bounded (summable_vonMangoldt_mul_gaussian hz) fun n => ?_
    have hn1 : (1 : ℝ) ≤ n.1 := by exact_mod_cast le_trans (by norm_num) n.2
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg,
      abs_of_pos (Real.exp_pos _)]
    have hc := norm_natCast_cpow_neg_le_one hn1 hs
    calc ArithmeticFunction.vonMangoldt n.1 * Real.exp (-Real.pi * z * (n.1 : ℝ) ^ 2) *
          ‖((n.1 : ℝ) : ℂ) ^ (-s)‖
        ≤ ArithmeticFunction.vonMangoldt n.1 * Real.exp (-Real.pi * z * (n.1 : ℝ) ^ 2) * 1 :=
          mul_le_mul_of_nonneg_left hc (mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
            (Real.exp_pos _).le)
      _ = _ := mul_one _
  rw [gaussianVonMangoldtCurrent_eq_tsum_cpow, gaussianVonMangoldtCurrent_eq_tsum_cpow,
    ← (hterm y hy).tsum_sub (hterm x hx)]
  have hdiff : ∀ n : GaussianEulerIndex,
      ‖(ArithmeticFunction.vonMangoldt n.1 : ℂ) * (Real.exp (-Real.pi * y * (n.1 : ℝ) ^ 2) : ℂ) *
          (n.1 : ℂ) ^ (-s) -
        (ArithmeticFunction.vonMangoldt n.1 : ℂ) * (Real.exp (-Real.pi * x * (n.1 : ℝ) ^ 2) : ℂ) *
          (n.1 : ℂ) ^ (-s)‖ ≤
      ArithmeticFunction.vonMangoldt n.1 *
        |Real.exp (-Real.pi * y * (n.1 : ℝ) ^ 2) - Real.exp (-Real.pi * x * (n.1 : ℝ) ^ 2)| := by
    intro n
    have hn1 : (1 : ℝ) ≤ n.1 := by exact_mod_cast le_trans (by norm_num) n.2
    have hc := norm_natCast_cpow_neg_le_one hn1 hs
    rw [← sub_mul, ← mul_sub, norm_mul, norm_mul, ← Complex.ofReal_sub, Complex.norm_real,
      Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
    calc ArithmeticFunction.vonMangoldt n.1 *
          |Real.exp (-Real.pi * y * (n.1 : ℝ) ^ 2) - Real.exp (-Real.pi * x * (n.1 : ℝ) ^ 2)| *
          ‖((n.1 : ℝ) : ℂ) ^ (-s)‖
        ≤ ArithmeticFunction.vonMangoldt n.1 *
          |Real.exp (-Real.pi * y * (n.1 : ℝ) ^ 2) - Real.exp (-Real.pi * x * (n.1 : ℝ) ^ 2)| *
            1 := mul_le_mul_of_nonneg_left hc (mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
              (abs_nonneg _))
      _ = _ := mul_one _
  refine (norm_tsum_le_tsum_norm ?_).trans ?_
  · exact Summable.of_nonneg_of_le (fun n => norm_nonneg _) hdiff (summable_atomicAnchorTerm hx hy)
  · exact (Summable.of_nonneg_of_le (fun n => norm_nonneg _) hdiff
      (summable_atomicAnchorTerm hx hy)).tsum_le_tsum hdiff (summable_atomicAnchorTerm hx hy)

/-- The atomic anchor variation tends to zero. -/
theorem tendsto_gaussianAtomicAnchorVariation {x : ℝ} (hx : 0 < x) :
    Tendsto (gaussianAtomicAnchorVariation x) (𝓝 x) (𝓝 0) := by
  have hx2 : 0 < x / 2 := by positivity
  have hbound := (summable_vonMangoldt_mul_gaussian hx2).mul_left 2
  have h := tendsto_tsum_of_dominated_convergence (𝓕 := 𝓝 x)
    (f := fun y (n : GaussianEulerIndex) => ArithmeticFunction.vonMangoldt n.1 *
      |Real.exp (-Real.pi * y * (n.1 : ℝ) ^ 2) - Real.exp (-Real.pi * x * (n.1 : ℝ) ^ 2)|)
    (g := fun _ => 0) hbound ?_ ?_
  · simp only [tsum_zero] at h
    exact h
  · intro n
    have hc : Continuous fun y : ℝ => ArithmeticFunction.vonMangoldt n.1 *
        |Real.exp (-Real.pi * y * (n.1 : ℝ) ^ 2) - Real.exp (-Real.pi * x * (n.1 : ℝ) ^ 2)| := by
      fun_prop
    simpa using hc.tendsto x
  · filter_upwards [Ioi_mem_nhds (show x / 2 < x by linarith)] with y hy n
    have hy' : x / 2 < y := hy
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
      (abs_nonneg _))]
    have hn0 : (0 : ℝ) ≤ (n.1 : ℝ) ^ 2 := sq_nonneg _
    have hp := mul_nonneg Real.pi_pos.le hn0
    have e1 : Real.exp (-Real.pi * y * (n.1 : ℝ) ^ 2) ≤
        Real.exp (-Real.pi * (x / 2) * (n.1 : ℝ) ^ 2) := by
      apply Real.exp_le_exp.2; nlinarith [mul_nonneg hp (sub_nonneg.2 hy'.le)]
    have e2 : Real.exp (-Real.pi * x * (n.1 : ℝ) ^ 2) ≤
        Real.exp (-Real.pi * (x / 2) * (n.1 : ℝ) ^ 2) := by
      apply Real.exp_le_exp.2; nlinarith [mul_nonneg hp hx2.le]
    have habs : |Real.exp (-Real.pi * y * (n.1 : ℝ) ^ 2) - Real.exp (-Real.pi * x * (n.1 : ℝ) ^ 2)|
        ≤ 2 * Real.exp (-Real.pi * (x / 2) * (n.1 : ℝ) ^ 2) := by
      refine (abs_sub _ _).trans ?_
      rw [abs_of_pos (Real.exp_pos _), abs_of_pos (Real.exp_pos _)]
      linarith
    calc ArithmeticFunction.vonMangoldt n.1 * |_|
        ≤ ArithmeticFunction.vonMangoldt n.1 * (2 * Real.exp (-Real.pi * (x / 2) * (n.1 : ℝ) ^ 2)) :=
          mul_le_mul_of_nonneg_left habs ArithmeticFunction.vonMangoldt_nonneg
      _ = 2 * (ArithmeticFunction.vonMangoldt n.1 *
          Real.exp (-Real.pi * (x / 2) * (n.1 : ℝ) ^ 2)) := by ring

/-! ## The continuum channel -/

/-- Continuum anchor variation `∫₁^∞ |e^{-πyu²} - e^{-πxu²}| du`. -/
def gaussianContinuumAnchorVariation (x y : ℝ) : ℝ :=
  ∫ u in Ici (1 : ℝ), |Real.exp (-Real.pi * y * u ^ 2) - Real.exp (-Real.pi * x * u ^ 2)|

theorem integrableOn_gaussian {y : ℝ} (hy : 0 < y) :
    IntegrableOn (fun u : ℝ => Real.exp (-Real.pi * y * u ^ 2)) (Ici 1) := by
  have h := integrable_exp_neg_mul_sq (mul_pos Real.pi_pos hy)
  refine (h.congr (Eventually.of_forall fun u => ?_)).integrableOn
  simp only [neg_mul]

theorem integrableOn_gaussianContinuumIntegrand {y : ℝ} (hy : 0 < y) {s : ℂ} (hs : 0 ≤ s.re) :
    IntegrableOn (gaussianContinuumIntegrand y s) (Ici 1) := by
  refine (integrableOn_gaussian hy).mono' ?_ ?_
  · exact ((by fun_prop : Continuous fun u : ℝ => (Real.exp (-Real.pi * y * u ^ 2) : ℂ)).measurable.mul
      (Complex.measurable_ofReal.pow_const (-s))).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ici] with u hu
    rw [gaussianContinuumIntegrand, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
    exact mul_le_of_le_one_right (Real.exp_pos _).le (norm_natCast_cpow_neg_le_one hu hs)

/-- The continuum current moves by at most the continuum anchor variation on `Re s ≥ 0`. -/
theorem norm_gaussianContinuumCurrent_sub_le {x y : ℝ} (hx : 0 < x) (hy : 0 < y) {s : ℂ}
    (hs : 0 ≤ s.re) :
    ‖gaussianContinuumCurrent y s - gaussianContinuumCurrent x s‖ ≤
      gaussianContinuumAnchorVariation x y := by
  rw [gaussianContinuumCurrent, gaussianContinuumCurrent,
    ← integral_sub (integrableOn_gaussianContinuumIntegrand hy hs)
      (integrableOn_gaussianContinuumIntegrand hx hs)]
  refine (norm_integral_le_integral_norm _).trans ?_
  refine setIntegral_mono_on ?_ ?_ measurableSet_Ici fun u hu => ?_
  · exact ((integrableOn_gaussianContinuumIntegrand hy hs).sub
      (integrableOn_gaussianContinuumIntegrand hx hs)).norm
  · exact ((integrableOn_gaussian hy).sub (integrableOn_gaussian hx)).abs
  · rw [gaussianContinuumIntegrand, gaussianContinuumIntegrand, ← sub_mul, norm_mul,
      ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_of_le_one_right (abs_nonneg _) (norm_natCast_cpow_neg_le_one hu hs)

/-- The continuum anchor variation tends to zero. -/
theorem tendsto_gaussianContinuumAnchorVariation {x : ℝ} (hx : 0 < x) :
    Tendsto (gaussianContinuumAnchorVariation x) (𝓝 x) (𝓝 0) := by
  have hx2 : 0 < x / 2 := by positivity
  have h := tendsto_integral_filter_of_dominated_convergence (μ := volume.restrict (Ici (1 : ℝ)))
    (l := 𝓝 x) (F := fun y u => |Real.exp (-Real.pi * y * u ^ 2) - Real.exp (-Real.pi * x * u ^ 2)|)
    (f := fun _ => 0) (fun u => 2 * Real.exp (-Real.pi * (x / 2) * u ^ 2)) ?_ ?_
    ((integrableOn_gaussian hx2).const_mul 2) ?_
  · simp only [integral_zero] at h
    exact h
  · exact Eventually.of_forall fun y => (by fun_prop : Continuous fun u : ℝ =>
      |Real.exp (-Real.pi * y * u ^ 2) - Real.exp (-Real.pi * x * u ^ 2)|).aestronglyMeasurable
  · filter_upwards [Ioi_mem_nhds (show x / 2 < x by linarith)] with y hy
    refine Eventually.of_forall fun u => ?_
    have hy' : x / 2 < y := hy
    have hn0 : (0 : ℝ) ≤ u ^ 2 := sq_nonneg _
    have hp := mul_nonneg Real.pi_pos.le hn0
    have e1 : Real.exp (-Real.pi * y * u ^ 2) ≤ Real.exp (-Real.pi * (x / 2) * u ^ 2) := by
      apply Real.exp_le_exp.2; nlinarith [mul_nonneg hp (sub_nonneg.2 hy'.le)]
    have e2 : Real.exp (-Real.pi * x * u ^ 2) ≤ Real.exp (-Real.pi * (x / 2) * u ^ 2) := by
      apply Real.exp_le_exp.2; nlinarith [mul_nonneg hp hx2.le]
    rw [Real.norm_eq_abs, abs_abs]
    refine (abs_sub _ _).trans ?_
    rw [abs_of_pos (Real.exp_pos _), abs_of_pos (Real.exp_pos _)]
    linarith
  · refine Eventually.of_forall fun u => ?_
    have hc : Continuous fun y : ℝ =>
        |Real.exp (-Real.pi * y * u ^ 2) - Real.exp (-Real.pi * x * u ^ 2)| := by fun_prop
    simpa using hc.tendsto x

/-- **Anchor continuity of the formation current.**  For every `x > 0` and `ε > 0`, eventually in
`y → x` one has `‖logDeriv Φ_y s - logDeriv Φ_x s‖ ≤ ε` for every `s` with `Re s > 0`. -/
theorem eventually_norm_logDeriv_gaussianFormation_sub_le {x : ℝ} (hx : 0 < x) {ε : ℝ}
    (hε : 0 < ε) :
    ∀ᶠ y in 𝓝 x, 0 < y ∧ ∀ s : ℂ, 0 < s.re →
      ‖logDeriv (gaussianEulerContinuumFormation y) s -
        logDeriv (gaussianEulerContinuumFormation x) s‖ ≤ ε := by
  have hsum := (tendsto_gaussianAtomicAnchorVariation hx).add
    (tendsto_gaussianContinuumAnchorVariation hx)
  rw [zero_add] at hsum
  filter_upwards [Ioi_mem_nhds hx, (tendsto_order.1 hsum).2 ε hε] with y hy hyε
  have hy0 : 0 < y := hy
  refine ⟨hy0, fun s hs => ?_⟩
  rw [logDeriv_gaussianEulerContinuumFormation hy0 hs, logDeriv_gaussianEulerContinuumFormation hx hs]
  have hrw : logDeriv gaussianArchimedeanHalfFactor s - gaussianVonMangoldtCurrent y s +
        gaussianContinuumCurrent y s -
      (logDeriv gaussianArchimedeanHalfFactor s - gaussianVonMangoldtCurrent x s +
        gaussianContinuumCurrent x s) =
      -(gaussianVonMangoldtCurrent y s - gaussianVonMangoldtCurrent x s) +
        (gaussianContinuumCurrent y s - gaussianContinuumCurrent x s) := by ring
  rw [hrw]
  refine (norm_add_le _ _).trans ?_
  rw [norm_neg]
  exact (add_le_add (norm_gaussianVonMangoldtCurrent_sub_le hx hy0 hs.le)
    (norm_gaussianContinuumCurrent_sub_le hx hy0 hs.le)).trans hyε.le

end RHTower
