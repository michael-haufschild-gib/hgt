import GaloisForLFunctions.RHTower.HamburgerStabilityCriticalLine

/-!
# The twisted Hamburger theorem: a constant root-number twist on a half-line

Let `f(s) = Σ a_n n^{-s}` and `E(s) = Γ_ℝ(s) f(s) - β Γ_ℝ(s - 1)` be as in Hamburger's theorem:
continuous on `1/2 ≤ Re s ≤ 3/2`, holomorphic inside and `O(1/(1 + t²))`.  Write the completed
function on the critical line as `Γ_ℝ(s) Φ(Im s / 2) = E(s) + β Γ_ℝ(s - 1)` (so `Φ` is the boundary
value of `f`) and its reflection defect as `Γ_ℝ(s) g(Im s / 2) = Λ(s) - Λ(1 - s)`.

**Theorem** (`coeff_eq_of_critical_line_twisted_defect`).  Suppose that for some `Y ≥ 0` and
`κ ≠ 0`,

* `g = (1 - κ⁻¹) Φ + r'` on `t < -Y`,

with `r'` Abel-sublinear (for instance zero), and that `g` is merely polynomially bounded on
`t ≥ -Y`.  Then every coefficient equals `2κβ`.

With `r' = 0` the hypothesis says that `Λ(1 - s) = κ⁻¹ Λ(s)` on the lower part of the critical
line, and nothing is assumed on the upper part.  For real coefficients the two parts are conjugate,
so the hypothesis says that the phase of `Λ(1/2 + iy)` is eventually constant modulo `π`.  Hamburger's
conclusion survives a non-real constant root number on one half-line.  With `κ = 1` the
hypothesis is weaker than the sublinear one of `coeff_eq_of_critical_line_even_sublinear_defect` on
the lower half-line and absent on the upper one.

**Proof.**
* The critical-line inverse Mellin integral of `θ`, together with the Mellin inversion of
  `x^{-1/2}(e^{-πx} - 1)` (whose transform is `Γ_ℝ(s - 1)`), gives `θ(x) - β x^{-1/2} = K_Φ(x)`.
  The Laplace step then gives `L(τ) = β + J_Φ(τ)`, where `J_h(τ) = (1/2π) ∫ h(t) k(2t, τ) dt`.
* The defect relation gives `L(τ) = S(τ) - β/(πτ) + β + J_g(τ)`, where `S(τ) = Σ a_n e^{-2πnτ}` is
  `i`-periodic.
* Split `J_h` along `t > Y`, `t < -Y`, `|t| ≤ Y` and eliminate the lower piece of `J_Φ`:
  `L = κ S - (κβ/π)/τ + β + K₀`, where `K₀` contains only upper pieces, bounded pieces and the
  lower remainder.
* For `v ≥ 0`, `Re τ > 0` and `Im τ ≥ 0` one has `arg(πτ²) ≥ 0`, hence the one-sided damping
  `‖k(v, τ)‖ ≤ 3 ‖τ‖^{-1/2} e^{-πv/2}` (`norm_pairKernel_le_of_nonneg`).  Upper pieces therefore
  vanish radially at every `i m`, whatever the defect there.  Bounded pieces and the remainder
  vanish radially by the Abel condition.
* Hamburger's periodicity/residue comparison with `c = -κβ/π` gives `a_n = -2πc = 2κβ`.
-/

open Complex Metric Set Filter Topology MeasureTheory

namespace RHTower

namespace HamburgerTwisted

open GaloisForLFunctions.HTGeometry HamburgerStability

noncomputable section

/-- **One-sided damping of the Laplace kernel.**  For `v ≥ 0`, `Re τ > 0` and `Im τ ≥ 0`,
`‖k(v, τ)‖ ≤ 3 ‖τ‖^{-1/2} e^{-πv/2}`. -/
theorem norm_pairKernel_le_of_nonneg {v : ℝ} (hv : 0 ≤ v) {τ : ℂ} (hτre : 0 < τ.re)
    (hτim : 0 ≤ τ.im) :
    ‖pairKernel v τ‖ ≤ 3 * ‖τ‖ ^ (-(1 / 2 : ℝ)) * Real.exp (-(Real.pi * v / 2)) := by
  have hτ : τ ≠ 0 := by intro h; rw [h] at hτre; simp at hτre
  have hpi := Real.pi_pos
  have hτpos : 0 < ‖τ‖ := norm_pos_iff.mpr hτ
  have hz0 : (Real.pi : ℂ) * τ ^ 2 ≠ 0 :=
    mul_ne_zero (by exact_mod_cast hpi.ne') (pow_ne_zero 2 hτ)
  set w : ℂ := -(1 - HamburgerStability.linePt v / 2) with hw
  have hwre : w.re = -(3 / 4) := by
    rw [hw]; simp only [neg_re, sub_re, one_re, div_re, HamburgerStability.linePt_re]; simp; norm_num
  have hwim : w.im = v / 2 := by rw [hw, HamburgerStability.linePt]; simp
  have harg : 0 ≤ ((Real.pi : ℂ) * τ ^ 2).arg := by
    rw [Complex.arg_nonneg_iff]
    have : ((Real.pi : ℂ) * τ ^ 2).im = Real.pi * (2 * τ.re * τ.im) := by
      simp [pow_two, mul_im]; ring
    rw [this]
    exact mul_nonneg hpi.le (mul_nonneg (mul_nonneg zero_le_two hτre.le) hτim)
  have hcpow : ‖((Real.pi : ℂ) * τ ^ 2) ^ w‖ ≤
      Real.pi ^ (-(3 / 4 : ℝ)) * ‖τ‖ ^ (-(3 / 2 : ℝ)) := by
    rw [Complex.norm_cpow_of_ne_zero hz0, hwre, hwim]
    have hnorm : ‖(Real.pi : ℂ) * τ ^ 2‖ = Real.pi * ‖τ‖ ^ 2 := by
      rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpi]
    rw [hnorm, Real.mul_rpow hpi.le (by positivity), ← Real.rpow_natCast,
      ← Real.rpow_mul hτpos.le]
    have e2 : ((2 : ℕ) : ℝ) * (-(3 / 4 : ℝ)) = -(3 / 2 : ℝ) := by norm_num
    rw [e2]
    have h1 : 1 ≤ Real.exp (((Real.pi : ℂ) * τ ^ 2).arg * (v / 2)) :=
      Real.one_le_exp (mul_nonneg harg (by linarith))
    rw [div_le_iff₀ (Real.exp_pos _)]
    have hA : 0 ≤ Real.pi ^ (-(3 / 4 : ℝ)) * ‖τ‖ ^ (-(3 / 2 : ℝ)) := by positivity
    nlinarith
  have hg := norm_gammaPair_le v
  have habs : |v| = v := abs_of_nonneg hv
  rw [habs] at hg
  have hsqrt0 : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hπ1 : Real.pi ^ (-(1 / 4 : ℝ)) * Real.pi ^ (-(3 / 4 : ℝ)) = Real.pi⁻¹ := by
    rw [← Real.rpow_add hpi]; norm_num; exact Real.rpow_neg_one _
  have hτ1 : ‖τ‖ * ‖τ‖ ^ (-(3 / 2 : ℝ)) = ‖τ‖ ^ (-(1 / 2 : ℝ)) := by
    rw [show ‖τ‖ ^ (-(1 / 2 : ℝ)) = ‖τ‖ ^ ((1 : ℝ) + (-(3 / 2 : ℝ))) by norm_num,
      Real.rpow_add hτpos, Real.rpow_one]
  have hEinv : (Real.exp (Real.pi * v / 2))⁻¹ = Real.exp (-(Real.pi * v / 2)) :=
    (Real.exp_neg _).symm
  unfold pairKernel
  rw [norm_mul, norm_mul]
  calc ‖gammaPair v‖ * (‖τ‖ * ‖((Real.pi : ℂ) * τ ^ 2) ^ (-(1 - HamburgerStability.linePt v / 2))‖)
      ≤ (Real.pi ^ (-(1 / 4 : ℝ)) * (Real.pi * (4 / Real.sqrt 2)) *
          (Real.exp (Real.pi * v / 2))⁻¹) *
        (‖τ‖ * (Real.pi ^ (-(3 / 4 : ℝ)) * ‖τ‖ ^ (-(3 / 2 : ℝ)))) :=
        mul_le_mul hg (mul_le_mul_of_nonneg_left hcpow (norm_nonneg _))
          (by positivity) (by positivity)
    _ = (Real.pi ^ (-(1 / 4 : ℝ)) * Real.pi ^ (-(3 / 4 : ℝ))) * Real.pi * (4 / Real.sqrt 2) *
        (‖τ‖ * ‖τ‖ ^ (-(3 / 2 : ℝ))) * (Real.exp (Real.pi * v / 2))⁻¹ := by ring
    _ = (4 / Real.sqrt 2) * ‖τ‖ ^ (-(1 / 2 : ℝ)) * Real.exp (-(Real.pi * v / 2)) := by
        rw [hπ1, hτ1, hEinv, inv_mul_cancel₀ hpi.ne']; ring
    _ ≤ 3 * ‖τ‖ ^ (-(1 / 2 : ℝ)) * Real.exp (-(Real.pi * v / 2)) := by
        gcongr
        rw [div_le_iff₀ hsqrt0]; nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)]

/-- **Upper pieces vanish radially.**  For polynomially bounded `h` and `Y ≥ 0`,
`ε J_{h 1_{t > Y}}(ε + i m) → 0` as `ε → 0⁺`, for every `m ≥ 0`, with no growth condition beyond
the polynomial bound. -/
theorem tendsto_mul_defectLaplace_upper_radial {h : ℝ → ℂ} {Ch : ℝ} {N : ℕ}
    (hhm : AEStronglyMeasurable h volume) (hhb : ∀ t, ‖h t‖ ≤ Ch * (1 + |t|) ^ N)
    {Y : ℝ} (hY : 0 ≤ Y) (m : ℕ) :
    Tendsto (fun ε : ℝ => (ε : ℂ) * defectLaplace ((Ioi Y).indicator h) ((ε : ℂ) + (m : ℂ) * I))
      (𝓝[>] 0) (𝓝 0) := by
  have hpi := Real.pi_pos
  set A : ℝ := ∫ t : ℝ, ‖h t‖ * Real.exp (-(Real.pi * |t|)) with hA
  have hAint : Integrable fun t : ℝ => ‖h t‖ * Real.exp (-(Real.pi * |t|)) :=
    integrable_abelMass hhm hhb hpi
  have hA0 : 0 ≤ A := integral_nonneg fun t => by positivity
  have hbound : ∀ ε : ℝ, 0 < ε →
      ‖(ε : ℂ) * defectLaplace ((Ioi Y).indicator h) ((ε : ℂ) + (m : ℂ) * I)‖ ≤
        3 / (2 * Real.pi) * A * ε ^ (1 / 2 : ℝ) := by
    intro ε hε
    set τ : ℂ := (ε : ℂ) + (m : ℂ) * I with hτ
    have hτre : 0 < τ.re := by simp [hτ, hε]
    have hτim : 0 ≤ τ.im := by simp [hτ]
    have hτn : ε ≤ ‖τ‖ := by
      have h1 := Complex.re_le_norm τ
      have h2 : τ.re = ε := by simp [hτ]
      linarith
    have hpow : ‖τ‖ ^ (-(1 / 2 : ℝ)) ≤ ε ^ (-(1 / 2 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos hε hτn (by norm_num)
    have hint := hAint.const_mul (3 * ‖τ‖ ^ (-(1 / 2 : ℝ)))
    have hle := norm_integral_le_of_norm_le
      (f := fun t => (Ioi Y).indicator h t * pairKernel (2 * t) τ) hint
      (Eventually.of_forall fun t => by
        rw [norm_mul]
        by_cases ht : t ∈ Ioi Y
        · rw [Set.indicator_of_mem ht]
          have htY : Y < t := ht
          have ht0 : 0 ≤ 2 * t := by linarith
          have hk := norm_pairKernel_le_of_nonneg ht0 hτre hτim
          have habs : |t| = t := abs_of_nonneg (by linarith)
          calc ‖h t‖ * ‖pairKernel (2 * t) τ‖ ≤ ‖h t‖ *
                (3 * ‖τ‖ ^ (-(1 / 2 : ℝ)) * Real.exp (-(Real.pi * (2 * t) / 2))) :=
                mul_le_mul_of_nonneg_left hk (norm_nonneg _)
            _ = 3 * ‖τ‖ ^ (-(1 / 2 : ℝ)) * (‖h t‖ * Real.exp (-(Real.pi * |t|))) := by
                rw [habs, show Real.pi * (2 * t) / 2 = Real.pi * t by ring]; ring
        · rw [Set.indicator_of_notMem ht, norm_zero, zero_mul]
          positivity)
    rw [integral_const_mul] at hle
    unfold defectLaplace
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    calc ε * (1 / (2 * Real.pi) * ‖∫ t : ℝ, (Ioi Y).indicator h t * pairKernel (2 * t) τ‖)
        ≤ ε * (1 / (2 * Real.pi) * (3 * ‖τ‖ ^ (-(1 / 2 : ℝ)) * A)) := by gcongr
      _ ≤ ε * (1 / (2 * Real.pi) * (3 * ε ^ (-(1 / 2 : ℝ)) * A)) := by gcongr
      _ = 3 / (2 * Real.pi) * A * (ε * ε ^ (-(1 / 2 : ℝ))) := by ring
      _ = 3 / (2 * Real.pi) * A * ε ^ (1 / 2 : ℝ) := by
          congr 1
          have key : ε ^ (1 / 2 : ℝ) = ε ^ (1 : ℝ) * ε ^ (-(1 / 2 : ℝ)) := by
            rw [← Real.rpow_add hε]; norm_num
          rw [key, Real.rpow_one]
  have hlim : Tendsto (fun ε : ℝ => 3 / (2 * Real.pi) * A * ε ^ (1 / 2 : ℝ)) (𝓝[>] 0)
      (𝓝 0) := by
    have hc : ContinuousAt (fun ε : ℝ => ε ^ (1 / 2 : ℝ)) 0 :=
      Real.continuousAt_rpow_const 0 (1 / 2) (Or.inr (by norm_num))
    have h0 : Tendsto (fun ε : ℝ => ε ^ (1 / 2 : ℝ)) (𝓝[>] 0) (𝓝 0) := by
      have := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
      simpa [Real.zero_rpow (by norm_num : (1 / 2 : ℝ) ≠ 0)] using this
    simpa using h0.const_mul (3 / (2 * Real.pi) * A)
  exact squeeze_zero_norm' (by
    filter_upwards [self_mem_nhdsWithin] with ε hε using hbound ε hε) hlim

/-- A polynomially bounded function supported in `[-Y, Y]` is Abel-sublinear. -/
theorem tendsto_mul_abelMass_indicator_Icc {h : ℝ → ℂ} {Ch : ℝ} {N : ℕ}
    (hhm : AEStronglyMeasurable h volume) (hhb : ∀ t, ‖h t‖ ≤ Ch * (1 + |t|) ^ N) (Y : ℝ) :
    Tendsto (fun δ => δ * abelMass ((Icc (-Y) Y).indicator h) δ) (𝓝[>] 0) (𝓝 0) := by
  have hCh : 0 ≤ Ch := by
    have := (norm_nonneg _).trans (hhb 0)
    simpa using this
  set F : ℝ → ℝ := fun t => Ch * (1 + |t|) ^ N with hF
  have hFc : Continuous F := by rw [hF]; fun_prop
  have hFint : Integrable ((Icc (-Y) Y).indicator F) :=
    (hFc.integrableOn_Icc).integrable_indicator measurableSet_Icc
  set B : ℝ := ∫ t : ℝ, (Icc (-Y) Y).indicator F t with hB
  have hbd : ∀ δ : ℝ, 0 < δ → abelMass ((Icc (-Y) Y).indicator h) δ ≤ B := by
    intro δ hδ
    unfold abelMass
    refine integral_mono (integrable_abelMass (hhm.indicator measurableSet_Icc)
      (fun t => (norm_indicator_le_norm_self h t).trans (hhb t)) hδ) hFint fun t => ?_
    by_cases ht : t ∈ Icc (-Y) Y
    · rw [Set.indicator_of_mem ht, Set.indicator_of_mem ht]
      calc ‖h t‖ * Real.exp (-(δ * |t|)) ≤ ‖h t‖ * 1 :=
            mul_le_mul_of_nonneg_left (Real.exp_le_one_iff.mpr (by
              have := abs_nonneg t; nlinarith)) (norm_nonneg _)
        _ ≤ F t := by rw [mul_one]; exact hhb t
    · rw [Set.indicator_of_notMem ht, Set.indicator_of_notMem ht, norm_zero, zero_mul]
  have hlim : Tendsto (fun δ : ℝ => δ * B) (𝓝[>] 0) (𝓝 0) := by
    have h0 : Tendsto (fun δ : ℝ => δ * B) (𝓝 (0 : ℝ)) (𝓝 (0 * B)) := tendsto_id.mul_const B
    rw [zero_mul] at h0
    exact h0.mono_left nhdsWithin_le_nhds
  refine squeeze_zero' ?_ ?_ hlim
  · filter_upwards [self_mem_nhdsWithin] with δ hδ
    exact mul_nonneg (le_of_lt hδ) (integral_nonneg fun t => by positivity)
  · filter_upwards [self_mem_nhdsWithin] with δ hδ
    exact mul_le_mul_of_nonneg_left (hbd δ hδ) (le_of_lt hδ)

/-- Restricting an Abel-sublinear function to a measurable set keeps it Abel-sublinear. -/
theorem tendsto_mul_abelMass_indicator {h : ℝ → ℂ} {Ch : ℝ} {N : ℕ}
    (hhm : AEStronglyMeasurable h volume) (hhb : ∀ t, ‖h t‖ ≤ Ch * (1 + |t|) ^ N)
    (hA : Tendsto (fun δ => δ * abelMass h δ) (𝓝[>] 0) (𝓝 0)) {s : Set ℝ}
    (hs : MeasurableSet s) :
    Tendsto (fun δ => δ * abelMass (s.indicator h) δ) (𝓝[>] 0) (𝓝 0) := by
  refine squeeze_zero' ?_ ?_ hA
  · filter_upwards [self_mem_nhdsWithin] with δ hδ
    exact mul_nonneg (le_of_lt hδ) (integral_nonneg fun t => by positivity)
  · filter_upwards [self_mem_nhdsWithin] with δ hδ
    refine mul_le_mul_of_nonneg_left ?_ (le_of_lt hδ)
    unfold abelMass
    refine integral_mono (integrable_abelMass (hhm.indicator hs)
      (fun t => (norm_indicator_le_norm_self h t).trans (hhb t)) hδ)
      (integrable_abelMass hhm hhb hδ) fun t => ?_
    exact mul_le_mul_of_nonneg_right (norm_indicator_le_norm_self h t) (by positivity)

/-- `J_h = J_{h 1_{t > Y}} + J_{h 1_{t < -Y}} + J_{h 1_{|t| ≤ Y}}`. -/
theorem defectLaplace_split {h : ℝ → ℂ} {Ch : ℝ} {N : ℕ}
    (hhm : AEStronglyMeasurable h volume) (hhb : ∀ t, ‖h t‖ ≤ Ch * (1 + |t|) ^ N)
    {Y : ℝ} (hY : 0 ≤ Y) {τ : ℂ} (hτ : 0 < τ.re) :
    defectLaplace h τ = defectLaplace ((Ioi Y).indicator h) τ +
      defectLaplace ((Iio (-Y)).indicator h) τ + defectLaplace ((Icc (-Y) Y).indicator h) τ := by
  have hb : ∀ s : Set ℝ, ∀ t, ‖s.indicator h t‖ ≤ Ch * (1 + |t|) ^ N :=
    fun s t => (norm_indicator_le_norm_self h t).trans (hhb t)
  have i1 := integrable_defectLaplace_integrand
    (hhm.indicator (measurableSet_Ioi (a := Y))) (hb _) hτ
  have i2 := integrable_defectLaplace_integrand
    (hhm.indicator (measurableSet_Iio (a := -Y))) (hb _) hτ
  have i3 := integrable_defectLaplace_integrand
    (hhm.indicator (measurableSet_Icc (a := -Y) (b := Y))) (hb _) hτ
  have hpt : ∀ t, h t * pairKernel (2 * t) τ =
      ((Ioi Y).indicator h t * pairKernel (2 * t) τ +
        (Iio (-Y)).indicator h t * pairKernel (2 * t) τ) +
          (Icc (-Y) Y).indicator h t * pairKernel (2 * t) τ := by
    intro t
    by_cases h1 : Y < t
    · have h2 : t ∉ Iio (-Y) := fun h' => by
        have : t < -Y := h'
        linarith
      have h3 : t ∉ Icc (-Y) Y := fun h' => by linarith [h'.2]
      rw [Set.indicator_of_mem (show t ∈ Ioi Y from h1), Set.indicator_of_notMem h2,
        Set.indicator_of_notMem h3]
      ring
    · by_cases h2 : t < -Y
      · have h1' : t ∉ Ioi Y := h1
        have h3 : t ∉ Icc (-Y) Y := fun h' => by linarith [h'.1]
        rw [Set.indicator_of_notMem h1', Set.indicator_of_mem (show t ∈ Iio (-Y) from h2),
          Set.indicator_of_notMem h3]
        ring
      · have h1' : t ∉ Ioi Y := h1
        have h2' : t ∉ Iio (-Y) := h2
        have h3 : t ∈ Icc (-Y) Y := ⟨not_lt.mp h2, not_lt.mp h1⟩
        rw [Set.indicator_of_notMem h1', Set.indicator_of_notMem h2',
          Set.indicator_of_mem h3]
        ring
  have h12 : Integrable (fun t => (Ioi Y).indicator h t * pairKernel (2 * t) τ +
      (Iio (-Y)).indicator h t * pairKernel (2 * t) τ) := i1.add i2
  unfold defectLaplace
  rw [integral_congr_ae (Eventually.of_forall hpt), integral_add h12 i3, integral_add i1 i2]
  ring

/-- Linearity of `J` on a piece: if `g = c Φ + r` on `s`, then
`J_{g 1_s} = c J_{Φ 1_s} + J_{r 1_s}`. -/
theorem defectLaplace_indicator_eq {g Φ r : ℝ → ℂ} {Cg : ℝ} {N : ℕ}
    (hΦm : AEStronglyMeasurable Φ volume) (hΦb : ∀ t, ‖Φ t‖ ≤ Cg * (1 + |t|) ^ N)
    (hrm : AEStronglyMeasurable r volume) (hrb : ∀ t, ‖r t‖ ≤ Cg * (1 + |t|) ^ N)
    {s : Set ℝ} (hs : MeasurableSet s) (c : ℂ) (hg : ∀ t ∈ s, g t = c * Φ t + r t)
    {τ : ℂ} (hτ : 0 < τ.re) :
    defectLaplace (s.indicator g) τ =
      c * defectLaplace (s.indicator Φ) τ + defectLaplace (s.indicator r) τ := by
  have iΦ := integrable_defectLaplace_integrand (hΦm.indicator hs)
    (fun t => (norm_indicator_le_norm_self Φ t).trans (hΦb t)) hτ
  have ir := integrable_defectLaplace_integrand (hrm.indicator hs)
    (fun t => (norm_indicator_le_norm_self r t).trans (hrb t)) hτ
  have hpt : ∀ t, s.indicator g t * pairKernel (2 * t) τ =
      c * (s.indicator Φ t * pairKernel (2 * t) τ) + s.indicator r t * pairKernel (2 * t) τ := by
    intro t
    by_cases ht : t ∈ s
    · rw [Set.indicator_of_mem ht, Set.indicator_of_mem ht, Set.indicator_of_mem ht, hg t ht]
      ring
    · rw [Set.indicator_of_notMem ht, Set.indicator_of_notMem ht, Set.indicator_of_notMem ht]
      ring
  unfold defectLaplace
  rw [integral_congr_ae (Eventually.of_forall hpt), integral_add (iΦ.const_mul c) ir,
    integral_const_mul]
  ring

/-- **The critical-line inverse Mellin integral of `θ`, polar part included.**  If
`Γ_ℝ(s) Φ(Im s / 2) = E(s) + β Γ_ℝ(s - 1)` on the critical line, then
`θ(x) - β x^{-1/2} = (1/2π) ∫ x^{-(1/4+it)} Γ_ℝ(1/2 + 2it) Φ(t) dt`.  The polar term
`β x^{-1/2} e^{-πx}` of `critical_line_inverse_mellin` combines with the Mellin inversion of
`x^{-1/2}(e^{-πx} - 1)`, whose transform on the critical line is `Γ_ℝ(s - 1)`. -/
theorem coeffTheta_eq_defectKernel {a : ℕ → ℂ}
    (ha : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => ‖a (n + 1)‖ / ((n : ℝ) + 1) ^ σ)
    {E : ℂ → ℂ} {β : ℂ} {C : ℝ} {Φ : ℝ → ℂ}
    (hEc : ContinuousOn E (verticalStrip (1 / 2) (3 / 2)))
    (hEd : DifferentiableOn ℂ E {s : ℂ | 1 / 2 < s.re ∧ s.re < 3 / 2})
    (hdecay : ∀ s ∈ verticalStrip (1 / 2) (3 / 2), ‖E s‖ ≤ C / (1 + s.im ^ 2))
    (hR : ∀ s : ℂ, s.re = 3 / 2 →
      Complex.Gammaℝ s * coeffDirichlet a s = E s + β * Complex.Gammaℝ (s - 1))
    (hΦ : ∀ t : ℝ, E (2 * (((1 / 4 : ℝ) : ℂ) + t * I)) +
      β * Complex.Gammaℝ (2 * (((1 / 4 : ℝ) : ℂ) + t * I) - 1) =
        Complex.Gammaℝ (2 * (((1 / 4 : ℝ) : ℂ) + t * I)) * Φ t)
    {x : ℝ} (hx : 0 < x) :
    coeffTheta a x = β * (x : ℂ) ^ (-(1 / 2 : ℂ)) + defectKernel Φ x := by
  have hθc : ContinuousOn (coeffTheta a) (Ioi 0) := continuousOn_coeffTheta a (ha 2 (by norm_num))
  have hθm : MellinConvergent (coeffTheta a) (3 / 4) :=
    mellinConvergent_coeffTheta a ha (by norm_num) (by norm_num)
  have hR' : ∀ s : ℂ, s.re = 3 / 2 →
      mellin (coeffTheta a) (s / 2) = E s + β * Complex.Gammaℝ (s - 1) := by
    intro s hs
    rw [mellin_coeffTheta a ha (by rw [hs]; norm_num)]
    exact hR s hs
  have h1 := critical_line_inverse_mellin hθc hθm hEc hEd hdecay hR' hx
  rw [Complex.real_smul] at h1
  set f₀ : ℝ → ℂ := fun y => (y : ℂ) ^ (-(1 / 2 : ℂ)) * expNegSubOne (Real.pi * y) with hf₀
  have hM : ∀ t : ℝ, HasMellin f₀ (((1 / 4 : ℝ) : ℂ) + t * I)
      (Complex.Gammaℝ (2 * (((1 / 4 : ℝ) : ℂ) + t * I) - 1)) := by
    intro t
    have h := hasMellin_halfPow_expNegSubOne_pi (s := 2 * (((1 / 4 : ℝ) : ℂ) + t * I))
      (by simp; norm_num) (by simp; norm_num)
    rwa [show 2 * (((1 / 4 : ℝ) : ℂ) + t * I) / 2 = ((1 / 4 : ℝ) : ℂ) + t * I by ring] at h
  have hconv : MellinConvergent f₀ ((1 / 4 : ℝ) : ℂ) := by
    have := (hM 0).1
    simpa using this
  have hGint : ∀ {y : ℝ}, 0 < y → ∀ σ : ℝ, Integrable fun t : ℝ =>
      (y : ℂ) ^ (-((σ : ℂ) + t * I)) * Complex.Gammaℝ (2 * (((1 / 4 : ℝ) : ℂ) + t * I) - 1) := by
    intro y hy σ
    have h := integrable_cpow_mul_Gammaℝ_line (σ := σ) (a := -(1 / 2)) (c := 2) (x := y)
      hy two_ne_zero (fun k hk => by
        have h4 : (4 * k : ℝ) = 1 := by linarith
        have : (4 * k : ℕ) = 1 := by exact_mod_cast h4
        omega)
    have e : ∀ t : ℝ, (((-(1 / 2) : ℝ) : ℂ) + ((2 * t : ℝ) : ℂ) * I) =
        2 * (((1 / 4 : ℝ) : ℂ) + t * I) - 1 := fun t => by push_cast; ring
    simp only [e] at h
    exact h
  have hvert : VerticalIntegrable (mellin f₀) (1 / 4) volume := by
    unfold VerticalIntegrable
    have h := hGint one_pos 0
    simp only [ofReal_one, one_cpow, one_mul] at h
    refine h.congr (Eventually.of_forall fun t => ?_)
    exact ((hM t).2).symm
  have hcont : ContinuousAt f₀ x := by
    refine ContinuousAt.mul ((continuousAt_cpow_const (Complex.ofReal_mem_slitPlane.mpr hx)).comp
      Complex.continuous_ofReal.continuousAt) ?_
    unfold expNegSubOne
    fun_prop
  have h2 := mellinInv_mellin_eq (1 / 4) f₀ hx hconv hvert hcont
  unfold mellinInv at h2
  rw [Complex.real_smul] at h2
  have h2' : ((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ t : ℝ,
      (x : ℂ) ^ (-(((1 / 4 : ℝ) : ℂ) + t * I)) *
        Complex.Gammaℝ (2 * (((1 / 4 : ℝ) : ℂ) + t * I) - 1) = f₀ x := by
    rw [← h2]
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    simp only [smul_eq_mul]
    rw [(hM t).2]
  have hIE : Integrable fun t : ℝ => (x : ℂ) ^ (-(((1 / 4 : ℝ) : ℂ) + t * I)) *
      E (2 * (((1 / 4 : ℝ) : ℂ) + t * I)) :=
    integrable_cpow_mul_comp_line hEc hdecay (by norm_num) (by norm_num) hx
  have hIG := hGint hx (1 / 4)
  have hpt : ∀ t : ℝ, (x : ℂ) ^ (-(((1 / 4 : ℝ) : ℂ) + t * I)) *
      (Complex.Gammaℝ (2 * (((1 / 4 : ℝ) : ℂ) + t * I)) * Φ t) =
      (x : ℂ) ^ (-(((1 / 4 : ℝ) : ℂ) + t * I)) * E (2 * (((1 / 4 : ℝ) : ℂ) + t * I)) +
        β * ((x : ℂ) ^ (-(((1 / 4 : ℝ) : ℂ) + t * I)) *
          Complex.Gammaℝ (2 * (((1 / 4 : ℝ) : ℂ) + t * I) - 1)) := by
    intro t
    rw [← hΦ t]; ring
  have hsplit : defectKernel Φ x = (((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ t : ℝ,
      (x : ℂ) ^ (-(((1 / 4 : ℝ) : ℂ) + t * I)) * E (2 * (((1 / 4 : ℝ) : ℂ) + t * I))) +
      β * (((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ t : ℝ,
        (x : ℂ) ^ (-(((1 / 4 : ℝ) : ℂ) + t * I)) *
          Complex.Gammaℝ (2 * (((1 / 4 : ℝ) : ℂ) + t * I) - 1)) := by
    unfold defectKernel
    rw [integral_congr_ae (Eventually.of_forall hpt), integral_add hIE (hIG.const_mul β),
      integral_const_mul]
    ring
  have hexp : expNegSubOne (Real.pi * x) = expNegPi x - 1 := by
    unfold expNegSubOne expNegPi; push_cast; ring
  rw [hsplit, h2']
  simp only [hf₀, hexp]
  linear_combination h1

/-- **The twisted Hamburger theorem.**  Hamburger's hypotheses on `E`, a polynomially bounded
reflection defect `g` on the critical line and the boundary value `Φ` of `f` there.  If
`g = (1 - κ⁻¹) Φ + r'` for `t < -Y`, with `κ ≠ 0`, `Y ≥ 0` and Abel-sublinear `r'`, then every
coefficient equals `2κβ`.  Nothing is assumed of the defect on `t ≥ -Y` beyond a polynomial
bound. -/
theorem coeff_eq_of_critical_line_twisted_defect {a : ℕ → ℂ}
    (ha : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => ‖a (n + 1)‖ / ((n : ℝ) + 1) ^ σ)
    {E : ℂ → ℂ} {β : ℂ} {C : ℝ} {g Φ r' : ℝ → ℂ} {CB : ℝ} {N : ℕ}
    (hEc : ContinuousOn E (verticalStrip (1 / 2) (3 / 2)))
    (hEd : DifferentiableOn ℂ E {s : ℂ | 1 / 2 < s.re ∧ s.re < 3 / 2})
    (hdecay : ∀ s ∈ verticalStrip (1 / 2) (3 / 2), ‖E s‖ ≤ C / (1 + s.im ^ 2))
    (hR : ∀ s : ℂ, s.re = 3 / 2 →
      Complex.Gammaℝ s * coeffDirichlet a s = E s + β * Complex.Gammaℝ (s - 1))
    (hC : ∀ s : ℂ, s.re = 1 / 2 → E s - E (1 - s) =
      -(β * (Complex.Gammaℝ (s - 1) - Complex.Gammaℝ (-s))) + Complex.Gammaℝ s * g (s.im / 2))
    (hΦ : ∀ t : ℝ, E (2 * (((1 / 4 : ℝ) : ℂ) + t * I)) +
      β * Complex.Gammaℝ (2 * (((1 / 4 : ℝ) : ℂ) + t * I) - 1) =
        Complex.Gammaℝ (2 * (((1 / 4 : ℝ) : ℂ) + t * I)) * Φ t)
    (hgm : Measurable g) (hgb : ∀ t, ‖g t‖ ≤ CB * (1 + |t|) ^ N)
    (hΦm : Measurable Φ) (hΦb : ∀ t, ‖Φ t‖ ≤ CB * (1 + |t|) ^ N)
    (hr'm : Measurable r') (hr'b : ∀ t, ‖r' t‖ ≤ CB * (1 + |t|) ^ N)
    (hr'A : Tendsto (fun δ => δ * abelMass r' δ) (𝓝[>] 0) (𝓝 0))
    {Y : ℝ} (hY : 0 ≤ Y) {κ : ℂ} (hκ : κ ≠ 0)
    (hlow : ∀ t, t < -Y → g t = (1 - κ⁻¹) * Φ t + r' t)
    (n : ℕ) : a (n + 1) = 2 * κ * β := by
  have hgm' := hgm.aestronglyMeasurable (μ := volume)
  have hΦm' := hΦm.aestronglyMeasurable (μ := volume)
  have hr'm' := hr'm.aestronglyMeasurable (μ := volume)
  have hθc : ContinuousOn (coeffTheta a) (Ioi 0) := continuousOn_coeffTheta a (ha 2 (by norm_num))
  have hθm : MellinConvergent (coeffTheta a) (3 / 4) :=
    mellinConvergent_coeffTheta a ha (by norm_num) (by norm_num)
  have hR' : ∀ s : ℂ, s.re = 3 / 2 →
      mellin (coeffTheta a) (s / 2) = E s + β * Complex.Gammaℝ (s - 1) := by
    intro s hs
    rw [mellin_coeffTheta a ha (by rw [hs]; norm_num)]
    exact hR s hs
  have him : ∀ t : ℝ, (2 * (((1 / 4 : ℝ) : ℂ) + t * I)).im / 2 = t := fun t => by simp
  have hdint : Integrable fun t : ℝ => Complex.Gammaℝ (2 * (((1 / 4 : ℝ) : ℂ) + t * I)) *
      g ((2 * (((1 / 4 : ℝ) : ℂ) + t * I)).im / 2) := by
    simp only [him]
    exact integrable_Gammaℝ_mul hgm' hgb
  -- the defect relation and its Laplace transform
  have htheta : ∀ x : ℝ, 0 < x → coeffTheta a x =
      1 * ((x : ℂ) ^ (-(1 / 2 : ℂ)) * coeffTheta a x⁻¹) + -β + β * (x : ℂ) ^ (-(1 / 2 : ℂ)) +
        defectKernel g x := by
    intro x hx
    have h := critical_line_even_theta_relation_defect
      (d := fun s => Complex.Gammaℝ s * g (s.im / 2)) hθc hθm hEc hEd hdecay hR' hC hdint hx
    simp only [him] at h
    unfold defectKernel
    linear_combination h
  have ha2 : Summable fun n : ℕ => ‖a (n + 1)‖ / ((n + 1 : ℕ) : ℝ) ^ 2 := by
    have := summable_sq_of_forall_rpow ha
    simpa using this
  set S : ℂ → ℂ := fun τ => ∑' n : ℕ, a (n + 1) * cexp (-(2 * Real.pi * ((n : ℂ) + 1) * τ))
    with hS
  have hL : ∀ τ : ℂ, 0 < τ.re → hamburgerSeries a τ =
      1 * S τ + -β / (Real.pi * τ) + β + defectLaplace g τ := fun τ hτ =>
    hamburgerSeries_eq_of_coeffTheta_relation_defect a a ha ha htheta
      (fun τ hτ => (defectKernel_laplace hgm hgb hτ).1)
      (differentiableOn_defectLaplace hgm' hgb)
      (fun τ hτ => (defectKernel_laplace hgm hgb hτ).2) hτ
  -- the untwisted identity `L = β + J_Φ`
  have htheta0 : ∀ x : ℝ, 0 < x → coeffTheta a x =
      0 * ((x : ℂ) ^ (-(1 / 2 : ℂ)) * coeffTheta a x⁻¹) + 0 + β * (x : ℂ) ^ (-(1 / 2 : ℂ)) +
        defectKernel Φ x := fun x hx => by
    rw [coeffTheta_eq_defectKernel ha hEc hEd hdecay hR hΦ hx]; ring
  have hL0 : ∀ τ : ℂ, 0 < τ.re → hamburgerSeries a τ = β + defectLaplace Φ τ := by
    intro τ hτ
    have h := hamburgerSeries_eq_of_coeffTheta_relation_defect a a ha ha htheta0
      (fun τ hτ => (defectKernel_laplace hΦm hΦb hτ).1)
      (differentiableOn_defectLaplace hΦm' hΦb)
      (fun τ hτ => (defectKernel_laplace hΦm hΦb hτ).2) hτ
    rw [h]; simp
  -- the pieces
  set U : Set ℝ := Ioi Y with hU
  set Lo : Set ℝ := Iio (-Y) with hLo
  set Mi : Set ℝ := Icc (-Y) Y with hMi
  set K₀ : ℂ → ℂ := fun τ => κ * defectLaplace (U.indicator g) τ -
      (κ - 1) * (defectLaplace (U.indicator Φ) τ + defectLaplace (Mi.indicator Φ) τ) +
      κ * (defectLaplace (Lo.indicator r') τ + defectLaplace (Mi.indicator g) τ) with hK₀
  have hκinv : κ * κ⁻¹ = 1 := mul_inv_cancel₀ hκ
  have hmain : ∀ τ : ℂ, 0 < τ.re →
      hamburgerSeries a τ = κ * S τ - κ * β / Real.pi / τ + β + K₀ τ := by
    intro τ hτ
    have eA := hL τ hτ
    have eB := hL0 τ hτ
    have eC := defectLaplace_split hgm' hgb hY hτ
    have eD := defectLaplace_split hΦm' hΦb hY hτ
    have eF := defectLaplace_indicator_eq (g := g) hΦm'
      (fun t => (hΦb t).trans (le_refl _)) hr'm' hr'b measurableSet_Iio (1 - κ⁻¹)
      (fun t ht => hlow t ht) hτ
    have hτ0 : τ ≠ 0 := by intro h0; rw [h0] at hτ; simp at hτ
    have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    simp only [hK₀]
    rw [show -β / (Real.pi * τ) = -(β / Real.pi / τ) by field_simp] at eA
    linear_combination κ * eA + κ * eC + κ * eF - (κ - 1) * eB - (κ - 1) * eD -
      defectLaplace (Lo.indicator Φ) τ * hκinv
  have hper : ∀ τ : ℂ, 0 < τ.re → hamburgerSeries a (τ + I) - hamburgerSeries a τ =
      -(κ * β / Real.pi) / (τ + I) - -(κ * β / Real.pi) / τ + (K₀ (τ + I) - K₀ τ) := by
    intro τ hτ
    have hτ' : 0 < (τ + I).re := by simpa using hτ
    have hexp : S (τ + I) = S τ := by
      simp only [hS]
      refine tsum_congr fun n => ?_
      rw [show -(2 * (Real.pi : ℂ) * ((n : ℂ) + 1) * (τ + I)) =
        -(2 * Real.pi * ((n : ℂ) + 1) * τ) + ((-((n : ℤ) + 1) : ℤ) : ℂ) * (2 * Real.pi * I) by
          push_cast; ring, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
    rw [hmain τ hτ, hmain (τ + I) hτ', hexp]
    ring
  -- radial vanishing of every piece of `K₀`
  have hmidΦ := tendsto_mul_abelMass_indicator_Icc hΦm' hΦb Y
  have hmidg := tendsto_mul_abelMass_indicator_Icc hgm' hgb Y
  have hrl := tendsto_mul_abelMass_indicator hr'm' hr'b hr'A (measurableSet_Iio (a := -Y))
  have hb : ∀ {h : ℝ → ℂ}, (∀ t, ‖h t‖ ≤ CB * (1 + |t|) ^ N) → ∀ s : Set ℝ, ∀ t,
      ‖s.indicator h t‖ ≤ CB * (1 + |t|) ^ N :=
    fun hh s t => (norm_indicator_le_norm_self _ t).trans (hh t)
  have hK₀rad : ∀ m : ℕ, Tendsto (fun ε : ℝ => (ε : ℂ) * K₀ ((ε : ℂ) + (m : ℂ) * I))
      (𝓝[>] 0) (𝓝 0) := by
    intro m
    have t0 := tendsto_mul_defectLaplace_upper_radial hgm' hgb hY m
    have t1 := tendsto_mul_defectLaplace_upper_radial hΦm' hΦb hY m
    have t2 := tendsto_mul_defectLaplace_radial (hΦm'.indicator measurableSet_Icc)
      (hb hΦb Mi) hmidΦ m
    have t4 := tendsto_mul_defectLaplace_radial (hr'm'.indicator measurableSet_Iio)
      (hb hr'b Lo) hrl m
    have t5 := tendsto_mul_defectLaplace_radial (hgm'.indicator measurableSet_Icc)
      (hb hgb Mi) hmidg m
    have := ((t0.const_mul κ).sub ((t1.add t2).const_mul (κ - 1))).add
      ((t4.add t5).const_mul κ)
    simp only [mul_zero, sub_zero, add_zero] at this
    refine this.congr' (Eventually.of_forall fun ε => ?_)
    simp only [hK₀]
    ring
  have hK : ∀ n₀ : ℕ, Tendsto (fun τ => (τ - (n₀ : ℂ) * I) * (K₀ (τ + I) - K₀ τ))
      (𝓝[{τ : ℂ | 0 < τ.re}] ((n₀ : ℂ) * I)) (𝓝 0) := by
    intro n₀
    refine tendsto_sub_mul_defect_of_radial ha2 (-(κ * β / Real.pi))
      (fun τ => K₀ (τ + I) - K₀ τ) hper n₀ ?_
    have h1 := hK₀rad (n₀ + 1)
    have h0 := hK₀rad n₀
    have := h1.sub h0
    rw [sub_zero] at this
    refine this.congr' (Eventually.of_forall fun ε => ?_)
    push_cast
    ring_nf
  have h := coeff_eq_of_hamburgerSeries_periodic_re_pos_of_defect ha2 (-(κ * β / Real.pi))
    (fun τ => K₀ (τ + I) - K₀ τ) hper hK n
  rw [h]
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp

end

end HamburgerTwisted

end RHTower
