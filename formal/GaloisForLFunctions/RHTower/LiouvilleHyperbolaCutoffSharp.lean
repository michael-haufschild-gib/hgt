import GaloisForLFunctions.RHTower.LiouvilleHyperbolaCutoffThreeQuarter

/-!
# The cutoff transport law at the exact exponent

`LiouvilleHyperbolaCutoffThreeQuarter` shows that for `0 < θ < 3/4`, `c ≠ 0`, the combination
`dP + cA_θ` of the Liouville triangle `P(x) = Σ_{n ≤ x} λ(n)(x/n - 1)` and the Möbius head
`A_θ(x) = Σ_{m ≤ x^θ} μ(m)W(x/m)` exceeds `±C x^β` infinitely often for every `β < 1 - θ/2`. Here
the exponent `1 - θ/2` itself is reached.

* **Rightmost zeros.** On each horizontal line the strip zeros form a finite set; its rightmost
  element `ρ` has no zero `ρ + c`, `c > 0` (`exists_rightmost_zero`). Moving to the rightmost zero
  and contracting `ρ ↦ 1 + θ(ρ - 1)` alternately produces points converging to `1`, so some
  rightmost zero has a nonvanishing contraction (`exists_rightmost_contracted_nonzero`). The
  root-head and Mertens-head arguments at the transported point are right translates of `ρ`.
* **RH from a one-sided bound** (`riemannHypothesis_of_eventually_le`). A zero with `Re ρ > ½` puts
  the transported pole strictly right of `1 - θ/2`, so `η(dP + cA_θ) ≤ C x^{1-θ/2}` for large `x`,
  with any `C`, forces RH. The same zeros extend the exponent law to `θ < 3/4`: oscillation beyond
  every `x^β`, `β < 1 - θ(1 - Θ)` (`frequently_gt_and_frequently_lt_abscissa_tq`).
* **The boundary pole.** Under RH the transported point `w = 1 + θ(ρ - 1)` of a critical zero lies
  on `Re z = 1 - θ/2`. With the one-sided measure of constant `ε`, the continuation identity
  `(ε/(z-β) + K/z - L(z))D₄(z) = η(N₄(z) + cR'_θ(z)D₄(z))` along `z = w + r`, `r ↓ 0`, together
  with `|L(w + r)| ≤ L(β + r) ≤ ε/r + O(1)` and `D₄(z) = (z - w)^m E(z)`, gives
  `|N₄(w)| ≤ ε|E(w)|` (`norm_tqPoleNumerator_le`). A constant below `|N₄(w)|/|E(w)|` is impossible.

**Theorem** (`exists_omega_pm_exact`). For every `0 < θ < 3/4`, real `d` and `c ≠ 0` there is
`δ > 0` with `dP + cA_θ > δ x^{1-θ/2}` and `dP + cA_θ < -δ x^{1-θ/2}` for arbitrarily large `x`.
-/

open Complex Filter MeasureTheory Set Topology
open GaloisForLFunctions.RHTower
open RHTower.LiouvilleTriangularHeadOscillation
open RHTower.LiouvilleHyperbolaCutoffOscillation
open RHTower.LiouvilleHyperbolaCutoffWide
open RHTower.LiouvilleHyperbolaCutoffThreeQuarter

namespace RHTower.LiouvilleHyperbolaCutoffSharp

noncomputable section

/-! ## Rightmost zeros on a horizontal line -/

/-- Every zero in the open strip has a zero on its horizontal line, at least as far right, with
no zero to its right on that line. -/
theorem exists_rightmost_zero {ρ₀ : ℂ} (hz : riemannZeta ρ₀ = 0) (h0 : 0 < ρ₀.re) :
    ∃ ρ : ℂ, riemannZeta ρ = 0 ∧ ρ.im = ρ₀.im ∧ ρ₀.re ≤ ρ.re ∧ ρ.re < 1 ∧
      ∀ c : ℝ, 0 < c → riemannZeta (ρ + c) ≠ 0 := by
  have hxi := xi_eq_zero_of_riemannZeta_eq_zero hz h0
  have hmem : ρ₀ ∈ stripHeightFinset ρ₀.im :=
    mem_stripHeightFinset.mpr ⟨h0, (xi_zero_re_mem_open_unit hxi).2, rfl, hxi⟩
  obtain ⟨ρ, hρS, hmax⟩ := (stripHeightFinset ρ₀.im).exists_max_image Complex.re ⟨ρ₀, hmem⟩
  obtain ⟨-, hρ1, hρim, hρxi⟩ := mem_stripHeightFinset.mp hρS
  refine ⟨ρ, (xi_eq_zero_iff_riemannZeta_eq_zero_and_nontrivial.mp hρxi).1, hρim,
    hmax ρ₀ hmem, hρ1, fun c hc hzc => ?_⟩
  have hre : (ρ + c).re = ρ.re + c := by simp
  rcases le_or_gt 1 (ρ + c).re with h1 | h1
  · exact riemannZeta_ne_zero_of_one_le_re h1 hzc
  · have hle := hmax ρ₀ hmem
    have hmc : ρ + c ∈ stripHeightFinset ρ₀.im :=
      mem_stripHeightFinset.mpr ⟨by rw [hre]; linarith, h1, by simp [hρim],
        xi_eq_zero_of_riemannZeta_eq_zero hzc (by rw [hre]; linarith)⟩
    have := hmax _ hmc
    rw [hre] at this
    linarith

/-- Starting from a zero `ρ₀` in the open strip, alternately moving to the rightmost zero of the
horizontal line and contracting `ρ ↦ 1 + θ(ρ - 1)` cannot produce zeros forever: the points converge
to `1`. So some rightmost zero `ρ` with `Re ρ ≥ Re ρ₀` has `ζ(1 + θ(ρ - 1)) ≠ 0`. -/
theorem exists_rightmost_contracted_nonzero {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) {ρ₀ : ℂ}
    (hz : riemannZeta ρ₀ = 0) (h0 : 0 < ρ₀.re) :
    ∃ ρ : ℂ, riemannZeta ρ = 0 ∧ ρ₀.re ≤ ρ.re ∧ ρ.re < 1 ∧ ρ.im ≠ 0 ∧
      (∀ c : ℝ, 0 < c → riemannZeta (ρ + c) ≠ 0) ∧ riemannZeta (1 + θ * (ρ - 1)) ≠ 0 := by
  by_contra hnone
  have him0 : ρ₀.im ≠ 0 := im_ne_zero_of_zero_mem_strip hz h0
  have hseq : ∀ n : ℕ, ∃ z : ℂ, riemannZeta z = 0 ∧ ρ₀.re ≤ z.re ∧ z.re < 1 ∧
      1 - z.re ≤ θ ^ n * (1 - ρ₀.re) ∧ z.im = θ ^ n * ρ₀.im ∧
      ∀ c : ℝ, 0 < c → riemannZeta (z + c) ≠ 0 := by
    intro n
    induction n with
    | zero =>
      obtain ⟨ρ, h1, h2, h3, h4, h5⟩ := exists_rightmost_zero hz h0
      exact ⟨ρ, h1, h3, h4, by simp; linarith, by simp [h2], h5⟩
    | succ n ih =>
      obtain ⟨z, hz1, hz2, hz3, hz4, hz5, hz6⟩ := ih
      have hzim : z.im ≠ 0 := by rw [hz5]; exact mul_ne_zero (pow_pos hθ0 n).ne' him0
      have hw : riemannZeta (1 + θ * (z - 1)) = 0 := by
        by_contra hne
        exact hnone ⟨z, hz1, hz2, hz3, hzim, hz6, hne⟩
      have hwre : (1 + θ * (z - 1)).re = 1 - θ * (1 - z.re) := by simp; ring
      have hwim : (1 + θ * (z - 1)).im = θ * z.im := by simp
      have hw0 : 0 < (1 + θ * (z - 1)).re := by rw [hwre]; nlinarith
      obtain ⟨ρ, h1, h2, h3, h4, h5⟩ := exists_rightmost_zero hw hw0
      rw [hwre] at h3
      have hpn : 0 < θ ^ n := pow_pos hθ0 n
      refine ⟨ρ, h1, by nlinarith, h4, ?_, ?_, h5⟩
      · rw [pow_succ]; nlinarith
      · rw [h2, hwim, hz5, pow_succ]; ring
  choose z hz1 _ hz3 hz4 hz5 _ using hseq
  have hp0 : Tendsto (fun n : ℕ => θ ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hθ0.le hθ1
  have hz1' : Tendsto z atTop (𝓝 1) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hb : Tendsto (fun n : ℕ => θ ^ n * ((1 - ρ₀.re) + |ρ₀.im|)) atTop (𝓝 0) := by
      simpa using hp0.mul_const ((1 - ρ₀.re) + |ρ₀.im|)
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hb
    have hn := norm_le_abs_re_add_abs_im (z n - 1)
    have h1 : 0 ≤ 1 - (z n).re := by linarith [hz3 n]
    have hre : |(z n - 1).re| ≤ θ ^ n * (1 - ρ₀.re) := by
      rw [Complex.sub_re, Complex.one_re, abs_sub_comm, abs_of_nonneg h1]
      exact hz4 n
    have him : |(z n - 1).im| = θ ^ n * |ρ₀.im| := by
      rw [Complex.sub_im, Complex.one_im, sub_zero, hz5, abs_mul, abs_of_pos (pow_pos hθ0 n)]
    linarith
  have hu1 := (RHTower.analyticAt_zetaResidueUnit 1).continuousAt.tendsto.comp hz1'
  have hu0 : Tendsto (fun n => RHTower.zetaResidueUnit (z n)) atTop (𝓝 0) := by
    have he : (fun n => RHTower.zetaResidueUnit (z n)) = fun _ : ℕ => (0 : ℂ) :=
      funext fun n => zetaResidueUnit_eq_zero_of_riemannZeta_eq_zero (hz1 n)
    rw [he]
    exact tendsto_const_nhds
  have he := tendsto_nhds_unique hu1 hu0
  simp at he

/-! ## One-sided bounds at the transported exponent -/

theorem zetaResidueUnit_add_ne_zero {ρ : ℂ} (hright : ∀ c : ℝ, 0 < c → riemannZeta (ρ + c) ≠ 0)
    (him : ρ.im ≠ 0) {c : ℝ} (hc : 0 < c) : RHTower.zetaResidueUnit (ρ + c) ≠ 0 := by
  have h1 : ρ + c ≠ 1 := by
    intro h; have := congrArg Complex.im h; simp at this; exact him this
  rw [zetaResidueUnit_eq h1]
  exact mul_ne_zero (sub_ne_zero.mpr h1) (hright c hc)

theorem rootArg_contract (θ : ℝ) (hθ : (θ : ℂ) ≠ 0) (ρ : ℂ) :
    rootArg θ (1 + θ * (ρ - 1)) = ρ + ((1 / (2 * θ) - 1 / 2 : ℝ) : ℂ) := by
  unfold rootArg; push_cast; field_simp; ring

theorem div_contract (θ : ℝ) (hθ : (θ : ℂ) ≠ 0) (ρ : ℂ) :
    (1 + θ * (ρ - 1)) / θ = ρ + ((1 / θ - 1 : ℝ) : ℂ) := by
  push_cast; field_simp; ring

/-- The contradiction at a zero with no zero to its right on its horizontal line: there the
root-head and Mertens-head arguments, both right translates of `ρ`, are not zeros. -/
theorem false_of_oneSided_rightmost {θ d c η C β K : ℝ} (hθ0 : 0 < θ) (hθ : θ < 3 / 4)
    (hc : c ≠ 0) (hη : |η| = 1) (hC : 0 ≤ C) (hβ : 1 - θ / 2 ≤ β) (hK : 0 ≤ K) {ρ : ℂ}
    (hρ : riemannZeta ρ = 0) (hρlo : 1 / 2 ≤ ρ.re) (hρhi : ρ.re < 1) (hρim : ρ.im ≠ 0)
    (hright : ∀ c : ℝ, 0 < c → riemannZeta (ρ + c) ≠ 0)
    (hwz : riemannZeta (1 + θ * (ρ - 1)) ≠ 0) (hβw : β < 1 - θ * (1 - ρ.re))
    (hg : ∀ u, 0 < u → η * (d * liouvilleTriangle (Real.exp u) + c * cutoffHead θ (Real.exp u))
      ≤ C * Real.exp (β * u) + K) :
    False := by
  have hθ1 : θ < 1 := by linarith
  have hθC : (θ : ℂ) ≠ 0 := by exact_mod_cast hθ0.ne'
  have hUv : RHTower.zetaResidueUnit (rootArg θ (1 + θ * (ρ - 1))) ≠ 0 := by
    rw [rootArg_contract θ hθC]
    refine zetaResidueUnit_add_ne_zero hright hρim ?_
    have : 1 / 2 < 1 / (2 * θ) := by rw [lt_div_iff₀ (by linarith)]; linarith
    linarith
  rcases lt_or_ge θ (2 / 3) with h23 | h23
  · exact false_of_oneSided_wide (d := d) hθ0 hθ1 hc hη hC (by linarith) (by linarith) hK hρ
      hρlo hρhi hρim hwz hUv hβw hg
  · have hUq : RHTower.zetaResidueUnit ((1 + θ * (ρ - 1)) / θ) ≠ 0 := by
      rw [div_contract θ hθC]
      refine zetaResidueUnit_add_ne_zero hright hρim ?_
      have : 1 < 1 / θ := by rw [lt_div_iff₀ hθ0]; linarith
      linarith
    exact false_of_oneSided_tq (d := d) hθ0 hθ1 hc hη hC (by linarith) (by linarith)
      (by linarith) (by linarith) hK hρ hρlo hρhi hρim hwz hUv hUq hβw hg

/-- **A one-sided bound at the exponent `1 - θ/2` implies RH.** For `0 < θ < 3/4`, `c ≠ 0`,
`η = ±1` and any `C ≥ 0`: if `η(dP + cA_θ)(x) ≤ C x^{1-θ/2}` for all large `x`, the Riemann
hypothesis holds. -/
theorem riemannHypothesis_of_eventually_le {θ d c η C : ℝ} (hθ0 : 0 < θ) (hθ : θ < 3 / 4)
    (hc : c ≠ 0) (hη : |η| = 1) (hC : 0 ≤ C)
    (h : ∀ᶠ x in atTop, η * (d * liouvilleTriangle x + c * cutoffHead θ x)
      ≤ C * x ^ (1 - θ / 2)) :
    RiemannHypothesis := by
  by_contra hRH
  have hnf : ¬ ∀ s ∈ rightHalf, xi s ≠ 0 := fun hf => hRH (rh_iff_xi_ne_zero_right.mpr hf)
  simp only [not_forall, not_not] at hnf
  obtain ⟨s, hs, hxs⟩ := hnf
  have hsre : 1 / 2 < s.re := mem_rightHalf.mp hs
  have hsz : riemannZeta s = 0 := (xi_eq_zero_iff_riemannZeta_eq_zero_and_nontrivial.mp hxs).1
  obtain ⟨ρ, hρ, hlo, hhi, him, hright, hwz⟩ :=
    exists_rightmost_contracted_nonzero hθ0 (by linarith) hsz (by linarith)
  obtain ⟨K, hK, hg⟩ := exists_oneSided_of_eventually_le_wide (by linarith) hη hC le_rfl h
  exact false_of_oneSided_rightmost hθ0 hθ hc hη hC le_rfl hK hρ (by linarith) hhi him hright
    hwz (by nlinarith) hg

/-- A one-sided bound `η(dP + cA_θ)(x) ≤ C x^β` for large `x` with `β < 1 - θ(1 - Θ)`,
`0 < θ < 3/4`, `c ≠ 0`, is impossible. -/
theorem false_of_eventually_le_abscissa_tq {θ d c η C β : ℝ} (hθ0 : 0 < θ) (hθ : θ < 3 / 4)
    (hc : c ≠ 0) (hη : |η| = 1) (hC : 0 ≤ C) (hβ : β < 1 - θ * (1 - zetaZeroAbscissa))
    (h : ∀ᶠ x in atTop, η * (d * liouvilleTriangle x + c * cutoffHead θ x) ≤ C * x ^ β) :
    False := by
  rcases lt_or_ge β (1 - θ / 2) with hβh | hβh
  · rcases lt_or_ge θ (2 / 3) with h23 | h23
    · exact false_of_eventually_le_wide hθ0 h23 hc hη hC hβh h
    · exact false_of_eventually_le_tq (by linarith) hθ hc hη hC hβh h
  set b := 1 - (1 - β) / θ with hbdef
  have hθb : θ * (1 - b) = 1 - β := by rw [hbdef]; field_simp; ring
  have hb : b < zetaZeroAbscissa := by
    by_contra hcon
    have : θ * (1 - b) ≤ θ * (1 - zetaZeroAbscissa) :=
      mul_le_mul_of_nonneg_left (by linarith [not_lt.mp hcon]) hθ0.le
    linarith
  have hb2 : 1 / 2 ≤ b := by
    have : (1 - β) / θ ≤ 1 / 2 := by rw [div_le_iff₀ hθ0]; linarith
    linarith
  obtain ⟨ρ₀, hz, -, hlo⟩ := exists_zetaZero_mem_openStrip_lt_re hb
  obtain ⟨ρ, hρ, hlo', hhi, him, hright, hwz⟩ :=
    exists_rightmost_contracted_nonzero hθ0 (by linarith) hz (by linarith)
  obtain ⟨K, hK, hg⟩ := exists_oneSided_of_eventually_le_wide (by linarith) hη hC le_rfl h
  refine false_of_oneSided_rightmost hθ0 hθ hc hη hC hβh hK hρ (by linarith) hhi him hright
    hwz ?_ hg
  have : θ * (1 - ρ.re) < θ * (1 - b) := mul_lt_mul_of_pos_left (by linarith) hθ0
  linarith

/-- **Exponent law, lower half, up to `θ < 3/4`.** For every `0 < θ < 3/4`, real `d`, `c ≠ 0`,
`C ≥ 0` and every `β < 1 - θ(1 - Θ)`, `Θ = sup Re ρ`, the combination `dP + cA_θ` exceeds
`C x^β` and falls below `-C x^β` for arbitrarily large `x`. -/
theorem frequently_gt_and_frequently_lt_abscissa_tq {θ : ℝ} (hθ0 : 0 < θ) (hθ : θ < 3 / 4)
    (d c : ℝ) (hc : c ≠ 0) {β C : ℝ} (hβ : β < 1 - θ * (1 - zetaZeroAbscissa)) (hC : 0 ≤ C) :
    (∃ᶠ x in atTop, C * x ^ β < d * liouvilleTriangle x + c * cutoffHead θ x) ∧
      (∃ᶠ x in atTop, d * liouvilleTriangle x + c * cutoffHead θ x < -(C * x ^ β)) := by
  constructor
  · by_contra h
    rw [Filter.not_frequently] at h
    exact false_of_eventually_le_abscissa_tq hθ0 hθ hc (η := 1) (by norm_num) hC hβ
      (h.mono fun x hx => by rw [one_mul]; exact not_lt.mp hx)
  · by_contra h
    rw [Filter.not_frequently] at h
    exact false_of_eventually_le_abscissa_tq hθ0 hθ hc (η := -1) (by norm_num) hC hβ
      (h.mono fun x hx => by rw [neg_one_mul, neg_le]; exact not_lt.mp hx)

/-! ## The exact exponent -/

/-- The refined remainder transform is holomorphic on `Re z > max(0, (3θ - 1)/2)` for every
`θ ≤ 1`. -/
theorem analyticOnNhd_refinedRemainderTransform_pos {θ : ℝ} (hθ1 : θ ≤ 1) :
    AnalyticOnNhd ℂ (refinedRemainderTransform θ) {z : ℂ | max 0 ((3 * θ - 1) / 2) < z.re} :=
  DifferentiableOn.analyticOnNhd
    (fun _ hz => (differentiableAt_integral_mul_cexp_exp
      ((measurable_refinedRemainder θ).comp Real.measurable_exp) (le_max_left _ _)
      (fun _ hu => (abs_refinedRemainder_exp_le hθ1 hu.le).trans
        (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (le_max_right _ _) hu.le))) hz)
      |>.differentiableWithinAt)
    (isOpen_lt continuous_const Complex.continuous_re)

/-- The one-sided measure of `η(dP + cA_θ)` at the exponent `β` and slack constant `ε`. -/
def cutMeasure (θ d c η ε β K : ℝ) : Measure ℝ :=
  expOneSidedMeasure (fun u => d * liouvilleTriangle (Real.exp u) + c * cutoffHead θ (Real.exp u))
    η ε β K

/-- **Continuation identity.** Under `η(dP + cA_θ)(e^u) ≤ C e^{βu} + K` and `C < ε`, the measure
`cutMeasure` has abscissa `β` and on `Re z > β`
`(ε/(z-β) + K/z - L(z)) D₄(z) = η(N₄(z) + cR'_θ(z)D₄(z))`. -/
theorem cutMeasure_continuation {θ d c η C ε β K : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hη : |η| = 1) (hC : 0 ≤ C) (hCε : C < ε) (hβθ : 1 - θ < β)
    (hβr : (3 * θ - 1) / 2 < β) (hβh : 1 / 2 < β) (hβ1 : β ≤ 1) (hK : 0 ≤ K)
    (hg : ∀ u, 0 < u → η * (d * liouvilleTriangle (Real.exp u) + c * cutoffHead θ (Real.exp u))
      ≤ C * Real.exp (β * u) + K) :
    IsAbscissa (cutMeasure θ d c η ε β K) β ∧ ∀ z : ℂ, β < z.re →
      ((ε : ℂ) / (z - β) + (K : ℂ) / z - complexLaplace (cutMeasure θ d c η ε β K) z)
          * tqPoleDenominator θ z
        = η * (tqPoleNumerator θ d c z + c * refinedRemainderTransform θ z
          * tqPoleDenominator θ z) := by
  set Z := LiouvilleTriangularShortHead.squareMass with hZdef
  have hZ := squareMass_pos
  have hθC : (θ : ℂ) ≠ 0 := by exact_mod_cast hθ0.ne'
  set f : ℝ → ℝ := fun u => d * liouvilleTriangle (Real.exp u) + c * cutoffHead θ (Real.exp u)
    with hfdef
  have hf : Measurable f := (measurable_const.mul
    (measurable_liouvilleTriangle.comp Real.measurable_exp)).add
    (measurable_const.mul ((measurable_cutoffHead θ).comp Real.measurable_exp))
  set B : ℝ := 2 * |d| + |c| * (Z + 3) with hBdef
  have hB : 0 ≤ B := by positivity
  have hb : ∀ u, 0 < u → |f u| ≤ B * Real.exp (2 * u) := fun u hu =>
    abs_cutCombination_exp_le_wide hθ1.le d c hu.le
  have hβ0 : 0 ≤ β := by linarith
  have hβ2 : β ≤ 2 := by linarith
  obtain ⟨hc0, hlo, hhi⟩ := isAbscissa_oneSidedMeasure hf hη hC hCε hK hB hβ2
    (by norm_num) hb hg
  set ν := expOneSidedMeasure f η ε β K with hνdef
  set Ψ : ℂ → ℂ := fun z => ((ε : ℝ) : ℂ) / (z - β) + (K : ℂ) / z
      - η * (tqPoleModel θ d c z + c * refinedRemainderTransform θ z) with hΨdef
  have hagree : ∀ z : ℂ, 2 < z.re → complexLaplace ν z = Ψ z := by
    intro z hz
    rw [complexLaplace_oneSidedMeasure_eq hf hβ0 hβ2 hCε.le hb hg hz]
    simp only [hΨdef, hfdef]
    rw [integral_cutCombination_exp_mul_cexp_tq hθ0 hθ1 d c hz]
  have hΨa : ∀ t : ℝ, β < t → AnalyticAt ℂ Ψ t := by
    intro t ht
    have ht0 : (t : ℂ) ≠ 0 := by exact_mod_cast (by linarith : (0 : ℝ) < t).ne'
    have htβ : (t : ℂ) - β ≠ 0 := by
      intro h; have := congrArg Complex.re h; simp at this; linarith
    have hP := analyticAt_tqPoleModel_ofReal hθ0 d c (by linarith : (1 : ℝ) / 2 < t)
      (by linarith : 1 - θ < t)
    have hR : AnalyticAt ℂ (refinedRemainderTransform θ) t :=
      analyticOnNhd_refinedRemainderTransform_pos hθ1.le t
        (show max 0 ((3 * θ - 1) / 2) < (t : ℂ).re by
          simp only [Complex.ofReal_re]; exact max_lt (by linarith) (by linarith))
    simp only [hΨdef]
    exact ((analyticAt_const.div (analyticAt_id.sub analyticAt_const) htβ).add
      (analyticAt_const.div analyticAt_id ht0)).sub
      (analyticAt_const.mul (hP.add (analyticAt_const.mul hR)))
  have hcβ : IsAbscissa ν β := isAbscissa_eq_of_analyticAt_real hc0 hlo hhi hΨa hagree
  set V : Set ℂ := {z : ℂ | β < z.re} with hV
  have hVo : IsOpen V := isOpen_lt continuous_const Complex.continuous_re
  set Lf : ℂ → ℂ := fun z => (((ε : ℝ) : ℂ) / (z - β) + (K : ℂ) / z
      - complexLaplace ν z) * tqPoleDenominator θ z with hLf
  set Rf : ℂ → ℂ := fun z => (η : ℂ) * (tqPoleNumerator θ d c z
      + c * refinedRemainderTransform θ z * tqPoleDenominator θ z) with hRf
  have hLa : AnalyticOnNhd ℂ Lf V := by
    refine DifferentiableOn.analyticOnNhd (fun z hz => ?_) hVo
    have hz' : β < z.re := hz
    have hz0 : z ≠ 0 := by intro h; rw [h, Complex.zero_re] at hz'; linarith
    have hzβ : z - β ≠ 0 := by
      intro h; have := congrArg Complex.re h; simp at this; linarith
    have d1 : DifferentiableAt ℂ (fun z : ℂ => ((ε : ℝ) : ℂ) / (z - β)) z :=
      (differentiableAt_const _).div (differentiableAt_id.sub_const _) hzβ
    have d2 : DifferentiableAt ℂ (fun z : ℂ => (K : ℂ) / z) z :=
      (differentiableAt_const _).div differentiableAt_id hz0
    exact (((d1.add d2).sub (hasDerivAt_complexLaplace hcβ hz').differentiableAt).mul
      (differentiableAt_tqPoleDenominator θ z)).differentiableWithinAt
  have hRa : AnalyticOnNhd ℂ Rf V := by
    refine DifferentiableOn.analyticOnNhd (fun z hz => ?_) hVo
    have hz' : β < z.re := hz
    have h2z : 2 * z ≠ 1 := by
      intro h; have := congrArg Complex.re h; simp at this; linarith
    have hR : DifferentiableAt ℂ (refinedRemainderTransform θ) z :=
      (analyticOnNhd_refinedRemainderTransform_pos hθ1.le z
        (show max 0 ((3 * θ - 1) / 2) < z.re from
          max_lt (by linarith) (by linarith))).differentiableAt
    exact ((differentiableAt_const _).mul ((differentiableAt_tqPoleNumerator θ d c h2z).add
      (((differentiableAt_const _).mul hR).mul
        (differentiableAt_tqPoleDenominator θ z)))).differentiableWithinAt
  have hθre : ∀ w : ℂ, (w / θ).re = w.re / θ := fun w => by
    rw [show w / (θ : ℂ) = w * ((θ⁻¹ : ℝ) : ℂ) by push_cast; ring, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, div_eq_mul_inv]
  have hev : Lf =ᶠ[𝓝 (3 : ℂ)] Rf := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (show (2 : ℝ) < (3 : ℂ).re by norm_num)] with z hz
    have hz' : 2 < z.re := hz
    have hz0 : z ≠ 0 := by intro h; rw [h, Complex.zero_re] at hz'; linarith
    have hz1 : z ≠ 1 := by intro h; rw [h, Complex.one_re] at hz'; linarith
    have hzh : z - 1 / 2 ≠ 0 := by
      intro h; have := congrArg Complex.re h; simp at this; linarith
    have hhre : 1 < (headArg θ z).re := by
      unfold headArg
      rw [Complex.add_re, hθre, Complex.one_re, Complex.sub_re, Complex.one_re]
      have : 0 < (z.re - 1) / θ := div_pos (by linarith) hθ0
      linarith
    have hvre : 1 < (rootArg θ z).re := by
      unfold rootArg
      rw [Complex.add_re, hθre, Complex.sub_re]
      have : 1 ≤ (z.re - (1 / 2 : ℂ).re) / θ := by
        rw [le_div_iff₀ hθ0]; norm_num; linarith
      norm_num at this ⊢
      linarith
    have hh1 : headArg θ z ≠ 1 := by intro h; rw [h, Complex.one_re] at hhre; linarith
    have hv1 : rootArg θ z ≠ 1 := by intro h; rw [h, Complex.one_re] at hvre; linarith
    have hU : RHTower.zetaResidueUnit z ≠ 0 := by
      rw [zetaResidueUnit_eq hz1]
      exact mul_ne_zero (sub_ne_zero.mpr hz1) (riemannZeta_ne_zero_of_one_lt_re (by linarith))
    have hUh : RHTower.zetaResidueUnit (headArg θ z) ≠ 0 := by
      rw [zetaResidueUnit_eq hh1]
      exact mul_ne_zero (sub_ne_zero.mpr hh1) (riemannZeta_ne_zero_of_one_lt_re hhre)
    have hUv : RHTower.zetaResidueUnit (rootArg θ z) ≠ 0 := by
      rw [zetaResidueUnit_eq hv1]
      exact mul_ne_zero (sub_ne_zero.mpr hv1) (riemannZeta_ne_zero_of_one_lt_re hvre)
    have hqre : 1 < (z / θ).re := by
      rw [hθre]; rw [lt_div_iff₀ hθ0]; linarith
    have hq1 : z / θ ≠ 1 := by intro h; rw [h, Complex.one_re] at hqre; linarith
    have hUq : RHTower.zetaResidueUnit (z / θ) ≠ 0 := by
      rw [zetaResidueUnit_eq hq1]
      exact mul_ne_zero (sub_ne_zero.mpr hq1) (riemannZeta_ne_zero_of_one_lt_re hqre)
    simp only [hLf, hRf]
    rw [hagree z hz', ← tqPoleModel_mul_denominator θ d c hθC hz0 hU hzh hUv hUh hUq]
    simp only [hΨdef]
    ring
  have h3V : (3 : ℂ) ∈ V := by show β < (3 : ℂ).re; norm_num; linarith
  have heq := hLa.eqOn_of_preconnected_of_eventuallyEq hRa
    (convex_halfSpace_re_gt β).isPreconnected h3V hev
  refine ⟨hcβ, fun z hz => ?_⟩
  exact heq hz

/-- At a real point `σ > max(½, 1 - θ)` every factor of `D₄` is nonzero. -/
theorem real_factors_ne_zero {θ σ : ℝ} (hθ0 : 0 < θ) (hσ : 1 / 2 < σ) (hσθ : 1 - θ < σ) :
    (σ : ℂ) ≠ 0 ∧ RHTower.zetaResidueUnit σ ≠ 0 ∧ (σ : ℂ) - 1 / 2 ≠ 0 ∧
      RHTower.zetaResidueUnit (rootArg θ σ) ≠ 0 ∧ RHTower.zetaResidueUnit (headArg θ σ) ≠ 0 ∧
      RHTower.zetaResidueUnit ((σ : ℂ) / θ) ≠ 0 := by
  refine ⟨by exact_mod_cast (by linarith : (0 : ℝ) < σ).ne',
    zetaResidueUnit_ofReal_ne_zero (by linarith), ?_, ?_, ?_, ?_⟩
  · intro h; have := congrArg Complex.re h; simp at this; linarith
  · have e : rootArg θ σ = (((σ - 1 / 2) / θ + 1 / 2 : ℝ) : ℂ) := by
      unfold rootArg; push_cast; ring
    rw [e]
    have := div_pos (by linarith : (0 : ℝ) < σ - 1 / 2) hθ0
    exact zetaResidueUnit_ofReal_ne_zero (by linarith)
  · have e : headArg θ σ = (((σ - 1) / θ + 1 : ℝ) : ℂ) := by
      unfold headArg; push_cast; ring
    rw [e]
    have : -1 < (σ - 1) / θ := by rw [lt_div_iff₀ hθ0]; linarith
    exact zetaResidueUnit_ofReal_ne_zero (by linarith)
  · have := zetaResidueUnit_ofReal_ne_zero (div_pos (by linarith : (0 : ℝ) < σ) hθ0)
    push_cast at this
    exact this

/-- On the real axis right of `β` the Laplace transform of `cutMeasure` is the explicit
`ε/(σ-β) + K/σ - η(M₄(σ) + cR'_θ(σ))`. -/
theorem complexLaplace_cutMeasure_ofReal {θ d c η C ε β K : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hη : |η| = 1) (hC : 0 ≤ C) (hCε : C < ε) (hβθ : 1 - θ < β)
    (hβr : (3 * θ - 1) / 2 < β) (hβh : 1 / 2 < β) (hβ1 : β ≤ 1) (hK : 0 ≤ K)
    (hg : ∀ u, 0 < u → η * (d * liouvilleTriangle (Real.exp u) + c * cutoffHead θ (Real.exp u))
      ≤ C * Real.exp (β * u) + K) {σ : ℝ} (hσ : β < σ) :
    complexLaplace (cutMeasure θ d c η ε β K) σ
      = (ε : ℂ) / (σ - β) + (K : ℂ) / σ
        - η * (tqPoleModel θ d c σ + c * refinedRemainderTransform θ σ) := by
  obtain ⟨-, hid⟩ := cutMeasure_continuation hθ0 hθ1 hη hC hCε hβθ hβr hβh hβ1 hK hg
  have h := hid σ (by simpa using hσ)
  obtain ⟨h0, hU, hh, hUv, hUh, hUq⟩ :=
    real_factors_ne_zero (σ := σ) hθ0 (by linarith) (by linarith)
  have hθC : (θ : ℂ) ≠ 0 := by exact_mod_cast hθ0.ne'
  have hD : tqPoleDenominator θ σ ≠ 0 := by
    unfold tqPoleDenominator cutPoleDenominator
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero h0 hU) hh) hUv) hUh)
      hUq
  rw [← tqPoleModel_mul_denominator θ d c hθC h0 hU hh hUv hUh hUq] at h
  apply mul_right_cancel₀ hD
  linear_combination -h

/-- **The local inequality at a transported pole on the boundary line.** Let `w` with `Re w = β`,
`Im w ≠ 0`, and `D₄(z) = (z - w)^m E(z)` near `w`, `m ≥ 1`. A bound
`η(dP + cA_θ)(e^u) ≤ C e^{βu} + K` gives `|N₄(w)| ≤ ε|E(w)|` for every `ε > C`. -/
theorem norm_tqPoleNumerator_le {θ d c η C ε β K : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hη : |η| = 1) (hC : 0 ≤ C) (hCε : C < ε) (hβθ : 1 - θ < β)
    (hβr : (3 * θ - 1) / 2 < β) (hβh : 1 / 2 < β) (hβ1 : β ≤ 1) (hK : 0 ≤ K)
    (hg : ∀ u, 0 < u → η * (d * liouvilleTriangle (Real.exp u) + c * cutoffHead θ (Real.exp u))
      ≤ C * Real.exp (β * u) + K) {w : ℂ} (hwre : w.re = β) (hwim : w.im ≠ 0) {m : ℕ}
    (hm : 1 ≤ m) {E : ℂ → ℂ} (hEan : AnalyticAt ℂ E w)
    (hfac : ∀ᶠ z in 𝓝 w, tqPoleDenominator θ z = (z - w) ^ m • E z) :
    ‖tqPoleNumerator θ d c w‖ ≤ ε * ‖E w‖ := by
  obtain ⟨-, hid⟩ := cutMeasure_continuation hθ0 hθ1 hη hC hCε hβθ hβr hβh hβ1 hK hg
  set ν := cutMeasure θ d c η ε β K with hν
  have hε : 0 ≤ ε := by linarith
  have hβ0 : 0 < β := by linarith
  set γ : ℝ := |w.im| with hγ
  have hγ0 : 0 < γ := abs_pos.mpr hwim
  set M : ℂ → ℂ := fun z => tqPoleModel θ d c z + c * refinedRemainderTransform θ z with hM
  -- the model is bounded on the real axis just right of `β`
  have hMan : AnalyticAt ℂ M ((β + 0 : ℝ) : ℂ) :=
    (analyticAt_tqPoleModel_ofReal hθ0 d c (by linarith) (by linarith)).add
      (analyticAt_const.mul (analyticOnNhd_refinedRemainderTransform_pos hθ1.le _
        (show max 0 ((3 * θ - 1) / 2) < ((β + 0 : ℝ) : ℂ).re by
          simp only [Complex.ofReal_re]; exact max_lt (by linarith) (by linarith))))
  have hMc : ContinuousAt (fun r : ℝ => M ((β + r : ℝ) : ℂ)) 0 :=
    ContinuousAt.comp (g := M) (f := fun r : ℝ => ((β + r : ℝ) : ℂ)) hMan.continuousAt
      (by fun_prop)
  set BM : ℝ := ‖M ((β + 0 : ℝ) : ℂ)‖ + 1 with hBM
  have hMb : ∀ᶠ r in 𝓝 (0 : ℝ), ‖M ((β + r : ℝ) : ℂ)‖ ≤ BM :=
    (hMc.norm.eventually (gt_mem_nhds (show ‖M ((β + 0 : ℝ) : ℂ)‖ < BM by
      rw [hBM]; linarith))).mono fun r hr => hr.le
  -- the remainder transform, the numerator and `E` are continuous at `w`
  have hRw : AnalyticAt ℂ (refinedRemainderTransform θ) w :=
    analyticOnNhd_refinedRemainderTransform_pos hθ1.le w
      (show max 0 ((3 * θ - 1) / 2) < w.re by rw [hwre]; exact max_lt (by linarith) (by linarith))
  have h2w : 2 * w ≠ 1 := by
    intro h; have := congrArg Complex.im h; simp at this; exact hwim this
  have hNw : ContinuousAt (tqPoleNumerator θ d c) w :=
    (differentiableAt_tqPoleNumerator θ d c h2w).continuousAt
  have htz : Tendsto (fun r : ℝ => w + r) (𝓝[>] (0 : ℝ)) (𝓝 w) := by
    have h : Tendsto (fun r : ℝ => w + r) (𝓝 (0 : ℝ)) (𝓝 (w + ((0 : ℝ) : ℂ))) :=
      (continuous_const.add Complex.continuous_ofReal).tendsto 0
    simpa using h.mono_left nhdsWithin_le_nhds
  set BR : ℝ := ‖refinedRemainderTransform θ w‖ + 1 with hBR
  have hRb : ∀ᶠ r : ℝ in 𝓝[>] 0, ‖refinedRemainderTransform θ (w + r)‖ ≤ BR :=
    ((hRw.continuousAt.norm.tendsto.comp htz).eventually (gt_mem_nhds (show
      ‖refinedRemainderTransform θ w‖ < BR by rw [hBR]; linarith))).mono fun r hr => hr.le
  set C₂ : ℝ := (ε + K) / γ + K / β + BM + |c| * BR with hC₂
  have hmain : ∀ᶠ r : ℝ in 𝓝[>] 0,
      ‖tqPoleNumerator θ d c (w + r)‖ ≤ ‖E (w + r)‖ * (ε + r * C₂) := by
    have hsmall : ∀ᶠ r : ℝ in 𝓝[>] 0, r < 1 := nhdsWithin_le_nhds (gt_mem_nhds (by norm_num))
    filter_upwards [htz.eventually hfac, self_mem_nhdsWithin, nhdsWithin_le_nhds hMb, hRb,
      hsmall] with r hr hr0 hMr hRr hr1
    have hr0' : 0 < r := hr0
    set z : ℂ := w + r with hz
    have hzre : z.re = β + r := by simp [hz, hwre]
    have hzim : z.im = w.im := by simp [hz]
    have hDz : tqPoleDenominator θ z = (r : ℂ) ^ m * E z := by
      rw [hr, smul_eq_mul, show w + (r : ℂ) - w = r by ring]
    -- the identity at `z`
    have e := hid z (by rw [hzre]; linarith)
    set A : ℂ := (ε : ℂ) / (z - β) + (K : ℂ) / z with hA
    have hηN : (η : ℂ) * tqPoleNumerator θ d c z = (A - complexLaplace ν z) * tqPoleDenominator θ z
        - η * c * refinedRemainderTransform θ z * tqPoleDenominator θ z := by
      linear_combination -e
    -- bounds
    have hγle : γ ≤ ‖z - β‖ := by
      have := Complex.abs_im_le_norm (z - β)
      rw [Complex.sub_im, hzim, Complex.ofReal_im, sub_zero] at this
      exact this
    have hγle' : γ ≤ ‖z‖ := by
      have := Complex.abs_im_le_norm z
      rw [hzim] at this
      exact this
    have hA1 : ‖(ε : ℂ) / (z - β)‖ ≤ ε / γ := by
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hε]
      exact div_le_div_of_nonneg_left hε hγ0 hγle
    have hA2 : ‖(K : ℂ) / z‖ ≤ K / γ := by
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hK]
      exact div_le_div_of_nonneg_left hK hγ0 hγle'
    have hL : ‖complexLaplace ν z‖ ≤ ε / r + K / β + BM := by
      have h1 : ‖complexLaplace ν z‖ ≤ laplaceReal ν (β + r) := by
        have := norm_complexLaplace_le ν z
        rw [hzre] at this
        exact this
      have hnn : 0 ≤ laplaceReal ν (β + r) := integral_nonneg fun u => (Real.exp_pos _).le
      have h2 : laplaceReal ν (β + r) = ‖complexLaplace ν ((β + r : ℝ) : ℂ)‖ := by
        rw [complexLaplace_ofReal, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnn]
      have h3 := complexLaplace_cutMeasure_ofReal hθ0 hθ1 hη hC hCε hβθ hβr hβh hβ1 hK hg
        (σ := β + r) (by linarith)
      rw [← hν] at h3
      have hq : ((β + r : ℝ) : ℂ) - β = r := by push_cast; ring
      have h4 : ‖(ε : ℂ) / (((β + r : ℝ) : ℂ) - β)‖ = ε / r := by
        rw [hq, norm_div, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
          Real.norm_eq_abs, abs_of_pos hr0', abs_of_nonneg hε]
      have h5 : ‖(K : ℂ) / ((β + r : ℝ) : ℂ)‖ ≤ K / β := by
        rw [norm_div, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_nonneg hK, abs_of_pos (by linarith)]
        exact div_le_div_of_nonneg_left hK hβ0 (by linarith)
      have h6 : ‖(η : ℂ) * M ((β + r : ℝ) : ℂ)‖ ≤ BM := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, hη, one_mul]; exact hMr
      refine h1.trans ?_
      rw [h2, h3]
      calc ‖(ε : ℂ) / (((β + r : ℝ) : ℂ) - β) + (K : ℂ) / ((β + r : ℝ) : ℂ)
            - η * (tqPoleModel θ d c ((β + r : ℝ) : ℂ)
              + c * refinedRemainderTransform θ ((β + r : ℝ) : ℂ))‖
          ≤ ‖(ε : ℂ) / (((β + r : ℝ) : ℂ) - β)‖ + ‖(K : ℂ) / ((β + r : ℝ) : ℂ)‖
            + ‖(η : ℂ) * M ((β + r : ℝ) : ℂ)‖ :=
            (norm_sub_le _ _).trans (add_le_add_left (norm_add_le _ _) _ |>.trans_eq (by ring))
        _ ≤ ε / r + K / β + BM := by rw [h4]; linarith
    have hNz : ‖tqPoleNumerator θ d c z‖ ≤ r ^ m * ‖E z‖ * (ε / r + C₂) := by
      have hn : ‖tqPoleNumerator θ d c z‖ = ‖(η : ℂ) * tqPoleNumerator θ d c z‖ := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, hη, one_mul]
      have hDn : ‖tqPoleDenominator θ z‖ = r ^ m * ‖E z‖ := by
        rw [hDz, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0']
      have hAL : ‖A - complexLaplace ν z‖ ≤ ε / γ + K / γ + (ε / r + K / β + BM) := by
        have := norm_sub_le A (complexLaplace ν z)
        have := norm_add_le ((ε : ℂ) / (z - β)) ((K : ℂ) / z)
        linarith
      have hcR : ‖(η : ℂ) * c * refinedRemainderTransform θ z‖ ≤ |c| * BR := by
        rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, hη, one_mul,
          Complex.norm_real, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left hRr (abs_nonneg c)
      rw [hn, hηN]
      have hD0 : 0 ≤ ‖tqPoleDenominator θ z‖ := norm_nonneg _
      calc ‖(A - complexLaplace ν z) * tqPoleDenominator θ z
            - η * c * refinedRemainderTransform θ z * tqPoleDenominator θ z‖
          ≤ ‖A - complexLaplace ν z‖ * ‖tqPoleDenominator θ z‖
            + ‖(η : ℂ) * c * refinedRemainderTransform θ z‖ * ‖tqPoleDenominator θ z‖ := by
            refine (norm_sub_le _ _).trans ?_
            rw [norm_mul, norm_mul]
        _ ≤ (ε / γ + K / γ + (ε / r + K / β + BM)) * ‖tqPoleDenominator θ z‖
            + |c| * BR * ‖tqPoleDenominator θ z‖ := by
            gcongr
        _ = r ^ m * ‖E z‖ * (ε / r + C₂) := by
            rw [hDn, hC₂]; field_simp; ring
    have hpow : r ^ m * (ε / r + C₂) ≤ ε + r * C₂ := by
      have e1 : r ^ m * (ε / r + C₂) = r ^ (m - 1) * (ε + r * C₂) := by
        have : r ^ m = r ^ (m - 1) * r := by rw [← pow_succ]; congr 1; omega
        rw [this]; field_simp
      have hC₂0 : 0 ≤ C₂ := by
        have : 0 ≤ |c| * BR := mul_nonneg (abs_nonneg c) (by positivity)
        rw [hC₂]; have : 0 ≤ BM := by positivity
        positivity
      rw [e1]
      have hp : r ^ (m - 1) ≤ 1 := pow_le_one₀ hr0'.le hr1.le
      have hq : 0 ≤ ε + r * C₂ := by positivity
      calc r ^ (m - 1) * (ε + r * C₂) ≤ 1 * (ε + r * C₂) :=
            mul_le_mul_of_nonneg_right hp hq
        _ = ε + r * C₂ := one_mul _
    calc ‖tqPoleNumerator θ d c z‖ ≤ r ^ m * ‖E z‖ * (ε / r + C₂) := hNz
      _ = ‖E z‖ * (r ^ m * (ε / r + C₂)) := by ring
      _ ≤ ‖E z‖ * (ε + r * C₂) := mul_le_mul_of_nonneg_left hpow (norm_nonneg _)
  have hl : Tendsto (fun r : ℝ => ‖tqPoleNumerator θ d c (w + r)‖) (𝓝[>] (0 : ℝ))
      (𝓝 ‖tqPoleNumerator θ d c w‖) := (hNw.tendsto.comp htz).norm
  have hr : Tendsto (fun r : ℝ => ‖E (w + r)‖ * (ε + r * C₂)) (𝓝[>] (0 : ℝ))
      (𝓝 (‖E w‖ * (ε + 0 * C₂))) := by
    refine ((hEan.continuousAt.tendsto.comp htz).norm).mul ?_
    have h0 : Tendsto (fun r : ℝ => ε + r * C₂) (𝓝 (0 : ℝ)) (𝓝 (ε + 0 * C₂)) :=
      (continuous_const.add (continuous_id.mul continuous_const)).tendsto 0
    exact h0.mono_left nhdsWithin_le_nhds
  have := le_of_tendsto_of_tendsto hl hr hmain
  rw [zero_mul, add_zero] at this
  linarith

/-- Under RH, `U(s) ≠ 0` for every nonreal `s` with `Re s > ½`. -/
theorem zetaResidueUnit_ne_zero_of_riemannHypothesis (hRH : RiemannHypothesis) {s : ℂ}
    (hs : 1 / 2 < s.re) (him : s.im ≠ 0) : RHTower.zetaResidueUnit s ≠ 0 := by
  have hs1 : s ≠ 1 := by intro h; rw [h, Complex.one_im] at him; exact him rfl
  rw [zetaResidueUnit_eq hs1]
  refine mul_ne_zero (sub_ne_zero.mpr hs1) (fun hz => ?_)
  exact rh_iff_xi_ne_zero_right.mp hRH s (mem_rightHalf.mpr hs)
    (xi_eq_zero_of_riemannZeta_eq_zero hz (by linarith))

/-- **The cut combination is `Ω±(x^{1-θ/2})`.** For every `0 < θ < 3/4`, every real `d` and every
`c ≠ 0` there is `δ > 0` with `dP + cA_θ > δ x^{1-θ/2}` and `dP + cA_θ < -δ x^{1-θ/2}`, each for
arbitrarily large `x`. -/
theorem exists_omega_pm_exact {θ : ℝ} (hθ0 : 0 < θ) (hθ : θ < 3 / 4) (d c : ℝ) (hc : c ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧
      (∃ᶠ x in atTop, δ * x ^ (1 - θ / 2) < d * liouvilleTriangle x + c * cutoffHead θ x) ∧
      (∃ᶠ x in atTop, d * liouvilleTriangle x + c * cutoffHead θ x < -(δ * x ^ (1 - θ / 2))) := by
  have hθ1 : θ < 1 := by linarith
  suffices key : ∃ δ : ℝ, 0 < δ ∧ ∀ η : ℝ, |η| = 1 → ¬ ∀ᶠ x in atTop,
      η * (d * liouvilleTriangle x + c * cutoffHead θ x) ≤ δ * x ^ (1 - θ / 2) by
    obtain ⟨δ, hδ, hk⟩ := key
    refine ⟨δ, hδ, ?_, ?_⟩
    · by_contra h
      rw [Filter.not_frequently] at h
      exact hk 1 (by norm_num) (h.mono fun x hx => by rw [one_mul]; exact not_lt.mp hx)
    · by_contra h
      rw [Filter.not_frequently] at h
      exact hk (-1) (by norm_num)
        (h.mono fun x hx => by rw [neg_one_mul, neg_le]; exact not_lt.mp hx)
  by_cases hRH : RiemannHypothesis
  swap
  · exact ⟨1, one_pos, fun η hη h =>
      hRH (riemannHypothesis_of_eventually_le hθ0 hθ hc hη zero_le_one h)⟩
  obtain ⟨ρ, hρ, hlo, -, him, -⟩ := exists_separated_contracted_zero hθ0 hθ1
  have hρre : ρ.re = 1 / 2 := by
    by_contra hne
    exact rh_iff_xi_ne_zero_right.mp hRH ρ (mem_rightHalf.mpr (lt_of_le_of_ne hlo (Ne.symm hne)))
      (xi_eq_zero_of_riemannZeta_eq_zero hρ (by linarith))
  set β : ℝ := 1 - θ / 2 with hβ
  set w : ℂ := 1 + θ * (ρ - 1) with hwdef
  have hθC : (θ : ℂ) ≠ 0 := by exact_mod_cast hθ0.ne'
  have hwre : w.re = β := by rw [hβ, hwdef]; simp [hρre]; ring
  have hwim0 : w.im ≠ 0 := by
    rw [hwdef]; simp only [Complex.add_im, Complex.one_im, zero_add, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero, Complex.sub_im, sub_zero]
    exact mul_ne_zero hθ0.ne' him
  -- the order of the transported pole
  have hDan : AnalyticOnNhd ℂ (tqPoleDenominator θ) univ :=
    DifferentiableOn.analyticOnNhd
      (fun z _ => (differentiableAt_tqPoleDenominator θ z).differentiableWithinAt) isOpen_univ
  have hD3 : tqPoleDenominator θ 3 ≠ 0 := by
    obtain ⟨h0, hU, hh, hUv, hUh, hUq⟩ :=
      real_factors_ne_zero (σ := 3) hθ0 (by norm_num) (by linarith)
    push_cast at h0 hU hh hUv hUh hUq
    unfold tqPoleDenominator cutPoleDenominator
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero h0 hU) hh) hUv) hUh)
      hUq
  have hnot : ¬ ∀ᶠ z in 𝓝 w, tqPoleDenominator θ z = 0 := by
    intro hzero
    have hall := hDan.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ
      (mem_univ w) hzero
    exact hD3 (hall (mem_univ 3))
  obtain ⟨m, E, hEan, hE0, hfac⟩ :=
    ((hDan w (mem_univ w)).exists_eventuallyEq_pow_smul_nonzero_iff).mpr hnot
  have hhw : headArg θ w = ρ := by unfold headArg; rw [hwdef]; field_simp; ring
  have hUh : RHTower.zetaResidueUnit (headArg θ w) = 0 := by
    rw [hhw]; exact zetaResidueUnit_eq_zero_of_riemannZeta_eq_zero hρ
  have hDw : tqPoleDenominator θ w = 0 := by
    unfold tqPoleDenominator cutPoleDenominator; rw [hUh, mul_zero, zero_mul]
  have hm : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · exfalso
      have := hfac.self_of_nhds
      rw [h, pow_zero, one_smul, hDw] at this
      exact hE0 this.symm
    · exact h
  -- the numerator at `w` does not vanish
  have hUw : RHTower.zetaResidueUnit w ≠ 0 :=
    zetaResidueUnit_ne_zero_of_riemannHypothesis hRH (by rw [hwre]; linarith) hwim0
  have hUv : RHTower.zetaResidueUnit (rootArg θ w) ≠ 0 := by
    rw [hwdef, rootArg_contract θ hθC]
    have : 1 / 2 < 1 / (2 * θ) := by rw [lt_div_iff₀ (by linarith)]; linarith
    refine zetaResidueUnit_ne_zero_of_riemannHypothesis hRH ?_ ?_
    · rw [Complex.add_re, Complex.ofReal_re, hρre]; linarith
    · rw [Complex.add_im, Complex.ofReal_im, add_zero]; exact him
  have hUq : RHTower.zetaResidueUnit (w / θ) ≠ 0 := by
    rw [hwdef, div_contract θ hθC]
    have : 1 < 1 / θ := by rw [lt_div_iff₀ hθ0]; linarith
    refine zetaResidueUnit_ne_zero_of_riemannHypothesis hRH ?_ ?_
    · rw [Complex.add_re, Complex.ofReal_re, hρre]; linarith
    · rw [Complex.add_im, Complex.ofReal_im, add_zero]; exact him
  have hNw : tqPoleNumerator θ d c w = c * LiouvilleTriangularShortHead.squareMass / θ
      * (w * RHTower.zetaResidueUnit w * (w - 1 / 2) * RHTower.zetaResidueUnit (rootArg θ w))
      * RHTower.zetaResidueUnit (w / θ) := by
    unfold tqPoleNumerator cutPoleNumerator; rw [hUh]; ring
  have hN0 : tqPoleNumerator θ d c w ≠ 0 := by
    rw [hNw]
    have hw0 : w ≠ 0 := by
      intro h0; have := congrArg Complex.re h0; rw [hwre, Complex.zero_re] at this; linarith
    have hwh : w - 1 / 2 ≠ 0 := by
      intro h0; have := congrArg Complex.re h0
      simp only [Complex.sub_re, Complex.zero_re] at this
      rw [hwre] at this; norm_num at this; linarith
    have ha : (c : ℂ) * LiouvilleTriangularShortHead.squareMass / θ ≠ 0 :=
      div_ne_zero (mul_ne_zero (by exact_mod_cast hc) (by exact_mod_cast squareMass_pos.ne')) hθC
    exact mul_ne_zero (mul_ne_zero ha (mul_ne_zero (mul_ne_zero (mul_ne_zero hw0 hUw) hwh) hUv))
      hUq
  -- the threshold
  have hNpos : 0 < ‖tqPoleNumerator θ d c w‖ := norm_pos_iff.mpr hN0
  have hEpos : 0 < ‖E w‖ := norm_pos_iff.mpr hE0
  refine ⟨‖tqPoleNumerator θ d c w‖ / (2 * ‖E w‖), by positivity, fun η hη h => ?_⟩
  set δ := ‖tqPoleNumerator θ d c w‖ / (2 * ‖E w‖) with hδ
  have hδ0 : 0 < δ := by positivity
  obtain ⟨K, hK, hg⟩ := exists_oneSided_of_eventually_le_wide hθ1.le hη hδ0.le le_rfl h
  have hb := norm_tqPoleNumerator_le (ε := 3 * δ / 2) hθ0 hθ1 hη hδ0.le (by linarith)
    (by linarith) (by linarith) (by linarith) (by linarith) hK hg hwre hwim0 hm hEan hfac
  have e : 3 * δ / 2 * ‖E w‖ = 3 / 4 * ‖tqPoleNumerator θ d c w‖ := by
    rw [hδ]; field_simp; ring
  linarith

end

end RHTower.LiouvilleHyperbolaCutoffSharp
