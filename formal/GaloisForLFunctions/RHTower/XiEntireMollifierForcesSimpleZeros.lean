import GaloisForLFunctions.RHTower.RiemannTower

/-!
# A mollifier with positive real part on the right half-plane forces simple zeros

Every zero-free right disc admits a local mollifier: a function `g`, holomorphic on the disc, with
`Re(g ξ) > 0` on its boundary (Nehari).  This module asks what a single mollifier, holomorphic
across the critical line, forces.

* `re_deriv_pos_of_re_pos_rightHalfDisc` (Julia–Carathéodory at a boundary zero): if `f` is
  analytic at `z₀`, `f(z₀) = 0` and `Re f > 0` on the open right half-disc at `z₀`, then `f'(z₀)`
  is a positive real number.  Proof: write `f = (z − z₀)^k h`, `h(z₀) = a ≠ 0`.  Positivity along
  rays `z₀ + ε w`, `Re w > 0`, gives `Re(a w^k) ≥ 0` for `Re w ≥ 0`.  For `k ≥ 2` the four
  directions `1, e^{±iπ/(2k)}, e^{iπ/k}` force `a = 0`.  For `k = 1` the directions `1, ±i`
  force `a > 0`.
* `simple_of_re_mul_xi_pos`: if `g` is analytic at a zero `ρ₀` of `xi` on the critical line and
  `Re(g ξ) > 0` on the right half-disc at `ρ₀`, then `ρ₀` is a simple zero and
  `g(ρ₀) ξ'(ρ₀)` is a positive real number.
* `riemannHypothesis_and_simple_of_entire_mollifier`: an entire `g` with `Re(g ξ) > 0` on the
  whole half-plane `Re s > ½` implies the Riemann hypothesis, simplicity of every zero, and
  `g(ρ) ξ'(ρ) > 0` at every zero.

So a producer for the seam criterion that uses one mollifier holomorphic across the critical line,
or disc mollifiers with a common holomorphic limit (every Dirichlet-polynomial mollifier), proves
strictly more than RH: it also proves the simple-zero conjecture and the pointwise positivity of
the mollified derivative at every zero.
-/

noncomputable section

open Complex Filter Topology Metric
open scoped Real

namespace RHTower

namespace EntireMollifier

/-- Positivity of `Re(a w^k)` on the closed right half-plane of directions. -/
theorem re_mul_pow_nonneg_of_pos {h : ℂ → ℂ} {z₀ : ℂ} {k : ℕ} (hh : ContinuousAt h z₀)
    {δ : ℝ} (hδ : 0 < δ)
    (hpos : ∀ z : ℂ, ‖z - z₀‖ < δ → 0 < (z - z₀).re → 0 < ((z - z₀) ^ k * h z).re)
    {w : ℂ} (hw : 0 < w.re) : 0 ≤ (w ^ k * h z₀).re := by
  have hw0 : w ≠ 0 := fun h0 => by rw [h0, Complex.zero_re] at hw; exact lt_irrefl 0 hw
  have hnw : 0 < ‖w‖ := norm_pos_iff.mpr hw0
  -- along the ray `z₀ + ε w`
  have hlim : Tendsto (fun ε : ℝ => (w ^ k * h (z₀ + (ε : ℂ) * w)).re) (𝓝[>] 0)
      (𝓝 (w ^ k * h z₀).re) := by
    have hray : Tendsto (fun ε : ℝ => z₀ + (ε : ℂ) * w) (𝓝[>] (0 : ℝ)) (𝓝 z₀) := by
      have : Continuous (fun ε : ℝ => z₀ + (ε : ℂ) * w) :=
        continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
      have h0 := this.tendsto 0
      simp only [Complex.ofReal_zero, zero_mul, add_zero] at h0
      exact h0.mono_left nhdsWithin_le_nhds
    exact (Complex.continuous_re.tendsto _).comp
      ((tendsto_const_nhds.mul (hh.tendsto.comp hray)))
  apply ge_of_tendsto hlim
  have hsmall : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε < δ / ‖w‖ := by
    have : (0 : ℝ) < δ / ‖w‖ := div_pos hδ hnw
    exact (eventually_lt_nhds this).filter_mono nhdsWithin_le_nhds
  filter_upwards [hsmall, self_mem_nhdsWithin] with ε hε hε0
  have hε0' : 0 < ε := hε0
  have hz : ‖(z₀ + (ε : ℂ) * w) - z₀‖ < δ := by
    rw [add_sub_cancel_left, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε0']
    rwa [lt_div_iff₀ hnw] at hε
  have hre : 0 < ((z₀ + (ε : ℂ) * w) - z₀).re := by
    rw [add_sub_cancel_left, Complex.re_ofReal_mul]; positivity
  have h := hpos _ hz hre
  rw [add_sub_cancel_left, mul_pow, mul_assoc, ← Complex.ofReal_pow, Complex.re_ofReal_mul] at h
  exact (pos_of_mul_pos_right h (by positivity)).le

/-- Extension to the closed right half-plane of directions. -/
theorem re_mul_pow_nonneg_of_nonneg {a : ℂ} {k : ℕ}
    (hpos : ∀ w : ℂ, 0 < w.re → 0 ≤ (w ^ k * a).re) {w : ℂ} (hw : 0 ≤ w.re) :
    0 ≤ (w ^ k * a).re := by
  have hcont : Continuous (fun t : ℝ => ((w + (t : ℂ)) ^ k * a).re) :=
    Complex.continuous_re.comp (((continuous_const.add Complex.continuous_ofReal).pow k).mul
      continuous_const)
  have hlim : Tendsto (fun t : ℝ => ((w + (t : ℂ)) ^ k * a).re) (𝓝[>] 0) (𝓝 (w ^ k * a).re) := by
    have := (hcont.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
    simpa using this
  apply ge_of_tendsto hlim
  filter_upwards [self_mem_nhdsWithin] with t ht
  apply hpos
  rw [Complex.add_re, Complex.ofReal_re]
  have : (0 : ℝ) < t := ht
  linarith

theorem re_exp_angle_nonneg {θ : ℝ} (hθ : |θ| ≤ π / 2) :
    0 ≤ (Complex.exp ((θ : ℂ) * I)).re := by
  rw [Complex.exp_ofReal_mul_I_re]
  exact Real.cos_nonneg_of_mem_Icc ⟨by linarith [neg_abs_le θ], by linarith [le_abs_self θ]⟩

/-- **Julia–Carathéodory at a boundary zero.**  If `f` is analytic at `z₀`, vanishes there, and has
positive real part on the open right half-disc at `z₀`, then `f'(z₀)` is a positive real number. -/
theorem re_deriv_pos_of_re_pos_rightHalfDisc {f : ℂ → ℂ} {z₀ : ℂ} {δ : ℝ} (hδ : 0 < δ)
    (hf : AnalyticAt ℂ f z₀) (h0 : f z₀ = 0)
    (hpos : ∀ z : ℂ, ‖z - z₀‖ < δ → 0 < (z - z₀).re → 0 < (f z).re) :
    0 < (deriv f z₀).re ∧ (deriv f z₀).im = 0 := by
  -- `f` is not locally zero
  have hnetop : analyticOrderAt f z₀ ≠ ⊤ := by
    intro htop
    have hev : f =ᶠ[𝓝 z₀] 0 := analyticOrderAt_eq_top.mp htop
    obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hev
    set t : ℝ := min (ε / 2) (δ / 2)
    have ht : 0 < t := lt_min (by linarith) (by linarith)
    have hzt : ‖(z₀ + (t : ℂ)) - z₀‖ < δ := by
      rw [add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht]
      exact lt_of_le_of_lt (min_le_right _ _) (by linarith)
    have hre : 0 < ((z₀ + (t : ℂ)) - z₀).re := by
      rw [add_sub_cancel_left, Complex.ofReal_re]; exact ht
    have hp := hpos _ hzt hre
    have hz : f (z₀ + (t : ℂ)) = 0 := by
      have := hball (y := z₀ + (t : ℂ)) (by
        rw [dist_eq_norm, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht]
        exact lt_of_le_of_lt (min_le_left _ _) (by linarith))
      simpa using this
    rw [hz, Complex.zero_re] at hp
    exact lt_irrefl 0 hp
  set k := (analyticOrderAt f z₀).toNat with hk
  have hcast : analyticOrderAt f z₀ = (k : ℕ∞) := (ENat.coe_toNat hnetop).symm
  have hk1 : 1 ≤ k := by
    rw [hk, Nat.one_le_iff_ne_zero, ne_eq, ENat.toNat_eq_zero]
    push Not
    refine ⟨?_, hnetop⟩
    rw [ne_eq, hf.analyticOrderAt_eq_zero]
    exact fun h => h h0
  obtain ⟨h, hh, hh0, hev⟩ := (hf.analyticOrderAt_eq_natCast).mp hcast
  -- positivity for `(z − z₀)^k h z` on a smaller half-disc
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hev
  set δ' := min δ ε
  have hδ' : 0 < δ' := lt_min hδ hε
  have hpos' : ∀ z : ℂ, ‖z - z₀‖ < δ' → 0 < (z - z₀).re → 0 < ((z - z₀) ^ k * h z).re := by
    intro z hz hre
    have h1 : ‖z - z₀‖ < δ := lt_of_lt_of_le hz (min_le_left _ _)
    have h2 : dist z z₀ < ε := by rw [dist_eq_norm]; exact lt_of_lt_of_le hz (min_le_right _ _)
    have := hpos z h1 hre
    rwa [hball h2, smul_eq_mul] at this
  have hcl : ∀ w : ℂ, 0 ≤ w.re → 0 ≤ (w ^ k * h z₀).re := fun w hw =>
    re_mul_pow_nonneg_of_nonneg
      (fun w' hw' => re_mul_pow_nonneg_of_pos hh.continuousAt hδ' hpos' hw') hw
  set a := h z₀ with ha
  -- the derivative is `h z₀` when `k = 1`
  rcases Nat.lt_or_ge k 2 with hk2 | hk2
  · have hk1' : k = 1 := by omega
    have hderiv : deriv f z₀ = a := by
      have hfe : f =ᶠ[𝓝 z₀] fun z => (z - z₀) * h z := by
        filter_upwards [hev] with z hz
        rw [hz, hk1', pow_one, smul_eq_mul]
      rw [hfe.deriv_eq]
      have hd : HasDerivAt (fun z => (z - z₀) * h z) (1 * h z₀ + (z₀ - z₀) * deriv h z₀) z₀ :=
        ((hasDerivAt_id z₀).sub_const z₀).mul hh.differentiableAt.hasDerivAt
      rw [hd.deriv, sub_self, zero_mul, add_zero, one_mul]
    rw [hderiv]
    have hre1 := hcl 1 (by norm_num)
    have hreI := hcl I (by simp)
    have hrenI := hcl (-I) (by simp)
    simp only [hk1', pow_one, one_mul] at hre1 hreI hrenI
    have hi1 : (I * a).re = -a.im := by simp [Complex.mul_re]
    have hi2 : (-I * a).re = a.im := by simp [Complex.mul_re]
    rw [hi1] at hreI
    rw [hi2] at hrenI
    have him : a.im = 0 := by linarith
    refine ⟨?_, him⟩
    rcases lt_or_eq_of_le hre1 with hlt | heq
    · exact hlt
    · exfalso
      exact hh0 (Complex.ext (by rw [← heq]; rfl) (by rw [him]; rfl))
  · exfalso
    have hkpos : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
    set θ : ℝ := π / (2 * k) with hθ
    have hθle : θ ≤ π / 4 := by
      rw [hθ, div_le_div_iff₀ (by positivity) (by norm_num)]
      have : (2 : ℝ) ≤ k := by exact_mod_cast hk2
      nlinarith [Real.pi_pos]
    have hθpos : 0 < θ := by positivity
    have hkθ : (k : ℝ) * θ = π / 2 := by rw [hθ]; field_simp
    have hpow : ∀ φ : ℝ, Complex.exp ((φ : ℂ) * I) ^ k = Complex.exp (((k * φ : ℝ) : ℂ) * I) := by
      intro φ
      rw [← Complex.exp_nat_mul]
      congr 1
      push_cast
      ring
    have h1 := hcl 1 (by norm_num)
    have h2 := hcl (Complex.exp (((2 * θ : ℝ) : ℂ) * I))
      (re_exp_angle_nonneg (by rw [abs_of_pos (by positivity)]; linarith))
    have h3 := hcl (Complex.exp ((θ : ℂ) * I))
      (re_exp_angle_nonneg (by rw [abs_of_pos hθpos]; linarith))
    have h4 := hcl (Complex.exp (((-θ : ℝ) : ℂ) * I))
      (re_exp_angle_nonneg (by rw [abs_neg, abs_of_pos hθpos]; linarith))
    rw [hpow] at h2 h3 h4
    rw [one_pow, one_mul] at h1
    have e2 : ((k : ℝ) * (2 * θ)) = π := by linarith
    have e3 : ((k : ℝ) * θ) = π / 2 := hkθ
    have e4 : ((k : ℝ) * (-θ)) = -(π / 2) := by linarith
    rw [e2, Complex.exp_pi_mul_I] at h2
    rw [e3] at h3
    rw [e4] at h4
    have hI : Complex.exp (((π / 2 : ℝ) : ℂ) * I) = I := by
      rw [show (((π / 2 : ℝ) : ℂ) * I) = (π / 2 : ℂ) * I by push_cast; ring]
      exact Complex.exp_pi_div_two_mul_I
    have hnI : Complex.exp (((-(π / 2) : ℝ) : ℂ) * I) = -I := by
      rw [show (((-(π / 2) : ℝ) : ℂ) * I) = -((π / 2 : ℂ) * I) by push_cast; ring,
        Complex.exp_neg, Complex.exp_pi_div_two_mul_I, Complex.inv_I]
    rw [hI] at h3
    rw [hnI] at h4
    simp only [neg_one_mul, Complex.neg_re] at h2
    have hi1 : (I * a).re = -a.im := by simp [Complex.mul_re]
    have hi2 : (-I * a).re = a.im := by simp [Complex.mul_re]
    rw [hi1] at h3
    rw [hi2] at h4
    exact hh0 (Complex.ext (by rw [Complex.zero_re]; linarith) (by rw [Complex.zero_im]; linarith))

/-! ## Consequences for `xi` -/

/-- A mollifier analytic at an on-line zero with `Re(g ξ) > 0` on the right half-disc forces the
zero to be simple, with `g(ρ₀) ξ'(ρ₀)` a positive real number. -/
theorem simple_of_re_mul_xi_pos {g : ℂ → ℂ} {ρ₀ : ℂ} {δ : ℝ} (hδ : 0 < δ)
    (hg : AnalyticAt ℂ g ρ₀) (hρ : xi ρ₀ = 0) (hre : ρ₀.re = 1 / 2)
    (hpos : ∀ z : ℂ, ‖z - ρ₀‖ < δ → 1 / 2 < z.re → 0 < (g z * xi z).re) :
    deriv xi ρ₀ ≠ 0 ∧ 0 < (g ρ₀ * deriv xi ρ₀).re ∧ (g ρ₀ * deriv xi ρ₀).im = 0 := by
  have hxi : AnalyticAt ℂ xi ρ₀ := xi_differentiable.analyticAt ρ₀
  have hf : AnalyticAt ℂ (fun z => g z * xi z) ρ₀ := hg.mul hxi
  have h0 : g ρ₀ * xi ρ₀ = 0 := by rw [hρ, mul_zero]
  have hpos' : ∀ z : ℂ, ‖z - ρ₀‖ < δ → 0 < (z - ρ₀).re → 0 < (g z * xi z).re := by
    intro z hz hzr
    apply hpos z hz
    rw [Complex.sub_re, hre] at hzr
    linarith
  obtain ⟨hr, hi⟩ := re_deriv_pos_of_re_pos_rightHalfDisc hδ hf h0 hpos'
  have hd : deriv (fun z => g z * xi z) ρ₀ = g ρ₀ * deriv xi ρ₀ := by
    have h : HasDerivAt (fun z => g z * xi z) (deriv g ρ₀ * xi ρ₀ + g ρ₀ * deriv xi ρ₀) ρ₀ :=
      hg.differentiableAt.hasDerivAt.mul hxi.differentiableAt.hasDerivAt
    rw [h.deriv, hρ, mul_zero, zero_add]
  rw [hd] at hr hi
  refine ⟨fun h => ?_, hr, hi⟩
  rw [h, mul_zero, Complex.zero_re] at hr
  exact lt_irrefl 0 hr

/-- **An entire mollifier proves more than RH.**  If `g` is entire and `Re(g ξ) > 0` on the
half-plane `Re s > ½`, then the Riemann hypothesis holds, every zero of `xi` is simple, and
`g(ρ) ξ'(ρ)` is a positive real number at every zero. -/
theorem riemannHypothesis_and_simple_of_entire_mollifier {g : ℂ → ℂ} (hg : Differentiable ℂ g)
    (hpos : ∀ s : ℂ, 1 / 2 < s.re → 0 < (g s * xi s).re) :
    RiemannHypothesis ∧ ∀ ρ : ℂ, xi ρ = 0 →
      deriv xi ρ ≠ 0 ∧ 0 < (g ρ * deriv xi ρ).re ∧ (g ρ * deriv xi ρ).im = 0 := by
  have hright : ∀ s ∈ rightHalf, xi s ≠ 0 := by
    intro s hs h0
    have := hpos s hs
    rw [h0, mul_zero, Complex.zero_re] at this
    exact lt_irrefl 0 this
  have hRH : RiemannHypothesis := rh_iff_xi_ne_zero_right.mpr hright
  refine ⟨hRH, fun ρ hρ => ?_⟩
  have hle : ρ.re ≤ 1 / 2 := by
    by_contra h
    push Not at h
    exact hright ρ h hρ
  have hge : 1 / 2 ≤ ρ.re := by
    by_contra h
    push Not at h
    have h1 : xi (1 - ρ) = 0 := by rw [xi_one_sub]; exact hρ
    have h2 : (1 - ρ) ∈ rightHalf := by
      show 1 / 2 < (1 - ρ).re
      rw [Complex.sub_re, Complex.one_re]; linarith
    exact hright _ h2 h1
  exact simple_of_re_mul_xi_pos one_pos (hg.analyticAt ρ) hρ (le_antisymm hle hge)
    (fun z _ hz => hpos z hz)

end EntireMollifier

end RHTower
