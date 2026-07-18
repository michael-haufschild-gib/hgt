import GaloisForLFunctions.RHTower.SlabConjugatedGermTheorem

/-!
# The trace edge estimate and the vanishing of the conjugation defect

The conjugated germ theorem (`SlabConjugatedGermTheorem`) reads Hermitian fiber data off
divisor-free slab boundary integrals, with the genuinely conjugated moments differing from
their reflected forms by defect contour terms whose weights are `O(h)` pointwise on the
slab `S(γ, h) = [γ − h, γ + h] × [−c, c]`.  This module closes that surface: the defect
contour terms vanish as `h → 0⁺`, because the trace edge integrals grow only
logarithmically while the defect weight decays linearly.

* **arsinh edge calculus** — the vertical-edge integral of the inverse distance to a fiber
  point is an inverse hyperbolic sine difference
  (`integral_inv_sqrt_edge`), bounded by `2 · arsinh(2c/h)`
  (`integral_inv_sqrt_edge_le`), and `h · arsinh(K/h) → 0` as `h → 0⁺`
  (`tendsto_mul_arsinh_div`): linear decay beats logarithmic growth;
* **the trace pole decomposition** (`exists_slabTracePoleBound`) — peeling the height
  fiber from `XiC` on a reference slab (`exists_xiC_closedRectangle_factorization`)
  exhibits `logDeriv XiC` as the sum of simple fiber poles and a cofactor logarithmic
  derivative bounded on the compact reference slab: at every non-divisor point of the
  reference slab, `‖logDeriv XiC z‖ ≤ M + ∑_w m_w · ‖z − w‖⁻¹`;
* **the defect vanishing** (`tendsto_slabDisplacementDefect`) — the displacement defect
  contour term is `O(h²)` on the horizontal edges and
  `O(h) · O(M + log(1/h))` on the vertical edges, hence tends to `0` as `h → 0⁺`;
* **the capstone** (`exists_slabDisplacementMoment_tendsto_rh_equivalence`) — at every
  height there is a band strictly inside the critical strip on which the genuinely
  displacement-weighted boundary moment `(2πi)⁻¹ ∮ Im(z − γ)(z − γ) · trace` converges,
  as `h → 0⁺`, to `i` times the fiber variance; its convergence to `0` is equivalent to
  the height fiber lying on the critical line.  The conjugation defect of the
  displacement germ is thereby discharged unconditionally: the critical line at height
  `γ` is read off a genuine limit of divisor-free boundary integrals.
-/

open Complex Set Filter Topology

namespace RHTower
namespace SlabTraceEdgeEstimate

open SlabGermResidueTransport SlabFullWidthAdmissibility SlabConjugatedGermTheorem

noncomputable section

/-! ## §1 The arsinh edge calculus -/

/-- The shifted-and-scaled inverse hyperbolic sine is an antiderivative of the inverse
distance to the point `δ + i·0` at horizontal offset `h`. -/
theorem hasDerivAt_arsinh_edge {h δ : ℝ} (hh : 0 < h) (y : ℝ) :
    HasDerivAt (fun t => Real.arsinh ((t - δ) / h))
      ((Real.sqrt (h ^ 2 + (y - δ) ^ 2))⁻¹) y := by
  have hinner : HasDerivAt (fun t : ℝ => (t - δ) / h) (1 / h) y := by
    simpa using ((hasDerivAt_id y).sub_const δ).div_const h
  have hcomp := (Real.hasDerivAt_arsinh ((y - δ) / h)).comp y hinner
  convert hcomp using 1
  have hs : Real.sqrt (1 + ((y - δ) / h) ^ 2) * h = Real.sqrt (h ^ 2 + (y - δ) ^ 2) := by
    rw [show Real.sqrt (1 + ((y - δ) / h) ^ 2) * h
        = Real.sqrt ((1 + ((y - δ) / h) ^ 2) * h ^ 2) from by
      rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hh.le]]
    congr 1
    field_simp
  rw [← hs]
  field_simp

/-- The inverse distance to a fiber point is continuous in the edge parameter. -/
theorem continuous_inv_sqrt_edge {h δ : ℝ} (hh : 0 < h) :
    Continuous fun y : ℝ => (Real.sqrt (h ^ 2 + (y - δ) ^ 2))⁻¹ := by
  apply Continuous.inv₀
  · exact Real.continuous_sqrt.comp (by fun_prop)
  · intro y
    positivity

/-- **The edge integral of the inverse distance.**  Along a vertical edge at horizontal
offset `h` from a pole at height `δ`, the integral of the inverse distance evaluates to
an inverse hyperbolic sine difference. -/
theorem integral_inv_sqrt_edge {h : ℝ} (hh : 0 < h) (δ a b : ℝ) :
    ∫ y in a..b, (Real.sqrt (h ^ 2 + (y - δ) ^ 2))⁻¹ =
      Real.arsinh ((b - δ) / h) - Real.arsinh ((a - δ) / h) :=
  intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ => hasDerivAt_arsinh_edge hh y)
    ((continuous_inv_sqrt_edge hh).intervalIntegrable a b)

/-- **Logarithmic edge control.**  For a pole height inside the band, the edge integral of
the inverse distance is at most `2 · arsinh(2c/h)`. -/
theorem integral_inv_sqrt_edge_le {h c δ : ℝ} (hh : 0 < h) (hδ1 : -c ≤ δ) (hδ2 : δ ≤ c) :
    ∫ y in (-c)..c, (Real.sqrt (h ^ 2 + (y - δ) ^ 2))⁻¹ ≤
      2 * Real.arsinh (2 * c / h) := by
  rw [integral_inv_sqrt_edge hh]
  have h1 : Real.arsinh ((c - δ) / h) ≤ Real.arsinh (2 * c / h) :=
    Real.arsinh_le_arsinh.mpr (by gcongr; linarith)
  have h2 : -Real.arsinh ((-c - δ) / h) ≤ Real.arsinh (2 * c / h) := by
    rw [show (-c - δ) / h = -((c + δ) / h) from by ring, Real.arsinh_neg, neg_neg]
    exact Real.arsinh_le_arsinh.mpr (by gcongr; linarith)
  linarith

/-- The inverse hyperbolic sine is dominated by a logarithm on the nonnegative axis. -/
theorem arsinh_le_log_one_add {x : ℝ} (hx : 0 ≤ x) :
    Real.arsinh x ≤ Real.log (1 + 2 * x) := by
  rw [Real.arsinh]
  apply Real.log_le_log (by positivity)
  have : Real.sqrt (1 + x ^ 2) ≤ 1 + x := by
    rw [show (1 : ℝ) + x = Real.sqrt ((1 + x) ^ 2) from (Real.sqrt_sq (by linarith)).symm]
    apply Real.sqrt_le_sqrt
    nlinarith
  linarith

/-- **Linear decay beats logarithmic growth.**  The product `h · arsinh(K/h)` vanishes as
`h → 0⁺`. -/
theorem tendsto_mul_arsinh_div {K : ℝ} (hK : 0 < K) :
    Tendsto (fun h : ℝ => h * Real.arsinh (K / h)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hlog : Tendsto (fun h : ℝ => h * Real.log (h + 2 * K) - h * Real.log h)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have h1 : Tendsto (fun h : ℝ => h * Real.log (h + 2 * K)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      have hc : ContinuousAt (fun h : ℝ => h * Real.log (h + 2 * K)) 0 :=
        ContinuousAt.mul continuousAt_id
          ((Real.continuousAt_log (by positivity)).comp (by fun_prop))
      have h0 := hc.tendsto
      simp only [zero_mul] at h0
      exact h0.mono_left nhdsWithin_le_nhds
    have h2 : Tendsto (fun h : ℝ => h * Real.log h) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      have := tendsto_log_mul_rpow_nhdsGT_zero (r := 1) one_pos
      simp only [Real.rpow_one] at this
      simpa [mul_comm] using this
    simpa using h1.sub h2
  apply squeeze_zero'
  · filter_upwards [self_mem_nhdsWithin] with h hh
    exact mul_nonneg (le_of_lt hh) (Real.arsinh_nonneg_iff.mpr (div_nonneg hK.le (le_of_lt hh)))
  · filter_upwards [self_mem_nhdsWithin] with h hh
    have hh0 : (0 : ℝ) < h := hh
    have hb := arsinh_le_log_one_add (div_nonneg hK.le hh0.le)
    have hlogeq : Real.log (1 + 2 * (K / h)) = Real.log (h + 2 * K) - Real.log h := by
      rw [show 1 + 2 * (K / h) = (h + 2 * K) / h from by field_simp]
      exact Real.log_div (by positivity) hh0.ne'
    calc h * Real.arsinh (K / h) ≤ h * Real.log (1 + 2 * (K / h)) :=
          mul_le_mul_of_nonneg_left hb hh0.le
      _ = h * Real.log (h + 2 * K) - h * Real.log h := by rw [hlogeq]; ring
  · exact hlog

/-! ## §2 The trace pole decomposition on a reference slab -/

/-- **The trace pole bound.**  At every height there are a band strictly inside the
critical strip and a reference gap `g ≤ 1` such that: the fiber over the band is the full
height fiber; every slab below the gap has packet equal to the height fiber and admissible
boundary; and at every non-divisor point of the reference slab the trace `logDeriv XiC` is
bounded by a constant plus the simple fiber poles.  Peel the height fiber from `XiC`
(`exists_xiC_closedRectangle_factorization`); the cofactor's logarithmic derivative is
continuous on the compact reference slab, hence bounded. -/
theorem exists_slabTracePoleBound (γ : ℝ) :
    ∃ c g M : ℝ, 0 < c ∧ c < 1 / 2 ∧ 0 < g ∧ g ≤ 1 ∧
      heightFiber γ c = heightFiber γ (1 / 2) ∧
      (∀ h : ℝ, 0 < h → h ≤ g → slabPacket γ h c = heightFiber γ c) ∧
      (∀ h : ℝ, 0 < h → h ≤ g → SlabAdmissible γ h c) ∧
      0 ≤ M ∧
      ∀ z : ℂ, γ - g ≤ z.re → z.re ≤ γ + g → -c ≤ z.im → z.im ≤ c → XiC z ≠ 0 →
        ‖logDeriv XiC z‖ ≤
          M + ∑ w ∈ heightFiber γ c, xiPacketMass w * ‖z - w‖⁻¹ := by
  classical
  obtain ⟨c, h₁, hc0, hc12, hh₁pos, hfib, hadm⟩ := exists_slabAdmissible_family γ
  obtain ⟨g₀, hg₀pos, _, hgap⟩ := exists_slabGap γ c hc0.le
  set g : ℝ := min 1 (min g₀ h₁) with hgdef
  have hgpos : 0 < g := lt_min one_pos (lt_min hg₀pos hh₁pos)
  have hg1 : g ≤ 1 := min_le_left _ _
  have hgapg : ∀ h : ℝ, 0 < h → h ≤ g → slabPacket γ h c = heightFiber γ c :=
    fun h hh0 hh => hgap h hh0 (hh.trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hadmg : ∀ h : ℝ, 0 < h → h ≤ g → SlabAdmissible γ h c :=
    fun h hh0 hh => hadm h hh0 (hh.trans ((min_le_right _ _).trans (min_le_right _ _)))
  obtain ⟨m, H, hHan, hm, hH0, hfact⟩ :=
    exists_xiC_closedRectangle_factorization (slabLower γ g c) (slabUpper γ g c)
  have hzeros : xiCClosedRectangleZeros (slabLower γ g c) (slabUpper γ g c)
      = heightFiber γ c := hgapg g hgpos le_rfl
  set K : Set ℂ := uIcc (slabLower γ g c).re (slabUpper γ g c).re ×ℂ
      uIcc (slabLower γ g c).im (slabUpper γ g c).im with hKdef
  have hKcompact : IsCompact K := isCompact_uIcc.reProdIm isCompact_uIcc
  have hcontOn : ContinuousOn (logDeriv H) K := by
    intro z hz
    have hA : AnalyticAt ℂ (logDeriv H) z := by
      rw [show logDeriv H = fun w => deriv H w / H w from rfl]
      exact (hHan z (mem_univ z)).deriv.div (hHan z (mem_univ z)) (hH0 z hz)
    exact hA.continuousAt.continuousWithinAt
  obtain ⟨C, hC⟩ := hKcompact.exists_bound_of_continuousOn hcontOn
  refine ⟨c, g, max C 0, hc0, hc12, hgpos, hg1, hfib, hgapg, hadmg, le_max_right _ _, ?_⟩
  intro z hre1 hre2 him1 him2 hXi
  have hzK : z ∈ K := by
    rw [hKdef, Complex.mem_reProdIm, slabLower_re, slabUpper_re, slabLower_im, slabUpper_im,
      uIcc_of_le (by linarith : γ - g ≤ γ + g), uIcc_of_le (by linarith : -c ≤ c)]
    exact ⟨Set.mem_Icc.mpr ⟨hre1, hre2⟩, Set.mem_Icc.mpr ⟨him1, him2⟩⟩
  have hHz : H z ≠ 0 := hH0 z hzK
  rw [hzeros] at hfact hm
  have hPz : (∏ w ∈ heightFiber γ c, (z - w) ^ m w) ≠ 0 := by
    intro hP0
    apply hXi
    rw [hfact z, hP0, zero_mul]
  have hpne : ∀ w ∈ heightFiber γ c, (fun u : ℂ => (u - w) ^ m w) z ≠ 0 :=
    fun w hw => Finset.prod_ne_zero_iff.mp hPz w hw
  have hXiCfun : XiC = fun u => (∏ w ∈ heightFiber γ c, (u - w) ^ m w) * H u :=
    funext hfact
  have hlog : logDeriv XiC z =
      (∑ w ∈ heightFiber γ c, (m w : ℂ) * (z - w)⁻¹) + logDeriv H z := by
    rw [hXiCfun,
      logDeriv_mul (f := fun u => ∏ w ∈ heightFiber γ c, (u - w) ^ m w) (g := H) z
        hPz hHz (by fun_prop) (hHan z (mem_univ z)).differentiableAt,
      logDeriv_prod hpne (fun w _ => by fun_prop)]
    congr 1
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [logDeriv_fun_pow (f := fun u => u - w) (by fun_prop) (m w),
      show logDeriv (fun u : ℂ => u - w) z = (z - w)⁻¹ from by
        rw [logDeriv_apply, show deriv (fun u : ℂ => u - w) z = 1 from
          ((hasDerivAt_id z).sub_const w).deriv, one_div]]
  rw [hlog]
  have hsum : ‖∑ w ∈ heightFiber γ c, (m w : ℂ) * (z - w)⁻¹‖ ≤
      ∑ w ∈ heightFiber γ c, xiPacketMass w * ‖z - w‖⁻¹ := by
    refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun w hw => ?_))
    rw [norm_mul, norm_inv, Complex.norm_natCast, hm w hw]
    rfl
  calc ‖(∑ w ∈ heightFiber γ c, (m w : ℂ) * (z - w)⁻¹) + logDeriv H z‖
      ≤ ‖∑ w ∈ heightFiber γ c, (m w : ℂ) * (z - w)⁻¹‖ + ‖logDeriv H z‖ := norm_add_le _ _
    _ ≤ (∑ w ∈ heightFiber γ c, xiPacketMass w * ‖z - w‖⁻¹) + max C 0 :=
        add_le_add hsum ((hC z hzK).trans (le_max_left _ _))
    _ = max C 0 + ∑ w ∈ heightFiber γ c, xiPacketMass w * ‖z - w‖⁻¹ := by ring

/-! ## §3 Edge integral bounds for the displacement defect -/

private theorem trace_eq_logDeriv_XiC {z : ℂ} (hA : XiExplicitAdmissible z) :
    continuedPrimeArchSourceRelativeTrace z = logDeriv XiC z :=
  (continuedPrimeArchSourceRelativeTrace_eq_xiRelativeResolventTrace
      hA.re_pos hA.ne_one hA.zeta_ne).trans
    (logDeriv_XiC_eq_relativeResolventTrace (XiC_ne_zero_of_admissible hA)).symm

private theorem continuousOn_logDeriv_XiC_comp {s : Set ℝ} {e : ℝ → ℂ} (he : Continuous e)
    (hne : ∀ x ∈ s, XiC (e x) ≠ 0) :
    ContinuousOn (fun x => logDeriv XiC (e x)) s := by
  intro x hx
  have hA : AnalyticAt ℂ (logDeriv XiC) (e x) := by
    rw [show logDeriv XiC = fun w => deriv XiC w / XiC w from rfl]
    exact (XiC_analytic (e x) (Set.mem_univ _)).deriv.div
      (XiC_analytic (e x) (Set.mem_univ _)) (hne x hx)
  exact (hA.continuousAt.comp he.continuousAt).continuousWithinAt

private theorem xiPacketMass_nonneg (w : ℂ) : 0 ≤ xiPacketMass w := by
  unfold xiPacketMass
  exact Nat.cast_nonneg _

/-- The boundary integral of `f` around a coordinate rectangle is bounded by the four
edgewise integrals of the norm. -/
theorem norm_rectIntegral_le (f : ℂ → ℂ) {z₁ z₂ : ℂ}
    (hre : z₁.re ≤ z₂.re) (him : z₁.im ≤ z₂.im) :
    ‖rectIntegral f z₁ z₂‖ ≤
      (∫ x in z₁.re..z₂.re, ‖f ((x : ℂ) + (z₁.im : ℂ) * I)‖) +
        (∫ x in z₁.re..z₂.re, ‖f ((x : ℂ) + (z₂.im : ℂ) * I)‖) +
        (∫ y in z₁.im..z₂.im, ‖f ((z₂.re : ℂ) + (y : ℂ) * I)‖) +
        ∫ y in z₁.im..z₂.im, ‖f ((z₁.re : ℂ) + (y : ℂ) * I)‖ := by
  unfold rectIntegral
  have hB := intervalIntegral.norm_integral_le_integral_norm
    (μ := MeasureTheory.volume) (f := fun x : ℝ => f ((x : ℂ) + (z₁.im : ℂ) * I)) hre
  have hT := intervalIntegral.norm_integral_le_integral_norm
    (μ := MeasureTheory.volume) (f := fun x : ℝ => f ((x : ℂ) + (z₂.im : ℂ) * I)) hre
  have hR := intervalIntegral.norm_integral_le_integral_norm
    (μ := MeasureTheory.volume) (f := fun y : ℝ => f ((z₂.re : ℂ) + (y : ℂ) * I)) him
  have hL := intervalIntegral.norm_integral_le_integral_norm
    (μ := MeasureTheory.volume) (f := fun y : ℝ => f ((z₁.re : ℂ) + (y : ℂ) * I)) him
  have key : ∀ a b r l : ℂ, ‖a - b + I • r - I • l‖ ≤ ‖a‖ + ‖b‖ + ‖r‖ + ‖l‖ := by
    intro a b r l
    have h1 : ‖a - b + I • r - I • l‖ ≤ ‖a - b + I • r‖ + ‖I • l‖ := norm_sub_le _ _
    have h2 : ‖a - b + I • r‖ ≤ ‖a - b‖ + ‖I • r‖ := norm_add_le _ _
    have h3 : ‖a - b‖ ≤ ‖a‖ + ‖b‖ := norm_sub_le _ _
    have h4 : ‖I • r‖ = ‖r‖ := by rw [smul_eq_mul, norm_mul, Complex.norm_I, one_mul]
    have h5 : ‖I • l‖ = ‖l‖ := by rw [smul_eq_mul, norm_mul, Complex.norm_I, one_mul]
    linarith
  exact (key _ _ _ _).trans (add_le_add (add_le_add (add_le_add hB hT) hR) hL)

/-- **Vertical edge bound.**  Along an admissible vertical edge at squared horizontal
offset `h²` from the height, the norm integral of the displacement defect weight against
the trace is at most `h · (g + c)` times a constant plus `2 · arsinh(2c/h)` per unit of
fiber mass. -/
private theorem vertical_edge_integral_le {γ c g M h x₀ : ℝ}
    (hc0 : 0 < c)
    (hbound : ∀ z : ℂ, γ - g ≤ z.re → z.re ≤ γ + g → -c ≤ z.im → z.im ≤ c → XiC z ≠ 0 →
      ‖logDeriv XiC z‖ ≤ M + ∑ w ∈ heightFiber γ c, xiPacketMass w * ‖z - w‖⁻¹)
    (hh0 : 0 < h) (hhg : h ≤ g)
    (hx₀ : (x₀ - γ) ^ 2 = h ^ 2) (hx₀1 : γ - g ≤ x₀) (hx₀2 : x₀ ≤ γ + g)
    (hedge : ∀ y ∈ uIcc (-c) c, XiExplicitAdmissible ((x₀ : ℂ) + (y : ℂ) * I)) :
    (∫ y in (-c)..c,
        ‖I * ((((x₀ : ℂ) + (y : ℂ) * I - (γ : ℂ)).re : ℝ) : ℂ) *
            ((x₀ : ℂ) + (y : ℂ) * I - (γ : ℂ)) *
          continuedPrimeArchSourceRelativeTrace ((x₀ : ℂ) + (y : ℂ) * I)‖) ≤
      h * (g + c) *
        (2 * c * M +
          (∑ w ∈ heightFiber γ c, xiPacketMass w) * (2 * Real.arsinh (2 * c / h))) := by
  have hcc : -c ≤ c := by linarith
  have habs : |x₀ - γ| = h := by
    rw [← Real.sqrt_sq_eq_abs, hx₀, Real.sqrt_sq hh0.le]
  have hXine : ∀ y ∈ uIcc (-c) c, XiC ((x₀ : ℂ) + (y : ℂ) * I) ≠ 0 := fun y hy =>
    XiC_ne_zero_of_admissible (hedge y hy)
  -- the trace agrees with the logarithmic derivative along the admissible edge
  have hcongr : EqOn
      (fun y : ℝ =>
        ‖I * ((((x₀ : ℂ) + (y : ℂ) * I - (γ : ℂ)).re : ℝ) : ℂ) *
            ((x₀ : ℂ) + (y : ℂ) * I - (γ : ℂ)) *
          continuedPrimeArchSourceRelativeTrace ((x₀ : ℂ) + (y : ℂ) * I)‖)
      (fun y : ℝ =>
        ‖I * ((((x₀ : ℂ) + (y : ℂ) * I - (γ : ℂ)).re : ℝ) : ℂ) *
            ((x₀ : ℂ) + (y : ℂ) * I - (γ : ℂ)) *
          logDeriv XiC ((x₀ : ℂ) + (y : ℂ) * I)‖) (uIcc (-c) c) := by
    intro y hy
    dsimp only
    rw [trace_eq_logDeriv_XiC (hedge y hy)]
  rw [intervalIntegral.integral_congr hcongr]
  -- coordinates of the edge points relative to the height and the fiber
  have hptre : ∀ y : ℝ, ((x₀ : ℂ) + (y : ℂ) * I).re = x₀ := fun y => by simp
  have hptim : ∀ y : ℝ, ((x₀ : ℂ) + (y : ℂ) * I).im = y := fun y => by simp
  have hdist : ∀ y : ℝ, ∀ w ∈ heightFiber γ c,
      ‖(x₀ : ℂ) + (y : ℂ) * I - w‖ = Real.sqrt (h ^ 2 + (y - w.im) ^ 2) := by
    intro y w hw
    have hwre : w.re = γ := ((mem_heightFiber hc0.le).mp hw).1
    rw [Complex.norm_eq_sqrt_sq_add_sq]
    congr 2
    · rw [show ((x₀ : ℂ) + (y : ℂ) * I - w).re = x₀ - γ from by simp [hwre], ← hx₀]
    · simp
  -- pointwise bound by the constant-plus-poles profile
  have hmono : ∀ y ∈ Icc (-c) c,
      ‖I * ((((x₀ : ℂ) + (y : ℂ) * I - (γ : ℂ)).re : ℝ) : ℂ) *
          ((x₀ : ℂ) + (y : ℂ) * I - (γ : ℂ)) *
        logDeriv XiC ((x₀ : ℂ) + (y : ℂ) * I)‖ ≤
      h * (g + c) *
        (M + ∑ w ∈ heightFiber γ c,
          xiPacketMass w * (Real.sqrt (h ^ 2 + (y - w.im) ^ 2))⁻¹) := by
    intro y hy
    obtain ⟨hy1, hy2⟩ := hy
    set z : ℂ := (x₀ : ℂ) + (y : ℂ) * I with hzdef
    have hzre : (z - (γ : ℂ)).re = x₀ - γ := by simp [hzdef]
    have hzim : (z - (γ : ℂ)).im = y := by simp [hzdef]
    have hWre : |(z - (γ : ℂ)).re| ≤ h := by rw [hzre, habs]
    have hW1 : ‖I * (((z - (γ : ℂ)).re : ℝ) : ℂ) * (z - (γ : ℂ))‖ ≤ h * ‖z - (γ : ℂ)‖ :=
      norm_displacement_defect_weight hWre
    have hzγ : ‖z - (γ : ℂ)‖ ≤ g + c := by
      refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
      rw [hzre, hzim, habs]
      have hyabs : |y| ≤ c := abs_le.mpr ⟨hy1, hy2⟩
      linarith
    have hW : ‖I * (((z - (γ : ℂ)).re : ℝ) : ℂ) * (z - (γ : ℂ))‖ ≤ h * (g + c) :=
      hW1.trans (mul_le_mul_of_nonneg_left hzγ hh0.le)
    have hzXi : XiC z ≠ 0 :=
      hXine y (by rw [uIcc_of_le hcc]; exact Set.mem_Icc.mpr ⟨hy1, hy2⟩)
    have hL : ‖logDeriv XiC z‖ ≤
        M + ∑ w ∈ heightFiber γ c,
          xiPacketMass w * (Real.sqrt (h ^ 2 + (y - w.im) ^ 2))⁻¹ := by
      have hb := hbound z (by rw [hzdef, hptre]; linarith) (by rw [hzdef, hptre]; linarith)
        (by rw [hzdef, hptim]; exact hy1) (by rw [hzdef, hptim]; exact hy2) hzXi
      refine hb.trans (le_of_eq ?_)
      congr 1
      refine Finset.sum_congr rfl fun w hw => ?_
      rw [hzdef, hdist y w hw]
    rw [norm_mul]
    exact mul_le_mul hW hL (norm_nonneg _) (mul_nonneg hh0.le (by linarith))
  -- integrate the profile
  have hint_profile : IntervalIntegrable
      (fun y : ℝ => h * (g + c) *
        (M + ∑ w ∈ heightFiber γ c,
          xiPacketMass w * (Real.sqrt (h ^ 2 + (y - w.im) ^ 2))⁻¹))
      MeasureTheory.volume (-c) c := by
    apply Continuous.intervalIntegrable
    apply Continuous.mul continuous_const
    apply Continuous.add continuous_const
    exact continuous_finsetSum _ fun w _ =>
      Continuous.mul continuous_const (continuous_inv_sqrt_edge hh0)
  have hint_lhs : IntervalIntegrable
      (fun y : ℝ =>
        ‖I * ((((x₀ : ℂ) + (y : ℂ) * I - (γ : ℂ)).re : ℝ) : ℂ) *
            ((x₀ : ℂ) + (y : ℂ) * I - (γ : ℂ)) *
          logDeriv XiC ((x₀ : ℂ) + (y : ℂ) * I)‖)
      MeasureTheory.volume (-c) c := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.norm
    have hedgecont : Continuous fun y : ℝ => (x₀ : ℂ) + (y : ℂ) * I := by fun_prop
    exact (Continuous.continuousOn (by fun_prop)).mul
      (continuousOn_logDeriv_XiC_comp hedgecont hXine)
  refine (intervalIntegral.integral_mono_on hcc hint_lhs hint_profile hmono).trans ?_
  -- evaluate the profile integral
  rw [intervalIntegral.integral_const_mul]
  have hsplit : (∫ y in (-c)..c,
      (M + ∑ w ∈ heightFiber γ c,
        xiPacketMass w * (Real.sqrt (h ^ 2 + (y - w.im) ^ 2))⁻¹)) =
      (∫ _ in (-c)..c, M) +
        ∫ y in (-c)..c, ∑ w ∈ heightFiber γ c,
          xiPacketMass w * (Real.sqrt (h ^ 2 + (y - w.im) ^ 2))⁻¹ := by
    apply intervalIntegral.integral_add
    · exact intervalIntegrable_const
    · apply Continuous.intervalIntegrable
      exact continuous_finsetSum _ fun w _ =>
        Continuous.mul continuous_const (continuous_inv_sqrt_edge hh0)
  rw [hsplit]
  have hconst : (∫ _ in (-c)..c, M) = 2 * c * M := by
    rw [intervalIntegral.integral_const, smul_eq_mul]
    ring
  have hsum_le : (∫ y in (-c)..c, ∑ w ∈ heightFiber γ c,
      xiPacketMass w * (Real.sqrt (h ^ 2 + (y - w.im) ^ 2))⁻¹) ≤
      (∑ w ∈ heightFiber γ c, xiPacketMass w) * (2 * Real.arsinh (2 * c / h)) := by
    have hfs := intervalIntegral.integral_finsetSum (μ := MeasureTheory.volume)
      (a := -c) (b := c) (s := heightFiber γ c)
      (f := fun w y => xiPacketMass w * (Real.sqrt (h ^ 2 + (y - w.im) ^ 2))⁻¹)
      (fun w _ => Continuous.intervalIntegrable
        (Continuous.mul continuous_const (continuous_inv_sqrt_edge hh0)) _ _)
    rw [hfs, Finset.sum_mul]
    refine Finset.sum_le_sum fun w hw => ?_
    obtain ⟨_, ⟨hwim1, hwim2⟩, _⟩ := (mem_heightFiber hc0.le).mp hw
    rw [intervalIntegral.integral_const_mul]
    exact mul_le_mul_of_nonneg_left
      (integral_inv_sqrt_edge_le hh0 hwim1 hwim2) (xiPacketMass_nonneg w)
  have hprofsum : (∫ _ in (-c)..c, M) +
      (∫ y in (-c)..c, ∑ w ∈ heightFiber γ c,
        xiPacketMass w * (Real.sqrt (h ^ 2 + (y - w.im) ^ 2))⁻¹) ≤
      2 * c * M + (∑ w ∈ heightFiber γ c, xiPacketMass w) *
        (2 * Real.arsinh (2 * c / h)) := by
    rw [hconst]
    exact add_le_add le_rfl hsum_le
  exact mul_le_mul_of_nonneg_left hprofsum (mul_nonneg hh0.le (by linarith))

/-- **Horizontal edge bound.**  Along an admissible horizontal edge of length `2h` on
which the trace is uniformly bounded, the norm integral of the displacement defect weight
against the trace is `O(h²)`. -/
private theorem horizontal_edge_integral_le {γ c g M₁ h y₀ : ℝ}
    (hh0 : 0 < h) (hhg : h ≤ g) (hy₀ : |y₀| ≤ c)
    (hM₁ : ∀ x ∈ Icc (γ - g) (γ + g),
      ‖logDeriv XiC ((x : ℂ) + (y₀ : ℂ) * I)‖ ≤ M₁)
    (hedge : ∀ x ∈ uIcc (γ - h) (γ + h),
      XiExplicitAdmissible ((x : ℂ) + (y₀ : ℂ) * I)) :
    (∫ x in (γ - h)..(γ + h),
        ‖I * ((((x : ℂ) + (y₀ : ℂ) * I - (γ : ℂ)).re : ℝ) : ℂ) *
            ((x : ℂ) + (y₀ : ℂ) * I - (γ : ℂ)) *
          continuedPrimeArchSourceRelativeTrace ((x : ℂ) + (y₀ : ℂ) * I)‖) ≤
      2 * h * (h * (g + c) * M₁) := by
  have hlim : γ - h ≤ γ + h := by linarith
  have hXine : ∀ x ∈ uIcc (γ - h) (γ + h), XiC ((x : ℂ) + (y₀ : ℂ) * I) ≠ 0 := fun x hx =>
    XiC_ne_zero_of_admissible (hedge x hx)
  have hcongr : EqOn
      (fun x : ℝ =>
        ‖I * ((((x : ℂ) + (y₀ : ℂ) * I - (γ : ℂ)).re : ℝ) : ℂ) *
            ((x : ℂ) + (y₀ : ℂ) * I - (γ : ℂ)) *
          continuedPrimeArchSourceRelativeTrace ((x : ℂ) + (y₀ : ℂ) * I)‖)
      (fun x : ℝ =>
        ‖I * ((((x : ℂ) + (y₀ : ℂ) * I - (γ : ℂ)).re : ℝ) : ℂ) *
            ((x : ℂ) + (y₀ : ℂ) * I - (γ : ℂ)) *
          logDeriv XiC ((x : ℂ) + (y₀ : ℂ) * I)‖) (uIcc (γ - h) (γ + h)) := by
    intro x hx
    dsimp only
    rw [trace_eq_logDeriv_XiC (hedge x hx)]
  rw [intervalIntegral.integral_congr hcongr]
  have hmono : ∀ x ∈ Icc (γ - h) (γ + h),
      ‖I * ((((x : ℂ) + (y₀ : ℂ) * I - (γ : ℂ)).re : ℝ) : ℂ) *
          ((x : ℂ) + (y₀ : ℂ) * I - (γ : ℂ)) *
        logDeriv XiC ((x : ℂ) + (y₀ : ℂ) * I)‖ ≤ h * (g + c) * M₁ := by
    intro x hx
    obtain ⟨hx1, hx2⟩ := hx
    set z : ℂ := (x : ℂ) + (y₀ : ℂ) * I with hzdef
    have hzre : (z - (γ : ℂ)).re = x - γ := by simp [hzdef]
    have hzim : (z - (γ : ℂ)).im = y₀ := by simp [hzdef]
    have hWre : |(z - (γ : ℂ)).re| ≤ h := by
      rw [hzre, abs_le]
      constructor <;> linarith
    have hW1 : ‖I * (((z - (γ : ℂ)).re : ℝ) : ℂ) * (z - (γ : ℂ))‖ ≤ h * ‖z - (γ : ℂ)‖ :=
      norm_displacement_defect_weight hWre
    have hzγ : ‖z - (γ : ℂ)‖ ≤ g + c := by
      refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
      rw [hzre, hzim]
      have : |x - γ| ≤ h := by rw [abs_le]; constructor <;> linarith
      linarith
    have hW : ‖I * (((z - (γ : ℂ)).re : ℝ) : ℂ) * (z - (γ : ℂ))‖ ≤ h * (g + c) :=
      hW1.trans (mul_le_mul_of_nonneg_left hzγ hh0.le)
    have hL : ‖logDeriv XiC z‖ ≤ M₁ :=
      hM₁ x (Set.mem_Icc.mpr ⟨by linarith, by linarith⟩)
    rw [norm_mul]
    exact mul_le_mul hW hL (norm_nonneg _)
      (mul_nonneg hh0.le (by linarith [abs_nonneg y₀]))
  have hint_lhs : IntervalIntegrable
      (fun x : ℝ =>
        ‖I * ((((x : ℂ) + (y₀ : ℂ) * I - (γ : ℂ)).re : ℝ) : ℂ) *
            ((x : ℂ) + (y₀ : ℂ) * I - (γ : ℂ)) *
          logDeriv XiC ((x : ℂ) + (y₀ : ℂ) * I)‖)
      MeasureTheory.volume (γ - h) (γ + h) := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.norm
    have hedgecont : Continuous fun x : ℝ => (x : ℂ) + (y₀ : ℂ) * I := by fun_prop
    exact (Continuous.continuousOn (by fun_prop)).mul
      (continuousOn_logDeriv_XiC_comp hedgecont hXine)
  refine (intervalIntegral.integral_mono_on hlim hint_lhs intervalIntegrable_const
    hmono).trans (le_of_eq ?_)
  rw [intervalIntegral.integral_const, smul_eq_mul]
  ring

/-! ## §4 The displacement defect vanishes -/

/-- **The defect contour term vanishes.**  Under the trace pole bound, the displacement
defect contour term — the boundary pairing of the defect weight
`i · Re(z − γ) · (z − γ)` with the continued trace — tends to `0` as `h → 0⁺`: the
horizontal edges contribute `O(h²)`, the vertical edges `O(h) · O(M + arsinh(2c/h))`, and
`h · arsinh(2c/h) → 0`. -/
theorem tendsto_slabDisplacementDefect {γ c g M : ℝ}
    (hc0 : 0 < c) (hgpos : 0 < g)
    (hadmg : ∀ h : ℝ, 0 < h → h ≤ g → SlabAdmissible γ h c)
    (hbound : ∀ z : ℂ, γ - g ≤ z.re → z.re ≤ γ + g → -c ≤ z.im → z.im ≤ c → XiC z ≠ 0 →
      ‖logDeriv XiC z‖ ≤ M + ∑ w ∈ heightFiber γ c, xiPacketMass w * ‖z - w‖⁻¹) :
    Tendsto (fun h : ℝ => slabWeightedContour
        (fun z => I * (((z - (γ : ℂ)).re : ℝ) : ℂ) * (z - (γ : ℂ))) γ h c)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hgg : γ - g ≤ γ + g := by linarith
  have hadmG := hadmg g hgpos le_rfl
  -- uniform trace bounds on the two horizontal reference edges
  have hbotne : ∀ x ∈ Icc (γ - g) (γ + g),
      XiC ((x : ℂ) + ((-c : ℝ) : ℂ) * I) ≠ 0 := fun x hx =>
    XiC_ne_zero_of_admissible (hadmG.bottom x (by rwa [uIcc_of_le hgg]))
  have htopne : ∀ x ∈ Icc (γ - g) (γ + g),
      XiC ((x : ℂ) + ((c : ℝ) : ℂ) * I) ≠ 0 := fun x hx =>
    XiC_ne_zero_of_admissible (hadmG.top x (by rwa [uIcc_of_le hgg]))
  obtain ⟨Cb, hCb⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (continuousOn_logDeriv_XiC_comp (e := fun x : ℝ => (x : ℂ) + ((-c : ℝ) : ℂ) * I)
      (by fun_prop) hbotne)
  obtain ⟨Ct, hCt⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (continuousOn_logDeriv_XiC_comp (e := fun x : ℝ => (x : ℂ) + ((c : ℝ) : ℂ) * I)
      (by fun_prop) htopne)
  set M₁ : ℝ := max (max Cb Ct) 0 with hM₁def
  have hM₁0 : 0 ≤ M₁ := le_max_right _ _
  have hM₁b : ∀ x ∈ Icc (γ - g) (γ + g),
      ‖logDeriv XiC ((x : ℂ) + ((-c : ℝ) : ℂ) * I)‖ ≤ M₁ := fun x hx =>
    (hCb x hx).trans ((le_max_left _ _).trans (le_max_left _ _))
  have hM₁t : ∀ x ∈ Icc (γ - g) (γ + g),
      ‖logDeriv XiC ((x : ℂ) + ((c : ℝ) : ℂ) * I)‖ ≤ M₁ := fun x hx =>
    (hCt x hx).trans ((le_max_right _ _).trans (le_max_left _ _))
  set S : ℝ := ∑ w ∈ heightFiber γ c, xiPacketMass w with hSdef
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun w _ => xiPacketMass_nonneg w
  have hπ : ‖(2 * Real.pi * I : ℂ)⁻¹‖ = (2 * Real.pi)⁻¹ := by
    rw [norm_inv, norm_mul, norm_mul, Complex.norm_I, Complex.norm_ofNat, mul_one,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  have hπle : (2 * Real.pi)⁻¹ ≤ 1 :=
    inv_le_one_of_one_le₀ (by nlinarith [Real.pi_gt_three])
  -- the eventual bound
  have hev : ∀ h ∈ Ioc (0 : ℝ) g,
      ‖slabWeightedContour
          (fun z => I * (((z - (γ : ℂ)).re : ℝ) : ℂ) * (z - (γ : ℂ))) γ h c‖ ≤
        4 * (g + c) * M₁ * h ^ 2 + 4 * c * M * (g + c) * h +
          4 * S * (g + c) * (h * Real.arsinh (2 * c / h)) := by
    intro h hh
    obtain ⟨hh0, hhg⟩ := hh
    have hadm' := hadmg h hh0 hhg
    have hre : (slabLower γ h c).re ≤ (slabUpper γ h c).re := by
      rw [slabLower_re, slabUpper_re]; linarith
    have him : (slabLower γ h c).im ≤ (slabUpper γ h c).im := by
      rw [slabLower_im, slabUpper_im]; linarith
    have hrect := norm_rectIntegral_le
      (fun z => (I * (((z - (γ : ℂ)).re : ℝ) : ℂ) * (z - (γ : ℂ))) *
        continuedPrimeArchSourceRelativeTrace z) hre him
    rw [slabLower_re, slabUpper_re, slabLower_im, slabUpper_im] at hrect
    have hsc : slabWeightedContour
        (fun z => I * (((z - (γ : ℂ)).re : ℝ) : ℂ) * (z - (γ : ℂ))) γ h c =
        (2 * Real.pi * I : ℂ)⁻¹ *
          rectIntegral
            (fun z => (I * (((z - (γ : ℂ)).re : ℝ) : ℂ) * (z - (γ : ℂ))) *
              continuedPrimeArchSourceRelativeTrace z)
            (slabLower γ h c) (slabUpper γ h c) := rfl
    rw [hsc, norm_mul, hπ]
    refine le_trans (mul_le_of_le_one_left (norm_nonneg _) hπle) ?_
    refine hrect.trans ?_
    have hB := horizontal_edge_integral_le (γ := γ) (c := c) (g := g) hh0 hhg
      (by rw [abs_neg, abs_of_pos hc0] : |(-c : ℝ)| ≤ c) hM₁b hadm'.bottom
    have hT := horizontal_edge_integral_le (γ := γ) (c := c) (g := g) hh0 hhg
      (by rw [abs_of_pos hc0] : |(c : ℝ)| ≤ c) hM₁t hadm'.top
    have hR := vertical_edge_integral_le (x₀ := γ + h) hc0 hbound hh0 hhg
      (by ring) (by linarith) (by linarith) hadm'.right
    have hL := vertical_edge_integral_le (x₀ := γ - h) hc0 hbound hh0 hhg
      (by ring) (by linarith) (by linarith) hadm'.left
    refine le_trans (add_le_add (add_le_add (add_le_add hB hT) hR) hL) (le_of_eq ?_)
    rw [← hSdef]
    ring
  -- the bounding function tends to zero
  have hφ : Tendsto (fun h : ℝ => 4 * (g + c) * M₁ * h ^ 2 + 4 * c * M * (g + c) * h +
      4 * S * (g + c) * (h * Real.arsinh (2 * c / h))) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hsq : Tendsto (fun h : ℝ => h ^ 2) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      have : Tendsto (fun h : ℝ => h ^ 2) (𝓝 (0 : ℝ)) (𝓝 0) := by
        have := (continuous_pow 2).tendsto (0 : ℝ)
        simpa using this
      exact this.mono_left nhdsWithin_le_nhds
    have hid : Tendsto (fun h : ℝ => h) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
      tendsto_id.mono_right nhdsWithin_le_nhds
    have har : Tendsto (fun h : ℝ => h * Real.arsinh (2 * c / h)) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
      tendsto_mul_arsinh_div (by linarith)
    have := ((hsq.const_mul (4 * (g + c) * M₁)).add
      (hid.const_mul (4 * c * M * (g + c)))).add (har.const_mul (4 * S * (g + c)))
    simpa using this
  -- squeeze
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall fun h => norm_nonneg _
  · filter_upwards [Ioc_mem_nhdsGT hgpos] with h hh using hev h hh
  · exact hφ

/-! ## §5 The capstone: the displacement moment converges to the fiber variance -/

/-- **The displacement germ as a genuine limit.**  At every height there is a band
strictly inside the critical strip on which the genuinely displacement-weighted boundary
moment `(2πi)⁻¹ ∮ Im(z − γ)(z − γ) · trace` converges, as `h → 0⁺`, to `i` times the
fiber variance of the full height fiber; and its convergence to `0` is equivalent to the
height fiber lying on the critical line.  The conjugation defect of the displacement germ
(`SlabConjugatedGermTheorem`) is hereby discharged: no reflected surrogate remains in the
statement. -/
theorem exists_slabDisplacementMoment_tendsto_rh_equivalence (γ : ℝ) :
    ∃ c : ℝ, 0 < c ∧ c < 1 / 2 ∧
      Tendsto (fun h : ℝ => slabDisplacementMoment γ h c) (𝓝[>] (0 : ℝ))
        (𝓝 (I * ((fiberVariance γ (1 / 2) : ℝ) : ℂ))) ∧
      (Tendsto (fun h : ℝ => slabDisplacementMoment γ h c) (𝓝[>] (0 : ℝ)) (𝓝 0) ↔
        ∀ w ∈ heightFiber γ (1 / 2), w.im = 0) := by
  have hhalf : (0 : ℝ) ≤ 1 / 2 := by norm_num
  obtain ⟨c, g, M, hc0, hc12, hgpos, -, hfib, hgapg, hadmg, -, hbound⟩ :=
    exists_slabTracePoleBound γ
  have hD := tendsto_slabDisplacementDefect hc0 hgpos hadmg hbound
  have hanW : AnalyticOnNhd ℂ (fun z : ℂ => -I * (z - (γ : ℂ)) ^ 2) Set.univ := by
    have h1 : Differentiable ℂ fun z : ℂ => z - (γ : ℂ) := differentiable_id.sub_const _
    exact ((differentiable_const _).mul (h1.pow 2)).differentiableOn.analyticOnNhd
      isOpen_univ
  -- below the gap the moment is `i · V` plus the defect contour term
  have hval : ∀ h : ℝ, 0 < h → h ≤ g →
      slabDisplacementMoment γ h c =
        I * ((fiberVariance γ (1 / 2) : ℝ) : ℂ) +
          slabWeightedContour
            (fun z => I * (((z - (γ : ℂ)).re : ℝ) : ℂ) * (z - (γ : ℂ))) γ h c := by
    intro h hh0 hhg
    have hadm' := hadmg h hh0 hhg
    rw [slabDisplacementMoment_decomposition hadm']
    congr 1
    rw [slabDisplacementReflectedMoment,
      slabWeightedContour_eq_packetSum hh0 hc0 hadm' hanW, hgapg h hh0 hhg, hfib]
    have hsum : ∑ w ∈ heightFiber γ (1 / 2),
        ((analyticOrderAt XiC w).toNat : ℂ) * (-I * (w - (γ : ℂ)) ^ 2)
        = -I * heightFiberCenteredMoment 2 γ (1 / 2) := by
      rw [heightFiberCenteredMoment, Finset.mul_sum]
      exact Finset.sum_congr rfl fun w _ => by ring
    rw [hsum, heightFiberCenteredMoment_two hhalf]
    ring
  have hmoment : Tendsto (fun h : ℝ => slabDisplacementMoment γ h c) (𝓝[>] (0 : ℝ))
      (𝓝 (I * ((fiberVariance γ (1 / 2) : ℝ) : ℂ))) := by
    have hbase : Tendsto (fun h : ℝ =>
        I * ((fiberVariance γ (1 / 2) : ℝ) : ℂ) +
          slabWeightedContour
            (fun z => I * (((z - (γ : ℂ)).re : ℝ) : ℂ) * (z - (γ : ℂ))) γ h c)
        (𝓝[>] (0 : ℝ)) (𝓝 (I * ((fiberVariance γ (1 / 2) : ℝ) : ℂ) + 0)) :=
      tendsto_const_nhds.add hD
    rw [add_zero] at hbase
    apply hbase.congr'
    filter_upwards [Ioc_mem_nhdsGT hgpos] with h hh
    exact (hval h hh.1 hh.2).symm
  refine ⟨c, hc0, hc12, hmoment, ?_⟩
  constructor
  · intro h0
    have hIV : I * ((fiberVariance γ (1 / 2) : ℝ) : ℂ) = 0 :=
      tendsto_nhds_unique hmoment h0
    have hV : fiberVariance γ (1 / 2) = 0 := by
      rcases mul_eq_zero.mp hIV with hI | hV
      · exact absurd hI I_ne_zero
      · exact_mod_cast hV
    exact (fiberVariance_eq_zero_iff hhalf).mp hV
  · intro hline
    have hV : fiberVariance γ (1 / 2) = 0 :=
      (fiberVariance_eq_zero_iff hhalf).mpr hline
    rw [hV] at hmoment
    simpa using hmoment

end

end SlabTraceEdgeEstimate
end RHTower
