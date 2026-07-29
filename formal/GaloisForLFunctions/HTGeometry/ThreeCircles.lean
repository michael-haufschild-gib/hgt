import Mathlib.Analysis.Complex.Hadamard
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import GaloisForLFunctions.HTGeometry.BallLogarithm

/-!
# Hadamard's three-circles theorem

`log M(r)` is a convex function of `log r` for a holomorphic function on an annulus.

Mathlib has the three-*lines* theorem on a vertical strip; the three-circles theorem is its image
under the exponential map, which carries the strip `log r₁ ≤ Re w ≤ log r₃` onto the closed annulus
`r₁ ≤ |z| ≤ r₃`.  Boundedness on the strip — needed by the three-lines theorem, and not automatic
since the strip is unbounded — comes from compactness of the annulus together with the
`2πi`-periodicity of the exponential.
-/

open Complex Set Metric

namespace GaloisForLFunctions.HTGeometry

/-- The closed annulus is compact. -/
theorem isCompact_annulus (r₁ r₃ : ℝ) : IsCompact {z : ℂ | r₁ ≤ ‖z‖ ∧ ‖z‖ ≤ r₃} := by
  have hset : {z : ℂ | r₁ ≤ ‖z‖ ∧ ‖z‖ ≤ r₃} = {z : ℂ | r₁ ≤ ‖z‖} ∩ Metric.closedBall 0 r₃ := by
    ext z
    simp [Metric.mem_closedBall, dist_zero_right]
  rw [hset]
  exact (isCompact_closedBall (0 : ℂ) r₃).inter_left (isClosed_le continuous_const continuous_norm)

/-- **Hadamard's three-circles theorem.**  For a function holomorphic on the closed annulus
`r₁ ≤ |z| ≤ r₃`, the maximum modulus is logarithmically convex: at radius `|z|` it is bounded by the
geometric interpolation of the bounds on the two boundary circles, with weight
`(log |z| - log r₁) / (log r₃ - log r₁)`. -/
theorem norm_le_of_three_circles {f : ℂ → ℂ} {r₁ r₃ : ℝ} (h1 : 0 < r₁) (h13 : r₁ < r₃)
    (hd : ∀ z : ℂ, r₁ ≤ ‖z‖ → ‖z‖ ≤ r₃ → DifferentiableAt ℂ f z) {M₁ M₃ : ℝ}
    (hM1 : ∀ z : ℂ, ‖z‖ = r₁ → ‖f z‖ ≤ M₁) (hM3 : ∀ z : ℂ, ‖z‖ = r₃ → ‖f z‖ ≤ M₃) {z : ℂ}
    (hz1 : r₁ ≤ ‖z‖) (hz3 : ‖z‖ ≤ r₃) :
    ‖f z‖ ≤ M₁ ^ (1 - (Real.log ‖z‖ - Real.log r₁) / (Real.log r₃ - Real.log r₁)) *
      M₃ ^ ((Real.log ‖z‖ - Real.log r₁) / (Real.log r₃ - Real.log r₁)) := by
  have h3 : (0 : ℝ) < r₃ := lt_trans h1 h13
  set l : ℝ := Real.log r₁ with hl
  set u : ℝ := Real.log r₃ with hu
  have hlu : l < u := Real.log_lt_log h1 h13
  set g : ℂ → ℂ := fun v => f (Complex.exp v) with hg
  -- the strip maps into the annulus
  have hann : ∀ w : ℂ, w.re ∈ Icc l u → r₁ ≤ ‖Complex.exp w‖ ∧ ‖Complex.exp w‖ ≤ r₃ := by
    intro w hw
    rw [Complex.norm_exp]
    constructor
    · rw [← Real.exp_log h1]
      exact Real.exp_le_exp.mpr hw.1
    · rw [← Real.exp_log h3]
      exact Real.exp_le_exp.mpr hw.2
  have hgdiff : ∀ w : ℂ, w.re ∈ Icc l u → DifferentiableAt ℂ g w := by
    intro w hw
    obtain ⟨ha, hb⟩ := hann w hw
    exact (hd _ ha hb).comp w (Complex.differentiable_exp w)
  -- `g` is bounded on the closed strip because the annulus is compact
  have hB : BddAbove ((norm ∘ g) '' Complex.HadamardThreeLines.verticalClosedStrip l u) := by
    obtain ⟨C, hC⟩ := (isCompact_annulus r₁ r₃).exists_bound_of_continuousOn
      (fun z hz => (hd z hz.1 hz.2).continuousAt.continuousWithinAt)
    refine ⟨C, ?_⟩
    rintro _ ⟨w, hw, rfl⟩
    exact hC _ (hann w hw)
  have hcl : closure (Complex.HadamardThreeLines.verticalStrip l u)
      = Complex.HadamardThreeLines.verticalClosedStrip l u := by
    rw [Complex.HadamardThreeLines.verticalStrip,
      Complex.HadamardThreeLines.verticalClosedStrip, ← closure_Ioo (ne_of_lt hlu),
      ← Complex.closure_preimage_re]
  have hdcc : DiffContOnCl ℂ g (Complex.HadamardThreeLines.verticalStrip l u) := by
    constructor
    · intro w hw
      exact (hgdiff w ⟨le_of_lt hw.1, le_of_lt hw.2⟩).differentiableWithinAt
    · rw [hcl]
      intro w hw
      exact (hgdiff w hw).continuousAt.continuousWithinAt
  have hedgeL : ∀ w ∈ re ⁻¹' {l}, ‖g w‖ ≤ M₁ := by
    intro w hw
    refine hM1 _ ?_
    rw [Complex.norm_exp]
    have : w.re = l := hw
    rw [this, hl, Real.exp_log h1]
  have hedgeR : ∀ w ∈ re ⁻¹' {u}, ‖g w‖ ≤ M₃ := by
    intro w hw
    refine hM3 _ ?_
    rw [Complex.norm_exp]
    have : w.re = u := hw
    rw [this, hu, Real.exp_log h3]
  -- transport the target point through the exponential
  have hz0 : z ≠ 0 := by
    intro hzero
    rw [hzero, norm_zero] at hz1
    linarith
  set w : ℂ := Complex.log z with hw
  have hwre : w.re = Real.log ‖z‖ := by rw [hw, Complex.log_re]
  have hwexp : Complex.exp w = z := Complex.exp_log hz0
  have hwmem : w ∈ Complex.HadamardThreeLines.verticalClosedStrip l u := by
    refine ⟨?_, ?_⟩
    · rw [hwre, hl]
      exact Real.log_le_log h1 hz1
    · rw [hwre, hu]
      exact Real.log_le_log (lt_of_lt_of_le h1 hz1) hz3
  have hmain := Complex.HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip'
    hlu hwmem hdcc hB hedgeL hedgeR
  rw [hg] at hmain
  simp only at hmain
  rw [hwexp, hwre] at hmain
  exact hmain

/-- **Three circles about an arbitrary centre.**  The translated form of the three-circles theorem:
for `g` holomorphic on `ball c R` and `r₁ < r₃ < R`, the modulus at distance `‖z - c‖` from the
centre is bounded by the logarithmic interpolation of the bounds on the two circles. -/
theorem norm_le_of_three_circles_center {g : ℂ → ℂ} {c : ℂ} {r₁ r₃ R : ℝ} (h1 : 0 < r₁)
    (h13 : r₁ < r₃) (h3R : r₃ < R) (hg : DifferentiableOn ℂ g (ball c R)) {M₁ M₃ : ℝ}
    (hM1 : ∀ z : ℂ, ‖z - c‖ = r₁ → ‖g z‖ ≤ M₁) (hM3 : ∀ z : ℂ, ‖z - c‖ = r₃ → ‖g z‖ ≤ M₃)
    {z : ℂ} (hz1 : r₁ ≤ ‖z - c‖) (hz3 : ‖z - c‖ ≤ r₃) :
    ‖g z‖ ≤ M₁ ^ (1 - (Real.log ‖z - c‖ - Real.log r₁) / (Real.log r₃ - Real.log r₁)) *
      M₃ ^ ((Real.log ‖z - c‖ - Real.log r₁) / (Real.log r₃ - Real.log r₁)) := by
  have hdiff : ∀ w : ℂ, r₁ ≤ ‖w‖ → ‖w‖ ≤ r₃ → DifferentiableAt ℂ (fun v : ℂ => g (c + v)) w := by
    intro w _ hw3
    have hmem : c + w ∈ ball c R := by
      rw [mem_ball_iff_norm]
      simpa using lt_of_le_of_lt hw3 h3R
    exact (hg.differentiableAt (isOpen_ball.mem_nhds hmem)).comp w (by fun_prop)
  have hM1' : ∀ w : ℂ, ‖w‖ = r₁ → ‖(fun v : ℂ => g (c + v)) w‖ ≤ M₁ := by
    intro w hw
    exact hM1 (c + w) (by simpa using hw)
  have hM3' : ∀ w : ℂ, ‖w‖ = r₃ → ‖(fun v : ℂ => g (c + v)) w‖ ≤ M₃ := by
    intro w hw
    exact hM3 (c + w) (by simpa using hw)
  have hmain := norm_le_of_three_circles h1 h13 hdiff hM1' hM3' hz1 hz3
  simpa using hmain

/-- **Sharpened lower bound via three circles.**  If `f = f c · exp g` on a disc and the branch `g`
is bounded by `M₁` on the inner circle and by `M₃` on the outer one, then on the intermediate circle
`‖f‖` is at least `‖f c‖ exp(-M₁^{1-t} M₃^{t})`, with `t` the logarithmic interpolation weight.

When `M₁` is an absolute constant and `M₃` grows like `log|t|`, the interpolated exponent is
`(log|t|)^{t}` with `t < 1` strictly — subpolynomial, which a direct Borel–Carathéodory bound is
not. -/
theorem norm_lower_bound_of_three_circles {f g : ℂ → ℂ} {c : ℂ} {R r₁ r₃ : ℝ} (h1 : 0 < r₁)
    (h13 : r₁ < r₃) (h3R : r₃ < R) (hg : DifferentiableOn ℂ g (ball c R))
    (hfg : ∀ z ∈ ball c R, f z = f c * Complex.exp (g z)) {M₁ M₃ : ℝ}
    (hM1 : ∀ z : ℂ, ‖z - c‖ = r₁ → ‖g z‖ ≤ M₁) (hM3 : ∀ z : ℂ, ‖z - c‖ = r₃ → ‖g z‖ ≤ M₃)
    {z : ℂ} (hz1 : r₁ ≤ ‖z - c‖) (hz3 : ‖z - c‖ ≤ r₃) :
    ‖f c‖ * Real.exp
        (-(M₁ ^ (1 - (Real.log ‖z - c‖ - Real.log r₁) / (Real.log r₃ - Real.log r₁)) *
          M₃ ^ ((Real.log ‖z - c‖ - Real.log r₁) / (Real.log r₃ - Real.log r₁))))
      ≤ ‖f z‖ := by
  have hzmem : z ∈ ball c R := by
    rw [mem_ball_iff_norm]
    exact lt_of_le_of_lt hz3 h3R
  have hbound := norm_le_of_three_circles_center h1 h13 h3R hg hM1 hM3 hz1 hz3
  have hmod : ‖f z‖ = ‖f c‖ * Real.exp ((g z).re) := by
    rw [hfg z hzmem, norm_mul, Complex.norm_exp]
  have hre : -(M₁ ^ (1 - (Real.log ‖z - c‖ - Real.log r₁) / (Real.log r₃ - Real.log r₁)) *
      M₃ ^ ((Real.log ‖z - c‖ - Real.log r₁) / (Real.log r₃ - Real.log r₁))) ≤ (g z).re := by
    have h1' : |(g z).re| ≤ ‖g z‖ := Complex.abs_re_le_norm _
    have h2' : -(g z).re ≤ |(g z).re| := neg_le_abs _
    linarith
  rw [hmod]
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hre) (norm_nonneg _)

/-- **Two-radius lower bound.**  A nonvanishing holomorphic function on `ball c R` that is bounded
between `mi` and `Mi` on a small disc `ball c ρ`, and by `M` on all of `ball c R`, satisfies

`‖f z‖ ≥ ‖f c‖ exp(-(B₁^{1-t} B₃^{t}))`,  `t = (log‖z-c‖ - log r₁)/(log r₃ - log r₁)`,

with `B₁, B₃` the Borel–Carathéodory bounds attached to the two radii.

The point is that the same branch of the logarithm is bounded twice, with a *different* ratio
`M/m` each time: a good ratio on the small disc and a bad one on the large disc.  The three-circles
interpolation then gives a bound governed mostly by the good ratio. -/
theorem norm_lower_bound_of_two_radii {f : ℂ → ℂ} {c : ℂ} {ρ R r₁ r₃ : ℝ} (h1 : 0 < r₁)
    (h1ρ : r₁ < ρ) (hρR : ρ ≤ R) (h13 : r₁ < r₃) (h3R : r₃ < R)
    (hf : DifferentiableOn ℂ f (ball c R)) (hne : ∀ z ∈ ball c R, f z ≠ 0) {Mi mi M m : ℝ}
    (hMi : ∀ z ∈ ball c ρ, ‖f z‖ ≤ Mi) (hmi0 : 0 < mi) (hmi : mi ≤ ‖f c‖)
    (hM : ∀ z ∈ ball c R, ‖f z‖ ≤ M) (hm0 : 0 < m) (hm : m ≤ ‖f c‖) {z : ℂ}
    (hz1 : r₁ ≤ ‖z - c‖) (hz3 : ‖z - c‖ ≤ r₃) :
    ‖f c‖ * Real.exp
        (-((2 * (Real.log (Mi / mi) + 1) * r₁ / (ρ - r₁)) ^
            (1 - (Real.log ‖z - c‖ - Real.log r₁) / (Real.log r₃ - Real.log r₁)) *
          (2 * (Real.log (M / m) + 1) * r₃ / (R - r₃)) ^
            ((Real.log ‖z - c‖ - Real.log r₁) / (Real.log r₃ - Real.log r₁))))
      ≤ ‖f z‖ := by
  have hR : (0 : ℝ) < R := lt_trans (lt_trans h1 h13) h3R
  obtain ⟨g, hgon, hg0, hgeq⟩ := exists_log_on_ball hR hf hne
  have hsub : ball c ρ ⊆ ball c R := ball_subset_ball hρR
  have hinner : ∀ w : ℂ, ‖w - c‖ = r₁ →
      ‖g w‖ ≤ 2 * (Real.log (Mi / mi) + 1) * r₁ / (ρ - r₁) := fun w hw =>
    norm_log_le_of_ball h1.le h1ρ (hgon.mono hsub) hg0 (fun x hx => hgeq x (hsub hx)) hMi hmi0 hmi
      (le_of_eq hw)
  have houter : ∀ w : ℂ, ‖w - c‖ = r₃ →
      ‖g w‖ ≤ 2 * (Real.log (M / m) + 1) * r₃ / (R - r₃) := fun w hw =>
    norm_log_le_of_ball (le_of_lt (lt_trans h1 h13)) h3R hgon hg0 hgeq hM hm0 hm (le_of_eq hw)
  exact norm_lower_bound_of_three_circles h1 h13 h3R hgon hgeq hinner houter hz1 hz3

/-- **Subpolynomial growth.**  A power `θ < 1` of the logarithm is eventually dominated by every
positive multiple of the logarithm, so `exp((log t)^θ)` is eventually below every positive power of
`t`.  This is what turns the logarithmically convex bound of the three-circles theorem into a
genuinely subpolynomial one. -/
theorem eventually_exp_log_rpow_le_rpow {θ : ℝ} (hθ1 : θ < 1) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ t : ℝ in Filter.atTop, Real.exp ((Real.log t) ^ θ) ≤ t ^ ε := by
  have h1 : (0 : ℝ) < 1 - θ := by linarith
  have hlim : Filter.Tendsto (fun t : ℝ => (Real.log t) ^ (θ - 1)) Filter.atTop (nhds 0) := by
    have hcomp := (tendsto_rpow_neg_atTop h1).comp Real.tendsto_log_atTop
    have hexp : -(1 - θ) = θ - 1 := by ring
    rw [show (fun t : ℝ => (Real.log t) ^ (θ - 1)) =
      (fun x : ℝ => x ^ (θ - 1)) ∘ Real.log by rfl]
    rw [← hexp]
    exact hcomp
  have hev : ∀ᶠ t : ℝ in Filter.atTop, (Real.log t) ^ (θ - 1) < ε :=
    hlim (Iio_mem_nhds hε)
  filter_upwards [hev, Filter.eventually_ge_atTop (Real.exp 1)] with t ht hte
  have htpos : (0 : ℝ) < t := lt_of_lt_of_le (Real.exp_pos 1) hte
  have hlog1 : (1 : ℝ) ≤ Real.log t := by
    have hle : Real.log (Real.exp 1) ≤ Real.log t := Real.log_le_log (Real.exp_pos 1) hte
    rwa [Real.log_exp] at hle
  have hlogpos : (0 : ℝ) < Real.log t := by linarith
  have hsplit : (Real.log t) ^ (θ - 1) * Real.log t = (Real.log t) ^ θ := by
    nth_rewrite 2 [← Real.rpow_one (Real.log t)]
    rw [← Real.rpow_add hlogpos]
    ring_nf
  rw [Real.rpow_def_of_pos htpos]
  refine Real.exp_le_exp.mpr ?_
  calc (Real.log t) ^ θ = (Real.log t) ^ (θ - 1) * Real.log t := hsplit.symm
    _ ≤ ε * Real.log t := by nlinarith
    _ = Real.log t * ε := by ring

/-- A constant times a power `θ < 1` is eventually below every positive multiple of the
identity. -/
theorem eventually_const_mul_rpow_le {c θ : ℝ} (hθ1 : θ < 1) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ L : ℝ in Filter.atTop, c * L ^ θ ≤ ε * L := by
  have h1 : (0 : ℝ) < 1 - θ := by linarith
  have hlim : Filter.Tendsto (fun L : ℝ => L ^ (θ - 1)) Filter.atTop (nhds 0) := by
    have hexp : -(1 - θ) = θ - 1 := by ring
    simpa [hexp] using tendsto_rpow_neg_atTop h1
  have hev : ∀ᶠ L : ℝ in Filter.atTop, c * L ^ (θ - 1) < ε := by
    have hlim' : Filter.Tendsto (fun L : ℝ => c * L ^ (θ - 1)) Filter.atTop (nhds 0) := by
      simpa using hlim.const_mul c
    exact hlim' (Iio_mem_nhds hε)
  filter_upwards [hev, Filter.eventually_gt_atTop (0 : ℝ)] with L hL hL0
  have hsplit : L ^ (θ - 1) * L = L ^ θ := by
    nth_rewrite 2 [← Real.rpow_one L]
    rw [← Real.rpow_add hL0]
    ring_nf
  calc c * L ^ θ = c * L ^ (θ - 1) * L := by rw [← hsplit]; ring
    _ ≤ ε * L := mul_le_mul_of_nonneg_right hL.le hL0.le

/-- A positive continuous function on `[a, ∞)` that tends to infinity has a positive lower
bound. -/
theorem exists_pos_lower_bound_of_tendsto_atTop {f : ℝ → ℝ} {a : ℝ}
    (hcont : ContinuousOn f (Ici a)) (hpos : ∀ u ∈ Ici a, 0 < f u)
    (hlim : Filter.Tendsto f Filter.atTop Filter.atTop) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ u ∈ Ici a, κ ≤ f u := by
  obtain ⟨U, hU⟩ := Filter.eventually_atTop.mp (hlim.eventually_ge_atTop 1)
  set U' : ℝ := max a U with hU'
  have hne : (Icc a U').Nonempty := Set.nonempty_Icc.mpr (le_max_left _ _)
  obtain ⟨x₀, hx₀mem, hx₀min⟩ :=
    isCompact_Icc.exists_isMinOn hne (hcont.mono Set.Icc_subset_Ici_self)
  refine ⟨min (f x₀) 1, lt_min (hpos x₀ (Set.Icc_subset_Ici_self hx₀mem)) one_pos, fun u hu => ?_⟩
  rcases le_or_gt u U' with h | h
  · exact le_trans (min_le_left _ _) (hx₀min (Set.mem_Icc.mpr ⟨hu, h⟩))
  · refine le_trans (min_le_right _ _) (hU u ?_)
    exact le_of_lt (lt_of_le_of_lt (le_max_right a U) h)

end GaloisForLFunctions.HTGeometry
