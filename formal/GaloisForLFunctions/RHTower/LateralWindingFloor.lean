/-
The archimedean winding floor away from the critical line.

Along a vertical edge `τ ↦ σ + iτ` at any abscissa `σ` in the strip, the completed
archimedean envelope `archFactor` never vanishes, so its phase advances at the rate
`Re(archFactor′/archFactor)`.  Off the line the rational part `(2s−1)/(s(s−1)) = 1/s + 1/(s−1)`
is no longer purely imaginary, but its real part is explicitly bounded by `O(1/τ²)`, and the
vertical digamma bound holds at every abscissa; the winding rate therefore carries the same
explicit `½·log(τ/2π)` floor as on the line, at the price of a `(1−σ)/τ²` correction.

A nonvanishing path with logarithmic derivative `ω` transports by the exponential of the
primitive of `ω` — no zero can appear, no phase can slip — so the envelope along a lateral
edge is a positive modulus times a unimodular phase whose advance is exactly the integrated
winding rate.  Feeding the floor through this polar presentation into the Euler-tail winding
lemma forces a transversal band-edge event on any lateral edge long enough that the
archimedean floor beats `π` plus the anchor and Dirichlet phase budgets: the archimedean
input is unconditional and explicit, and the residual hypotheses are finite Dirichlet phase
data on the edge.
-/
import GaloisForLFunctions.RHTower.ArchWinding
import GaloisForLFunctions.RHTower.DigammaAsymptotic
import GaloisForLFunctions.RHTower.EulerTailWinding

open Complex Metric MeasureTheory

namespace RHTower

/-! ### The strip point and the envelope along a lateral edge -/

/-- The point at abscissa `σ` and height `τ`. -/
noncomputable def stripPt (σ τ : ℝ) : ℂ := (σ : ℂ) + (τ : ℂ) * I

theorem stripPt_re (σ τ : ℝ) : (stripPt σ τ).re = σ := by unfold stripPt; simp

theorem stripPt_im (σ τ : ℝ) : (stripPt σ τ).im = τ := by unfold stripPt; simp

/-- At the central abscissa the strip point is the critical-line point. -/
theorem stripPt_one_half : stripPt (1 / 2) = linePt := by
  funext τ
  unfold stripPt linePt
  norm_num

theorem hasDerivAt_stripPt (σ τ : ℝ) : HasDerivAt (stripPt σ) Complex.I τ := by
  unfold stripPt
  simpa using
    (((Complex.ofRealCLM.hasDerivAt (x := τ)).mul_const Complex.I).const_add ((σ : ℝ) : ℂ))

theorem stripPt_ne_zero {σ τ : ℝ} (hτ : τ ≠ 0) : stripPt σ τ ≠ 0 := by
  intro h0
  have h := congrArg Complex.im h0
  rw [stripPt_im] at h
  exact hτ (by simpa using h)

theorem stripPt_ne_one {σ τ : ℝ} (hτ : τ ≠ 0) : stripPt σ τ ≠ 1 := by
  intro h1
  have h := congrArg Complex.im h1
  rw [stripPt_im] at h
  exact hτ (by simpa using h)

/-- The completed archimedean envelope never vanishes off the real axis in the right
half plane. -/
theorem archFactor_stripPt_ne_zero {σ τ : ℝ} (hσ : 0 < σ) (hτ : τ ≠ 0) :
    archFactor (stripPt σ τ) ≠ 0 :=
  archFactor_ne_zero (stripPt_ne_zero hτ) (stripPt_ne_one hτ)
    (Gammaℝ_ne_zero_of_re_pos (by rw [stripPt_re]; exact hσ))

/-- Lateral derivative of the envelope: the vertical edge has tangent `i`. -/
theorem hasDerivAt_archFactor_strip {σ : ℝ} (hσ : 0 < σ) (τ : ℝ) :
    HasDerivAt (fun τ : ℝ => archFactor (stripPt σ τ))
      (archFactorDeriv (stripPt σ τ) * Complex.I) τ := by
  have hre : 0 < (stripPt σ τ).re := by rw [stripPt_re]; exact hσ
  have hcomp := HasDerivAt.comp τ (hasDerivAt_archFactor_of_re_pos hre) (hasDerivAt_stripPt σ τ)
  simpa [Function.comp] using hcomp

/-! ### The strip winding datum and its digamma form -/

/-- The complex winding datum `archFactor′/archFactor` along the vertical edge at
abscissa `σ`. -/
noncomputable def stripWinding (σ τ : ℝ) : ℂ :=
  archFactorDeriv (stripPt σ τ) / archFactor (stripPt σ τ)

/-- The lateral winding rate: the phase velocity of the envelope along the edge. -/
noncomputable def stripWindingRate (σ τ : ℝ) : ℝ := (stripWinding σ τ).re

/-- At the central abscissa the strip winding datum is the critical-line winding datum. -/
theorem stripWinding_one_half : stripWinding (1 / 2) = archWinding := by
  funext τ
  unfold stripWinding archWinding
  rw [stripPt_one_half]

/-- At the central abscissa the lateral winding rate is the critical-line winding rate. -/
theorem stripWindingRate_one_half : stripWindingRate (1 / 2) = windingRate := by
  funext τ
  unfold stripWindingRate windingRate
  rw [stripWinding_one_half]

theorem archFactorDeriv_strip_eq_mul {σ τ : ℝ} (hσ : 0 < σ) (hτ : τ ≠ 0) :
    archFactorDeriv (stripPt σ τ) = archFactor (stripPt σ τ) * stripWinding σ τ := by
  unfold stripWinding
  rw [mul_comm, div_mul_cancel₀ _ (archFactor_stripPt_ne_zero hσ hτ)]

/-- The strip winding datum in rational-plus-digamma form. -/
theorem stripWinding_eq {σ τ : ℝ} (hσ : 0 < σ) (hτ : τ ≠ 0) :
    stripWinding σ τ = (2 * stripPt σ τ - 1) / (stripPt σ τ * (stripPt σ τ - 1)) +
      (Complex.digamma ((stripPt σ τ) / 2) / 2 - (Real.log Real.pi : ℂ) / 2) := by
  have hG : Complex.Gammaℝ (stripPt σ τ) ≠ 0 :=
    Gammaℝ_ne_zero_of_re_pos (by rw [stripPt_re]; exact hσ)
  have hs0 : stripPt σ τ ≠ 0 := stripPt_ne_zero hτ
  have hs1 : stripPt σ τ - 1 ≠ 0 := sub_ne_zero.mpr (stripPt_ne_one hτ)
  unfold stripWinding archFactorDeriv archFactor
  field_simp

/-! ### The rational real-part budget off the line -/

/-- **Lower budget for the rational part.**  Off the line the rational term
`(2s−1)/(s(s−1)) = 1/s + 1/(s−1)` acquires a real part; in the strip it is bounded below
by `(σ−1)/τ²`: the `1/s` piece is nonnegative and the `1/(s−1)` piece loses at most
`(1−σ)/τ²`. -/
theorem strip_rational_re_ge {σ τ : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hτ : 0 < τ) :
    (σ - 1) / τ ^ 2 ≤ ((2 * stripPt σ τ - 1) / (stripPt σ τ * (stripPt σ τ - 1))).re := by
  have hs0 : stripPt σ τ ≠ 0 := stripPt_ne_zero (ne_of_gt hτ)
  have hs1 : stripPt σ τ - 1 ≠ 0 := sub_ne_zero.mpr (stripPt_ne_one (ne_of_gt hτ))
  have hsplit : (2 * stripPt σ τ - 1) / (stripPt σ τ * (stripPt σ τ - 1))
      = (stripPt σ τ)⁻¹ + (stripPt σ τ - 1)⁻¹ := by
    field_simp
    ring
  have hsub : stripPt σ τ - 1 = ((σ - 1 : ℝ) : ℂ) + (τ : ℂ) * Complex.I := by
    unfold stripPt
    push_cast
    ring
  have hn1 : Complex.normSq (stripPt σ τ) = σ ^ 2 + τ ^ 2 := by
    unfold stripPt
    exact Complex.normSq_add_mul_I σ τ
  have hn2 : Complex.normSq (stripPt σ τ - 1) = (σ - 1) ^ 2 + τ ^ 2 := by
    rw [hsub]
    exact Complex.normSq_add_mul_I (σ - 1) τ
  have hre2 : (stripPt σ τ - 1).re = σ - 1 := by rw [hsub]; simp
  rw [hsplit, Complex.add_re, Complex.inv_re, Complex.inv_re, hn1, hn2, stripPt_re, hre2]
  have h1 : (0 : ℝ) ≤ σ / (σ ^ 2 + τ ^ 2) := by positivity
  have h2 : (σ - 1) / τ ^ 2 ≤ (σ - 1) / ((σ - 1) ^ 2 + τ ^ 2) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_nonneg (sq_nonneg (σ - 1)) (sub_nonneg.mpr hσ1)]
  linarith

/-- **Upper budget for the rational part.**  In the strip the rational term's real part is
at most `σ/τ²`: the `1/(s−1)` piece is nonpositive and the `1/s` piece gains at most
`σ/τ²`. -/
theorem strip_rational_re_le {σ τ : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hτ : 0 < τ) :
    ((2 * stripPt σ τ - 1) / (stripPt σ τ * (stripPt σ τ - 1))).re ≤ σ / τ ^ 2 := by
  have hs0 : stripPt σ τ ≠ 0 := stripPt_ne_zero (ne_of_gt hτ)
  have hs1 : stripPt σ τ - 1 ≠ 0 := sub_ne_zero.mpr (stripPt_ne_one (ne_of_gt hτ))
  have hsplit : (2 * stripPt σ τ - 1) / (stripPt σ τ * (stripPt σ τ - 1))
      = (stripPt σ τ)⁻¹ + (stripPt σ τ - 1)⁻¹ := by
    field_simp
    ring
  have hsub : stripPt σ τ - 1 = ((σ - 1 : ℝ) : ℂ) + (τ : ℂ) * Complex.I := by
    unfold stripPt
    push_cast
    ring
  have hn1 : Complex.normSq (stripPt σ τ) = σ ^ 2 + τ ^ 2 := by
    unfold stripPt
    exact Complex.normSq_add_mul_I σ τ
  have hn2 : Complex.normSq (stripPt σ τ - 1) = (σ - 1) ^ 2 + τ ^ 2 := by
    rw [hsub]
    exact Complex.normSq_add_mul_I (σ - 1) τ
  have hre2 : (stripPt σ τ - 1).re = σ - 1 := by rw [hsub]; simp
  rw [hsplit, Complex.add_re, Complex.inv_re, Complex.inv_re, hn1, hn2, stripPt_re, hre2]
  have h1 : σ / (σ ^ 2 + τ ^ 2) ≤ σ / τ ^ 2 :=
    div_le_div₀ hσ.le le_rfl (by positivity) (by nlinarith [sq_nonneg σ])
  have h2 : (σ - 1) / ((σ - 1) ^ 2 + τ ^ 2) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
  linarith

/-- **To the right of `σ = 1` the rational part costs nothing**: both pieces `1/s` and
`1/(s−1)` have nonnegative real part there. -/
theorem strip_rational_re_nonneg {σ τ : ℝ} (hσ1 : 1 ≤ σ) (hτ : 0 < τ) :
    0 ≤ ((2 * stripPt σ τ - 1) / (stripPt σ τ * (stripPt σ τ - 1))).re := by
  have hσ : (0 : ℝ) < σ := lt_of_lt_of_le one_pos hσ1
  have hs0 : stripPt σ τ ≠ 0 := stripPt_ne_zero (ne_of_gt hτ)
  have hs1 : stripPt σ τ - 1 ≠ 0 := sub_ne_zero.mpr (stripPt_ne_one (ne_of_gt hτ))
  have hsplit : (2 * stripPt σ τ - 1) / (stripPt σ τ * (stripPt σ τ - 1))
      = (stripPt σ τ)⁻¹ + (stripPt σ τ - 1)⁻¹ := by
    field_simp
    ring
  have hsub : stripPt σ τ - 1 = ((σ - 1 : ℝ) : ℂ) + (τ : ℂ) * Complex.I := by
    unfold stripPt
    push_cast
    ring
  have hn1 : Complex.normSq (stripPt σ τ) = σ ^ 2 + τ ^ 2 := by
    unfold stripPt
    exact Complex.normSq_add_mul_I σ τ
  have hn2 : Complex.normSq (stripPt σ τ - 1) = (σ - 1) ^ 2 + τ ^ 2 := by
    rw [hsub]
    exact Complex.normSq_add_mul_I (σ - 1) τ
  have hre2 : (stripPt σ τ - 1).re = σ - 1 := by rw [hsub]; simp
  rw [hsplit, Complex.add_re, Complex.inv_re, Complex.inv_re, hn1, hn2, stripPt_re, hre2]
  have h1 : (0 : ℝ) ≤ σ / (σ ^ 2 + τ ^ 2) := by positivity
  have h2 : (0 : ℝ) ≤ (σ - 1) / ((σ - 1) ^ 2 + τ ^ 2) :=
    div_nonneg (by linarith) (by positivity)
  linarith

/-! ### The off-line winding floor -/

/-- **The off-line archimedean winding floor.**  The critical-line floor
`(log(τ/2π) − 4/τ² − π/τ)/2` conceded by `(1−σ)/τ²` for the real part the rational term
acquires off the line. -/
noncomputable def stripFloor (σ τ : ℝ) : ℝ :=
  (Real.log (τ / (2 * Real.pi)) - (4 / τ ^ 2 + Real.pi / τ)) / 2 - (1 - σ) / τ ^ 2

/-- In the strip the off-line floor concedes to the critical-line floor expression. -/
theorem stripFloor_le_line_floor {σ τ : ℝ} (hσ1 : σ ≤ 1) (hτ : 0 < τ) :
    stripFloor σ τ ≤ (Real.log (τ / (2 * Real.pi)) - (4 / τ ^ 2 + Real.pi / τ)) / 2 := by
  unfold stripFloor
  have h : (0 : ℝ) ≤ (1 - σ) / τ ^ 2 := by
    apply div_nonneg (by linarith) (by positivity)
  linarith

/-- **The lateral winding rate carries the explicit off-line floor**: at every abscissa
`0 < σ ≤ 1` and height `τ > 0`,
`Re(archFactor′/archFactor)(σ+iτ) ≥ (log(τ/2π) − 4/τ² − π/τ)/2 − (1−σ)/τ²`.
The digamma vertical bound holds at every abscissa; only the rational term pays for
leaving the line. -/
theorem stripWindingRate_ge {σ τ : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hτ : 0 < τ) :
    stripFloor σ τ ≤ stripWindingRate σ τ := by
  have hrat := strip_rational_re_ge hσ hσ1 hτ
  unfold stripWindingRate
  rw [stripWinding_eq hσ (ne_of_gt hτ), Complex.add_re]
  have harg : (stripPt σ τ) / 2 = ((σ / 2 : ℝ) : ℂ) + ((τ / 2 : ℝ) : ℂ) * Complex.I := by
    unfold stripPt
    push_cast
    ring
  have h := re_digamma_ge (x := σ / 2) (y := τ / 2) (by positivity) (by positivity)
  rw [← harg] at h
  have e1 : 1 / ((τ / 2) ^ 2) = 4 / τ ^ 2 := by
    rw [show ((τ : ℝ) / 2) ^ 2 = τ ^ 2 / 4 from by ring, one_div_div]
  have e2 : 2 * (τ / 2) = τ := by ring
  rw [e1, e2] at h
  have hΨre : ((Complex.digamma ((stripPt σ τ) / 2) / 2 - (Real.log Real.pi : ℂ) / 2)).re
      = (Complex.digamma ((stripPt σ τ) / 2)).re / 2 - Real.log Real.pi / 2 := by
    rw [Complex.sub_re, re_div_two, re_div_two, Complex.ofReal_re]
  rw [hΨre]
  have hlog : Real.log (τ / (2 * Real.pi)) = Real.log (τ / 2) - Real.log Real.pi := by
    rw [show τ / (2 * Real.pi) = (τ / 2) / Real.pi from by ring,
      Real.log_div (by positivity : (0 : ℝ) < τ / 2).ne' (ne_of_gt Real.pi_pos)]
  have hneg : (σ - 1) / τ ^ 2 = -((1 - σ) / τ ^ 2) := by ring
  unfold stripFloor
  rw [hlog]
  linarith [hneg ▸ hrat]

/-- **To the right of `σ = 1` the lateral winding rate carries the full critical-line floor
with no concession**: the rational part's real part is nonnegative there, so only the
digamma bound speaks. -/
theorem stripWindingRate_ge_of_one_le {σ τ : ℝ} (hσ1 : 1 ≤ σ) (hτ : 0 < τ) :
    (Real.log (τ / (2 * Real.pi)) - (4 / τ ^ 2 + Real.pi / τ)) / 2 ≤ stripWindingRate σ τ := by
  have hσ : (0 : ℝ) < σ := lt_of_lt_of_le one_pos hσ1
  have hrat := strip_rational_re_nonneg hσ1 hτ
  unfold stripWindingRate
  rw [stripWinding_eq hσ (ne_of_gt hτ), Complex.add_re]
  have harg : (stripPt σ τ) / 2 = ((σ / 2 : ℝ) : ℂ) + ((τ / 2 : ℝ) : ℂ) * Complex.I := by
    unfold stripPt
    push_cast
    ring
  have h := re_digamma_ge (x := σ / 2) (y := τ / 2) (by positivity) (by positivity)
  rw [← harg] at h
  have e1 : 1 / ((τ / 2) ^ 2) = 4 / τ ^ 2 := by
    rw [show ((τ : ℝ) / 2) ^ 2 = τ ^ 2 / 4 from by ring, one_div_div]
  have e2 : 2 * (τ / 2) = τ := by ring
  rw [e1, e2] at h
  have hΨre : ((Complex.digamma ((stripPt σ τ) / 2) / 2 - (Real.log Real.pi : ℂ) / 2)).re
      = (Complex.digamma ((stripPt σ τ) / 2)).re / 2 - Real.log Real.pi / 2 := by
    rw [Complex.sub_re, re_div_two, re_div_two, Complex.ofReal_re]
  rw [hΨre]
  have hlog : Real.log (τ / (2 * Real.pi)) = Real.log (τ / 2) - Real.log Real.pi := by
    rw [show τ / (2 * Real.pi) = (τ / 2) / Real.pi from by ring,
      Real.log_div (by positivity : (0 : ℝ) < τ / 2).ne' (ne_of_gt Real.pi_pos)]
  rw [hlog]
  linarith

/-- **The lateral winding rate's ceiling**: the digamma vertical bound and the rational
budget cap the rate by the logarithm of the distance to the origin plus explicit `1/τ`
corrections — the winding datum is bounded on both sides off the line. -/
theorem stripWindingRate_le {σ τ : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hτ : 0 < τ) :
    stripWindingRate σ τ ≤
      (Real.log ((σ ^ 2 + τ ^ 2) / 4) / 2 - Real.log Real.pi) / 2
        + (4 / τ ^ 2 + Real.pi / τ) / 2 + σ / τ ^ 2 := by
  have hrat := strip_rational_re_le hσ hσ1 hτ
  unfold stripWindingRate
  rw [stripWinding_eq hσ (ne_of_gt hτ), Complex.add_re]
  have harg : (stripPt σ τ) / 2 = ((σ / 2 : ℝ) : ℂ) + ((τ / 2 : ℝ) : ℂ) * Complex.I := by
    unfold stripPt
    push_cast
    ring
  have hb := re_digamma_vertical_bound_uncond (σ := σ / 2) (t := τ / 2)
    (by positivity) (by positivity)
  rw [← harg] at hb
  have habs := abs_le.mp hb
  have e0 : (σ / 2) ^ 2 + (τ / 2) ^ 2 = (σ ^ 2 + τ ^ 2) / 4 := by ring
  have e1 : 1 / ((τ / 2) ^ 2) = 4 / τ ^ 2 := by
    rw [show ((τ : ℝ) / 2) ^ 2 = τ ^ 2 / 4 from by ring, one_div_div]
  have e2 : 2 * (τ / 2) = τ := by ring
  rw [e0, e1, e2] at habs
  have hΨre : ((Complex.digamma ((stripPt σ τ) / 2) / 2 - (Real.log Real.pi : ℂ) / 2)).re
      = (Complex.digamma ((stripPt σ τ) / 2)).re / 2 - Real.log Real.pi / 2 := by
    rw [Complex.sub_re, re_div_two, re_div_two, Complex.ofReal_re]
  rw [hΨre]
  linarith [habs.2]

/-- The off-line floor is monotone in the height. -/
theorem stripFloor_mono_height {σ τ τ' : ℝ} (hσ1 : σ ≤ 1) (h0 : 0 < τ) (hττ' : τ ≤ τ') :
    stripFloor σ τ ≤ stripFloor σ τ' := by
  have h0' : 0 < τ' := lt_of_lt_of_le h0 hττ'
  have hlog : Real.log (τ / (2 * Real.pi)) ≤ Real.log (τ' / (2 * Real.pi)) :=
    Real.log_le_log (by positivity) (div_le_div₀ h0'.le hττ' (by positivity) le_rfl)
  have h4 : 4 / τ' ^ 2 ≤ 4 / τ ^ 2 :=
    div_le_div₀ (by norm_num) le_rfl (by positivity) (by nlinarith)
  have hπ : Real.pi / τ' ≤ Real.pi / τ :=
    div_le_div₀ Real.pi_pos.le le_rfl h0 hττ'
  have hσ' : (1 - σ) / τ' ^ 2 ≤ (1 - σ) / τ ^ 2 :=
    div_le_div₀ (by linarith) le_rfl (by positivity) (by nlinarith)
  unfold stripFloor
  linarith

/-- The off-line floor is monotone in the abscissa: the concession shrinks as the edge
approaches the `σ = 1` boundary. -/
theorem stripFloor_mono_sigma {σ σ' τ : ℝ} (hσσ' : σ ≤ σ') (hτ : 0 < τ) :
    stripFloor σ τ ≤ stripFloor σ' τ := by
  have h : (1 - σ') / τ ^ 2 ≤ (1 - σ) / τ ^ 2 :=
    (div_le_div_iff_of_pos_right (by positivity)).mpr (by linarith)
  unfold stripFloor
  linarith

/-- **The off-line floor is positive above an explicit absolute height**: for every
abscissa `σ ≥ 0` the floor is positive from height `12` on. -/
theorem stripFloor_pos {σ τ : ℝ} (hσ : 0 ≤ σ) (hτ : 12 ≤ τ) : 0 < stripFloor σ τ := by
  have h12 : (0 : ℝ) < 12 := by norm_num
  have hbase : 0 < stripFloor 0 12 := by
    have hπlt : Real.pi < 3.15 := Real.pi_lt_d2
    have hπgt : 3 < Real.pi := Real.pi_gt_three
    have hlog : (1 : ℝ) - Real.pi / 6 ≤ Real.log (12 / (2 * Real.pi)) := by
      have h6π : (12 : ℝ) / (2 * Real.pi) = (Real.pi / 6)⁻¹ := by
        rw [inv_div]
        ring
      rw [h6π, Real.log_inv]
      have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < Real.pi / 6 by positivity)
      linarith
    unfold stripFloor
    have e4 : (4 : ℝ) / 12 ^ 2 = 1 / 36 := by norm_num
    have e1 : (1 - 0 : ℝ) / 12 ^ 2 = 1 / 144 := by norm_num
    rw [e4, e1]
    nlinarith
  calc (0 : ℝ) < stripFloor 0 12 := hbase
    _ ≤ stripFloor 0 τ := stripFloor_mono_height (by norm_num) h12 hτ
    _ ≤ stripFloor σ τ := stripFloor_mono_sigma hσ (lt_of_lt_of_le h12 hτ)

/-! ### Continuity along the edge and the lateral winding phase -/

/-- The strip winding datum is continuous along the edge away from the real axis. -/
theorem continuousOn_stripWinding {σ : ℝ} (hσ : 0 < σ) :
    ContinuousOn (stripWinding σ) (Set.Ioi (0 : ℝ)) := by
  have hstrip : Continuous (stripPt σ) := by
    unfold stripPt
    exact continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
  have hmaps : Set.MapsTo (stripPt σ) (Set.Ioi (0 : ℝ)) {z : ℂ | 0 < z.re} := by
    intro τ _
    simp only [Set.mem_setOf_eq, stripPt_re]
    exact hσ
  have hD : ContinuousOn (fun τ : ℝ => archFactorDeriv (stripPt σ τ)) (Set.Ioi 0) :=
    continuousOn_archFactorDeriv.comp hstrip.continuousOn hmaps
  have hF : ContinuousOn (fun τ : ℝ => archFactor (stripPt σ τ)) (Set.Ioi 0) := fun τ _ =>
    (hasDerivAt_archFactor_strip hσ τ).continuousAt.continuousWithinAt
  exact hD.div hF fun τ hτ => archFactor_stripPt_ne_zero hσ (ne_of_gt hτ)

theorem continuousOn_stripWindingRate {σ : ℝ} (hσ : 0 < σ) :
    ContinuousOn (stripWindingRate σ) (Set.Ioi (0 : ℝ)) :=
  Complex.continuous_re.comp_continuousOn (continuousOn_stripWinding hσ)

/-- The lateral winding phase: the primitive of the lateral winding rate from a basepoint. -/
noncomputable def stripWindingPhase (σ γ u : ℝ) : ℝ := ∫ t in γ..u, stripWindingRate σ t

/-- At the central abscissa the lateral winding phase is the critical-line winding phase. -/
theorem stripWindingPhase_one_half : stripWindingPhase (1 / 2) = windingPhase := by
  funext γ u
  unfold stripWindingPhase windingPhase
  rw [stripWindingRate_one_half]

/-- **The lateral winding phase advances at least at the off-line floor of the left
endpoint.** -/
theorem stripWindingPhase_ge_of_floor {σ a b : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1)
    (ha : 0 < a) (hab : a ≤ b) :
    (b - a) * stripFloor σ a ≤ stripWindingPhase σ a b := by
  have hlow : ∀ u ∈ Set.Icc a b, stripFloor σ a ≤ stripWindingRate σ u := fun u hu =>
    le_trans (stripFloor_mono_height hσ1 ha hu.1)
      (stripWindingRate_ge hσ hσ1 (lt_of_lt_of_le ha hu.1))
  have hsub : Set.uIcc a b ⊆ Set.Ioi (0 : ℝ) := by
    rw [Set.uIcc_of_le hab]
    exact fun t ht => lt_of_lt_of_le ha ht.1
  calc (b - a) * stripFloor σ a = ∫ _ in a..b, stripFloor σ a := by
        rw [intervalIntegral.integral_const, smul_eq_mul]
    _ ≤ ∫ u in a..b, stripWindingRate σ u :=
        intervalIntegral.integral_mono_on hab intervalIntegrable_const
          (((continuousOn_stripWindingRate hσ).mono hsub).intervalIntegrable) hlow
    _ = stripWindingPhase σ a b := rfl

/-! ### Transport and polar presentation of a nonvanishing path -/

/-- **A path transports by the exponential of its logarithmic derivative's primitive.**
If `G′ = G·ω` along an interval, with `ω` continuous on an open set containing it, then
`G(τ) = G(a)·exp(∫ω)`: no zero appears and no phase slips, because `G·exp(−∫ω)` has zero
derivative. -/
theorem path_transport_exp_logDeriv {G ω : ℝ → ℂ} {U : Set ℝ} {a b : ℝ}
    (hU : IsOpen U) (hsub : Set.Icc a b ⊆ U)
    (hG : ∀ τ ∈ Set.Icc a b, HasDerivAt G (G τ * ω τ) τ)
    (hωc : ContinuousOn ω U) :
    ∀ τ ∈ Set.Icc a b,
      G τ = G a * Complex.exp (((∫ t in a..τ, (ω t).re : ℝ) : ℂ)
        + ((∫ t in a..τ, (ω t).im : ℝ) : ℂ) * Complex.I) := by
  intro τ hτ
  have hre_c : ContinuousOn (fun t => (ω t).re) U :=
    Complex.continuous_re.comp_continuousOn hωc
  have him_c : ContinuousOn (fun t => (ω t).im) U :=
    Complex.continuous_im.comp_continuousOn hωc
  have hsubu : ∀ u ∈ Set.Icc a b, Set.uIcc a u ⊆ U := by
    intro u hu
    rw [Set.uIcc_of_le hu.1]
    exact fun t ht => hsub ⟨ht.1, le_trans ht.2 hu.2⟩
  have hx' : ∀ u ∈ Set.Icc a b,
      HasDerivAt (fun u => ∫ t in a..u, (ω t).re) ((ω u).re) u := fun u hu =>
    intervalIntegral.integral_hasDerivAt_right
      ((hre_c.mono (hsubu u hu)).intervalIntegrable)
      (hre_c.stronglyMeasurableAtFilter hU u (hsub hu))
      (hre_c.continuousAt (hU.mem_nhds (hsub hu)))
  have hy' : ∀ u ∈ Set.Icc a b,
      HasDerivAt (fun u => ∫ t in a..u, (ω t).im) ((ω u).im) u := fun u hu =>
    intervalIntegral.integral_hasDerivAt_right
      ((him_c.mono (hsubu u hu)).intervalIntegrable)
      (him_c.stronglyMeasurableAtFilter hU u (hsub hu))
      (him_c.continuousAt (hU.mem_nhds (hsub hu)))
  set M : ℝ → ℂ := fun u => ((∫ t in a..u, (ω t).re : ℝ) : ℂ)
    + ((∫ t in a..u, (ω t).im : ℝ) : ℂ) * Complex.I with hMdef
  have hM' : ∀ u ∈ Set.Icc a b, HasDerivAt M (ω u) u := by
    intro u hu
    have h := ((hx' u hu).ofReal_comp).add (((hy' u hu).ofReal_comp).mul_const Complex.I)
    rwa [Complex.re_add_im] at h
  have hH : ∀ u ∈ Set.Icc a b,
      HasDerivAt (fun u => G u * Complex.exp (-(M u))) 0 u := by
    intro u hu
    have hexp : HasDerivAt (fun u => Complex.exp (-(M u)))
        (Complex.exp (-(M u)) * -(ω u)) u := ((hM' u hu).neg).cexp
    have h := (hG u hu).mul hexp
    convert h using 1
    ring
  have huIcc : Set.uIcc a τ ⊆ Set.Icc a b := by
    rw [Set.uIcc_of_le hτ.1]
    exact Set.Icc_subset_Icc le_rfl hτ.2
  have h0 : (∫ _ in a..τ, (0 : ℂ))
      = G τ * Complex.exp (-(M τ)) - G a * Complex.exp (-(M a)) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u hu => hH u (huIcc hu))
      intervalIntegrable_const
  rw [intervalIntegral.integral_zero] at h0
  have hMa : M a = 0 := by
    simp [hMdef, intervalIntegral.integral_same]
  have hGa : G τ * Complex.exp (-(M τ)) = G a := by
    have h := sub_eq_zero.mp h0.symm
    rwa [hMa, neg_zero, Complex.exp_zero, mul_one] at h
  calc G τ = G τ * Complex.exp (-(M τ)) * Complex.exp (M τ) := by
        rw [mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, mul_one]
    _ = G a * Complex.exp (M τ) := by rw [hGa]

/-- **The polar presentation of a path from its logarithmic derivative.**  A path with
`G′ = G·ω` is a real modulus times a unimodular phase: the modulus is driven by `Re ω`,
the phase by `Im ω`, from the polar data of the left endpoint. -/
theorem polar_presentation_of_logDeriv {G ω : ℝ → ℂ} {U : Set ℝ} {a b : ℝ}
    (hU : IsOpen U) (hsub : Set.Icc a b ⊆ U)
    (hG : ∀ τ ∈ Set.Icc a b, HasDerivAt G (G τ * ω τ) τ)
    (hωc : ContinuousOn ω U) :
    ∀ τ ∈ Set.Icc a b,
      G τ = ((‖G a‖ * Real.exp (∫ t in a..τ, (ω t).re) : ℝ) : ℂ)
        * Complex.exp ((((G a).arg + ∫ t in a..τ, (ω t).im : ℝ) : ℂ) * Complex.I) := by
  intro τ hτ
  have h := path_transport_exp_logDeriv hU hsub hG hωc τ hτ
  rw [h]
  conv_lhs => rw [← Complex.norm_mul_exp_arg_mul_I (G a)]
  rw [Complex.exp_add, Complex.ofReal_mul, Complex.ofReal_exp, Complex.ofReal_add, add_mul,
    Complex.exp_add]
  ring

/-- Continuity of the primitive of a function continuous on an open superset of the
interval. -/
theorem continuousOn_primitive_of_open {g : ℝ → ℝ} {U : Set ℝ} {a b : ℝ}
    (hU : IsOpen U) (hsub : Set.Icc a b ⊆ U) (hg : ContinuousOn g U) :
    ContinuousOn (fun u => ∫ t in a..u, g t) (Set.Icc a b) := by
  intro u hu
  have hsubu : Set.uIcc a u ⊆ U := by
    rw [Set.uIcc_of_le hu.1]
    exact fun t ht => hsub ⟨ht.1, le_trans ht.2 hu.2⟩
  have hd : HasDerivAt (fun u => ∫ t in a..u, g t) (g u) u :=
    intervalIntegral.integral_hasDerivAt_right
      ((hg.mono hsubu).intervalIntegrable)
      (hg.stronglyMeasurableAtFilter hU u (hsub hu))
      (hg.continuousAt (hU.mem_nhds (hsub hu)))
  exact hd.continuousAt.continuousWithinAt

/-- **Complete polar data from a logarithmic derivative and one nonvanishing point.**  A
path with `G′ = G·ω` that does not vanish at the left endpoint carries the full polar data
along the edge — a nonvanishing real modulus, the polar factorization, a continuous phase,
and the phase-advance identity `θ(τ) − θ(a) = ∫ Im ω` — exactly the hypothesis set the
lateral event theorems place on the anchor. -/
theorem polar_data_of_logDeriv {G ω : ℝ → ℂ} {U : Set ℝ} {a b : ℝ}
    (hU : IsOpen U) (hsub : Set.Icc a b ⊆ U)
    (hG : ∀ τ ∈ Set.Icc a b, HasDerivAt G (G τ * ω τ) τ)
    (hωc : ContinuousOn ω U) (ha0 : G a ≠ 0) :
    ∃ R θ : ℝ → ℝ,
      (∀ τ ∈ Set.Icc a b, R τ ≠ 0) ∧
      (∀ τ ∈ Set.Icc a b, G τ = (R τ : ℂ) * Complex.exp ((θ τ : ℝ) * Complex.I)) ∧
      ContinuousOn θ (Set.Icc a b) ∧
      (∀ τ ∈ Set.Icc a b, θ τ - θ a = ∫ t in a..τ, (ω t).im) := by
  refine ⟨fun τ => ‖G a‖ * Real.exp (∫ t in a..τ, (ω t).re),
    fun τ => (G a).arg + ∫ t in a..τ, (ω t).im, ?_, ?_, ?_, ?_⟩
  · intro τ _
    exact mul_ne_zero (norm_ne_zero_iff.mpr ha0) (Real.exp_ne_zero _)
  · exact polar_presentation_of_logDeriv hU hsub hG hωc
  · exact continuousOn_const.add (continuousOn_primitive_of_open hU hsub
      (Complex.continuous_im.comp_continuousOn hωc))
  · intro τ _
    simp [intervalIntegral.integral_same]

/-- **The phase budget from a pointwise band on the winding rate.**  A pointwise bound
`|Im ω| ≤ B` on the edge converts into the two-sided phase-advance budget `(b−a)·B` that
the lateral event theorems consume. -/
theorem phase_advance_bound_of_im_bound {ω : ℝ → ℂ} {a b B : ℝ} (hab : a ≤ b)
    (hB : ∀ τ ∈ Set.Icc a b, |(ω τ).im| ≤ B) :
    |∫ t in a..b, (ω t).im| ≤ (b - a) * B := by
  have h : ∀ x ∈ Set.uIoc a b, ‖(ω x).im‖ ≤ B := by
    intro x hx
    rw [Set.uIoc_of_le hab] at hx
    exact hB x ⟨hx.1.le, hx.2⟩
  have hle := intervalIntegral.norm_integral_le_of_norm_le_const h
  rwa [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hab), mul_comm] at hle

/-! ### The archimedean polar presentation on a lateral edge -/

theorem hasDerivAt_archFactor_strip_logDeriv {σ : ℝ} (hσ : 0 < σ) {τ : ℝ} (hτ : τ ≠ 0) :
    HasDerivAt (fun τ : ℝ => archFactor (stripPt σ τ))
      (archFactor (stripPt σ τ) * (stripWinding σ τ * Complex.I)) τ := by
  have h := hasDerivAt_archFactor_strip hσ τ
  rwa [archFactorDeriv_strip_eq_mul hσ hτ, mul_assoc] at h

/-- **The archimedean envelope on a lateral edge, in polar form.**  Along the vertical edge
at abscissa `σ` the envelope is a positive modulus (driven by `−Im` of the winding datum)
times a unimodular phase whose advance from the left endpoint is exactly the lateral winding
phase. -/
theorem archFactor_lateral_polar {σ a b : ℝ} (hσ : 0 < σ) (ha : 0 < a) :
    ∀ τ ∈ Set.Icc a b,
      archFactor (stripPt σ τ)
        = ((‖archFactor (stripPt σ a)‖
              * Real.exp (∫ t in a..τ, -(stripWinding σ t).im) : ℝ) : ℂ)
          * Complex.exp ((((archFactor (stripPt σ a)).arg
              + stripWindingPhase σ a τ : ℝ) : ℂ) * Complex.I) := by
  intro τ hτ
  have hsub : Set.Icc a b ⊆ Set.Ioi (0 : ℝ) := fun t ht => lt_of_lt_of_le ha ht.1
  have hωc : ContinuousOn (fun t => stripWinding σ t * Complex.I) (Set.Ioi 0) :=
    (continuousOn_stripWinding hσ).mul continuousOn_const
  have hG : ∀ t ∈ Set.Icc a b, HasDerivAt (fun t : ℝ => archFactor (stripPt σ t))
      (archFactor (stripPt σ t) * (stripWinding σ t * Complex.I)) t := fun t ht =>
    hasDerivAt_archFactor_strip_logDeriv hσ (ne_of_gt (hsub ht))
  have h := polar_presentation_of_logDeriv isOpen_Ioi hsub hG hωc τ hτ
  simpa only [Complex.mul_I_re, Complex.mul_I_im] using h

/-! ### The lateral-edge event theorem -/

/-- Product of polar forms. -/
theorem polar_mul (r₁ r₂ θ₁ θ₂ : ℝ) :
    ((r₁ : ℂ) * Complex.exp ((θ₁ : ℝ) * Complex.I))
        * ((r₂ : ℂ) * Complex.exp ((θ₂ : ℝ) * Complex.I))
      = ((r₁ * r₂ : ℝ) : ℂ) * Complex.exp (((θ₁ + θ₂ : ℝ) : ℂ) * Complex.I) := by
  push_cast
  rw [add_mul, Complex.exp_add]
  ring

/-- **The off-line archimedean winding floor forces a band-edge event on a lateral edge.**
If along the vertical edge at abscissa `0 < σ ≤ 1` the target factors through the
archimedean envelope and a Dirichlet part with phase budget `C_D`, the anchor has phase
budget `C₁`, and the edge is long enough that

  `π + C₁ + C_D ≤ (b − a) · stripFloor σ a`,

then a transversal band-edge event is forced: some real-ratio member of the pencil vanishes
on the edge.  The archimedean floor is explicit and unconditional; the two budgets are
finite Dirichlet phase data on the edge. -/
theorem exists_bandEvent_of_lateral_edge {Λ₁ Λ₂ : ℂ → ℂ} {D : ℝ → ℂ}
    {R₁ RD θ₁ θD : ℝ → ℝ} {σ a b C₁ CD : ℝ}
    (hσ : 0 < σ) (hσ1 : σ ≤ 1) (ha : 0 < a) (hab : a ≤ b)
    (hR1 : ∀ τ ∈ Set.Icc a b, R₁ τ ≠ 0)
    (hP1 : ∀ τ ∈ Set.Icc a b,
      Λ₁ (stripPt σ τ) = (R₁ τ : ℂ) * Complex.exp ((θ₁ τ : ℝ) * I))
    (hsplit : ∀ τ ∈ Set.Icc a b, Λ₂ (stripPt σ τ) = archFactor (stripPt σ τ) * D τ)
    (hPD : ∀ τ ∈ Set.Icc a b, D τ = (RD τ : ℂ) * Complex.exp ((θD τ : ℝ) * I))
    (hθ1c : ContinuousOn θ₁ (Set.Icc a b)) (hθDc : ContinuousOn θD (Set.Icc a b))
    (hceil1 : θ₁ b - θ₁ a ≤ C₁) (hceilD : -CD ≤ θD b - θD a)
    (hgap : Real.pi + C₁ + CD ≤ (b - a) * stripFloor σ a) :
    ∃ τ ∈ Set.Icc a b,
      pencil Λ₁ Λ₂ ((incidence Λ₁ Λ₂ (stripPt σ τ)).re : ℂ) 1 (stripPt σ τ) = 0 := by
  set R₂ : ℝ → ℝ := fun τ =>
    (‖archFactor (stripPt σ a)‖ * Real.exp (∫ t in a..τ, -(stripWinding σ t).im)) * RD τ
    with hR₂def
  set θ₂ : ℝ → ℝ := fun τ =>
    ((archFactor (stripPt σ a)).arg + stripWindingPhase σ a τ) + θD τ with hθ₂def
  have hsubO : Set.Icc a b ⊆ Set.Ioi (0 : ℝ) := fun t ht => lt_of_lt_of_le ha ht.1
  have hP2 : ∀ τ ∈ Set.Icc a b,
      Λ₂ (stripPt σ τ) = (R₂ τ : ℂ) * Complex.exp ((θ₂ τ : ℝ) * I) := by
    intro τ hτ
    rw [hsplit τ hτ, archFactor_lateral_polar hσ ha τ hτ, hPD τ hτ, polar_mul]
  have hθ2c : ContinuousOn θ₂ (Set.Icc a b) := by
    apply ContinuousOn.add _ hθDc
    apply continuousOn_const.add
    exact continuousOn_primitive_of_open isOpen_Ioi hsubO (continuousOn_stripWindingRate hσ)
  have hphase_a : stripWindingPhase σ a a = 0 := intervalIntegral.integral_same
  have hfloor : (b - a) * stripFloor σ a - CD ≤ θ₂ b - θ₂ a := by
    have h := stripWindingPhase_ge_of_floor hσ hσ1 ha hab
    simp only [hθ₂def, hphase_a]
    linarith
  have hgap' : Real.pi ≤ ((b - a) * stripFloor σ a - CD) - C₁ := by linarith
  exact exists_bandEvent_of_target_winding_floor hab hR1 hP1 hP2 hθ1c hθ2c
    hfloor hceil1 hgap'

/-- **The lateral-edge event theorem for the completed carrier.**  The target is the
completed carrier `completedGN N = archFactor · gN N` itself: on a lateral edge long enough
against the explicit off-line archimedean floor, net of the anchor's and the Dirichlet
part's phase budgets, a real-ratio member of the anchored pencil is forced to vanish. -/
theorem exists_bandEvent_of_lateral_edge_completedGN {Λ₁ : ℂ → ℂ} (N : ℕ)
    {R₁ RD θ₁ θD : ℝ → ℝ} {σ a b C₁ CD : ℝ}
    (hσ : 0 < σ) (hσ1 : σ ≤ 1) (ha : 0 < a) (hab : a ≤ b)
    (hR1 : ∀ τ ∈ Set.Icc a b, R₁ τ ≠ 0)
    (hP1 : ∀ τ ∈ Set.Icc a b,
      Λ₁ (stripPt σ τ) = (R₁ τ : ℂ) * Complex.exp ((θ₁ τ : ℝ) * I))
    (hPD : ∀ τ ∈ Set.Icc a b,
      gN N (stripPt σ τ) = (RD τ : ℂ) * Complex.exp ((θD τ : ℝ) * I))
    (hθ1c : ContinuousOn θ₁ (Set.Icc a b)) (hθDc : ContinuousOn θD (Set.Icc a b))
    (hceil1 : θ₁ b - θ₁ a ≤ C₁) (hceilD : -CD ≤ θD b - θD a)
    (hgap : Real.pi + C₁ + CD ≤ (b - a) * stripFloor σ a) :
    ∃ τ ∈ Set.Icc a b,
      pencil Λ₁ (completedGN N)
        ((incidence Λ₁ (completedGN N) (stripPt σ τ)).re : ℂ) 1 (stripPt σ τ) = 0 :=
  exists_bandEvent_of_lateral_edge hσ hσ1 ha hab hR1 hP1 (fun _ _ => rfl) hPD
    hθ1c hθDc hceil1 hceilD hgap

/-- **The concrete lateral edge.**  At height `a ≥ 12` the off-line floor is positive, so
any lateral edge of length at least `(π + C₁ + C_D)/stripFloor σ a` — with nonnegative
anchor and Dirichlet phase budgets `C₁`, `C_D` — forces a band-edge event of the anchored
completed carrier.  Every archimedean quantity is explicit: the height threshold, the floor,
and the length threshold. -/
theorem exists_bandEvent_of_long_lateral_edge {Λ₁ : ℂ → ℂ} (N : ℕ)
    {R₁ RD θ₁ θD : ℝ → ℝ} {σ a b C₁ CD : ℝ}
    (hσ : 0 < σ) (hσ1 : σ ≤ 1) (ha : 12 ≤ a) (hC1 : 0 ≤ C₁) (hCD : 0 ≤ CD)
    (hlen : (Real.pi + C₁ + CD) / stripFloor σ a ≤ b - a)
    (hR1 : ∀ τ ∈ Set.Icc a b, R₁ τ ≠ 0)
    (hP1 : ∀ τ ∈ Set.Icc a b,
      Λ₁ (stripPt σ τ) = (R₁ τ : ℂ) * Complex.exp ((θ₁ τ : ℝ) * I))
    (hPD : ∀ τ ∈ Set.Icc a b,
      gN N (stripPt σ τ) = (RD τ : ℂ) * Complex.exp ((θD τ : ℝ) * I))
    (hθ1c : ContinuousOn θ₁ (Set.Icc a b)) (hθDc : ContinuousOn θD (Set.Icc a b))
    (hceil1 : θ₁ b - θ₁ a ≤ C₁) (hceilD : -CD ≤ θD b - θD a) :
    ∃ τ ∈ Set.Icc a b,
      pencil Λ₁ (completedGN N)
        ((incidence Λ₁ (completedGN N) (stripPt σ τ)).re : ℂ) 1 (stripPt σ τ) = 0 := by
  have hfl : 0 < stripFloor σ a := stripFloor_pos hσ.le ha
  have hnum : (0 : ℝ) < Real.pi + C₁ + CD := by positivity
  have hgap : Real.pi + C₁ + CD ≤ (b - a) * stripFloor σ a := by
    rw [div_le_iff₀ hfl] at hlen
    linarith
  have hab : a ≤ b := by
    have h : (0 : ℝ) < (Real.pi + C₁ + CD) / stripFloor σ a := by positivity
    linarith
  exact exists_bandEvent_of_lateral_edge_completedGN N hσ hσ1
    (lt_of_lt_of_le (by norm_num) ha) hab hR1 hP1 hPD hθ1c hθDc hceil1 hceilD hgap

end RHTower
