import GaloisForLFunctions.RHTower.SquarefreeConvolutionHalfMovingAnchorEscapeSharpness

/-!
# Growing-multiplicity escaping-quartet sharpness

The actual functional-equation quartet gauges can carry zero order tending to infinity while
remaining compact-open invisible.  At height `n + 1`, raise the normalized quartet gauge to power
`n + 1`.  Its error scale is `(n + 1)/(n + 1)²`, so the gauges still converge locally uniformly
to one.  Multiplying Xi preserves its functional equation, Schwarz symmetry, and
hypertranscendence, but creates zero jets through order `n` at an off-critical point escaping
vertically.

This is the Xi-passport sharpness companion to the moving-anchor interior-cluster no-go.  It does
not preserve literal Euler coefficients and does not construct an arithmetic half-divisor.
-/

open Complex Filter Metric Set Topology

namespace RHTower

open GaloisForLFunctions
open GaloisForLFunctions.HTGeometry

noncomputable section

/-- Normalized escaping quartet with multiplicity increasing at the same rate as its height. -/
def growingMultiplicityEscapingQuartetGauge (a : ℝ) (n : ℕ) (s : ℂ) : ℂ :=
  multiplicityEscapingQuartetGauge a (n + 1) n s

/-- Xi multiplied by the growing-multiplicity escaping quartet. -/
def growingMultiplicityEscapingQuartetGaugedXi (a : ℝ) (n : ℕ) (s : ℂ) : ℂ :=
  growingMultiplicityEscapingQuartetGauge a n s * xi s

private theorem growingMultiplicityEscapingQuartet_ratio_tendsto_zero :
    Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ) / (((n + 1 : ℕ) : ℝ) ^ (2 : ℕ)))
      atTop (nhds 0) := by
  convert (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)) using 1
  funext n
  push_cast
  field_simp

private theorem escapingQuartetScale_sq_mul_eq_div
    (n : ℕ) (z : ℂ) :
    (escapingQuartetScale n : ℂ) ^ (2 : ℕ) * z =
      z / (((((n + 1 : ℕ) : ℝ) : ℂ)) ^ (2 : ℕ)) := by
  unfold escapingQuartetScale escapingQuartetHeight
  push_cast
  field_simp

/-- Unbounded quartet multiplicity remains compact-open invisible. -/
theorem growingMultiplicityEscapingQuartetGauge_tendstoLocallyUniformly_one
    (a : ℝ) :
    TendstoLocallyUniformly (growingMultiplicityEscapingQuartetGauge a)
      (fun _ : ℂ => 1) atTop := by
  have hbase := tendstoLocallyUniformly_one_add_div_pow
    (a := fun n : ℕ => ((n + 1 : ℕ) : ℝ))
    (d := fun n : ℕ => n + 1)
    (fun n => by positivity)
    growingMultiplicityEscapingQuartet_ratio_tendsto_zero
  have hminus := hbase.comp
    (fun s : ℂ => ((s - (1 / 2 : ℂ)) - (a : ℂ)) ^ (2 : ℕ)) (by fun_prop)
  have hplus := hbase.comp
    (fun s : ℂ => ((s - (1 / 2 : ℂ)) + (a : ℂ)) ^ (2 : ℕ)) (by fun_prop)
  have hprod := hminus.mul₀ hplus continuous_const continuous_const
  convert hprod using 1
  · funext n s
    simp only [growingMultiplicityEscapingQuartetGauge,
      multiplicityEscapingQuartetGauge, normalizedEscapingQuartetGauge]
    rw [mul_pow]
    rw [escapingQuartetScale_sq_mul_eq_div,
      escapingQuartetScale_sq_mul_eq_div]
    rfl
  · funext s
    simp

/-- The Xi carriers with growing escaping multiplicity still converge compact-open to Xi. -/
theorem growingMultiplicityEscapingQuartetGaugedXi_tendstoLocallyUniformly
    (a : ℝ) :
    TendstoLocallyUniformly (growingMultiplicityEscapingQuartetGaugedXi a)
      xi atTop := by
  have hxi : TendstoLocallyUniformly (fun _n : ℕ => xi) xi atTop :=
    tendstoLocallyUniformly_const_sequence xi
  have hxiContinuous : Continuous xi :=
    continuous_iff_continuousAt.mpr fun s =>
      (xi_analyticOnNhd_univ s (Set.mem_univ s)).continuousAt
  have hprod :=
    (growingMultiplicityEscapingQuartetGauge_tendstoLocallyUniformly_one a).mul₀
      hxi continuous_const hxiContinuous
  change TendstoLocallyUniformly
      (fun n s => growingMultiplicityEscapingQuartetGauge a n s * xi s)
      (fun s => 1 * xi s) atTop at hprod
  simpa only [growingMultiplicityEscapingQuartetGaugedXi, one_mul] using! hprod

/-- Every carrier retains the completed functional equation. -/
theorem growingMultiplicityEscapingQuartetGaugedXi_one_sub
    (a : ℝ) (n : ℕ) (s : ℂ) :
    growingMultiplicityEscapingQuartetGaugedXi a n (1 - s) =
      growingMultiplicityEscapingQuartetGaugedXi a n s := by
  unfold growingMultiplicityEscapingQuartetGaugedXi
    growingMultiplicityEscapingQuartetGauge
  exact multiplicityEscapingQuartetGaugedXi_one_sub a (n + 1) n s

/-- Every carrier retains Schwarz symmetry. -/
theorem growingMultiplicityEscapingQuartetGaugedXi_conj
    (a : ℝ) (n : ℕ) (s : ℂ) :
    growingMultiplicityEscapingQuartetGaugedXi a n ((starRingEnd ℂ) s) =
      (starRingEnd ℂ) (growingMultiplicityEscapingQuartetGaugedXi a n s) := by
  unfold growingMultiplicityEscapingQuartetGaugedXi
    growingMultiplicityEscapingQuartetGauge
  exact multiplicityEscapingQuartetGaugedXi_conj a (n + 1) n s

/-- Every carrier remains hypertranscendental. -/
theorem growingMultiplicityEscapingQuartetGaugedXi_hypertranscendental
    (a : ℝ) (n : ℕ) :
    Hypertranscendental (growingMultiplicityEscapingQuartetGaugedXi a n) := by
  unfold growingMultiplicityEscapingQuartetGaugedXi
    growingMultiplicityEscapingQuartetGauge
  exact multiplicityEscapingQuartetGaugedXi_hypertranscendental a (n + 1) n

/-- The carrier's jets through order `n` vanish at its escaping quartet point. -/
theorem growingMultiplicityEscapingQuartetGaugedXi_jet_zero
    (a : ℝ) (n j : ℕ) (hj : j ≤ n) :
    iteratedDeriv j (growingMultiplicityEscapingQuartetGaugedXi a n)
      (quartetPoint a (escapingQuartetHeight n)) = 0 := by
  change iteratedDeriv j
    (fun s => normalizedEscapingQuartetGauge a n s ^ (n + 1) * xi s)
      (quartetPoint a (escapingQuartetHeight n)) = 0
  let c := quartetPoint a (escapingQuartetHeight n)
  let W := normalizedEscapingQuartetGauge a n
  have hWdiff : Differentiable ℂ W := by
    unfold W normalizedEscapingQuartetGauge
    fun_prop
  have hWzero : W c = 0 := by
    unfold W c
    rw [normalizedEscapingQuartetGauge_eq,
      centeredQuartetGauge_quartetPoint, mul_zero]
  have hpow : ∀ r : ℕ, r < n + 1 →
      iteratedDeriv r (fun s => W s ^ (n + 1)) c = 0 := by
    exact iteratedDeriv_pow_eq_zero_before_order hWdiff hWzero (n + 1)
  have hxidiff : Differentiable ℂ xi := by
    exact Complex.analyticOnNhd_univ_iff_differentiable.mp xi_analyticOnNhd_univ
  have hzero : iteratedDeriv j (fun s => W s ^ (n + 1) * xi s) c = 0 := by
    refine complex_iteratedDeriv_mul_eq_zero_before_add_order
      ((hWdiff.pow (n + 1)).contDiff.contDiffAt) hxidiff.contDiff.contDiffAt
      (m := n + 1) (n := 0) hpow (fun r hr => by omega) (by omega)
  simpa [W, c] using hzero

/-- Positive horizontal displacement puts every escaping zero in `rightHalf`. -/
theorem growingMultiplicityEscapingQuartetAnchor_mem_rightHalf
    {a : ℝ} (ha : 0 < a) (n : ℕ) :
    quartetPoint a (escapingQuartetHeight n) ∈ rightHalf := by
  rw [mem_rightHalf]
  simp [quartetPoint]
  linarith

/-- Imaginary parts of the marked zeros tend to infinity. -/
theorem growingMultiplicityEscapingQuartetAnchor_im_tendsto_atTop
    (a : ℝ) :
    Tendsto (fun n => (quartetPoint a (escapingQuartetHeight n)).im)
      atTop atTop := by
  convert (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds :
    Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop) using 1
  funext n
  simp [quartetPoint, escapingQuartetHeight]

/-- The marked zeros eventually avoid every compact subset of the plane. -/
theorem growingMultiplicityEscapingQuartetAnchor_eventually_avoid_compact
    (a : ℝ) {K : Set ℂ} (hK : IsCompact K) :
    ∀ᶠ n in atTop, quartetPoint a (escapingQuartetHeight n) ∉ K := by
  obtain ⟨R, hKR⟩ := hK.isBounded.subset_closedBall (0 : ℂ)
  filter_upwards
    [(growingMultiplicityEscapingQuartetAnchor_im_tendsto_atTop a).eventually_gt_atTop R]
      with n hn
  intro hmem
  have hnorm := Metric.mem_closedBall.mp (hKR hmem)
  rw [dist_zero_right] at hnorm
  exact (not_lt_of_ge (Complex.im_le_norm
    (quartetPoint a (escapingQuartetHeight n)))) (lt_of_le_of_lt hnorm hn)

end

end RHTower
