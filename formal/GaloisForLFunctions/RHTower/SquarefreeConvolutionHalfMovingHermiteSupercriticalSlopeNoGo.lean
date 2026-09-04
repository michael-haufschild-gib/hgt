import GaloisForLFunctions.RHTower.SquarefreeConvolutionHalfMovingHermiteArithmeticHighDepthNoGo

/-!
# Every point-Hermite slope above `5/11` fails

The arithmetic mode-tail obstruction admits a sharp variable Euler point.  Given a depth slope
`alpha > 5/11`, choose a real Euler point whose gap `d` from the Hermite anchor `6/11` lies
strictly between `5/11` and `alpha`.  A sufficiently small positive exponential tilt then makes
the Poisson remainder decay at rate

`t * (alpha - d / (1 - t)) > 0`.

Thus the corrected source tends to zero at that Euler point, contradicting source fidelity and the
nonvanishing squarefree-half Euler product.  Together with the subcritical local-boundedness
obstruction, this isolates the exact slope `5/11` as the only monotone linear point-Hermite
boundary not excluded by these two mechanisms.
-/

open Complex Filter Metric Set Topology

namespace RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

/-- Real action of the `n`-th dressed Dirichlet mode at a variable real witness. -/
def boundaryDressedModeActionAt (sigma : ℝ) (N n : ℕ) : ℝ :=
  ((N : ℝ) - Real.log n) * (sigma - 6 / 11)

theorem boundaryDressedModeFrequency_mul_realGap (sigma : ℝ) (N n : ℕ) :
    boundaryDressedModeFrequency N n *
        ((sigma : ℂ) - boundaryExteriorPoint) =
      (boundaryDressedModeActionAt sigma N n : ℂ) := by
  rw [show (sigma : ℂ) - boundaryExteriorPoint =
      ((sigma - 6 / 11 : ℝ) : ℂ) by
    apply Complex.ext <;> simp [boundaryExteriorPoint]]
  simp only [boundaryDressedModeFrequency, boundaryDressedModeActionAt]
  push_cast
  ring

theorem boundarySeparator_mul_dressedMode_at_real_eq
    (sigma : ℝ) (N : ℕ) {n : ℕ} (hn : n ≠ 0) :
    boundaryExponentialSeparator N (sigma : ℂ) *
        (boundaryDressedModeCoefficient N n *
          Complex.exp
            (boundaryDressedModeFrequency N n * boundaryExteriorPoint)) =
      LSeries.term squarefreeConvolutionHalf (sigma : ℂ) n *
        Complex.exp (-(boundaryDressedModeActionAt sigma N n : ℂ)) := by
  rw [LSeries.term_of_ne_zero hn, div_eq_mul_inv, ← Complex.cpow_neg]
  have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hpow : ((n : ℂ) ^ (-((sigma : ℂ)))) =
      Complex.exp (-((Real.log n : ℝ) : ℂ) * (sigma : ℂ)) := by
    have hne : (n : ℂ) ≠ 0 := by exact_mod_cast hn
    rw [Complex.cpow_def_of_ne_zero hne]
    congr 1
    rw [← Complex.natCast_log]
    ring
  rw [hpow, boundaryExponentialSeparator, boundaryDressedModeCoefficient,
    boundaryDressedModeFrequency]
  calc
    Complex.exp ((N : ℂ) * (boundaryExteriorPoint - (sigma : ℂ))) *
        (squarefreeConvolutionHalf n *
          Complex.exp (-(N : ℂ) * boundaryExteriorPoint) *
          Complex.exp (((N : ℂ) - (Real.log n : ℂ)) *
            boundaryExteriorPoint)) =
      squarefreeConvolutionHalf n *
        Complex.exp
          ((N : ℂ) * (boundaryExteriorPoint - (sigma : ℂ)) +
            (-(N : ℂ) * boundaryExteriorPoint +
              ((N : ℂ) - (Real.log n : ℂ)) * boundaryExteriorPoint)) := by
        rw [Complex.exp_add, Complex.exp_add]
        ring
    _ = squarefreeConvolutionHalf n *
        Complex.exp
          (-((Real.log n : ℝ) : ℂ) * (sigma : ℂ) +
            -(boundaryDressedModeActionAt sigma N n : ℂ)) := by
      congr 2
      rw [boundaryDressedModeActionAt]
      push_cast
      norm_num [boundaryExteriorPoint]
      ring
    _ = squarefreeConvolutionHalf n *
        Complex.exp (-((Real.log n : ℝ) : ℂ) * (sigma : ℂ)) *
        Complex.exp (-(boundaryDressedModeActionAt sigma N n : ℂ)) := by
      rw [Complex.exp_add]
      ring

/-- Exact Poisson-tail decomposition at any real witness. -/
theorem boundaryHermiteJet_correctedSource_real_eq_modeSum
    (sigma : ℝ) (N K : ℕ) :
    squarefreeHalfDirichletPartialSum N (sigma : ℂ) +
        boundaryHermiteJetCounterterm N K (sigma : ℂ) =
      ∑ n ∈ Finset.range N,
        LSeries.term squarefreeConvolutionHalf (sigma : ℂ) n *
          ((1 : ℂ) -
            Complex.exp (-(boundaryDressedModeActionAt sigma N n : ℂ)) *
              (∑ j ∈ Finset.range (K + 1),
                (boundaryDressedModeActionAt sigma N n : ℂ) ^ j /
                  (j.factorial : ℂ))) := by
  rw [boundaryHermiteJetCounterterm,
    boundaryHermiteJetPolynomial_eq_modeTaylorSum,
    squarefreeHalfDirichletPartialSum, Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n hnrange
  by_cases hn0 : n = 0
  · subst n
    simp [LSeries.term_zero, boundaryDressedModeCoefficient]
  · rw [boundaryDressedModeFrequency_mul_realGap]
    rw [show -boundaryExponentialSeparator N (sigma : ℂ) *
          (boundaryDressedModeCoefficient N n *
            Complex.exp
              (boundaryDressedModeFrequency N n * boundaryExteriorPoint) *
            (∑ j ∈ Finset.range (K + 1),
              (boundaryDressedModeActionAt sigma N n : ℂ) ^ j /
                (j.factorial : ℂ))) =
        -(boundaryExponentialSeparator N (sigma : ℂ) *
          (boundaryDressedModeCoefficient N n *
            Complex.exp
              (boundaryDressedModeFrequency N n * boundaryExteriorPoint))) *
          (∑ j ∈ Finset.range (K + 1),
            (boundaryDressedModeActionAt sigma N n : ℂ) ^ j /
              (j.factorial : ℂ)) by ring,
      boundarySeparator_mul_dressedMode_at_real_eq sigma N hn0]
    ring

theorem boundaryDressedModeActionAt_nonneg
    {sigma : ℝ} (hgap : 0 ≤ sigma - 6 / 11)
    {N n : ℕ} (hn : n ∈ Finset.range N) :
    0 ≤ boundaryDressedModeActionAt sigma N n := by
  have hlog : Real.log n ≤ (n : ℝ) :=
    Real.log_le_self (Nat.cast_nonneg n)
  have hnN : (n : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast Nat.le_of_lt (Finset.mem_range.mp hn)
  unfold boundaryDressedModeActionAt
  exact mul_nonneg (by linarith) hgap

theorem boundaryDressedModeActionAt_le
    {sigma : ℝ} (hgap : 0 ≤ sigma - 6 / 11)
    (N n : ℕ) :
    boundaryDressedModeActionAt sigma N n ≤
      (sigma - 6 / 11) * (N : ℝ) := by
  have hlog : 0 ≤ Real.log n := Real.log_natCast_nonneg n
  unfold boundaryDressedModeActionAt
  nlinarith

theorem norm_squarefreeHalf_term_real_le_one
    (sigma : ℝ) (hsigma : 0 ≤ sigma) (n : ℕ) :
    ‖LSeries.term squarefreeConvolutionHalf (sigma : ℂ) n‖ ≤ 1 := by
  by_cases hn0 : n = 0
  · subst n
    simp [LSeries.term_zero]
  · rw [LSeries.norm_term_eq, if_neg hn0]
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn0
    have hre : 0 ≤ ((sigma : ℂ)).re := by simpa
    have hden : 1 ≤ (n : ℝ) ^ ((sigma : ℂ)).re :=
      Real.one_le_rpow hn1 hre
    exact (div_le_one (lt_of_lt_of_le zero_lt_one hden)).2
      ((norm_squarefreeConvolutionHalf_le_one n).trans hden)

/-- Uniform Chernoff bound for a corrected source at a variable real Euler witness. -/
theorem norm_boundaryHermiteJet_correctedSource_real_le_chernoff
    (sigma : ℝ) (N K : ℕ) {t q : ℝ}
    (hgap : 0 ≤ sigma - 6 / 11) (hsigma : 0 ≤ sigma)
    (ht : 0 ≤ t) (_hq : 0 ≤ q)
    (hexpSub : Real.exp t - 1 ≤ q) :
    ‖squarefreeHalfDirichletPartialSum N (sigma : ℂ) +
        boundaryHermiteJetCounterterm N K (sigma : ℂ)‖ ≤
      (N : ℝ) * Real.exp
        (-(t * ((K + 1 : ℕ) : ℝ)) +
          (((sigma - 6 / 11) * (N : ℝ)) * q)) := by
  rw [boundaryHermiteJet_correctedSource_real_eq_modeSum]
  calc
    ‖∑ n ∈ Finset.range N,
        LSeries.term squarefreeConvolutionHalf (sigma : ℂ) n *
          ((1 : ℂ) -
            Complex.exp (-(boundaryDressedModeActionAt sigma N n : ℂ)) *
              (∑ j ∈ Finset.range (K + 1),
                (boundaryDressedModeActionAt sigma N n : ℂ) ^ j /
                  (j.factorial : ℂ)))‖ ≤
      ∑ n ∈ Finset.range N,
        ‖LSeries.term squarefreeConvolutionHalf (sigma : ℂ) n *
          ((1 : ℂ) -
            Complex.exp (-(boundaryDressedModeActionAt sigma N n : ℂ)) *
              (∑ j ∈ Finset.range (K + 1),
                (boundaryDressedModeActionAt sigma N n : ℂ) ^ j /
                  (j.factorial : ℂ)))‖ := norm_sum_le _ _
    _ ≤ ∑ _n ∈ Finset.range N,
        Real.exp
          (-(t * ((K + 1 : ℕ) : ℝ)) +
            (((sigma - 6 / 11) * (N : ℝ)) * q)) := by
      apply Finset.sum_le_sum
      intro n hn
      have hx0 := boundaryDressedModeActionAt_nonneg hgap hn
      have hxN := boundaryDressedModeActionAt_le hgap N n
      have htail := realPoissonUpperTail_le_chernoff (K + 1) hx0 ht
      have hexpSub0 : 0 ≤ Real.exp t - 1 := by
        have := Real.one_le_exp ht
        linarith
      have haction : boundaryDressedModeActionAt sigma N n *
          (Real.exp t - 1) ≤
        ((sigma - 6 / 11) * (N : ℝ)) * q := by
        calc
          boundaryDressedModeActionAt sigma N n *
              (Real.exp t - 1) ≤
            ((sigma - 6 / 11) * (N : ℝ)) *
              (Real.exp t - 1) :=
            mul_le_mul_of_nonneg_right hxN hexpSub0
          _ ≤ ((sigma - 6 / 11) * (N : ℝ)) * q :=
            mul_le_mul_of_nonneg_left hexpSub
              (mul_nonneg hgap (Nat.cast_nonneg N))
      rw [norm_mul, complex_poissonUpperTail_eq_ofReal,
        Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (realPoissonUpperTail_nonneg (K + 1) hx0)]
      calc
        ‖LSeries.term squarefreeConvolutionHalf (sigma : ℂ) n‖ *
            realPoissonUpperTail (K + 1)
              (boundaryDressedModeActionAt sigma N n) ≤
          1 * realPoissonUpperTail (K + 1)
              (boundaryDressedModeActionAt sigma N n) := by
            exact mul_le_mul_of_nonneg_right
              (norm_squarefreeHalf_term_real_le_one sigma hsigma n)
              (realPoissonUpperTail_nonneg (K + 1) hx0)
        _ ≤ Real.exp
            (-(t * ((K + 1 : ℕ) : ℝ)) +
              boundaryDressedModeActionAt sigma N n *
                (Real.exp t - 1)) := by
          simpa only [one_mul] using htail
        _ ≤ Real.exp
            (-(t * ((K + 1 : ℕ) : ℝ)) +
              (((sigma - 6 / 11) * (N : ℝ)) * q)) := by
          apply Real.exp_le_exp.mpr
          linarith
    _ = (N : ℝ) * Real.exp
        (-(t * ((K + 1 : ℕ) : ℝ)) +
          (((sigma - 6 / 11) * (N : ℝ)) * q)) := by simp

theorem exp_sub_one_le_div_one_sub_of_nonneg_lt_one
    {t : ℝ} (ht : 0 ≤ t) (ht1 : t < 1) :
    Real.exp t - 1 ≤ t / (1 - t) := by
  have hsmall := Real.exp_bound_div_one_sub_of_interval ht ht1
  calc
    Real.exp t - 1 ≤ 1 / (1 - t) - 1 := sub_le_sub_right hsmall 1
    _ = t / (1 - t) := by
      field_simp [ne_of_gt (sub_pos.mpr ht1)]
      ring

/-- Gap between the Hermite anchor and the adaptive Euler witness. -/
def supercriticalHermiteEulerGap (alpha : ℝ) : ℝ :=
  (alpha + 5 / 11) / 2

/-- Adaptive Euler witness for a prescribed supercritical depth slope. -/
def supercriticalHermiteEulerAbscissa (alpha : ℝ) : ℝ :=
  6 / 11 + supercriticalHermiteEulerGap alpha

/-- Exponential tilt chosen halfway inside the admissible Chernoff interval. -/
def supercriticalHermiteChernoffTilt (alpha : ℝ) : ℝ :=
  (alpha - supercriticalHermiteEulerGap alpha) / (2 * alpha)

/-- Strict exponential decay rate left by the adaptive witness and tilt. -/
def supercriticalHermiteChernoffRate (alpha : ℝ) : ℝ :=
  supercriticalHermiteChernoffTilt alpha *
    (alpha - supercriticalHermiteEulerGap alpha /
      (1 - supercriticalHermiteChernoffTilt alpha))

theorem supercriticalHermiteEulerGap_gt_five_div_eleven
    {alpha : ℝ} (halpha : 5 / 11 < alpha) :
    5 / 11 < supercriticalHermiteEulerGap alpha := by
  unfold supercriticalHermiteEulerGap
  linarith

theorem supercriticalHermiteEulerGap_lt
    {alpha : ℝ} (halpha : 5 / 11 < alpha) :
    supercriticalHermiteEulerGap alpha < alpha := by
  unfold supercriticalHermiteEulerGap
  linarith

theorem one_lt_supercriticalHermiteEulerAbscissa
    {alpha : ℝ} (halpha : 5 / 11 < alpha) :
    1 < supercriticalHermiteEulerAbscissa alpha := by
  unfold supercriticalHermiteEulerAbscissa
  linarith [supercriticalHermiteEulerGap_gt_five_div_eleven halpha]

theorem supercriticalHermiteEulerAbscissa_mem_farHalf
    {alpha : ℝ} (halpha : 5 / 11 < alpha) :
    (supercriticalHermiteEulerAbscissa alpha : ℂ) ∈ farHalf := by
  rw [mem_farHalf]
  simpa using one_lt_supercriticalHermiteEulerAbscissa halpha

theorem supercriticalHermiteChernoffTilt_pos
    {alpha : ℝ} (halpha : 5 / 11 < alpha) :
    0 < supercriticalHermiteChernoffTilt alpha := by
  have halpha0 : 0 < alpha := by linarith
  unfold supercriticalHermiteChernoffTilt
  exact div_pos
    (sub_pos.mpr (supercriticalHermiteEulerGap_lt halpha)) (by positivity)

theorem supercriticalHermiteChernoffTilt_lt_one
    {alpha : ℝ} (halpha : 5 / 11 < alpha) :
    supercriticalHermiteChernoffTilt alpha < 1 := by
  have halpha0 : 0 < alpha := by linarith
  unfold supercriticalHermiteChernoffTilt
  rw [div_lt_one (by positivity : 0 < 2 * alpha)]
  have hgap0 : 0 < supercriticalHermiteEulerGap alpha :=
    (by linarith [supercriticalHermiteEulerGap_gt_five_div_eleven halpha])
  linarith

theorem supercriticalHermiteEulerGap_div_one_sub_tilt_lt
    {alpha : ℝ} (halpha : 5 / 11 < alpha) :
    supercriticalHermiteEulerGap alpha /
        (1 - supercriticalHermiteChernoffTilt alpha) < alpha := by
  have halpha0 : 0 < alpha := by linarith
  have ht1 := supercriticalHermiteChernoffTilt_lt_one halpha
  rw [div_lt_iff₀ (sub_pos.mpr ht1)]
  have hformula : alpha * (1 - supercriticalHermiteChernoffTilt alpha) =
      (alpha + supercriticalHermiteEulerGap alpha) / 2 := by
    unfold supercriticalHermiteChernoffTilt
    field_simp [ne_of_gt halpha0]
    ring
  rw [hformula]
  linarith [supercriticalHermiteEulerGap_lt halpha]

theorem supercriticalHermiteChernoffRate_pos
    {alpha : ℝ} (halpha : 5 / 11 < alpha) :
    0 < supercriticalHermiteChernoffRate alpha := by
  unfold supercriticalHermiteChernoffRate
  exact mul_pos (supercriticalHermiteChernoffTilt_pos halpha)
    (sub_pos.mpr
      (supercriticalHermiteEulerGap_div_one_sub_tilt_lt halpha))

/-- Every eventual depth slope strictly above `5/11` makes the corrected source vanish at an
adaptive Euler witness. -/
theorem tendsto_boundaryHermiteJet_correctedSource_supercriticalEuler_of_eventually_slope_le_depth
    {depth : ℕ → ℕ} {alpha : ℝ} (halpha : 5 / 11 < alpha)
    (hdepth : ∀ᶠ N : ℕ in atTop,
      alpha * (N : ℝ) ≤ (depth N : ℝ)) :
    Tendsto
      (fun N =>
        squarefreeHalfDirichletPartialSum N
            (supercriticalHermiteEulerAbscissa alpha : ℂ) +
          boundaryHermiteJetCounterterm N (depth N)
            (supercriticalHermiteEulerAbscissa alpha : ℂ))
      atTop (nhds 0) := by
  let d := supercriticalHermiteEulerGap alpha
  let sigma := supercriticalHermiteEulerAbscissa alpha
  let t := supercriticalHermiteChernoffTilt alpha
  let q := t / (1 - t)
  let gamma := supercriticalHermiteChernoffRate alpha
  have hd0 : 0 ≤ d := by
    dsimp [d]
    linarith [supercriticalHermiteEulerGap_gt_five_div_eleven halpha]
  have hsigmaGap : sigma - 6 / 11 = d := by
    simp [sigma, supercriticalHermiteEulerAbscissa, d]
  have hsigma0 : 0 ≤ sigma := by
    linarith [one_lt_supercriticalHermiteEulerAbscissa halpha]
  have ht0 : 0 ≤ t := (supercriticalHermiteChernoffTilt_pos halpha).le
  have ht1 : t < 1 := supercriticalHermiteChernoffTilt_lt_one halpha
  have hq0 : 0 ≤ q := div_nonneg ht0 (sub_pos.mpr ht1).le
  have hexpSub : Real.exp t - 1 ≤ q :=
    exp_sub_one_le_div_one_sub_of_nonneg_lt_one ht0 ht1
  have hgamma : 0 < gamma := supercriticalHermiteChernoffRate_pos halpha
  have hmajor : Tendsto
      (fun N : ℕ => (N : ℝ) * Real.exp (-gamma * (N : ℝ)))
      atTop (nhds 0) := by
    have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 gamma hgamma).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
    simpa [Function.comp_def, Real.rpow_one, mul_assoc, mul_left_comm, mul_comm] using h
  refine squeeze_zero_norm' ?_ hmajor
  filter_upwards [hdepth] with N hdepthN
  have hbound := norm_boundaryHermiteJet_correctedSource_real_le_chernoff
    sigma N (depth N) (by simpa [hsigmaGap] using hd0) hsigma0 ht0 hq0 hexpSub
  calc
    ‖squarefreeHalfDirichletPartialSum N
          (supercriticalHermiteEulerAbscissa alpha : ℂ) +
        boundaryHermiteJetCounterterm N (depth N)
          (supercriticalHermiteEulerAbscissa alpha : ℂ)‖ ≤
      (N : ℝ) * Real.exp
        (-(t * (((depth N) + 1 : ℕ) : ℝ)) +
          (((sigma - 6 / 11) * (N : ℝ)) * q)) := by
      simpa [sigma] using hbound
    _ ≤ (N : ℝ) * Real.exp (-gamma * (N : ℝ)) := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg N)
      apply Real.exp_le_exp.mpr
      have hsucc : (depth N : ℝ) ≤ (((depth N) + 1 : ℕ) : ℝ) := by
        norm_num
      calc
        -(t * (((depth N) + 1 : ℕ) : ℝ)) +
            (((sigma - 6 / 11) * (N : ℝ)) * q) ≤
          -(t * (alpha * (N : ℝ))) + d * (N : ℝ) * q := by
            rw [hsigmaGap]
            nlinarith
        _ = -gamma * (N : ℝ) := by
          dsimp [gamma, q, t, d]
          unfold supercriticalHermiteChernoffRate
          ring

/-- Arithmetic source fidelity excludes every eventual point-Hermite slope strictly above the
geometric threshold `5/11`. -/
theorem not_squarefreeHalfCountertermAdmissible_boundaryHermiteJetCounterterm_of_eventually_slope_le_depth_gt_five_div_eleven
    {depth : ℕ → ℕ} {alpha : ℝ} (halpha : 5 / 11 < alpha)
    (hdepth : ∀ᶠ N : ℕ in atTop,
      alpha * (N : ℝ) ≤ (depth N : ℝ)) :
    ¬ SquarefreeHalfCountertermAdmissible
      (fun N => boundaryHermiteJetCounterterm N (depth N)) := by
  intro hadm
  let sigma := supercriticalHermiteEulerAbscissa alpha
  have hsigmaFar : (sigma : ℂ) ∈ farHalf := by
    simpa [sigma] using supercriticalHermiteEulerAbscissa_mem_farHalf halpha
  have hcounter : Tendsto
      (fun N => boundaryHermiteJetCounterterm N (depth N) (sigma : ℂ))
      atTop (nhds 0) := hadm.2.tendsto_at hsigmaFar
  have hdirichlet : Tendsto
      (fun N => squarefreeHalfDirichletPartialSum N (sigma : ℂ))
      atTop (nhds (LSeries squarefreeConvolutionHalf (sigma : ℂ))) := by
    simpa only [squarefreeHalfDirichletPartialSum] using
      tendstoLocallyUniformlyOn_squarefreeConvolutionHalf_partialSums.tendsto_at
        hsigmaFar
  have hsource : Tendsto
      (fun N => squarefreeHalfDirichletPartialSum N (sigma : ℂ) +
        boundaryHermiteJetCounterterm N (depth N) (sigma : ℂ))
      atTop (nhds (LSeries squarefreeConvolutionHalf (sigma : ℂ))) := by
    simpa using hdirichlet.add hcounter
  have hcancel : Tendsto
      (fun N => squarefreeHalfDirichletPartialSum N (sigma : ℂ) +
        boundaryHermiteJetCounterterm N (depth N) (sigma : ℂ))
      atTop (nhds 0) := by
    simpa [sigma] using
      tendsto_boundaryHermiteJet_correctedSource_supercriticalEuler_of_eventually_slope_le_depth
        halpha hdepth
  have hzero : LSeries squarefreeConvolutionHalf (sigma : ℂ) = 0 :=
    tendsto_nhds_unique hsource hcancel
  have hsigma : 1 < sigma := by
    simpa [sigma] using one_lt_supercriticalHermiteEulerAbscissa halpha
  have hs : 1 < (sigma : ℂ).re := by simpa using hsigma
  have h2s : 1 < (2 * (sigma : ℂ)).re := by
    rw [show (2 : ℂ) * (sigma : ℂ) = ((2 * sigma : ℝ) : ℂ) by
      push_cast
      ring]
    simp only [ofReal_re]
    linarith [hsigma]
  have hquot : riemannZeta (sigma : ℂ) /
      riemannZeta (2 * (sigma : ℂ)) ≠ 0 :=
    div_ne_zero (riemannZeta_ne_zero_of_one_lt_re hs)
      (riemannZeta_ne_zero_of_one_lt_re h2s)
  apply hquot
  rw [← LSeries_squarefreeConvolutionHalf_sq hs, hzero]
  norm_num

end

end RHTower
