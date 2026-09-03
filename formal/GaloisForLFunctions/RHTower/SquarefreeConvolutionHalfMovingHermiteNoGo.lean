import GaloisForLFunctions.RHTower.SquarefreeConvolutionHalfFixedJetEscape
import GaloisForLFunctions.RHTower.SquarefreeConvolutionHalfInteriorUnbounded

/-!
# A linear-depth Hermite transition class is still too narrow

For cutoff `N` and jet depth `K`, take the degree-`K` Taylor polynomial at `b=6/11` of the
positively dressed source `exp(N(s-b)) D_N(s)`, then multiply it by `-exp(N(b-s))`.  This is the
canonical moving-depth Hermite counterterm.

Cauchy's estimate on the circle of radius `1/77` bounds its Taylor polynomial at the independent
interior point `a=4/7`.  The distance `a-b=2/77` contributes `2^K`, while the separating
exponential contributes `exp(-N/77)` after the Cauchy-circle cost.  Hence every schedule satisfying
`K <= N/154` still tends to zero at `a`.  The previously proved interior obstruction then rules
out local boundedness for every cofinal Cayley schedule.

This closes a growing linear-depth Hermite class.  Faster depths and distributed/nonlocal
counterterms remain open.
-/

open Complex Filter Metric Set Topology

namespace RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

/-- Taylor polynomial of the positively dressed arithmetic source at `b=6/11`. -/
def boundaryHermiteJetPolynomial (N K : ℕ) (s : ℂ) : ℂ :=
  ∑ j ∈ Finset.range (K + 1),
    iteratedDeriv j (boundaryPositiveExponentialDress N) boundaryExteriorPoint /
        (j.factorial : ℂ) *
      (s - boundaryExteriorPoint) ^ j

/-- Moving-depth Hermite counterterm obtained by undoing the positive exponential dress. -/
def boundaryHermiteJetCounterterm (N K : ℕ) (s : ℂ) : ℂ :=
  -boundaryExponentialSeparator N s * boundaryHermiteJetPolynomial N K s

theorem analytic_boundaryHermiteJetPolynomial (N K : ℕ) :
    AnalyticOnNhd ℂ (boundaryHermiteJetPolynomial N K) Set.univ := by
  intro s _
  change AnalyticAt ℂ (fun z => ∑ j ∈ Finset.range (K + 1),
    iteratedDeriv j (boundaryPositiveExponentialDress N) boundaryExteriorPoint /
        (j.factorial : ℂ) * (z - boundaryExteriorPoint) ^ j) s
  have hterm : ∀ j ∈ Finset.range (K + 1), AnalyticAt ℂ
      (fun z : ℂ =>
        iteratedDeriv j (boundaryPositiveExponentialDress N) boundaryExteriorPoint /
            (j.factorial : ℂ) * (z - boundaryExteriorPoint) ^ j) s := by
    intro j _
    exact analyticAt_const.mul ((analyticAt_id.sub analyticAt_const).pow j)
  have heq : (fun z : ℂ => ∑ j ∈ Finset.range (K + 1),
      iteratedDeriv j (boundaryPositiveExponentialDress N) boundaryExteriorPoint /
          (j.factorial : ℂ) * (z - boundaryExteriorPoint) ^ j) =
      ∑ j ∈ Finset.range (K + 1), fun z : ℂ =>
        iteratedDeriv j (boundaryPositiveExponentialDress N) boundaryExteriorPoint /
            (j.factorial : ℂ) * (z - boundaryExteriorPoint) ^ j := by
    funext z
    simp
  rw [heq]
  exact Finset.analyticAt_sum (Finset.range (K + 1)) hterm

theorem analyticOnNhd_boundaryHermiteJetCounterterm (N K : ℕ) :
    AnalyticOnNhd ℂ (boundaryHermiteJetCounterterm N K) rightHalf := by
  exact ((analytic_boundaryExponentialSeparator N).neg.mul
    (analytic_boundaryHermiteJetPolynomial N K)).mono (Set.subset_univ _)

@[simp] theorem boundaryHermiteJetPolynomial_at_boundary (N K : ℕ) :
    boundaryHermiteJetPolynomial N K boundaryExteriorPoint =
      squarefreeHalfDirichletPartialSum N boundaryExteriorPoint := by
  rw [boundaryHermiteJetPolynomial]
  rw [Finset.sum_eq_single 0]
  · simp [iteratedDeriv_zero, boundaryPositiveExponentialDress]
  · intro j hj hj0
    simp [hj0]
  · simp

@[simp] theorem boundaryHermiteJetCounterterm_at_boundary (N K : ℕ) :
    boundaryHermiteJetCounterterm N K boundaryExteriorPoint =
      -squarefreeHalfDirichletPartialSum N boundaryExteriorPoint := by
  simp [boundaryHermiteJetCounterterm]

theorem boundaryHermiteJetCounterterm_corrected_value (N K : ℕ) :
    squarefreeHalfDirichletPartialSum N boundaryExteriorPoint +
      boundaryHermiteJetCounterterm N K boundaryExteriorPoint = 0 := by
  simp

private theorem norm_boundaryPositiveExponentialSeparator_on_smallSphere_le
    (N : ℕ) {w : ℂ} (hw : w ∈ sphere boundaryExteriorPoint (1 / 77 : ℝ)) :
    ‖boundaryPositiveExponentialSeparator N w‖ ≤
      Real.exp ((N : ℝ) / 77) := by
  have hwnorm : ‖w - boundaryExteriorPoint‖ = (1 / 77 : ℝ) := by
    simpa [Complex.dist_eq] using mem_sphere.mp hw
  have hre := Complex.abs_re_le_norm (w - boundaryExteriorPoint)
  have hrele : w.re - (6 / 11 : ℝ) ≤ 1 / 77 := by
    rw [show (w - boundaryExteriorPoint).re = w.re - (6 / 11 : ℝ) by
      simp [boundaryExteriorPoint], hwnorm] at hre
    exact (le_abs_self _).trans hre
  rw [boundaryPositiveExponentialSeparator, Complex.norm_exp]
  apply Real.exp_le_exp.mpr
  have hrexp :
      (((N : ℂ) * (w - boundaryExteriorPoint)).re) =
        (N : ℝ) * (w.re - (6 / 11 : ℝ)) := by
    simp [boundaryExteriorPoint]
  rw [hrexp]
  have hN : (0 : ℝ) ≤ N := by positivity
  nlinarith

private theorem norm_boundaryPositiveExponentialDress_on_smallSphere_le
    (N : ℕ) {w : ℂ} (hw : w ∈ sphere boundaryExteriorPoint (1 / 77 : ℝ)) :
    ‖boundaryPositiveExponentialDress N w‖ ≤
      (N : ℝ) * Real.exp ((N : ℝ) / 77) := by
  have hwnorm : ‖w - boundaryExteriorPoint‖ = (1 / 77 : ℝ) := by
    simpa [Complex.dist_eq] using mem_sphere.mp hw
  have hre := Complex.abs_re_le_norm (w - boundaryExteriorPoint)
  have hwre : 0 ≤ w.re := by
    have hreal : |w.re - (6 / 11 : ℝ)| ≤ 1 / 77 := by
      rw [show (w - boundaryExteriorPoint).re = w.re - (6 / 11 : ℝ) by
        simp [boundaryExteriorPoint], hwnorm] at hre
      exact hre
    have := (abs_le.mp hreal).1
    norm_num at *
    linarith
  rw [boundaryPositiveExponentialDress, norm_mul]
  exact mul_le_mul
    (norm_boundaryPositiveExponentialSeparator_on_smallSphere_le N hw)
    (norm_squarefreeHalfDirichletPartialSum_le_nat N hwre)
    (norm_nonneg _) (Real.exp_pos _).le |>.trans_eq (mul_comm _ _)

theorem norm_iteratedDeriv_boundaryPositiveExponentialDress_smallCircle_le
    (j N : ℕ) :
    ‖iteratedDeriv j (boundaryPositiveExponentialDress N) boundaryExteriorPoint‖ ≤
      (j.factorial : ℝ) * ((N : ℝ) * Real.exp ((N : ℝ) / 77)) /
        (1 / 77 : ℝ) ^ j := by
  have hdiff : Differentiable ℂ (boundaryPositiveExponentialDress N) := by
    intro s
    exact (((analytic_boundaryPositiveExponentialSeparator N).mul
      (analyticOnNhd_squarefreeHalfDirichletPartialSum N)) s (Set.mem_univ s)).differentiableAt
  exact Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le j (by norm_num)
    hdiff.differentiableOn.diffContOnCl
    (fun w hw => norm_boundaryPositiveExponentialDress_on_smallSphere_le N hw)

private theorem norm_boundaryExterior_gap :
    ‖cayleyExteriorPoint - boundaryExteriorPoint‖ = (2 / 77 : ℝ) := by
  norm_num [cayleyExteriorPoint, boundaryExteriorPoint, Complex.norm_real]

theorem norm_boundaryHermiteJetPolynomial_cayleyExteriorPoint_le (N K : ℕ) :
    ‖boundaryHermiteJetPolynomial N K cayleyExteriorPoint‖ ≤
      ((N : ℝ) * Real.exp ((N : ℝ) / 77)) * 2 ^ (K + 1) := by
  rw [boundaryHermiteJetPolynomial]
  calc
    ‖∑ j ∈ Finset.range (K + 1),
        iteratedDeriv j (boundaryPositiveExponentialDress N) boundaryExteriorPoint /
            (j.factorial : ℂ) *
          (cayleyExteriorPoint - boundaryExteriorPoint) ^ j‖ ≤
        ∑ j ∈ Finset.range (K + 1),
          ‖iteratedDeriv j (boundaryPositiveExponentialDress N) boundaryExteriorPoint /
              (j.factorial : ℂ) *
            (cayleyExteriorPoint - boundaryExteriorPoint) ^ j‖ := norm_sum_le _ _
    _ ≤ ∑ j ∈ Finset.range (K + 1),
        ((N : ℝ) * Real.exp ((N : ℝ) / 77)) * 2 ^ j := by
      apply Finset.sum_le_sum
      intro j hj
      have hc := norm_iteratedDeriv_boundaryPositiveExponentialDress_smallCircle_le j N
      have hjfac : (0 : ℝ) < j.factorial := by positivity
      rw [norm_mul, norm_div, Complex.norm_natCast, norm_pow, norm_boundaryExterior_gap]
      calc
        ‖iteratedDeriv j (boundaryPositiveExponentialDress N) boundaryExteriorPoint‖ /
              (j.factorial : ℝ) * (2 / 77 : ℝ) ^ j ≤
            (((j.factorial : ℝ) * ((N : ℝ) * Real.exp ((N : ℝ) / 77)) /
              (1 / 77 : ℝ) ^ j) / (j.factorial : ℝ)) * (2 / 77 : ℝ) ^ j := by
          gcongr
        _ = ((N : ℝ) * Real.exp ((N : ℝ) / 77)) * 2 ^ j := by
          field_simp
          rw [div_pow, div_pow]
          norm_num
          ring
    _ = ((N : ℝ) * Real.exp ((N : ℝ) / 77)) *
        (∑ j ∈ Finset.range (K + 1), (2 : ℝ) ^ j) := by
      rw [Finset.mul_sum]
    _ ≤ ((N : ℝ) * Real.exp ((N : ℝ) / 77)) * 2 ^ (K + 1) := by
      gcongr
      rw [geom_sum_eq (by norm_num : (2 : ℝ) ≠ 1)]
      norm_num

theorem norm_boundaryHermiteJetCounterterm_cayleyExteriorPoint_le (N K : ℕ) :
    ‖boundaryHermiteJetCounterterm N K cayleyExteriorPoint‖ ≤
      (N : ℝ) * 2 ^ (K + 1) * Real.exp (-(N : ℝ) / 77) := by
  rw [boundaryHermiteJetCounterterm, norm_mul, norm_neg,
    norm_boundaryExponentialSeparator]
  have hpoly := norm_boundaryHermiteJetPolynomial_cayleyExteriorPoint_le N K
  have hexp :
      Real.exp ((N : ℝ) * ((6 / 11 : ℝ) - cayleyExteriorPoint.re)) =
        Real.exp (-(2 * (N : ℝ)) / 77) := by
    congr 1
    norm_num [cayleyExteriorPoint]
    ring
  rw [hexp]
  calc
    Real.exp (-(2 * (N : ℝ)) / 77) *
        ‖boundaryHermiteJetPolynomial N K cayleyExteriorPoint‖ ≤
      Real.exp (-(2 * (N : ℝ)) / 77) *
        (((N : ℝ) * Real.exp ((N : ℝ) / 77)) * 2 ^ (K + 1)) :=
      mul_le_mul_of_nonneg_left hpoly (Real.exp_pos _).le
    _ = (N : ℝ) * 2 ^ (K + 1) * Real.exp (-(N : ℝ) / 77) := by
      have hexpCombine :
          Real.exp (-(2 * (N : ℝ)) / 77) * Real.exp ((N : ℝ) / 77) =
            Real.exp (-(N : ℝ) / 77) := by
        rw [← Real.exp_add]
        congr 1
        ring
      rw [show Real.exp (-(2 * (N : ℝ)) / 77) *
          (((N : ℝ) * Real.exp ((N : ℝ) / 77)) * 2 ^ (K + 1)) =
          (N : ℝ) * 2 ^ (K + 1) *
            (Real.exp (-(2 * (N : ℝ)) / 77) * Real.exp ((N : ℝ) / 77)) by ring,
        hexpCombine]

theorem tendsto_boundaryHermiteJetCounterterm_cayleyExteriorPoint_of_eventually_depth_le_one_div_54
    {depth : ℕ → ℕ}
    (hdepth : ∀ᶠ N : ℕ in atTop, (depth N : ℝ) ≤ (N : ℝ) / 54) :
    Tendsto (fun N => boundaryHermiteJetCounterterm N (depth N) cayleyExteriorPoint)
      atTop (𝓝 0) := by
  have htwoexp : (2 : ℝ) ≤ Real.exp (7 / 10 : ℝ) := by
    have h := Real.sum_le_exp_of_nonneg (x := (7 / 10 : ℝ)) (by norm_num) 4
    norm_num at h ⊢
    linarith
  have hmajor : Tendsto
      (fun N : ℕ => 2 * (N : ℝ) * Real.exp (-(1 / 41580 : ℝ) * (N : ℝ)))
      atTop (𝓝 0) := by
    have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 (1 / 41580 : ℝ)
      (by norm_num)).comp (tendsto_natCast_atTop_atTop (R := ℝ))
    simpa only [Function.comp_apply, Real.rpow_one, mul_zero, zero_mul, mul_assoc, mul_left_comm,
      mul_comm] using h.const_mul 2
  refine squeeze_zero_norm' ?_ hmajor
  filter_upwards [hdepth] with N hdepthN
  ·
    have hpow : (2 : ℝ) ^ depth N ≤
        Real.exp ((7 / 10 : ℝ) * (depth N : ℝ)) := by
      calc
        (2 : ℝ) ^ depth N ≤ (Real.exp (7 / 10 : ℝ)) ^ depth N :=
          pow_le_pow_left₀ (by norm_num) htwoexp _
        _ = Real.exp ((7 / 10 : ℝ) * (depth N : ℝ)) := by
          rw [← Real.exp_nat_mul]
          congr 1
          ring
    have hdepthScaled :
        (7 / 10 : ℝ) * (depth N : ℝ) ≤ 7 * (N : ℝ) / 540 := by
      nlinarith [hdepthN]
    have hexpDepth : Real.exp ((7 / 10 : ℝ) * (depth N : ℝ)) ≤
        Real.exp (7 * (N : ℝ) / 540) :=
      Real.exp_le_exp.mpr hdepthScaled
    have hcounter := norm_boundaryHermiteJetCounterterm_cayleyExteriorPoint_le N (depth N)
    calc
      ‖boundaryHermiteJetCounterterm N (depth N) cayleyExteriorPoint‖ ≤
          (N : ℝ) * 2 ^ (depth N + 1) * Real.exp (-(N : ℝ) / 77) := hcounter
      _ = 2 * (N : ℝ) * ((2 : ℝ) ^ depth N * Real.exp (-(N : ℝ) / 77)) := by
        rw [pow_succ]
        ring
      _ ≤ 2 * (N : ℝ) *
          (Real.exp (7 * (N : ℝ) / 540) * Real.exp (-(N : ℝ) / 77)) := by
        gcongr
        exact hpow.trans hexpDepth
      _ = 2 * (N : ℝ) * Real.exp (-(1 / 41580 : ℝ) * (N : ℝ)) := by
        rw [← Real.exp_add]
        congr 1
        ring

theorem tendsto_boundaryHermiteJetCounterterm_cayleyExteriorPoint_of_depth_le_one_div_54
    {depth : ℕ → ℕ}
    (hdepth : ∀ N : ℕ, (depth N : ℝ) ≤ (N : ℝ) / 54) :
    Tendsto (fun N => boundaryHermiteJetCounterterm N (depth N) cayleyExteriorPoint)
      atTop (𝓝 0) := by
  exact
    tendsto_boundaryHermiteJetCounterterm_cayleyExteriorPoint_of_eventually_depth_le_one_div_54
      (Filter.Eventually.of_forall hdepth)

theorem tendsto_boundaryHermiteJetCounterterm_cayleyExteriorPoint_of_depth_le_one_div_77
    {depth : ℕ → ℕ}
    (hdepth : ∀ N : ℕ, (depth N : ℝ) ≤ (N : ℝ) / 77) :
    Tendsto (fun N => boundaryHermiteJetCounterterm N (depth N) cayleyExteriorPoint)
      atTop (𝓝 0) := by
  apply tendsto_boundaryHermiteJetCounterterm_cayleyExteriorPoint_of_depth_le_one_div_54
  intro N
  apply (hdepth N).trans
  have hN : (0 : ℝ) ≤ N := by positivity
  nlinarith

theorem tendsto_boundaryHermiteJetCounterterm_cayleyExteriorPoint_of_depth_le
    {depth : ℕ → ℕ}
    (hdepth : ∀ N : ℕ, (depth N : ℝ) ≤ (N : ℝ) / 154) :
    Tendsto (fun N => boundaryHermiteJetCounterterm N (depth N) cayleyExteriorPoint)
      atTop (𝓝 0) := by
  apply tendsto_boundaryHermiteJetCounterterm_cayleyExteriorPoint_of_depth_le_one_div_54
  intro N
  apply (hdepth N).trans
  have hN : (0 : ℝ) ≤ N := by positivity
  nlinarith

/-- Every Hermite depth schedule eventually below slope `1/54` is incompatible with local
boundedness of a cofinal Cayley approximation. -/
theorem no_cofinal_locallyBounded_boundaryHermiteJetCounterterm_of_eventually_depth_le_one_div_54
    {depth kappa : ℕ → ℕ}
    (hdepth : ∀ᶠ N : ℕ in atTop, (depth N : ℝ) ≤ (N : ℝ) / 54)
    (hkappa : Tendsto kappa atTop atTop) :
    ¬ PoleClearedFirstTraceCountertermScheduledLocallyBounded
      (fun N => boundaryHermiteJetCounterterm N (depth N)) kappa := by
  exact no_cofinal_locallyBounded_of_counterterm_tendsto_zero_at_cayleyExteriorPoint
    hkappa
      (tendsto_boundaryHermiteJetCounterterm_cayleyExteriorPoint_of_eventually_depth_le_one_div_54
        hdepth)

theorem no_cofinal_locallyBounded_boundaryHermiteJetCounterterm_of_depth_le_one_div_54
    {depth kappa : ℕ → ℕ}
    (hdepth : ∀ N : ℕ, (depth N : ℝ) ≤ (N : ℝ) / 54)
    (hkappa : Tendsto kappa atTop atTop) :
    ¬ PoleClearedFirstTraceCountertermScheduledLocallyBounded
      (fun N => boundaryHermiteJetCounterterm N (depth N)) kappa := by
  exact
    no_cofinal_locallyBounded_boundaryHermiteJetCounterterm_of_eventually_depth_le_one_div_54
      (Filter.Eventually.of_forall hdepth) hkappa

/-- Compatibility corollary at slope `1/77`. -/
theorem no_cofinal_locallyBounded_boundaryHermiteJetCounterterm_of_depth_le_one_div_77
    {depth kappa : ℕ → ℕ}
    (hdepth : ∀ N : ℕ, (depth N : ℝ) ≤ (N : ℝ) / 77)
    (hkappa : Tendsto kappa atTop atTop) :
    ¬ PoleClearedFirstTraceCountertermScheduledLocallyBounded
      (fun N => boundaryHermiteJetCounterterm N (depth N)) kappa := by
  exact no_cofinal_locallyBounded_boundaryHermiteJetCounterterm_of_depth_le_one_div_54
    (fun N => (hdepth N).trans (by
      have hN : (0 : ℝ) ≤ N := by positivity
      nlinarith)) hkappa

/-- Compatibility corollary at the original conservative slope `1/154`. -/
theorem no_cofinal_locallyBounded_boundaryHermiteJetCounterterm_of_depth_le
    {depth kappa : ℕ → ℕ}
    (hdepth : ∀ N : ℕ, (depth N : ℝ) ≤ (N : ℝ) / 154)
    (hkappa : Tendsto kappa atTop atTop) :
    ¬ PoleClearedFirstTraceCountertermScheduledLocallyBounded
      (fun N => boundaryHermiteJetCounterterm N (depth N)) kappa := by
  exact no_cofinal_locallyBounded_of_counterterm_tendsto_zero_at_cayleyExteriorPoint
    hkappa (tendsto_boundaryHermiteJetCounterterm_cayleyExteriorPoint_of_depth_le hdepth)

end

end RHTower
