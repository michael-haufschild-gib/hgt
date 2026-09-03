import GaloisForLFunctions.RHTower.SquarefreeConvolutionHalfMovingHermiteFarWitnessNoGo
import GaloisForLFunctions.RHTower.RiemannGaussian.FiniteToEntireExpandingTaylor

/-!
# High Hermite depth cancels the Euler source

The canonical moving Hermite correction also fails at the opposite depth scale. At the Euler-side
point `s=1101/1100`, the degree-`K` Taylor polynomial reconstructs the positively dressed entire
source whenever `K>=N/2`. Undoing the exponential dress therefore makes the counterterm converge to the
negative of the nonzero Euler source, rather than to zero.

Thus every schedule eventually above slope `1/2` violates source fidelity. Together with the far
interior witness, a surviving point-Hermite schedule must avoid both `K<=N/15` and `K>=N/2` on
every tail; the intermediate and oscillatory regimes remain open.
-/

open Complex Filter Metric Set Topology

namespace RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

/-- Centered Taylor remainder for an entire scalar function, obtained from a larger comparison
circle. -/
theorem entire_iteratedDeriv_partialSum_remainder_le_of_sphere_bound
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) (c : ℂ) {R M : ℝ} (hR : 0 < R)
    (hbound : ∀ z : ℂ, ‖z - c‖ = R → ‖f z‖ ≤ M)
    {w : ℂ} (hw : ‖w - c‖ < R) (N : ℕ) :
    ‖(∑ j ∈ Finset.range N,
        iteratedDeriv j f c / (j.factorial : ℂ) * (w - c) ^ j) - f w‖ ≤
      M * (‖w - c‖ / R) ^ N / (1 - ‖w - c‖ / R) := by
  let g : ℂ → ℂ := fun z => f (c + z)
  have hg : Differentiable ℂ g := by
    have hadd : Differentiable ℂ (fun z : ℂ => c + z) :=
      (differentiable_const (c := c)).add differentiable_id
    exact hf.comp hadd
  have hgbound : ∀ z : ℂ, ‖z‖ = R → ‖g z‖ ≤ M := by
    intro z hz
    apply hbound (c + z)
    simpa only [add_sub_cancel_left] using hz
  have hrem :=
    RiemannGaussian.entire_cauchyPowerSeries_partialSum_remainder_le_of_sphere_bound
      hg hR hgbound (w := w - c) hw N
  have hgw : g (w - c) = f w := by
    simp [g]
  rw [hgw] at hrem
  convert hrem using 1
  rw [FormalMultilinearSeries.partialSum]
  apply congrArg (fun z : ℂ => ‖z - f w‖)
  apply Finset.sum_congr rfl
  intro j hj
  rw [FormalMultilinearSeries.apply_eq_pow_smul_coeff, smul_eq_mul]
  have hp : HasFPowerSeriesOnBall g (cauchyPowerSeries g 0 1) 0 ⊤ :=
    hg.hasFPowerSeriesOnBall 0 (R := 1) (by norm_num)
  have hfac := hp.factorial_smul (1 : ℂ) j
  rw [iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod,
    Finset.prod_const_one, one_smul] at hfac
  change j.factorial • (cauchyPowerSeries g 0 1).coeff j =
    iteratedDeriv j g 0 at hfac
  have hcoeff : (cauchyPowerSeries g 0 1).coeff j =
      iteratedDeriv j g 0 / (j.factorial : ℂ) := by
    rw [eq_div_iff (by exact_mod_cast j.factorial_ne_zero)]
    simpa only [nsmul_eq_mul, mul_comm] using hfac
  rw [hcoeff, iteratedDeriv_comp_const_add]
  ring

/-- Euler-side point half a unit to the right of the Hermite anchor. -/
def hermiteEulerCancellationPoint : ℂ := (1101 / 1100 : ℂ)

theorem hermiteEulerCancellationPoint_mem_farHalf :
    hermiteEulerCancellationPoint ∈ farHalf := by
  rw [mem_farHalf]
  norm_num [hermiteEulerCancellationPoint]

private theorem norm_boundaryPositiveExponentialDress_on_fullCircle_le
    (N : ℕ) {w : ℂ} (hw : ‖w - boundaryExteriorPoint‖ = (6 / 11 : ℝ)) :
    ‖boundaryPositiveExponentialDress N w‖ ≤
      (N : ℝ) * Real.exp ((6 / 11 : ℝ) * (N : ℝ)) := by
  have hre := Complex.abs_re_le_norm (w - boundaryExteriorPoint)
  have hreal : |w.re - (6 / 11 : ℝ)| ≤ 6 / 11 := by
    rw [show (w - boundaryExteriorPoint).re = w.re - (6 / 11 : ℝ) by
      simp [boundaryExteriorPoint], hw] at hre
    exact hre
  have hwre : 0 ≤ w.re := by
    linarith [(abs_le.mp hreal).1]
  have hsep : ‖boundaryPositiveExponentialSeparator N w‖ ≤
      Real.exp ((6 / 11 : ℝ) * (N : ℝ)) := by
    rw [boundaryPositiveExponentialSeparator, Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    have hrele : w.re - (6 / 11 : ℝ) ≤ 6 / 11 :=
      (le_abs_self _).trans hreal
    have hrexp :
        (((N : ℂ) * (w - boundaryExteriorPoint)).re) =
          (N : ℝ) * (w.re - (6 / 11 : ℝ)) := by
      simp [boundaryExteriorPoint]
    rw [hrexp]
    have hN : (0 : ℝ) ≤ N := by positivity
    nlinarith
  rw [boundaryPositiveExponentialDress, norm_mul]
  exact mul_le_mul hsep (norm_squarefreeHalfDirichletPartialSum_le_nat N hwre)
    (norm_nonneg _) (Real.exp_pos _).le |>.trans_eq (mul_comm _ _)

private theorem norm_hermiteEulerCancellationPoint_gap :
    ‖hermiteEulerCancellationPoint - boundaryExteriorPoint‖ = (501 / 1100 : ℝ) := by
  norm_num [hermiteEulerCancellationPoint, boundaryExteriorPoint, Complex.norm_real]

theorem norm_boundaryHermiteJetPolynomial_sub_dress_at_hermiteEulerCancellationPoint_le
    (N K : ℕ) :
    ‖boundaryHermiteJetPolynomial N K hermiteEulerCancellationPoint -
        boundaryPositiveExponentialDress N hermiteEulerCancellationPoint‖ ≤
      (200 / 33 : ℝ) * (N : ℝ) * Real.exp ((6 / 11 : ℝ) * (N : ℝ)) *
        (167 / 200 : ℝ) ^ (K + 1) := by
  have hdiff : Differentiable ℂ (boundaryPositiveExponentialDress N) := by
    intro s
    exact (((analytic_boundaryPositiveExponentialSeparator N).mul
      (analyticOnNhd_squarefreeHalfDirichletPartialSum N)) s
        (Set.mem_univ s)).differentiableAt
  have hrem := entire_iteratedDeriv_partialSum_remainder_le_of_sphere_bound
    hdiff boundaryExteriorPoint (R := (6 / 11 : ℝ))
      (M := (N : ℝ) * Real.exp ((6 / 11 : ℝ) * (N : ℝ))) (by norm_num)
      (fun z hz => norm_boundaryPositiveExponentialDress_on_fullCircle_le N hz)
      (w := hermiteEulerCancellationPoint) (by
        rw [norm_hermiteEulerCancellationPoint_gap]
        norm_num) (K + 1)
  rw [norm_hermiteEulerCancellationPoint_gap] at hrem
  change ‖boundaryHermiteJetPolynomial N K hermiteEulerCancellationPoint -
      boundaryPositiveExponentialDress N hermiteEulerCancellationPoint‖ ≤ _
  rw [boundaryHermiteJetPolynomial]
  calc
    _ ≤ ((N : ℝ) * Real.exp ((6 / 11 : ℝ) * (N : ℝ))) *
        ((501 / 1100 : ℝ) / (6 / 11 : ℝ)) ^ (K + 1) /
          (1 - (501 / 1100 : ℝ) / (6 / 11 : ℝ)) := hrem
    _ = (200 / 33 : ℝ) * (N : ℝ) * Real.exp ((6 / 11 : ℝ) * (N : ℝ)) *
        (167 / 200 : ℝ) ^ (K + 1) := by ring

private theorem boundaryExponentialSeparator_mul_positiveDress
    (N : ℕ) (s : ℂ) :
    boundaryExponentialSeparator N s * boundaryPositiveExponentialDress N s =
      squarefreeHalfDirichletPartialSum N s := by
  rw [boundaryPositiveExponentialDress, boundaryExponentialSeparator,
    boundaryPositiveExponentialSeparator]
  rw [← mul_assoc, ← Complex.exp_add]
  have : (N : ℂ) * (boundaryExteriorPoint - s) +
      (N : ℂ) * (s - boundaryExteriorPoint) = 0 := by ring
  rw [this, Complex.exp_zero, one_mul]

theorem norm_boundaryHermiteJet_correctedSource_hermiteEulerCancellationPoint_le
    (N K : ℕ) :
    ‖squarefreeHalfDirichletPartialSum N hermiteEulerCancellationPoint +
        boundaryHermiteJetCounterterm N K hermiteEulerCancellationPoint‖ ≤
      (200 / 33 : ℝ) * (N : ℝ) * Real.exp ((9 / 100 : ℝ) * (N : ℝ)) *
        (167 / 200 : ℝ) ^ (K + 1) := by
  have hrem :=
    norm_boundaryHermiteJetPolynomial_sub_dress_at_hermiteEulerCancellationPoint_le N K
  have heq : squarefreeHalfDirichletPartialSum N hermiteEulerCancellationPoint +
      boundaryHermiteJetCounterterm N K hermiteEulerCancellationPoint =
      boundaryExponentialSeparator N hermiteEulerCancellationPoint *
        (boundaryPositiveExponentialDress N hermiteEulerCancellationPoint -
          boundaryHermiteJetPolynomial N K hermiteEulerCancellationPoint) := by
    rw [boundaryHermiteJetCounterterm,
      ← boundaryExponentialSeparator_mul_positiveDress]
    ring
  rw [heq, norm_mul, norm_boundaryExponentialSeparator]
  have hsep :
      Real.exp ((N : ℝ) * ((6 / 11 : ℝ) - hermiteEulerCancellationPoint.re)) =
        Real.exp (-(501 / 1100 : ℝ) * (N : ℝ)) := by
    congr 1
    norm_num [hermiteEulerCancellationPoint]
    ring
  rw [hsep, norm_sub_rev]
  calc
    Real.exp (-(501 / 1100 : ℝ) * (N : ℝ)) *
        ‖boundaryHermiteJetPolynomial N K hermiteEulerCancellationPoint -
          boundaryPositiveExponentialDress N hermiteEulerCancellationPoint‖ ≤
      Real.exp (-(501 / 1100 : ℝ) * (N : ℝ)) *
        ((200 / 33 : ℝ) * (N : ℝ) * Real.exp ((6 / 11 : ℝ) * (N : ℝ)) *
          (167 / 200 : ℝ) ^ (K + 1)) :=
      mul_le_mul_of_nonneg_left hrem (Real.exp_pos _).le
    _ = (200 / 33 : ℝ) * (N : ℝ) * Real.exp ((9 / 100 : ℝ) * (N : ℝ)) *
        (167 / 200 : ℝ) ^ (K + 1) := by
      rw [show Real.exp (-(501 / 1100 : ℝ) * (N : ℝ)) *
          ((200 / 33 : ℝ) * (N : ℝ) * Real.exp ((6 / 11 : ℝ) * (N : ℝ)) *
            (167 / 200 : ℝ) ^ (K + 1)) =
          (200 / 33 : ℝ) * (N : ℝ) *
            (Real.exp (-(501 / 1100 : ℝ) * (N : ℝ)) *
              Real.exp ((6 / 11 : ℝ) * (N : ℝ))) *
            (167 / 200 : ℝ) ^ (K + 1) by ring,
        ← Real.exp_add]
      congr 1
      ring

theorem tendsto_boundaryHermiteJet_correctedSource_hermiteEulerCancellationPoint_of_eventually_one_half_le_depth
    {depth : ℕ → ℕ}
    (hdepth : ∀ᶠ N : ℕ in atTop, (1 / 2 : ℝ) * (N : ℝ) ≤ (depth N : ℝ)) :
    Tendsto (fun N => squarefreeHalfDirichletPartialSum N hermiteEulerCancellationPoint +
        boundaryHermiteJetCounterterm N (depth N) hermiteEulerCancellationPoint)
      atTop (𝓝 0) := by
  have hexp : Real.exp (1801 / 10000 : ℝ) ≤ 200 / 167 := by
    have h := real_exp_sub_sum_le_factorial_tail
      (1801 / 10000 : ℝ) (by norm_num) 4
    norm_num [Finset.sum_range_succ] at h ⊢
    nlinarith [Real.exp_pos (1801 / 10000 : ℝ)]
  have hbase : (167 / 200 : ℝ) ≤ Real.exp (-(1801 / 10000 : ℝ)) := by
    rw [Real.exp_neg, inv_eq_one_div, le_div_iff₀ (Real.exp_pos _)]
    calc
      (167 / 200 : ℝ) * Real.exp (1801 / 10000 : ℝ) ≤
          (167 / 200 : ℝ) * (200 / 167 : ℝ) :=
        mul_le_mul_of_nonneg_left hexp (by norm_num)
      _ = 1 := by norm_num
  have hmajor : Tendsto
      (fun N : ℕ => (200 / 33 : ℝ) * (N : ℝ) *
        Real.exp (-(1 / 20000 : ℝ) * (N : ℝ)))
      atTop (𝓝 0) := by
    have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 (1 / 20000 : ℝ)
      (by norm_num)).comp (tendsto_natCast_atTop_atTop (R := ℝ))
    simpa only [Function.comp_apply, Real.rpow_one, mul_zero, zero_mul, mul_assoc, mul_left_comm,
      mul_comm] using h.const_mul (200 / 33 : ℝ)
  refine squeeze_zero_norm' ?_ hmajor
  filter_upwards [hdepth] with N hdepthN
  have hcounter :=
    norm_boundaryHermiteJet_correctedSource_hermiteEulerCancellationPoint_le
      N (depth N)
  have hpowSucc : (167 / 200 : ℝ) ^ (depth N + 1) ≤
      (167 / 200 : ℝ) ^ depth N :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.le_succ _)
  have hpowExp : (167 / 200 : ℝ) ^ depth N ≤
      Real.exp (-(1801 / 10000 : ℝ) * (depth N : ℝ)) := by
    calc
      (167 / 200 : ℝ) ^ depth N ≤
          (Real.exp (-(1801 / 10000 : ℝ))) ^ depth N :=
        pow_le_pow_left₀ (by norm_num) hbase _
      _ = Real.exp (-(1801 / 10000 : ℝ) * (depth N : ℝ)) := by
        rw [← Real.exp_nat_mul]
        congr 1
        ring
  have hexpDepth : Real.exp (-(1801 / 10000 : ℝ) * (depth N : ℝ)) ≤
      Real.exp (-(1801 / 20000 : ℝ) * (N : ℝ)) := by
    apply Real.exp_le_exp.mpr
    nlinarith [hdepthN]
  calc
    ‖squarefreeHalfDirichletPartialSum N hermiteEulerCancellationPoint +
        boundaryHermiteJetCounterterm N (depth N) hermiteEulerCancellationPoint‖ ≤
      (200 / 33 : ℝ) * (N : ℝ) * Real.exp ((9 / 100 : ℝ) * (N : ℝ)) *
        (167 / 200 : ℝ) ^ (depth N + 1) := hcounter
    _ ≤ (200 / 33 : ℝ) * (N : ℝ) * Real.exp ((9 / 100 : ℝ) * (N : ℝ)) *
        Real.exp (-(1801 / 20000 : ℝ) * (N : ℝ)) := by
      gcongr
      exact hpowSucc.trans (hpowExp.trans hexpDepth)
    _ = (200 / 33 : ℝ) * (N : ℝ) *
        Real.exp (-(1 / 20000 : ℝ) * (N : ℝ)) := by
      rw [show (200 / 33 : ℝ) * (N : ℝ) * Real.exp ((9 / 100 : ℝ) * (N : ℝ)) *
          Real.exp (-(1801 / 20000 : ℝ) * (N : ℝ)) =
          (200 / 33 : ℝ) * (N : ℝ) *
            (Real.exp ((9 / 100 : ℝ) * (N : ℝ)) *
              Real.exp (-(1801 / 20000 : ℝ) * (N : ℝ))) by
        ring, ← Real.exp_add]
      congr 1
      ring

/-- Compatibility corollary for the simpler superdiagonal hypothesis. -/
theorem tendsto_boundaryHermiteJet_correctedSource_hermiteEulerCancellationPoint_of_eventually_one_le_depth
    {depth : ℕ → ℕ} (hdepth : ∀ᶠ N : ℕ in atTop, N ≤ depth N) :
    Tendsto (fun N => squarefreeHalfDirichletPartialSum N hermiteEulerCancellationPoint +
        boundaryHermiteJetCounterterm N (depth N) hermiteEulerCancellationPoint)
      atTop (𝓝 0) := by
  apply tendsto_boundaryHermiteJet_correctedSource_hermiteEulerCancellationPoint_of_eventually_one_half_le_depth
  filter_upwards [hdepth] with N hN
  have hNr : (N : ℝ) ≤ depth N := by exact_mod_cast hN
  nlinarith

/-- Depth at least `N/2` reconstructs and cancels the Euler-side source, so the Hermite
counterterm cannot remain source-faithful. -/
theorem not_squarefreeHalfCountertermAdmissible_boundaryHermiteJetCounterterm_of_eventually_one_half_le_depth
    {depth : ℕ → ℕ}
    (hdepth : ∀ᶠ N : ℕ in atTop, (1 / 2 : ℝ) * (N : ℝ) ≤ (depth N : ℝ)) :
    ¬ SquarefreeHalfCountertermAdmissible
      (fun N => boundaryHermiteJetCounterterm N (depth N)) := by
  intro hadm
  have hcounter : Tendsto
      (fun N => boundaryHermiteJetCounterterm N (depth N)
        hermiteEulerCancellationPoint) atTop (𝓝 0) :=
    hadm.2.tendsto_at hermiteEulerCancellationPoint_mem_farHalf
  have hdirichlet : Tendsto
      (fun N => squarefreeHalfDirichletPartialSum N hermiteEulerCancellationPoint)
      atTop (𝓝 (LSeries squarefreeConvolutionHalf hermiteEulerCancellationPoint)) := by
    simpa only [squarefreeHalfDirichletPartialSum] using
      tendstoLocallyUniformlyOn_squarefreeConvolutionHalf_partialSums.tendsto_at
        hermiteEulerCancellationPoint_mem_farHalf
  have hsource : Tendsto
      (fun N => squarefreeHalfDirichletPartialSum N hermiteEulerCancellationPoint +
        boundaryHermiteJetCounterterm N (depth N) hermiteEulerCancellationPoint)
      atTop (𝓝 (LSeries squarefreeConvolutionHalf hermiteEulerCancellationPoint)) := by
    simpa using hdirichlet.add hcounter
  have hcancel :=
    tendsto_boundaryHermiteJet_correctedSource_hermiteEulerCancellationPoint_of_eventually_one_half_le_depth
      hdepth
  have hzero : LSeries squarefreeConvolutionHalf hermiteEulerCancellationPoint = 0 :=
    tendsto_nhds_unique hsource hcancel
  have hs : 1 < hermiteEulerCancellationPoint.re := by
    norm_num [hermiteEulerCancellationPoint]
  have h2s : 1 < (2 * hermiteEulerCancellationPoint).re := by
    norm_num [hermiteEulerCancellationPoint]
  have hquot : riemannZeta hermiteEulerCancellationPoint /
      riemannZeta (2 * hermiteEulerCancellationPoint) ≠ 0 :=
    div_ne_zero (riemannZeta_ne_zero_of_one_lt_re hs)
      (riemannZeta_ne_zero_of_one_lt_re h2s)
  apply hquot
  rw [← LSeries_squarefreeConvolutionHalf_sq hs, hzero]
  norm_num

/-- Compatibility corollary for every eventually superdiagonal schedule. -/
theorem not_squarefreeHalfCountertermAdmissible_boundaryHermiteJetCounterterm_of_eventually_one_le_depth
    {depth : ℕ → ℕ} (hdepth : ∀ᶠ N : ℕ in atTop, N ≤ depth N) :
    ¬ SquarefreeHalfCountertermAdmissible
      (fun N => boundaryHermiteJetCounterterm N (depth N)) := by
  apply not_squarefreeHalfCountertermAdmissible_boundaryHermiteJetCounterterm_of_eventually_one_half_le_depth
  filter_upwards [hdepth] with N hN
  have hNr : (N : ℝ) ≤ depth N := by exact_mod_cast hN
  nlinarith

end

end RHTower
