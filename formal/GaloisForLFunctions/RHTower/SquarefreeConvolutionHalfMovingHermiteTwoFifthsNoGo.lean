import GaloisForLFunctions.RHTower.SquarefreeConvolutionHalfMovingHermiteVeryNearOneWitnessNoGo

/-!
# The `20/21` witness closes Hermite depths through slope `2/5`

Keep the arithmetic witness `s=20/21`, but enlarge the Cauchy circle about the Hermite anchor
`6/11` from radius `3/8` to radius `2/5`. The circle still lies in `Re(s) >= 0`. The witness gap
is `94/231`, so the Taylor ratio becomes `235/231`; after undoing the exponential dress,

`|c_{N,K}(20/21)| ≤ 58 N (235/231)^(K+1) exp(-(8/1155)N)`.

The rational inequality `235/231 ≤ exp(1/58)` makes this tend to zero whenever `K ≤ 2N/5`,
with residual exponential rate `1/33495`. The already-proved pole-factor lower bound at the same
witness makes local boundedness require the counterterm to be unbounded there. Thus every surviving
canonical point-Hermite schedule must exceed slope `2/5` infinitely often.
-/

open Complex Filter Metric Set Topology

namespace RHTower

noncomputable section

private theorem norm_boundaryPositiveExponentialDress_on_twoFifthsSphere_le
    (N : ℕ) {w : ℂ} (hw : w ∈ sphere boundaryExteriorPoint (2 / 5 : ℝ)) :
    ‖boundaryPositiveExponentialDress N w‖ ≤
      (N : ℝ) * Real.exp ((2 / 5 : ℝ) * (N : ℝ)) := by
  have hwnorm : ‖w - boundaryExteriorPoint‖ = (2 / 5 : ℝ) := by
    simpa [Complex.dist_eq] using mem_sphere.mp hw
  have hre := Complex.abs_re_le_norm (w - boundaryExteriorPoint)
  have hreal : |w.re - (6 / 11 : ℝ)| ≤ 2 / 5 := by
    rw [show (w - boundaryExteriorPoint).re = w.re - (6 / 11 : ℝ) by
      simp [boundaryExteriorPoint], hwnorm] at hre
    exact hre
  have hwre : 0 ≤ w.re := by
    have := (abs_le.mp hreal).1
    norm_num at *
    linarith
  have hsep : ‖boundaryPositiveExponentialSeparator N w‖ ≤
      Real.exp ((2 / 5 : ℝ) * (N : ℝ)) := by
    rw [boundaryPositiveExponentialSeparator, Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    have hrele : w.re - (6 / 11 : ℝ) ≤ 2 / 5 :=
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

theorem norm_iteratedDeriv_boundaryPositiveExponentialDress_twoFifthsCircle_le
    (j N : ℕ) :
    ‖iteratedDeriv j (boundaryPositiveExponentialDress N) boundaryExteriorPoint‖ ≤
      (j.factorial : ℝ) * ((N : ℝ) * Real.exp ((2 / 5 : ℝ) * (N : ℝ))) /
        (2 / 5 : ℝ) ^ j := by
  have hdiff : Differentiable ℂ (boundaryPositiveExponentialDress N) := by
    intro s
    exact (((analytic_boundaryPositiveExponentialSeparator N).mul
      (analyticOnNhd_squarefreeHalfDirichletPartialSum N)) s
        (Set.mem_univ s)).differentiableAt
  exact Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le j (by norm_num)
    hdiff.differentiableOn.diffContOnCl
    (fun w hw => norm_boundaryPositiveExponentialDress_on_twoFifthsSphere_le N hw)

private theorem norm_hermiteVeryNearOneExterior_gap_twoFifths :
    ‖hermiteVeryNearOneExteriorPoint - boundaryExteriorPoint‖ = (94 / 231 : ℝ) := by
  norm_num [hermiteVeryNearOneExteriorPoint, boundaryExteriorPoint, Complex.norm_real]

theorem norm_boundaryHermiteJetPolynomial_hermiteVeryNearOneExteriorPoint_twoFifths_le
    (N K : ℕ) :
    ‖boundaryHermiteJetPolynomial N K hermiteVeryNearOneExteriorPoint‖ ≤
      58 * ((N : ℝ) * Real.exp ((2 / 5 : ℝ) * (N : ℝ))) *
        (235 / 231 : ℝ) ^ (K + 1) := by
  rw [boundaryHermiteJetPolynomial]
  calc
    ‖∑ j ∈ Finset.range (K + 1),
        iteratedDeriv j (boundaryPositiveExponentialDress N) boundaryExteriorPoint /
            (j.factorial : ℂ) *
          (hermiteVeryNearOneExteriorPoint - boundaryExteriorPoint) ^ j‖ ≤
      ∑ j ∈ Finset.range (K + 1),
        ‖iteratedDeriv j (boundaryPositiveExponentialDress N) boundaryExteriorPoint /
            (j.factorial : ℂ) *
          (hermiteVeryNearOneExteriorPoint - boundaryExteriorPoint) ^ j‖ := norm_sum_le _ _
    _ ≤ ∑ j ∈ Finset.range (K + 1),
        ((N : ℝ) * Real.exp ((2 / 5 : ℝ) * (N : ℝ))) *
          (235 / 231 : ℝ) ^ j := by
      apply Finset.sum_le_sum
      intro j hj
      have hc :=
        norm_iteratedDeriv_boundaryPositiveExponentialDress_twoFifthsCircle_le j N
      have hjfac : (0 : ℝ) < j.factorial := by positivity
      rw [norm_mul, norm_div, Complex.norm_natCast, norm_pow,
        norm_hermiteVeryNearOneExterior_gap_twoFifths]
      calc
        ‖iteratedDeriv j (boundaryPositiveExponentialDress N) boundaryExteriorPoint‖ /
              (j.factorial : ℝ) * (94 / 231 : ℝ) ^ j ≤
          (((j.factorial : ℝ) *
              ((N : ℝ) * Real.exp ((2 / 5 : ℝ) * (N : ℝ))) /
            (2 / 5 : ℝ) ^ j) / (j.factorial : ℝ)) *
              (94 / 231 : ℝ) ^ j := by
            gcongr
        _ = ((N : ℝ) * Real.exp ((2 / 5 : ℝ) * (N : ℝ))) *
            (235 / 231 : ℝ) ^ j := by
          rw [show (94 / 231 : ℝ) = (2 / 5 : ℝ) * (235 / 231 : ℝ) by norm_num,
            mul_pow]
          field_simp
    _ = ((N : ℝ) * Real.exp ((2 / 5 : ℝ) * (N : ℝ))) *
        (∑ j ∈ Finset.range (K + 1), (235 / 231 : ℝ) ^ j) := by
      rw [Finset.mul_sum]
    _ ≤ ((N : ℝ) * Real.exp ((2 / 5 : ℝ) * (N : ℝ))) *
        (58 * (235 / 231 : ℝ) ^ (K + 1)) := by
      gcongr
      rw [geom_sum_eq (by norm_num : (235 / 231 : ℝ) ≠ 1)]
      rw [show (235 / 231 : ℝ) - 1 = 4 / 231 by norm_num,
        div_le_iff₀ (by norm_num : (0 : ℝ) < 4 / 231)]
      have hp : (0 : ℝ) ≤ (235 / 231 : ℝ) ^ (K + 1) := by positivity
      nlinarith
    _ = 58 * ((N : ℝ) * Real.exp ((2 / 5 : ℝ) * (N : ℝ))) *
        (235 / 231 : ℝ) ^ (K + 1) := by ring

theorem norm_boundaryHermiteJetCounterterm_hermiteVeryNearOneExteriorPoint_twoFifths_le
    (N K : ℕ) :
    ‖boundaryHermiteJetCounterterm N K hermiteVeryNearOneExteriorPoint‖ ≤
      58 * (N : ℝ) * (235 / 231 : ℝ) ^ (K + 1) *
        Real.exp (-(8 / 1155 : ℝ) * (N : ℝ)) := by
  rw [boundaryHermiteJetCounterterm, norm_mul, norm_neg,
    norm_boundaryExponentialSeparator]
  have hpoly :=
    norm_boundaryHermiteJetPolynomial_hermiteVeryNearOneExteriorPoint_twoFifths_le N K
  have hexp :
      Real.exp ((N : ℝ) * ((6 / 11 : ℝ) - hermiteVeryNearOneExteriorPoint.re)) =
        Real.exp (-(94 / 231 : ℝ) * (N : ℝ)) := by
    congr 1
    norm_num [hermiteVeryNearOneExteriorPoint]
    ring
  rw [hexp]
  calc
    Real.exp (-(94 / 231 : ℝ) * (N : ℝ)) *
        ‖boundaryHermiteJetPolynomial N K hermiteVeryNearOneExteriorPoint‖ ≤
      Real.exp (-(94 / 231 : ℝ) * (N : ℝ)) *
        (58 * ((N : ℝ) * Real.exp ((2 / 5 : ℝ) * (N : ℝ))) *
          (235 / 231 : ℝ) ^ (K + 1)) :=
      mul_le_mul_of_nonneg_left hpoly (Real.exp_pos _).le
    _ = 58 * (N : ℝ) * (235 / 231 : ℝ) ^ (K + 1) *
        Real.exp (-(8 / 1155 : ℝ) * (N : ℝ)) := by
      rw [show Real.exp (-(94 / 231 : ℝ) * (N : ℝ)) *
          (58 * ((N : ℝ) * Real.exp ((2 / 5 : ℝ) * (N : ℝ))) *
            (235 / 231 : ℝ) ^ (K + 1)) =
        58 * (N : ℝ) * (235 / 231 : ℝ) ^ (K + 1) *
          (Real.exp (-(94 / 231 : ℝ) * (N : ℝ)) *
            Real.exp ((2 / 5 : ℝ) * (N : ℝ))) by ring,
        ← Real.exp_add]
      congr 1
      ring

theorem tendsto_boundaryHermiteJetCounterterm_hermiteVeryNearOneExteriorPoint_of_eventually_depth_le_two_div_five
    {depth : ℕ → ℕ}
    (hdepth : ∀ᶠ N : ℕ in atTop, (depth N : ℝ) ≤ 2 * (N : ℝ) / 5) :
    Tendsto (fun N =>
      boundaryHermiteJetCounterterm N (depth N) hermiteVeryNearOneExteriorPoint)
      atTop (nhds 0) := by
  have hbaseExp : (235 / 231 : ℝ) ≤ Real.exp (1 / 58 : ℝ) := by
    have h := Real.sum_le_exp_of_nonneg (x := (1 / 58 : ℝ)) (by norm_num) 3
    norm_num [Finset.sum_range_succ] at h ⊢
    linarith
  have hmajor : Tendsto
      (fun N : ℕ => 60 * (N : ℝ) *
        Real.exp (-(1 / 33495 : ℝ) * (N : ℝ)))
      atTop (nhds 0) := by
    have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1
      (1 / 33495 : ℝ) (by norm_num)).comp
        (tendsto_natCast_atTop_atTop (R := ℝ))
    simpa [Function.comp_def, Real.rpow_one, mul_assoc, mul_left_comm, mul_comm] using
      h.const_mul 60
  refine squeeze_zero_norm' ?_ hmajor
  filter_upwards [hdepth] with N hdepthN
  have hpow : (235 / 231 : ℝ) ^ depth N ≤
      Real.exp ((1 / 58 : ℝ) * (depth N : ℝ)) := by
    calc
      (235 / 231 : ℝ) ^ depth N ≤
          (Real.exp (1 / 58 : ℝ)) ^ depth N :=
        pow_le_pow_left₀ (by norm_num) hbaseExp _
      _ = Real.exp ((1 / 58 : ℝ) * (depth N : ℝ)) := by
        rw [← Real.exp_nat_mul]
        congr 1
        ring
  have hdepthScaled :
      (1 / 58 : ℝ) * (depth N : ℝ) ≤ (1 / 145 : ℝ) * (N : ℝ) := by
    nlinarith [hdepthN]
  have hexpDepth : Real.exp ((1 / 58 : ℝ) * (depth N : ℝ)) ≤
      Real.exp ((1 / 145 : ℝ) * (N : ℝ)) :=
    Real.exp_le_exp.mpr hdepthScaled
  have hcounter :=
    norm_boundaryHermiteJetCounterterm_hermiteVeryNearOneExteriorPoint_twoFifths_le
      N (depth N)
  calc
    ‖boundaryHermiteJetCounterterm N (depth N) hermiteVeryNearOneExteriorPoint‖ ≤
      58 * (N : ℝ) * (235 / 231 : ℝ) ^ (depth N + 1) *
        Real.exp (-(8 / 1155 : ℝ) * (N : ℝ)) := hcounter
    _ = (58 * (235 / 231 : ℝ)) * (N : ℝ) *
        ((235 / 231 : ℝ) ^ depth N *
          Real.exp (-(8 / 1155 : ℝ) * (N : ℝ))) := by
      rw [pow_succ]
      ring
    _ ≤ 60 * (N : ℝ) *
        (Real.exp ((1 / 145 : ℝ) * (N : ℝ)) *
          Real.exp (-(8 / 1155 : ℝ) * (N : ℝ))) := by
      have hprefactor : (58 : ℝ) * (235 / 231 : ℝ) ≤ 60 := by norm_num
      gcongr
      exact hpow.trans hexpDepth
    _ = 60 * (N : ℝ) *
        Real.exp (-(1 / 33495 : ℝ) * (N : ℝ)) := by
      rw [← Real.exp_add]
      congr 1
      ring

/-- The `20/21` witness closes every canonical Hermite schedule eventually below slope `2/5`. -/
theorem no_cofinal_locallyBounded_boundaryHermiteJetCounterterm_of_eventually_depth_le_two_div_five
    {depth kappa : ℕ → ℕ}
    (hdepth : ∀ᶠ N : ℕ in atTop, (depth N : ℝ) ≤ 2 * (N : ℝ) / 5)
    (hkappa : Tendsto kappa atTop atTop) :
    ¬ PoleClearedFirstTraceCountertermScheduledLocallyBounded
      (fun N => boundaryHermiteJetCounterterm N (depth N)) kappa := by
  exact
    no_cofinal_locallyBounded_of_counterterm_tendsto_zero_at_hermiteVeryNearOneExteriorPoint
      hkappa
      (tendsto_boundaryHermiteJetCounterterm_hermiteVeryNearOneExteriorPoint_of_eventually_depth_le_two_div_five
        hdepth)

end

end RHTower
