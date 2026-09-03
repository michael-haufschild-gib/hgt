import GaloisForLFunctions.RHTower.SquarefreeConvolutionHalfAnchoredCounterterm
import GaloisForLFunctions.HTGeometry.LogDerivUniformLimit

/-!
# First-jet obstruction for the anchored counterterm

The rank-one boundary anchor cancels every corrected approximation at `s = 6/11`, but it cannot
make any cofinal Cayley schedule locally bounded.  Its derivative at the anchor contains
`N D_N(6/11)`, whereas Cauchy's estimate bounds the derivative of the raw Dirichlet polynomial by
`22N`.  Since the raw values have no bounded tail, the corrected first jets escape.  The remaining
Cayley factor is eventually bounded below, so local boundedness of the full quotient contradicts
Cauchy's derivative estimate.

Thus cancelling one value is insufficient.  Any viable singular renormalization must control at
least a transition jet rather than merely interpolate the obstruction point.
-/

open Complex Filter Metric Set Topology

namespace RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

/-- Every squarefree convolution-half coefficient has norm at most one. -/
theorem norm_squarefreeConvolutionHalf_le_one (n : ℕ) :
    ‖squarefreeConvolutionHalf n‖ ≤ 1 := by
  rw [← squarefreeBinomialHalf_eq_squarefreeConvolutionHalf]
  by_cases hn : n = 0
  · subst n
    simp [squarefreeBinomialHalf]
  rw [squarefreeBinomialHalf, ArithmeticFunction.coe_mk, if_neg hn]
  simp only [Finsupp.prod, norm_prod]
  exact Finset.prod_le_one (fun _ _ => norm_nonneg _) fun p hp =>
    norm_choose_complex_half_le_one (n.factorization p)

/-- On the closed nonnegative half-plane, the `N`-term Dirichlet polynomial has norm at most
`N`. -/
theorem norm_squarefreeHalfDirichletPartialSum_le_nat
    (N : ℕ) {s : ℂ} (hs : 0 ≤ s.re) :
    ‖squarefreeHalfDirichletPartialSum N s‖ ≤ N := by
  rw [squarefreeHalfDirichletPartialSum]
  calc
    ‖∑ n ∈ Finset.range N, LSeries.term squarefreeConvolutionHalf s n‖ ≤
        ∑ n ∈ Finset.range N, ‖LSeries.term squarefreeConvolutionHalf s n‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _n ∈ Finset.range N, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro n hn
      by_cases hn0 : n = 0
      · subst n
        simp [LSeries.term_zero]
      rw [LSeries.norm_term_eq, if_neg hn0]
      have hn1 : (1 : ℝ) ≤ (n : ℝ) := by
        exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hn0)
      have hden : 1 ≤ (n : ℝ) ^ s.re := Real.one_le_rpow hn1 hs
      exact (div_le_one (lt_of_lt_of_le zero_lt_one hden)).2
        ((norm_squarefreeConvolutionHalf_le_one n).trans hden)
    _ = N := by simp

/-- Cauchy's estimate on the radius-`1/22` disc around `6/11` gives a linear derivative bound. -/
theorem norm_deriv_squarefreeHalfDirichletPartialSum_boundary_le (N : ℕ) :
    ‖deriv (squarefreeHalfDirichletPartialSum N) boundaryExteriorPoint‖ ≤
      22 * (N : ℝ) := by
  have hdiff : Differentiable ℂ (squarefreeHalfDirichletPartialSum N) := by
    intro s
    exact ((analyticOnNhd_squarefreeHalfDirichletPartialSum N) s (Set.mem_univ s)).differentiableAt
  have hbound : ∀ w : ℂ, ‖w - boundaryExteriorPoint‖ ≤ (1 / 22 : ℝ) →
      ‖squarefreeHalfDirichletPartialSum N w‖ ≤ (N : ℝ) := by
    intro w hw
    apply norm_squarefreeHalfDirichletPartialSum_le_nat
    have hre := Complex.abs_re_le_norm (w - boundaryExteriorPoint)
    have hreal : |w.re - (6 / 11 : ℝ)| ≤ 1 / 22 := by
      rw [show (w - boundaryExteriorPoint).re = w.re - (6 / 11 : ℝ) by
        simp [boundaryExteriorPoint]] at hre
      exact hre.trans hw
    have := (abs_le.mp hreal).1
    norm_num at *
    linarith
  have h := GaloisForLFunctions.HTGeometry.norm_deriv_le_of_forall_norm_le hdiff
    (c := boundaryExteriorPoint) (R := (1 / 22 : ℝ)) (ε := (N : ℝ))
    (δ := (1 / 22 : ℝ)) (by norm_num) hbound (z := boundaryExteriorPoint) (by norm_num)
  convert h using 1
  all_goals ring

/-- The separator's slope at its anchor is `-N`. -/
theorem hasDerivAt_boundaryExponentialSeparator_at_boundary (N : ℕ) :
    HasDerivAt (boundaryExponentialSeparator N) (-(N : ℂ)) boundaryExteriorPoint := by
  change HasDerivAt
    (fun s : ℂ => Complex.exp ((N : ℂ) * (boundaryExteriorPoint - s)))
    (-(N : ℂ)) boundaryExteriorPoint
  have hinner :=
    (((hasDerivAt_const boundaryExteriorPoint boundaryExteriorPoint).sub
      (hasDerivAt_id' boundaryExteriorPoint)).const_mul
      (N : ℂ)).cexp
  simpa only [Pi.sub_apply, id_eq, sub_self, mul_zero, Complex.exp_zero, one_mul,
    zero_sub, mul_neg, mul_one] using hinner

/-- The anchored counterterm differentiates to `N D_N(6/11)` at its anchor. -/
theorem hasDerivAt_boundaryAnchoredCounterterm_at_boundary (N : ℕ) :
    HasDerivAt (boundaryAnchoredCounterterm N)
      ((N : ℂ) * squarefreeHalfDirichletPartialSum N boundaryExteriorPoint)
      boundaryExteriorPoint := by
  change HasDerivAt
    (fun s : ℂ => -squarefreeHalfDirichletPartialSum N boundaryExteriorPoint *
      boundaryExponentialSeparator N s)
    ((N : ℂ) * squarefreeHalfDirichletPartialSum N boundaryExteriorPoint)
    boundaryExteriorPoint
  have h := (hasDerivAt_boundaryExponentialSeparator_at_boundary N).const_mul
    (-squarefreeHalfDirichletPartialSum N boundaryExteriorPoint)
  simpa only [neg_mul, mul_neg, neg_neg, mul_comm] using h

/-- Exact first jet of the corrected arithmetic factor at the anchor. -/
theorem deriv_boundaryAnchoredCorrected_at_boundary (N : ℕ) :
    deriv (fun s => squarefreeHalfDirichletPartialSum N s +
      boundaryAnchoredCounterterm N s) boundaryExteriorPoint =
      deriv (squarefreeHalfDirichletPartialSum N) boundaryExteriorPoint +
        (N : ℂ) * squarefreeHalfDirichletPartialSum N boundaryExteriorPoint := by
  have hD : HasDerivAt (squarefreeHalfDirichletPartialSum N)
      (deriv (squarefreeHalfDirichletPartialSum N) boundaryExteriorPoint)
      boundaryExteriorPoint :=
    ((analyticOnNhd_squarefreeHalfDirichletPartialSum N) boundaryExteriorPoint
      (Set.mem_univ _)).differentiableAt.hasDerivAt
  exact (hD.add (hasDerivAt_boundaryAnchoredCounterterm_at_boundary N)).deriv

/-- Since the corrected arithmetic factor vanishes at the anchor, derivatives of the other
factors disappear from the quotient's product rule. -/
theorem deriv_poleClearedFirstTrace_boundaryAnchoredCounterterm_at_boundary
    (kappa : ℕ → ℕ) (N : ℕ) :
    deriv (poleClearedFirstTraceCountertermScheduledApprox
      boundaryAnchoredCounterterm kappa N) boundaryExteriorPoint =
      poleFactorSqrtApprox (kappa N) boundaryExteriorPoint *
        (deriv (squarefreeHalfDirichletPartialSum N) boundaryExteriorPoint +
          (N : ℂ) * squarefreeHalfDirichletPartialSum N boundaryExteriorPoint) /
        squarefreeCarlemanHalfDet boundaryExteriorPoint := by
  let A : ℂ → ℂ := fun s => squarefreeHalfDirichletPartialSum N s +
    boundaryAnchoredCounterterm N s
  have hR : HasDerivAt (poleFactorSqrtApprox (kappa N))
      (deriv (poleFactorSqrtApprox (kappa N)) boundaryExteriorPoint)
      boundaryExteriorPoint :=
    (analyticOnNhd_poleFactorSqrtApprox_rightHalf (kappa N) boundaryExteriorPoint
      boundaryExteriorPoint_mem_rightHalf).differentiableAt.hasDerivAt
  have hA : HasDerivAt A
      (deriv (squarefreeHalfDirichletPartialSum N) boundaryExteriorPoint +
        (N : ℂ) * squarefreeHalfDirichletPartialSum N boundaryExteriorPoint)
      boundaryExteriorPoint := by
    have hD : HasDerivAt (squarefreeHalfDirichletPartialSum N)
        (deriv (squarefreeHalfDirichletPartialSum N) boundaryExteriorPoint)
        boundaryExteriorPoint :=
      ((analyticOnNhd_squarefreeHalfDirichletPartialSum N) boundaryExteriorPoint
        (Set.mem_univ _)).differentiableAt.hasDerivAt
    exact hD.add (hasDerivAt_boundaryAnchoredCounterterm_at_boundary N)
  have hdet : HasDerivAt squarefreeCarlemanHalfDet
      (deriv squarefreeCarlemanHalfDet boundaryExteriorPoint) boundaryExteriorPoint :=
    (analyticOnNhd_squarefreeCarlemanHalfDet_rightHalf boundaryExteriorPoint
      boundaryExteriorPoint_mem_rightHalf).differentiableAt.hasDerivAt
  have h := (hR.mul hA).div hdet
    (squarefreeCarlemanHalfDet_ne_zero boundaryExteriorPoint)
  rw [show poleClearedFirstTraceCountertermScheduledApprox
      boundaryAnchoredCounterterm kappa N =
      fun s => poleFactorSqrtApprox (kappa N) s * A s /
        squarefreeCarlemanHalfDet s by
      rfl]
  change deriv (poleFactorSqrtApprox (kappa N) * A / squarefreeCarlemanHalfDet)
      boundaryExteriorPoint = _
  rw [h.deriv]
  dsimp [A]
  simp only [boundaryAnchoredCounterterm_corrected_value, mul_zero, zero_mul, zero_add,
    sub_zero]
  field_simp [squarefreeCarlemanHalfDet_ne_zero boundaryExteriorPoint]

private theorem exists_large_squarefreeHalfDirichletPartialSum_boundary
    (B : ℝ) (M : ℕ) :
    ∃ N : ℕ, M ≤ N ∧ B <
      ‖squarefreeHalfDirichletPartialSum N boundaryExteriorPoint‖ := by
  by_contra h
  push Not at h
  exact not_eventually_bounded_squarefreeHalfDirichletPartialSum_boundaryExteriorPoint
    ⟨B, M, fun N hMN => h N hMN⟩

/-- No cofinal Cayley schedule makes the rank-one boundary-anchored correction locally bounded.
The obstruction has moved from the value to the first jet. -/
theorem no_cofinal_boundaryAnchoredCounterterm_locallyBounded
    {kappa : ℕ → ℕ} (hkappa : Tendsto kappa atTop atTop) :
    ¬ PoleClearedFirstTraceCountertermScheduledLocallyBounded
      boundaryAnchoredCounterterm kappa := by
  intro hloc
  obtain ⟨R, hR, hball, C, hC⟩ :=
    hloc boundaryExteriorPoint boundaryExteriorPoint_mem_rightHalf
  let ρ : ℝ := R / 2
  have hρ : 0 < ρ := by dsimp [ρ]; linarith
  have hρR : ρ < R := by dsimp [ρ]; linarith
  have hCnonneg : 0 ≤ C := by
    have h := hC 0 boundaryExteriorPoint (mem_ball_self hR)
    exact (norm_nonneg _).trans h
  let K : ℝ := C / ρ
  have hKnonneg : 0 ≤ K := div_nonneg hCnonneg hρ.le
  have hderivUpper : ∀ N : ℕ,
      ‖deriv (poleClearedFirstTraceCountertermScheduledApprox
        boundaryAnchoredCounterterm kappa N) boundaryExteriorPoint‖ ≤ K := by
    intro N
    let P : ℂ → ℂ := poleClearedFirstTraceCountertermScheduledApprox
      boundaryAnchoredCounterterm kappa N
    have hana : AnalyticOnNhd ℂ P rightHalf :=
      analyticOnNhd_poleClearedFirstTraceCountertermScheduledApprox_rightHalf
        boundaryAnchoredCounterterm_admissible kappa N
    have hclosure : closure (ball boundaryExteriorPoint ρ) ⊆ rightHalf := by
      rw [closure_ball _ hρ.ne']
      exact fun z hz => hball (Metric.closedBall_subset_ball hρR hz)
    have hdiff : DifferentiableOn ℂ P (closure (ball boundaryExteriorPoint ρ)) :=
      hana.differentiableOn.mono hclosure
    apply Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hρ hdiff.diffContOnCl
    intro z hz
    apply hC N z
    exact Metric.closedBall_subset_ball hρR (Metric.sphere_subset_closedBall hz)
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp
    (hkappa.eventually (eventually_ge_atTop 24))
  let d : ℝ := ‖squarefreeCarlemanHalfDet boundaryExteriorPoint‖
  have hd : 0 < d := norm_pos_iff.mpr
    (squarefreeCarlemanHalfDet_ne_zero boundaryExteriorPoint)
  obtain ⟨N, hN, hraw⟩ :=
    exists_large_squarefreeHalfDirichletPartialSum_boundary
      (22 + K * d + 1) (max N₀ 1)
  have hNstage : N₀ ≤ N := (le_max_left N₀ 1).trans hN
  have hNone : 1 ≤ N := (le_max_right N₀ 1).trans hN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (Nat.zero_lt_of_lt hNone)
  let D : ℂ := squarefreeHalfDirichletPartialSum N boundaryExteriorPoint
  let D' : ℂ := deriv (squarefreeHalfDirichletPartialSum N) boundaryExteriorPoint
  have hD' : ‖D'‖ ≤ 22 * (N : ℝ) :=
    norm_deriv_squarefreeHalfDirichletPartialSum_boundary_le N
  have hreverse : (N : ℝ) * ‖D‖ - ‖D'‖ ≤ ‖D' + (N : ℂ) * D‖ := by
    have h := norm_sub_norm_le ((N : ℂ) * D) (-D')
    rw [norm_mul, norm_natCast, norm_neg, sub_neg_eq_add, add_comm] at h
    exact h
  have hAlarge : K * d < ‖D' + (N : ℂ) * D‖ := by
    have hraw' : 22 + K * d + 1 < ‖D‖ := hraw
    have hKd : 0 ≤ K * d := mul_nonneg hKnonneg hd.le
    have hbase : (N : ℝ) * ‖D‖ - 22 * (N : ℝ) ≤
        ‖D' + (N : ℂ) * D‖ := by
      exact (sub_le_sub_left hD' ((N : ℝ) * ‖D‖)).trans hreverse
    have hgap : K * d + 1 < ‖D‖ - 22 := by linarith
    have hNge : (1 : ℝ) ≤ N := by exact_mod_cast hNone
    calc
      K * d < 1 * (K * d + 1) := by linarith
      _ ≤ (N : ℝ) * (K * d + 1) :=
        mul_le_mul_of_nonneg_right hNge (by linarith)
      _ < (N : ℝ) * (‖D‖ - 22) := mul_lt_mul_of_pos_left hgap hNpos
      _ = (N : ℝ) * ‖D‖ - 22 * (N : ℝ) := by ring
      _ ≤ ‖D' + (N : ℂ) * D‖ := hbase
  have hfactor := norm_poleFactorSqrtApprox_boundaryExteriorPoint_five_pow
    (hN₀ N hNstage)
  have hone : (1 : ℝ) ≤ ‖poleFactorSqrtApprox (kappa N) boundaryExteriorPoint‖ := by
    exact (one_le_pow₀ (by norm_num)).trans hfactor
  have hderivLower : K <
      ‖deriv (poleClearedFirstTraceCountertermScheduledApprox
        boundaryAnchoredCounterterm kappa N) boundaryExteriorPoint‖ := by
    rw [deriv_poleClearedFirstTrace_boundaryAnchoredCounterterm_at_boundary,
      norm_div, norm_mul]
    change K < ‖poleFactorSqrtApprox (kappa N) boundaryExteriorPoint‖ *
      ‖D' + (N : ℂ) * D‖ / d
    have hnum : K * d <
        ‖poleFactorSqrtApprox (kappa N) boundaryExteriorPoint‖ *
          ‖D' + (N : ℂ) * D‖ :=
      hAlarge.trans_le (by
        simpa only [one_mul] using
          mul_le_mul_of_nonneg_right hone (norm_nonneg (D' + (N : ℂ) * D)))
    exact (lt_div_iff₀ hd).2 hnum
  exact (not_lt_of_ge (hderivUpper N)) hderivLower

end

end RHTower
