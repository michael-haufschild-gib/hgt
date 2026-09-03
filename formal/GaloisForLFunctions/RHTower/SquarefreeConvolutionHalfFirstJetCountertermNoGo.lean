import GaloisForLFunctions.RHTower.SquarefreeConvolutionHalfAnchoredCountertermNoGo

/-!
# Second-jet obstruction for a first-jet Hermite counterterm

The first Hermite correction multiplies the degree-one Taylor jet of
`exp(N(s-b)) D_N(s)` at `b = 6/11` by `-exp(N(b-s))`.  It is entire, disappears
compact-open on `Re s > 1`, and cancels both value and first derivative of the corrected
arithmetic factor at the anchor.

Its second derivative is

```text
D_N''(b) + 2 N D_N'(b) + N² D_N(b).
```

Cauchy bounds the first two raw derivatives by `22N` and `968N`.  Since `D_N(b)` has
no bounded tail, the quadratic value term forces second-jet escape.  The Cayley factor is
eventually bounded below for every cofinal schedule, so local boundedness of the full quotient
would contradict Cauchy's second-derivative estimate.

Thus matching one finite jet only moves the obstruction from derivative order one to order two.
-/

open Complex Filter Metric Set Topology

namespace RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

def boundaryFirstJetPolynomial (N : ℕ) (s : ℂ) : ℂ :=
  squarefreeHalfDirichletPartialSum N boundaryExteriorPoint +
    (deriv (squarefreeHalfDirichletPartialSum N) boundaryExteriorPoint +
      (N : ℂ) * squarefreeHalfDirichletPartialSum N boundaryExteriorPoint) *
      (s - boundaryExteriorPoint)

def boundaryFirstJetCounterterm (N : ℕ) (s : ℂ) : ℂ :=
  -boundaryExponentialSeparator N s * boundaryFirstJetPolynomial N s

theorem analytic_boundaryFirstJetPolynomial (N : ℕ) :
    AnalyticOnNhd ℂ (boundaryFirstJetPolynomial N) Set.univ := by
  intro s _
  exact analyticAt_const.add (analyticAt_const.mul (analyticAt_id.sub analyticAt_const))

theorem analyticOnNhd_boundaryFirstJetCounterterm (N : ℕ) :
    AnalyticOnNhd ℂ (boundaryFirstJetCounterterm N) rightHalf := by
  exact ((analytic_boundaryExponentialSeparator N).neg.mul
    (analytic_boundaryFirstJetPolynomial N)).mono (Set.subset_univ _)

@[simp] theorem boundaryFirstJetPolynomial_at_boundary (N : ℕ) :
    boundaryFirstJetPolynomial N boundaryExteriorPoint =
      squarefreeHalfDirichletPartialSum N boundaryExteriorPoint := by
  simp [boundaryFirstJetPolynomial]

@[simp] theorem boundaryFirstJetCounterterm_at_boundary (N : ℕ) :
    boundaryFirstJetCounterterm N boundaryExteriorPoint =
      -squarefreeHalfDirichletPartialSum N boundaryExteriorPoint := by
  simp [boundaryFirstJetCounterterm]

theorem boundaryFirstJetCounterterm_corrected_value (N : ℕ) :
    squarefreeHalfDirichletPartialSum N boundaryExteriorPoint +
      boundaryFirstJetCounterterm N boundaryExteriorPoint = 0 := by
  simp

theorem hasDerivAt_boundaryFirstJetPolynomial (N : ℕ) (s : ℂ) :
    HasDerivAt (boundaryFirstJetPolynomial N)
      (deriv (squarefreeHalfDirichletPartialSum N) boundaryExteriorPoint +
        (N : ℂ) * squarefreeHalfDirichletPartialSum N boundaryExteriorPoint) s := by
  change HasDerivAt
    (fun z : ℂ => squarefreeHalfDirichletPartialSum N boundaryExteriorPoint +
      (deriv (squarefreeHalfDirichletPartialSum N) boundaryExteriorPoint +
        (N : ℂ) * squarefreeHalfDirichletPartialSum N boundaryExteriorPoint) *
        (z - boundaryExteriorPoint)) _ s
  exact ((((hasDerivAt_id' s).sub_const boundaryExteriorPoint).const_mul
      (deriv (squarefreeHalfDirichletPartialSum N) boundaryExteriorPoint +
        (N : ℂ) * squarefreeHalfDirichletPartialSum N boundaryExteriorPoint)).const_add
    (squarefreeHalfDirichletPartialSum N boundaryExteriorPoint)).congr_deriv (by ring)

theorem hasDerivAt_boundaryExponentialSeparator (N : ℕ) (s : ℂ) :
    HasDerivAt (boundaryExponentialSeparator N)
      (-(N : ℂ) * boundaryExponentialSeparator N s) s := by
  change HasDerivAt
    (fun z : ℂ => Complex.exp ((N : ℂ) * (boundaryExteriorPoint - z)))
    (-(N : ℂ) * Complex.exp ((N : ℂ) * (boundaryExteriorPoint - s))) s
  have hinner :=
    (((hasDerivAt_const s boundaryExteriorPoint).sub (hasDerivAt_id' s)).const_mul
      (N : ℂ)).cexp
  apply hinner.congr_deriv
  simp only [Pi.sub_apply]
  ring

theorem hasDerivAt_boundaryFirstJetCounterterm_at_boundary (N : ℕ) :
    HasDerivAt (boundaryFirstJetCounterterm N)
      (-deriv (squarefreeHalfDirichletPartialSum N) boundaryExteriorPoint)
      boundaryExteriorPoint := by
  change HasDerivAt
    (fun s => -boundaryExponentialSeparator N s * boundaryFirstJetPolynomial N s)
    (-deriv (squarefreeHalfDirichletPartialSum N) boundaryExteriorPoint)
    boundaryExteriorPoint
  have h := ((hasDerivAt_boundaryExponentialSeparator_at_boundary N).neg.mul
    (hasDerivAt_boundaryFirstJetPolynomial N boundaryExteriorPoint))
  exact h.congr_deriv (by
    simp only [Pi.neg_apply, boundaryExponentialSeparator_at_boundary,
      boundaryFirstJetPolynomial_at_boundary]
    ring)

theorem deriv_boundaryFirstJetCounterterm (N : ℕ) (s : ℂ) :
    deriv (boundaryFirstJetCounterterm N) s =
      (N : ℂ) * boundaryExponentialSeparator N s * boundaryFirstJetPolynomial N s -
        boundaryExponentialSeparator N s *
          (deriv (squarefreeHalfDirichletPartialSum N) boundaryExteriorPoint +
            (N : ℂ) * squarefreeHalfDirichletPartialSum N boundaryExteriorPoint) := by
  have h := ((hasDerivAt_boundaryExponentialSeparator N s).neg.mul
    (hasDerivAt_boundaryFirstJetPolynomial N s)).deriv
  rw [show boundaryFirstJetCounterterm N =
      -boundaryExponentialSeparator N * boundaryFirstJetPolynomial N by
    rfl]
  rw [h]
  simp only [Pi.neg_apply]
  ring

theorem iteratedDeriv_two_boundaryFirstJetCounterterm_at_boundary (N : ℕ) :
    iteratedDeriv 2 (boundaryFirstJetCounterterm N) boundaryExteriorPoint =
      (N : ℂ) ^ 2 * squarefreeHalfDirichletPartialSum N boundaryExteriorPoint +
        2 * (N : ℂ) *
          deriv (squarefreeHalfDirichletPartialSum N) boundaryExteriorPoint := by
  let H1 : ℂ := deriv (squarefreeHalfDirichletPartialSum N) boundaryExteriorPoint +
    (N : ℂ) * squarefreeHalfDirichletPartialSum N boundaryExteriorPoint
  let F : ℂ → ℂ := fun s =>
    (N : ℂ) * boundaryExponentialSeparator N s * boundaryFirstJetPolynomial N s -
      boundaryExponentialSeparator N s * H1
  have hE := hasDerivAt_boundaryExponentialSeparator N boundaryExteriorPoint
  have hT := hasDerivAt_boundaryFirstJetPolynomial N boundaryExteriorPoint
  have hF : HasDerivAt F
      ((N : ℂ) ^ 2 * squarefreeHalfDirichletPartialSum N boundaryExteriorPoint +
        2 * (N : ℂ) *
          deriv (squarefreeHalfDirichletPartialSum N) boundaryExteriorPoint)
      boundaryExteriorPoint := by
    have h := (((hE.const_mul (N : ℂ)).mul hT).sub (hE.mul_const H1))
    apply h.congr_deriv
    dsimp [H1]
    simp only [boundaryExponentialSeparator_at_boundary,
      boundaryFirstJetPolynomial_at_boundary]
    ring
  have hderiv : deriv (boundaryFirstJetCounterterm N) = F := by
    funext s
    exact deriv_boundaryFirstJetCounterterm N s
  rw [show iteratedDeriv 2 (boundaryFirstJetCounterterm N) =
      deriv (deriv (boundaryFirstJetCounterterm N)) by
    rw [show (2 : ℕ) = 1 + 1 by omega, iteratedDeriv_succ, iteratedDeriv_one],
    hderiv, hF.deriv]

theorem iteratedDeriv_two_boundaryFirstJetCorrected_at_boundary (N : ℕ) :
    iteratedDeriv 2
      (squarefreeHalfDirichletPartialSum N + boundaryFirstJetCounterterm N)
      boundaryExteriorPoint =
      iteratedDeriv 2 (squarefreeHalfDirichletPartialSum N) boundaryExteriorPoint +
        2 * (N : ℂ) *
          deriv (squarefreeHalfDirichletPartialSum N) boundaryExteriorPoint +
        (N : ℂ) ^ 2 * squarefreeHalfDirichletPartialSum N boundaryExteriorPoint := by
  have hD : ContDiffAt ℂ 2 (squarefreeHalfDirichletPartialSum N) boundaryExteriorPoint :=
    ((analyticOnNhd_squarefreeHalfDirichletPartialSum N) boundaryExteriorPoint
      (Set.mem_univ _)).contDiffAt
  have hc : ContDiffAt ℂ 2 (boundaryFirstJetCounterterm N) boundaryExteriorPoint :=
    (analyticOnNhd_boundaryFirstJetCounterterm N boundaryExteriorPoint
      boundaryExteriorPoint_mem_rightHalf).contDiffAt
  rw [iteratedDeriv_add hD hc,
    iteratedDeriv_two_boundaryFirstJetCounterterm_at_boundary]
  ring

theorem norm_iteratedDeriv_squarefreeHalfDirichletPartialSum_boundary_le
    (m N : ℕ) :
    ‖iteratedDeriv m (squarefreeHalfDirichletPartialSum N) boundaryExteriorPoint‖ ≤
      (m.factorial : ℝ) * (N : ℝ) / (1 / 22 : ℝ) ^ m := by
  have hdiff : Differentiable ℂ (squarefreeHalfDirichletPartialSum N) := by
    intro s
    exact ((analyticOnNhd_squarefreeHalfDirichletPartialSum N) s (Set.mem_univ s)).differentiableAt
  have hbound : ∀ w ∈ sphere boundaryExteriorPoint (1 / 22 : ℝ),
      ‖squarefreeHalfDirichletPartialSum N w‖ ≤ (N : ℝ) := by
    intro w hw
    apply norm_squarefreeHalfDirichletPartialSum_le_nat
    have hwnorm : ‖w - boundaryExteriorPoint‖ = (1 / 22 : ℝ) := by
      simpa [Complex.dist_eq] using mem_sphere.mp hw
    have hre := Complex.abs_re_le_norm (w - boundaryExteriorPoint)
    have hreal : |w.re - (6 / 11 : ℝ)| ≤ 1 / 22 := by
      rw [show (w - boundaryExteriorPoint).re = w.re - (6 / 11 : ℝ) by
        simp [boundaryExteriorPoint], hwnorm] at hre
      exact hre
    have := (abs_le.mp hreal).1
    norm_num at *
    linarith
  exact Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le m (by norm_num)
    hdiff.differentiableOn.diffContOnCl hbound

theorem norm_iteratedDeriv_two_squarefreeHalfDirichletPartialSum_boundary_le (N : ℕ) :
    ‖iteratedDeriv 2 (squarefreeHalfDirichletPartialSum N) boundaryExteriorPoint‖ ≤
      968 * (N : ℝ) := by
  have h := norm_iteratedDeriv_squarefreeHalfDirichletPartialSum_boundary_le 2 N
  calc
    _ ≤ (2 : ℝ) * (N : ℝ) / (1 / 484 : ℝ) := by norm_num at h ⊢; exact h
    _ = 968 * (N : ℝ) := by ring

theorem norm_boundaryFirstJetPolynomial_le (N : ℕ) (s : ℂ) :
    ‖boundaryFirstJetPolynomial N s‖ ≤
      (N : ℝ) ^ 2 + (22 * (N : ℝ) + (N : ℝ) ^ 3) *
        ‖s - boundaryExteriorPoint‖ := by
  have hD0 := norm_squarefreeHalfDirichletPartialSum_boundary_le_sq N
  have hD1 := norm_deriv_squarefreeHalfDirichletPartialSum_boundary_le N
  rw [boundaryFirstJetPolynomial]
  calc
    ‖squarefreeHalfDirichletPartialSum N boundaryExteriorPoint +
        (deriv (squarefreeHalfDirichletPartialSum N) boundaryExteriorPoint +
          (N : ℂ) * squarefreeHalfDirichletPartialSum N boundaryExteriorPoint) *
          (s - boundaryExteriorPoint)‖ ≤
        ‖squarefreeHalfDirichletPartialSum N boundaryExteriorPoint‖ +
          ‖deriv (squarefreeHalfDirichletPartialSum N) boundaryExteriorPoint +
            (N : ℂ) * squarefreeHalfDirichletPartialSum N boundaryExteriorPoint‖ *
            ‖s - boundaryExteriorPoint‖ := by
      simpa only [norm_mul] using norm_add_le
        (squarefreeHalfDirichletPartialSum N boundaryExteriorPoint)
        ((deriv (squarefreeHalfDirichletPartialSum N) boundaryExteriorPoint +
          (N : ℂ) * squarefreeHalfDirichletPartialSum N boundaryExteriorPoint) *
          (s - boundaryExteriorPoint))
    _ ≤ (N : ℝ) ^ 2 +
        (22 * (N : ℝ) + (N : ℝ) * (N : ℝ) ^ 2) *
          ‖s - boundaryExteriorPoint‖ := by
      gcongr
      calc
        ‖deriv (squarefreeHalfDirichletPartialSum N) boundaryExteriorPoint +
            (N : ℂ) * squarefreeHalfDirichletPartialSum N boundaryExteriorPoint‖ ≤
            ‖deriv (squarefreeHalfDirichletPartialSum N) boundaryExteriorPoint‖ +
              ‖(N : ℂ) * squarefreeHalfDirichletPartialSum N boundaryExteriorPoint‖ :=
          norm_add_le _ _
        _ ≤ 22 * (N : ℝ) + (N : ℝ) * (N : ℝ) ^ 2 := by
          rw [norm_mul, norm_natCast]
          gcongr
    _ = (N : ℝ) ^ 2 + (22 * (N : ℝ) + (N : ℝ) ^ 3) *
        ‖s - boundaryExteriorPoint‖ := by ring

theorem tendstoLocallyUniformlyOn_boundaryFirstJetCounterterm_farHalf :
    TendstoLocallyUniformlyOn boundaryFirstJetCounterterm (fun _ => 0) atTop farHalf := by
  rw [Metric.tendstoLocallyUniformlyOn_iff]
  intro ε hε x hx
  let δ : ℝ := (x.re - 1) / 2
  have hδ : 0 < δ := by
    dsimp [δ]
    have := mem_farHalf.mp hx
    linarith
  let t : Set ℂ := ball x 1 ∩ {y | 1 + δ < y.re}
  have hxt : x ∈ t := by
    constructor
    · exact mem_ball_self (by norm_num)
    · change 1 + δ < x.re
      dsimp [δ]
      have := mem_farHalf.mp hx
      linarith
  have ht : t ∈ 𝓝[farHalf] x := by
    apply mem_nhdsWithin_of_mem_nhds
    exact (isOpen_ball.inter (isOpen_lt continuous_const Complex.continuous_re)).mem_nhds hxt
  let a : ℝ := 5 / 11 + δ
  have ha : 0 < a := by dsimp [a]; linarith
  let L : ℝ := 1 + ‖x - boundaryExteriorPoint‖
  have hL : 0 < L := by dsimp [L]; positivity
  let C0 : ℝ := 1 + 23 * L
  have hC0 : 0 < C0 := by dsimp [C0]; positivity
  have hseq0 : Tendsto
      (fun N : ℕ => (N : ℝ) ^ 3 * Real.exp (-a * (N : ℝ))) atTop (𝓝 0) := by
    convert (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 3 a ha).comp
        (tendsto_natCast_atTop_atTop (R := ℝ)) using 1
    ext N
    simp only [Function.comp_apply]
    congr 1
    exact (Real.rpow_natCast (N : ℝ) 3).symm
  have hseq : Tendsto
      (fun N : ℕ => C0 * (N : ℝ) ^ 3 * Real.exp (-a * (N : ℝ))) atTop (𝓝 0) := by
    convert hseq0.const_mul C0 using 1
    · ext N
      ring
    · simp
  obtain ⟨N₀, hN₀⟩ := (Metric.tendsto_atTop.mp hseq) ε hε
  exact ⟨t, ht, Filter.eventually_atTop.2 ⟨max N₀ 1, fun N hN y hy => by
    have hNN₀ : N₀ ≤ N := (le_max_left N₀ 1).trans hN
    have hN1 : 1 ≤ N := (le_max_right N₀ 1).trans hN
    have hNreal : (1 : ℝ) ≤ N := by exact_mod_cast hN1
    have hNnonneg : (0 : ℝ) ≤ N := le_trans zero_le_one hNreal
    have hyball : y ∈ ball x 1 := hy.1
    have hyre : 1 + δ < y.re := hy.2
    have hyxb : ‖y - boundaryExteriorPoint‖ < L := by
      have hyx : ‖y - x‖ < 1 := by simpa [Complex.dist_eq] using hyball
      dsimp [L]
      calc
        ‖y - boundaryExteriorPoint‖ = ‖(y - x) + (x - boundaryExteriorPoint)‖ := by ring_nf
        _ ≤ ‖y - x‖ + ‖x - boundaryExteriorPoint‖ := norm_add_le _ _
        _ < 1 + ‖x - boundaryExteriorPoint‖ := by linarith
    have hpoly : ‖boundaryFirstJetPolynomial N y‖ ≤ C0 * (N : ℝ) ^ 3 := by
      have hN2 : (N : ℝ) ^ 2 ≤ (N : ℝ) ^ 3 := by nlinarith [sq_nonneg (N : ℝ)]
      have hcoef : 22 * (N : ℝ) + (N : ℝ) ^ 3 ≤ 23 * (N : ℝ) ^ 3 := by
        have hNle : (N : ℝ) ≤ (N : ℝ) ^ 3 := by nlinarith [sq_nonneg (N : ℝ)]
        nlinarith
      have hbound := norm_boundaryFirstJetPolynomial_le N y
      dsimp [C0]
      calc
        ‖boundaryFirstJetPolynomial N y‖ ≤
            (N : ℝ) ^ 2 + (22 * (N : ℝ) + (N : ℝ) ^ 3) *
              ‖y - boundaryExteriorPoint‖ := hbound
        _ ≤ (N : ℝ) ^ 3 + 23 * (N : ℝ) ^ 3 * L := by
          gcongr
        _ = (1 + 23 * L) * (N : ℝ) ^ 3 := by ring
    have hexpExponent :
        (N : ℝ) * ((6 / 11 : ℝ) - y.re) ≤ -a * (N : ℝ) := by
      dsimp [a]
      nlinarith
    have hseqLt : C0 * (N : ℝ) ^ 3 * Real.exp (-a * (N : ℝ)) < ε := by
      have hdist := hN₀ N hNN₀
      have habsC : |C0| = C0 := abs_of_pos hC0
      simpa [Real.dist_eq, habsC] using hdist
    calc
      dist 0 (boundaryFirstJetCounterterm N y) =
          ‖boundaryExponentialSeparator N y‖ * ‖boundaryFirstJetPolynomial N y‖ := by
        simp [boundaryFirstJetCounterterm]
      _ ≤ ‖boundaryExponentialSeparator N y‖ * (C0 * (N : ℝ) ^ 3) :=
        mul_le_mul_of_nonneg_left hpoly (norm_nonneg _)
      _ = Real.exp ((N : ℝ) * ((6 / 11 : ℝ) - y.re)) *
          (C0 * (N : ℝ) ^ 3) := by rw [norm_boundaryExponentialSeparator]
      _ ≤ Real.exp (-a * (N : ℝ)) * (C0 * (N : ℝ) ^ 3) :=
        mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hexpExponent) (by positivity)
      _ = C0 * (N : ℝ) ^ 3 * Real.exp (-a * (N : ℝ)) := by ring
      _ < ε := hseqLt⟩⟩

theorem boundaryFirstJetCounterterm_admissible :
    SquarefreeHalfCountertermAdmissible boundaryFirstJetCounterterm :=
  ⟨analyticOnNhd_boundaryFirstJetCounterterm,
    tendstoLocallyUniformlyOn_boundaryFirstJetCounterterm_farHalf⟩

theorem iteratedDeriv_two_poleClearedFirstTrace_boundaryFirstJetCounterterm_at_boundary
    (kappa : ℕ → ℕ) (N : ℕ) :
    iteratedDeriv 2
      (poleClearedFirstTraceCountertermScheduledApprox
        boundaryFirstJetCounterterm kappa N) boundaryExteriorPoint =
      (poleFactorSqrtApprox (kappa N) boundaryExteriorPoint /
          squarefreeCarlemanHalfDet boundaryExteriorPoint) *
        (iteratedDeriv 2 (squarefreeHalfDirichletPartialSum N) boundaryExteriorPoint +
          2 * (N : ℂ) *
            deriv (squarefreeHalfDirichletPartialSum N) boundaryExteriorPoint +
          (N : ℂ) ^ 2 * squarefreeHalfDirichletPartialSum N boundaryExteriorPoint) := by
  let q : ℂ → ℂ := fun s =>
    poleFactorSqrtApprox (kappa N) s / squarefreeCarlemanHalfDet s
  let A : ℂ → ℂ := squarefreeHalfDirichletPartialSum N + boundaryFirstJetCounterterm N
  have hqana : AnalyticAt ℂ q boundaryExteriorPoint :=
    (analyticOnNhd_poleFactorSqrtApprox_rightHalf (kappa N) boundaryExteriorPoint
      boundaryExteriorPoint_mem_rightHalf).div
      (analyticOnNhd_squarefreeCarlemanHalfDet_rightHalf boundaryExteriorPoint
        boundaryExteriorPoint_mem_rightHalf)
      (squarefreeCarlemanHalfDet_ne_zero boundaryExteriorPoint)
  have hAana : AnalyticAt ℂ A boundaryExteriorPoint :=
    (((analyticOnNhd_squarefreeHalfDirichletPartialSum N).mono (Set.subset_univ _)).add
      (analyticOnNhd_boundaryFirstJetCounterterm N)) boundaryExteriorPoint
      boundaryExteriorPoint_mem_rightHalf
  have hq : ContDiffAt ℂ 2 q boundaryExteriorPoint := hqana.contDiffAt
  have hA : ContDiffAt ℂ 2 A boundaryExteriorPoint := hAana.contDiffAt
  rw [show poleClearedFirstTraceCountertermScheduledApprox
      boundaryFirstJetCounterterm kappa N = q * A by
    funext s
    simp [poleClearedFirstTraceCountertermScheduledApprox, q, A]
    ring]
  rw [iteratedDeriv_mul hq hA]
  have hA0 : A boundaryExteriorPoint = 0 := by
    simp [A]
  have hA1 : iteratedDeriv 1 A boundaryExteriorPoint = 0 := by
    rw [iteratedDeriv_one]
    have hD : HasDerivAt (squarefreeHalfDirichletPartialSum N)
        (deriv (squarefreeHalfDirichletPartialSum N) boundaryExteriorPoint)
        boundaryExteriorPoint :=
      ((analyticOnNhd_squarefreeHalfDirichletPartialSum N) boundaryExteriorPoint
        (Set.mem_univ _)).differentiableAt.hasDerivAt
    have hc := hasDerivAt_boundaryFirstJetCounterterm_at_boundary N
    change deriv (squarefreeHalfDirichletPartialSum N + boundaryFirstJetCounterterm N)
      boundaryExteriorPoint = 0
    simpa using (hD.add hc).deriv
  have hA2 := iteratedDeriv_two_boundaryFirstJetCorrected_at_boundary N
  change iteratedDeriv 2 A boundaryExteriorPoint = _ at hA2
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose_zero_right,
    Nat.choose_self, Nat.cast_one, iteratedDeriv_zero, hA0, hA1, mul_zero,
    add_zero, zero_add, Nat.reduceSubDiff, q, A]
  rw [hA2]
  ring

theorem deriv_boundaryFirstJetCorrected_at_boundary (N : ℕ) :
    deriv (fun s => squarefreeHalfDirichletPartialSum N s +
      boundaryFirstJetCounterterm N s) boundaryExteriorPoint = 0 := by
  have hD : HasDerivAt (squarefreeHalfDirichletPartialSum N)
      (deriv (squarefreeHalfDirichletPartialSum N) boundaryExteriorPoint)
      boundaryExteriorPoint :=
    ((analyticOnNhd_squarefreeHalfDirichletPartialSum N) boundaryExteriorPoint
      (Set.mem_univ _)).differentiableAt.hasDerivAt
  change deriv (squarefreeHalfDirichletPartialSum N + boundaryFirstJetCounterterm N)
    boundaryExteriorPoint = 0
  simpa using (hD.add (hasDerivAt_boundaryFirstJetCounterterm_at_boundary N)).deriv

private theorem exists_large_squarefreeHalfDirichletPartialSum_boundary_firstJet
    (B : ℝ) (M : ℕ) :
    ∃ N : ℕ, M ≤ N ∧ B <
      ‖squarefreeHalfDirichletPartialSum N boundaryExteriorPoint‖ := by
  by_contra h
  push Not at h
  exact not_eventually_bounded_squarefreeHalfDirichletPartialSum_boundaryExteriorPoint
    ⟨B, M, fun N hMN => h N hMN⟩

theorem no_cofinal_boundaryFirstJetCounterterm_locallyBounded
    {kappa : ℕ → ℕ} (hkappa : Tendsto kappa atTop atTop) :
    ¬ PoleClearedFirstTraceCountertermScheduledLocallyBounded
      boundaryFirstJetCounterterm kappa := by
  intro hloc
  obtain ⟨R, hR, hball, C, hC⟩ :=
    hloc boundaryExteriorPoint boundaryExteriorPoint_mem_rightHalf
  let ρ : ℝ := R / 2
  have hρ : 0 < ρ := by dsimp [ρ]; linarith
  have hρR : ρ < R := by dsimp [ρ]; linarith
  have hCnonneg : 0 ≤ C := by
    have h := hC 0 boundaryExteriorPoint (mem_ball_self hR)
    exact (norm_nonneg _).trans h
  let K : ℝ := 2 * C / ρ ^ 2
  have hKnonneg : 0 ≤ K := div_nonneg (mul_nonneg (by norm_num) hCnonneg) (sq_nonneg ρ)
  have hderivUpper : ∀ N : ℕ,
      ‖iteratedDeriv 2
        (poleClearedFirstTraceCountertermScheduledApprox
          boundaryFirstJetCounterterm kappa N) boundaryExteriorPoint‖ ≤ K := by
    intro N
    let P : ℂ → ℂ := poleClearedFirstTraceCountertermScheduledApprox
      boundaryFirstJetCounterterm kappa N
    have hana : AnalyticOnNhd ℂ P rightHalf := by
      exact (analyticOnNhd_poleFactorSqrtApprox_rightHalf (kappa N)).mul
        (((analyticOnNhd_squarefreeHalfDirichletPartialSum N).mono (Set.subset_univ _)).add
          (analyticOnNhd_boundaryFirstJetCounterterm N)) |>.div
          analyticOnNhd_squarefreeCarlemanHalfDet_rightHalf
          (fun s _ => squarefreeCarlemanHalfDet_ne_zero s)
    have hclosure : closure (ball boundaryExteriorPoint ρ) ⊆ rightHalf := by
      rw [closure_ball _ hρ.ne']
      exact fun z hz => hball (Metric.closedBall_subset_ball hρR hz)
    have hdiff : DifferentiableOn ℂ P (closure (ball boundaryExteriorPoint ρ)) :=
      hana.differentiableOn.mono hclosure
    have h := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le
      2 hρ hdiff.diffContOnCl (fun z hz =>
        hC N z (Metric.closedBall_subset_ball hρR (Metric.sphere_subset_closedBall hz)))
    simpa [K] using h
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp
    (hkappa.eventually (eventually_ge_atTop 24))
  let d : ℝ := ‖squarefreeCarlemanHalfDet boundaryExteriorPoint‖
  have hd : 0 < d := norm_pos_iff.mpr
    (squarefreeCarlemanHalfDet_ne_zero boundaryExteriorPoint)
  obtain ⟨N, hN, hraw⟩ :=
    exists_large_squarefreeHalfDirichletPartialSum_boundary_firstJet
      (1013 + K * d) (max N₀ 1)
  have hNstage : N₀ ≤ N := (le_max_left N₀ 1).trans hN
  have hNone : 1 ≤ N := (le_max_right N₀ 1).trans hN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (Nat.zero_lt_of_lt hNone)
  have hNge : (1 : ℝ) ≤ N := by exact_mod_cast hNone
  let D : ℂ := squarefreeHalfDirichletPartialSum N boundaryExteriorPoint
  let D1 : ℂ := deriv (squarefreeHalfDirichletPartialSum N) boundaryExteriorPoint
  let D2 : ℂ := iteratedDeriv 2 (squarefreeHalfDirichletPartialSum N)
    boundaryExteriorPoint
  have hD1 : ‖D1‖ ≤ 22 * (N : ℝ) :=
    norm_deriv_squarefreeHalfDirichletPartialSum_boundary_le N
  have hD2 : ‖D2‖ ≤ 968 * (N : ℝ) :=
    norm_iteratedDeriv_two_squarefreeHalfDirichletPartialSum_boundary_le N
  have hother : ‖D2 + 2 * (N : ℂ) * D1‖ ≤
      968 * (N : ℝ) + 44 * (N : ℝ) ^ 2 := by
    calc
      ‖D2 + 2 * (N : ℂ) * D1‖ ≤ ‖D2‖ + ‖2 * (N : ℂ) * D1‖ := norm_add_le _ _
      _ ≤ 968 * (N : ℝ) + 2 * (N : ℝ) * (22 * (N : ℝ)) := by
        rw [norm_mul, norm_mul, norm_natCast]
        norm_num
        gcongr
      _ = 968 * (N : ℝ) + 44 * (N : ℝ) ^ 2 := by ring
  have hreverse : (N : ℝ) ^ 2 * ‖D‖ - ‖D2 + 2 * (N : ℂ) * D1‖ ≤
      ‖D2 + 2 * (N : ℂ) * D1 + (N : ℂ) ^ 2 * D‖ := by
    have h := norm_sub_norm_le ((N : ℂ) ^ 2 * D) (-(D2 + 2 * (N : ℂ) * D1))
    rw [norm_mul, norm_pow, norm_natCast, norm_neg, sub_neg_eq_add, add_comm] at h
    calc
      (N : ℝ) ^ 2 * ‖D‖ - ‖D2 + 2 * (N : ℂ) * D1‖ =
          (N : ℝ) ^ 2 * ‖D‖ - ‖2 * (N : ℂ) * D1 + D2‖ := by
        congr 2
        ring
      _ ≤ ‖(N : ℂ) ^ 2 * D + (2 * (N : ℂ) * D1 + D2)‖ := h
      _ = ‖D2 + 2 * (N : ℂ) * D1 + (N : ℂ) ^ 2 * D‖ := by
        congr 1
        ring
  have hsecond : (N : ℝ) ^ 2 * ‖D‖ -
      (968 * (N : ℝ) + 44 * (N : ℝ) ^ 2) ≤
      ‖D2 + 2 * (N : ℂ) * D1 + (N : ℂ) ^ 2 * D‖ :=
    (sub_le_sub_left hother ((N : ℝ) ^ 2 * ‖D‖)).trans hreverse
  have hjetLarge : K * d <
      ‖D2 + 2 * (N : ℂ) * D1 + (N : ℂ) ^ 2 * D‖ := by
    have hKd : 0 ≤ K * d := mul_nonneg hKnonneg hd.le
    have hn2pos : 0 < (N : ℝ) ^ 2 := sq_pos_of_pos hNpos
    have hn2ge : (1 : ℝ) ≤ (N : ℝ) ^ 2 := by nlinarith
    have hraw' : 1013 + K * d < ‖D‖ := hraw
    have hmul := mul_lt_mul_of_pos_left hraw' hn2pos
    calc
      K * d < (N : ℝ) ^ 2 * (K * d) + (N : ℝ) := by nlinarith
      _ ≤ (N : ℝ) ^ 2 * (K * d) +
          (969 * (N : ℝ) ^ 2 - 968 * (N : ℝ)) := by nlinarith
      _ = (N : ℝ) ^ 2 * (1013 + K * d) -
          (968 * (N : ℝ) + 44 * (N : ℝ) ^ 2) := by ring
      _ < (N : ℝ) ^ 2 * ‖D‖ -
          (968 * (N : ℝ) + 44 * (N : ℝ) ^ 2) := by linarith
      _ ≤ ‖D2 + 2 * (N : ℂ) * D1 + (N : ℂ) ^ 2 * D‖ := hsecond
  have hfactor := norm_poleFactorSqrtApprox_boundaryExteriorPoint_five_pow
    (hN₀ N hNstage)
  have hone : (1 : ℝ) ≤ ‖poleFactorSqrtApprox (kappa N) boundaryExteriorPoint‖ :=
    (one_le_pow₀ (by norm_num)).trans hfactor
  have hderivLower : K <
      ‖iteratedDeriv 2
        (poleClearedFirstTraceCountertermScheduledApprox
          boundaryFirstJetCounterterm kappa N) boundaryExteriorPoint‖ := by
    rw [iteratedDeriv_two_poleClearedFirstTrace_boundaryFirstJetCounterterm_at_boundary,
      norm_mul, norm_div]
    change K <
      (‖poleFactorSqrtApprox (kappa N) boundaryExteriorPoint‖ / d) *
        ‖D2 + 2 * (N : ℂ) * D1 + (N : ℂ) ^ 2 * D‖
    rw [div_mul_eq_mul_div]
    apply (lt_div_iff₀ hd).2
    exact hjetLarge.trans_le (by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hone
        (norm_nonneg (D2 + 2 * (N : ℂ) * D1 + (N : ℂ) ^ 2 * D)))
  exact (not_lt_of_ge (hderivUpper N)) hderivLower

end

end RHTower

