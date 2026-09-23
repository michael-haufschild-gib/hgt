import GaloisForLFunctions.RHTower.SquarefreeConvolutionHalfCofinalScheduleNoGo
import GaloisForLFunctions.RHTower.SquarefreeConvolutionHalfCountertermNecessity
import GaloisForLFunctions.RHTower.SquarefreeConvolutionHalfCayleyScheduleCeiling

/-!
# Interior unboundedness of the squarefree convolution half

The Abel obstruction is not special to the rational witness `6/11`.  If the canonical
convolution-half Dirichlet partial sums were bounded at any real point `sigma` with
`1/2 < sigma < 1`, Abel summation would make their Dirichlet series holomorphic on a half-plane
still containing `s = 1`.  Squaring in the Euler chamber and applying analytic uniqueness would
again force the zeta residue unit to vanish at one.

Thus the raw arithmetic half has no bounded tail at every real point of the open interval
`(1/2, 1)`.  A source-faithful singular renormalization must consequently remain active throughout
that whole interval; cancelling one fixed anchor cannot suffice.
-/

open Complex Filter Metric Set Topology

namespace RHTower

open GaloisForLFunctions
open GaloisForLFunctions.RHTower

noncomputable section

/-- Raw convolution-half Dirichlet partial sums are unbounded at every real point strictly between
`1/2` and `1`. -/
theorem not_exists_bound_squarefreeHalfDirichletPartialSum_of_half_lt_real_lt_one
    {sigma : ℝ} (hsigmaHalf : 1 / 2 < sigma) (hsigmaOne : sigma < 1) :
    ¬ ∃ C : ℝ, ∀ N : ℕ,
      ‖squarefreeHalfDirichletPartialSum N (sigma : ℂ)‖ ≤ C := by
  rintro ⟨C, hC⟩
  let tau : ℝ := (sigma + 1) / 2
  have hsigmaTau : sigma < tau := by
    dsimp [tau]
    linarith
  have htauOne : tau < 1 := by
    dsimp [tau]
    linarith
  have hhalfTau : 1 / 2 < tau := by
    dsimp [tau]
    linarith
  have hshiftBound : ∀ N : ℕ,
      ‖dirichletPartialSum squarefreeConvolutionHalfShift N (sigma : ℂ)‖ ≤ C := by
    intro N
    rw [dirichletPartialSum_squarefreeConvolutionHalfShift]
    exact hC (N + 1)
  have hconv : DirichletConvergesAt squarefreeConvolutionHalfShift (tau : ℂ) := by
    have h := tendsto_dirichlet_partialSum_of_bounded hshiftBound
      (s := (tau : ℂ) - (sigma : ℂ)) (by
        simp only [Complex.sub_re, Complex.ofReal_re]
        linarith)
    obtain ⟨L, hL⟩ := h
    refine ⟨L, ?_⟩
    convert hL using 1
    ext N
    unfold dirichletPartialSum squarefreeConvolutionHalfShift
    apply Finset.sum_congr rfl
    intro n hn
    have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hne : ((((n : ℝ) + 1 : ℝ)) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.2 (ne_of_gt hpos)
    rw [mul_assoc, ← Complex.cpow_add _ _ hne]
    congr 2
    ring
  let F : ℂ → ℂ := dirichletSum squarefreeConvolutionHalfShift
  let U : Set ℂ := {s : ℂ | tau < s.re}
  have hFdiff : DifferentiableOn ℂ F U := by
    simpa [F, U] using differentiableOn_dirichletSum hconv
  have hFana : AnalyticOnNhd ℂ F U :=
    hFdiff.analyticOnNhd (isOpen_lt continuous_const Complex.continuous_re)
  have hFeq : EqOn F (LSeries squarefreeConvolutionHalf) farHalf := by
    intro s hs
    have hstau : tau < s.re := by
      have hsone := mem_farHalf.mp hs
      linarith
    have hconvS : DirichletConvergesAt squarefreeConvolutionHalfShift s :=
      tendsto_dirichlet_partialSum_of_re_lt hconv (by simpa using hstau)
    have hleft := tendsto_dirichletSum hconvS
    have hleft' : Tendsto (fun N => squarefreeHalfDirichletPartialSum (N + 1) s)
        atTop (𝓝 (F s)) := by
      simpa [F, dirichletPartialSum_squarefreeConvolutionHalfShift] using hleft
    have hright0 :=
      tendstoLocallyUniformlyOn_squarefreeConvolutionHalf_partialSums.tendsto_at hs
    have hright : Tendsto (fun N => squarefreeHalfDirichletPartialSum (N + 1) s)
        atTop (𝓝 (LSeries squarefreeConvolutionHalf s)) :=
      hright0.comp (tendsto_add_atTop_nat 1)
    exact tendsto_nhds_unique hleft' hright
  let H : ℂ → ℂ := fun s =>
    (s - 1) * F s ^ (2 : ℕ) * riemannZeta (2 * s) - zetaResidueUnit s
  have hHana : AnalyticOnNhd ℂ H U := by
    intro s hs
    have htwo : 2 * s ≠ 1 := by
      intro h
      have hre := congrArg Complex.re h
      norm_num at hre
      change tau < s.re at hs
      linarith
    exact (((show AnalyticAt ℂ (fun z : ℂ => z - 1) s by fun_prop).mul
      ((hFana s hs).pow 2)).mul
      ((analyticOn_riemannZeta (2 * s) htwo).comp (by fun_prop))).sub
      (analyticAt_zetaResidueUnit s)
  have hHzeroFar : EqOn H 0 farHalf := by
    intro s hs
    have hs1 : 1 < s.re := mem_farHalf.mp hs
    have htwo : riemannZeta (2 * s) ≠ 0 :=
      riemannZeta_ne_zero_of_one_lt_re (by norm_num; linarith)
    have htwo' : riemannZeta (s * 2) ≠ 0 := by simpa [mul_comm] using htwo
    have hsne : s ≠ 1 := by
      intro h
      rw [h] at hs1
      norm_num at hs1
    dsimp [H]
    rw [hFeq hs, LSeries_squarefreeConvolutionHalf_sq hs1]
    rw [zetaResidueUnit, Function.update_of_ne hsne]
    field_simp [htwo']
    ring
  have hUpre : IsPreconnected U := by
    exact (convex_halfSpace_re_gt tau).isPreconnected
  have honeU : (1 : ℂ) ∈ U := by
    change tau < (1 : ℂ).re
    simpa using htauOne
  have hfreq : ∃ᶠ s in 𝓝[≠] (2 : ℂ), H s = 0 := by
    have hfar : ∀ᶠ s in 𝓝 (2 : ℂ), s ∈ farHalf :=
      isOpen_farHalf.mem_nhds two_mem_farHalf
    have hzero : ∀ᶠ s in 𝓝 (2 : ℂ), H s = 0 :=
      hfar.mono (fun s hs => hHzeroFar hs)
    exact (Filter.Eventually.filter_mono nhdsWithin_le_nhds hzero).frequently
  have htwoU : (2 : ℂ) ∈ U := by
    change tau < (2 : ℂ).re
    norm_num
    linarith
  have hzeroAll := hHana.eqOn_zero_of_preconnected_of_frequently_eq_zero
    hUpre htwoU hfreq
  have hzero := hzeroAll honeU
  dsimp [H] at hzero
  rw [zetaResidueUnit_one] at hzero
  norm_num at hzero

/-- Strong tail form of interior unboundedness. -/
theorem not_eventually_bounded_squarefreeHalfDirichletPartialSum_of_half_lt_real_lt_one
    {sigma : ℝ} (hsigmaHalf : 1 / 2 < sigma) (hsigmaOne : sigma < 1) :
    ¬ ∃ C : ℝ, ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ‖squarefreeHalfDirichletPartialSum N (sigma : ℂ)‖ ≤ C := by
  rintro ⟨C, N₀, hC⟩
  apply not_exists_bound_squarefreeHalfDirichletPartialSum_of_half_lt_real_lt_one
    hsigmaHalf hsigmaOne
  let B : ℝ := ∑ N ∈ Finset.range N₀,
    ‖squarefreeHalfDirichletPartialSum N (sigma : ℂ)‖
  refine ⟨max C B, fun N => ?_⟩
  by_cases hN : N₀ ≤ N
  · exact (hC N hN).trans (le_max_left _ _)
  · have hmem : N ∈ Finset.range N₀ := Finset.mem_range.mpr (by omega)
    have hterm : ‖squarefreeHalfDirichletPartialSum N (sigma : ℂ)‖ ≤ B := by
      dsimp [B]
      exact Finset.single_le_sum (fun i _ => norm_nonneg
        (squarefreeHalfDirichletPartialSum i (sigma : ℂ))) hmem
    exact hterm.trans (le_max_right _ _)

/-- The existing Cayley exterior witness `4/7` also has no bounded raw tail. -/
theorem not_eventually_bounded_squarefreeHalfDirichletPartialSum_cayleyExteriorPoint :
    ¬ ∃ C : ℝ, ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ‖squarefreeHalfDirichletPartialSum N cayleyExteriorPoint‖ ≤ C := by
  simpa [cayleyExteriorPoint] using
    (not_eventually_bounded_squarefreeHalfDirichletPartialSum_of_half_lt_real_lt_one
      (sigma := (4 / 7 : ℝ)) (by norm_num) (by norm_num))

/-- Local boundedness of a cofinal corrected family forces its counterterm to remain unbounded at
the second interior witness `4/7`, not only at the original anchor `6/11`. -/
theorem counterterm_not_eventually_bounded_at_cayleyExteriorPoint_of_cofinal_locallyBounded
    {counterterm : ℕ → ℂ → ℂ} {kappa : ℕ → ℕ}
    (hkappa : Tendsto kappa atTop atTop)
    (hloc : PoleClearedFirstTraceCountertermScheduledLocallyBounded counterterm kappa) :
    ¬ ∃ B : ℝ, ∃ M₀ : ℕ, ∀ N : ℕ, M₀ ≤ N →
      ‖counterterm N cayleyExteriorPoint‖ ≤ B := by
  obtain ⟨R, hR, _, C, hC⟩ :=
    hloc cayleyExteriorPoint cayleyExteriorPoint_mem_rightHalf
  have hcenter : cayleyExteriorPoint ∈ ball cayleyExteriorPoint R := mem_ball_self hR
  have hbound : ∀ N : ℕ,
      ‖poleClearedFirstTraceCountertermScheduledApprox counterterm kappa N
        cayleyExteriorPoint‖ ≤ C :=
    fun N => hC N cayleyExteriorPoint hcenter
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp
    (hkappa.eventually (eventually_ge_atTop 24))
  rintro ⟨B, M₀, hB⟩
  apply not_eventually_bounded_squarefreeHalfDirichletPartialSum_cayleyExteriorPoint
  let K : ℝ := C * ‖squarefreeCarlemanHalfDet cayleyExteriorPoint‖
  refine ⟨K + B, max N₀ M₀, fun N hN => ?_⟩
  have hNkappa : 24 ≤ kappa N := hN₀ N ((le_max_left N₀ M₀).trans hN)
  have hNM : M₀ ≤ N := (le_max_right N₀ M₀).trans hN
  have hfactor := norm_poleFactorSqrtApprox_cayleyExteriorPoint_geometric
    (show 3 ≤ kappa N by omega)
  have hpow : (20 : ℝ) ≤ (5 / 4 : ℝ) ^ (kappa N - 1) := by
    calc
      (20 : ℝ) ≤ (5 / 4 : ℝ) ^ (23 : ℕ) := by norm_num
      _ ≤ (5 / 4 : ℝ) ^ (kappa N - 1) :=
        pow_le_pow_right₀ (by norm_num) (by omega)
  have honeGeom : (1 : ℝ) ≤ (5 / 4 : ℝ) ^ (kappa N - 1) / 20 := by
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 20)]
    simpa using hpow
  have honeFactor : (1 : ℝ) ≤
      ‖poleFactorSqrtApprox (kappa N) cayleyExteriorPoint‖ :=
    honeGeom.trans hfactor
  have hdetpos : 0 < ‖squarefreeCarlemanHalfDet cayleyExteriorPoint‖ :=
    norm_pos_iff.mpr (squarefreeCarlemanHalfDet_ne_zero cayleyExteriorPoint)
  have hsource := hbound N
  have hprod :
      ‖poleFactorSqrtApprox (kappa N) cayleyExteriorPoint‖ *
          ‖squarefreeHalfDirichletPartialSum N cayleyExteriorPoint +
            counterterm N cayleyExteriorPoint‖ ≤ K := by
    rw [poleClearedFirstTraceCountertermScheduledApprox, norm_div, norm_mul] at hsource
    exact (div_le_iff₀ hdetpos).mp hsource
  have hcorrected :
      ‖squarefreeHalfDirichletPartialSum N cayleyExteriorPoint +
        counterterm N cayleyExteriorPoint‖ ≤ K := by
    calc
      _ = 1 * ‖squarefreeHalfDirichletPartialSum N cayleyExteriorPoint +
          counterterm N cayleyExteriorPoint‖ := by ring
      _ ≤ ‖poleFactorSqrtApprox (kappa N) cayleyExteriorPoint‖ *
          ‖squarefreeHalfDirichletPartialSum N cayleyExteriorPoint +
            counterterm N cayleyExteriorPoint‖ :=
        mul_le_mul_of_nonneg_right honeFactor (norm_nonneg _)
      _ ≤ K := hprod
  calc
    ‖squarefreeHalfDirichletPartialSum N cayleyExteriorPoint‖ =
        ‖(squarefreeHalfDirichletPartialSum N cayleyExteriorPoint +
          counterterm N cayleyExteriorPoint) - counterterm N cayleyExteriorPoint‖ := by
      ring_nf
    _ ≤ ‖squarefreeHalfDirichletPartialSum N cayleyExteriorPoint +
          counterterm N cayleyExteriorPoint‖ +
        ‖counterterm N cayleyExteriorPoint‖ := norm_sub_le _ _
    _ ≤ K + B := add_le_add hcorrected (hB N hNM)

/-- A correction tending to zero at `4/7` cannot repair any cofinal Cayley schedule. -/
theorem no_cofinal_locallyBounded_of_counterterm_tendsto_zero_at_cayleyExteriorPoint
    {counterterm : ℕ → ℂ → ℂ} {kappa : ℕ → ℕ}
    (hkappa : Tendsto kappa atTop atTop)
    (hcounterterm :
      Tendsto (fun N => counterterm N cayleyExteriorPoint) atTop (𝓝 0)) :
    ¬ PoleClearedFirstTraceCountertermScheduledLocallyBounded counterterm kappa := by
  intro hloc
  apply (counterterm_not_eventually_bounded_at_cayleyExteriorPoint_of_cofinal_locallyBounded
    hkappa hloc)
  obtain ⟨N₀, hN₀⟩ := (Metric.tendsto_atTop.mp hcounterterm) 1 zero_lt_one
  refine ⟨1, N₀, fun N hN => ?_⟩
  have hdist := hN₀ N hN
  simpa [dist_zero_right] using le_of_lt hdist

end

end RHTower
