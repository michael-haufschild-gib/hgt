import GaloisForLFunctions.RHTower.SquarefreeConvolutionHalfIteratedLogSchedule
import GaloisForLFunctions.RHTower.DirichletUniformAbel
import GaloisForLFunctions.RHTower.DirichletLSeriesBridge

/-!
# Universal no-go for raw scheduled squarefree-half truncations

The canonical convolution-half Dirichlet partial sums cannot be eventually bounded at the fixed
point `s = 6/11`.  Otherwise Abel summation would continue their Dirichlet series holomorphically
to `Re s > 2/3`.  On `Re s > 1` its square is `zeta(s) / zeta(2s)`, so multiplying by
`(s - 1) zeta(2s)` and using analytic uniqueness would force the residue unit
`(s - 1) zeta(s)` to vanish at `s = 1`, contradicting its value `1`.

Every cofinal Cayley schedule eventually has degree at least `24`.  The certified base-five lower
bound for its pole-factor approximant then turns local boundedness of the scheduled product into
eventual boundedness of the Dirichlet partial sums.  Hence no cofinal raw schedule is locally
bounded.  A viable continuation scheme must change the regularization rather than slow the degree
schedule further.
-/

open Complex Filter Metric Set Topology

namespace RHTower

open GaloisForLFunctions
open GaloisForLFunctions.RHTower

noncomputable section

/-- Zero-indexed coefficient shift used by the corpus's conditional Dirichlet-series API. -/
def squarefreeConvolutionHalfShift (n : ℕ) : ℂ :=
  squarefreeConvolutionHalf (n + 1)

/-- Shifted ordinary Dirichlet partial sums are the canonical `LSeries` partial sums. -/
theorem dirichletPartialSum_squarefreeConvolutionHalfShift (N : ℕ) (s : ℂ) :
    dirichletPartialSum squarefreeConvolutionHalfShift N s =
      squarefreeHalfDirichletPartialSum (N + 1) s := by
  change dirichletPartialSum (fun n => squarefreeConvolutionHalf (n + 1)) N s = _
  rw [dirichletPartialSum_eq_sum_term]
  unfold squarefreeHalfDirichletPartialSum
  rw [show Finset.range (N + 1) = insert 0 (Finset.Icc 1 N) by
    ext n
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
    omega]
  rw [Finset.sum_insert (by simp), LSeries.term_zero, zero_add]

/-- The raw half-series partial sums are unbounded at `s = 6/11`.

The proof is qualitative: boundedness plus Abel summation would produce a holomorphic square root
across the simple zeta pole at one. -/
theorem not_exists_bound_squarefreeHalfDirichletPartialSum_boundaryExteriorPoint :
    ¬ ∃ C : ℝ, ∀ N : ℕ,
      ‖squarefreeHalfDirichletPartialSum N boundaryExteriorPoint‖ ≤ C := by
  rintro ⟨C, hC⟩
  have hshiftBound : ∀ N : ℕ,
      ‖dirichletPartialSum squarefreeConvolutionHalfShift N boundaryExteriorPoint‖ ≤ C := by
    intro N
    rw [dirichletPartialSum_squarefreeConvolutionHalfShift]
    exact hC (N + 1)
  have hconv : DirichletConvergesAt squarefreeConvolutionHalfShift (2 / 3 : ℂ) := by
    have h := tendsto_dirichlet_partialSum_of_bounded hshiftBound
      (s := (2 / 3 : ℂ) - boundaryExteriorPoint) (by norm_num [boundaryExteriorPoint])
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
    norm_num [boundaryExteriorPoint]
  let F : ℂ → ℂ := dirichletSum squarefreeConvolutionHalfShift
  let U : Set ℂ := {s : ℂ | (2 / 3 : ℝ) < s.re}
  have hFdiff : DifferentiableOn ℂ F U := by
    simpa [F, U] using differentiableOn_dirichletSum hconv
  have hFana : AnalyticOnNhd ℂ F U :=
    hFdiff.analyticOnNhd (isOpen_lt continuous_const Complex.continuous_re)
  have hFeq : EqOn F (LSeries squarefreeConvolutionHalf) farHalf := by
    intro s hs
    have hs23 : (2 / 3 : ℝ) < s.re := by
      have := mem_farHalf.mp hs
      norm_num at *
      linarith
    have hconvS : DirichletConvergesAt squarefreeConvolutionHalfShift s :=
      tendsto_dirichlet_partialSum_of_re_lt hconv (by simpa using hs23)
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
      change (2 / 3 : ℝ) < s.re at hs
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
    exact (convex_halfSpace_re_gt (2 / 3 : ℝ)).isPreconnected
  have honeU : (1 : ℂ) ∈ U := by norm_num [U]
  have hfreq : ∃ᶠ s in 𝓝[≠] (2 : ℂ), H s = 0 := by
    have hfar : ∀ᶠ s in 𝓝 (2 : ℂ), s ∈ farHalf :=
      isOpen_farHalf.mem_nhds two_mem_farHalf
    have hzero : ∀ᶠ s in 𝓝 (2 : ℂ), H s = 0 := hfar.mono (fun s hs => hHzeroFar hs)
    exact (Filter.Eventually.filter_mono nhdsWithin_le_nhds hzero).frequently
  have htwoU : (2 : ℂ) ∈ U := by norm_num [U]
  have hzeroAll := hHana.eqOn_zero_of_preconnected_of_frequently_eq_zero
    hUpre htwoU hfreq
  have hzero := hzeroAll honeU
  dsimp [H] at hzero
  rw [zetaResidueUnit_one] at hzero
  norm_num at hzero

/-- Strong form: the raw half-series partial sums have no bounded tail at `s = 6/11`. -/
theorem not_eventually_bounded_squarefreeHalfDirichletPartialSum_boundaryExteriorPoint :
    ¬ ∃ C : ℝ, ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ‖squarefreeHalfDirichletPartialSum N boundaryExteriorPoint‖ ≤ C := by
  rintro ⟨C, N₀, hC⟩
  apply not_exists_bound_squarefreeHalfDirichletPartialSum_boundaryExteriorPoint
  let H : ℝ := ∑ N ∈ Finset.range N₀,
    ‖squarefreeHalfDirichletPartialSum N boundaryExteriorPoint‖
  refine ⟨max C H, fun N => ?_⟩
  by_cases hN : N₀ ≤ N
  · exact (hC N hN).trans (le_max_left _ _)
  · have hmem : N ∈ Finset.range N₀ := Finset.mem_range.mpr (by omega)
    have hterm : ‖squarefreeHalfDirichletPartialSum N boundaryExteriorPoint‖ ≤ H := by
      dsimp [H]
      exact Finset.single_le_sum (fun i _ => norm_nonneg
        (squarefreeHalfDirichletPartialSum i boundaryExteriorPoint)) hmem
    exact hterm.trans (le_max_right _ _)

/-- No cofinal Cayley-degree schedule makes the raw pole-cleared source approximants locally
bounded on the strict right half-plane. -/
theorem no_cofinal_poleClearedFirstTraceScheduledLocallyBounded
    {kappa : ℕ → ℕ} (hkappa : Tendsto kappa atTop atTop) :
    ¬ PoleClearedFirstTraceScheduledLocallyBounded kappa := by
  intro hloc
  obtain ⟨R, hR, hball, C, hC⟩ :=
    hloc boundaryExteriorPoint boundaryExteriorPoint_mem_rightHalf
  have hcenter : boundaryExteriorPoint ∈ ball boundaryExteriorPoint R := mem_ball_self hR
  have hbound : ∀ N : ℕ,
      ‖poleClearedFirstTraceScheduledApprox kappa N boundaryExteriorPoint‖ ≤ C :=
    fun N => hC N boundaryExteriorPoint hcenter
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp
    (hkappa.eventually (eventually_ge_atTop 24))
  let K : ℝ := C * ‖squarefreeCarlemanHalfDet boundaryExteriorPoint‖
  have hpartial : ∀ N : ℕ, N₀ ≤ N →
      ‖squarefreeHalfDirichletPartialSum N boundaryExteriorPoint‖ ≤ K := by
    intro N hN
    have hfactor := norm_poleFactorSqrtApprox_boundaryExteriorPoint_five_pow (hN₀ N hN)
    have hdetpos : 0 < ‖squarefreeCarlemanHalfDet boundaryExteriorPoint‖ :=
      norm_pos_iff.mpr (squarefreeCarlemanHalfDet_ne_zero boundaryExteriorPoint)
    have hsource := hbound N
    have hprod :
        ‖poleFactorSqrtApprox (kappa N) boundaryExteriorPoint‖ *
            ‖squarefreeHalfDirichletPartialSum N boundaryExteriorPoint‖ ≤ K := by
      rw [poleClearedFirstTraceScheduledApprox, norm_div, norm_mul] at hsource
      exact (div_le_iff₀ hdetpos).mp hsource
    have hone : (1 : ℝ) ≤ (5 : ℝ) ^ (kappa N - 24) := one_le_pow₀ (by norm_num)
    calc
      ‖squarefreeHalfDirichletPartialSum N boundaryExteriorPoint‖ =
          1 * ‖squarefreeHalfDirichletPartialSum N boundaryExteriorPoint‖ := by ring
      _ ≤ (5 : ℝ) ^ (kappa N - 24) *
          ‖squarefreeHalfDirichletPartialSum N boundaryExteriorPoint‖ :=
        mul_le_mul_of_nonneg_right hone (norm_nonneg _)
      _ ≤ ‖poleFactorSqrtApprox (kappa N) boundaryExteriorPoint‖ *
          ‖squarefreeHalfDirichletPartialSum N boundaryExteriorPoint‖ :=
        mul_le_mul_of_nonneg_right hfactor (norm_nonneg _)
      _ ≤ K := hprod
  exact not_eventually_bounded_squarefreeHalfDirichletPartialSum_boundaryExteriorPoint
    ⟨K, N₀, hpartial⟩

/-- The formerly surviving iterated-log schedule is not locally bounded. -/
theorem not_iteratedLogarithmicCayleySchedule_locallyBounded :
    ¬ PoleClearedFirstTraceScheduledLocallyBounded
      iteratedLogarithmicCayleySchedule :=
  no_cofinal_poleClearedFirstTraceScheduledLocallyBounded
    tendsto_iteratedLogarithmicCayleySchedule_atTop

end

end RHTower
