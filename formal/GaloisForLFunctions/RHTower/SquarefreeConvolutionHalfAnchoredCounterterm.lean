import GaloisForLFunctions.RHTower.SquarefreeConvolutionHalfCountertermNecessity

/-!
# An explicit source-faithful singular counterterm

The rank-one separator `exp(N(6/11-s))` decays compact-open on `Re s > 1` and equals one at the
certified obstruction point.  Scaling it by the negative raw value there gives an entire
counterterm which preserves the Euler germ and cancels every corrected approximant exactly at
`s = 6/11`.  Its amplitude and the counterterm family itself are necessarily unbounded there.

This repairs the point witness without asserting local boundedness of the corrected family.  The
remaining question is whether a source-defined singular counterterm can control its transition
layer on the full strict right half-plane.
-/

open Complex Filter Metric Set Topology

namespace RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

/-- Entire separator equal to one at `s = 6/11` and exponentially decaying to its right. -/
def boundaryExponentialSeparator (N : ℕ) (s : ℂ) : ℂ :=
  Complex.exp ((N : ℂ) * (boundaryExteriorPoint - s))

theorem norm_boundaryExponentialSeparator (N : ℕ) (s : ℂ) :
    ‖boundaryExponentialSeparator N s‖ =
      Real.exp ((N : ℝ) * ((6 / 11 : ℝ) - s.re)) := by
  rw [boundaryExponentialSeparator, Complex.norm_exp]
  simp [boundaryExteriorPoint]

theorem analytic_boundaryExponentialSeparator (N : ℕ) :
    AnalyticOnNhd ℂ (boundaryExponentialSeparator N) Set.univ := by
  intro s _
  exact ((analyticAt_const.mul (analyticAt_const.sub analyticAt_id))).cexp

/-- Crude term bound used only to dominate the anchored amplitude by a polynomial. -/
theorem norm_squarefreeConvolutionHalf_boundaryTerm_le (n : ℕ) :
    ‖LSeries.term squarefreeConvolutionHalf boundaryExteriorPoint n‖ ≤ (n : ℝ) := by
  by_cases hn : n = 0
  · subst n
    simp [LSeries.term_zero]
  rw [LSeries.norm_term_eq, if_neg hn]
  have hcoeff : ‖squarefreeConvolutionHalf n‖ ≤ (n : ℝ) := by
    exact (norm_squarefreeConvolutionHalf_le_card_divisors hn).trans
      (by exact_mod_cast Nat.card_divisors_le_self n)
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hn)
  have hden : 1 ≤ (n : ℝ) ^ (6 / 11 : ℝ) :=
    Real.one_le_rpow hn1 (by norm_num)
  have hdenpos : 0 < (n : ℝ) ^ (6 / 11 : ℝ) :=
    Real.rpow_pos_of_pos (lt_of_lt_of_le zero_lt_one hn1) _
  rw [show boundaryExteriorPoint.re = (6 / 11 : ℝ) by norm_num [boundaryExteriorPoint]]
  calc
    ‖squarefreeConvolutionHalf n‖ / (n : ℝ) ^ (6 / 11 : ℝ) ≤
        (n : ℝ) / (n : ℝ) ^ (6 / 11 : ℝ) :=
      div_le_div_of_nonneg_right hcoeff hdenpos.le
    _ ≤ (n : ℝ) := (div_le_iff₀ hdenpos).2 (by nlinarith)

theorem norm_squarefreeHalfDirichletPartialSum_boundary_le_sq (N : ℕ) :
    ‖squarefreeHalfDirichletPartialSum N boundaryExteriorPoint‖ ≤ (N : ℝ) ^ 2 := by
  rw [squarefreeHalfDirichletPartialSum]
  calc
    ‖∑ n ∈ Finset.range N, LSeries.term squarefreeConvolutionHalf boundaryExteriorPoint n‖ ≤
        ∑ n ∈ Finset.range N,
          ‖LSeries.term squarefreeConvolutionHalf boundaryExteriorPoint n‖ :=
      norm_sum_le _ _
    _ ≤ ∑ n ∈ Finset.range N, (n : ℝ) :=
      Finset.sum_le_sum fun n _ => norm_squarefreeConvolutionHalf_boundaryTerm_le n
    _ ≤ ∑ _n ∈ Finset.range N, (N : ℝ) :=
      Finset.sum_le_sum fun n hn => by
        exact_mod_cast (Finset.mem_range.mp hn).le
    _ = (N : ℝ) ^ 2 := by simp [pow_two]

/-- Rank-one entire counterterm cancelling the raw arithmetic value at the certified exterior
point while decaying exponentially to the right. -/
def boundaryAnchoredCounterterm (N : ℕ) (s : ℂ) : ℂ :=
  -squarefreeHalfDirichletPartialSum N boundaryExteriorPoint *
    boundaryExponentialSeparator N s

theorem analyticOnNhd_boundaryAnchoredCounterterm (N : ℕ) :
    AnalyticOnNhd ℂ (boundaryAnchoredCounterterm N) rightHalf := by
  exact (analyticOnNhd_const.mul
    ((analytic_boundaryExponentialSeparator N).mono (Set.subset_univ _)))

@[simp] theorem boundaryExponentialSeparator_at_boundary (N : ℕ) :
    boundaryExponentialSeparator N boundaryExteriorPoint = 1 := by
  simp [boundaryExponentialSeparator]

@[simp] theorem boundaryAnchoredCounterterm_at_boundary (N : ℕ) :
    boundaryAnchoredCounterterm N boundaryExteriorPoint =
      -squarefreeHalfDirichletPartialSum N boundaryExteriorPoint := by
  simp [boundaryAnchoredCounterterm]

theorem boundaryAnchoredCounterterm_corrected_value (N : ℕ) :
    squarefreeHalfDirichletPartialSum N boundaryExteriorPoint +
      boundaryAnchoredCounterterm N boundaryExteriorPoint = 0 := by
  simp

theorem not_eventually_bounded_boundaryAnchoredCounterterm_at_boundary :
    ¬ ∃ B : ℝ, ∃ M₀ : ℕ, ∀ N : ℕ, M₀ ≤ N →
      ‖boundaryAnchoredCounterterm N boundaryExteriorPoint‖ ≤ B := by
  apply counterterm_not_eventually_bounded_of_corrected_eventually_bounded
  exact ⟨0, 0, fun N _ => by simp⟩

/-- The anchored correction disappears compact-open throughout the Euler chamber. -/
theorem tendstoLocallyUniformlyOn_boundaryAnchoredCounterterm_farHalf :
    TendstoLocallyUniformlyOn boundaryAnchoredCounterterm (fun _ => 0) atTop farHalf := by
  rw [Metric.tendstoLocallyUniformlyOn_iff]
  intro ε hε x hx
  let δ : ℝ := (x.re - 1) / 2
  have hδ : 0 < δ := by
    dsimp [δ]
    have := mem_farHalf.mp hx
    linarith
  let t : Set ℂ := {y | 1 + δ < y.re}
  have hxt : x ∈ t := by
    change 1 + δ < x.re
    dsimp [δ]
    have := mem_farHalf.mp hx
    linarith
  have ht : t ∈ 𝓝[farHalf] x := by
    apply mem_nhdsWithin_of_mem_nhds
    exact (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hxt
  refine ⟨t, ht, ?_⟩
  let a : ℝ := 5 / 11 + δ
  have ha : 0 < a := by dsimp [a]; linarith
  have hseq : Tendsto
      (fun N : ℕ => (N : ℝ) ^ 2 * Real.exp (-a * (N : ℝ))) atTop (𝓝 0) := by
    convert (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 2 a ha).comp
        (tendsto_natCast_atTop_atTop (R := ℝ)) using 1
    ext N
    simp only [Function.comp_apply, Real.rpow_two]
  obtain ⟨N₀, hN₀⟩ := (Metric.tendsto_atTop.mp hseq) ε hε
  exact Filter.eventually_atTop.2 ⟨N₀, fun N hN y hy => by
    have hyre : 1 + δ < y.re := hy
    have hexpExponent :
        (N : ℝ) * ((6 / 11 : ℝ) - y.re) ≤ -a * (N : ℝ) := by
      have hNnonneg : (0 : ℝ) ≤ N := by positivity
      dsimp [a]
      nlinarith
    have hseqLt : (N : ℝ) ^ 2 * Real.exp (-a * (N : ℝ)) < ε := by
      have hdist := hN₀ N hN
      simpa [Real.dist_eq, abs_of_nonneg (mul_nonneg (sq_nonneg _) (Real.exp_pos _).le)]
        using hdist
    calc
      dist 0 (boundaryAnchoredCounterterm N y) =
          ‖squarefreeHalfDirichletPartialSum N boundaryExteriorPoint‖ *
            ‖boundaryExponentialSeparator N y‖ := by
        simp [boundaryAnchoredCounterterm]
      _ ≤ (N : ℝ) ^ 2 * ‖boundaryExponentialSeparator N y‖ :=
        mul_le_mul_of_nonneg_right
          (norm_squarefreeHalfDirichletPartialSum_boundary_le_sq N) (norm_nonneg _)
      _ = (N : ℝ) ^ 2 *
          Real.exp ((N : ℝ) * ((6 / 11 : ℝ) - y.re)) := by
        rw [norm_boundaryExponentialSeparator]
      _ ≤ (N : ℝ) ^ 2 * Real.exp (-a * (N : ℝ)) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexpExponent) (sq_nonneg _)
      _ < ε := hseqLt⟩

theorem boundaryAnchoredCounterterm_admissible :
    SquarefreeHalfCountertermAdmissible boundaryAnchoredCounterterm :=
  ⟨analyticOnNhd_boundaryAnchoredCounterterm,
    tendstoLocallyUniformlyOn_boundaryAnchoredCounterterm_farHalf⟩

/-- The counterterm itself is necessarily non-normal at its anchor. -/
theorem not_boundaryAnchoredCounterterm_locallyBounded_at_boundary :
    ¬ ∃ R : ℝ, 0 < R ∧ ∃ C : ℝ, ∀ N : ℕ, ∀ s ∈ ball boundaryExteriorPoint R,
      ‖boundaryAnchoredCounterterm N s‖ ≤ C := by
  rintro ⟨R, hR, C, hC⟩
  apply not_eventually_bounded_boundaryAnchoredCounterterm_at_boundary
  exact ⟨C, 0, fun N _ => hC N boundaryExteriorPoint (mem_ball_self hR)⟩

/-- Despite its singular amplitude, the corrected scheduled value vanishes exactly at the old
obstruction point for every degree schedule. -/
@[simp] theorem poleClearedFirstTrace_boundaryAnchoredCounterterm_at_boundary
    (kappa : ℕ → ℕ) (N : ℕ) :
    poleClearedFirstTraceCountertermScheduledApprox
      boundaryAnchoredCounterterm kappa N boundaryExteriorPoint = 0 := by
  simp [poleClearedFirstTraceCountertermScheduledApprox]

end

end RHTower
