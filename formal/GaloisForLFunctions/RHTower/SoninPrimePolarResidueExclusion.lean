import GaloisForLFunctions.RHTower.SoninPrimePolarEulerHead
import GaloisForLFunctions.HTGeometry.ConvexDiffCountableConnected

/-!
# Native Mellin primitives exclude the quantized first-prime residue

An exact Euler-chamber identity for the native source primitive propagates
as a division-free differential equation. At a hypothetical strict-right
zero, continuity then forces the prime-current residue to vanish, whereas
its arithmetic continuation has residue minus a positive integer.

The Euler-chamber identity is supplied by the native source limit. The final
theorem converts finite native cumulative energy to zero exclusion; it does
not claim an unconditional bound for that arithmetic energy.
-/

noncomputable section
open Complex Filter Set Topology
open scoped BigOperators

namespace RHTower

theorem analyticAt_soninSourcePrimeCurrent (b : ℝ) (f : SoninL2)
    {s : ℂ} (hs : 1 / 2 < s.re) (hs1 : s ≠ 1) :
    AnalyticAt ℂ (soninSourcePrimeCurrent b f) s := by
  have hs0 : s ≠ 0 := by
    intro h
    simp only [h, zero_re] at hs
    linarith
  have hpolar : AnalyticAt ℂ (soninPolarHeadCurrent b) s := by
    unfold soninPolarHeadCurrent
    exact (((analyticAt_id.sub analyticAt_const).neg.mul analyticAt_const).cexp.div
      (analyticAt_id.sub analyticAt_const) (sub_ne_zero.mpr hs1)).add
      ((analyticAt_id.neg.mul analyticAt_const).cexp.div analyticAt_id hs0)
  exact (analyticOnNhd_soninSourceMellinPrimitive f s hs).deriv.neg.add hpolar

/-- A physical source with the exact first-prime current identity excludes every strict-right
zeta zero. The contradiction uses the full positive integer multiplicity. -/
theorem riemannHypothesis_of_soninSourcePrimeCurrent
    (b : ℝ) (f : SoninL2)
    (hEuler : ∀ s : ℂ, 1 < s.re →
      soninSourcePrimeCurrent b f s = xiPrimeLogDirichlet s) :
    RiemannHypothesis := by
  let U : Set ℂ := {s : ℂ | 1 / 2 < s.re} \ {1}
  let A : ℂ → ℂ := soninSourcePrimeCurrent b f
  have hUopen : IsOpen U :=
    (isOpen_lt continuous_const Complex.continuous_re).sdiff isClosed_singleton
  have htwo : (2 : ℂ) ∈ U := by norm_num [U]
  have hUpre : IsPreconnected U :=
    GaloisForLFunctions.HTGeometry.isPreconnected_diff_of_countable_of_convex_complex
      (convex_halfSpace_re_gt _) (isOpen_lt continuous_const Complex.continuous_re)
      (countable_singleton 1) htwo
  have hZ : AnalyticOnNhd ℂ riemannZeta U := by
    intro s hs
    exact analyticOn_riemannZeta s hs.2
  have hA : AnalyticOnNhd ℂ A U := by
    intro s hs
    exact analyticAt_soninSourcePrimeCurrent b f hs.1
      (by simpa only [mem_singleton_iff] using hs.2)
  have htail : AnalyticOnNhd ℂ xiPrimeLogHigherValuation U := by
    intro s hs
    exact differentiableOn_xiPrimeLogHigherValuation_halfPlane.analyticAt
      ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs.1)
  let H : ℂ → ℂ := fun s => deriv riemannZeta s +
    (A s + xiPrimeLogHigherValuation s) * riemannZeta s
  have hH : AnalyticOnNhd ℂ H U := by
    intro s hs
    exact (hZ s hs).deriv.add (((hA s hs).add (htail s hs)).mul (hZ s hs))
  have hHev : H =ᶠ[𝓝 (2 : ℂ)] 0 := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (show (1 : ℝ) < (2 : ℂ).re by norm_num)] with s hs
    have hz := riemannZeta_ne_zero_of_one_lt_re hs
    have heq : A s + xiPrimeLogHigherValuation s = infinitePrimeFlux s := by
      rw [show A s = xiPrimeLogDirichlet s from hEuler s hs,
        infinitePrimeFlux_eq_primeLog_add_higherValuation hs]
    change deriv riemannZeta s + (A s + xiPrimeLogHigherValuation s) * riemannZeta s = 0
    rw [heq, infinitePrimeFlux, logDeriv_apply]
    field_simp
    ring
  have hHzero : EqOn H 0 U :=
    hH.eqOn_zero_of_preconnected_of_eventuallyEq_zero hUpre htwo hHev
  rw [riemannHypothesis_iff_riemannZeta_ne_zero_of_half_lt_re]
  intro ρ hρ hz
  have hρU : ρ ∈ U := ⟨hρ, by simpa only [mem_singleton_iff] using riemannZeta_zero_ne_one hz⟩
  have hZnot : ¬ (riemannZeta =ᶠ[𝓝 ρ] 0) := by
    intro heq
    have hzero := hZ.eqOn_zero_of_preconnected_of_eventuallyEq_zero hUpre hρU heq
    exact riemannZeta_ne_zero_of_one_lt_re (s := 2) (by norm_num) (hzero htwo)
  have hZpunct : ∀ᶠ s in 𝓝[≠] ρ, riemannZeta s ≠ 0 :=
    (hZ ρ hρU).eventually_eq_zero_or_eventually_ne_zero.resolve_left hZnot
  have hmatch : xiPrimeLogDirichletContinuation =ᶠ[𝓝[≠] ρ] A := by
    filter_upwards [hZpunct, nhdsWithin_le_nhds (hUopen.mem_nhds hρU)] with s hs hsU
    have hzero : deriv riemannZeta s +
        (A s + xiPrimeLogHigherValuation s) * riemannZeta s = 0 := hHzero hsU
    simp only [xiPrimeLogDirichletContinuation, infinitePrimeFlux, logDeriv_apply]
    field_simp
    linear_combination -hzero
  have hfinite : Tendsto xiPrimeLogDirichletContinuation (𝓝[≠] ρ) (𝓝 (A ρ)) :=
    ((hA ρ hρU).continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr' hmatch.symm
  have hres0 := (tendsto_sub_self_punctured_zero ρ).mul hfinite
  rw [zero_mul] at hres0
  obtain ⟨m, hm, hres⟩ := xiPrimeLogDirichletContinuation_zero_residue hρ hz
  have hm0 : (m : ℂ) = 0 := neg_eq_zero.mp (tendsto_nhds_unique hres hres0)
  have hmNat : m = 0 := by exact_mod_cast hm0
  omega

/-- Finite native cumulative energy forces zero exclusion by the quantized residue contradiction.
The unchanged prime atoms and polar integrals supply every input to the conversion. -/
theorem riemannHypothesis_of_soninPrimePolarGridEnergy
    (hE : Summable soninPrimePolarGridEnergy) : RiemannHypothesis := by
  obtain ⟨φ, hφ, f, hf⟩ :=
    (soninPrimePolarCellSource_cofinal_limit_iff_energy 1 (by norm_num)).mpr hE
  exact riemannHypothesis_of_soninSourcePrimeCurrent (Real.log 2) f
    (fun _ hs => soninSourcePrimeCurrent_eq_primeLog_of_source_limit hφ hf hs)

/-- Any finite quantitative bound on cofinal returns of the actual arithmetic source excludes
strict-right zeros. The size of the finite bound is irrelevant to integer residue exclusion. -/
theorem riemannHypothesis_of_soninPrimePolarGrid_bounded_returns
    (a : ℝ) (ha : 0 < a) (C : ℝ)
    (hbound : ∀ M : ℕ, ∃ N, M ≤ N ∧ ‖soninPrimePolarGridSource a N‖ ^ 2 ≤ C) :
    RiemannHypothesis :=
  riemannHypothesis_of_soninPrimePolarGridEnergy
    ((soninPrimePolarGrid_bounded_returns_iff_energy a ha).mp ⟨C, hbound⟩)

/-- The quantitative input may be imposed directly on the original prime atoms and strong polar
integrals. The already admitted cell correction transfers it to the arithmetic grid. -/
theorem riemannHypothesis_of_soninPrimePolarCellSource_bounded_returns
    (a : ℝ) (ha : 0 < a) (C : ℝ)
    (hbound : ∀ M : ℕ, ∃ N, M ≤ N ∧ ‖soninPrimePolarCellSource a N‖ ^ 2 ≤ C) :
    RiemannHypothesis := by
  let eN : ℕ → SoninL2 := fun N => ∑ n ∈ Finset.range (N + 1), soninPolarGroundCellError a n
  let e : SoninL2 := ∑' n, soninPolarGroundCellError a n
  have he : Tendsto eN atTop (𝓝 e) := by
    simpa only [Function.comp_def] using
      (summable_soninPolarGroundCellError a ha.le).hasSum.tendsto_sum_nat.comp
        (tendsto_add_atTop_nat 1)
  have hsmall : ∀ᶠ N in atTop, ‖eN N‖ < ‖e‖ + 1 :=
    he.norm.eventually (gt_mem_nhds (by linarith : ‖e‖ < ‖e‖ + 1))
  obtain ⟨M₀, hM₀⟩ := eventually_atTop.mp hsmall
  apply riemannHypothesis_of_soninPrimePolarGrid_bounded_returns a ha
    (2 * C + 2 * (‖e‖ + 1) ^ 2)
  intro M
  obtain ⟨N, hN, hC⟩ := hbound (max M M₀)
  refine ⟨N, (le_max_left M M₀).trans hN, ?_⟩
  have heN : ‖eN N‖ ≤ ‖e‖ + 1 := (hM₀ N ((le_max_right M M₀).trans hN)).le
  have hgrid : soninPrimePolarGridSource a N = soninPrimePolarCellSource a N + eN N := by
    rw [soninPrimePolarCellSource_eq_grid_sub_error]
    exact (sub_add_cancel _ _).symm
  rw [hgrid]
  have htri := norm_add_le (soninPrimePolarCellSource a N) (eN N)
  have he0 := norm_nonneg (eN N)
  have hsource0 := norm_nonneg (soninPrimePolarCellSource a N)
  have htri2 := pow_le_pow_left₀
    (norm_nonneg (soninPrimePolarCellSource a N + eN N)) htri 2
  have heN2 := pow_le_pow_left₀ he0 heN 2
  have hq := sq_nonneg (‖soninPrimePolarCellSource a N‖ - ‖eN N‖)
  nlinarith [norm_nonneg (soninPrimePolarCellSource a N + eN N), norm_nonneg e]

end RHTower
