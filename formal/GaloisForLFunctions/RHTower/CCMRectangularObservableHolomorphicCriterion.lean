import GaloisForLFunctions.RHTower.CCMRectangularObservablePoleTomography

/-!
# A holomorphic observable-tail criterion for RH

This file removes the internally constructed meromorphic continuation from the hypothesis.  It
asks for an independent holomorphic function on `Re s > 1` that agrees, on some far-right
half-plane, with the ordinary Dirichlet series of one fixed-width observable rectangular Weil
tail.  Analytic continuation then forces the Xi-cancelled carrier to acquire the full Xi zero
order.  At an off-critical zero of multiplicity `m`, however, that carrier has exact order
`m - 1`.  Hence such a holomorphic lift excludes every right Xi zero and proves RH.

The coefficient sequence is still the zero-side Weil polarization in the present Lean corpus.
Making the hypothesis wholly prime--Gamma source-side requires the separate explicit-formula
transport for the rectangular two-edge test.
-/

open Complex Filter Function Set

namespace RHTower

noncomputable section

/-- An independent holomorphic continuation of one observable rectangular Weil tail.  Agreement
is required only on some far-right half-plane, where the ordinary Dirichlet series converges. -/
def XiRectangularWeilTailHolomorphicContinuation (L : ℝ) (N : ℕ) : Prop :=
  ∃ F : ℂ → ℂ,
    AnalyticOnNhd ℂ F {s : ℂ | 1 < s.re} ∧
      ∃ sigma0 : ℝ, 1 < sigma0 ∧
        ∀ s : ℂ, sigma0 < s.re →
          F s = LSeries (xiRectangularWeilTailCoefficient L N) s

/-- A holomorphic lift of one fixed-width observable rectangular Weil tail excludes all
off-critical Xi zeros and therefore proves RH. -/
theorem riemannHypothesis_of_xiRectangularWeilTailHolomorphicContinuation
    {L : ℝ} (hL : 0 < L) {N : ℕ}
    (hN : ∀ n : ℕ, N ≤ n → 1 ≤ n ∧ L ≤ Real.log n / 2)
    (hlift : XiRectangularWeilTailHolomorphicContinuation L N) :
    RiemannHypothesis := by
  by_contra hRH
  have hne : Nonempty XiRightZeroCopy :=
    nonempty_xiRightZeroCopy_of_not_riemannHypothesis hRH
  let q : XiRightZeroCopy := Classical.choice hne
  obtain ⟨F, hF, sigma0, hsigma0, hmatch⟩ := hlift
  let U : Set ℂ := {s : ℂ | 1 < s.re}
  have hUopen : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hUpre : IsPreconnected U := (convex_halfSpace_re_gt 1).isPreconnected
  let delta : ℝ := xiRightTransverseSup
  have hdelta0 : 0 ≤ delta := (xiRightTransverseSup_pos hne).le
  have hupper : ∀ r : XiRightZeroCopy, (xiRightCenteredZero r).re ≤ delta :=
    xiRightCenteredZero_re_le_sup
  let correction : ℂ → ℂ := fun s =>
    -xiRectangularLandauPrefixSeries L 0 N s +
      LSeries (xiRectangularWeilRemainderCoefficient L N) s
  let A : ℂ → ℂ := fun s =>
    (2 : ℂ)⁻¹ * (F s - correction s)
  have hcorrection : AnalyticOnNhd ℂ correction U := by
    intro s hs
    exact analyticAt_xiRectangularWeilTailCorrection hN hs
  have hA : AnalyticOnNhd ℂ A U := by
    intro s hs
    exact analyticAt_const.mul ((hF s hs).sub (hcorrection s hs))
  have hcancel : AnalyticOnNhd ℂ (xiRectangularCancelledSeries L) U :=
    (differentiableOn_xiRectangularCancelledSeries_rightOne L).analyticOnNhd hUopen
  have hxi : AnalyticOnNhd ℂ (fun s : ℂ => xi (s - 1 / 2)) U := by
    intro s _
    exact (xi_analyticOnNhd_univ _ (Set.mem_univ _)).comp
      (analyticAt_id.sub analyticAt_const)
  have hprod : AnalyticOnNhd ℂ
      ((fun s : ℂ => xi (s - 1 / 2)) * A) U := hxi.mul hA
  let T : ℝ := max sigma0 (1 + delta)
  let z0 : ℂ := (T + 1 : ℝ)
  have hz0U : z0 ∈ U := by
    change 1 < T + 1
    have : 1 < T := lt_of_lt_of_le hsigma0 (le_max_left _ _)
    linarith
  have hevent : xiRectangularCancelledSeries L =ᶠ[nhds z0]
      ((fun s : ℂ => xi (s - 1 / 2)) * A) := by
    have hz0V : T < z0.re := by
      change T < T + 1
      linarith
    have hVopen : IsOpen {s : ℂ | T < s.re} :=
      isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [hVopen.mem_nhds hz0V] with s hs
    have hsigma : sigma0 < s.re := (le_max_left _ _).trans_lt hs
    have hsdelta : 1 + delta < s.re := (le_max_right _ _).trans_lt hs
    have hs1 : 1 < s.re := by linarith
    have hseries := LSeries_xiRectangularWeilTailCoefficient_eq_continuation
      hN hdelta0 hupper hsdelta
    have hFs : F s = xiRectangularWeilTailContinuation L N s :=
      (hmatch s hsigma).trans hseries
    have hAs : A s = xiRectangularRightDirichletContinuation L s := by
      dsimp only [A]
      rw [hFs]
      simp only [xiRectangularWeilTailContinuation, correction]
      ring
    have hxi0 : xi (s - 1 / 2) ≠ 0 := by
      intro hzero
      obtain ⟨r, hr⟩ :=
        exists_xiRightZeroCopy_shiftedPole_eq_of_xi_shifted_eq_zero hs1 hzero
      have hre := congrArg Complex.re hr
      rw [xiRightShiftedPole, Complex.add_re, Complex.one_re] at hre
      linarith [hupper r]
    change xiRectangularCancelledSeries L s = xi (s - 1 / 2) * A s
    rw [hAs]
    unfold xiRectangularRightDirichletContinuation
    have hxi0' : xi ((s * 2 - 1) / 2) ≠ 0 := by
      have harg : (s * 2 - 1) / 2 = s - 1 / 2 := by ring
      rw [harg]
      exact hxi0
    field_simp [hxi0, hxi0']
  have heqOn : EqOn (xiRectangularCancelledSeries L)
      ((fun s : ℂ => xi (s - 1 / 2)) * A) U :=
    hcancel.eqOn_of_preconnected_of_eventuallyEq hprod hUpre hz0U hevent
  have hpU : xiRightShiftedPole q ∈ U := by
    change 1 < (xiRightShiftedPole q).re
    rw [xiRightShiftedPole, Complex.add_re, Complex.one_re]
    linarith [xiRightCenteredZero_re_pos q]
  have hpEvent : xiRectangularCancelledSeries L =ᶠ[nhds (xiRightShiftedPole q)]
      ((fun s : ℂ => xi (s - 1 / 2)) * A) := by
    filter_upwards [hUopen.mem_nhds hpU] with s hs
    exact heqOn hs
  have horders := analyticOrderAt_congr hpEvent
  have hprodLower : (xiRightMultiplicity q : ℕ∞) ≤
      analyticOrderAt (((fun s : ℂ => xi (s - 1 / 2)) * A))
        (xiRightShiftedPole q) := by
    rw [analyticOrderAt_mul (hxi _ hpU) (hA _ hpU),
      xi_shifted_half_order]
    exact le_add_right le_rfl
  rw [xiRectangularCancelledSeries_order hL q] at horders
  rw [← horders] at hprodLower
  have hm : 0 < xiRightMultiplicity q := xiRightMultiplicity_pos q
  have hltNat : xiRightMultiplicity q - 1 < xiRightMultiplicity q :=
    Nat.sub_one_lt (Nat.ne_of_gt hm)
  have hlt : (xiRightMultiplicity q - 1 : ℕ∞) <
      (xiRightMultiplicity q : ℕ∞) := by exact_mod_cast hltNat
  exact (not_lt_of_ge hprodLower) hlt

/-- RH makes the canonical observable-tail continuation holomorphic on `Re s > 1`.  With no
right Xi divisor, the far-right Dirichlet-series identity therefore supplies the independent
holomorphic lift required by the criterion. -/
theorem xiRectangularWeilTailHolomorphicContinuation_of_riemannHypothesis
    {L : ℝ} (hL : 0 < L) {N : ℕ}
    (hN : ∀ n : ℕ, N ≤ n → 1 ≤ n ∧ L ≤ Real.log n / 2)
    (hRH : RiemannHypothesis) :
    XiRectangularWeilTailHolomorphicContinuation L N := by
  have hupper : ∀ q : XiRightZeroCopy, (xiRightCenteredZero q).re ≤ 0 := by
    intro q
    have hzero : xi (q.1.1 : ℂ) = 0 :=
      xi_eq_zero_of_mem_divisor_support q.1.1
    have hright : (q.1.1 : ℂ) ∈ rightHalf := by
      rw [mem_rightHalf]
      have hq := q.2
      rw [I_mul_xiSpectralPoint] at hq
      simp only [Complex.sub_re] at hq
      norm_num at hq ⊢
      linarith
    exact False.elim ((rh_iff_xi_ne_zero_right.mp hRH)
      (q.1.1 : ℂ) hright hzero)
  refine ⟨xiRectangularWeilTailContinuation L N, ?_, 2, by norm_num, ?_⟩
  · intro s hs
    exact (riemannHypothesis_iff_observableTailContinuation_analytic_rightOne hL hN).mp
      hRH s hs
  · intro s hs
    exact (LSeries_xiRectangularWeilTailCoefficient_eq_continuation
      hN (delta := 0) (by norm_num) hupper (by linarith)).symm

/-- **Exact observable-holomorphic RH law.**  For every admissible fixed-width tail, the named
holomorphic-continuation interface is precisely equivalent to RH. -/
theorem xiRectangularWeilTailHolomorphicContinuation_iff_riemannHypothesis
    {L : ℝ} (hL : 0 < L) {N : ℕ}
    (hN : ∀ n : ℕ, N ≤ n → 1 ≤ n ∧ L ≤ Real.log n / 2) :
    XiRectangularWeilTailHolomorphicContinuation L N ↔ RiemannHypothesis :=
  ⟨riemannHypothesis_of_xiRectangularWeilTailHolomorphicContinuation hL hN,
    xiRectangularWeilTailHolomorphicContinuation_of_riemannHypothesis hL hN⟩

end

end RHTower
