import GaloisForLFunctions.RHTower.XiMassCriticalOutgoingCurrent
import GaloisForLFunctions.RHTower.XiMassPrimeOpenCore

/-!
# Exact outgoing-current form of the mass-shifted prime open core

The absolutely summable bottom Euler atomization and the critical cofinal prime sum have the same
limit. Combining this identification with the Volterra-adjoint law isolates every uniformly bounded
face term and proves that RH is equivalent to one outgoing normalized-Chebyshev current. All
statements are unconditional; the final equivalence marks the remaining source cancellation rather
than assuming it.
-/

open Complex Filter MeasureTheory Set Topology

namespace RHTower

noncomputable section

theorem criticalMellinAtomWeight_cast_eq_lSeriesTerm_half
    {n : ℕ} (hn : n ≠ 0) :
    (criticalMellinAtomWeight n : ℂ) =
      LSeries.term (fun k => (ArithmeticFunction.vonMangoldt k : ℂ)) (1 / 2 : ℂ) n := by
  rw [criticalMellinAtomWeight, LSeries.term_of_ne_zero hn]
  have hncast : (n : ℂ) = (((n : ℝ) : ℝ) : ℂ) := by norm_cast
  have hhalfcast : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by norm_num
  rw [hncast]
  rw [hhalfcast]
  rw [← Complex.ofReal_cpow (Nat.cast_nonneg n) (1 / 2 : ℝ)]
  push_cast
  rw [show (-1 / 2 : ℝ) = -(1 / 2 : ℝ) by ring]
  rw [Real.rpow_neg (Nat.cast_nonneg n)]
  rw [mul_comm]
  rw [Complex.ofReal_inv]
  simp only [div_eq_mul_inv]

theorem xiMassCriticalPrimePartialSource_eq_sum_centered
    (a sigma u H : ℝ) :
    xiMassCriticalPrimePartialSource a sigma u H =
      ∑ k ∈ Finset.Icc 2 ⌊Real.exp H⌋₊,
        xiMassCenteredPrimeAtom a ((sigma : ℂ) + u * I) k := by
  rw [xiMassCriticalPrimePartialSource]
  apply Finset.sum_congr rfl
  intro k hk
  rw [xiMassCenteredPrimeAtom,
    ← criticalMellinAtomWeight_cast_eq_lSeriesTerm_half (by
      have hk2 := (Finset.mem_Icc.mp hk).1
      omega)]

theorem tendsto_xiMassCriticalPrimePartialSource_atTop_tsum_centered
    {a c sigma : ℝ} (hhalf : 1 / 2 < c) (hca : c < a) (hsigma : 0 < sigma)
    (u : ℝ) :
    Tendsto (fun H : ℝ => xiMassCriticalPrimePartialSource a sigma u H) atTop
      (𝓝 (∑' n : ℕ, xiMassCenteredPrimeAtom a ((sigma : ℂ) + u * I) n)) := by
  have htau : 0 < (((sigma : ℂ) + u * I)).re := by
    simpa [Complex.mul_re] using hsigma
  have hsummable := summable_xiMassCenteredPrimeAtom hhalf hca htau
  have hnat : Tendsto
      (fun N : ℕ => ∑ n ∈ Finset.range N,
        xiMassCenteredPrimeAtom a ((sigma : ℂ) + u * I) n)
      atTop (𝓝 (∑' n : ℕ,
        xiMassCenteredPrimeAtom a ((sigma : ℂ) + u * I) n)) :=
    (hsummable.hasSum_iff_tendsto_nat).mp hsummable.hasSum
  have hindex : Tendsto (fun H : ℝ => ⌊Real.exp H⌋₊ + 1) atTop atTop :=
    (tendsto_add_atTop_nat 1).comp
      (tendsto_nat_floor_atTop.comp Real.tendsto_exp_atTop)
  refine (hnat.comp hindex).congr' ?_
  filter_upwards [eventually_ge_atTop (Real.log 2)] with H hH
  rw [xiMassCriticalPrimePartialSource_eq_sum_centered]
  let N : ℕ := ⌊Real.exp H⌋₊
  have hN : 2 ≤ N := by
    apply Nat.le_floor
    calc
      (2 : ℝ) = Real.exp (Real.log 2) :=
        (Real.exp_log (by norm_num : (0 : ℝ) < 2)).symm
      _ ≤ Real.exp H := Real.exp_le_exp.mpr hH
  rw [show Finset.Icc 2 N = Finset.Ico 2 (N + 1) by
    ext k
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega]
  rw [Finset.sum_Ico_eq_sub _ (by omega : 2 ≤ N + 1)]
  have hsmall :
      (∑ k ∈ Finset.range 2,
        xiMassCenteredPrimeAtom a ((sigma : ℂ) + u * I) k) = 0 := by
    have hzero : xiMassCenteredPrimeAtom a ((sigma : ℂ) + u * I) 0 = 0 := by
      rw [xiMassCenteredPrimeAtom, LSeries.term_zero, zero_mul]
    have hone : xiMassCenteredPrimeAtom a ((sigma : ℂ) + u * I) 1 = 0 := by
      rw [xiMassCenteredPrimeAtom, LSeries.term_of_ne_zero one_ne_zero]
      simp [ArithmeticFunction.vonMangoldt_apply_one]
    norm_num [Finset.sum_range_succ, hzero, hone]
  rw [hsmall, sub_zero]
  simp only [Function.comp_apply, N]

theorem xiMassBottomPrimeIntegral_eq_polar_add_completedErrorFlux
    {a c sigma : ℝ} (hhalf : 1 / 2 < c) (hca : c < a) (hsigma : 0 < sigma)
    (u : ℝ) :
    xiMassBottomPrimeIntegral a c ((sigma : ℂ) + u * I) =
      (2 * Real.pi : ℂ) *
          xiMassAnalyticTest a ((sigma : ℂ) + u * I) xiMassArchPole +
        xiMassCompletedErrorFlux a sigma u := by
  have htau : 0 < (((sigma : ℂ) + u * I)).re := by
    simpa [Complex.mul_re] using hsigma
  have hsum := tendsto_xiMassCriticalPrimePartialSource_atTop_tsum_centered
    hhalf hca hsigma u
  have hflux := tendsto_xiMassCriticalPrimePartialSource_atTop
    (lt_trans hhalf hca) hsigma u
  have heq := tendsto_nhds_unique hsum hflux
  rw [xiMassBottomPrimeIntegral,
    integral_xiMassBottomPrimeIntegrand_eq_tsum_centeredAtom hhalf hca htau]
  exact heq

theorem norm_xiMassExpDampedFourier_le
    {a sigma : ℝ} (ha : 0 < a) (hsigma : 0 < sigma) (u : ℝ) :
    ‖xiMassExpDampedFourier a sigma u‖ ≤
      2 * (∫ x : ℝ, Real.exp (-(sigma * |x|))) := by
  let J : ℝ := ∫ x : ℝ, Real.exp (-(sigma * |x|))
  have hleft := (integrableOn_expNegHalf_mul_xiMassFourier ha hsigma u).norm
  have hexp : IntegrableOn (fun h : ℝ => Real.exp ((-1 / 2 : ℝ) * h)) (Ioi 0) :=
    integrableOn_exp_mul_Ioi (show (-1 / 2 : ℝ) < 0 by norm_num) 0
  have hright : IntegrableOn (fun h : ℝ => J * Real.exp ((-1 / 2 : ℝ) * h)) (Ioi 0) :=
    hexp.const_mul J
  have hmono :
      (∫ h in Ioi (0 : ℝ),
        ‖(Real.exp (-h / 2) : ℂ) *
          stripFourier (xiMassAnalyticTest a ((sigma : ℂ) + u * I)) (h : ℂ)‖) ≤
      ∫ h in Ioi (0 : ℝ), J * Real.exp ((-1 / 2 : ℝ) * h) := by
    apply integral_mono_ae hleft hright
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with h hh
    have hF := norm_stripFourier_xiMassAnalyticTest_vertical_le ha hsigma u h
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    calc
      Real.exp (-h / 2) *
          ‖stripFourier (xiMassAnalyticTest a ((sigma : ℂ) + u * I)) (h : ℂ)‖ ≤
        Real.exp (-h / 2) * J :=
          mul_le_mul_of_nonneg_left (by simpa [J] using hF) (Real.exp_nonneg _)
      _ = J * Real.exp ((-1 / 2 : ℝ) * h) := by ring
  calc
    ‖xiMassExpDampedFourier a sigma u‖ ≤
        ∫ h in Ioi (0 : ℝ),
          ‖(Real.exp (-h / 2) : ℂ) *
            stripFourier (xiMassAnalyticTest a ((sigma : ℂ) + u * I)) (h : ℂ)‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ h in Ioi (0 : ℝ), J * Real.exp ((-1 / 2 : ℝ) * h) := hmono
    _ = J * 2 := by
      rw [integral_const_mul,
        integral_exp_mul_Ioi (show (-1 / 2 : ℝ) < 0 by norm_num) 0]
      norm_num
    _ = 2 * (∫ x : ℝ, Real.exp (-(sigma * |x|))) := by simp only [J]; ring

noncomputable def xiMassCriticalOutgoingExplicitFace (a sigma u : ℝ) : ℂ :=
  (2 * Real.pi : ℂ) *
      xiMassAnalyticTest a ((sigma : ℂ) + u * I) xiMassArchPole +
    stripFourier (xiMassAnalyticTest a ((sigma : ℂ) + u * I)) 0 -
    xiMassExpDampedFourier a sigma u

theorem xiMassBottomPrimeIntegral_eq_explicitFace_add_outgoingFlux
    {a c sigma : ℝ} (hhalf : 1 / 2 < c) (hca : c < a) (hsigma : 0 < sigma)
    (u : ℝ) :
    xiMassBottomPrimeIntegral a c ((sigma : ℂ) + u * I) =
      xiMassCriticalOutgoingExplicitFace a sigma u +
        xiMassCriticalOutgoingFlux a sigma u := by
  rw [xiMassBottomPrimeIntegral_eq_polar_add_completedErrorFlux hhalf hca hsigma u,
    xiMassCompletedErrorFlux_eq_criticalOutgoingFlux (lt_trans hhalf hca) hsigma u]
  rw [xiMassCriticalOutgoingExplicitFace]
  ring

theorem norm_xiMassCriticalOutgoingExplicitFace_le
    {a sigma : ℝ} (hhalf : 1 / 2 < a) (hsigma : 0 < sigma) (u : ℝ) :
    ‖xiMassCriticalOutgoingExplicitFace a sigma u‖ ≤
      2 * Real.pi * Real.exp (-sigma * xiMassArchPoleFrequency a) +
        3 * (∫ x : ℝ, Real.exp (-(sigma * |x|))) := by
  let P : ℂ := (2 * Real.pi : ℂ) *
    xiMassAnalyticTest a ((sigma : ℂ) + u * I) xiMassArchPole
  let F0 : ℂ := stripFourier
    (xiMassAnalyticTest a ((sigma : ℂ) + u * I)) 0
  let Q : ℂ := xiMassExpDampedFourier a sigma u
  let J : ℝ := ∫ x : ℝ, Real.exp (-(sigma * |x|))
  have hP : ‖P‖ = 2 * Real.pi * Real.exp (-sigma * xiMassArchPoleFrequency a) := by
    dsimp only [P]
    rw [norm_mul, norm_xiMassAnalyticTest_archPole_eq hhalf]
    simp [Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  have hF0 : ‖F0‖ ≤ J := by
    dsimp only [F0, J]
    simpa only [Complex.ofReal_zero] using
      norm_stripFourier_xiMassAnalyticTest_vertical_le (lt_trans (by norm_num) hhalf)
        hsigma u 0
  have hQ : ‖Q‖ ≤ 2 * J := by
    simpa only [Q, J] using
      norm_xiMassExpDampedFourier_le (lt_trans (by norm_num) hhalf) hsigma u
  calc
    ‖xiMassCriticalOutgoingExplicitFace a sigma u‖ = ‖P + F0 - Q‖ := rfl
    _ ≤ ‖P‖ + ‖F0‖ + ‖Q‖ :=
      (norm_sub_le (P + F0) Q).trans (add_le_add (norm_add_le P F0) le_rfl)
    _ ≤ (2 * Real.pi * Real.exp (-sigma * xiMassArchPoleFrequency a)) + J + 2 * J := by
      exact add_le_add (add_le_add hP.le hF0) hQ
    _ = 2 * Real.pi * Real.exp (-sigma * xiMassArchPoleFrequency a) +
        3 * (∫ x : ℝ, Real.exp (-(sigma * |x|))) := by simp only [J]; ring

def XiMassCriticalOutgoingFluxLineBound (a sigma : ℝ) : Prop :=
  ∃ C : ℝ, ∀ u : ℝ, ‖xiMassCriticalOutgoingFlux a sigma u‖ ≤ C

theorem xiMassBottomPrimeLineBound_iff_criticalOutgoingFluxLineBound
    {a c sigma : ℝ} (hhalf : 1 / 2 < c) (hca : c < a) (hsigma : 0 < sigma) :
    XiMassBottomPrimeLineBound a c sigma ↔
      XiMassCriticalOutgoingFluxLineBound a sigma := by
  let B : ℝ := 2 * Real.pi * Real.exp (-sigma * xiMassArchPoleFrequency a) +
    3 * (∫ x : ℝ, Real.exp (-(sigma * |x|)))
  have hface : ∀ u : ℝ, ‖xiMassCriticalOutgoingExplicitFace a sigma u‖ ≤ B :=
    fun u => norm_xiMassCriticalOutgoingExplicitFace_le (lt_trans hhalf hca) hsigma u
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨C + B, fun u => ?_⟩
    have heq := xiMassBottomPrimeIntegral_eq_explicitFace_add_outgoingFlux
      hhalf hca hsigma u
    have hout : xiMassCriticalOutgoingFlux a sigma u =
        xiMassBottomPrimeIntegral a c ((sigma : ℂ) + u * I) -
          xiMassCriticalOutgoingExplicitFace a sigma u := by
      rw [heq]
      ring
    rw [hout]
    exact (norm_sub_le _ _).trans (add_le_add (hC u) (hface u))
  · rintro ⟨C, hC⟩
    refine ⟨B + C, fun u => ?_⟩
    rw [xiMassBottomPrimeIntegral_eq_explicitFace_add_outgoingFlux
      hhalf hca hsigma u]
    exact (norm_add_le _ _).trans (add_le_add (hface u) (hC u))

theorem riemannHypothesis_iff_xiMassCriticalOutgoingFluxLineBound
    {a c sigma : ℝ} (hhalf : 1 / 2 < c) (hca : c < a) (hsigma : 0 < sigma) :
    RiemannHypothesis ↔ XiMassCriticalOutgoingFluxLineBound a sigma := by
  calc
    RiemannHypothesis ↔ XiMassBottomPrimeLineBound a c sigma :=
      riemannHypothesis_iff_xiMassBottomPrimeLineBound hhalf hca hsigma
    _ ↔ XiMassCriticalOutgoingFluxLineBound a sigma :=
      xiMassBottomPrimeLineBound_iff_criticalOutgoingFluxLineBound hhalf hca hsigma

end

end RHTower
