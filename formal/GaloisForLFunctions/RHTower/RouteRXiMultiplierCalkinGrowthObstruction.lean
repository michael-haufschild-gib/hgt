import GaloisForLFunctions.RHTower.RouteRCrossPrimeStokesCalkinPolarHandoff
import GaloisForLFunctions.RHTower.XiHorizontalStripDecay

/-!
# Route R: reciprocal growth forced on every Xi-multiplier Calkin landing

Suppose the fixed `(2,3)` cross-prime Stokes receiver is represented, modulo a compact
operator, by `XiC z` times an operator-valued source multiplier.  Its explicit Calkin floor
then forces the product

`‖XiC z‖ * ‖sourceMultiplier z‖`

to dominate the normalized reflection-odd curvature.  This has two consequences.

* At a zero of `XiC`, such a factorization forces neutral horizontal grade.
* On every closed horizontal substrip, a nonneutral factorization cannot have a uniformly
  bounded multiplier: exponential decay of `XiC` forces reciprocal growth.

Thus a regular bounded Euler--Gamma multiplier cannot be the missing Route R producer.  Any
surviving source construction must be singular at the Xi divisor, or have at least the forced
reciprocal growth before reaching it.
-/

open Complex Filter Topology

namespace RHTower

noncomputable section

private abbrev RouteRPhysicalOperator :=
  ArchimedeanWeightedL2 →L[ℂ] ArchimedeanWeightedL2

/-- Pointwise quantitative obstruction.  Compact correction cannot reduce the fixed physical
Calkin floor, so a coefficient-faithful Xi multiplier must carry all of it. -/
theorem routeRTwoThreeStokesCalkinFactorization_forces_multiplier_product
    {A : ℝ} (hA : 0 < A) (a : ℝ) (z : ℂ)
    (S K : RouteRPhysicalOperator)
    (hK : IsCompactOperator K)
    (hfactor : routeRTwoThreeStokesSoninCommutator A a = XiC z • S + K) :
    |routeRCrossPrimeStokesOddCurvature 2 3 a| / Real.sqrt 6 ≤
      ‖XiC z‖ * ‖S‖ := by
  calc
    |routeRCrossPrimeStokesOddCurvature 2 3 a| / Real.sqrt 6 ≤
        essentialNorm (routeRTwoThreeStokesSoninCommutator A a) :=
      abs_routeRTwoThreeStokesOddCurvature_div_sqrt_six_le_essentialNorm hA a
    _ ≤ ‖routeRTwoThreeStokesSoninCommutator A a - K‖ :=
      essentialNorm_le _ K hK
    _ = ‖XiC z • S‖ := by rw [hfactor, add_sub_cancel_right]
    _ = ‖XiC z‖ * ‖S‖ := norm_smul _ _

/-- The positive survivor of the obstruction: away from the Xi divisor, every source multiplier
has an explicit reciprocal lower bound. -/
theorem routeRTwoThreeStokesCalkinFactorization_forces_reciprocal_growth
    {A : ℝ} (hA : 0 < A) (a : ℝ) (z : ℂ)
    (S K : RouteRPhysicalOperator)
    (hK : IsCompactOperator K)
    (hfactor : routeRTwoThreeStokesSoninCommutator A a = XiC z • S + K)
    (hz : XiC z ≠ 0) :
    |routeRCrossPrimeStokesOddCurvature 2 3 a| /
        (Real.sqrt 6 * ‖XiC z‖) ≤ ‖S‖ := by
  have hXi : 0 < ‖XiC z‖ := norm_pos_iff.mpr hz
  have hsqrt : 0 < Real.sqrt 6 := Real.sqrt_pos.2 (by norm_num)
  have hproduct :=
    routeRTwoThreeStokesCalkinFactorization_forces_multiplier_product
      hA a z S K hK hfactor
  rw [div_le_iff₀ (mul_pos hsqrt hXi)]
  rw [div_le_iff₀ hsqrt] at hproduct
  calc |routeRCrossPrimeStokesOddCurvature 2 3 a|
      ≤ ‖XiC z‖ * ‖S‖ * Real.sqrt 6 := hproduct
    _ = ‖S‖ * (Real.sqrt 6 * ‖XiC z‖) := by ring

/-- At an actual Xi zero, a compact-corrected coefficient-faithful factorization forces the
horizontal grade to be neutral. -/
theorem routeRTwoThreeStokesCalkinFactorization_at_Xi_zero_forces_neutral
    {A : ℝ} (hA : 0 < A) (a : ℝ) (z : ℂ)
    (S K : RouteRPhysicalOperator)
    (hK : IsCompactOperator K)
    (hz : XiC z = 0)
    (hfactor : routeRTwoThreeStokesSoninCommutator A a = XiC z • S + K) :
    a = 0 := by
  apply (routeRTwoThreeStokesSoninCommutator_isCompactOperator_iff hA a).1
  simpa [hfactor, hz] using hK

/-- A bounded regular Xi multiplier cannot represent a nonneutral fixed Route R receiver modulo
compact operators on a whole horizontal line.  This is the global hostile test for a proposed
pre-divisor Xi-multiplier producer. -/
theorem no_bounded_XiHorizontalMultiplier_compactFactorization
    {A B δ a b : ℝ} (hA : 0 < A) (hB : B < 1) (hδ : 0 < δ)
    (hδstrip : 2 * δ < Real.pi / 2) (hb : |b| ≤ B) (ha : a ≠ 0) :
    ¬ ∃ (S K : ℝ → RouteRPhysicalOperator) (M : ℝ),
        0 ≤ M ∧
        (∀ t : ℝ, ‖S t‖ ≤ M) ∧
        (∀ t : ℝ, IsCompactOperator (K t)) ∧
        (∀ t : ℝ,
          routeRTwoThreeStokesSoninCommutator A a =
            XiC ((t : ℂ) + (b : ℂ) * Complex.I) • S t + K t) := by
  rintro ⟨S, K, M, hM, hS, hK, hfactor⟩
  obtain ⟨C, hC, hXi⟩ :=
    exists_norm_XiC_horizontal_le hB hδ.le hδstrip
  let c : ℝ := |routeRCrossPrimeStokesOddCurvature 2 3 a| / Real.sqrt 6
  have hcurvature : routeRCrossPrimeStokesOddCurvature 2 3 a ≠ 0 :=
    (routeRCrossPrimeStokesOddCurvature_eq_zero_iff
      (p := 2) (q := 3) (by norm_num) (by norm_num) a).not.mpr ha
  have hc : 0 < c :=
    div_pos (abs_pos.mpr hcurvature) (Real.sqrt_pos.2 (by norm_num))
  have hpoint : ∀ t : ℝ,
      c ≤ ‖XiC ((t : ℂ) + (b : ℂ) * Complex.I)‖ * ‖S t‖ := by
    intro t
    exact routeRTwoThreeStokesCalkinFactorization_forces_multiplier_product
      hA a _ (S t) (K t) (hK t) (hfactor t)
  have harg : Tendsto (fun t : ℝ ↦ -(δ * t)) atTop atBot := by
    exact tendsto_neg_atTop_atBot.comp
      (Tendsto.const_mul_atTop hδ tendsto_id)
  have hzero : Tendsto (fun t : ℝ ↦ C * M * Real.exp (-(δ * t)))
      atTop (nhds 0) := by
    simpa using (Real.tendsto_exp_atBot.comp harg).const_mul (C * M)
  have hc0 : c ≤ 0 := by
    apply ge_of_tendsto hzero
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    have hXi' := hXi t b hb
    rw [abs_of_nonneg ht] at hXi'
    calc
      c ≤ ‖XiC ((t : ℂ) + (b : ℂ) * Complex.I)‖ * ‖S t‖ := hpoint t
      _ ≤ (C * Real.exp (-(δ * t))) * M :=
        mul_le_mul hXi' (hS t) (norm_nonneg _) (mul_nonneg hC (Real.exp_pos _).le)
      _ = C * M * Real.exp (-(δ * t)) := by ring
  exact (not_le_of_gt hc) hc0

/-- Divisor-specialized source-to-Xi Calkin landing closes the existing explicit Route R RH
endpoint.  All remaining mathematical content is construction of this factorization from the
pre-divisor Euler--Gamma--Stokes source. -/
theorem riemannHypothesis_of_routeRTwoThree_XiCalkinFactorization
    {A : ℝ} (hA : 0 < A)
    (hfactor : ∀ rho : XiDivisorSupport,
      ∃ S K : RouteRPhysicalOperator,
        IsCompactOperator K ∧
        routeRTwoThreeStokesSoninCommutator A
            (primeDepthBVWoldXiCenteredRate rho) =
          XiC (xiSpectralPointSupport rho) • S + K) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_routeRTwoThreeStokesSoninCommutator_compact hA
  intro rho
  obtain ⟨S, K, hK, hlanding⟩ := hfactor rho
  have hXi : XiC (xiSpectralPointSupport rho) = 0 :=
    XiC_xiSpectralPointSupport_eq_zero rho
  simpa [hlanding, hXi] using hK

end

end RHTower
