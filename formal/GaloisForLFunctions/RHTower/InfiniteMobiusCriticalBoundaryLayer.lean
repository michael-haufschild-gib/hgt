import GaloisForLFunctions.RHTower.InfiniteMobiusCriticalLaplaceResponse

/-!
# Positive/signed critical boundary layer of the all-prime Möbius channel

The normalized squarefree mass and the signed Möbius shift occupy the same moving aperture

`x_σ(u) = u(σ - 1) / π`.

The positive mass has Laplace limit `(1 + u)⁻¹`, whereas the signed shift has the reciprocal
second-order response `ζ(2)(1 + u)`.  More strongly, their product cancels the singular shifted
zeta factor exactly at every `σ > 1`:

`B_σ(u) * τ_σ(x_σ(u)) / (σ - 1)²
  = ζ(2σ)² / (ζ(2s_σ(u)) G(σ)²)`,

where `s_σ(u) = σ + u(σ - 1)` and `G(σ) = (σ - 1)ζ(σ)` is the analytic residue unit.  Hence the
product tends to `ζ(2)` independently of `u`.

This is an unconditional source-side constraint.  It uses no Xi divisor, zero-location sign, or
RH-equivalent limiting measure.  It fixes the noncompact scale and cancellation that a charged
pole-to-divisor graph must preserve; it does not construct that graph or prove RH.
-/

open Complex MeasureTheory Set Filter ArithmeticFunction LSeries
open scoped BigOperators LSeries.notation Moebius Topology

noncomputable section
namespace RHTower

/-- The positive moving Laplace scale on the critical squarefree-Möbius aperture. -/
def mobiusCriticalBoundaryRate (sigma u : ℝ) : ℝ :=
  u * (sigma - 1) / Real.pi

/-- The shifted Dirichlet parameter seen at moving boundary rate `u`. -/
def mobiusCriticalBoundaryParameter (sigma u : ℝ) : ℝ :=
  sigma + u * (sigma - 1)

/-- The Laplace transform of the positive squarefree-Möbius mass at its moving critical scale. -/
def squarefreeMobiusBoundaryLayerLaplace (sigma u : ℝ) : ℂ :=
  (squarefreeMobiusTotal (mobiusCriticalBoundaryParameter sigma u) : ℂ) /
    (squarefreeMobiusTotal sigma : ℂ)

/-- The actual positive squarefree-channel Laplace summand at the moving scale. -/
def squarefreeMobiusBoundaryLayerTerm (sigma u : ℝ) (n : ℕ) : ℝ :=
  squarefreeMobiusProbability sigma n *
    (n : ℝ) ^ (-(u * (sigma - 1)))

/-- Multiplying one squarefree channel probability by the moving Laplace weight simply shifts its
Dirichlet exponent from `sigma` to `mobiusCriticalBoundaryParameter sigma u`. -/
theorem squarefreeMobiusBoundaryLayerTerm_eq
    (sigma u : ℝ) (n : ℕ) :
    squarefreeMobiusBoundaryLayerTerm sigma u n =
      squarefreeMobiusMass (mobiusCriticalBoundaryParameter sigma u) n /
        squarefreeMobiusTotal sigma := by
  rw [squarefreeMobiusBoundaryLayerTerm, squarefreeMobiusProbability]
  by_cases hsq : Squarefree n
  · have hn0 : n ≠ 0 := by
      intro hn
      subst n
      exact not_squarefree_zero hsq
    have hnpos : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn0
    rw [squarefreeMobiusMass, if_pos hsq,
      squarefreeMobiusMass, if_pos hsq]
    have hrpow :
        (n : ℝ) ^ (-sigma) * (n : ℝ) ^ (-(u * (sigma - 1))) =
          (n : ℝ) ^ (-(mobiusCriticalBoundaryParameter sigma u)) := by
      rw [← Real.rpow_add hnpos]
      congr 1
      unfold mobiusCriticalBoundaryParameter
      ring
    rw [div_mul_eq_mul_div, hrpow]
  · simp [squarefreeMobiusMass, hsq]

/-- The positive moving-aperture Laplace row is summable throughout the Euler half-plane. -/
theorem summable_squarefreeMobiusBoundaryLayerTerm
    {sigma u : ℝ} (hsigma : 1 < sigma) (hu : 0 ≤ u) :
    Summable (squarefreeMobiusBoundaryLayerTerm sigma u) := by
  have hparamGt : 1 < mobiusCriticalBoundaryParameter sigma u := by
    unfold mobiusCriticalBoundaryParameter
    nlinarith
  have hfun : squarefreeMobiusBoundaryLayerTerm sigma u =
      fun n => squarefreeMobiusMass (mobiusCriticalBoundaryParameter sigma u) n /
        squarefreeMobiusTotal sigma := by
    funext n
    exact squarefreeMobiusBoundaryLayerTerm_eq sigma u n
  rw [hfun]
  exact (summable_squarefreeMobiusMass hparamGt).div_const _

/-- Exact total-mass ratio for the moving-aperture squarefree Laplace transform. -/
theorem tsum_squarefreeMobiusBoundaryLayerTerm
    (sigma u : ℝ) :
    (∑' n : ℕ, squarefreeMobiusBoundaryLayerTerm sigma u n) =
      squarefreeMobiusTotal (mobiusCriticalBoundaryParameter sigma u) /
        squarefreeMobiusTotal sigma := by
  rw [show (∑' n : ℕ, squarefreeMobiusBoundaryLayerTerm sigma u n) =
      ∑' n : ℕ,
        squarefreeMobiusMass (mobiusCriticalBoundaryParameter sigma u) n /
          squarefreeMobiusTotal sigma by
    apply tsum_congr
    exact squarefreeMobiusBoundaryLayerTerm_eq sigma u]
  rw [tsum_div_const]
  rfl

/-- Complex form of the exact probability-transform identity used by the analytic limit. -/
theorem ofReal_tsum_squarefreeMobiusBoundaryLayerTerm
    (sigma u : ℝ) :
    ((∑' n : ℕ, squarefreeMobiusBoundaryLayerTerm sigma u n : ℝ) : ℂ) =
      squarefreeMobiusBoundaryLayerLaplace sigma u := by
  rw [tsum_squarefreeMobiusBoundaryLayerTerm sigma u,
    squarefreeMobiusBoundaryLayerLaplace, Complex.ofReal_div]

/-- The rescaled logarithmic coordinate of the positive squarefree channel has the mean-one
exponential Laplace transform `(1 + u)⁻¹` at criticality. -/
theorem tendsto_squarefreeMobiusBoundaryLayerLaplace
    {u : ℝ} (hu : 0 ≤ u) :
    Tendsto (fun sigma : ℝ => squarefreeMobiusBoundaryLayerLaplace sigma u)
      (𝓝[>] (1 : ℝ)) (𝓝 ((((1 + u : ℝ) : ℂ))⁻¹)) := by
  have hsigma : Tendsto (fun sigma : ℝ => (sigma : ℂ))
      (𝓝[>] (1 : ℝ)) (𝓝 (1 : ℂ)) :=
    Complex.continuous_ofReal.continuousAt.tendsto.mono_left inf_le_left
  have hparamReal : Tendsto (fun sigma : ℝ => mobiusCriticalBoundaryParameter sigma u)
      (𝓝[>] (1 : ℝ)) (𝓝 (1 : ℝ)) := by
    have hcont : ContinuousAt
        (fun sigma : ℝ => mobiusCriticalBoundaryParameter sigma u) 1 := by
      unfold mobiusCriticalBoundaryParameter
      fun_prop
    simpa [mobiusCriticalBoundaryParameter] using
      hcont.tendsto.mono_left inf_le_left
  have hparam : Tendsto
      (fun sigma : ℝ => ((mobiusCriticalBoundaryParameter sigma u : ℝ) : ℂ))
      (𝓝[>] (1 : ℝ)) (𝓝 (1 : ℂ)) :=
    Complex.continuous_ofReal.continuousAt.tendsto.comp hparamReal
  have htwoArg : Tendsto (fun sigma : ℝ => 2 * (sigma : ℂ))
      (𝓝[>] (1 : ℝ)) (𝓝 (2 : ℂ)) := by
    simpa using (tendsto_const_nhds.mul hsigma :
      Tendsto (fun sigma : ℝ => (2 : ℂ) * (sigma : ℂ))
        (𝓝[>] (1 : ℝ)) (𝓝 ((2 : ℂ) * 1)))
  have htwoParamArg : Tendsto
      (fun sigma : ℝ => 2 * ((mobiusCriticalBoundaryParameter sigma u : ℝ) : ℂ))
      (𝓝[>] (1 : ℝ)) (𝓝 (2 : ℂ)) := by
    simpa using (tendsto_const_nhds.mul hparam :
      Tendsto
        (fun sigma : ℝ => (2 : ℂ) *
          ((mobiusCriticalBoundaryParameter sigma u : ℝ) : ℂ))
        (𝓝[>] (1 : ℝ)) (𝓝 ((2 : ℂ) * 1)))
  have hnum : Tendsto (fun sigma : ℝ => riemannZeta (2 * (sigma : ℂ)))
      (𝓝[>] (1 : ℝ)) (𝓝 (riemannZeta (2 : ℂ))) :=
    (differentiableAt_riemannZeta (by norm_num : (2 : ℂ) ≠ 1)).continuousAt.tendsto.comp htwoArg
  have hparamNum : Tendsto
      (fun sigma : ℝ =>
        riemannZeta (2 * ((mobiusCriticalBoundaryParameter sigma u : ℝ) : ℂ)))
      (𝓝[>] (1 : ℝ)) (𝓝 (riemannZeta (2 : ℂ))) :=
    (differentiableAt_riemannZeta (by norm_num : (2 : ℂ) ≠ 1)).continuousAt.tendsto.comp
      htwoParamArg
  have hunit : Tendsto (fun sigma : ℝ => zetaResidueUnit (sigma : ℂ))
      (𝓝[>] (1 : ℝ)) (𝓝 (1 : ℂ)) := by
    simpa using zetaResidueUnit_analyticAt.continuousAt.tendsto.comp hsigma
  have hparamUnit : Tendsto
      (fun sigma : ℝ => zetaResidueUnit
        ((mobiusCriticalBoundaryParameter sigma u : ℝ) : ℂ))
      (𝓝[>] (1 : ℝ)) (𝓝 (1 : ℂ)) := by
    simpa using zetaResidueUnit_analyticAt.continuousAt.tendsto.comp hparam
  have huOne : 1 + u ≠ 0 := by nlinarith
  have hzetaTwo : riemannZeta (2 : ℂ) ≠ 0 :=
    riemannZeta_ne_zero_of_one_lt_re (by norm_num)
  have hlimit := (hparamUnit.mul hnum).div
    ((hunit.mul hparamNum).mul_const (((1 + u : ℝ) : ℂ)))
    (mul_ne_zero (mul_ne_zero one_ne_zero hzetaTwo) (by exact_mod_cast huOne))
  have htarget :
      riemannZeta (2 : ℂ) /
          (riemannZeta (2 : ℂ) * (((1 + u : ℝ) : ℂ))) =
        (((1 + u : ℝ) : ℂ))⁻¹ := by
    field_simp [hzetaTwo, huOne]
  have hlimit' : Tendsto
      (fun sigma : ℝ =>
        zetaResidueUnit ((mobiusCriticalBoundaryParameter sigma u : ℝ) : ℂ) *
            riemannZeta (2 * (sigma : ℂ)) /
          ((zetaResidueUnit (sigma : ℂ) *
              riemannZeta (2 * ((mobiusCriticalBoundaryParameter sigma u : ℝ) : ℂ))) *
            (((1 + u : ℝ) : ℂ))))
      (𝓝[>] (1 : ℝ)) (𝓝 ((((1 + u : ℝ) : ℂ))⁻¹)) := by
    simp only [one_mul] at hlimit
    rw [htarget] at hlimit
    simpa using hlimit
  apply hlimit'.congr'
  filter_upwards [self_mem_nhdsWithin] with sigma hsigmaGt
  change 1 < sigma at hsigmaGt
  have hsigOne : sigma ≠ 1 := ne_of_gt hsigmaGt
  have hparamGt : 1 < mobiusCriticalBoundaryParameter sigma u := by
    unfold mobiusCriticalBoundaryParameter
    nlinarith
  have hparamOne : mobiusCriticalBoundaryParameter sigma u ≠ 1 := ne_of_gt hparamGt
  have hsigZeta : 1 < ((sigma : ℂ)).re := by simpa using hsigmaGt
  have hparamZeta : 1 < (((mobiusCriticalBoundaryParameter sigma u : ℝ) : ℂ)).re := by
    simpa using hparamGt
  have htwoSigZeta : 1 < (2 * (sigma : ℂ)).re := by
    norm_num
    linarith
  have htwoParamZeta :
      1 < (2 * ((mobiusCriticalBoundaryParameter sigma u : ℝ) : ℂ)).re := by
    norm_num
    linarith
  rw [squarefreeMobiusBoundaryLayerLaplace,
    ofReal_squarefreeMobiusTotal_eq_zetaRatio hparamGt,
    ofReal_squarefreeMobiusTotal_eq_zetaRatio hsigmaGt]
  have hunitSig : zetaResidueUnit (sigma : ℂ) =
      ((sigma : ℂ) - 1) * riemannZeta (sigma : ℂ) := by
    rw [zetaResidueUnit, Function.update_of_ne (by exact_mod_cast hsigOne)]
  have hunitParam :
      zetaResidueUnit ((mobiusCriticalBoundaryParameter sigma u : ℝ) : ℂ) =
        (((mobiusCriticalBoundaryParameter sigma u : ℝ) : ℂ) - 1) *
          riemannZeta ((mobiusCriticalBoundaryParameter sigma u : ℝ) : ℂ) := by
    rw [zetaResidueUnit, Function.update_of_ne (by exact_mod_cast hparamOne)]
  rw [hunitSig, hunitParam]
  have hsigOneC : (sigma : ℂ) - 1 ≠ 0 :=
    sub_ne_zero.mpr (by exact_mod_cast hsigOne)
  have hparamOneC :
      ((mobiusCriticalBoundaryParameter sigma u : ℝ) : ℂ) - 1 ≠ 0 :=
    sub_ne_zero.mpr (by exact_mod_cast hparamOne)
  have huOneC : (((1 + u : ℝ) : ℂ)) ≠ 0 := by exact_mod_cast huOne
  field_simp [hsigOne, hparamOne, huOne, hsigOneC, hparamOneC, huOneC,
    riemannZeta_ne_zero_of_one_lt_re hsigZeta,
    riemannZeta_ne_zero_of_one_lt_re hparamZeta,
    riemannZeta_ne_zero_of_one_lt_re htwoSigZeta,
    riemannZeta_ne_zero_of_one_lt_re htwoParamZeta]
  unfold mobiusCriticalBoundaryParameter
  push_cast
  ring

/-- At the same moving aperture, Möbius cancellation is second-order and has reciprocal response
`zeta(2) * (1 + u)`. -/
theorem tendsto_infiniteMobiusLaplaceMultiplier_moving_boundary
    {u : ℝ} (hu : 0 ≤ u) :
    Tendsto
      (fun sigma : ℝ =>
        infiniteMobiusLaplaceMultiplier sigma
            (mobiusCriticalBoundaryRate sigma u) / (sigma - 1) ^ 2)
      (𝓝[>] (1 : ℝ))
      (𝓝 (riemannZeta (2 : ℂ) * ((1 + u : ℝ) : ℂ))) := by
  have hsigma : Tendsto (fun sigma : ℝ => (sigma : ℂ))
      (𝓝[>] (1 : ℝ)) (𝓝 (1 : ℂ)) :=
    Complex.continuous_ofReal.continuousAt.tendsto.mono_left inf_le_left
  have hparamReal : Tendsto (fun sigma : ℝ => mobiusCriticalBoundaryParameter sigma u)
      (𝓝[>] (1 : ℝ)) (𝓝 (1 : ℝ)) := by
    have hcont : ContinuousAt
        (fun sigma : ℝ => mobiusCriticalBoundaryParameter sigma u) 1 := by
      unfold mobiusCriticalBoundaryParameter
      fun_prop
    simpa [mobiusCriticalBoundaryParameter] using
      hcont.tendsto.mono_left inf_le_left
  have hparam : Tendsto
      (fun sigma : ℝ => ((mobiusCriticalBoundaryParameter sigma u : ℝ) : ℂ))
      (𝓝[>] (1 : ℝ)) (𝓝 (1 : ℂ)) :=
    Complex.continuous_ofReal.continuousAt.tendsto.comp hparamReal
  have htwoArg : Tendsto (fun sigma : ℝ => 2 * (sigma : ℂ))
      (𝓝[>] (1 : ℝ)) (𝓝 (2 : ℂ)) := by
    simpa using (tendsto_const_nhds.mul hsigma :
      Tendsto (fun sigma : ℝ => (2 : ℂ) * (sigma : ℂ))
        (𝓝[>] (1 : ℝ)) (𝓝 ((2 : ℂ) * 1)))
  have hnum : Tendsto (fun sigma : ℝ => riemannZeta (2 * (sigma : ℂ)))
      (𝓝[>] (1 : ℝ)) (𝓝 (riemannZeta (2 : ℂ))) :=
    (differentiableAt_riemannZeta (by norm_num : (2 : ℂ) ≠ 1)).continuousAt.tendsto.comp htwoArg
  have hunit : Tendsto (fun sigma : ℝ => zetaResidueUnit (sigma : ℂ))
      (𝓝[>] (1 : ℝ)) (𝓝 (1 : ℂ)) := by
    simpa using zetaResidueUnit_analyticAt.continuousAt.tendsto.comp hsigma
  have hparamUnit : Tendsto
      (fun sigma : ℝ => zetaResidueUnit
        ((mobiusCriticalBoundaryParameter sigma u : ℝ) : ℂ))
      (𝓝[>] (1 : ℝ)) (𝓝 (1 : ℂ)) := by
    simpa using zetaResidueUnit_analyticAt.continuousAt.tendsto.comp hparam
  have hlimit := (hnum.mul_const (((1 + u : ℝ) : ℂ))).div
    (hunit.mul hparamUnit) (by norm_num : (1 : ℂ) * 1 ≠ 0)
  have hlimit' : Tendsto
      (fun sigma : ℝ =>
        riemannZeta (2 * (sigma : ℂ)) * (((1 + u : ℝ) : ℂ)) /
          (zetaResidueUnit (sigma : ℂ) *
            zetaResidueUnit ((mobiusCriticalBoundaryParameter sigma u : ℝ) : ℂ)))
      (𝓝[>] (1 : ℝ))
      (𝓝 (riemannZeta (2 : ℂ) * (((1 + u : ℝ) : ℂ)))) := by
    simpa using hlimit
  apply hlimit'.congr'
  filter_upwards [self_mem_nhdsWithin] with sigma hsigmaGt
  change 1 < sigma at hsigmaGt
  have hsigOne : sigma ≠ 1 := ne_of_gt hsigmaGt
  have hparamGt : 1 < mobiusCriticalBoundaryParameter sigma u := by
    unfold mobiusCriticalBoundaryParameter
    nlinarith
  have hparamOne : mobiusCriticalBoundaryParameter sigma u ≠ 1 := ne_of_gt hparamGt
  have huOne : 1 + u ≠ 0 := by nlinarith
  have hsigOneC : (sigma : ℂ) - 1 ≠ 0 :=
    sub_ne_zero.mpr (by exact_mod_cast hsigOne)
  have hparamOneC :
      ((mobiusCriticalBoundaryParameter sigma u : ℝ) : ℂ) - 1 ≠ 0 :=
    sub_ne_zero.mpr (by exact_mod_cast hparamOne)
  have huOneC : (((1 + u : ℝ) : ℂ)) ≠ 0 := by exact_mod_cast huOne
  have hrate : 0 ≤ mobiusCriticalBoundaryRate sigma u := by
    unfold mobiusCriticalBoundaryRate
    positivity
  have hsigZeta : 1 < ((sigma : ℂ)).re := by simpa using hsigmaGt
  have htwoZeta : 1 < (2 * (sigma : ℂ)).re := by
    norm_num
    linarith
  have hparamZeta : 1 < (((mobiusCriticalBoundaryParameter sigma u : ℝ) : ℂ)).re := by
    simpa using hparamGt
  rw [infiniteMobiusLaplaceMultiplier_eq_zetaRatio hsigmaGt hrate]
  have harg : sigma + Real.pi * mobiusCriticalBoundaryRate sigma u =
      mobiusCriticalBoundaryParameter sigma u := by
    unfold mobiusCriticalBoundaryRate mobiusCriticalBoundaryParameter
    field_simp [Real.pi_ne_zero]
  rw [harg]
  have hunitSig : zetaResidueUnit (sigma : ℂ) =
      ((sigma : ℂ) - 1) * riemannZeta (sigma : ℂ) := by
    rw [zetaResidueUnit, Function.update_of_ne (by exact_mod_cast hsigOne)]
  have hunitParam :
      zetaResidueUnit ((mobiusCriticalBoundaryParameter sigma u : ℝ) : ℂ) =
        (((mobiusCriticalBoundaryParameter sigma u : ℝ) : ℂ) - 1) *
          riemannZeta ((mobiusCriticalBoundaryParameter sigma u : ℝ) : ℂ) := by
    rw [zetaResidueUnit, Function.update_of_ne (by exact_mod_cast hparamOne)]
  rw [hunitSig, hunitParam]
  field_simp [hsigOne, hparamOne, huOne, hsigOneC, hparamOneC, huOneC,
    riemannZeta_ne_zero_of_one_lt_re hsigZeta,
    riemannZeta_ne_zero_of_one_lt_re htwoZeta,
    riemannZeta_ne_zero_of_one_lt_re hparamZeta]
  unfold mobiusCriticalBoundaryParameter
  push_cast
  ring

/-- Exact positive/signed cancellation at the moving critical aperture. The singular zeta factor
at the shifted parameter cancels before taking the critical limit. -/
theorem squarefreeMobiusBoundaryLayerLaplace_mul_signed_eq
    {sigma u : ℝ} (hsigma : 1 < sigma) (hu : 0 ≤ u) :
    squarefreeMobiusBoundaryLayerLaplace sigma u *
        (infiniteMobiusLaplaceMultiplier sigma
            (mobiusCriticalBoundaryRate sigma u) / (sigma - 1) ^ 2) =
      riemannZeta (2 * (sigma : ℂ)) ^ 2 /
        (riemannZeta
            (2 * ((mobiusCriticalBoundaryParameter sigma u : ℝ) : ℂ)) *
          zetaResidueUnit (sigma : ℂ) ^ 2) := by
  have hsigOne : sigma ≠ 1 := ne_of_gt hsigma
  have hparamGt : 1 < mobiusCriticalBoundaryParameter sigma u := by
    unfold mobiusCriticalBoundaryParameter
    nlinarith
  have hrate : 0 ≤ mobiusCriticalBoundaryRate sigma u := by
    unfold mobiusCriticalBoundaryRate
    positivity
  have harg : sigma + Real.pi * mobiusCriticalBoundaryRate sigma u =
      mobiusCriticalBoundaryParameter sigma u := by
    unfold mobiusCriticalBoundaryRate mobiusCriticalBoundaryParameter
    field_simp [Real.pi_ne_zero]
  have hsigZeta : 1 < ((sigma : ℂ)).re := by simpa using hsigma
  have hparamZeta : 1 < (((mobiusCriticalBoundaryParameter sigma u : ℝ) : ℂ)).re := by
    simpa using hparamGt
  have htwoSigZeta : 1 < (2 * (sigma : ℂ)).re := by
    norm_num
    linarith
  have htwoParamZeta :
      1 < (2 * ((mobiusCriticalBoundaryParameter sigma u : ℝ) : ℂ)).re := by
    norm_num
    linarith
  rw [squarefreeMobiusBoundaryLayerLaplace,
    ofReal_squarefreeMobiusTotal_eq_zetaRatio hparamGt,
    ofReal_squarefreeMobiusTotal_eq_zetaRatio hsigma,
    infiniteMobiusLaplaceMultiplier_eq_zetaRatio hsigma hrate,
    harg]
  have hunitSig : zetaResidueUnit (sigma : ℂ) =
      ((sigma : ℂ) - 1) * riemannZeta (sigma : ℂ) := by
    rw [zetaResidueUnit, Function.update_of_ne (by exact_mod_cast hsigOne)]
  rw [hunitSig]
  have hsigOneC : (sigma : ℂ) - 1 ≠ 0 :=
    sub_ne_zero.mpr (by exact_mod_cast hsigOne)
  field_simp [hsigOne, hsigOneC,
    riemannZeta_ne_zero_of_one_lt_re hsigZeta,
    riemannZeta_ne_zero_of_one_lt_re hparamZeta,
    riemannZeta_ne_zero_of_one_lt_re htwoSigZeta,
    riemannZeta_ne_zero_of_one_lt_re htwoParamZeta]

/-- The positive escaped mass and signed Möbius response have scale-independent critical product
`zeta(2)`. -/
theorem tendsto_squarefreeMass_mul_signedMobius_moving_boundary
    {u : ℝ} (hu : 0 ≤ u) :
    Tendsto
      (fun sigma : ℝ =>
        squarefreeMobiusBoundaryLayerLaplace sigma u *
          (infiniteMobiusLaplaceMultiplier sigma
              (mobiusCriticalBoundaryRate sigma u) / (sigma - 1) ^ 2))
      (𝓝[>] (1 : ℝ)) (𝓝 (riemannZeta (2 : ℂ))) := by
  have h := (tendsto_squarefreeMobiusBoundaryLayerLaplace hu).mul
    (tendsto_infiniteMobiusLaplaceMultiplier_moving_boundary hu)
  have huOne : 1 + u ≠ 0 := by nlinarith
  have huOneC : (((1 + u : ℝ) : ℂ)) ≠ 0 := by exact_mod_cast huOne
  have hscalar :
      (((1 + u : ℝ) : ℂ))⁻¹ *
          (riemannZeta (2 : ℂ) * (((1 + u : ℝ) : ℂ))) =
        riemannZeta (2 : ℂ) := by
    field_simp [huOne, huOneC]
  rw [hscalar] at h
  exact h

end RHTower
