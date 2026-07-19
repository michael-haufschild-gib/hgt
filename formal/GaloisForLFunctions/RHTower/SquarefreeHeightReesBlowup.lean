import GaloisForLFunctions.RHTower.InfiniteMobiusCriticalBoundaryLayer
import GaloisForLFunctions.RHTower.SquarefreeFixedCurrentLocalization

/-!
# The squarefree height overlap has two inequivalent critical charts

The normalized squarefree overlap at base `sigma > 1`, real aperture `delta`, and physical
height `gamma` is

`Z_sq(sigma + delta * (sigma - 1) + i gamma) / Z_sq(sigma)`.

There is no single nondegenerate critical normalization for all heights.  On the microscopic
scale `gamma = (sigma - 1) * eta`, the overlap converges to the Cauchy profile
`(1 + delta + i eta)⁻¹`.  At any fixed nonzero physical height it instead vanishes linearly in
`sigma - 1`; after the forced reciprocal rescaling its limit is
`zeta(2) * Z_sq(1 + i gamma)`.

Thus the critical source is a two-chart blow-up: a contact chart at height scale
`O(sigma - 1)` and a renormalized fixed-height chart.  A common uniformly nondegenerate height
Hilbert trivialization cannot be obtained from this overlap.  The result is source-side and
unconditional; it neither invokes a Xi divisor nor proves the Green--Ward estimate needed for RH.
-/

open Complex Filter Set
open scoped Topology

noncomputable section
namespace RHTower

open GaloisForLFunctions

/-- The squarefree source parameter at real aperture `delta` and physical height `gamma`. -/
def squarefreeHeightParameter (sigma delta gamma : ℝ) : ℂ :=
  ((sigma + delta * (sigma - 1) : ℝ) : ℂ) + (gamma : ℂ) * Complex.I

@[simp] theorem squarefreeHeightParameter_re (sigma delta gamma : ℝ) :
    (squarefreeHeightParameter sigma delta gamma).re =
      sigma + delta * (sigma - 1) := by
  simp [squarefreeHeightParameter]

/-- The normalized squarefree overlap in physical-height coordinates. -/
def squarefreeHeightOverlap (sigma delta gamma : ℝ) : ℂ :=
  squarefreePartition (squarefreeHeightParameter sigma delta gamma) /
    squarefreePartition (sigma : ℂ)

/-- The contact-chart overlap, where physical height is of order `sigma - 1`. -/
def squarefreeMicroscopicHeightOverlap (sigma delta eta : ℝ) : ℂ :=
  squarefreeHeightOverlap sigma delta ((sigma - 1) * eta)

/-- The forced fixed-height normalization away from height zero. -/
def squarefreeMacroscopicHeightOverlap (sigma delta gamma : ℝ) : ℂ :=
  squarefreeHeightOverlap sigma delta gamma / ((sigma - 1 : ℝ) : ℂ)

/-- Exact transition function between the microscopic and macroscopic charts. -/
theorem squarefreeHeight_chart_transition
    {sigma : ℝ} (hsigma : sigma ≠ 1) (delta eta : ℝ) :
    ((sigma - 1 : ℝ) : ℂ) *
        squarefreeMacroscopicHeightOverlap sigma delta ((sigma - 1) * eta) =
      squarefreeMicroscopicHeightOverlap sigma delta eta := by
  rw [squarefreeMacroscopicHeightOverlap, squarefreeMicroscopicHeightOverlap]
  exact mul_div_cancel₀ _ (by exact_mod_cast sub_ne_zero.mpr hsigma)

/-- In the microscopic height chart, the squarefree overlap has the universal Cauchy limit. -/
theorem tendsto_squarefreeMicroscopicHeightOverlap
    {delta : ℝ} (hdelta : 0 ≤ delta) (eta : ℝ) :
    Tendsto (fun sigma : ℝ => squarefreeMicroscopicHeightOverlap sigma delta eta)
      (𝓝[>] (1 : ℝ))
      (𝓝 ((((1 + delta : ℝ) : ℂ) + (eta : ℂ) * Complex.I)⁻¹)) := by
  let q : ℂ := ((1 + delta : ℝ) : ℂ) + (eta : ℂ) * Complex.I
  have hq : q ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp [q] at hre
    linarith
  have hsigma : Tendsto (fun sigma : ℝ => (sigma : ℂ))
      (𝓝[>] (1 : ℝ)) (𝓝 (1 : ℂ)) :=
    Complex.continuous_ofReal.continuousAt.tendsto.mono_left inf_le_left
  have hparam : Tendsto
      (fun sigma : ℝ =>
        squarefreeHeightParameter sigma delta ((sigma - 1) * eta))
      (𝓝[>] (1 : ℝ)) (𝓝 (1 : ℂ)) := by
    have hcont : ContinuousAt
        (fun sigma : ℝ =>
          squarefreeHeightParameter sigma delta ((sigma - 1) * eta)) 1 := by
      unfold squarefreeHeightParameter
      fun_prop
    simpa [squarefreeHeightParameter] using hcont.tendsto.mono_left inf_le_left
  have htwoSigma : Tendsto (fun sigma : ℝ => 2 * (sigma : ℂ))
      (𝓝[>] (1 : ℝ)) (𝓝 (2 : ℂ)) := by
    simpa using (tendsto_const_nhds.mul hsigma :
      Tendsto (fun sigma : ℝ => (2 : ℂ) * (sigma : ℂ))
        (𝓝[>] (1 : ℝ)) (𝓝 ((2 : ℂ) * 1)))
  have htwoParam : Tendsto
      (fun sigma : ℝ =>
        2 * squarefreeHeightParameter sigma delta ((sigma - 1) * eta))
      (𝓝[>] (1 : ℝ)) (𝓝 (2 : ℂ)) := by
    simpa using (tendsto_const_nhds.mul hparam :
      Tendsto
        (fun sigma : ℝ =>
          (2 : ℂ) * squarefreeHeightParameter sigma delta ((sigma - 1) * eta))
        (𝓝[>] (1 : ℝ)) (𝓝 ((2 : ℂ) * 1)))
  have hzetaTwoSigma : Tendsto
      (fun sigma : ℝ => riemannZeta (2 * (sigma : ℂ)))
      (𝓝[>] (1 : ℝ)) (𝓝 (riemannZeta (2 : ℂ))) :=
    (differentiableAt_riemannZeta (by norm_num : (2 : ℂ) ≠ 1)).continuousAt.tendsto.comp
      htwoSigma
  have hzetaTwoParam : Tendsto
      (fun sigma : ℝ =>
        riemannZeta
          (2 * squarefreeHeightParameter sigma delta ((sigma - 1) * eta)))
      (𝓝[>] (1 : ℝ)) (𝓝 (riemannZeta (2 : ℂ))) :=
    (differentiableAt_riemannZeta (by norm_num : (2 : ℂ) ≠ 1)).continuousAt.tendsto.comp
      htwoParam
  have hunitSigma : Tendsto (fun sigma : ℝ => zetaResidueUnit (sigma : ℂ))
      (𝓝[>] (1 : ℝ)) (𝓝 (1 : ℂ)) := by
    simpa using zetaResidueUnit_analyticAt.continuousAt.tendsto.comp hsigma
  have hunitParam : Tendsto
      (fun sigma : ℝ =>
        zetaResidueUnit
          (squarefreeHeightParameter sigma delta ((sigma - 1) * eta)))
      (𝓝[>] (1 : ℝ)) (𝓝 (1 : ℂ)) := by
    simpa using zetaResidueUnit_analyticAt.continuousAt.tendsto.comp hparam
  have hzetaTwo : riemannZeta (2 : ℂ) ≠ 0 :=
    riemannZeta_ne_zero_of_one_lt_re (by norm_num)
  have hregularized := (hunitParam.mul hzetaTwoSigma).div
    ((hunitSigma.mul hzetaTwoParam).mul_const q)
    (mul_ne_zero (mul_ne_zero one_ne_zero hzetaTwo) hq)
  have htarget :
      riemannZeta (2 : ℂ) / (riemannZeta (2 : ℂ) * q) = q⁻¹ := by
    field_simp [hzetaTwo, hq]
  have hlimit : Tendsto
      (fun sigma : ℝ =>
        zetaResidueUnit
              (squarefreeHeightParameter sigma delta ((sigma - 1) * eta)) *
            riemannZeta (2 * (sigma : ℂ)) /
          ((zetaResidueUnit (sigma : ℂ) *
              riemannZeta
                (2 * squarefreeHeightParameter sigma delta ((sigma - 1) * eta))) * q))
      (𝓝[>] (1 : ℝ)) (𝓝 q⁻¹) := by
    simp only [one_mul] at hregularized
    rw [htarget] at hregularized
    simpa using hregularized
  apply hlimit.congr'
  filter_upwards [self_mem_nhdsWithin] with sigma hsigmaGt
  change 1 < sigma at hsigmaGt
  have hsigOne : sigma ≠ 1 := ne_of_gt hsigmaGt
  have hparamGt :
      1 < (squarefreeHeightParameter sigma delta ((sigma - 1) * eta)).re := by
    simp [squarefreeHeightParameter]
    nlinarith
  have hparamOne :
      squarefreeHeightParameter sigma delta ((sigma - 1) * eta) ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    simp [squarefreeHeightParameter] at hre
    nlinarith
  have hsigZeta : 1 < ((sigma : ℂ)).re := by simpa using hsigmaGt
  have hparamZeta :
      1 < (squarefreeHeightParameter sigma delta ((sigma - 1) * eta)).re := hparamGt
  have htwoSigZeta : 1 < (2 * (sigma : ℂ)).re := by
    norm_num
    linarith
  have htwoParamZeta :
      1 < (2 * squarefreeHeightParameter sigma delta ((sigma - 1) * eta)).re := by
    norm_num [Complex.mul_re]
    nlinarith [mul_nonneg hdelta (sub_nonneg.mpr hsigmaGt.le)]
  rw [squarefreeMicroscopicHeightOverlap, squarefreeHeightOverlap]
  simp only [squarefreePartition]
  have hunitSig : zetaResidueUnit (sigma : ℂ) =
      ((sigma : ℂ) - 1) * riemannZeta (sigma : ℂ) := by
    rw [zetaResidueUnit, Function.update_of_ne (by exact_mod_cast hsigOne)]
  have hunitPar :
      zetaResidueUnit
          (squarefreeHeightParameter sigma delta ((sigma - 1) * eta)) =
        (squarefreeHeightParameter sigma delta ((sigma - 1) * eta) - 1) *
          riemannZeta
            (squarefreeHeightParameter sigma delta ((sigma - 1) * eta)) := by
    rw [zetaResidueUnit, Function.update_of_ne hparamOne]
  rw [hunitSig, hunitPar]
  have hsigOneC : (sigma : ℂ) - 1 ≠ 0 :=
    sub_ne_zero.mpr (by exact_mod_cast hsigOne)
  have hparamOneC :
      squarefreeHeightParameter sigma delta ((sigma - 1) * eta) - 1 ≠ 0 :=
    sub_ne_zero.mpr hparamOne
  field_simp [hq, hsigOneC, hparamOneC,
    riemannZeta_ne_zero_of_one_lt_re hsigZeta,
    riemannZeta_ne_zero_of_one_lt_re hparamZeta,
    riemannZeta_ne_zero_of_one_lt_re htwoSigZeta,
    riemannZeta_ne_zero_of_one_lt_re htwoParamZeta]
  unfold squarefreeHeightParameter q
  push_cast
  ring

/-- At every fixed nonzero physical height, division by `sigma - 1` is the unique scalar
normalization exposing a nonzero squarefree boundary section. -/
theorem tendsto_squarefreeMacroscopicHeightOverlap
    {delta : ℝ} (hdelta : 0 ≤ delta) {gamma : ℝ} (hgamma : gamma ≠ 0) :
    Tendsto (fun sigma : ℝ => squarefreeMacroscopicHeightOverlap sigma delta gamma)
      (𝓝[>] (1 : ℝ))
      (𝓝 (riemannZeta (2 : ℂ) *
        squarefreePartition ((1 : ℂ) + (gamma : ℂ) * Complex.I))) := by
  let t : ℂ := (1 : ℂ) + (gamma : ℂ) * Complex.I
  have htOne : t ≠ 1 := by
    intro h
    have him := congrArg Complex.im h
    simp [t] at him
    exact hgamma him
  have hsigma : Tendsto (fun sigma : ℝ => (sigma : ℂ))
      (𝓝[>] (1 : ℝ)) (𝓝 (1 : ℂ)) :=
    Complex.continuous_ofReal.continuousAt.tendsto.mono_left inf_le_left
  have hparam : Tendsto
      (fun sigma : ℝ => squarefreeHeightParameter sigma delta gamma)
      (𝓝[>] (1 : ℝ)) (𝓝 t) := by
    have hcont : ContinuousAt
        (fun sigma : ℝ => squarefreeHeightParameter sigma delta gamma) 1 := by
      unfold squarefreeHeightParameter
      fun_prop
    simpa [squarefreeHeightParameter, t] using hcont.tendsto.mono_left inf_le_left
  have htwoSigma : Tendsto (fun sigma : ℝ => 2 * (sigma : ℂ))
      (𝓝[>] (1 : ℝ)) (𝓝 (2 : ℂ)) := by
    simpa using (tendsto_const_nhds.mul hsigma :
      Tendsto (fun sigma : ℝ => (2 : ℂ) * (sigma : ℂ))
        (𝓝[>] (1 : ℝ)) (𝓝 ((2 : ℂ) * 1)))
  have htwoParam : Tendsto
      (fun sigma : ℝ => 2 * squarefreeHeightParameter sigma delta gamma)
      (𝓝[>] (1 : ℝ)) (𝓝 (2 * t)) :=
    tendsto_const_nhds.mul hparam
  have hzetaParam : Tendsto
      (fun sigma : ℝ => riemannZeta (squarefreeHeightParameter sigma delta gamma))
      (𝓝[>] (1 : ℝ)) (𝓝 (riemannZeta t)) :=
    (differentiableAt_riemannZeta htOne).continuousAt.tendsto.comp hparam
  have hzetaTwoSigma : Tendsto
      (fun sigma : ℝ => riemannZeta (2 * (sigma : ℂ)))
      (𝓝[>] (1 : ℝ)) (𝓝 (riemannZeta (2 : ℂ))) :=
    (differentiableAt_riemannZeta (by norm_num : (2 : ℂ) ≠ 1)).continuousAt.tendsto.comp
      htwoSigma
  have htwoTRe : 1 < (2 * t).re := by
    simp [t, Complex.mul_re]
  have htwoTOne : 2 * t ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    simp [t, Complex.mul_re] at hre
  have hzetaTwoParam : Tendsto
      (fun sigma : ℝ =>
        riemannZeta (2 * squarefreeHeightParameter sigma delta gamma))
      (𝓝[>] (1 : ℝ)) (𝓝 (riemannZeta (2 * t))) :=
    (differentiableAt_riemannZeta htwoTOne).continuousAt.tendsto.comp htwoParam
  have hunitSigma : Tendsto (fun sigma : ℝ => zetaResidueUnit (sigma : ℂ))
      (𝓝[>] (1 : ℝ)) (𝓝 (1 : ℂ)) := by
    simpa using zetaResidueUnit_analyticAt.continuousAt.tendsto.comp hsigma
  have hzetaTwoT : riemannZeta (2 * t) ≠ 0 :=
    riemannZeta_ne_zero_of_one_lt_re htwoTRe
  have hregularized := (hzetaParam.mul hzetaTwoSigma).div
    (hzetaTwoParam.mul hunitSigma) (mul_ne_zero hzetaTwoT one_ne_zero)
  have htarget :
      riemannZeta t * riemannZeta (2 : ℂ) /
          (riemannZeta (2 * t) * 1) =
        riemannZeta (2 : ℂ) * squarefreePartition t := by
    rw [squarefreePartition]
    field_simp [hzetaTwoT]
  have hlimit : Tendsto
      (fun sigma : ℝ =>
        riemannZeta (squarefreeHeightParameter sigma delta gamma) *
            riemannZeta (2 * (sigma : ℂ)) /
          (riemannZeta (2 * squarefreeHeightParameter sigma delta gamma) *
            zetaResidueUnit (sigma : ℂ)))
      (𝓝[>] (1 : ℝ))
      (𝓝 (riemannZeta (2 : ℂ) * squarefreePartition t)) := by
    rw [htarget] at hregularized
    exact hregularized
  apply hlimit.congr'
  filter_upwards [self_mem_nhdsWithin] with sigma hsigmaGt
  change 1 < sigma at hsigmaGt
  have hsigOne : sigma ≠ 1 := ne_of_gt hsigmaGt
  have hparamGt : 1 < (squarefreeHeightParameter sigma delta gamma).re := by
    simp [squarefreeHeightParameter]
    nlinarith
  have hparamOne : squarefreeHeightParameter sigma delta gamma ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    simp [squarefreeHeightParameter] at hre
    nlinarith
  have hsigZeta : 1 < ((sigma : ℂ)).re := by simpa using hsigmaGt
  have hparamZeta : 1 < (squarefreeHeightParameter sigma delta gamma).re := hparamGt
  have htwoSigZeta : 1 < (2 * (sigma : ℂ)).re := by
    norm_num
    linarith
  have htwoParamZeta :
      1 < (2 * squarefreeHeightParameter sigma delta gamma).re := by
    norm_num [Complex.mul_re]
    nlinarith [mul_nonneg hdelta (sub_nonneg.mpr hsigmaGt.le)]
  rw [squarefreeMacroscopicHeightOverlap, squarefreeHeightOverlap]
  simp only [squarefreePartition]
  have hunitSig : zetaResidueUnit (sigma : ℂ) =
      ((sigma : ℂ) - 1) * riemannZeta (sigma : ℂ) := by
    rw [zetaResidueUnit, Function.update_of_ne (by exact_mod_cast hsigOne)]
  rw [hunitSig]
  have hsigOneC : (sigma : ℂ) - 1 ≠ 0 :=
    sub_ne_zero.mpr (by exact_mod_cast hsigOne)
  field_simp [hsigOneC,
    riemannZeta_ne_zero_of_one_lt_re hsigZeta,
    riemannZeta_ne_zero_of_one_lt_re hparamZeta,
    riemannZeta_ne_zero_of_one_lt_re htwoSigZeta,
    riemannZeta_ne_zero_of_one_lt_re htwoParamZeta]
  push_cast
  ring

/-- The unrenormalized squarefree overlap collapses at every fixed nonzero physical height. -/
theorem tendsto_squarefreeHeightOverlap_fixed_nonzero
    {delta : ℝ} (hdelta : 0 ≤ delta) {gamma : ℝ} (hgamma : gamma ≠ 0) :
    Tendsto (fun sigma : ℝ => squarefreeHeightOverlap sigma delta gamma)
      (𝓝[>] (1 : ℝ)) (𝓝 0) := by
  have hmacro := tendsto_squarefreeMacroscopicHeightOverlap hdelta hgamma
  have hepsilon : Tendsto (fun sigma : ℝ => ((sigma - 1 : ℝ) : ℂ))
      (𝓝[>] (1 : ℝ)) (𝓝 0) := by
    have hcont : ContinuousAt (fun sigma : ℝ => ((sigma - 1 : ℝ) : ℂ)) 1 := by
      fun_prop
    simpa using hcont.tendsto.mono_left inf_le_left
  have hprod := hmacro.mul hepsilon
  have hprod0 : Tendsto
      (fun sigma : ℝ => squarefreeMacroscopicHeightOverlap sigma delta gamma *
        ((sigma - 1 : ℝ) : ℂ)) (𝓝[>] (1 : ℝ)) (𝓝 0) := by
    simpa using hprod
  apply hprod0.congr'
  filter_upwards [self_mem_nhdsWithin] with sigma hsigmaGt
  change 1 < sigma at hsigmaGt
  rw [squarefreeMacroscopicHeightOverlap]
  exact div_mul_cancel₀ _ (show ((sigma - 1 : ℝ) : ℂ) ≠ 0 by
    exact_mod_cast sub_ne_zero.mpr (ne_of_gt hsigmaGt))

end RHTower
