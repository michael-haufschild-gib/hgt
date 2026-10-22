import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmThetaMobiusTwoSidedApertureWall

/-!
# Unit normalization and strict Hardy-Gram rigidity of the two-sided source

P-G37 proves that the raw source aperture is expansive on its negative side.
This module implements its positive survivor: normalize by the exact finite
squarefree mass ratio before taking the critical boundary.

The result is a literal two-sided family of unit Hilbert vectors.  Its complete
critical Gram is the normalized right-half-plane Hardy kernel

`sqrt(1+2u) sqrt(1+2v) / (1+u+v)`.

The loss from one is an exact square and vanishes only when `u=v`.  Thus scalar
normalization repairs reversibility without erasing displacement: off-wall
source motion becomes a strict Hilbert angle.  Any Route P saturation law must
force equality of source apertures, not merely boundedness or unit norm.
-/

open Complex Filter MeasureTheory Set Topology
open scoped BigOperators

namespace RHTower.HedenmalmThetaSource

noncomputable section

private theorem exp_pair_mul_probability_eq_boundaryLayerTerm_twoSided
    {sigma u v : ℝ} (n : ℕ) :
    Real.exp (-(v * (sigma - 1) * Real.log n)) *
          Real.exp (-(u * (sigma - 1) * Real.log n)) *
          squarefreeMobiusProbability sigma n =
        squarefreeMobiusBoundaryLayerTerm sigma (u + v) n := by
  by_cases hsq : Squarefree n
  · have hn0 : n ≠ 0 := fun hn => by
      subst n
      exact not_squarefree_zero hsq
    have hnpos : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn0
    rw [squarefreeMobiusBoundaryLayerTerm, Real.rpow_def_of_pos hnpos,
      ← Real.exp_add]
    have harg :
        -(v * (sigma - 1) * Real.log n) +
            -(u * (sigma - 1) * Real.log n) =
          Real.log n * -((u + v) * (sigma - 1)) := by
      ring
    rw [harg]
    ring
  · simp [squarefreeMobiusBoundaryLayerTerm, squarefreeMobiusProbability,
      squarefreeMobiusMass, hsq]

/-- Exact two-aperture Gram throughout the full two-sided Hilbert range. -/
theorem inner_infiniteMobiusCriticalTwoSidedDampedSignedWeightLp_eq_boundaryLayerLaplace
    {sigma u v : ℝ} (hsigma : 1 < sigma)
    (hu : -(1 / 2 : ℝ) < u) (hv : -(1 / 2 : ℝ) < v) :
    inner ℂ
        (infiniteMobiusCriticalTwoSidedDampedSignedWeightLp sigma u hsigma hu)
        (infiniteMobiusCriticalTwoSidedDampedSignedWeightLp sigma v hsigma hv) =
      squarefreeMobiusBoundaryLayerLaplace sigma (u + v) := by
  rw [lp.inner_eq_tsum]
  simp only [infiniteMobiusCriticalTwoSidedDampedSignedWeightLp,
    RCLike.inner_apply]
  rw [show
      (∑' n : ℕ,
        infiniteMobiusCriticalDampedSignedWeight sigma v n *
          (starRingEnd ℂ)
            (infiniteMobiusCriticalDampedSignedWeight sigma u n)) =
        ∑' n : ℕ,
          (squarefreeMobiusBoundaryLayerTerm sigma (u + v) n : ℂ) by
    apply tsum_congr
    intro n
    rw [infiniteMobiusCriticalDampedSignedWeight,
      infiniteMobiusCriticalDampedSignedWeight]
    have hnorm :
        infiniteMobiusSignedWeight sigma n *
            (starRingEnd ℂ) (infiniteMobiusSignedWeight sigma n) =
          (squarefreeMobiusProbability sigma n : ℂ) := by
      calc
        _ = ((‖infiniteMobiusSignedWeight sigma n‖ : ℂ) ^ 2) :=
          RCLike.mul_conj (infiniteMobiusSignedWeight sigma n)
        _ = _ := by
          rw [← Complex.ofReal_pow, norm_infiniteMobiusSignedWeight_sq hsigma]
    simp only [map_mul, Complex.conj_ofReal]
    rw [show
      (Real.exp (-(v * (sigma - 1) * Real.log n)) : ℂ) *
            infiniteMobiusSignedWeight sigma n *
          ((Real.exp (-(u * (sigma - 1) * Real.log n)) : ℂ) *
            (starRingEnd ℂ) (infiniteMobiusSignedWeight sigma n)) =
        ((Real.exp (-(v * (sigma - 1) * Real.log n)) *
          Real.exp (-(u * (sigma - 1) * Real.log n)) : ℝ) : ℂ) *
          (infiniteMobiusSignedWeight sigma n *
            (starRingEnd ℂ) (infiniteMobiusSignedWeight sigma n)) by
      push_cast
      ring]
    rw [hnorm]
    simpa only [Complex.ofReal_mul] using congrArg Complex.ofReal
      (exp_pair_mul_probability_eq_boundaryLayerTerm_twoSided
        (sigma := sigma) (u := u) (v := v) n)]
  rw [← Complex.ofReal_tsum
    (squarefreeMobiusBoundaryLayerTerm sigma (u + v))]
  exact ofReal_tsum_squarefreeMobiusBoundaryLayerTerm sigma (u + v)

/-- Positive finite-source scalar that unitarizes the raw aperture vector. -/
def mobiusCriticalTwoSidedUnitNormalization (sigma u : ℝ) : ℝ :=
  Real.sqrt
    (squarefreeMobiusTotal sigma /
      squarefreeMobiusTotal (mobiusCriticalBoundaryParameter sigma (2 * u)))

/-- Exact unit normalization of the two-sided squarefree-Möbius source. -/
def infiniteMobiusCriticalTwoSidedUnitSignedWeightLp
    (sigma u : ℝ) (hsigma : 1 < sigma) (hu : -(1 / 2 : ℝ) < u) :
    lp (fun _ : ℕ => ℂ) 2 :=
  (mobiusCriticalTwoSidedUnitNormalization sigma u : ℂ) •
    infiniteMobiusCriticalTwoSidedDampedSignedWeightLp sigma u hsigma hu

/-- The normalization square is the inverse raw norm-square ratio. -/
theorem mobiusCriticalTwoSidedUnitNormalization_sq
    {sigma u : ℝ} (hsigma : 1 < sigma) (hu : -(1 / 2 : ℝ) < u) :
    mobiusCriticalTwoSidedUnitNormalization sigma u ^ 2 =
      squarefreeMobiusTotal sigma /
        squarefreeMobiusTotal (mobiusCriticalBoundaryParameter sigma (2 * u)) := by
  rw [mobiusCriticalTwoSidedUnitNormalization, Real.sq_sqrt]
  exact div_nonneg (squarefreeMobiusTotal_pos hsigma).le
    (squarefreeMobiusTotal_pos (by
      rw [mobiusCriticalBoundaryParameter]
      nlinarith)).le

/-- Every normalized finite-source aperture vector has squared norm one. -/
theorem norm_sq_infiniteMobiusCriticalTwoSidedUnitSignedWeightLp
    {sigma u : ℝ} (hsigma : 1 < sigma) (hu : -(1 / 2 : ℝ) < u) :
    ‖infiniteMobiusCriticalTwoSidedUnitSignedWeightLp sigma u hsigma hu‖ ^ 2 = 1 := by
  have hnormalization : 0 ≤ mobiusCriticalTwoSidedUnitNormalization sigma u :=
    Real.sqrt_nonneg _
  rw [infiniteMobiusCriticalTwoSidedUnitSignedWeightLp, norm_smul, mul_pow,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnormalization,
    mobiusCriticalTwoSidedUnitNormalization_sq hsigma hu,
    norm_sq_infiniteMobiusCriticalTwoSidedDampedSignedWeightLp hsigma hu]
  have hsig := (squarefreeMobiusTotal_pos hsigma).ne'
  have hparam :
      squarefreeMobiusTotal (mobiusCriticalBoundaryParameter sigma (2 * u)) ≠ 0 := by
    apply (squarefreeMobiusTotal_pos _).ne'
    rw [mobiusCriticalBoundaryParameter]
    nlinarith
  field_simp [hsig, hparam]

/-- Exact finite-source normalized two-aperture Gram. -/
theorem inner_infiniteMobiusCriticalTwoSidedUnitSignedWeightLp
    {sigma u v : ℝ} (hsigma : 1 < sigma)
    (hu : -(1 / 2 : ℝ) < u) (hv : -(1 / 2 : ℝ) < v) :
    inner ℂ
        (infiniteMobiusCriticalTwoSidedUnitSignedWeightLp sigma u hsigma hu)
        (infiniteMobiusCriticalTwoSidedUnitSignedWeightLp sigma v hsigma hv) =
      (mobiusCriticalTwoSidedUnitNormalization sigma u : ℂ) *
        (mobiusCriticalTwoSidedUnitNormalization sigma v : ℂ) *
          squarefreeMobiusBoundaryLayerLaplace sigma (u + v) := by
  rw [infiniteMobiusCriticalTwoSidedUnitSignedWeightLp,
    infiniteMobiusCriticalTwoSidedUnitSignedWeightLp,
    inner_smul_left, inner_smul_right,
    inner_infiniteMobiusCriticalTwoSidedDampedSignedWeightLp_eq_boundaryLayerLaplace
      hsigma hu hv]
  simp
  ring

/-- Critical normalization limit is the forced scalar `sqrt (1+2u)`. -/
theorem tendsto_mobiusCriticalTwoSidedUnitNormalization
    {u : ℝ} (hu : -(1 / 2 : ℝ) < u) :
    Tendsto (fun sigma : ℝ =>
      if 1 < sigma then
        mobiusCriticalTwoSidedUnitNormalization sigma u
      else 0)
      (𝓝[>] (1 : ℝ)) (𝓝 (Real.sqrt (1 + 2 * u))) := by
  have hnorm :=
    tendsto_norm_sq_infiniteMobiusCriticalTwoSidedDampedSignedWeightLp hu
  have hlimitPos : 0 < 1 + 2 * u := by linarith
  have hlimitNe : (1 + 2 * u)⁻¹ ≠ 0 := inv_ne_zero hlimitPos.ne'
  have hinv := hnorm.inv₀ hlimitNe
  have hsqrt := Real.continuous_sqrt.continuousAt.tendsto.comp hinv
  change Tendsto
      (fun sigma : ℝ => Real.sqrt
        ((if hsigma : 1 < sigma then
          ‖infiniteMobiusCriticalTwoSidedDampedSignedWeightLp sigma u hsigma hu‖ ^ 2
        else 0)⁻¹))
      (𝓝[>] (1 : ℝ)) (𝓝 (Real.sqrt (((1 + 2 * u)⁻¹)⁻¹))) at hsqrt
  have hsqrt' : Tendsto
      (fun sigma : ℝ => Real.sqrt
        ((if hsigma : 1 < sigma then
          ‖infiniteMobiusCriticalTwoSidedDampedSignedWeightLp sigma u hsigma hu‖ ^ 2
        else 0)⁻¹))
      (𝓝[>] (1 : ℝ)) (𝓝 (Real.sqrt (1 + 2 * u))) := by
    simpa only [inv_inv] using hsqrt
  refine hsqrt'.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with sigma hsigma
  change 1 < sigma at hsigma
  rw [if_pos hsigma, dif_pos hsigma,
    norm_sq_infiniteMobiusCriticalTwoSidedDampedSignedWeightLp hsigma hu,
    mobiusCriticalTwoSidedUnitNormalization]
  congr 1
  have hsig := (squarefreeMobiusTotal_pos hsigma).ne'
  have hparam :
      squarefreeMobiusTotal (mobiusCriticalBoundaryParameter sigma (2 * u)) ≠ 0 := by
    apply (squarefreeMobiusTotal_pos _).ne'
    rw [mobiusCriticalBoundaryParameter]
    nlinarith
  field_simp [hsig, hparam]

/-- **P-G38 normalized Hardy-Gram law.** The critical Gram of the
two-sided unit source is the normalized Cauchy kernel. -/
theorem tendsto_inner_infiniteMobiusCriticalTwoSidedUnitSignedWeightLp
    {u v : ℝ} (hu : -(1 / 2 : ℝ) < u) (hv : -(1 / 2 : ℝ) < v) :
    Tendsto (fun sigma : ℝ =>
      if hsigma : 1 < sigma then
        inner ℂ
          (infiniteMobiusCriticalTwoSidedUnitSignedWeightLp sigma u hsigma hu)
          (infiniteMobiusCriticalTwoSidedUnitSignedWeightLp sigma v hsigma hv)
      else 0)
      (𝓝[>] (1 : ℝ))
      (𝓝 ((Real.sqrt (1 + 2 * u) : ℂ) *
        (Real.sqrt (1 + 2 * v) : ℂ) *
          (((1 + u + v : ℝ) : ℂ))⁻¹)) := by
  have hNu := Complex.continuous_ofReal.continuousAt.tendsto.comp
    (tendsto_mobiusCriticalTwoSidedUnitNormalization hu)
  have hNv := Complex.continuous_ofReal.continuousAt.tendsto.comp
    (tendsto_mobiusCriticalTwoSidedUnitNormalization hv)
  have huv : -1 < u + v := by linarith
  have hB := tendsto_squarefreeMobiusBoundaryLayerLaplace_of_negOne_lt huv
  have hmul := (hNu.mul hNv).mul hB
  have hlimit :
      ((((1 + (u + v) : ℝ) : ℂ))⁻¹) =
        (((1 + u + v : ℝ) : ℂ))⁻¹ := by
    congr 2
    ring
  rw [← hlimit]
  refine hmul.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with sigma hsigma
  change 1 < sigma at hsigma
  simp only [Function.comp_apply, if_pos hsigma, dif_pos hsigma]
  exact (inner_infiniteMobiusCriticalTwoSidedUnitSignedWeightLp hsigma hu hv).symm

/-- Normalized critical Hardy overlap of two two-sided aperture states. -/
def mobiusCriticalTwoSidedUnitHardyGram (u v : ℝ) : ℝ :=
  Real.sqrt (1 + 2 * u) * Real.sqrt (1 + 2 * v) / (1 + u + v)

/-- Exact Hellinger/Hardy defect of the normalized source curve. -/
theorem one_sub_mobiusCriticalTwoSidedUnitHardyGram
    {u v : ℝ} (hu : -(1 / 2 : ℝ) < u) (hv : -(1 / 2 : ℝ) < v) :
    1 - mobiusCriticalTwoSidedUnitHardyGram u v =
      (Real.sqrt (1 + 2 * u) - Real.sqrt (1 + 2 * v)) ^ 2 /
        (2 * (1 + u + v)) := by
  have hxu : 0 ≤ 1 + 2 * u := by linarith
  have hxv : 0 ≤ 1 + 2 * v := by linarith
  have hsu := Real.sq_sqrt hxu
  have hsv := Real.sq_sqrt hxv
  have hden : 1 + u + v ≠ 0 := by linarith
  rw [mobiusCriticalTwoSidedUnitHardyGram]
  field_simp [hden]
  nlinarith

/-- Normalized critical source overlap never exceeds one. -/
theorem mobiusCriticalTwoSidedUnitHardyGram_le_one
    {u v : ℝ} (hu : -(1 / 2 : ℝ) < u) (hv : -(1 / 2 : ℝ) < v) :
    mobiusCriticalTwoSidedUnitHardyGram u v ≤ 1 := by
  rw [← sub_nonneg]
  rw [one_sub_mobiusCriticalTwoSidedUnitHardyGram hu hv]
  exact div_nonneg (sq_nonneg _) (by linarith)

/-- Unit overlap is rigid: it occurs exactly for equal apertures. -/
theorem mobiusCriticalTwoSidedUnitHardyGram_eq_one_iff
    {u v : ℝ} (hu : -(1 / 2 : ℝ) < u) (hv : -(1 / 2 : ℝ) < v) :
    mobiusCriticalTwoSidedUnitHardyGram u v = 1 ↔ u = v := by
  constructor
  · intro hgram
    have hdef := one_sub_mobiusCriticalTwoSidedUnitHardyGram hu hv
    rw [hgram] at hdef
    have hden : 2 * (1 + u + v) ≠ 0 := by linarith
    have hsqrtSq :
        (Real.sqrt (1 + 2 * u) - Real.sqrt (1 + 2 * v)) ^ 2 = 0 := by
      have hquot :
          (Real.sqrt (1 + 2 * u) - Real.sqrt (1 + 2 * v)) ^ 2 /
              (2 * (1 + u + v)) = 0 := by
        linarith
      exact ((div_eq_zero_iff).mp hquot).resolve_right hden
    have hsqrt : Real.sqrt (1 + 2 * u) = Real.sqrt (1 + 2 * v) := by
      nlinarith
    have harg : 1 + 2 * u = 1 + 2 * v :=
      Real.sqrt_inj (by linarith) (by linarith) |>.mp hsqrt
    linarith
  · intro huv
    subst v
    rw [mobiusCriticalTwoSidedUnitHardyGram]
    have hx : 0 ≤ 1 + 2 * u := by linarith
    rw [← pow_two, Real.sq_sqrt hx]
    have hne : 1 + u + u ≠ 0 := by linarith
    field_simp [hne]
    ring

end
end RHTower.HedenmalmThetaSource
