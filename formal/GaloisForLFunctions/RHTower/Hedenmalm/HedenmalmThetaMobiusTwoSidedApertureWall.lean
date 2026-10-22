import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmThetaXiHardySymmetricSquareWeld
import GaloisForLFunctions.RHTower.MobiusCriticalFisherTangentCoefficients

/-!
# Two-sided Möbius source aperture and the half-density wall

P-G36 identifies the finite Route P channel as a critical half-density
renormalized Hardy symmetric square.  A possible rigidity mechanism would make
the source aperture reversible and contractive on both sides of the critical
state.  This module proves the exact answer instead.

The damped squarefree-Möbius source remains an actual Hilbert vector for every
`u > -1/2`, not merely for positive damping.  Its squared norm has the critical
limit

`(1 + 2u)⁻¹`.

Hence every negative aperture in the Hilbert range is strictly expansive.
Reversible raw contractivity is impossible, and `u = -1/2` is the intrinsic
half-density wall.  The positive survivor is coefficient-exact: the unique
positive critical scalar that unitarizes the raw curve is `sqrt (1 + 2u)`.
This points to a normalized source connection rather than a two-sided
contraction as the next Route P object.
-/

open Complex Filter MeasureTheory Set Topology
open scoped BigOperators

namespace RHTower.HedenmalmThetaSource

noncomputable section

/-- Squared coefficient norm is the boundary-layer summand at twice the
aperture.  The factor two is the Hilbert symmetric square. -/
theorem norm_sq_infiniteMobiusCriticalDampedSignedWeight_eq_boundaryLayer
    {sigma u : ℝ} (hsigma : 1 < sigma) (n : ℕ) :
    ‖infiniteMobiusCriticalDampedSignedWeight sigma u n‖ ^ 2 =
      squarefreeMobiusBoundaryLayerTerm sigma (2 * u) n := by
  rw [infiniteMobiusCriticalDampedSignedWeight, norm_mul, mul_pow,
    norm_infiniteMobiusSignedWeight_sq hsigma, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
    squarefreeMobiusBoundaryLayerTerm]
  by_cases hsq : Squarefree n
  · have hn : n ≠ 0 := fun hn => by subst n; exact not_squarefree_zero hsq
    have hnpos : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
    calc
      _ = squarefreeMobiusProbability sigma n *
          Real.exp (Real.log n * (-(2 * u * (sigma - 1)))) := by
        rw [mul_comm, pow_two, ← Real.exp_add]
        congr 2
        ring
      _ = _ := by rw [Real.rpow_def_of_pos hnpos]
  · simp [squarefreeMobiusProbability, squarefreeMobiusMass, hsq]

/-- The raw source is square-summable throughout the maximal open range
`u > -1/2` exposed by its shifted Dirichlet exponent. -/
theorem summable_norm_sq_infiniteMobiusCriticalDampedSignedWeight_of_negHalf_lt
    {sigma u : ℝ} (hsigma : 1 < sigma) (hu : -(1 / 2 : ℝ) < u) :
    Summable (fun n : ℕ =>
      ‖infiniteMobiusCriticalDampedSignedWeight sigma u n‖ ^ 2) := by
  have hparam : 1 < mobiusCriticalBoundaryParameter sigma (2 * u) := by
    rw [mobiusCriticalBoundaryParameter]
    nlinarith
  have hsum : Summable (fun n : ℕ =>
      squarefreeMobiusMass
          (mobiusCriticalBoundaryParameter sigma (2 * u)) n /
        squarefreeMobiusTotal sigma) :=
    (summable_squarefreeMobiusMass hparam).div_const _
  exact hsum.congr (fun n => by
    rw [norm_sq_infiniteMobiusCriticalDampedSignedWeight_eq_boundaryLayer hsigma,
      squarefreeMobiusBoundaryLayerTerm_eq])

/-- Two-sided Hilbert lift of the critical source aperture. -/
def infiniteMobiusCriticalTwoSidedDampedSignedWeightLp
    (sigma u : ℝ) (hsigma : 1 < sigma) (hu : -(1 / 2 : ℝ) < u) :
    lp (fun _ : ℕ => ℂ) 2 :=
  ⟨infiniteMobiusCriticalDampedSignedWeight sigma u,
    HilbertSchmidt.memℓp_of_sq
      (summable_norm_sq_infiniteMobiusCriticalDampedSignedWeight_of_negHalf_lt
        hsigma hu)⟩

/-- Exact finite-`sigma` norm-square ratio on the two-sided aperture. -/
theorem norm_sq_infiniteMobiusCriticalTwoSidedDampedSignedWeightLp
    {sigma u : ℝ} (hsigma : 1 < sigma) (hu : -(1 / 2 : ℝ) < u) :
    ‖infiniteMobiusCriticalTwoSidedDampedSignedWeightLp sigma u hsigma hu‖ ^ 2 =
      squarefreeMobiusTotal (mobiusCriticalBoundaryParameter sigma (2 * u)) /
        squarefreeMobiusTotal sigma := by
  rw [HilbertSchmidt.lp_norm_sq_eq]
  change (∑' n : ℕ,
    ‖infiniteMobiusCriticalDampedSignedWeight sigma u n‖ ^ 2) = _
  rw [show (fun n : ℕ =>
      ‖infiniteMobiusCriticalDampedSignedWeight sigma u n‖ ^ 2) =
      squarefreeMobiusBoundaryLayerTerm sigma (2 * u) by
    funext n
    exact norm_sq_infiniteMobiusCriticalDampedSignedWeight_eq_boundaryLayer hsigma n,
    tsum_squarefreeMobiusBoundaryLayerTerm]

private theorem tendsto_mobiusCriticalBoundaryParameter_nhdsGT
    {u : ℝ} (hu : -1 < u) :
    Tendsto (fun sigma : ℝ => mobiusCriticalBoundaryParameter sigma u)
      (𝓝[>] (1 : ℝ)) (𝓝[>] (1 : ℝ)) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · have hcont : ContinuousAt
        (fun sigma : ℝ => mobiusCriticalBoundaryParameter sigma u) 1 := by
      unfold mobiusCriticalBoundaryParameter
      fun_prop
    simpa [mobiusCriticalBoundaryParameter] using
      hcont.tendsto.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with sigma hsigma
    unfold mobiusCriticalBoundaryParameter
    change 1 < sigma at hsigma
    change 1 < sigma + u * (sigma - 1)
    have hscale : 0 < (1 + u) * (sigma - 1) :=
      mul_pos (by linarith) (by linarith)
    nlinarith

/-- Boundary-layer Laplace law extended from positive apertures to the full
Euler-safe range `u > -1`.  Negative aperture is the exact inverse of the
positive aperture `-u/(1+u)` based at the shifted boundary parameter. -/
theorem tendsto_squarefreeMobiusBoundaryLayerLaplace_of_negOne_lt
    {u : ℝ} (hu : -1 < u) :
    Tendsto (fun sigma : ℝ => squarefreeMobiusBoundaryLayerLaplace sigma u)
      (𝓝[>] (1 : ℝ)) (𝓝 ((((1 + u : ℝ) : ℂ))⁻¹)) := by
  by_cases hu0 : 0 ≤ u
  · exact tendsto_squarefreeMobiusBoundaryLayerLaplace hu0
  · have huNeg : u < 0 := lt_of_not_ge hu0
    let v : ℝ := -u / (1 + u)
    have hu1 : 0 < 1 + u := by linarith
    have hv : 0 ≤ v := by
      dsimp only [v]
      exact div_nonneg (neg_nonneg.mpr huNeg.le) hu1.le
    have hvFormula : 1 + v = 1 / (1 + u) := by
      dsimp only [v]
      field_simp [hu1.ne']
      ring
    have hv1 : 1 + v ≠ 0 := by
      rw [hvFormula]
      exact one_div_ne_zero hu1.ne'
    have hforward := tendsto_squarefreeMobiusBoundaryLayerLaplace hv
    have hparam := tendsto_mobiusCriticalBoundaryParameter_nhdsGT hu
    have hcomp := hforward.comp hparam
    have htarget : ((((1 + v : ℝ) : ℂ))⁻¹) ≠ 0 :=
      inv_ne_zero (by exact_mod_cast hv1)
    have hinv := hcomp.inv₀ htarget
    have hlimit :
        (((((1 + v : ℝ) : ℂ))⁻¹)⁻¹) = ((((1 + u : ℝ) : ℂ))⁻¹) := by
      rw [inv_inv, ← Complex.ofReal_inv]
      exact congrArg Complex.ofReal (by simpa [one_div] using hvFormula)
    rw [← hlimit]
    refine hinv.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with sigma hsigma
    change 1 < sigma at hsigma
    have hparamGt : 1 < mobiusCriticalBoundaryParameter sigma u := by
      rw [mobiusCriticalBoundaryParameter]
      have hscale : 0 < (1 + u) * (sigma - 1) :=
        mul_pos hu1 (by linarith)
      nlinarith
    have hsigTotal : squarefreeMobiusTotal sigma ≠ 0 :=
      (squarefreeMobiusTotal_pos hsigma).ne'
    have hparamTotal :
        squarefreeMobiusTotal (mobiusCriticalBoundaryParameter sigma u) ≠ 0 :=
      (squarefreeMobiusTotal_pos hparamGt).ne'
    have hreturn :
        mobiusCriticalBoundaryParameter
            (mobiusCriticalBoundaryParameter sigma u) v = sigma := by
      dsimp only [v]
      rw [mobiusCriticalBoundaryParameter, mobiusCriticalBoundaryParameter]
      field_simp [hu1.ne']
      ring
    simp only [Function.comp_apply, squarefreeMobiusBoundaryLayerLaplace, hreturn]
    field_simp [hsigTotal, hparamTotal]

/-- **P-G37 half-density law.** The two-sided Hilbert source has critical
norm-square `(1 + 2u)⁻¹`. -/
theorem tendsto_norm_sq_infiniteMobiusCriticalTwoSidedDampedSignedWeightLp
    {u : ℝ} (hu : -(1 / 2 : ℝ) < u) :
    Tendsto (fun sigma : ℝ =>
      if hsigma : 1 < sigma then
        ‖infiniteMobiusCriticalTwoSidedDampedSignedWeightLp sigma u hsigma hu‖ ^ 2
      else 0)
      (𝓝[>] (1 : ℝ)) (𝓝 ((1 + 2 * u)⁻¹)) := by
  have h2u : -1 < 2 * u := by linarith
  have hcomplex :=
    tendsto_squarefreeMobiusBoundaryLayerLaplace_of_negOne_lt h2u
  have hreal := Complex.continuous_re.continuousAt.tendsto.comp hcomplex
  have hlimitRe : ((((1 + 2 * u : ℝ) : ℂ))⁻¹).re = (1 + 2 * u)⁻¹ := by
    rw [← Complex.ofReal_inv]
    rfl
  rw [← hlimitRe]
  refine hreal.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with sigma hsigma
  change 1 < sigma at hsigma
  rw [dif_pos hsigma,
    norm_sq_infiniteMobiusCriticalTwoSidedDampedSignedWeightLp hsigma hu]
  simp only [Function.comp_apply, squarefreeMobiusBoundaryLayerLaplace]
  rw [← Complex.ofReal_div]
  rfl

/-- Every negative aperture before the half-density wall is asymptotically
strictly expansive, ruling out a reversible raw contraction. -/
theorem tendsto_norm_sq_twoSidedDamped_gt_one_of_negative
    {u : ℝ} (huLower : -(1 / 2 : ℝ) < u) (huUpper : u < 0) :
    Tendsto (fun sigma : ℝ =>
      if hsigma : 1 < sigma then
        ‖infiniteMobiusCriticalTwoSidedDampedSignedWeightLp sigma u hsigma huLower‖ ^ 2
      else 0)
      (𝓝[>] (1 : ℝ)) (𝓝 ((1 + 2 * u)⁻¹)) ∧
      1 < (1 + 2 * u)⁻¹ := by
  refine ⟨tendsto_norm_sq_infiniteMobiusCriticalTwoSidedDampedSignedWeightLp huLower, ?_⟩
  rw [one_lt_inv₀] <;> linarith

end

end RHTower.HedenmalmThetaSource
