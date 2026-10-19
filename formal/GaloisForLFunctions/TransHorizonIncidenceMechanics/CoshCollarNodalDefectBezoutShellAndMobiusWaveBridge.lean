import GaloisForLFunctions.BiScaleUncertainty.StationaryResolventMarkovPositivityAndNodalDefectProducer
import GaloisForLFunctions.BezoutValuationIncidence.ArbitraryDepthBezoutShellsAndRoutePMSecondLayerProfile
import GaloisForLFunctions.BezoutValuationIncidence.ReturnWindowTwoMomentKernelsAndSharpZeroBlocks
import GaloisForLFunctions.RHTower.CHMDLightConeFoldTailBound
import GaloisForLFunctions.TransHorizonIncidenceMechanics.PolarRadicalInvarianceNodalDriftAndFermiGradientBridge
import GaloisForLFunctions.TransHorizonIncidenceMechanics.PronicCausalQuadratureInteriorSawtoothAndFermiGramBridge

/-!
# `cosh(x/2)`-Collar Ground-Potential Confinement, Common Nodal Defect Graph, Arbitrary-Depth Bézout Shell Factorization, and Folded Möbius Klein–Gordon Transport Bridge

This module synthesizes four major families of unconditional theorems from the broader corpus
(`BiScaleUncertainty`, `BezoutValuationIncidence`, and `RHTower.CHMDChebyshevTransport`) with the
Trans-Horizon Incidence Mechanics (THIM) programme:

1. **`cosh(x/2)`-Collar Ground-Potential Confinement, Odd-Sector Half-Mass Five-Term Collar Balance,
   and Chiral-Drift Collar Bound (§1)**:
   - `abs_thetaGroundPotential_le_div_cosh`, `riemannKernelReal_le_of_abs_le`,
     `inv_cosh_le_inv_cosh_add_theta_div_cosh`, `abs_inner_groundPotentialOperator_self_le_collar_split`,
     and `norm_sq_sub_groundPotential_le_collar_split`:
     Sharpens the uniform ground-potential bound `|thetaGroundPotential x| ≤ thetaGroundPotentialBound`
     by retaining the exact `Real.cosh (x / 2)` denominator and combining it with the even strict
     antitonicity of `riemannKernelReal` on `[0, ∞)` (`strictAntiOn_riemannKernelReal_Ici`) to bound
     `|⟪groundPotentialOperator u, u⟫_ℝ|`, `‖u‖ ^ 2 - ⟪groundPotentialOperator u, u⟫_ℝ`, and
     `⟪primeDiagonalOperator u, u⟫_ℝ` by explicit collar-vs.-far-field splits at any radius `0 ≤ R`.
   - `odd_eigenvector_posGraph_and_negGraph_five_term_jump_le_half_collar_split`:
     Combines the `cosh(R / 2)` collar-vs.-far-field splitting of `groundPotentialOperator` with
     THIM's odd-sector half-mass lobe law (`norm_posGraph_and_negGraph_fst_sq_eq_half_of_odd`):
     for every odd eigenvector `resolvent w = μ • w` (`μ ≠ 0`, `reflectMass w = -w`) with
     `q = rieszLift w` and every collar radius `0 ≤ R`, the five-term nonnegative positive-lobe and
     negative-lobe jump sums are bounded above by
     `((1 + thetaGroundPotentialBound / Real.cosh (R / 2)) / 2) * ‖q.val.fst‖ ^ 2 + (thetaGroundPotentialBound / riemannKernelReal R) * ‖thetaToVolume (posGraph q).val.fst‖ ^ 2`
     (and symmetrically for `negGraph q`).
   - `odd_posGraph_primeShift_sq_add_quarter_drift_sq_le_collar_split`:
     Combines the odd-sector joint Pythagorean inequality for `primeShiftOperator` and the chiral
     `oddPrimeDriftOperator` (`odd_posGraph_and_negGraph_primeShift_sq_add_quarter_absGraph_drift_sq_le`)
     with the `cosh(R / 2)` collar-split bound on `primeDiagonalOperator`, bounding
     `⟪primeShiftOperator (posGraph p).val.fst, (posGraph p).val.fst⟫_ℝ ^ 2 + (1 / 4) * ⟪oddPrimeDriftOperator p.val.fst, (absGraph p).val.fst⟫_ℝ ^ 2`
     by the squared `cosh(R / 2)` collar-split upper bound for every odd `p : SourceGraph` and `0 ≤ R`.

2. **Common Nodal Defect Graph `nodalDefectGraph`, Markov Sub-Invariance, Odd-Sector Balanced-Nodal
   Coincidence, and Collar Criteria for `RiemannHypothesis` (§2)**:
   - `odd_eigenvector_nodalDefectGraph_subinvariance_and_bilateral_cs`:
     For any odd eigenvector `resolvent w = μ • w` with `0 < μ ≤ 1`, `reflectMass w = -w`, and
     `q = rieszLift w`, packages the common nodal defect graph identity
     `nodalDefectGraph μ q = stationaryGraphLift (stationaryCollarPotential μ (negGraph q).val.fst) - negGraph q`,
     its a.e. nonnegativity `0 ≤ᵐ[massMeasure] (nodalDefectGraph μ q).val.fst`, the pointwise lobe
     Markov sub-invariance inequalities for `(posGraph q).val.fst` and `(negGraph q).val.fst`, and
     the bilateral `stationaryGroundGraph` Cauchy–Schwarz lower bound.
   - `balancedNodalGraph_eq_half_norm_sq_smul_absGraph_of_odd`:
     For every odd graph vector `p : SourceGraph` (`reflectGraph p = -p`),
     `balancedNodalGraph p = ((1 / 2) * ‖p.val.fst‖ ^ 2) • absGraph p` and
     `primGraph (balancedNodalGraph p) = ((1 / 2) * ‖p.val.fst‖ ^ 2) • primGraph (absGraph p)`.
   - `eigenvalue_le_one_half_of_four_term_posGraph_ge_groundPotential`,
     `riemannHypothesis_of_odd_eigenvector_four_term_posGraph_ge_groundPotential`, and
     `riemannHypothesis_of_odd_eigenvector_four_term_posGraph_ge_collar_split`:
     Combine THIM's odd-sector spectral equivalence
     `not_riemannHypothesis_iff_exists_odd_eigenvector_mem_Ioo_half_one` with the positive-lobe
     four-term jump excess criteria.

3. **Arbitrary-Depth (`r ≥ 1`) Bézout Shell Observation-State Factorization, Iso-State `(2r - 1)`-Step
   Annihilation, and Common-Return Two-Moment Kernel Bridge (§3)**:
   - `bezoutLayerActiveSawtoothSum_horizonObservationState` and
     `bezoutLayerActiveSawtoothSum_eq_of_horizonObservationState_eq`:
     For every depth `r ≥ 1`, cutoff `N : ℕ`, and weight `c : ℕ → ℝ`, the `r`-th Bézout layer active
     sawtooth sum `bezoutLayerActiveSawtoothSum r N c` factors identically through THIM's finite
     multiplicative observation state `horizonObservationState N`.
   - `sum_range_bezoutLayerActiveSawtoothSum_sub_add_eq_zero_of_isoState`:
     Generalizing the depth-`1` and depth-`2` iso-state annihilation laws to arbitrary Bézout shell
     depth `r ≥ 1` (width `2 * r - 1`), proves that whenever the initial and terminal `(2 * r - 1)`-tuples
     of `horizonObservationState N` match across a shifted window `[M₀, M₀ + M)`, the `(2 * r - 1)`-step
     difference sum of `bezoutLayerActiveSawtoothSum r N c` vanishes identically.
   - `pmSecondLayer_and_returnWindow_two_moment_bridge`:
     Unifies the cutoff-independent Route PM second-layer decomposition
     (`pmPowerDampedCenteredDivisorPrefix_eq_first_and_second_layer_add_fourStep`,
     `secondLayerActiveSawtoothSum_pmPowerDampedRealWeight_eq`) with the common-return two-moment
     kernel classification (`sieveReturnWindow_two_moment_kernel`) and sharp `2N - 3` variance
     detection (`sieveReturnWindow_sharp_detection`).

4. **Folded Möbius Klein–Gordon Prime-Wave Transport & Light-Cone Rapidity Tail Bridge (§4)**:
   - `kleinGordon_chebyshev_transport_mobius_three_piece_and_lightCone_bridge`:
     Unifies the von-Mangoldt-free folded Möbius three-piece decomposition of the Klein–Gordon
     Chebyshev discrepancy transport (`chebyshevDiscrepancyTransport_eq_mobius_pieces`,
     `mobiusFold_eq`, `abs_remainderFold_le`), the order-one light-cone Bessel bound
     `|lightConeBesselReal w| ≤ 1` (`abs_lightConeBesselReal_nonneg_le_one`), the quantitative
     cutoff-and-rapidity tail bound `C * foldRapidityEnvelope y * N ^ (-(π - 3 / 2))`
     (`exists_tsum_abs_mobiusFold_tail_le_rapidity_envelope`), and the one-sided boundedness
     equivalences for `RiemannHypothesis` (`riemannHypothesis_iff_mobius_pieces_bddAbove`,
     `riemannHypothesis_iff_mobius_pieces_bddBelow`).
-/

open Complex MeasureTheory Set Filter Topology Finset
open scoped BigOperators InnerProductSpace Real

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics

open GaloisForLFunctions.BiScaleUncertainty
open GaloisForLFunctions.BezoutValuationIncidence
open GaloisForLFunctions.NymanMellin
open GaloisForLFunctions.HTGeometry
open _root_.RHTower
open _root_.RHTower.Sieve
open _root_.RHTower.CHMDDoobGraph
open _root_.RHTower.CHMDClosedJump
open _root_.RHTower.CHMDTranslation
open _root_.RHTower.ThetaSourceWard
open _root_.RHTower.CHMDPolar
open _root_.RHTower.CHMDLightCone
open _root_.RHTower.CHMDStage22
open _root_.RHTower.CHMDQuarticMoment
open _root_.RHTower.CHMDLightConeBesselZero
open _root_.RHTower.CHMDChebyshevTransport

noncomputable section

/-! ## §1. `cosh(x/2)`-Collar Ground-Potential Confinement, Odd-Sector Half-Mass Five-Term Collar Balance, and Chiral-Drift Collar Bound -/

/-- Uniform bound on the numerator integral of `thetaGroundPotential x` before dividing by
`Real.cosh (x / 2)`:
`|∫ t in Ioi 0, archLevyDensity t * thetaSecondDifference t x| ≤ thetaGroundPotentialBound`. -/
theorem abs_integral_thetaSecondDifference_kernel_le (x : ℝ) :
    |∫ t in Ioi (0 : ℝ), archLevyDensity t * thetaSecondDifference t x| ≤
      thetaGroundPotentialBound := by
  have hn := norm_integral_le_of_norm_le
    (integrableOn_mul_archLevyDensity.const_mul (2 * (thetaLipConstant : ℝ)))
    ((ae_restrict_mem measurableSet_Ioi).mono fun t ht => norm_thetaSecondDifference_kernel_le ht x)
  rw [integral_const_mul, Real.norm_eq_abs] at hn
  exact hn

/-- **Exponentially Decaying `cosh(x / 2)` Pointwise Bound on `thetaGroundPotential`**:
for every `x : ℝ`,
`|thetaGroundPotential x| ≤ thetaGroundPotentialBound / Real.cosh (x / 2)`. -/
theorem abs_thetaGroundPotential_le_div_cosh (x : ℝ) :
    |thetaGroundPotential x| ≤ thetaGroundPotentialBound / Real.cosh (x / 2) := by
  unfold thetaGroundPotential
  rw [abs_div, abs_of_pos (Real.cosh_pos (x / 2))]
  exact div_le_div_of_nonneg_right (abs_integral_thetaSecondDifference_kernel_le x)
    (Real.cosh_pos (x / 2)).le

/-- **Explicit Collar Minimum of `riemannKernelReal`**:
because `riemannKernelReal` is even (`riemannKernelReal_abs`) and strictly antitone on `[0, ∞)`
(`strictAntiOn_riemannKernelReal_Ici`), its minimum on `[-R, R]` is attained at `±R`:
for every `x : ℝ` with `|x| ≤ R`, `riemannKernelReal R ≤ riemannKernelReal x`. -/
theorem riemannKernelReal_le_of_abs_le {R x : ℝ} (hx : |x| ≤ R) :
    riemannKernelReal R ≤ riemannKernelReal x := by
  have hR0 : 0 ≤ R := (abs_nonneg x).trans hx
  rw [← riemannKernelReal_abs x]
  exact strictAntiOn_riemannKernelReal_Ici.antitoneOn
    (mem_Ici.mpr (abs_nonneg x)) (mem_Ici.mpr hR0) hx

/-- **Pointwise Collar-vs.-Far-Field Decomposition of `1 / Real.cosh (x / 2)`**:
for every `0 ≤ R` and `x : ℝ`,
`1 / Real.cosh (x / 2) ≤ 1 / Real.cosh (R / 2) + (1 / riemannKernelReal R) * (riemannKernelReal x / Real.cosh (x / 2))`. -/
theorem inv_cosh_le_inv_cosh_add_theta_div_cosh {R : ℝ} (hR : 0 ≤ R) (x : ℝ) :
    1 / Real.cosh (x / 2) ≤
      1 / Real.cosh (R / 2) +
        (1 / riemannKernelReal R) * (riemannKernelReal x / Real.cosh (x / 2)) := by
  have hθR : 0 < riemannKernelReal R := riemannKernelReal_pos R
  have hθx : 0 < riemannKernelReal x := riemannKernelReal_pos x
  have hchx : 0 < Real.cosh (x / 2) := Real.cosh_pos (x / 2)
  have hchR : 0 < Real.cosh (R / 2) := Real.cosh_pos (R / 2)
  by_cases hx : |x| ≤ R
  · have hle : riemannKernelReal R ≤ riemannKernelReal x := riemannKernelReal_le_of_abs_le hx
    have h1 : 1 ≤ riemannKernelReal x / riemannKernelReal R := (one_le_div hθR).mpr hle
    have h2 : 1 / Real.cosh (x / 2) ≤
        (1 / riemannKernelReal R) * (riemannKernelReal x / Real.cosh (x / 2)) := by
      calc 1 / Real.cosh (x / 2)
          = 1 * (1 / Real.cosh (x / 2)) := by ring
        _ ≤ (riemannKernelReal x / riemannKernelReal R) * (1 / Real.cosh (x / 2)) :=
            mul_le_mul_of_nonneg_right h1 (by positivity)
        _ = (1 / riemannKernelReal R) * (riemannKernelReal x / Real.cosh (x / 2)) := by ring
    have h3 : 0 ≤ 1 / Real.cosh (R / 2) := by positivity
    linarith
  · push Not at hx
    have hcosh : Real.cosh (R / 2) ≤ Real.cosh (x / 2) := by
      rw [Real.cosh_le_cosh, abs_div, abs_div, abs_of_nonneg hR, abs_two]
      exact div_le_div_of_nonneg_right hx.le (by norm_num)
    have h1 : 1 / Real.cosh (x / 2) ≤ 1 / Real.cosh (R / 2) :=
      one_div_le_one_div_of_le hchR hcosh
    have h2 : 0 ≤ (1 / riemannKernelReal R) * (riemannKernelReal x / Real.cosh (x / 2)) := by
      positivity
    linarith

/-- Pointwise collar-vs.-far-field upper bound on `|thetaGroundPotential x|`. -/
theorem abs_thetaGroundPotential_le_collar_split {R : ℝ} (hR : 0 ≤ R) (x : ℝ) :
    |thetaGroundPotential x| ≤
      thetaGroundPotentialBound / Real.cosh (R / 2) +
        (thetaGroundPotentialBound / (archGroundConstant * riemannKernelReal R)) *
          (archGroundConstant * riemannKernelReal x / Real.cosh (x / 2)) := by
  have hc_pos : 0 < archGroundConstant := archGroundConstant_pos
  have hθR : 0 < riemannKernelReal R := riemannKernelReal_pos R
  have hB : 0 ≤ thetaGroundPotentialBound := thetaGroundPotentialBound_nonneg
  have h1 := abs_thetaGroundPotential_le_div_cosh x
  have h2 := mul_le_mul_of_nonneg_left (inv_cosh_le_inv_cosh_add_theta_div_cosh hR x) hB
  have hrew : thetaGroundPotentialBound *
      (1 / Real.cosh (R / 2) +
        (1 / riemannKernelReal R) * (riemannKernelReal x / Real.cosh (x / 2))) =
      thetaGroundPotentialBound / Real.cosh (R / 2) +
        (thetaGroundPotentialBound / (archGroundConstant * riemannKernelReal R)) *
          (archGroundConstant * riemannKernelReal x / Real.cosh (x / 2)) := by
    field_simp [hc_pos.ne', hθR.ne', (Real.cosh_pos (R / 2)).ne', (Real.cosh_pos (x / 2)).ne']
  rw [div_eq_mul_one_div] at h1
  exact h1.trans (by linarith [h2, hrew])

private theorem archDiagonalOperator_ae_mass (u : MassSpace) :
    archDiagonalOperator u =ᵐ[massMeasure]
      fun x => (archGroundConstant * riemannKernelReal x / Real.cosh (x / 2)) * u x := by
  have heq : archDiagonalOperator u =
      u - groundPotentialOperator u - primeDiagonalOperator u := by
    have h := congrArg (fun T : MassSpace →L[ℝ] MassSpace => T u) sub_groundPotentialOperator_eq
    change u - groundPotentialOperator u = primeDiagonalOperator u + archDiagonalOperator u at h
    exact eq_sub_of_add_eq' h.symm
  rw [heq]
  filter_upwards [Lp.coeFn_sub (u - groundPotentialOperator u) (primeDiagonalOperator u),
    Lp.coeFn_sub u (groundPotentialOperator u),
    groundPotentialOperator_ae u, primeDiagonalOperator_ae u] with x hx1 hx2 hg hp
  simp only [Pi.sub_apply] at hx1 hx2
  rw [hx1, hx2, hg, hp, thetaGroundPotential_eq_harmonic x]
  unfold primeDiagonalPotential
  ring

private theorem integrable_archDiagonal_sq_mass (u : MassSpace) :
    Integrable (fun x => (archGroundConstant * riemannKernelReal x / Real.cosh (x / 2)) * u x ^ 2)
      massMeasure := by
  refine (L2.integrable_inner (archDiagonalOperator u) u).congr ?_
  filter_upwards [archDiagonalOperator_ae_mass u] with x hx
  simp only [hx, RCLike.inner_apply', conj_trivial]
  ring

private theorem integral_archDiagonal_sq_mass (u : MassSpace) :
    (∫ x, (archGroundConstant * riemannKernelReal x / Real.cosh (x / 2)) * u x ^ 2 ∂massMeasure) =
      archGroundConstant * ‖thetaToVolume u‖ ^ 2 := by
  rw [← inner_archDiagonalOperator_self, inner_archDiagonalOperator_eq_mass]
  apply integral_congr_ae
  filter_upwards [] with x
  ring

/-- **Explicit Collar-vs.-Far-Field Bound on `groundPotentialOperator`**:
for every collar radius `0 ≤ R` and every `u : MassSpace`,
`|⟪groundPotentialOperator u, u⟫_ℝ| ≤ (thetaGroundPotentialBound / Real.cosh (R / 2)) * ‖u‖ ^ 2 + (thetaGroundPotentialBound / riemannKernelReal R) * ‖thetaToVolume u‖ ^ 2`. -/
theorem abs_inner_groundPotentialOperator_self_le_collar_split {R : ℝ} (hR : 0 ≤ R)
    (u : MassSpace) :
    |⟪groundPotentialOperator u, u⟫_ℝ| ≤
      (thetaGroundPotentialBound / Real.cosh (R / 2)) * ‖u‖ ^ 2 +
        (thetaGroundPotentialBound / riemannKernelReal R) * ‖thetaToVolume u‖ ^ 2 := by
  have hc_pos : 0 < archGroundConstant := archGroundConstant_pos
  have hθR : 0 < riemannKernelReal R := riemannKernelReal_pos R
  have hint_g0 : Integrable (fun x => thetaGroundPotential x * u x ^ 2) massMeasure := by
    refine (L2.integrable_inner (groundPotentialOperator u) u).congr ?_
    filter_upwards [groundPotentialOperator_ae u] with x hx
    simp only [hx, RCLike.inner_apply', conj_trivial]
    ring
  have hint_g : Integrable (fun x => |thetaGroundPotential x * u x ^ 2|) massMeasure :=
    hint_g0.abs
  have hint_u : Integrable (fun x => u x ^ 2) massMeasure := by
    refine (L2.integrable_inner u u).congr ?_
    filter_upwards [] with x
    simp [pow_two]
  have hu_eq : (∫ x, u x ^ 2 ∂massMeasure) = ‖u‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [] with x
    simp [pow_two]
  have hint_rhs := (hint_u.const_mul (thetaGroundPotentialBound / Real.cosh (R / 2))).add
    ((integrable_archDiagonal_sq_mass u).const_mul
      (thetaGroundPotentialBound / (archGroundConstant * riemannKernelReal R)))
  have h1 : |⟪groundPotentialOperator u, u⟫_ℝ| ≤
      ∫ x, |thetaGroundPotential x * u x ^ 2| ∂massMeasure := by
    rw [inner_groundPotentialOperator_self, ← Real.norm_eq_abs]
    exact norm_integral_le_integral_norm _
  have h2 : (∫ x, |thetaGroundPotential x * u x ^ 2| ∂massMeasure) ≤
      ∫ x, ((thetaGroundPotentialBound / Real.cosh (R / 2)) * u x ^ 2 +
        (thetaGroundPotentialBound / (archGroundConstant * riemannKernelReal R)) *
          ((archGroundConstant * riemannKernelReal x / Real.cosh (x / 2)) * u x ^ 2))
        ∂massMeasure := by
    refine integral_mono hint_g hint_rhs fun x => ?_
    rw [abs_mul, abs_of_nonneg (sq_nonneg (u x))]
    have hpt := mul_le_mul_of_nonneg_right (abs_thetaGroundPotential_le_collar_split hR x)
      (sq_nonneg (u x))
    linarith
  rw [integral_add (hint_u.const_mul _) ((integrable_archDiagonal_sq_mass u).const_mul _),
    integral_const_mul, integral_const_mul, hu_eq, integral_archDiagonal_sq_mass] at h2
  have hsimp : (thetaGroundPotentialBound / (archGroundConstant * riemannKernelReal R)) *
      (archGroundConstant * ‖thetaToVolume u‖ ^ 2) =
      (thetaGroundPotentialBound / riemannKernelReal R) * ‖thetaToVolume u‖ ^ 2 := by
    field_simp [hc_pos.ne', hθR.ne']
  linarith [h1, h2, hsimp]

/-- **Explicit Collar-vs.-Far-Field Upper Bounds on `‖u‖ ^ 2 - ⟪groundPotentialOperator u, u⟫_ℝ`
and `⟪primeDiagonalOperator u, u⟫_ℝ`**:
for every `0 ≤ R` and `u : MassSpace`,
`‖u‖ ^ 2 - ⟪groundPotentialOperator u, u⟫_ℝ ≤ (1 + thetaGroundPotentialBound / Real.cosh (R / 2)) * ‖u‖ ^ 2 + (thetaGroundPotentialBound / riemannKernelReal R) * ‖thetaToVolume u‖ ^ 2`
and
`⟪primeDiagonalOperator u, u⟫_ℝ ≤ (1 + thetaGroundPotentialBound / Real.cosh (R / 2)) * ‖u‖ ^ 2 + (thetaGroundPotentialBound / riemannKernelReal R - archGroundConstant) * ‖thetaToVolume u‖ ^ 2`. -/
theorem norm_sq_sub_groundPotential_le_collar_split {R : ℝ} (hR : 0 ≤ R) (u : MassSpace) :
    ‖u‖ ^ 2 - ⟪groundPotentialOperator u, u⟫_ℝ ≤
      (1 + thetaGroundPotentialBound / Real.cosh (R / 2)) * ‖u‖ ^ 2 +
        (thetaGroundPotentialBound / riemannKernelReal R) * ‖thetaToVolume u‖ ^ 2 ∧
    ⟪primeDiagonalOperator u, u⟫_ℝ ≤
      (1 + thetaGroundPotentialBound / Real.cosh (R / 2)) * ‖u‖ ^ 2 +
        (thetaGroundPotentialBound / riemannKernelReal R - archGroundConstant) *
          ‖thetaToVolume u‖ ^ 2 := by
  have h1 := neg_le_of_abs_le (abs_inner_groundPotentialOperator_self_le_collar_split hR u)
  have h2 := arch_add_primeDiagonal_eq_norm_sq_sub_groundPotential u
  exact ⟨by linarith, by linarith⟩

/-- Collar-split upper bound on the five-term jump sum of `posGraph (rieszLift w)`. -/
theorem posGraph_five_term_jump_le_collar_split_of_eigenvector
    {μ : ℝ} (hμ : μ ≠ 0) {w : MassSpace} (heig : resolvent w = μ • w)
    {R : ℝ} (hR : 0 ≤ R) :
    let q := rieszLift w
    stationaryEnergy (thetaProduct (posGraph q).val.fst) +
        ⟪primeGenerator (posGraph q).val.fst, (posGraph q).val.fst⟫_ℝ -
        ⟪(fullGroundEquiv (posGraph q)).val.snd, (fullGroundEquiv (negGraph q)).val.snd⟫_ℝ +
        ⟪primeShiftOperator (posGraph q).val.fst, (negGraph q).val.fst⟫_ℝ +
        ((2 * μ - 1) / μ) * ‖(posGraph q).val.fst‖ ^ 2 ≤
      (1 + thetaGroundPotentialBound / Real.cosh (R / 2)) *
          ‖(posGraph q).val.fst‖ ^ 2 +
        (thetaGroundPotentialBound / riemannKernelReal R) *
          ‖thetaToVolume (posGraph q).val.fst‖ ^ 2 := by
  intro q
  have h1 := posGraph_five_term_jump_eq_diagonals_of_eigenvector hμ heig
  have h2 := arch_add_primeDiagonal_eq_norm_sq_sub_groundPotential (posGraph q).val.fst
  have h3 := (norm_sq_sub_groundPotential_le_collar_split hR (posGraph q).val.fst).1
  linarith

/-- Collar-split upper bound on the five-term jump sum of `negGraph (rieszLift w)`. -/
theorem negGraph_five_term_jump_le_collar_split_of_eigenvector
    {μ : ℝ} (hμ : μ ≠ 0) {w : MassSpace} (heig : resolvent w = μ • w)
    {R : ℝ} (hR : 0 ≤ R) :
    let q := rieszLift w
    stationaryEnergy (thetaProduct (negGraph q).val.fst) +
        ⟪primeGenerator (negGraph q).val.fst, (negGraph q).val.fst⟫_ℝ -
        ⟪(fullGroundEquiv (posGraph q)).val.snd, (fullGroundEquiv (negGraph q)).val.snd⟫_ℝ +
        ⟪primeShiftOperator (posGraph q).val.fst, (negGraph q).val.fst⟫_ℝ +
        ((2 * μ - 1) / μ) * ‖(negGraph q).val.fst‖ ^ 2 ≤
      (1 + thetaGroundPotentialBound / Real.cosh (R / 2)) *
          ‖(negGraph q).val.fst‖ ^ 2 +
        (thetaGroundPotentialBound / riemannKernelReal R) *
          ‖thetaToVolume (negGraph q).val.fst‖ ^ 2 := by
  intro q
  have h1 := negGraph_five_term_jump_eq_diagonals_of_eigenvector hμ heig
  have h2 := arch_add_primeDiagonal_eq_norm_sq_sub_groundPotential (negGraph q).val.fst
  have h3 := (norm_sq_sub_groundPotential_le_collar_split hR (negGraph q).val.fst).1
  linarith

/-- **Odd-Sector Half-Mass `cosh(R/2)` Collar-Split Bound on the Five-Term Lobe Jump Sums
(`odd_eigenvector_posGraph_and_negGraph_five_term_jump_le_half_collar_split`):**
For every odd eigenvector `resolvent w = μ • w` (`μ ≠ 0`, `reflectMass w = -w`) with
`q = rieszLift w` and every collar radius `0 ≤ R`:
1. the five-term nonnegative positive-lobe jump sum is bounded above by
   `((1 + thetaGroundPotentialBound / Real.cosh (R / 2)) / 2) * ‖q.val.fst‖ ^ 2 + (thetaGroundPotentialBound / riemannKernelReal R) * ‖thetaToVolume (posGraph q).val.fst‖ ^ 2`,
2. the five-term nonnegative negative-lobe jump sum is bounded above by
   `((1 + thetaGroundPotentialBound / Real.cosh (R / 2)) / 2) * ‖q.val.fst‖ ^ 2 + (thetaGroundPotentialBound / riemannKernelReal R) * ‖thetaToVolume (negGraph q).val.fst‖ ^ 2`. -/
theorem odd_eigenvector_posGraph_and_negGraph_five_term_jump_le_half_collar_split
    {μ : ℝ} (hμ : μ ≠ 0) {w : MassSpace} (hodd : reflectMass w = -w)
    (heig : resolvent w = μ • w) {R : ℝ} (hR : 0 ≤ R) :
    let q := rieszLift w
    stationaryEnergy (thetaProduct (posGraph q).val.fst) +
        ⟪primeGenerator (posGraph q).val.fst, (posGraph q).val.fst⟫_ℝ -
        ⟪(fullGroundEquiv (posGraph q)).val.snd, (fullGroundEquiv (negGraph q)).val.snd⟫_ℝ +
        ⟪primeShiftOperator (posGraph q).val.fst, (negGraph q).val.fst⟫_ℝ +
        ((2 * μ - 1) / μ) * ((1 / 2 : ℝ) * ‖q.val.fst‖ ^ 2) ≤
      ((1 + thetaGroundPotentialBound / Real.cosh (R / 2)) / 2) * ‖q.val.fst‖ ^ 2 +
        (thetaGroundPotentialBound / riemannKernelReal R) *
          ‖thetaToVolume (posGraph q).val.fst‖ ^ 2 ∧
    stationaryEnergy (thetaProduct (negGraph q).val.fst) +
        ⟪primeGenerator (negGraph q).val.fst, (negGraph q).val.fst⟫_ℝ -
        ⟪(fullGroundEquiv (posGraph q)).val.snd, (fullGroundEquiv (negGraph q)).val.snd⟫_ℝ +
        ⟪primeShiftOperator (posGraph q).val.fst, (negGraph q).val.fst⟫_ℝ +
        ((2 * μ - 1) / μ) * ((1 / 2 : ℝ) * ‖q.val.fst‖ ^ 2) ≤
      ((1 + thetaGroundPotentialBound / Real.cosh (R / 2)) / 2) * ‖q.val.fst‖ ^ 2 +
        (thetaGroundPotentialBound / riemannKernelReal R) *
          ‖thetaToVolume (negGraph q).val.fst‖ ^ 2 := by
  intro q
  have hq_odd : reflectGraph q = -q := (odd_eigenvector_lobe_energy_and_snd_sq hμ hodd heig).1
  obtain ⟨hpos_sq, hneg_sq⟩ := norm_posGraph_and_negGraph_fst_sq_eq_half_of_odd hq_odd
  have hp := posGraph_five_term_jump_le_collar_split_of_eigenvector hμ heig hR
  have hn := negGraph_five_term_jump_le_collar_split_of_eigenvector hμ heig hR
  change _ ≤ _ at hp hn
  rw [hpos_sq] at hp
  rw [hneg_sq] at hn
  exact ⟨by linarith, by linarith⟩

/-- **Odd-Sector Chiral-Drift and Positive-Lobe Prime-Shift `cosh(R/2)` Collar Bound
(`odd_posGraph_primeShift_sq_add_quarter_drift_sq_le_collar_split`):**
For every odd graph vector `p : SourceGraph` (`reflectGraph p = -p`) and every collar radius
`0 ≤ R`:
1. `⟪primeDiagonalOperator (posGraph p).val.fst, (posGraph p).val.fst⟫_ℝ ≤ ((1 + thetaGroundPotentialBound / Real.cosh (R / 2)) / 2) * ‖p.val.fst‖ ^ 2 + (thetaGroundPotentialBound / riemannKernelReal R - archGroundConstant) * ‖thetaToVolume (posGraph p).val.fst‖ ^ 2`,
2. `⟪primeShiftOperator (posGraph p).val.fst, (posGraph p).val.fst⟫_ℝ ^ 2 + (1 / 4) * ⟪oddPrimeDriftOperator p.val.fst, (absGraph p).val.fst⟫_ℝ ^ 2 ≤ (((1 + thetaGroundPotentialBound / Real.cosh (R / 2)) / 2) * ‖p.val.fst‖ ^ 2 + (thetaGroundPotentialBound / riemannKernelReal R - archGroundConstant) * ‖thetaToVolume (posGraph p).val.fst‖ ^ 2) ^ 2`. -/
theorem odd_posGraph_primeShift_sq_add_quarter_drift_sq_le_collar_split
    {p : SourceGraph} (hp : reflectGraph p = -p) {R : ℝ} (hR : 0 ≤ R) :
    ⟪primeDiagonalOperator (posGraph p).val.fst, (posGraph p).val.fst⟫_ℝ ≤
        ((1 + thetaGroundPotentialBound / Real.cosh (R / 2)) / 2) * ‖p.val.fst‖ ^ 2 +
          (thetaGroundPotentialBound / riemannKernelReal R - archGroundConstant) *
            ‖thetaToVolume (posGraph p).val.fst‖ ^ 2 ∧
      ⟪primeShiftOperator (posGraph p).val.fst, (posGraph p).val.fst⟫_ℝ ^ 2 +
          (1 / 4 : ℝ) * ⟪oddPrimeDriftOperator p.val.fst, (absGraph p).val.fst⟫_ℝ ^ 2 ≤
        (((1 + thetaGroundPotentialBound / Real.cosh (R / 2)) / 2) * ‖p.val.fst‖ ^ 2 +
          (thetaGroundPotentialBound / riemannKernelReal R - archGroundConstant) *
            ‖thetaToVolume (posGraph p).val.fst‖ ^ 2) ^ 2 := by
  obtain ⟨hpos_sq, _⟩ := norm_posGraph_and_negGraph_fst_sq_eq_half_of_odd hp
  have hcol := (norm_sq_sub_groundPotential_le_collar_split hR (posGraph p).val.fst).2
  rw [hpos_sq] at hcol
  have hdiag_le :
      ⟪primeDiagonalOperator (posGraph p).val.fst, (posGraph p).val.fst⟫_ℝ ≤
        ((1 + thetaGroundPotentialBound / Real.cosh (R / 2)) / 2) * ‖p.val.fst‖ ^ 2 +
          (thetaGroundPotentialBound / riemannKernelReal R - archGroundConstant) *
            ‖thetaToVolume (posGraph p).val.fst‖ ^ 2 := by
    linarith
  have hdiag_nn :
      0 ≤ ⟪primeDiagonalOperator (posGraph p).val.fst, (posGraph p).val.fst⟫_ℝ :=
    primeDiagonalOperator_isPositive.inner_nonneg_left (posGraph p).val.fst
  have hsq_le := pow_le_pow_left₀ hdiag_nn hdiag_le 2
  have hpyth := (odd_posGraph_and_negGraph_primeShift_sq_add_quarter_absGraph_drift_sq_le hp).1
  exact ⟨hdiag_le, hpyth.trans hsq_le⟩

/-! ## §2. Common Nodal Defect Graph `nodalDefectGraph`, Markov Sub-Invariance, Odd-Sector Balanced-Nodal Coincidence, and Collar Criteria for `RiemannHypothesis` -/

/-- **Odd-Sector Common Nodal Defect Graph, Pointwise Lobe Sub-Invariance, and Bilateral
`stationaryGroundGraph` Cauchy–Schwarz Lower Bound
(`odd_eigenvector_nodalDefectGraph_subinvariance_and_bilateral_cs`):**
For every odd eigenvector `resolvent w = μ • w` with `0 < μ`, `μ ≤ 1`, `reflectMass w = -w`,
and `q = rieszLift w`:
1. `nodalDefectGraph μ q = stationaryGraphLift (stationaryCollarPotential μ (negGraph q).val.fst) - negGraph q`,
2. `0 ≤ᵐ[massMeasure] ((nodalDefectGraph μ q).val.fst : ℝ → ℝ)`,
3. `((posGraph q).val.fst : ℝ → ℝ) ≤ᵐ[massMeasure] (stationaryResolvent (stationaryCollarPotential μ (posGraph q).val.fst) : ℝ → ℝ)`,
4. `((negGraph q).val.fst : ℝ → ℝ) ≤ᵐ[massMeasure] (stationaryResolvent (stationaryCollarPotential μ (negGraph q).val.fst) : ℝ → ℝ)`,
5. `⟪fullGroundEquiv (nodalDefectGraph μ q), fullGroundEquiv q⟫_ℝ = 0`,
6. `⟪fullGroundEquiv (nodalDefectGraph μ q), fullGroundEquiv (absGraph q)⟫_ℝ = 2 * (-⟪(fullGroundEquiv (posGraph q)).val.snd, (fullGroundEquiv (negGraph q)).val.snd⟫_ℝ + ⟪primeShiftOperator (posGraph q).val.fst, (negGraph q).val.fst⟫_ℝ)`,
7. `4 * (-⟪(fullGroundEquiv (posGraph q)).val.snd, (fullGroundEquiv (negGraph q)).val.snd⟫_ℝ + ⟪primeShiftOperator (posGraph q).val.fst, (negGraph q).val.fst⟫_ℝ) ^ 2 ≤ (‖(nodalDefectGraph μ q).val.fst‖ ^ 2 + stationaryEnergy (thetaProduct (nodalDefectGraph μ q).val.fst)) * (‖q.val.fst‖ ^ 2 + stationaryEnergy (thetaProduct (absGraph q).val.fst))`. -/
theorem odd_eigenvector_nodalDefectGraph_subinvariance_and_bilateral_cs
    {μ : ℝ} (hμ0 : 0 < μ) (hμ1 : μ ≤ 1) {w : MassSpace} (_hodd : reflectMass w = -w)
    (heig : resolvent w = μ • w) :
    let q := rieszLift w
    nodalDefectGraph μ q =
        stationaryGraphLift (stationaryCollarPotential μ (negGraph q).val.fst) - negGraph q ∧
      0 ≤ᵐ[massMeasure] ((nodalDefectGraph μ q).val.fst : ℝ → ℝ) ∧
      ((posGraph q).val.fst : ℝ → ℝ) ≤ᵐ[massMeasure]
        (stationaryResolvent (stationaryCollarPotential μ (posGraph q).val.fst) : ℝ → ℝ) ∧
      ((negGraph q).val.fst : ℝ → ℝ) ≤ᵐ[massMeasure]
        (stationaryResolvent (stationaryCollarPotential μ (negGraph q).val.fst) : ℝ → ℝ) ∧
      ⟪fullGroundEquiv (nodalDefectGraph μ q), fullGroundEquiv q⟫_ℝ = 0 ∧
      ⟪fullGroundEquiv (nodalDefectGraph μ q), fullGroundEquiv (absGraph q)⟫_ℝ =
        2 * (-⟪(fullGroundEquiv (posGraph q)).val.snd, (fullGroundEquiv (negGraph q)).val.snd⟫_ℝ +
          ⟪primeShiftOperator (posGraph q).val.fst, (negGraph q).val.fst⟫_ℝ) ∧
      4 * (-⟪(fullGroundEquiv (posGraph q)).val.snd, (fullGroundEquiv (negGraph q)).val.snd⟫_ℝ +
          ⟪primeShiftOperator (posGraph q).val.fst, (negGraph q).val.fst⟫_ℝ) ^ 2 ≤
        (‖(nodalDefectGraph μ q).val.fst‖ ^ 2 +
            stationaryEnergy (thetaProduct (nodalDefectGraph μ q).val.fst)) *
          (‖q.val.fst‖ ^ 2 + stationaryEnergy (thetaProduct (absGraph q).val.fst)) := by
  intro q
  have h1 := nodalDefectGraph_eq_negGraph_defect_of_eigenvector hμ0.ne' heig
  obtain ⟨h2, h3, h4⟩ :=
    nodalDefectGraph_fst_ae_nonneg_and_lobe_subinvariance_of_eigenvector hμ0 hμ1 heig
  obtain ⟨_, _, h5, h6, h7⟩ := inner_fullGroundEquiv_nodalDefectGraph_of_eigenvector hμ0.ne' heig
  have hsp := neg_sourcePair_posGraph_negGraph_eq_stationary_add_primeShift q
  have h6' : ⟪fullGroundEquiv (nodalDefectGraph μ q), fullGroundEquiv (absGraph q)⟫_ℝ =
      2 * (-⟪(fullGroundEquiv (posGraph q)).val.snd, (fullGroundEquiv (negGraph q)).val.snd⟫_ℝ +
        ⟪primeShiftOperator (posGraph q).val.fst, (negGraph q).val.fst⟫_ℝ) := by
    change _ = -2 * sourcePair (posGraph q) (negGraph q) at h6
    linarith [h6, hsp]
  have hsq_eq :
      4 * (-⟪(fullGroundEquiv (posGraph q)).val.snd, (fullGroundEquiv (negGraph q)).val.snd⟫_ℝ +
          ⟪primeShiftOperator (posGraph q).val.fst, (negGraph q).val.fst⟫_ℝ) ^ 2 =
        4 * sourcePair (posGraph q) (negGraph q) ^ 2 := by
    rw [← hsp]
    ring
  change 4 * sourcePair (posGraph q) (negGraph q) ^ 2 ≤ _ at h7
  rw [← hsq_eq] at h7
  exact ⟨h1, h2, h3, h4, h5, h6', h7⟩

/-- **Odd-Sector Coincidence of `balancedNodalGraph` and `absGraph`**:
for every odd graph vector `p : SourceGraph` (`reflectGraph p = -p`), its positive and negative
lobes have equal `MassSpace` norm-squared `(1 / 2) * ‖p.val.fst‖ ^ 2`, so
`balancedNodalGraph p = ((1 / 2) * ‖p.val.fst‖ ^ 2) • absGraph p` and
`primGraph (balancedNodalGraph p) = ((1 / 2) * ‖p.val.fst‖ ^ 2) • primGraph (absGraph p)`. -/
theorem balancedNodalGraph_eq_half_norm_sq_smul_absGraph_of_odd {p : SourceGraph}
    (hp : reflectGraph p = -p) :
    balancedNodalGraph p = ((1 / 2 : ℝ) * ‖p.val.fst‖ ^ 2) • absGraph p ∧
      primGraph (balancedNodalGraph p) =
        ((1 / 2 : ℝ) * ‖p.val.fst‖ ^ 2) • primGraph (absGraph p) := by
  obtain ⟨hpos, hneg⟩ := norm_posGraph_and_negGraph_fst_sq_eq_half_of_odd hp
  have h1 : balancedNodalGraph p = ((1 / 2 : ℝ) * ‖p.val.fst‖ ^ 2) • absGraph p := by
    unfold balancedNodalGraph
    rw [hpos, hneg, ← smul_add, posGraph_add_negGraph]
  have h2 : primGraph (balancedNodalGraph p) =
      ((1 / 2 : ℝ) * ‖p.val.fst‖ ^ 2) • primGraph (absGraph p) := by
    apply source_projection_injective
    change (primGraph (balancedNodalGraph p)).val.fst =
      ((1 / 2 : ℝ) * ‖p.val.fst‖ ^ 2) • (primGraph (absGraph p)).val.fst
    rw [h1, primGraph_fst, primGraph_fst]
    change (((1 / 2 : ℝ) * ‖p.val.fst‖ ^ 2) • (absGraph p).val.fst) -
        (2 * ⟪((1 / 2 : ℝ) * ‖p.val.fst‖ ^ 2) • (absGraph p).val.fst, oneL⟫_ℝ) • oneL =
      ((1 / 2 : ℝ) * ‖p.val.fst‖ ^ 2) •
        ((absGraph p).val.fst - (2 * ⟪(absGraph p).val.fst, oneL⟫_ℝ) • oneL)
    rw [real_inner_smul_left, smul_sub, smul_smul]
    congr 2
    ring
  exact ⟨h1, h2⟩

/-- Positive-lobe (`posGraph q`) four-term jump excess criterion for `μ ≤ 1 / 2`. -/
theorem eigenvalue_le_one_half_of_four_term_posGraph_ge_groundPotential
    {μ : ℝ} (hμ : 0 < μ) {w : MassSpace} (heig : resolvent w = μ • w)
    (hp : (posGraph (rieszLift w)).val.fst ≠ 0)
    (hjump :
      let q := rieszLift w
      ‖(posGraph q).val.fst‖ ^ 2 -
          ⟪groundPotentialOperator (posGraph q).val.fst, (posGraph q).val.fst⟫_ℝ ≤
        stationaryEnergy (thetaProduct (posGraph q).val.fst) +
          ⟪primeGenerator (posGraph q).val.fst, (posGraph q).val.fst⟫_ℝ -
          ⟪(fullGroundEquiv (posGraph q)).val.snd, (fullGroundEquiv (negGraph q)).val.snd⟫_ℝ +
          ⟪primeShiftOperator (posGraph q).val.fst, (negGraph q).val.fst⟫_ℝ) :
    μ ≤ 1 / 2 := by
  have hbal1 := posGraph_five_term_jump_eq_diagonals_of_eigenvector hμ.ne' heig
  have hbal2 := arch_add_primeDiagonal_eq_norm_sq_sub_groundPotential (posGraph (rieszLift w)).val.fst
  have hp_pos : 0 < ‖(posGraph (rieszLift w)).val.fst‖ ^ 2 :=
    sq_pos_of_pos (norm_pos_iff.mpr hp)
  have hle : ((2 * μ - 1) / μ) * ‖(posGraph (rieszLift w)).val.fst‖ ^ 2 ≤ 0 := by
    linarith [hbal1, hbal2, hjump]
  have hdiv_le : (2 * μ - 1) / μ ≤ 0 :=
    nonpos_of_mul_nonpos_left hle hp_pos
  have hnum_le : 2 * μ - 1 ≤ 0 := by
    by_contra hpos
    push Not at hpos
    have : 0 < (2 * μ - 1) / μ := div_pos hpos hμ
    linarith
  linarith

/-- **Odd-Sector Positive-Lobe Four-Term Jump Excess Criterion for `RiemannHypothesis`
(`riemannHypothesis_of_odd_eigenvector_four_term_posGraph_ge_groundPotential`):**
If for every nonzero odd eigenvector `resolvent w = μ • w` (`reflectMass w = -w`) with
`μ ∈ Set.Ioo (1 / 2) 1` and `q = rieszLift w`, the four-term nonnegative positive-lobe jump sum is
at least `‖(posGraph q).val.fst‖ ^ 2 - ⟪groundPotentialOperator (posGraph q).val.fst, (posGraph q).val.fst⟫_ℝ`,
then `RiemannHypothesis` holds. -/
theorem riemannHypothesis_of_odd_eigenvector_four_term_posGraph_ge_groundPotential
    (hodd_jump :
      ∀ {μ : ℝ} {w : MassSpace},
        μ ∈ Set.Ioo (1 / 2 : ℝ) 1 → w ≠ 0 → reflectMass w = -w → resolvent w = μ • w →
        let q := rieszLift w
        ‖(posGraph q).val.fst‖ ^ 2 -
            ⟪groundPotentialOperator (posGraph q).val.fst, (posGraph q).val.fst⟫_ℝ ≤
          stationaryEnergy (thetaProduct (posGraph q).val.fst) +
            ⟪primeGenerator (posGraph q).val.fst, (posGraph q).val.fst⟫_ℝ -
            ⟪(fullGroundEquiv (posGraph q)).val.snd, (fullGroundEquiv (negGraph q)).val.snd⟫_ℝ +
            ⟪primeShiftOperator (posGraph q).val.fst, (negGraph q).val.fst⟫_ℝ) :
    RiemannHypothesis := by
  by_contra hnotRH
  obtain ⟨μ, w, hμ, hw, hodd, heig⟩ :=
    not_riemannHypothesis_iff_exists_odd_eigenvector_mem_Ioo_half_one.mp hnotRH
  have hμ0 : 0 < μ := by linarith [hμ.1]
  have hq_odd : reflectGraph (rieszLift w) = -rieszLift w :=
    (odd_eigenvector_lobe_energy_and_snd_sq hμ0.ne' hodd heig).1
  have hfst : (rieszLift w).val.fst = μ • w := heig
  have hq_ne : (rieszLift w).val.fst ≠ 0 := by
    rw [hfst]
    exact smul_ne_zero hμ0.ne' hw
  have hpos_ne : (posGraph (rieszLift w)).val.fst ≠ 0 := by
    obtain ⟨hpos_sq, _⟩ := norm_posGraph_and_negGraph_fst_sq_eq_half_of_odd hq_odd
    intro h0
    have hnorm0 : ‖(posGraph (rieszLift w)).val.fst‖ ^ 2 = 0 := by rw [h0, norm_zero, sq, zero_mul]
    have hq_norm_pos : 0 < ‖(rieszLift w).val.fst‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hq_ne)
    linarith
  have hle : μ ≤ 1 / 2 :=
    eigenvalue_le_one_half_of_four_term_posGraph_ge_groundPotential hμ0 heig hpos_ne
      (hodd_jump hμ hw hodd heig)
  linarith [hμ.1]

/-- **Odd-Sector `cosh(R/2)` Collar-Split Four-Term Jump Excess Criterion for `RiemannHypothesis`
(`riemannHypothesis_of_odd_eigenvector_four_term_posGraph_ge_collar_split`):**
If for every nonzero odd eigenvector `resolvent w = μ • w` (`reflectMass w = -w`) with
`μ ∈ Set.Ioo (1 / 2) 1` and `q = rieszLift w`, there exists a collar radius `0 ≤ R` at which the
four-term nonnegative positive-lobe jump sum is at least
`((1 + thetaGroundPotentialBound / Real.cosh (R / 2)) / 2) * ‖q.val.fst‖ ^ 2 + (thetaGroundPotentialBound / riemannKernelReal R) * ‖thetaToVolume (posGraph q).val.fst‖ ^ 2`,
then `RiemannHypothesis` holds. -/
theorem riemannHypothesis_of_odd_eigenvector_four_term_posGraph_ge_collar_split
    (hodd_collar :
      ∀ {μ : ℝ} {w : MassSpace},
        μ ∈ Set.Ioo (1 / 2 : ℝ) 1 → w ≠ 0 → reflectMass w = -w → resolvent w = μ • w →
        let q := rieszLift w
        ∃ R : ℝ, 0 ≤ R ∧
          ((1 + thetaGroundPotentialBound / Real.cosh (R / 2)) / 2) * ‖q.val.fst‖ ^ 2 +
              (thetaGroundPotentialBound / riemannKernelReal R) *
                ‖thetaToVolume (posGraph q).val.fst‖ ^ 2 ≤
            stationaryEnergy (thetaProduct (posGraph q).val.fst) +
              ⟪primeGenerator (posGraph q).val.fst, (posGraph q).val.fst⟫_ℝ -
              ⟪(fullGroundEquiv (posGraph q)).val.snd, (fullGroundEquiv (negGraph q)).val.snd⟫_ℝ +
              ⟪primeShiftOperator (posGraph q).val.fst, (negGraph q).val.fst⟫_ℝ) :
    RiemannHypothesis := by
  refine riemannHypothesis_of_odd_eigenvector_four_term_posGraph_ge_groundPotential ?_
  intro μ w hμ hw hodd heig q
  have hμ0 : 0 < μ := by linarith [hμ.1]
  obtain ⟨R, hR, hge⟩ := hodd_collar hμ hw hodd heig
  have hq_odd : reflectGraph q = -q :=
    (odd_eigenvector_lobe_energy_and_snd_sq hμ0.ne' hodd heig).1
  obtain ⟨hpos_sq, _⟩ := norm_posGraph_and_negGraph_fst_sq_eq_half_of_odd hq_odd
  have hcol := (norm_sq_sub_groundPotential_le_collar_split hR (posGraph q).val.fst).1
  rw [hpos_sq] at hcol
  linarith

/-! ## §3. Arbitrary-Depth (`r ≥ 1`) Bézout Shell Observation-State Factorization, Iso-State `(2r - 1)`-Step Annihilation, and Common-Return Two-Moment Kernel Bridge -/

/-- **Arbitrary-Depth Bézout Shell Observation-State Factorization
(`bezoutLayerActiveSawtoothSum_horizonObservationState`):**
For every depth `1 ≤ r`, horizon cutoff `N : ℕ`, sieve weight `c : ℕ → ℝ`, and integer `m : ℕ`,
the `r`-th Bézout layer active sawtooth sum depends on `m` solely through the finite multiplicative
observation state `horizonObservationState N m = Nat.gcd m (horizonLcm N)`:
`bezoutLayerActiveSawtoothSum r N c (horizonObservationState N m) = bezoutLayerActiveSawtoothSum r N c m`. -/
theorem bezoutLayerActiveSawtoothSum_horizonObservationState
    {r : ℕ} (hr : 1 ≤ r) (N : ℕ) (c : ℕ → ℝ) (m : ℕ) :
    bezoutLayerActiveSawtoothSum r N c (horizonObservationState N m) =
      bezoutLayerActiveSawtoothSum r N c m := by
  unfold bezoutLayerActiveSawtoothSum
  congr 1
  have hfilter :
      (Finset.Icc (2 * r - 1) N).filter (fun d => d ∣ horizonObservationState N m) =
        (Finset.Icc (2 * r - 1) N).filter (fun d => d ∣ m) := by
    ext d
    simp only [Finset.mem_filter, Finset.mem_Icc]
    refine and_congr_right fun hd => ?_
    exact dvd_horizonObservationState_iff N m d
      (Finset.mem_Icc.mpr ⟨by have := hd.1; omega, hd.2⟩)
  rw [hfilter]

/-- **Iso-State Invariance of Arbitrary-Depth Bézout Layer Active Sawtooth Sums
(`bezoutLayerActiveSawtoothSum_eq_of_horizonObservationState_eq`):**
Whenever `horizonObservationState N k = horizonObservationState N l`, every depth-`r` (`1 ≤ r`)
Bézout layer active sawtooth sum agrees at `k` and `l`:
`bezoutLayerActiveSawtoothSum r N c k = bezoutLayerActiveSawtoothSum r N c l`. -/
theorem bezoutLayerActiveSawtoothSum_eq_of_horizonObservationState_eq
    {N k l : ℕ} (h : horizonObservationState N k = horizonObservationState N l)
    {r : ℕ} (hr : 1 ≤ r) (c : ℕ → ℝ) :
    bezoutLayerActiveSawtoothSum r N c k = bezoutLayerActiveSawtoothSum r N c l := by
  rw [← bezoutLayerActiveSawtoothSum_horizonObservationState hr N c k,
    ← bezoutLayerActiveSawtoothSum_horizonObservationState hr N c l, h]

/-- **Iso-State `(2r - 1)`-Step Annihilation of Arbitrary-Depth Bézout Shells
(`sum_range_bezoutLayerActiveSawtoothSum_sub_add_eq_zero_of_isoState`):**
For every depth `1 ≤ r`, cutoff `N : ℕ`, weight `c : ℕ → ℝ`, base offset `M₀ : ℕ`, and window
length `M : ℕ`, if the `(2 * r - 1)`-tuple of finite multiplicative observation states matches at
the window boundaries (`∀ j ∈ Finset.range (2 * r - 1), horizonObservationState N (M₀ + M + j) = horizonObservationState N (M₀ + j)`),
then the `(2 * r - 1)`-step Bézout shell sum vanishes identically:
`∑ n ∈ Finset.range M, (bezoutLayerActiveSawtoothSum r N c (M₀ + n) - bezoutLayerActiveSawtoothSum r N c (M₀ + n + (2 * r - 1))) = 0`. -/
theorem sum_range_bezoutLayerActiveSawtoothSum_sub_add_eq_zero_of_isoState
    {r : ℕ} (hr : 1 ≤ r) (N : ℕ) (c : ℕ → ℝ) (M₀ M : ℕ)
    (hiso : ∀ j ∈ Finset.range (2 * r - 1),
      horizonObservationState N (M₀ + M + j) = horizonObservationState N (M₀ + j)) :
    (∑ n ∈ Finset.range M,
      (bezoutLayerActiveSawtoothSum r N c (M₀ + n) -
        bezoutLayerActiveSawtoothSum r N c (M₀ + n + (2 * r - 1)))) = 0 := by
  let F : ℕ → ℝ := fun n => bezoutLayerActiveSawtoothSum r N c (M₀ + n)
  have htel := sum_range_sub_add_step_eq_boundary F (2 * r - 1) M
  dsimp only [F] at htel
  have hcongr_lhs :
      (∑ n ∈ Finset.range M,
        (bezoutLayerActiveSawtoothSum r N c (M₀ + n) -
          bezoutLayerActiveSawtoothSum r N c (M₀ + n + (2 * r - 1)))) =
      ∑ n ∈ Finset.range M,
        (bezoutLayerActiveSawtoothSum r N c (M₀ + n) -
          bezoutLayerActiveSawtoothSum r N c (M₀ + (n + (2 * r - 1)))) :=
    Finset.sum_congr rfl fun n _ => by rw [Nat.add_assoc]
  have hcongr_rhs :
      (∑ j ∈ Finset.range (2 * r - 1), bezoutLayerActiveSawtoothSum r N c (M₀ + (M + j))) =
        ∑ j ∈ Finset.range (2 * r - 1), bezoutLayerActiveSawtoothSum r N c (M₀ + j) := by
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [← Nat.add_assoc]
    exact bezoutLayerActiveSawtoothSum_eq_of_horizonObservationState_eq (hiso j hj) hr c
  rw [hcongr_lhs, htel, hcongr_rhs, sub_self]

/-- **Route PM Two-Layer Bézout Decomposition and Common-Return Two-Moment Kernel Bridge
(`pmSecondLayer_and_returnWindow_two_moment_bridge`):**
Unifies the cutoff-independent Route PM second-layer decomposition with the common-return window
two-moment kernel and sharp `2N - 3` variance detection:
1. For every `ε : ℝ` and `n : ℕ`,
   `pmPowerDampedCenteredDivisorPrefix ε n = addDiff (pmActiveSawtoothComponent ε) n + (pmSecondLayerSawtoothComponent ε (n - 1) - pmSecondLayerSawtoothComponent ε (n + 2)) + pmFourStepBezoutInteriorPrefix ε n`.
2. For every `ε : ℝ`, `2 ≤ N`, and sub-horizon `1 ≤ m ≤ N`,
   `bezoutLayerActiveSawtoothSum 2 N (pmPowerDampedRealWeight ε) m = pmSecondLayerSawtoothComponent ε m`.
3. For every `N a b k : ℕ` and `c : ℕ → ℝ`, vanishing on the positive-radius common-return window
   `sieveReturnWindowZero N (a + 1) (b + 1) k c` is equivalent to vanishing on `Icc 2 (min (max (b + 1) a) N)`
   together with both harmonic and raw tail moments vanishing on `Icc (min (max (b + 1) a) N + 1) N`.
4. At centered radius `n + 1` on level `n + 3` (`2(n + 3) - 3 = 2n + 3` samples),
   `sieveReturnWindowZero (n + 3) (n + 1) (n + 1) k c ↔ sieveVariance (n + 3) c = 0`. -/
theorem pmSecondLayer_and_returnWindow_two_moment_bridge :
    (∀ (ε : ℝ) (n : ℕ),
      pmPowerDampedCenteredDivisorPrefix ε n =
        addDiff (pmActiveSawtoothComponent ε) n +
          (pmSecondLayerSawtoothComponent ε (n - 1) -
            pmSecondLayerSawtoothComponent ε (n + 2)) +
          pmFourStepBezoutInteriorPrefix ε n) ∧
    (∀ (ε : ℝ) {N m : ℕ}, 2 ≤ N → 1 ≤ m → m ≤ N →
      bezoutLayerActiveSawtoothSum 2 N (pmPowerDampedRealWeight ε) m =
        pmSecondLayerSawtoothComponent ε m) ∧
    (∀ (N a b k : ℕ) (c : ℕ → ℝ),
      sieveReturnWindowZero N (a + 1) (b + 1) k c ↔
        (∀ d ∈ Finset.Icc 2 (min (max (b + 1) a) N), c d = 0) ∧
          (∑ d ∈ Finset.Icc (min (max (b + 1) a) N + 1) N, c d / (d : ℝ)) = 0 ∧
          (∑ d ∈ Finset.Icc (min (max (b + 1) a) N + 1) N, c d) = 0) ∧
    (∀ (n k : ℕ) (c : ℕ → ℝ),
      sieveReturnWindowZero (n + 3) (n + 1) (n + 1) k c ↔
        sieveVariance (n + 3) c = 0) := by
  refine ⟨pmPowerDampedCenteredDivisorPrefix_eq_first_and_second_layer_add_fourStep, ?_,
    sieveReturnWindow_two_moment_kernel, sieveReturnWindow_sharp_detection⟩
  intro ε N m hN hm1 hmN
  rw [bezoutLayerActiveSawtoothSum_two_eq]
  exact secondLayerActiveSawtoothSum_pmPowerDampedRealWeight_eq ε hN hm1 hmN

/-! ## §4. Folded Möbius Klein–Gordon Prime-Wave Transport & Light-Cone Rapidity Tail Bridge -/

/-- **Folded Möbius Klein–Gordon Prime-Wave Transport and Light-Cone Rapidity Tail Bridge
(`kleinGordon_chebyshev_transport_mobius_three_piece_and_lightCone_bridge`):**
Unifies the von-Mangoldt-free folded Möbius decomposition of the Klein–Gordon Chebyshev discrepancy
transport with the light-cone Bessel bound and rapidity-envelope tail bound:
1. For every `y : ℝ`,
   `chebyshevDiscrepancyTransport y = chmdPrimeKernel y 0 - (mobiusWaveConstant * mobiusWave y + (Real.eulerMascheroniConstant + 1) * mobiusTailPairing y + remainderFoldSeries y)`.
2. For every `y : ℝ` and `0 ≤ v`,
   `mobiusFold y v = mobiusWaveConstant * conjugatedKernel y v + (Real.eulerMascheroniConstant + 1) * (Real.exp (-v) * ∫ s in Ioi v, chmdPrimeKernel y s * Real.exp (s / 2)) + remainderFold y v`
   and `|remainderFold y v| ≤ 7 * laplacianBound * Real.exp (-(v / 2))`.
3. For every `0 ≤ w`, `|lightConeBesselReal w| ≤ 1`, and there exists `0 ≤ C` such that for all
   `y : ℝ` and `1 ≤ N`,
   `(∑' j : ℕ, |mobiusFold y (Real.log ((j + N + 1 : ℕ) : ℝ))|) ≤ C * foldRapidityEnvelope y * (N : ℝ) ^ (-(π - 3 / 2))`.
4. `RiemannHypothesis` is equivalent both to the upper bound and to the lower bound on the sum of
   the three Möbius transport pieces on `[0, ∞)`. -/
theorem kleinGordon_chebyshev_transport_mobius_three_piece_and_lightCone_bridge :
    (∀ y : ℝ,
      chebyshevDiscrepancyTransport y =
        chmdPrimeKernel y 0 -
          (mobiusWaveConstant * mobiusWave y +
            (Real.eulerMascheroniConstant + 1) * mobiusTailPairing y +
            remainderFoldSeries y)) ∧
    (∀ (y v : ℝ), 0 ≤ v →
      mobiusFold y v =
        mobiusWaveConstant * conjugatedKernel y v +
          (Real.eulerMascheroniConstant + 1) *
            (Real.exp (-v) * ∫ s in Ioi v, chmdPrimeKernel y s * Real.exp (s / 2)) +
          remainderFold y v ∧
      |remainderFold y v| ≤ 7 * laplacianBound * Real.exp (-(v / 2))) ∧
    (∀ w : ℝ, 0 ≤ w → |lightConeBesselReal w| ≤ 1) ∧
    (∃ C : ℝ, 0 ≤ C ∧ ∀ (y : ℝ) (N : ℕ), 1 ≤ N →
      (∑' j : ℕ, |mobiusFold y (Real.log ((j + N + 1 : ℕ) : ℝ))|) ≤
        C * foldRapidityEnvelope y * (N : ℝ) ^ (-(π - 3 / 2))) ∧
    (RiemannHypothesis ↔ ∃ M : ℝ, ∀ y : ℝ, 0 ≤ y →
      mobiusWaveConstant * mobiusWave y +
        (Real.eulerMascheroniConstant + 1) * mobiusTailPairing y +
        remainderFoldSeries y ≤ M) ∧
    (RiemannHypothesis ↔ ∃ M : ℝ, ∀ y : ℝ, 0 ≤ y →
      -M ≤ mobiusWaveConstant * mobiusWave y +
        (Real.eulerMascheroniConstant + 1) * mobiusTailPairing y +
        remainderFoldSeries y) :=
  ⟨chebyshevDiscrepancyTransport_eq_mobius_pieces,
   fun y v hv => ⟨mobiusFold_eq y hv, abs_remainderFold_le y v⟩,
   fun _ hw => abs_lightConeBesselReal_nonneg_le_one hw,
   exists_tsum_abs_mobiusFold_tail_le_rapidity_envelope,
   riemannHypothesis_iff_mobius_pieces_bddAbove,
   riemannHypothesis_iff_mobius_pieces_bddBelow⟩

end

end GaloisForLFunctions.TransHorizonIncidenceMechanics
