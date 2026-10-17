import GaloisForLFunctions.BiScaleUncertainty.BalancedNodalStationaryAndPrimeShiftDecompositionProducer
import GaloisForLFunctions.BiScaleUncertainty.OddProfileCollarDominanceAndUnimodalPrimeWindowProducer

/-!
# Exponential `cosh(x / 2)`-Decay Ground-Potential Bounds, Collar-to-`thetaToVolume` Dominance, and Five-Term Nodal / Off-Diagonal Prime-Clock Exclusion Laws

This module develops **Pillar XLIII** of the `BiScaleUncertainty` framework, sharpening the uniform
ground-potential bound `‖thetaGroundPotential x‖ ≤ thetaGroundPotentialBound` by retaining the exact
`Real.cosh (x / 2)` denominator and combining it with the even strict antitonicity of
`riemannKernelReal` on `[0, ∞)` (`strictAntiOn_riemannKernelReal_Ici`) to establish explicit,
existential-free collar-to-`thetaToVolume` dominance inequalities and eigenvalue exclusion laws:

1. **Exponentially Decaying `cosh(x / 2)` Pointwise Bounds on `thetaGroundPotential` and
   `primeDiagonalPotential` (§1)**:
   - `abs_integral_thetaSecondDifference_kernel_le`:
     `|∫ t in Ioi 0, archLevyDensity t * thetaSecondDifference t x| ≤ thetaGroundPotentialBound`.
   - `abs_thetaGroundPotential_le_div_cosh` and `neg_div_cosh_le_thetaGroundPotential_and_lt_one`:
     `|thetaGroundPotential x| ≤ thetaGroundPotentialBound / Real.cosh (x / 2)` and
     `-thetaGroundPotentialBound / Real.cosh (x / 2) ≤ thetaGroundPotential x < 1`.
   - `one_sub_thetaGroundPotential_bounds_div_cosh` and `primeDiagonalPotential_le_one_add_div_cosh`:
     `1 - thetaGroundPotentialBound / Real.cosh (x / 2) ≤ 1 - thetaGroundPotential x ≤ 1 + thetaGroundPotentialBound / Real.cosh (x / 2)`
     and `primeDiagonalPotential x ≤ 1 + thetaGroundPotentialBound / Real.cosh (x / 2)`.
   - `abs_primeKernelSum_add_arch_sub_cosh_le`:
     `|primeKernelSum x + archGroundConstant * riemannKernelReal x - Real.cosh (x / 2)| ≤ thetaGroundPotentialBound`.

2. **Exact `cosh(x / 2)`-Cancelled Volume Integral and Collar Monotonicity of `riemannKernelReal` (§2)**:
   - `inner_groundPotentialOperator_self_eq_volume`:
     when `thetaGroundPotential x * u x ^ 2` is integrated against `massMeasure`, the
     `Real.cosh (x / 2)` denominator in `thetaGroundPotential x` cancels the `Real.cosh (x / 2)`
     factor in `massDensity x = riemannKernelReal x * Real.cosh (x / 2)` identically:
     `⟪groundPotentialOperator u, u⟫_ℝ = ∫ x, (∫ t in Ioi 0, archLevyDensity t * thetaSecondDifference t x) * riemannKernelReal x * u x ^ 2`.
   - `riemannKernelReal_le_of_abs_le`:
     because `riemannKernelReal` is even and strictly antitone on `[0, ∞)`, for every `|x| ≤ R`,
     `riemannKernelReal R ≤ riemannKernelReal x`.
   - `inv_cosh_le_inv_cosh_add_theta_div_cosh` and `nearInd_le_cosh_div_theta_mul_arch`:
     for every `0 ≤ R` and `x : ℝ`,
     `1 / Real.cosh (x / 2) ≤ 1 / Real.cosh (R / 2) + (1 / riemannKernelReal R) * (riemannKernelReal x / Real.cosh (x / 2))`
     and `nearInd R x ≤ (Real.cosh (R / 2) / (archGroundConstant * riemannKernelReal R)) * (archGroundConstant * riemannKernelReal x / Real.cosh (x / 2))`.

3. **Explicit Collar-to-`thetaToVolume` Dominance for `nearMass`, `groundPotentialOperator`, and
   `primeDiagonalOperator` (§3)**:
   - `norm_nearMul_sq_le_thetaToVolume_sq` and `nearMass_le_thetaToVolume_sq`:
     for every `R : ℝ`, `u : MassSpace`, and `p : SourceGraph`,
     `‖nearMul R u‖ ^ 2 ≤ (Real.cosh (R / 2) / riemannKernelReal R) * ‖thetaToVolume u‖ ^ 2` and
     `nearMass R p ≤ (Real.cosh (R / 2) / riemannKernelReal R) * ‖thetaToVolume p.val.fst‖ ^ 2`.
   - `abs_inner_groundPotentialOperator_self_le_collar_split` and
     `norm_sq_sub_groundPotential_le_collar_split`:
     for every `0 ≤ R` and `u : MassSpace`,
     `|⟪groundPotentialOperator u, u⟫_ℝ| ≤ (thetaGroundPotentialBound / Real.cosh (R / 2)) * ‖u‖ ^ 2 + (thetaGroundPotentialBound / riemannKernelReal R) * ‖thetaToVolume u‖ ^ 2`
     and
     `⟪primeDiagonalOperator u, u⟫_ℝ ≤ (1 + thetaGroundPotentialBound / Real.cosh (R / 2)) * ‖u‖ ^ 2 + (thetaGroundPotentialBound / riemannKernelReal R - archGroundConstant) * ‖thetaToVolume u‖ ^ 2`.

4. **`thetaToVolume` Confinement of Negative Doob Energy, Five-Term Nodal Collar Bounds, and
   Eigenvalue Exclusion Criteria (§4)**:
   - `exists_thetaToVolume_energy_bound`, `exists_archDiagonal_energy_bound`, and
     `exists_thetaToVolume_lower_of_resolvent`:
     upgrades `exists_window_energy_bound` and `exists_window_mass_resolvent` from compact window
     indicators `nearMass R` to the smooth global operator `thetaToVolume` and `archDiagonalOperator`.
   - `balancedNodalGraph_five_term_jump_le_collar_split_of_eigenvector`,
     `posGraph_five_term_jump_le_collar_split_of_eigenvector`, and
     `negGraph_five_term_jump_le_collar_split_of_eigenvector`:
     explicit collar-split upper bounds on the five-term nonnegative jump sum for `balancedNodalGraph q`,
     `posGraph q`, and `negGraph q`.
   - `eigenvalue_le_one_half_of_four_term_balancedNodal_ge_groundPotential`,
     `eigenvalue_le_one_half_of_four_term_posGraph_ge_groundPotential`,
     `eigenvalue_le_one_half_of_four_term_negGraph_ge_groundPotential`,
     `eigenvalue_le_one_half_of_four_term_balancedNodal_ge_collar_split`, and
     `eigenvalue_le_one_half_of_frequently_offDiag_primeClock_ge_neg`:
     exact Rayleigh / nodal-cross and cofinal off-diagonal prime-clock exclusion laws forcing
     `μ ≤ 1 / 2`.
-/

open MeasureTheory Set Filter Topology Complex Zeta23
open scoped InnerProductSpace BigOperators
noncomputable section

namespace GaloisForLFunctions.BiScaleUncertainty

open _root_.RHTower
open _root_.RHTower.CHMDDoobGraph
open _root_.RHTower.CHMDClosedJump
open _root_.RHTower.CHMDTranslation
open _root_.RHTower.ThetaSourceWard
open _root_.RHTower.CHMDPolar

/-! ## Section 1: Exponentially Decaying `cosh(x / 2)` Pointwise Bounds on `thetaGroundPotential` and `primeDiagonalPotential` -/

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

/-- Two-sided pointwise enclosure of `thetaGroundPotential x` with exponential `cosh(x / 2)` lower
decay:
`-thetaGroundPotentialBound / Real.cosh (x / 2) ≤ thetaGroundPotential x ∧ thetaGroundPotential x < 1`. -/
theorem neg_div_cosh_le_thetaGroundPotential_and_lt_one (x : ℝ) :
    -thetaGroundPotentialBound / Real.cosh (x / 2) ≤ thetaGroundPotential x ∧
      thetaGroundPotential x < 1 := by
  have h1 := neg_le_of_abs_le (abs_thetaGroundPotential_le_div_cosh x)
  rw [neg_div]
  exact ⟨h1, thetaGroundPotential_lt_one x⟩

/-- Two-sided `cosh(x / 2)`-decaying pointwise enclosure of `1 - thetaGroundPotential x`. -/
theorem one_sub_thetaGroundPotential_bounds_div_cosh (x : ℝ) :
    1 - thetaGroundPotentialBound / Real.cosh (x / 2) ≤ 1 - thetaGroundPotential x ∧
      1 - thetaGroundPotential x ≤ 1 + thetaGroundPotentialBound / Real.cosh (x / 2) := by
  have h := abs_le.mp (abs_thetaGroundPotential_le_div_cosh x)
  exact ⟨by linarith, by linarith⟩

/-- **Exponentially Decaying `cosh(x / 2)` Pointwise Upper Bound on `primeDiagonalPotential`**:
for every `x : ℝ`,
`primeDiagonalPotential x ≤ 1 + thetaGroundPotentialBound / Real.cosh (x / 2)` and
`primeDiagonalPotential x + archGroundConstant * riemannKernelReal x / Real.cosh (x / 2) ≤ 1 + thetaGroundPotentialBound / Real.cosh (x / 2)`. -/
theorem primeDiagonalPotential_le_one_add_div_cosh (x : ℝ) :
    primeDiagonalPotential x ≤ 1 + thetaGroundPotentialBound / Real.cosh (x / 2) ∧
      primeDiagonalPotential x +
          archGroundConstant * riemannKernelReal x / Real.cosh (x / 2) ≤
        1 + thetaGroundPotentialBound / Real.cosh (x / 2) := by
  have h1 : primeDiagonalPotential x < 1 - thetaGroundPotential x :=
    primeKernelSum_div_cosh_lt_one_sub_thetaGroundPotential x
  have h2 := (one_sub_thetaGroundPotential_bounds_div_cosh x).2
  have h3 : primeDiagonalPotential x +
      archGroundConstant * riemannKernelReal x / Real.cosh (x / 2) =
      1 - thetaGroundPotential x := by
    unfold primeDiagonalPotential
    rw [one_sub_thetaGroundPotential_eq, add_div]
  exact ⟨h1.le.trans h2, h3.le.trans h2⟩

/-- Uniform `thetaGroundPotentialBound` deviation bound between
`primeKernelSum x + archGroundConstant * riemannKernelReal x` and `Real.cosh (x / 2)`. -/
theorem abs_primeKernelSum_add_arch_sub_cosh_le (x : ℝ) :
    |primeKernelSum x + archGroundConstant * riemannKernelReal x - Real.cosh (x / 2)| ≤
      thetaGroundPotentialBound := by
  have heq : primeKernelSum x + archGroundConstant * riemannKernelReal x - Real.cosh (x / 2) =
      -(∫ t in Ioi (0 : ℝ), archLevyDensity t * thetaSecondDifference t x) := by
    rw [integral_thetaSecondDifference_kernel_eq x]
    ring
  rw [heq, abs_neg]
  exact abs_integral_thetaSecondDifference_kernel_le x

/-! ## Section 2: Exact `cosh(x / 2)`-Cancelled Volume Integral and Collar Monotonicity of `riemannKernelReal` -/

/-- **Exact `cosh(x / 2)`-Cancelled Volume Integral for `groundPotentialOperator`**:
when `thetaGroundPotential x * u x ^ 2` is integrated against
`massMeasure = volume.withDensity (ENNReal.ofReal ∘ massDensity)`, the `Real.cosh (x / 2)`
denominator in `thetaGroundPotential x` cancels the `Real.cosh (x / 2)` factor in `massDensity x`
identically. -/
theorem inner_groundPotentialOperator_self_eq_volume (u : MassSpace) :
    ⟪groundPotentialOperator u, u⟫_ℝ =
      ∫ x, (∫ t in Ioi (0 : ℝ), archLevyDensity t * thetaSecondDifference t x) *
        riemannKernelReal x * u x ^ 2 := by
  rw [inner_groundPotentialOperator_self, integral_mass]
  apply integral_congr_ae
  filter_upwards [] with x
  unfold massDensity thetaGroundPotential
  have hch : Real.cosh (x / 2) ≠ 0 := (Real.cosh_pos (x / 2)).ne'
  field_simp [hch]

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

/-- Pointwise dominance of the compact window indicator `nearInd R x` by the smooth archimedean
diagonal density `archGroundConstant * riemannKernelReal x / Real.cosh (x / 2)`. -/
theorem nearInd_le_cosh_div_theta_mul_arch (R x : ℝ) :
    nearInd R x ≤
      (Real.cosh (R / 2) / (archGroundConstant * riemannKernelReal R)) *
        (archGroundConstant * riemannKernelReal x / Real.cosh (x / 2)) := by
  have hc_pos : 0 < archGroundConstant := archGroundConstant_pos
  have hθR : 0 < riemannKernelReal R := riemannKernelReal_pos R
  have hθx : 0 < riemannKernelReal x := riemannKernelReal_pos x
  have hchx : 0 < Real.cosh (x / 2) := Real.cosh_pos (x / 2)
  rcases nearInd_zero_or_one R x with h0 | h1
  · rw [h0]
    positivity
  · rw [h1]
    have hxR : |x| ≤ R := by
      by_contra hc
      simp [nearInd, hc] at h1
    have hR0 : 0 ≤ R := (abs_nonneg x).trans hxR
    have hθ_le : riemannKernelReal R ≤ riemannKernelReal x := riemannKernelReal_le_of_abs_le hxR
    have hcosh_le : Real.cosh (x / 2) ≤ Real.cosh (R / 2) := by
      rw [Real.cosh_le_cosh, abs_div, abs_div, abs_of_nonneg hR0, abs_two]
      exact div_le_div_of_nonneg_right hxR (by norm_num)
    have hdiv1 : 1 ≤ Real.cosh (R / 2) / Real.cosh (x / 2) := (one_le_div hchx).mpr hcosh_le
    have hdiv2 : 1 ≤ riemannKernelReal x / riemannKernelReal R := (one_le_div hθR).mpr hθ_le
    calc (1 : ℝ) = 1 * 1 := by ring
      _ ≤ (Real.cosh (R / 2) / Real.cosh (x / 2)) *
          (riemannKernelReal x / riemannKernelReal R) :=
          mul_le_mul hdiv1 hdiv2 zero_le_one (by positivity)
      _ = (Real.cosh (R / 2) / (archGroundConstant * riemannKernelReal R)) *
          (archGroundConstant * riemannKernelReal x / Real.cosh (x / 2)) := by
          field_simp [hc_pos.ne', hθR.ne', hchx.ne']

/-! ## Section 3: Explicit Collar-to-`thetaToVolume` Dominance for `nearMass`, `groundPotentialOperator`, and `primeDiagonalOperator` -/

/-- Pointwise a.e. multiplication formula for `archDiagonalOperator` on `MassSpace`. -/
theorem archDiagonalOperator_ae (u : MassSpace) :
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

theorem integrable_archDiagonal_sq_mass (u : MassSpace) :
    Integrable (fun x => (archGroundConstant * riemannKernelReal x / Real.cosh (x / 2)) * u x ^ 2)
      massMeasure := by
  refine (L2.integrable_inner (archDiagonalOperator u) u).congr ?_
  filter_upwards [archDiagonalOperator_ae u] with x hx
  simp only [hx, RCLike.inner_apply', conj_trivial]
  ring

theorem integral_archDiagonal_sq_mass (u : MassSpace) :
    (∫ x, (archGroundConstant * riemannKernelReal x / Real.cosh (x / 2)) * u x ^ 2 ∂massMeasure) =
      archGroundConstant * ‖thetaToVolume u‖ ^ 2 := by
  rw [← inner_archDiagonalOperator_self, inner_archDiagonalOperator_eq_mass]
  apply integral_congr_ae
  filter_upwards [] with x
  ring

/-- **Explicit Collar-to-`thetaToVolume` Dominance for `nearMul R u`**:
for every window radius `R : ℝ` and every `u : MassSpace`,
`‖nearMul R u‖ ^ 2 ≤ (Real.cosh (R / 2) / riemannKernelReal R) * ‖thetaToVolume u‖ ^ 2`
and
`‖nearMul R u‖ ^ 2 ≤ (Real.cosh (R / 2) / (archGroundConstant * riemannKernelReal R)) * ⟪archDiagonalOperator u, u⟫_ℝ`. -/
theorem norm_nearMul_sq_le_thetaToVolume_sq (R : ℝ) (u : MassSpace) :
    ‖nearMul R u‖ ^ 2 ≤
      (Real.cosh (R / 2) / riemannKernelReal R) * ‖thetaToVolume u‖ ^ 2 ∧
    ‖nearMul R u‖ ^ 2 ≤
      (Real.cosh (R / 2) / (archGroundConstant * riemannKernelReal R)) *
        ⟪archDiagonalOperator u, u⟫_ℝ := by
  have hc_pos : 0 < archGroundConstant := archGroundConstant_pos
  have hθR : 0 < riemannKernelReal R := riemannKernelReal_pos R
  have hnear_eq : ‖nearMul R u‖ ^ 2 = ∫ x, nearInd R x * u x ^ 2 ∂massMeasure := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [nearMul_coeFn R u] with x hx
    simp only [hx, RCLike.inner_apply', conj_trivial]
    rcases nearInd_zero_or_one R x with h | h <;> simp [h, pow_two]
  have hint_near : Integrable (fun x => nearInd R x * u x ^ 2) massMeasure := by
    refine (L2.integrable_inner (nearMul R u) u).congr ?_
    filter_upwards [nearMul_coeFn R u] with x hx
    simp only [hx, RCLike.inner_apply', conj_trivial]
    ring
  have hint_arch := (integrable_archDiagonal_sq_mass u).const_mul
    (Real.cosh (R / 2) / (archGroundConstant * riemannKernelReal R))
  have hle : (∫ x, nearInd R x * u x ^ 2 ∂massMeasure) ≤
      ∫ x, (Real.cosh (R / 2) / (archGroundConstant * riemannKernelReal R)) *
        ((archGroundConstant * riemannKernelReal x / Real.cosh (x / 2)) * u x ^ 2) ∂massMeasure := by
    refine integral_mono hint_near hint_arch fun x => ?_
    have hpt := mul_le_mul_of_nonneg_right (nearInd_le_cosh_div_theta_mul_arch R x) (sq_nonneg (u x))
    linarith
  rw [integral_const_mul, integral_archDiagonal_sq_mass] at hle
  rw [← hnear_eq] at hle
  have hsimp : (Real.cosh (R / 2) / (archGroundConstant * riemannKernelReal R)) *
      (archGroundConstant * ‖thetaToVolume u‖ ^ 2) =
      (Real.cosh (R / 2) / riemannKernelReal R) * ‖thetaToVolume u‖ ^ 2 := by
    field_simp [hc_pos.ne', hθR.ne']
  have harch_eq := inner_archDiagonalOperator_self u
  exact ⟨hle.trans_eq hsimp, by rw [harch_eq]; exact hle⟩

/-- **Explicit Collar-to-`thetaToVolume` Dominance for `nearMass R p`**:
for every window radius `R : ℝ` and every `p : SourceGraph`,
`nearMass R p ≤ (Real.cosh (R / 2) / riemannKernelReal R) * ‖thetaToVolume p.val.fst‖ ^ 2`. -/
theorem nearMass_le_thetaToVolume_sq (R : ℝ) (p : SourceGraph) :
    nearMass R p ≤
      (Real.cosh (R / 2) / riemannKernelReal R) * ‖thetaToVolume p.val.fst‖ ^ 2 ∧
    nearMass R p ≤
      (Real.cosh (R / 2) / (archGroundConstant * riemannKernelReal R)) *
        ⟪archDiagonalOperator p.val.fst, p.val.fst⟫_ℝ := by
  rw [nearMass_eq_norm_sq]
  exact norm_nearMul_sq_le_thetaToVolume_sq R p.val.fst

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

/-! ## Section 4: `thetaToVolume` Confinement of Negative Doob Energy, Five-Term Nodal Collar Bounds, and Eigenvalue Exclusion Criteria -/

/-- **Negative Doob Energy is Controlled by `‖thetaToVolume p.val.fst‖ ^ 2`**:
for every `0 < ε`, there exists `0 ≤ C` such that for all `p : SourceGraph`,
`-ε * ‖p.val.fst‖ ^ 2 - C * ‖thetaToVolume p.val.fst‖ ^ 2 ≤ sourceEnergy p`. -/
theorem exists_thetaToVolume_energy_bound {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p : SourceGraph,
      -ε * ‖p.val.fst‖ ^ 2 - C * ‖thetaToVolume p.val.fst‖ ^ 2 ≤ sourceEnergy p := by
  obtain ⟨R, C₀, _, hC₀, hbound⟩ := exists_window_energy_bound hε
  have hθR : 0 < riemannKernelReal R := riemannKernelReal_pos R
  have hchR : 0 < Real.cosh (R / 2) := Real.cosh_pos (R / 2)
  refine ⟨C₀ * (Real.cosh (R / 2) / riemannKernelReal R), by positivity, fun p => ?_⟩
  have h1 := hbound p
  have hsm : sourceMap p = p.val.fst := rfl
  rw [hsm] at h1
  have h2 := mul_le_mul_of_nonneg_left (nearMass_le_thetaToVolume_sq R p).1 hC₀
  linarith

/-- **Negative Doob Energy is Absorbed by `archDiagonalOperator`**:
for every `0 < ε`, there exists `0 ≤ K` such that for all `p : SourceGraph`,
`-ε * ‖p.val.fst‖ ^ 2 ≤ sourceEnergy p + K * ⟪archDiagonalOperator p.val.fst, p.val.fst⟫_ℝ`. -/
theorem exists_archDiagonal_energy_bound {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ p : SourceGraph,
      -ε * ‖p.val.fst‖ ^ 2 ≤
        sourceEnergy p + K * ⟪archDiagonalOperator p.val.fst, p.val.fst⟫_ℝ := by
  obtain ⟨C, hC, hbound⟩ := exists_thetaToVolume_energy_bound hε
  have hc_pos : 0 < archGroundConstant := archGroundConstant_pos
  refine ⟨C / archGroundConstant, div_nonneg hC hc_pos.le, fun p => ?_⟩
  have h1 := hbound p
  have h2 : (C / archGroundConstant) * ⟪archDiagonalOperator p.val.fst, p.val.fst⟫_ℝ =
      C * ‖thetaToVolume p.val.fst‖ ^ 2 := by
    rw [inner_archDiagonalOperator_self]
    field_simp [hc_pos.ne']
  linarith

/-- **Uniform `thetaToVolume` and `archDiagonalOperator` Lower Bound for Approximate Eigenvectors
Above `1 / 2`**:
for every `1 / 2 < μ`, there exist `0 < θ` and `0 < η` such that every unit vector `w : MassSpace`
with `‖resolvent w - μ • w‖ ≤ η` satisfies
`θ ≤ ‖thetaToVolume (resolvent w)‖ ^ 2` and
`archGroundConstant * θ ≤ ⟪archDiagonalOperator (resolvent w), resolvent w⟫_ℝ`. -/
theorem exists_thetaToVolume_lower_of_resolvent {μ : ℝ} (hμ : 1 / 2 < μ) :
    ∃ θ η : ℝ, 0 < θ ∧ 0 < η ∧ ∀ w : MassSpace, ‖w‖ = 1 →
      ‖resolvent w - μ • w‖ ≤ η →
        θ ≤ ‖thetaToVolume (resolvent w)‖ ^ 2 ∧
        archGroundConstant * θ ≤
          ⟪archDiagonalOperator (resolvent w), resolvent w⟫_ℝ := by
  obtain ⟨R, θ₀, η, _, hθ₀, hη, hres⟩ := exists_window_mass_resolvent hμ
  have hθR : 0 < riemannKernelReal R := riemannKernelReal_pos R
  have hchR : 0 < Real.cosh (R / 2) := Real.cosh_pos (R / 2)
  have hc_pos : 0 < archGroundConstant := archGroundConstant_pos
  refine ⟨θ₀ * (riemannKernelReal R / Real.cosh (R / 2)), η, by positivity, hη,
    fun w hw hρ => ?_⟩
  have h1 := hres w hw hρ
  have h2 := (norm_nearMul_sq_le_thetaToVolume_sq R (resolvent w)).1
  have h3 : θ₀ * (riemannKernelReal R / Real.cosh (R / 2)) ≤
      ‖thetaToVolume (resolvent w)‖ ^ 2 := by
    have hmul := mul_le_mul_of_nonneg_left (h1.trans h2)
      (show 0 ≤ riemannKernelReal R / Real.cosh (R / 2) by positivity)
    have hsimp : (riemannKernelReal R / Real.cosh (R / 2)) *
        ((Real.cosh (R / 2) / riemannKernelReal R) * ‖thetaToVolume (resolvent w)‖ ^ 2) =
        ‖thetaToVolume (resolvent w)‖ ^ 2 := by
      field_simp [hθR.ne', hchR.ne']
    linarith
  refine ⟨h3, ?_⟩
  rw [inner_archDiagonalOperator_self]
  exact mul_le_mul_of_nonneg_left h3 hc_pos.le

/-- **Collar-Split Upper Bound on the Five-Term Balanced-Nodal Jump Sum of Any Eigenvector**:
for every eigenvector `resolvent w = μ • w` (`μ ≠ 0`) with `q = rieszLift w` and every `0 ≤ R`,
the five-term nonnegative balanced-nodal jump sum is bounded above by
`(1 + thetaGroundPotentialBound / Real.cosh (R / 2)) * ‖(balancedNodalGraph q).val.fst‖ ^ 2 + (thetaGroundPotentialBound / riemannKernelReal R) * ‖thetaToVolume (balancedNodalGraph q).val.fst‖ ^ 2`. -/
theorem balancedNodalGraph_five_term_jump_le_collar_split_of_eigenvector
    {μ : ℝ} (hμ : μ ≠ 0) {w : MassSpace} (heig : resolvent w = μ • w)
    {R : ℝ} (hR : 0 ≤ R) :
    let q := rieszLift w
    stationaryEnergy (thetaProduct (balancedNodalGraph q).val.fst) +
        ⟪primeGenerator (balancedNodalGraph q).val.fst, (balancedNodalGraph q).val.fst⟫_ℝ -
        ‖q.val.fst‖ ^ 4 *
          ⟪(fullGroundEquiv (posGraph q)).val.snd, (fullGroundEquiv (negGraph q)).val.snd⟫_ℝ +
        ‖q.val.fst‖ ^ 4 *
          ⟪primeShiftOperator (posGraph q).val.fst, (negGraph q).val.fst⟫_ℝ +
        ((2 * μ - 1) / μ) * ‖(balancedNodalGraph q).val.fst‖ ^ 2 ≤
      (1 + thetaGroundPotentialBound / Real.cosh (R / 2)) *
          ‖(balancedNodalGraph q).val.fst‖ ^ 2 +
        (thetaGroundPotentialBound / riemannKernelReal R) *
          ‖thetaToVolume (balancedNodalGraph q).val.fst‖ ^ 2 := by
  intro q
  have h1 := (balancedNodalGraph_five_term_jump_eq_diagonals_of_eigenvector hμ heig).2
  have h2 := (norm_sq_sub_groundPotential_le_collar_split hR (balancedNodalGraph q).val.fst).1
  linarith

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

/-- **Balanced-Nodal Four-Term Jump Excess Criterion for `μ ≤ 1 / 2`**:
for any eigenvector `resolvent w = μ • w` (`0 < μ`) with `(balancedNodalGraph (rieszLift w)).val.fst ≠ 0`,
if the four-term nonnegative balanced-nodal jump sum is at least
`‖b.val.fst‖ ^ 2 - ⟪groundPotentialOperator b.val.fst, b.val.fst⟫_ℝ`, then `μ ≤ 1 / 2`. -/
theorem eigenvalue_le_one_half_of_four_term_balancedNodal_ge_groundPotential
    {μ : ℝ} (hμ : 0 < μ) {w : MassSpace} (heig : resolvent w = μ • w)
    (hb : (balancedNodalGraph (rieszLift w)).val.fst ≠ 0)
    (hjump :
      let q := rieszLift w
      ‖(balancedNodalGraph q).val.fst‖ ^ 2 -
          ⟪groundPotentialOperator (balancedNodalGraph q).val.fst,
            (balancedNodalGraph q).val.fst⟫_ℝ ≤
        stationaryEnergy (thetaProduct (balancedNodalGraph q).val.fst) +
          ⟪primeGenerator (balancedNodalGraph q).val.fst, (balancedNodalGraph q).val.fst⟫_ℝ -
          ‖q.val.fst‖ ^ 4 *
            ⟪(fullGroundEquiv (posGraph q)).val.snd, (fullGroundEquiv (negGraph q)).val.snd⟫_ℝ +
          ‖q.val.fst‖ ^ 4 *
            ⟪primeShiftOperator (posGraph q).val.fst, (negGraph q).val.fst⟫_ℝ) :
    μ ≤ 1 / 2 := by
  have hbal := (balancedNodalGraph_five_term_jump_eq_diagonals_of_eigenvector hμ.ne' heig).2
  have hb_pos : 0 < ‖(balancedNodalGraph (rieszLift w)).val.fst‖ ^ 2 :=
    sq_pos_of_pos (norm_pos_iff.mpr hb)
  have hle : ((2 * μ - 1) / μ) * ‖(balancedNodalGraph (rieszLift w)).val.fst‖ ^ 2 ≤ 0 := by
    linarith [hbal, hjump]
  have hdiv_le : (2 * μ - 1) / μ ≤ 0 :=
    nonpos_of_mul_nonpos_left hle hb_pos
  have hnum_le : 2 * μ - 1 ≤ 0 := by
    by_contra hpos
    push Not at hpos
    have : 0 < (2 * μ - 1) / μ := div_pos hpos hμ
    linarith
  linarith

/-- **Collar-Split Balanced-Nodal Four-Term Jump Criterion for `μ ≤ 1 / 2`**:
for any eigenvector `resolvent w = μ • w` (`0 < μ`) with `(balancedNodalGraph (rieszLift w)).val.fst ≠ 0`
and any collar radius `0 ≤ R`, if the four-term nonnegative balanced-nodal jump sum is at least
`(1 + thetaGroundPotentialBound / Real.cosh (R / 2)) * ‖b.val.fst‖ ^ 2 + (thetaGroundPotentialBound / riemannKernelReal R) * ‖thetaToVolume b.val.fst‖ ^ 2`,
then `μ ≤ 1 / 2`. -/
theorem eigenvalue_le_one_half_of_four_term_balancedNodal_ge_collar_split
    {μ R : ℝ} (hμ : 0 < μ) (hR : 0 ≤ R) {w : MassSpace} (heig : resolvent w = μ • w)
    (hb : (balancedNodalGraph (rieszLift w)).val.fst ≠ 0)
    (hjump :
      let q := rieszLift w
      (1 + thetaGroundPotentialBound / Real.cosh (R / 2)) *
          ‖(balancedNodalGraph q).val.fst‖ ^ 2 +
        (thetaGroundPotentialBound / riemannKernelReal R) *
          ‖thetaToVolume (balancedNodalGraph q).val.fst‖ ^ 2 ≤
        stationaryEnergy (thetaProduct (balancedNodalGraph q).val.fst) +
          ⟪primeGenerator (balancedNodalGraph q).val.fst, (balancedNodalGraph q).val.fst⟫_ℝ -
          ‖q.val.fst‖ ^ 4 *
            ⟪(fullGroundEquiv (posGraph q)).val.snd, (fullGroundEquiv (negGraph q)).val.snd⟫_ℝ +
          ‖q.val.fst‖ ^ 4 *
            ⟪primeShiftOperator (posGraph q).val.fst, (negGraph q).val.fst⟫_ℝ) :
    μ ≤ 1 / 2 := by
  have hcol := (norm_sq_sub_groundPotential_le_collar_split hR
    (balancedNodalGraph (rieszLift w)).val.fst).1
  exact eigenvalue_le_one_half_of_four_term_balancedNodal_ge_groundPotential hμ heig hb
    (hcol.trans hjump)

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

/-- Negative-lobe (`negGraph q`) four-term jump excess criterion for `μ ≤ 1 / 2`. -/
theorem eigenvalue_le_one_half_of_four_term_negGraph_ge_groundPotential
    {μ : ℝ} (hμ : 0 < μ) {w : MassSpace} (heig : resolvent w = μ • w)
    (hn : (negGraph (rieszLift w)).val.fst ≠ 0)
    (hjump :
      let q := rieszLift w
      ‖(negGraph q).val.fst‖ ^ 2 -
          ⟪groundPotentialOperator (negGraph q).val.fst, (negGraph q).val.fst⟫_ℝ ≤
        stationaryEnergy (thetaProduct (negGraph q).val.fst) +
          ⟪primeGenerator (negGraph q).val.fst, (negGraph q).val.fst⟫_ℝ -
          ⟪(fullGroundEquiv (posGraph q)).val.snd, (fullGroundEquiv (negGraph q)).val.snd⟫_ℝ +
          ⟪primeShiftOperator (posGraph q).val.fst, (negGraph q).val.fst⟫_ℝ) :
    μ ≤ 1 / 2 := by
  have hbal1 := negGraph_five_term_jump_eq_diagonals_of_eigenvector hμ.ne' heig
  have hbal2 := arch_add_primeDiagonal_eq_norm_sq_sub_groundPotential (negGraph (rieszLift w)).val.fst
  have hn_pos : 0 < ‖(negGraph (rieszLift w)).val.fst‖ ^ 2 :=
    sq_pos_of_pos (norm_pos_iff.mpr hn)
  have hle : ((2 * μ - 1) / μ) * ‖(negGraph (rieszLift w)).val.fst‖ ^ 2 ≤ 0 := by
    linarith [hbal1, hbal2, hjump]
  have hdiv_le : (2 * μ - 1) / μ ≤ 0 :=
    nonpos_of_mul_nonpos_left hle hn_pos
  have hnum_le : 2 * μ - 1 ≤ 0 := by
    by_contra hpos
    push Not at hpos
    have : 0 < (2 * μ - 1) / μ := div_pos hpos hμ
    linarith
  linarith

/-- **Cofinal (`liminf`) Off-Diagonal Prime-Clock Nonnegativity Criterion for `μ ≤ 1 / 2`**:
for any nonzero eigenvector `resolvent w = μ • w`, if for every `0 < ε` and every cutoff `k : ℕ`,
there exist cofinally many scales `N` (`∃ᶠ N : ℕ in atTop`) at which every prime-clock packet `S`
within the canonical realization tolerance satisfies
`-ε ≤ offDiagSourcePairSum S (canonicalPrimeGraphClockAtom k N)`, then `μ ≤ 1 / 2`. -/
theorem eigenvalue_le_one_half_of_frequently_offDiag_primeClock_ge_neg
    {μ : ℝ} {w : MassSpace} (hw : w ≠ 0) (heig : resolvent w = μ • w)
    (hliminf : ∀ ε > 0, ∀ k : ℕ, ∃ᶠ N : ℕ in atTop,
      ∀ S : Finset ℕ,
        ‖(∑ p ∈ S, canonicalPrimeGraphClockAtom k N p) - rieszLift w‖ <
          ((2 * μ - 1) / (4 * μ)) * ‖(rieszLift w).val.fst‖ ^ 2 /
            (2 + 2 * ‖rieszLift w‖) →
        (∑ p ∈ S, ‖canonicalPrimeGraphClockAtom k N p‖ ^ 2) <
          ((2 * μ - 1) / (4 * μ)) * ‖(rieszLift w).val.fst‖ ^ 2 /
            (2 + 2 * ‖rieszLift w‖) →
        -ε ≤ offDiagSourcePairSum S (canonicalPrimeGraphClockAtom k N)) :
    μ ≤ 1 / 2 := by
  by_contra hgt
  push Not at hgt
  obtain ⟨hneg, k, hev⟩ :=
    exists_cutoff_eventually_offDiag_primeClock_neg_of_eigenvector_gt_half hgt hw heig 0
  set ε := -(((1 - 2 * μ) / (2 * μ)) * ‖(rieszLift w).val.fst‖ ^ 2) / 2
  have hε : 0 < ε := by dsimp [ε]; linarith
  have hfreq := hliminf ε hε k
  obtain ⟨N, hge, ⟨S, _, happ, hdiag, hoff⟩⟩ := (hfreq.and_eventually hev).exists
  have hge' := hge S happ hdiag
  dsimp [ε] at hge'
  linarith

end GaloisForLFunctions.BiScaleUncertainty
