import GaloisForLFunctions.ArithmeticCriticalityTheory.NonnegativeConeZeroFormCriterion
import GaloisForLFunctions.ArithmeticCompensationTheory.TheApertureFloorMustDecayDoublyExponentially
import GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy.TheApertureFloorUnderAbsoluteDecay

/-!
# Transport in aperture and the ceiling Lyapunov identity

This module resolves Open Problem 6 of `ArithmeticOrientationTheory/README.md` by establishing the
exact aperture-transport and aperture-derivative identities for the full zero form `Ẑ`, the window
floor `w(R)`, the `Φ`-gauge plateau family `Θ_L = Φ u_L`, and the restricted Weil ground energy
`μ(A) = ccmRestrictedWeilGroundEnergy A`, together with their sign-definite jump terms and their
compatibility with the doubly exponential Gaussian ceiling.

1. **Two-aperture gauge conservation and sign-definite step jump (§1).** For any test `F ∈ C²_c(ℝ)`
   and any window gauge `M ∈ C²_c(ℝ)` (`0 ≤ M ≤ 1`, `M = 0` outside `(−R, R)`, `M = 1` on `supp F`),
   the full zero form splits into the sign-definite jump energy `J_M(F) ≥ 0`, the boundary-killing
   potential `∫ F² (−𝒲M)`, and the Lorentz polar forcing `2 E_+(F)² − 2 E_−(F)²`
   (`fullZeroForm_eq_windowGauge_balance`). Comparing two nested window gauges `0 ≤ M₁ ≤ M₂ ≤ 1`
   (`M₁ = M₂ = 1` on `supp F`), each shift jump profile is monotone (`gaugeJumpProfile_mono_gauge`),
   the potential drop at every plateau point `M₁(x) = M₂(x)` is the nonnegative boundary-shell flux
   `𝒲M₂(x) − 𝒲M₁(x) ≥ 0` (`poleFreeWeilOperator_sub_eq_shellFlux`,
   `poleFreeWeilOperator_mono_of_eq_at_point`), and the sign-definite aperture-step jump increment
   `J_{M₂}(F) − J_{M₁}(F) ≥ 0` equals the boundary-shell flux `∫ F² (𝒲M₂ − 𝒲M₁)` identically
   (`gaugeStepJumpEnergy_eq_gaugeStepBoundaryFlux`, `gaugeStepJumpEnergy_nonneg`).
2. **Exact aperture derivatives of the window killing potential and Suzuki window floor (§2).**
   At every interior point `|x| < R`, the archimedean window killing potential `archWindowKilling R x`
   has exact aperture derivative `−(archBoundaryJumpRate R x + 3/2) < 0`
   (`hasDerivAt_archWindowKilling`), where `archBoundaryJumpRate R x = ν(R − x) + ν(R + x) > 0` is
   the outward Lévy jump rate across the aperture boundaries `±R`. Globally, Suzuki's window floor
   `windowFloor R = −log(2R) − (3/2)R − (γ + log π) − 4R³` has exact aperture derivative
   `−(1/R + 3/2 + 12R²) < 0` (`hasDerivAt_windowFloor`), is strictly antitone on `(0, ∞)`
   (`strictAntiOn_windowFloor`), and satisfies the integral transport identity
   `windowFloor R₁ − windowFloor R₂ = ∫_{R₁}^{R₂} (1/R + 3/2 + 12R²) dR` (`windowFloor_sub_eq_integral`).
3. **The exact `Φ`-gauge boundary-defect identity (§3).** Because `∫ Φ(x) cosh(x/2) dx = 1/2`, every
   profile `u ∈ C²_c(ℝ)` obeys the exact identity
   `Ẑ(Φ u) = J_Φ(u) − thetaBoundaryDefectMass u + 2 (thetaBoundaryFlux u)² − 2 oddPoleMoment(Φ u)²`
   (`fullZeroForm_phiDoob_eq_jump_sub_defect_add_flux`), where `J_Φ(u) ≥ 0` is the sign-definite
   `Φ`-gauge jump energy, `thetaBoundaryDefectMass u = ∫ (1 − u)² Φ cosh(x/2) ≥ 0` is the
   sign-definite exterior boundary defect mass, and `thetaBoundaryFlux u = ∫ (1 − u) Φ cosh(x/2)` is
   the exterior boundary flux. On the plateau truncations `Θ_L = Φ u_L` (`u_L = smoothPlateau L`),
   `oddPoleMoment Θ_L = 0` and all three boundary terms are supported on the exterior collar `|x| > L`
   and bounded by `tailWeight L` (`fullZeroForm_thetaPlateau_eq`).
4. **The aperture spectral jump of `μ(A)` and its total-jump equivalences for RH (§4).** For
   `a.1 ≤ b.1`, the aperture spectral jump `apertureSpectralJump a b = μ(a) − μ(b)` equals the
   variational ground-state relaxation `Q_b(v_{a,b}) − Q_b(u_b) ≥ 0`
   (`apertureSpectralJump_eq_groundState_relaxation`), is sign-definite (`apertureSpectralJump_nonneg`),
   and telescopes along any aperture chain (`sum_apertureSpectralJump_eq`). While any additive step
   leaving a positive margin `c > 0` below `1/5000` is impossible along unbounded apertures
   (`not_additive_step_transport`), replacing that margin by the exact initial energy `μ(A₀)` yields
   an exact characterization of RH: along any monotone unbounded sequence `A_j → ∞`, RH is equivalent
   to `∀ J, ∑_{j < J} Δ_spec(A_j, A_{j+1}) ≤ μ(A₀)` (`riemannHypothesis_iff_sum_apertureSpectralJump_le`)
   and to `HasSum (fun j => Δ_spec(A_j, A_{j+1})) μ(A₀)` (`riemannHypothesis_iff_hasSum_apertureSpectralJump`),
   with doubly exponential tail `0 ≤ μ(A₀) − ∑_{j < J} Δ_spec(A_j, A_{j+1}) ≤ K exp(apertureCeilingExponent A_J)`.
5. **The ceiling-renormalized Lyapunov functional and vanishing-floor transport (§5).** With the
   ceiling loss primitive `ceilingLossPrimitive A = π e^{2(A−2)} − (11/2)A` (derivative
   `ceilingLossRate A = 2π e^{2(A−2)} − 11/2 > 0` for `A ≥ 2`), the ceiling-renormalized ground
   energy `ceilingScaledGroundEnergy A = exp(ceilingLossPrimitive A) · μ(A)` is unconditionally
   bounded above by `K` on `[3, ∞)` (`exists_ceilingScaledGroundEnergy_le`), and for any smooth path
   `μ`, `−μ' ≤ β' μ` is equivalent to nonnegativity of the derivative of the Lyapunov functional
   `e^{β(A)} μ(A)` (`hasDerivAt_exp_mul_floor`, `monotoneOn_exp_mul_of_relative_decay`). Dropping the
   impossible half-summability `∑ c_i ≤ 1/2` to `c_j ≤ 1` (`0 ≤ q_j`) gives the ceiling-compatible
   vanishing-floor relative transport theorem (`riemannHypothesis_of_vanishing_relative_step`,
   `riemannHypothesis_iff_exists_relative_step`), realized by the doubly exponential step factors
   `ceilingStepFactor`, together with graded negative-floor additive transport feeding the zero-width
   dictionary (`groundEnergy_ge_neg_exp_of_graded_additive_step`).
-/

open MeasureTheory Set Filter Topology Finset RHTower RHTower.CHMDPolar
open GaloisForLFunctions.ArithmeticCriticalityTheory
open GaloisForLFunctions.ArithmeticCompensationTheory
open GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy
open GaloisForLFunctions.SquareRootThreshold

noncomputable section

namespace GaloisForLFunctions.ArithmeticOrientationTheory

/-! ## §1. Two-Aperture Gauge Conservation and the Sign-Definite Jump Increment -/

/-- The aperture-step jump-energy increment `J_{M₂}(F) − J_{M₁}(F)` between two window gauges. -/
def gaugeStepJumpEnergy (M₁ M₂ F : ℝ → ℝ) : ℝ :=
  signedJumpEnergy M₂ F - signedJumpEnergy M₁ F

/-- The aperture-step boundary-shell flux `∫ F(x)² (𝒲M₂(x) − 𝒲M₁(x)) dx` between two window gauges. -/
def gaugeStepBoundaryFlux (M₁ M₂ F : ℝ → ℝ) : ℝ :=
  ∫ x, F x ^ 2 * (poleFreeWeilOperator M₂ x - poleFreeWeilOperator M₁ x)

/-- Pointwise monotonicity of the shift jump under gauge enlargement `0 ≤ M₁ ≤ M₂`. -/
theorem signedShiftJump_mono_gauge {M₁ M₂ F : ℝ → ℝ} (hnn : ∀ y, 0 ≤ M₁ y)
    (hle : ∀ y, M₁ y ≤ M₂ y) (t x : ℝ) :
    signedShiftJump M₁ F t x ≤ signedShiftJump M₂ F t x := by
  unfold signedShiftJump
  have h1 : 0 ≤ M₁ x * M₁ (x + t) := mul_nonneg (hnn x) (hnn (x + t))
  have h2 : M₁ x * M₁ (x + t) ≤ M₂ x * M₂ (x + t) :=
    mul_le_mul (hle x) (hle (x + t)) (hnn (x + t)) ((hnn x).trans (hle x))
  exact mul_le_mul_of_nonneg_right h2 (sq_nonneg _)

/-- Every shift jump profile `gaugeJumpProfile M F t` is monotone under gauge enlargement `0 ≤ M₁ ≤ M₂`. -/
theorem gaugeJumpProfile_mono_gauge {M₁ M₂ F : ℝ → ℝ} (hF : Continuous F)
    (hM₁ : Continuous M₁) (hM₁c : HasCompactSupport M₁)
    (hM₂ : Continuous M₂) (hM₂c : HasCompactSupport M₂)
    (hnn : ∀ y, 0 ≤ M₁ y) (hle : ∀ y, M₁ y ≤ M₂ y) (t : ℝ) :
    gaugeJumpProfile M₁ F t ≤ gaugeJumpProfile M₂ F t := by
  have hut : Continuous fun x => F (x + t) := hF.comp (continuous_id.add continuous_const)
  have i1 : Integrable fun x => signedShiftJump M₁ F t x := by
    unfold signedShiftJump
    exact ((hM₁.mul (hM₁.comp (continuous_id.add continuous_const))).mul
      ((hF.sub hut).pow 2)).integrable_of_hasCompactSupport hM₁c.mul_right.mul_right
  have i2 : Integrable fun x => signedShiftJump M₂ F t x := by
    unfold signedShiftJump
    exact ((hM₂.mul (hM₂.comp (continuous_id.add continuous_const))).mul
      ((hF.sub hut).pow 2)).integrable_of_hasCompactSupport hM₂c.mul_right.mul_right
  exact integral_mono i1 i2 (signedShiftJump_mono_gauge hnn hle t)

/-- **Full zero form in a window gauge.** For any smooth compactly supported test `F` and any window
gauge `M ∈ C²_c(ℝ)` (`0 ≤ M ≤ 1`, vanishing outside `(−R, R)`, `M = 1` on `supp F`), the full zero
form splits into the sign-definite jump energy `J_M(F) ≥ 0`, the boundary-killing potential
`∫ F² (−𝒲M)`, and the Lorentz polar forcing `2 E_+(F)² − 2 E_−(F)²`. -/
theorem fullZeroForm_eq_windowGauge_balance {F M : ℝ → ℝ} {R : ℝ} (hF : ContDiff ℝ 2 F)
    (hFc : HasCompactSupport F) (hMd : ContDiff ℝ 2 M) (hMcs : HasCompactSupport M)
    (hle : ∀ y, M y ≤ 1) (hnn : ∀ y, 0 ≤ M y) (hzero : ∀ y, R ≤ |y| → M y = 0)
    (hFM : ∀ x, F x ≠ 0 → M x = 1) :
    fullZeroForm F =
      signedJumpEnergy M F + (∫ x, F x ^ 2 * -poleFreeWeilOperator M x) +
        2 * evenPoleMoment F ^ 2 - 2 * oddPoleMoment F ^ 2 := by
  have hQ := markovEnergy_eq_gauge_window hF hFc hMd hMcs hle hnn hzero hFM
  have hpot : (∫ x, F x ^ 2 * M x * -poleFreeWeilOperator M x) =
      ∫ x, F x ^ 2 * -poleFreeWeilOperator M x := by
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    by_cases hx : F x = 0
    · simp [hx]
    · simp [hFM x hx]
  unfold fullZeroForm
  rw [hQ, hpot]
  ring

/-- **Pointwise boundary-shell flux formula.** At any point `x` where `M₁ x = M₂ x`, the diagonal
archimedean density and the Euler–Mascheroni/π constant cancel identically in
`𝒲M₂(x) − 𝒲M₁(x)`, leaving only the prime and archimedean boundary-shell shifts of `M₂ − M₁`. -/
theorem poleFreeWeilOperator_sub_eq_shellFlux {M₁ M₂ : ℝ → ℝ} {K₁ K₂ x : ℝ}
    (hM₁c : Continuous M₁) (hLip₁ : ∀ a b, |M₁ a - M₁ b| ≤ K₁ * |a - b|)
    (hM₂c : Continuous M₂) (hLip₂ : ∀ a b, |M₂ a - M₂ b| ≤ K₂ * |a - b|)
    (hx : M₁ x = M₂ x) :
    poleFreeWeilOperator M₂ x - poleFreeWeilOperator M₁ x =
      (profilePrimeSum M₂ x - profilePrimeSum M₁ x) +
        ∫ u in Ioi (0 : ℝ), archLevyDensity u *
          ((M₂ (x + u) - M₁ (x + u)) + (M₂ (x - u) - M₁ (x - u))) := by
  have hI₁ : IntegrableOn (profileArchTerm M₁ x) (Ioi 0) :=
    integrableOn_profileArchTerm hM₁c hLip₁ x
  have hI₂ : IntegrableOn (profileArchTerm M₂ x) (Ioi 0) :=
    integrableOn_profileArchTerm hM₂c hLip₂ x
  have harch : (∫ u in Ioi (0 : ℝ), profileArchTerm M₁ x u) -
      (∫ u in Ioi (0 : ℝ), profileArchTerm M₂ x u) =
      ∫ u in Ioi (0 : ℝ), archLevyDensity u *
        ((M₂ (x + u) - M₁ (x + u)) + (M₂ (x - u) - M₁ (x - u))) := by
    rw [← integral_sub hI₁ hI₂]
    refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
    unfold profileArchTerm
    rw [hx]
    ring
  unfold poleFreeWeilOperator
  rw [hx, ← harch]
  ring

/-- At any plateau point `x` where `M₁ x = M₂ x` and `M₁ ≤ M₂` globally, `𝒲M₁(x) ≤ 𝒲M₂(x)`
(equivalently, the boundary-killing potential `−𝒲M(x)` decreases as the gauge widens). -/
theorem poleFreeWeilOperator_mono_of_eq_at_point {M₁ M₂ : ℝ → ℝ} {R₁ R₂ K₁ K₂ x : ℝ}
    (hM₁c : Continuous M₁) (hLip₁ : ∀ a b, |M₁ a - M₁ b| ≤ K₁ * |a - b|)
    (hnn₁ : ∀ y, 0 ≤ M₁ y) (hle₁ : ∀ y, M₁ y ≤ 1) (hzero₁ : ∀ y, R₁ ≤ |y| → M₁ y = 0)
    (hM₂c : Continuous M₂) (hLip₂ : ∀ a b, |M₂ a - M₂ b| ≤ K₂ * |a - b|)
    (hnn₂ : ∀ y, 0 ≤ M₂ y) (hle₂ : ∀ y, M₂ y ≤ 1) (hzero₂ : ∀ y, R₂ ≤ |y| → M₂ y = 0)
    (hle : ∀ y, M₁ y ≤ M₂ y) (hx : M₁ x = M₂ x) :
    poleFreeWeilOperator M₁ x ≤ poleFreeWeilOperator M₂ x := by
  have hdec₁ : ∀ y, |M₁ y| ≤ Real.exp (8 * |R₁|) * Real.exp (-(8 * |y|)) := fun y => by
    by_cases hy : |y| < R₁
    · rw [abs_of_nonneg (hnn₁ y), ← Real.exp_add]
      exact (hle₁ y).trans (Real.one_le_exp (by nlinarith [le_abs_self R₁]))
    · rw [hzero₁ y (not_lt.mp hy), abs_zero]; positivity
  have hdec₂ : ∀ y, |M₂ y| ≤ Real.exp (8 * |R₂|) * Real.exp (-(8 * |y|)) := fun y => by
    by_cases hy : |y| < R₂
    · rw [abs_of_nonneg (hnn₂ y), ← Real.exp_add]
      exact (hle₂ y).trans (Real.one_le_exp (by nlinarith [le_abs_self R₂]))
    · rw [hzero₂ y (not_lt.mp hy), abs_zero]; positivity
  have hP₁ : Summable fun n : ℕ => vonMangoldtAtom n * (M₁ (x + Real.log n) + M₁ (x - Real.log n)) :=
    summable_atom_mul_profileShift hdec₁ x
  have hP₂ : Summable fun n : ℕ => vonMangoldtAtom n * (M₂ (x + Real.log n) + M₂ (x - Real.log n)) :=
    summable_atom_mul_profileShift hdec₂ x
  have hP : profilePrimeSum M₁ x ≤ profilePrimeSum M₂ x := by
    unfold profilePrimeSum
    exact hP₁.tsum_le_tsum (fun n => mul_le_mul_of_nonneg_left
      (add_le_add (hle (x + Real.log n)) (hle (x - Real.log n))) (vonMangoldtAtom_nonneg n)) hP₂
  have hA : (∫ u in Ioi (0 : ℝ), profileArchTerm M₂ x u) ≤
      ∫ u in Ioi (0 : ℝ), profileArchTerm M₁ x u := by
    refine setIntegral_mono_on (integrableOn_profileArchTerm hM₂c hLip₂ x)
      (integrableOn_profileArchTerm hM₁c hLip₁ x) measurableSet_Ioi fun u hu => ?_
    unfold profileArchTerm
    rw [hx]
    have hω := (archLevyDensity_pos hu).le
    have hsum : M₁ (x + u) + M₁ (x - u) ≤ M₂ (x + u) + M₂ (x - u) :=
      add_le_add (hle (x + u)) (hle (x - u))
    linarith [mul_le_mul_of_nonneg_left hsum hω]
  unfold poleFreeWeilOperator
  rw [hx]
  linarith

/-- **Two-aperture conservation law.** For any smooth compactly supported test `F` and any two
window gauges `M₁, M₂` equal to `1` on `supp F`, the aperture-step jump increment
`J_{M₂}(F) − J_{M₁}(F)` equals the boundary-shell flux `∫ F(x)² (𝒲M₂(x) − 𝒲M₁(x)) dx`. -/
theorem gaugeStepJumpEnergy_eq_gaugeStepBoundaryFlux {F M₁ M₂ : ℝ → ℝ} {R₁ R₂ : ℝ}
    (hF : ContDiff ℝ 2 F) (hFc : HasCompactSupport F)
    (hM₁d : ContDiff ℝ 2 M₁) (hM₁cs : HasCompactSupport M₁)
    (hle₁ : ∀ y, M₁ y ≤ 1) (hnn₁ : ∀ y, 0 ≤ M₁ y) (hzero₁ : ∀ y, R₁ ≤ |y| → M₁ y = 0)
    (hFM₁ : ∀ x, F x ≠ 0 → M₁ x = 1)
    (hM₂d : ContDiff ℝ 2 M₂) (hM₂cs : HasCompactSupport M₂)
    (hle₂ : ∀ y, M₂ y ≤ 1) (hnn₂ : ∀ y, 0 ≤ M₂ y) (hzero₂ : ∀ y, R₂ ≤ |y| → M₂ y = 0)
    (hFM₂ : ∀ x, F x ≠ 0 → M₂ x = 1) :
    gaugeStepJumpEnergy M₁ M₂ F = gaugeStepBoundaryFlux M₁ M₂ F := by
  have h1 := markovEnergy_eq_gauge_window hF hFc hM₁d hM₁cs hle₁ hnn₁ hzero₁ hFM₁
  have h2 := markovEnergy_eq_gauge_window hF hFc hM₂d hM₂cs hle₂ hnn₂ hzero₂ hFM₂
  obtain ⟨K₁, -, hK₁⟩ := exists_lipschitz_bound_of_compactSupport (hM₁d.of_le (by norm_num)) hM₁cs
  obtain ⟨K₂, -, hK₂⟩ := exists_lipschitz_bound_of_compactSupport (hM₂d.of_le (by norm_num)) hM₂cs
  have hdec₁ : ∀ y, |M₁ y| ≤ Real.exp (8 * |R₁|) * Real.exp (-(8 * |y|)) := fun y => by
    by_cases hy : |y| < R₁
    · rw [abs_of_nonneg (hnn₁ y), ← Real.exp_add]
      exact (hle₁ y).trans (Real.one_le_exp (by nlinarith [le_abs_self R₁]))
    · rw [hzero₁ y (not_lt.mp hy), abs_zero]; positivity
  have hdec₂ : ∀ y, |M₂ y| ≤ Real.exp (8 * |R₂|) * Real.exp (-(8 * |y|)) := fun y => by
    by_cases hy : |y| < R₂
    · rw [abs_of_nonneg (hnn₂ y), ← Real.exp_add]
      exact (hle₂ y).trans (Real.one_le_exp (by nlinarith [le_abs_self R₂]))
    · rw [hzero₂ y (not_lt.mp hy), abs_zero]; positivity
  have hg₁ : Continuous (poleFreeWeilOperator M₁) :=
    continuous_poleFreeWeilOperator hM₁d.continuous (fun a b => hK₁ b a) hdec₁
  have hg₂ : Continuous (poleFreeWeilOperator M₂) :=
    continuous_poleFreeWeilOperator hM₂d.continuous (fun a b => hK₂ b a) hdec₂
  have hi₁ : Integrable fun x => F x ^ 2 * M₁ x * -poleFreeWeilOperator M₁ x :=
    (((hF.continuous.pow 2).mul hM₁d.continuous).mul hg₁.neg).integrable_of_hasCompactSupport
      (CHMDPolar.hasCompactSupport_sq hFc).mul_right.mul_right
  have hi₂ : Integrable fun x => F x ^ 2 * M₂ x * -poleFreeWeilOperator M₂ x :=
    (((hF.continuous.pow 2).mul hM₂d.continuous).mul hg₂.neg).integrable_of_hasCompactSupport
      (CHMDPolar.hasCompactSupport_sq hFc).mul_right.mul_right
  have hflux : gaugeStepBoundaryFlux M₁ M₂ F =
      (∫ x, F x ^ 2 * M₁ x * -poleFreeWeilOperator M₁ x) -
        ∫ x, F x ^ 2 * M₂ x * -poleFreeWeilOperator M₂ x := by
    unfold gaugeStepBoundaryFlux
    rw [← integral_sub hi₁ hi₂]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    by_cases hx : F x = 0
    · simp [hx]
    · simp only [hFM₁ x hx, hFM₂ x hx]
      ring
  unfold gaugeStepJumpEnergy
  linarith

/-- **Sign-definiteness of the aperture-step jump increment.** When `0 ≤ M₁ ≤ M₂ ≤ 1` and both
window gauges equal `1` on `supp F`, `0 ≤ gaugeStepJumpEnergy M₁ M₂ F` and
`0 ≤ gaugeStepBoundaryFlux M₁ M₂ F`. -/
theorem gaugeStepJumpEnergy_nonneg {F M₁ M₂ : ℝ → ℝ} {R₁ R₂ : ℝ}
    (hF : ContDiff ℝ 2 F) (hFc : HasCompactSupport F)
    (hM₁d : ContDiff ℝ 2 M₁) (hM₁cs : HasCompactSupport M₁)
    (hle₁ : ∀ y, M₁ y ≤ 1) (hnn₁ : ∀ y, 0 ≤ M₁ y) (hzero₁ : ∀ y, R₁ ≤ |y| → M₁ y = 0)
    (hFM₁ : ∀ x, F x ≠ 0 → M₁ x = 1)
    (hM₂d : ContDiff ℝ 2 M₂) (hM₂cs : HasCompactSupport M₂)
    (hle₂ : ∀ y, M₂ y ≤ 1) (hnn₂ : ∀ y, 0 ≤ M₂ y) (hzero₂ : ∀ y, R₂ ≤ |y| → M₂ y = 0)
    (hFM₂ : ∀ x, F x ≠ 0 → M₂ x = 1) (hle : ∀ y, M₁ y ≤ M₂ y) :
    0 ≤ gaugeStepJumpEnergy M₁ M₂ F ∧ 0 ≤ gaugeStepBoundaryFlux M₁ M₂ F := by
  have heq := gaugeStepJumpEnergy_eq_gaugeStepBoundaryFlux hF hFc hM₁d hM₁cs hle₁ hnn₁ hzero₁ hFM₁
    hM₂d hM₂cs hle₂ hnn₂ hzero₂ hFM₂
  obtain ⟨K₁, -, hK₁⟩ := exists_lipschitz_bound_of_compactSupport (hM₁d.of_le (by norm_num)) hM₁cs
  obtain ⟨K₂, -, hK₂⟩ := exists_lipschitz_bound_of_compactSupport (hM₂d.of_le (by norm_num)) hM₂cs
  have hflux : 0 ≤ gaugeStepBoundaryFlux M₁ M₂ F := by
    unfold gaugeStepBoundaryFlux
    refine integral_nonneg fun x => ?_
    by_cases hx : F x = 0
    · simp [hx]
    · have hmono := poleFreeWeilOperator_mono_of_eq_at_point
        hM₁d.continuous (fun a b => hK₁ b a) hnn₁ hle₁ hzero₁
        hM₂d.continuous (fun a b => hK₂ b a) hnn₂ hle₂ hzero₂ hle
        ((hFM₁ x hx).trans (hFM₂ x hx).symm)
      exact mul_nonneg (sq_nonneg _) (sub_nonneg.mpr hmono)
  exact ⟨heq ▸ hflux, hflux⟩

/-! ## §2. Exact Aperture-Derivative Identities for the Window Killing Potential and Suzuki Floor -/

/-- The pointwise archimedean window killing potential
`−½ log(1 − e^{−2(R−x)}) − ½ log(1 − e^{−2(R+x)}) − (3/2) R − (γ + log π)` at `|x| < R`. -/
def archWindowKilling (R x : ℝ) : ℝ :=
  -(1 / 2) * Real.log (1 - Real.exp (-2 * (R - x))) +
    -(1 / 2) * Real.log (1 - Real.exp (-2 * (R + x))) - 3 / 2 * R - 2 * archConstantReal

/-- The outward archimedean boundary Lévy jump rate `ν(R − x) + ν(R + x)` at `|x| < R`. -/
def archBoundaryJumpRate (R x : ℝ) : ℝ :=
  archDiagonalDensity (R - x) + archDiagonalDensity (R + x)

/-- At every interior point `|x| < R`, the outward boundary jump rate is strictly positive. -/
theorem archBoundaryJumpRate_pos {R x : ℝ} (hx : |x| < R) :
    0 < archBoundaryJumpRate R x := by
  have ha : 0 < R - x := by linarith [le_abs_self x]
  have hb : 0 < R + x := by linarith [neg_abs_le x]
  exact add_pos (archDiagonalDensity_pos ha) (archDiagonalDensity_pos hb)

/-- **Pointwise aperture-derivative identity for the window killing potential.** At every interior
point `|x| < R`, `∂_R archWindowKilling(R, x) = −(archBoundaryJumpRate(R, x) + 3/2) < 0`. -/
theorem hasDerivAt_archWindowKilling {R x : ℝ} (hx : |x| < R) :
    HasDerivAt (fun r => archWindowKilling r x)
      (-(archBoundaryJumpRate R x + 3 / 2)) R := by
  have ha : 0 < R - x := by linarith [le_abs_self x]
  have hb : 0 < R + x := by linarith [neg_abs_le x]
  have hda : HasDerivAt (fun r => -(1 / 2) * Real.log (1 - Real.exp (-2 * (r - x))))
      (-archDiagonalDensity (R - x)) R := by
    have h1 := (hasDerivAt_half_log_one_sub_exp ha).comp R ((hasDerivAt_id R).sub_const x)
    have h2 := h1.neg
    refine h2.congr_of_eventuallyEq (Eventually.of_forall fun r => by dsimp; ring) |>.congr_deriv ?_
    ring
  have hdb : HasDerivAt (fun r => -(1 / 2) * Real.log (1 - Real.exp (-2 * (r + x))))
      (-archDiagonalDensity (R + x)) R := by
    have h1 := (hasDerivAt_half_log_one_sub_exp hb).comp R ((hasDerivAt_id R).add_const x)
    have h2 := h1.neg
    refine h2.congr_of_eventuallyEq (Eventually.of_forall fun r => by dsimp; ring) |>.congr_deriv ?_
    ring
  have hlin : HasDerivAt (fun r => 3 / 2 * r) (3 / 2) R := by
    simpa using (hasDerivAt_id R).const_mul (3 / 2 : ℝ)
  have htot := ((hda.add hdb).sub hlin).sub_const (2 * archConstantReal)
  refine htot.congr_deriv ?_
  unfold archBoundaryJumpRate
  ring

/-- The Suzuki window-floor dissipation rate `1 / R + 3 / 2 + 12 R²`: boundary killing flux `1/R`
plus archimedean drift `3/2` plus odd polar forcing rate `12 R²`. -/
def windowFloorDissipationRate (R : ℝ) : ℝ :=
  1 / R + 3 / 2 + 12 * R ^ 2

theorem windowFloorDissipationRate_pos {R : ℝ} (hR : 0 < R) :
    0 < windowFloorDissipationRate R := by
  unfold windowFloorDissipationRate
  positivity

/-- **Exact aperture derivative of Suzuki's window floor.** For `0 < R`,
`d/dR windowFloor(R) = −windowFloorDissipationRate(R) = −(1/R + 3/2 + 12 R²) < 0`. -/
theorem hasDerivAt_windowFloor {R : ℝ} (hR : 0 < R) :
    HasDerivAt windowFloor (-windowFloorDissipationRate R) R := by
  have hlog : HasDerivAt (fun r => Real.log (2 * r)) (1 / R) R := by
    have h := (Real.hasDerivAt_log (by positivity : (2 * R : ℝ) ≠ 0)).comp R
      ((hasDerivAt_id R).const_mul 2)
    refine h.congr_deriv ?_
    field_simp [hR.ne']
  have h1 : HasDerivAt (fun r => -Real.log (2 * r)) (-(1 / R)) R := hlog.neg
  have h2 : HasDerivAt (fun r => 3 / 2 * r) (3 / 2) R := by
    simpa using (hasDerivAt_id R).const_mul (3 / 2 : ℝ)
  have h3 : HasDerivAt (fun r => 4 * r ^ 3) (12 * R ^ 2) R := by
    have hp := ((hasDerivAt_id R).pow 3).const_mul (4 : ℝ)
    refine hp.congr_deriv ?_
    dsimp
    ring
  have htot := (((h1.sub h2).sub_const (2 * archConstantReal)).sub h3)
  refine htot.congr_deriv ?_
  unfold windowFloorDissipationRate
  ring

/-- Suzuki's window floor `windowFloor` is strictly antitone on `(0, ∞)`. -/
theorem strictAntiOn_windowFloor : StrictAntiOn windowFloor (Ioi 0) := by
  refine strictAntiOn_of_hasDerivWithinAt_neg (convex_Ioi 0)
    (f' := fun R => -windowFloorDissipationRate R) ?_ ?_ ?_
  · intro R hR
    exact (hasDerivAt_windowFloor hR).continuousAt.continuousWithinAt
  · intro R hR
    rw [interior_Ioi] at hR
    exact (hasDerivAt_windowFloor hR).hasDerivWithinAt
  · intro R hR
    rw [interior_Ioi] at hR
    exact neg_neg_of_pos (windowFloorDissipationRate_pos hR)

/-- **Integral aperture-transport identity for Suzuki's window floor.** For `0 < R₁ ≤ R₂`,
`windowFloor R₁ − windowFloor R₂ = ∫_{R₁}^{R₂} windowFloorDissipationRate(R) dR`. -/
theorem windowFloor_sub_eq_integral {R₁ R₂ : ℝ} (hR₁ : 0 < R₁) (hR : R₁ ≤ R₂) :
    windowFloor R₁ - windowFloor R₂ =
      ∫ R in R₁..R₂, windowFloorDissipationRate R := by
  have hcont : ContinuousOn windowFloorDissipationRate (uIcc R₁ R₂) := by
    rw [uIcc_of_le hR]
    unfold windowFloorDissipationRate
    refine ((continuousOn_const.div continuousOn_id fun x hx => ?_).add continuousOn_const).add
      (continuousOn_const.mul (continuousOn_id.pow 2))
    dsimp at *
    linarith [hx.1]
  have hderiv : ∀ x ∈ uIcc R₁ R₂, HasDerivAt (fun r => -windowFloor r)
      (windowFloorDissipationRate x) x := by
    intro x hx
    rw [uIcc_of_le hR] at hx
    have hx0 : 0 < x := lt_of_lt_of_le hR₁ hx.1
    exact (hasDerivAt_windowFloor hx0).neg.congr_deriv (neg_neg _)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable]
  ring

/-! ## §3. The Exact `Φ`-Gauge Boundary-Defect Identity and Doubly Exponential Localization -/

/-- The `Φ`-gauge exterior boundary defect mass `∫ (1 − u(x))² Φ(x) cosh(x/2) dx`. -/
def thetaBoundaryDefectMass (u : ℝ → ℝ) : ℝ :=
  ∫ x, (1 - u x) ^ 2 * riemannKernelReal x * Real.cosh (x / 2)

/-- The `Φ`-gauge exterior boundary flux `∫ (1 − u(x)) Φ(x) cosh(x/2) dx`. -/
def thetaBoundaryFlux (u : ℝ → ℝ) : ℝ :=
  ∫ x, (1 - u x) * riemannKernelReal x * Real.cosh (x / 2)

/-- The `Φ`-gauge exterior boundary defect mass is always sign-definite (`≥ 0`). -/
theorem thetaBoundaryDefectMass_nonneg (u : ℝ → ℝ) :
    0 ≤ thetaBoundaryDefectMass u := by
  unfold thetaBoundaryDefectMass
  exact integral_nonneg fun x => mul_nonneg (mul_nonneg (sq_nonneg _)
    (riemannKernelReal_pos x).le) (Real.cosh_pos _).le

/-- When `u ≤ 1`, the `Φ`-gauge exterior boundary flux is nonnegative (`≥ 0`). -/
theorem thetaBoundaryFlux_nonneg_of_le_one {u : ℝ → ℝ} (hu1 : ∀ x, u x ≤ 1) :
    0 ≤ thetaBoundaryFlux u := by
  unfold thetaBoundaryFlux
  exact integral_nonneg fun x => mul_nonneg (mul_nonneg (by linarith [hu1 x])
    (riemannKernelReal_pos x).le) (Real.cosh_pos _).le

/-- For every `u ∈ C²_c(ℝ)`, `thetaBoundaryFlux u = 1/2 − evenPoleMoment (Φ u)`. -/
theorem thetaBoundaryFlux_eq {u : ℝ → ℝ} (hu : Continuous u) (huc : HasCompactSupport u) :
    thetaBoundaryFlux u = 1 / 2 - evenPoleMoment (phiDoobTest u) := by
  have hIc := integrable_riemannKernelReal_mul_cosh
  have hiu : Integrable fun x => riemannKernelReal x * u x * Real.cosh (x / 2) :=
    ((continuous_riemannKernelReal.mul hu).mul
      (Real.continuous_cosh.comp (continuous_id.div_const 2))).integrable_of_hasCompactSupport
      huc.mul_left.mul_right
  unfold thetaBoundaryFlux evenPoleMoment phiDoobTest
  rw [← integral_riemannKernelReal_cosh_half, ← integral_sub hIc hiu]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only
  ring

/-- **Exact `Φ`-gauge boundary-defect identity.** Because `∫ Φ(x) cosh(x/2) dx = 1/2`, every
`u ∈ C²_c(ℝ)` satisfies the exact identity
`Ẑ(Φ u) = J_Φ(u) − thetaBoundaryDefectMass u + 2 (thetaBoundaryFlux u)² − 2 oddPoleMoment(Φ u)²`,
with both `J_Φ(u) ≥ 0` and `thetaBoundaryDefectMass u ≥ 0` sign-definite. -/
theorem fullZeroForm_phiDoob_eq_jump_sub_defect_add_flux {u : ℝ → ℝ}
    (hu : ContDiff ℝ 2 u) (huc : HasCompactSupport u) :
    fullZeroForm (phiDoobTest u) =
      signedJumpEnergy riemannKernelReal u - thetaBoundaryDefectMass u +
        2 * thetaBoundaryFlux u ^ 2 - 2 * oddPoleMoment (phiDoobTest u) ^ 2 := by
  have hrep := markovEnergy_phiDoob_translateSpan_mul_eq (Finset.univ : Finset Unit) (fun _ => 1)
    (fun _ => 0) hu huc
  have hT1 : ∀ y, translateSpan (Finset.univ : Finset Unit) (fun _ => 1) (fun _ => 0) y = 1 :=
    fun y => by simp [translateSpan, translateGroundState, (riemannKernelReal_pos y).ne']
  have hS1 : ∀ x, translateSource (Finset.univ : Finset Unit) (fun _ => 1) (fun _ => 0) x =
      -Real.cosh (x / 2) := fun x => by
    simp [translateSource, translateCoshCoefficient, translateSinhCoefficient]
  simp only [hT1, hS1, one_mul, mul_one] at hrep
  have hIc := integrable_riemannKernelReal_mul_cosh
  have hiu : Integrable fun x => riemannKernelReal x * u x * Real.cosh (x / 2) :=
    ((continuous_riemannKernelReal.mul hu.continuous).mul
      (Real.continuous_cosh.comp (continuous_id.div_const 2))).integrable_of_hasCompactSupport
      huc.mul_left.mul_right
  have hiu2 : Integrable fun x => u x ^ 2 * riemannKernelReal x * Real.cosh (x / 2) :=
    (((hu.continuous.pow 2).mul continuous_riemannKernelReal).mul
      (Real.continuous_cosh.comp (continuous_id.div_const 2))).integrable_of_hasCompactSupport
      (CHMDPolar.hasCompactSupport_sq huc).mul_right.mul_right
  have hneg : (∫ x, u x ^ 2 * riemannKernelReal x * -Real.cosh (x / 2)) =
      -∫ x, u x ^ 2 * riemannKernelReal x * Real.cosh (x / 2) := by
    rw [← integral_neg]
    exact integral_congr_ae (Eventually.of_forall fun x => by simp only; ring)
  have hdef : thetaBoundaryDefectMass u =
      1 / 2 - 2 * evenPoleMoment (phiDoobTest u) +
        ∫ x, u x ^ 2 * riemannKernelReal x * Real.cosh (x / 2) := by
    have hisub : Integrable fun x =>
        riemannKernelReal x * Real.cosh (x / 2) -
          2 * (riemannKernelReal x * u x * Real.cosh (x / 2)) :=
      hIc.sub (hiu.const_mul 2)
    have hint : (∫ x, (1 - u x) ^ 2 * riemannKernelReal x * Real.cosh (x / 2)) =
        (∫ x, (riemannKernelReal x * Real.cosh (x / 2) -
          2 * (riemannKernelReal x * u x * Real.cosh (x / 2))) +
          u x ^ 2 * riemannKernelReal x * Real.cosh (x / 2)) :=
      integral_congr_ae (Eventually.of_forall fun x => by dsimp; ring)
    unfold thetaBoundaryDefectMass evenPoleMoment phiDoobTest
    rw [hint, integral_add hisub hiu2, integral_sub hIc (hiu.const_mul 2),
      integral_const_mul, integral_riemannKernelReal_cosh_half]
  rw [thetaBoundaryFlux_eq hu.continuous huc, hdef]
  unfold fullZeroForm
  rw [hrep, hneg]
  ring

/-- **Exact plateau-truncation identity and tail bounds.** Along `Θ_L = Φ u_L` (`u_L = smoothPlateau L`),
`Ẑ(Θ_L) = J_Φ(u_L) − thetaBoundaryDefectMass u_L + 2 (thetaBoundaryFlux u_L)²`, with every term
sign-definite and both boundary defect and boundary flux bounded by `tailWeight L`. -/
theorem fullZeroForm_thetaPlateau_eq (L : ℝ) :
    fullZeroForm (thetaPlateau L) =
      signedJumpEnergy riemannKernelReal (smoothPlateau L) -
        thetaBoundaryDefectMass (smoothPlateau L) +
        2 * thetaBoundaryFlux (smoothPlateau L) ^ 2 ∧
      0 ≤ signedJumpEnergy riemannKernelReal (smoothPlateau L) ∧
      0 ≤ thetaBoundaryDefectMass (smoothPlateau L) ∧
      thetaBoundaryDefectMass (smoothPlateau L) ≤ tailWeight L ∧
      0 ≤ thetaBoundaryFlux (smoothPlateau L) ∧
      thetaBoundaryFlux (smoothPlateau L) ≤ tailWeight L := by
  have hpeq : phiDoobTest (smoothPlateau L) = thetaPlateau L := rfl
  have hid := fullZeroForm_phiDoob_eq_jump_sub_defect_add_flux (contDiff_smoothPlateau L)
    (hasCompactSupport_smoothPlateau L)
  have hodd : oddPoleMoment (thetaPlateau L) = 0 :=
    oddPoleMoment_eq_zero_of_even fun x => by
      unfold thetaPlateau
      rw [riemannKernelReal_neg', smoothPlateau_neg]
  rw [hpeq, hodd] at hid
  have hJ0 : 0 ≤ signedJumpEnergy riemannKernelReal (smoothPlateau L) :=
    signedJumpEnergy_nonneg_of_nonneg fun y => (riemannKernelReal_pos y).le
  have hD0 := thetaBoundaryDefectMass_nonneg (smoothPlateau L)
  have hF0 := thetaBoundaryFlux_nonneg_of_le_one (smoothPlateau_le_one L)
  have hu0 := smoothPlateau_nonneg L
  have hu1 := smoothPlateau_le_one L
  have hIc := integrable_riemannKernelReal_mul_cosh
  have hiu : Integrable fun x => riemannKernelReal x * smoothPlateau L x * Real.cosh (x / 2) :=
    ((continuous_riemannKernelReal.mul (contDiff_smoothPlateau L).continuous).mul
      (Real.continuous_cosh.comp (continuous_id.div_const 2))).integrable_of_hasCompactSupport
      (hasCompactSupport_smoothPlateau L).mul_left.mul_right
  have hiu2 : Integrable fun x =>
      smoothPlateau L x ^ 2 * riemannKernelReal x * Real.cosh (x / 2) :=
    ((((contDiff_smoothPlateau L).continuous.pow 2).mul continuous_riemannKernelReal).mul
      (Real.continuous_cosh.comp (continuous_id.div_const 2))).integrable_of_hasCompactSupport
      (CHMDPolar.hasCompactSupport_sq (hasCompactSupport_smoothPlateau L)).mul_right.mul_right
  have hiF : Integrable fun x =>
      (1 - smoothPlateau L x) * riemannKernelReal x * Real.cosh (x / 2) := by
    refine (hIc.sub hiu).congr (Eventually.of_forall fun x => ?_)
    simp only [Pi.sub_apply]; ring
  have hiD : Integrable fun x =>
      (1 - smoothPlateau L x) ^ 2 * riemannKernelReal x * Real.cosh (x / 2) := by
    refine ((hIc.sub (hiu.const_mul 2)).add hiu2).congr (Eventually.of_forall fun x => ?_)
    simp only [Pi.add_apply, Pi.sub_apply]; ring
  have hFτ : thetaBoundaryFlux (smoothPlateau L) ≤ tailWeight L := by
    unfold thetaBoundaryFlux tailWeight
    refine integral_mono hiF (integrable_kernelTail_mul L) fun x => ?_
    by_cases hx : |x| ≤ L
    · simp [smoothPlateau_eq_one hx, kernelTail_eq_zero hx]
    · rw [kernelTail_eq (not_le.mp hx)]
      have hΦ := (riemannKernelReal_pos x).le
      have hc := (Real.cosh_pos (x / 2)).le
      have hκ := primeShiftConstant_nonneg
      have h1 : 1 - smoothPlateau L x ≤ 1 := by linarith [hu0 x]
      have h2 : 0 ≤ 1 - smoothPlateau L x := by linarith [hu1 x]
      nlinarith [mul_le_mul_of_nonneg_left h1 hΦ, mul_nonneg hΦ hc, mul_nonneg hΦ hκ,
        mul_nonneg (mul_nonneg h2 hΦ) hc]
  have hDF : thetaBoundaryDefectMass (smoothPlateau L) ≤ thetaBoundaryFlux (smoothPlateau L) := by
    unfold thetaBoundaryDefectMass thetaBoundaryFlux
    refine integral_mono hiD hiF fun x => ?_
    have hΦ := (riemannKernelReal_pos x).le
    have hc := (Real.cosh_pos (x / 2)).le
    have h1 : 1 - smoothPlateau L x ≤ 1 := by linarith [hu0 x]
    have h2 : 0 ≤ 1 - smoothPlateau L x := by linarith [hu1 x]
    have hsq : (1 - smoothPlateau L x) ^ 2 ≤ 1 - smoothPlateau L x := by nlinarith
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hsq hΦ) hc
  exact ⟨by linarith, hJ0, hD0, hDF.trans hFτ, hF0, hFτ⟩

/-! ## §4. The Aperture Spectral Jump of `μ(A)` and Its Total-Jump Equivalences for RH -/

/-- The **aperture spectral jump** `Δ_spec(a, b) = μ(a) − μ(b)` of the restricted Weil ground energy. -/
def apertureSpectralJump (a b : SuzukiPositiveAperture) : ℝ :=
  ccmRestrictedWeilGroundEnergy a - ccmRestrictedWeilGroundEnergy b

/-- **Variational ground-state representation of the aperture spectral jump.** For `a.1 ≤ b.1` and
any extension `v : CCMArchimedeanFormDomain b` of the normalized ground state
`u_a = ccmRestrictedWeilNormalizedGroundFormVector a` with `v.1 = u_a.1`, the spectral jump
`Δ_spec(a, b)` equals the quadratic relaxation `Q_b(v) − Q_b(u_b) ≥ 0`. -/
theorem apertureSpectralJump_eq_groundState_relaxation {a b : SuzukiPositiveAperture}
    (hab : a.1 ≤ b.1) {v : CCMArchimedeanFormDomain b}
    (hvu : v.1 = (ccmRestrictedWeilNormalizedGroundFormVector a).1) :
    apertureSpectralJump a b =
      ccmRestrictedWeilSourceQuadratic b v -
        ccmRestrictedWeilSourceQuadratic b (ccmRestrictedWeilNormalizedGroundFormVector b) := by
  unfold apertureSpectralJump
  rw [ccmRestrictedWeilSourceQuadratic_eq_of_val_eq hab hvu,
    ccmRestrictedWeilNormalizedGroundFormVector_source a,
    ccmRestrictedWeilNormalizedGroundFormVector_source b]

/-- **Sign-definiteness of the aperture spectral jump.** For `a.1 ≤ b.1`, `0 ≤ Δ_spec(a, b)`. -/
theorem apertureSpectralJump_nonneg {a b : SuzukiPositiveAperture} (hab : a.1 ≤ b.1) :
    0 ≤ apertureSpectralJump a b :=
  sub_nonneg.mpr (ccmRestrictedWeilGroundEnergy_antitone hab)

/-- Additivity (cocycle law) of the aperture spectral jump across three apertures. -/
theorem apertureSpectralJump_add (a b c : SuzukiPositiveAperture) :
    apertureSpectralJump a b + apertureSpectralJump b c = apertureSpectralJump a c := by
  unfold apertureSpectralJump
  ring

/-- **Telescoping aperture balance.** Along any sequence `A : ℕ → SuzukiPositiveAperture`,
`∑_{j < J} Δ_spec(A_j, A_{j+1}) = μ(A₀) − μ(A_J)` and
`μ(A_J) = μ(A₀) − ∑_{j < J} Δ_spec(A_j, A_{j+1})`. -/
theorem sum_apertureSpectralJump_eq (A : ℕ → SuzukiPositiveAperture) (J : ℕ) :
    ∑ j ∈ range J, apertureSpectralJump (A j) (A (j + 1)) =
      ccmRestrictedWeilGroundEnergy (A 0) - ccmRestrictedWeilGroundEnergy (A J) := by
  induction J with
  | zero => simp
  | succ J ih =>
    rw [Finset.sum_range_succ, ih]
    unfold apertureSpectralJump
    ring

/-- **Fixed-margin additive transport is impossible along unbounded apertures.** Starting at
`(A 0).1 ≤ 3/10`, any additive step bound `μ(A_j) − r_j ≤ μ(A_{j+1})` with
`∑_{j < J} r_j ≤ 1/5000 − c` (`c > 0`, in particular `1/10000`) is refuted by the Gaussian ceiling. -/
theorem not_additive_step_transport {A : ℕ → SuzukiPositiveAperture} {r : ℕ → ℝ} {c : ℝ}
    (hA0 : (A 0).1 ≤ 3 / 10) (hAtop : Tendsto (fun j => (A j).1) atTop atTop)
    (hc : 0 < c) (hr : ∀ J : ℕ, ∑ j ∈ range J, r j ≤ 1 / 5000 - c) :
    ¬ ∀ j, ccmRestrictedWeilGroundEnergy (A j) - r j ≤
      ccmRestrictedWeilGroundEnergy (A (j + 1)) := by
  intro hstep
  refine not_exists_positive_floor_along hAtop ⟨c, hc, fun J => ?_⟩
  have hbase : 1 / 5000 ≤ ccmRestrictedWeilGroundEnergy (A 0) :=
    one_div_5000_le_ccmRestrictedWeilGroundEnergy_threeTenths hA0
  have htel := sub_sum_le_of_additive_step
    (μ := fun j => ccmRestrictedWeilGroundEnergy (A j)) hstep J
  have hrJ := hr J
  linarith

/-- **Exact total-jump characterization of RH (partial-sum form).** Along any unbounded aperture
sequence `A_j → ∞`, the Riemann Hypothesis holds if and only if the cumulative aperture spectral
jump never exceeds the initial ground energy `μ(A₀)`:
`∀ J, ∑_{j < J} Δ_spec(A_j, A_{j+1}) ≤ μ(A₀)`. -/
theorem riemannHypothesis_iff_sum_apertureSpectralJump_le
    {A : ℕ → SuzukiPositiveAperture} (hAtop : Tendsto (fun j => (A j).1) atTop atTop) :
    RiemannHypothesis ↔
      ∀ J : ℕ, ∑ j ∈ range J, apertureSpectralJump (A j) (A (j + 1)) ≤
        ccmRestrictedWeilGroundEnergy (A 0) := by
  constructor
  · intro hRH J
    rw [sum_apertureSpectralJump_eq]
    linarith [ccmRestrictedWeilGroundEnergy_nonneg_of_riemannHypothesis' hRH (A J)]
  · intro hsum
    rw [riemannHypothesis_iff_not_bddAbove_groundEnergyNonnegApertures]
    rintro ⟨M, hM⟩
    obtain ⟨J, hJ⟩ := (hAtop.eventually_gt_atTop M).exists
    have hmem : (A J).1 ∈ groundEnergyNonnegApertures := by
      refine ⟨(A J).2, ?_⟩
      have h := hsum J
      rw [sum_apertureSpectralJump_eq] at h
      have hcongr : ccmRestrictedWeilGroundEnergy ⟨(A J).1, (A J).2⟩ =
          ccmRestrictedWeilGroundEnergy (A J) := by congr 1
      rw [hcongr]
      linarith
    exact absurd (hM hmem) (not_le.mpr hJ)

/-- **Exact total-jump characterization of RH (`HasSum` form).** Along any monotone unbounded
aperture sequence `A₀ ≤ A₁ ≤ …` with `A_j → ∞`, the Riemann Hypothesis holds if and only if the
sign-definite spectral jumps sum to `μ(A₀)` (`∑_{j=0}^∞ Δ_spec(A_j, A_{j+1}) = μ(A₀)`). -/
theorem riemannHypothesis_iff_hasSum_apertureSpectralJump
    {A : ℕ → SuzukiPositiveAperture} (hAmono : Monotone fun j => (A j).1)
    (hAtop : Tendsto (fun j => (A j).1) atTop atTop) :
    RiemannHypothesis ↔
      HasSum (fun j => apertureSpectralJump (A j) (A (j + 1)))
        (ccmRestrictedWeilGroundEnergy (A 0)) := by
  rw [hasSum_iff_tendsto_nat_of_nonneg fun j => apertureSpectralJump_nonneg (hAmono (Nat.le_succ j))]
  simp_rw [sum_apertureSpectralJump_eq]
  constructor
  · intro hRH
    have hlim : Tendsto (fun J => ccmRestrictedWeilGroundEnergy (A J)) atTop (𝓝 0) := by
      rw [Metric.tendsto_atTop]
      intro ε hε
      obtain ⟨A₀, hA₀⟩ :=
        (riemannHypothesis_iff_tendsto_ccmRestrictedWeilGroundEnergy_zero.mp hRH) ε hε
      obtain ⟨N, hN⟩ := eventually_atTop.mp (hAtop.eventually_ge_atTop A₀)
      refine ⟨N, fun J hJ => ?_⟩
      simpa [Real.dist_eq] using hA₀ (A J) (hN J hJ)
    simpa using tendsto_const_nhds.sub hlim
  · intro hlim
    have h0 : Tendsto (fun J => ccmRestrictedWeilGroundEnergy (A J)) atTop (𝓝 0) := by
      have h := (tendsto_const_nhds (x := ccmRestrictedWeilGroundEnergy (A 0))).sub hlim
      simpa using h
    by_contra hnotRH
    obtain ⟨B, hB⟩ := exists_ccmRestrictedWeilGroundEnergy_neg_of_not_riemannHypothesis hnotRH
    have hneg : ∀ᶠ J in atTop, ccmRestrictedWeilGroundEnergy (A J) ≤
        ccmRestrictedWeilGroundEnergy B := by
      filter_upwards [hAtop.eventually_ge_atTop B.1] with J hJ
      exact ccmRestrictedWeilGroundEnergy_antitone hJ
    have hle : (0 : ℝ) ≤ ccmRestrictedWeilGroundEnergy B :=
      le_of_tendsto h0 hneg
    linarith

/-- **Doubly exponential tail of the aperture spectral jump.** Under RH, for all `A.1 ≥ 3`, the
remaining spectral jump `μ(A)` from `A` to `∞` is nonnegative and bounded above by the Gaussian
ceiling `K exp(−π e^{2(A−2)} + 11A/2)`. -/
theorem exists_apertureSpectralJump_tail_le_ceiling :
    ∃ K : ℝ, 0 < K ∧
      ∀ (_ : RiemannHypothesis) (A : SuzukiPositiveAperture), 3 ≤ A.1 →
        0 ≤ ccmRestrictedWeilGroundEnergy A ∧
          ccmRestrictedWeilGroundEnergy A ≤ K * Real.exp (apertureCeilingExponent A.1) := by
  obtain ⟨K, hK0, hK⟩ := exists_pos_groundEnergy_ceiling
  refine ⟨K, hK0, fun hRH A hA =>
    ⟨ccmRestrictedWeilGroundEnergy_nonneg_of_riemannHypothesis' hRH A, hK A hA⟩⟩

/-! ## §5. The Ceiling-Renormalized Lyapunov Functional and Vanishing-Floor Transport -/

/-- The **ceiling loss primitive** `β_ceil(A) = −apertureCeilingExponent A = π e^{2(A−2)} − (11/2) A`. -/
def ceilingLossPrimitive (A : ℝ) : ℝ :=
  -apertureCeilingExponent A

/-- The **instantaneous ceiling loss rate** `β'_ceil(A) = 2π e^{2(A−2)} − 11/2`. -/
def ceilingLossRate (A : ℝ) : ℝ :=
  2 * Real.pi * Real.exp (2 * (A - 2)) - 11 / 2

/-- The **ceiling-renormalized ground energy** `Λ_ceil(A) = e^{β_ceil(A)} μ(A)`. -/
def ceilingScaledGroundEnergy (A : SuzukiPositiveAperture) : ℝ :=
  Real.exp (ceilingLossPrimitive A.1) * ccmRestrictedWeilGroundEnergy A

/-- The ceiling loss primitive has exact derivative `ceilingLossRate A` at every `A : ℝ`. -/
theorem hasDerivAt_ceilingLossPrimitive (A : ℝ) :
    HasDerivAt ceilingLossPrimitive (ceilingLossRate A) A := by
  unfold ceilingLossPrimitive apertureCeilingExponent ceilingLossRate
  have hexp : HasDerivAt (fun a => Real.exp (2 * (a - 2)))
      (Real.exp (2 * (A - 2)) * 2) A := by
    have hlin : HasDerivAt (fun a => 2 * (a - 2)) 2 A := by
      simpa using ((hasDerivAt_id A).sub_const 2).const_mul 2
    exact hlin.exp
  have h1 : HasDerivAt (fun a => Real.pi * Real.exp (2 * (a - 2)))
      (Real.pi * (Real.exp (2 * (A - 2)) * 2)) A := hexp.const_mul Real.pi
  have h2 : HasDerivAt (fun a => 11 / 2 * a) (11 / 2) A := by
    simpa using (hasDerivAt_id A).const_mul (11 / 2 : ℝ)
  have htot := (h2.sub h1).neg
  refine htot.congr_deriv ?_
  ring

/-- The instantaneous ceiling loss rate `ceilingLossRate A` is strictly positive for all `A ≥ 2`. -/
theorem ceilingLossRate_pos {A : ℝ} (hA : 2 ≤ A) :
    0 < ceilingLossRate A := by
  unfold ceilingLossRate
  have hexp : (1 : ℝ) ≤ Real.exp (2 * (A - 2)) :=
    Real.one_le_exp (by linarith)
  have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
  nlinarith

/-- The ceiling loss primitive `ceilingLossPrimitive` is strictly monotone on `[2, ∞)`. -/
theorem strictMonoOn_ceilingLossPrimitive :
    StrictMonoOn ceilingLossPrimitive (Ici 2) := by
  refine strictMonoOn_of_hasDerivWithinAt_pos (convex_Ici 2)
    (f' := ceilingLossRate) ?_ ?_ ?_
  · intro A _
    exact (hasDerivAt_ceilingLossPrimitive A).continuousAt.continuousWithinAt
  · intro A _
    exact (hasDerivAt_ceilingLossPrimitive A).hasDerivWithinAt
  · intro A hA
    rw [interior_Ici] at hA
    exact ceilingLossRate_pos hA.le

/-- **Unconditional boundedness of the ceiling-renormalized ground energy.** Unlike `μ(A)` itself
(which decays faster than `K e^{−β_ceil(A)}`), the renormalized Lyapunov functional
`ceilingScaledGroundEnergy A = e^{β_ceil(A)} μ(A)` is unconditionally bounded above by a uniform
constant `K > 0` for all `A.1 ≥ 3`, and has the exact same sign as `μ(A)`. -/
theorem exists_ceilingScaledGroundEnergy_le :
    ∃ K : ℝ, 0 < K ∧
      (∀ A : SuzukiPositiveAperture, 3 ≤ A.1 → ceilingScaledGroundEnergy A ≤ K) ∧
      (∀ A : SuzukiPositiveAperture,
        0 ≤ ceilingScaledGroundEnergy A ↔ 0 ≤ ccmRestrictedWeilGroundEnergy A) := by
  obtain ⟨K, hK0, hK⟩ := exists_pos_groundEnergy_ceiling
  refine ⟨K, hK0, fun A hA => ?_, fun A => ?_⟩
  · unfold ceilingScaledGroundEnergy ceilingLossPrimitive
    have hbound := hK A hA
    have hexp_pos : 0 < Real.exp (-apertureCeilingExponent A.1) := Real.exp_pos _
    calc Real.exp (-apertureCeilingExponent A.1) * ccmRestrictedWeilGroundEnergy A
        ≤ Real.exp (-apertureCeilingExponent A.1) *
            (K * Real.exp (apertureCeilingExponent A.1)) :=
          mul_le_mul_of_nonneg_left hbound hexp_pos.le
      _ = K * (Real.exp (-apertureCeilingExponent A.1) *
            Real.exp (apertureCeilingExponent A.1)) := by ring
      _ = K := by rw [← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]
  · unfold ceilingScaledGroundEnergy
    exact mul_nonneg_iff_right_nonneg_of_pos (Real.exp_pos _)

/-- **Exact differential ceiling-Lyapunov identity.** For any differentiable floor trajectory `μ`
and loss primitive `β`, `d/dA [e^{β(A)} μ(A)] = e^{β(A)} (μ'(A) + β'(A) μ(A))`, so the relative
decay bound `−μ'(A) ≤ β'(A) μ(A)` holds if and only if `e^{β(A)} μ(A)` has nonnegative derivative. -/
theorem hasDerivAt_exp_mul_floor {μ β : ℝ → ℝ} {μ' β' A : ℝ}
    (hμ : HasDerivAt μ μ' A) (hβ : HasDerivAt β β' A) :
    HasDerivAt (fun a => Real.exp (β a) * μ a)
      (Real.exp (β A) * (μ' + β' * μ A)) A ∧
      (-μ' ≤ β' * μ A ↔ 0 ≤ Real.exp (β A) * (μ' + β' * μ A)) := by
  refine ⟨?_, ?_⟩
  · have h := (hβ.exp.mul hμ)
    refine h.congr_deriv ?_
    ring
  · rw [mul_nonneg_iff_right_nonneg_of_pos (Real.exp_pos _)]
    constructor <;> intro h <;> linarith

/-- **Continuous relative aperture transport.** If `−μ'(A) ≤ β'(A) μ(A)` on `[A₀, ∞)`, then
`A ↦ e^{β(A)} μ(A)` is monotone nondecreasing on `[A₀, ∞)`, and `0 ≤ μ(A₀)` propagates to
`0 ≤ μ(A)` for all `A ≥ A₀` even when `e^{−β(A)} → 0`. -/
theorem monotoneOn_exp_mul_of_relative_decay {μ β μ' β' : ℝ → ℝ} {A₀ : ℝ}
    (hμ : ∀ A ∈ Ici A₀, HasDerivAt μ (μ' A) A)
    (hβ : ∀ A ∈ Ici A₀, HasDerivAt β (β' A) A)
    (hrel : ∀ A ∈ Ici A₀, -μ' A ≤ β' A * μ A) :
    MonotoneOn (fun A => Real.exp (β A) * μ A) (Ici A₀) ∧
      (0 ≤ μ A₀ → ∀ A ≥ A₀, 0 ≤ μ A) := by
  have hmono : MonotoneOn (fun A => Real.exp (β A) * μ A) (Ici A₀) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici A₀)
      (f' := fun A => Real.exp (β A) * (μ' A + β' A * μ A)) ?_ ?_ ?_
    · intro A hA
      exact ((hasDerivAt_exp_mul_floor (hμ A hA) (hβ A hA)).1).continuousAt.continuousWithinAt
    · intro A hA
      exact ((hasDerivAt_exp_mul_floor (hμ A (interior_subset hA))
        (hβ A (interior_subset hA))).1).hasDerivWithinAt
    · intro A hA
      exact ((hasDerivAt_exp_mul_floor (hμ A (interior_subset hA))
        (hβ A (interior_subset hA))).2).mp (hrel A (interior_subset hA))
  refine ⟨hmono, fun h0 A hA => ?_⟩
  have h1 : Real.exp (β A₀) * μ A₀ ≤ Real.exp (β A) * μ A :=
    hmono self_mem_Ici hA hA
  have h2 : 0 ≤ Real.exp (β A₀) * μ A₀ := mul_nonneg (Real.exp_pos _).le h0
  exact (mul_nonneg_iff_right_nonneg_of_pos (Real.exp_pos (β A))).mp (h2.trans h1)

/-- **Vanishing-floor relative step transport implies RH.** Unlike `TheApertureFloorUnderAbsoluteDecay`
(which imposed `∑ c_i ≤ 1/2` to force a positive floor `μ(A_J) ≥ 1/10000` and was refuted by the
Gaussian ceiling), any relative step bound `(1 − c_j) μ(A_j) ≤ μ(A_{j+1})` with `c_j ≤ 1`
starting at `(A 0).1 ≤ 3/10` along `A_j → ∞` allows the floor `(∏_{i < J} (1 − c_i)) / 5000` to
decay to `0` at the Gaussian rate while still forcing `0 ≤ μ(A_J)` at every finite stage `J` and
therefore proving the Riemann Hypothesis. -/
theorem riemannHypothesis_of_vanishing_relative_step
    {A : ℕ → SuzukiPositiveAperture} {c : ℕ → ℝ}
    (hA0 : (A 0).1 ≤ 3 / 10) (hAtop : Tendsto (fun j => (A j).1) atTop atTop)
    (hc : ∀ j, c j ≤ 1)
    (hstep : ∀ j, (1 - c j) * ccmRestrictedWeilGroundEnergy (A j) ≤
      ccmRestrictedWeilGroundEnergy (A (j + 1))) :
    (∀ J : ℕ, (∏ i ∈ range J, (1 - c i)) * (1 / 5000) ≤
      ccmRestrictedWeilGroundEnergy (A J)) ∧
    (∀ J : ℕ, 0 ≤ ccmRestrictedWeilGroundEnergy (A J)) ∧
    RiemannHypothesis := by
  have hq : ∀ i, 0 ≤ 1 - c i := fun i => sub_nonneg.mpr (hc i)
  have hprod : ∀ J : ℕ, (∏ i ∈ range J, (1 - c i)) * ccmRestrictedWeilGroundEnergy (A 0) ≤
      ccmRestrictedWeilGroundEnergy (A J) := fun J => by
    rw [mul_comm]
    exact mul_prod_le_of_relative_step
      (μ := fun j => ccmRestrictedWeilGroundEnergy (A j)) hq hstep J
  have hbase : 1 / 5000 ≤ ccmRestrictedWeilGroundEnergy (A 0) :=
    one_div_5000_le_ccmRestrictedWeilGroundEnergy_threeTenths hA0
  have hfloor : ∀ J : ℕ, (∏ i ∈ range J, (1 - c i)) * (1 / 5000) ≤
      ccmRestrictedWeilGroundEnergy (A J) := fun J => by
    have hp0 : 0 ≤ ∏ i ∈ range J, (1 - c i) := Finset.prod_nonneg fun i _ => hq i
    exact (mul_le_mul_of_nonneg_left hbase hp0).trans (hprod J)
  have hnonneg : ∀ J : ℕ, 0 ≤ ccmRestrictedWeilGroundEnergy (A J) := fun J => by
    have hp0 : 0 ≤ (∏ i ∈ range J, (1 - c i)) * (1 / 5000) :=
      mul_nonneg (Finset.prod_nonneg fun i _ => hq i) (by norm_num)
    exact hp0.trans (hfloor J)
  refine ⟨hfloor, hnonneg, ?_⟩
  rw [riemannHypothesis_iff_not_bddAbove_groundEnergyNonnegApertures]
  rintro ⟨M, hM⟩
  obtain ⟨J, hJ⟩ := (hAtop.eventually_gt_atTop M).exists
  have hmem : (A J).1 ∈ groundEnergyNonnegApertures := by
    refine ⟨(A J).2, ?_⟩
    have hcongr : ccmRestrictedWeilGroundEnergy ⟨(A J).1, (A J).2⟩ =
        ccmRestrictedWeilGroundEnergy (A J) := by congr 1
    rw [hcongr]
    exact hnonneg J
  exact absurd (hM hmem) (not_le.mpr hJ)

/-- **Equivalence between RH and vanishing-floor relative step transport.** Along any unbounded
aperture sequence `A_j → ∞` starting at `(A 0).1 ≤ 3/10`, RH holds if and only if there exist
step factors `q : ℕ → ℝ` with `0 ≤ q j` and `q j * μ(A_j) ≤ μ(A_{j+1})` for all `j`. -/
theorem riemannHypothesis_iff_exists_relative_step
    {A : ℕ → SuzukiPositiveAperture}
    (hA0 : (A 0).1 ≤ 3 / 10) (hAtop : Tendsto (fun j => (A j).1) atTop atTop) :
    RiemannHypothesis ↔
      ∃ q : ℕ → ℝ, (∀ j, 0 ≤ q j) ∧
        ∀ j, q j * ccmRestrictedWeilGroundEnergy (A j) ≤
          ccmRestrictedWeilGroundEnergy (A (j + 1)) := by
  constructor
  · intro hRH
    refine ⟨fun _ => 0, fun _ => le_rfl, fun j => ?_⟩
    simp [ccmRestrictedWeilGroundEnergy_nonneg_of_riemannHypothesis' hRH (A (j + 1))]
  · rintro ⟨q, hq0, hstep⟩
    have hc : ∀ j, 1 - q j ≤ 1 := fun j => by linarith [hq0 j]
    have hstep' : ∀ j, (1 - (1 - q j)) * ccmRestrictedWeilGroundEnergy (A j) ≤
        ccmRestrictedWeilGroundEnergy (A (j + 1)) := by
      intro j
      simpa using hstep j
    exact (riemannHypothesis_of_vanishing_relative_step hA0 hAtop hc hstep').2.2

/-- The **ceiling step factor** `q_ceil(A, j) = exp(−(β_ceil(A_{j+1}) − β_ceil(A_j))) ∈ (0, 1]`. -/
def ceilingStepFactor (A : ℕ → SuzukiPositiveAperture) (j : ℕ) : ℝ :=
  Real.exp (-(ceilingLossPrimitive (A (j + 1)).1 - ceilingLossPrimitive (A j).1))

/-- The ceiling step factors are strictly positive and telescope exactly to the Gaussian ceiling
weight `exp(β_ceil(A₀)) * exp(apertureCeilingExponent(A_J))`. -/
theorem prod_ceilingStepFactor_eq (A : ℕ → SuzukiPositiveAperture) (J : ℕ) :
    (∀ j, 0 < ceilingStepFactor A j) ∧
      ∏ j ∈ range J, ceilingStepFactor A j =
        Real.exp (ceilingLossPrimitive (A 0).1) *
          Real.exp (apertureCeilingExponent (A J).1) := by
  refine ⟨fun j => Real.exp_pos _, ?_⟩
  induction J with
  | zero =>
    simp [ceilingLossPrimitive, ← Real.exp_add]
  | succ J ih =>
    rw [Finset.prod_range_succ, ih]
    unfold ceilingStepFactor ceilingLossPrimitive
    rw [mul_assoc, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring

/-- **Ceiling-renormalized monotonicity criterion for RH.** Along any unbounded aperture sequence
`A_j → ∞` starting at `(A 0).1 ≤ 3/10`, if the ceiling-renormalized ground energy
`ceilingScaledGroundEnergy (A j) = e^{β_ceil(A_j)} μ(A_j)` is nondecreasing (`Λ_ceil(A_j) ≤ Λ_ceil(A_{j+1})`),
then `μ(A)` satisfies the ceiling-compatible relative step bound with `ceilingStepFactor`,
remains above the doubly exponential floor `(1/5000) e^{β_ceil(A₀)} e^{apertureCeilingExponent(A_J)} > 0`
at every finite stage `J`, and the Riemann Hypothesis holds. -/
theorem riemannHypothesis_of_ceilingScaledGroundEnergy_mono
    {A : ℕ → SuzukiPositiveAperture}
    (hA0 : (A 0).1 ≤ 3 / 10) (hAtop : Tendsto (fun j => (A j).1) atTop atTop)
    (hmono : ∀ j, ceilingScaledGroundEnergy (A j) ≤ ceilingScaledGroundEnergy (A (j + 1))) :
    (∀ J : ℕ, (1 / 5000) * Real.exp (ceilingLossPrimitive (A 0).1) *
        Real.exp (apertureCeilingExponent (A J).1) ≤
      ccmRestrictedWeilGroundEnergy (A J)) ∧
    RiemannHypothesis := by
  have hstep : ∀ j, ceilingStepFactor A j * ccmRestrictedWeilGroundEnergy (A j) ≤
      ccmRestrictedWeilGroundEnergy (A (j + 1)) := by
    intro j
    have hj := hmono j
    unfold ceilingScaledGroundEnergy at hj
    unfold ceilingStepFactor
    have hexp_pos : 0 < Real.exp (-ceilingLossPrimitive (A (j + 1)).1) := Real.exp_pos _
    have hmul := mul_le_mul_of_nonneg_left hj hexp_pos.le
    have hleft : Real.exp (-ceilingLossPrimitive (A (j + 1)).1) *
        (Real.exp (ceilingLossPrimitive (A j).1) * ccmRestrictedWeilGroundEnergy (A j)) =
        Real.exp (-(ceilingLossPrimitive (A (j + 1)).1 - ceilingLossPrimitive (A j).1)) *
          ccmRestrictedWeilGroundEnergy (A j) := by
      rw [← mul_assoc, ← Real.exp_add]
      congr 2
      ring
    have hright : Real.exp (-ceilingLossPrimitive (A (j + 1)).1) *
        (Real.exp (ceilingLossPrimitive (A (j + 1)).1) *
          ccmRestrictedWeilGroundEnergy (A (j + 1))) =
        ccmRestrictedWeilGroundEnergy (A (j + 1)) := by
      rw [← mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul]
    linarith
  have hc : ∀ j, 1 - ceilingStepFactor A j ≤ 1 := fun j => by
    linarith [(prod_ceilingStepFactor_eq A 0).1 j]
  have hstep' : ∀ j, (1 - (1 - ceilingStepFactor A j)) * ccmRestrictedWeilGroundEnergy (A j) ≤
      ccmRestrictedWeilGroundEnergy (A (j + 1)) := by
    intro j
    simpa using hstep j
  have hres := riemannHypothesis_of_vanishing_relative_step hA0 hAtop hc hstep'
  refine ⟨fun J => ?_, hres.2.2⟩
  have hf := hres.1 J
  have hpeq : (∏ i ∈ range J, (1 - (1 - ceilingStepFactor A i))) =
      ∏ i ∈ range J, ceilingStepFactor A i := by
    refine Finset.prod_congr rfl fun i _ => by ring
  rw [hpeq, (prod_ceilingStepFactor_eq A J).2] at hf
  linarith

/-- **Graded additive transport.** Even with both relative decay `(1 − c_j) ≤ 1` and additive
leakage `δ_j ≥ 0`, if `(1 − c_j) μ(A_j) − δ_j ≤ μ(A_{j+1})` holds and the ceiling-weighted leakage
sum satisfies `∑_{j < J} e^{β_j} δ_j ≤ e^{β₀} μ(A₀) + M`, then `μ(A_J) ≥ −M e^{−β_J}`. In
particular, when `M = 0` (`∑_{j < J} e^{β_j} δ_j ≤ e^{β₀} μ(A₀)`), `0 ≤ μ(A_J)` at every finite
stage `J` and RH holds. -/
theorem groundEnergy_ge_neg_exp_of_graded_step
    {A : ℕ → SuzukiPositiveAperture} {β δ : ℕ → ℝ} {M : ℝ}
    (hstep : ∀ j, Real.exp (β (j + 1)) * ccmRestrictedWeilGroundEnergy (A (j + 1)) ≥
      Real.exp (β j) * ccmRestrictedWeilGroundEnergy (A j) - Real.exp (β (j + 1)) * δ j)
    (hsum : ∀ J : ℕ, ∑ j ∈ range J, Real.exp (β (j + 1)) * δ j ≤
      Real.exp (β 0) * ccmRestrictedWeilGroundEnergy (A 0) + M) :
    ∀ J : ℕ, -M * Real.exp (-β J) ≤ ccmRestrictedWeilGroundEnergy (A J) := by
  have htel : ∀ J : ℕ,
      Real.exp (β 0) * ccmRestrictedWeilGroundEnergy (A 0) -
        ∑ j ∈ range J, Real.exp (β (j + 1)) * δ j ≤
      Real.exp (β J) * ccmRestrictedWeilGroundEnergy (A J) :=
    sub_sum_le_of_additive_step
      (μ := fun j => Real.exp (β j) * ccmRestrictedWeilGroundEnergy (A j))
      (r := fun j => Real.exp (β (j + 1)) * δ j) hstep
  intro J
  have h1 : -M ≤ Real.exp (β J) * ccmRestrictedWeilGroundEnergy (A J) := by
    linarith [htel J, hsum J]
  have hexp_pos : 0 < Real.exp (-β J) := Real.exp_pos _
  have h2 := mul_le_mul_of_nonneg_right h1 hexp_pos.le
  have hright : Real.exp (β J) * ccmRestrictedWeilGroundEnergy (A J) * Real.exp (-β J) =
      ccmRestrictedWeilGroundEnergy (A J) := by
    calc Real.exp (β J) * ccmRestrictedWeilGroundEnergy (A J) * Real.exp (-β J)
        = (Real.exp (β J) * Real.exp (-β J)) * ccmRestrictedWeilGroundEnergy (A J) := by ring
      _ = ccmRestrictedWeilGroundEnergy (A J) := by
          rw [← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul]
  linarith

/-- **Complete Synthesis for Open Problem 6 (Transport in Aperture and the Ceiling-Lyapunov Identity).**
Unites the five pillars of aperture transport:
1. **Exact two-aperture gauge conservation**: for nested window gauges `0 ≤ M₁ ≤ M₂ ≤ 1` equal to `1`
   on `supp F`, `0 ≤ ΔJ(M₁, M₂; F) = Φ_shell(M₁, M₂; F)`, with identical cancellation of all bulk
   and prime terms on the common plateau `{M₁ = M₂ = 1}`;
2. **Exact aperture derivatives of the window potential and floor**:
   `∂_R K_R(x) = −(w_arch(R−x) + w_arch(R+x) + 3/2) < 0` and
   `windowFloor'(R) = −(1/R + 3/2 + 12 R²) < 0`;
3. **Exact `Φ`-gauge boundary-defect identity**:
   `Ẑ(Φ u) = J_Φ(u) − thetaBoundaryDefectMass u + 2 (thetaBoundaryFlux u)² − 2 oddPoleMoment(Φ u)²`,
   with both `J_Φ(u) ≥ 0` and `thetaBoundaryDefectMass u ≥ 0` sign-definite;
4. **Total-jump characterization of RH**: along any monotone unbounded `A_j → ∞`,
   `RiemannHypothesis ↔ (∀ J, ∑_{j < J} Δ_spec(A_j, A_{j+1}) ≤ μ(A₀))` and
   `RiemannHypothesis ↔ HasSum (fun j => Δ_spec(A_j, A_{j+1})) (μ(A₀))`;
5. **Ceiling-renormalized Lyapunov transport**: `ceilingScaledGroundEnergy A = e^{β_ceil(A)} μ(A)`
   is unconditionally bounded above by a uniform constant `K > 0` for `A.1 ≥ 3`, and dropping
   `∑ c_i ≤ 1/2` to `c_j ≤ 1` (`0 ≤ q_j`) allows the lower floor to decay to `0` at the Gaussian
   ceiling rate while still forcing `0 ≤ μ(A_J)` at every finite stage `J` and hence RH. -/
theorem apertureTransport_and_ceilingLyapunov_synthesis :
    (∀ {F M₁ M₂ : ℝ → ℝ} {R₁ R₂ : ℝ},
      ContDiff ℝ 2 F → HasCompactSupport F →
      ContDiff ℝ 2 M₁ → HasCompactSupport M₁ →
      (∀ y, M₁ y ≤ 1) → (∀ y, 0 ≤ M₁ y) → (∀ y, R₁ ≤ |y| → M₁ y = 0) →
      (∀ x, F x ≠ 0 → M₁ x = 1) →
      ContDiff ℝ 2 M₂ → HasCompactSupport M₂ →
      (∀ y, M₂ y ≤ 1) → (∀ y, 0 ≤ M₂ y) → (∀ y, R₂ ≤ |y| → M₂ y = 0) →
      (∀ x, F x ≠ 0 → M₂ x = 1) → (∀ y, M₁ y ≤ M₂ y) →
      0 ≤ gaugeStepJumpEnergy M₁ M₂ F ∧
        gaugeStepJumpEnergy M₁ M₂ F = gaugeStepBoundaryFlux M₁ M₂ F) ∧
    (∀ {R : ℝ}, 0 < R → HasDerivAt windowFloor (-windowFloorDissipationRate R) R ∧
      0 < windowFloorDissipationRate R) ∧
    (∀ L : ℝ,
      fullZeroForm (thetaPlateau L) =
        signedJumpEnergy riemannKernelReal (smoothPlateau L) -
          thetaBoundaryDefectMass (smoothPlateau L) +
          2 * thetaBoundaryFlux (smoothPlateau L) ^ 2 ∧
      0 ≤ signedJumpEnergy riemannKernelReal (smoothPlateau L) ∧
      0 ≤ thetaBoundaryDefectMass (smoothPlateau L) ∧
      thetaBoundaryDefectMass (smoothPlateau L) ≤ tailWeight L) ∧
    (∀ {A : ℕ → SuzukiPositiveAperture},
      Monotone (fun j => (A j).1) → Tendsto (fun j => (A j).1) atTop atTop →
      (RiemannHypothesis ↔
        HasSum (fun j => apertureSpectralJump (A j) (A (j + 1)))
          (ccmRestrictedWeilGroundEnergy (A 0)))) ∧
    (∃ K : ℝ, 0 < K ∧
      (∀ A : SuzukiPositiveAperture, 3 ≤ A.1 → ceilingScaledGroundEnergy A ≤ K) ∧
      (∀ A : SuzukiPositiveAperture,
        0 ≤ ceilingScaledGroundEnergy A ↔ 0 ≤ ccmRestrictedWeilGroundEnergy A)) := by
  refine ⟨fun hF hFc hM₁d hM₁cs hle₁ hnn₁ hzero₁ hFM₁ hM₂d hM₂cs hle₂ hnn₂ hzero₂ hFM₂ hle =>
    ⟨(gaugeStepJumpEnergy_nonneg hF hFc hM₁d hM₁cs hle₁ hnn₁ hzero₁ hFM₁
       hM₂d hM₂cs hle₂ hnn₂ hzero₂ hFM₂ hle).1,
     gaugeStepJumpEnergy_eq_gaugeStepBoundaryFlux hF hFc hM₁d hM₁cs hle₁ hnn₁ hzero₁ hFM₁
       hM₂d hM₂cs hle₂ hnn₂ hzero₂ hFM₂⟩,
    fun hR => ⟨hasDerivAt_windowFloor hR, windowFloorDissipationRate_pos hR⟩,
    fun L => ⟨(fullZeroForm_thetaPlateau_eq L).1, (fullZeroForm_thetaPlateau_eq L).2.1,
      (fullZeroForm_thetaPlateau_eq L).2.2.1, (fullZeroForm_thetaPlateau_eq L).2.2.2.1⟩,
    fun hAmono hAtop => riemannHypothesis_iff_hasSum_apertureSpectralJump hAmono hAtop,
    exists_ceilingScaledGroundEnergy_le⟩

end ArithmeticOrientationTheory
end GaloisForLFunctions

