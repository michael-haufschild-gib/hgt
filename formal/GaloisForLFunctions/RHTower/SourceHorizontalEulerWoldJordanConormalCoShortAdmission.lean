import GaloisForLFunctions.RHTower.SourceHorizontalEulerWoldJordanResidualSelection

/-!
# Euler--Wold Jordan admission into the literal Xi conormal co-short

The intrinsic Hahn--Jordan Euler/Wold residuals are admitted componentwise into the actual
four-orientation Route-P conormal short.  No addition or grade-forgetting is performed: the
negative Euler and positive Wold matrices are shortened separately.

The main finite law is stronger than a cofinal matching.  If `S(c)=4‖c‖²` is the literal
four-orientation short and `A₊(c,N)` is the admitted Wold leg, then the existing regularized Xi
endpoint response `R(c,q,N)` satisfies

`A₊(c,N) + R(c,q,N) = 2 S(c)`

at every source clock.  This is the Green--Stokes complement transported through the conormal
short: Wold Jordan mass is twice the interior third jet, while the endpoint response is twice the
same short times the complementary endpoint third jet.

The coefficient is then specialized to the actual multiplicity-split completed-Xi residue.  At
positive aperture it is literally the Gamma--Julia source coupling times Burnol's nested-window
top-conormal feature.  Summation over the actual support fibre restores analytic multiplicity.
No Loewner order, equivariance, spectral projection, scalar contractivity, or RH premise is used.
-/

open Complex Matrix Filter Topology
open scoped BigOperators ComplexOrder

namespace RHTower

noncomputable section

/-- Literal scalar Schur contraction of the physical corner through the retained environment
pivot.  It is a rational matrix operation, not an operator-spectrum construction. -/
def sourceHorizontalNonSpectralConormalShort
    (B : Matrix (Fin 2) (Fin 2) ℂ) : ℂ :=
  B 0 0 - B 0 1 * (B 1 1)⁻¹ * B 1 0

/-- Real value of the complete four-orientation conormal short. -/
def sourceHorizontalLiteralConormalShort (c : ℂ) : ℝ :=
  4 * Complex.normSq c

/-- Shorting a real multiple of the diagonal four-orientation orbit retains its sign and exact
coefficient.  This applies to the negative Euler leg as well as the positive Wold leg. -/
theorem sourceHorizontalNonSpectralConormalShort_orbit_smul
    (a : ℝ) (c : ℂ) :
    sourceHorizontalNonSpectralConormalShort
        (((a : ℂ) • routePJuliaSharedOrientationOrbitBlock c)) =
      (a * sourceHorizontalLiteralConormalShort c : ℝ) := by
  rw [sourceHorizontalNonSpectralConormalShort,
    routePJuliaSharedOrientationOrbitBlock_eq_diagonal]
  simp [sourceHorizontalLiteralConormalShort]

/-- The unweighted literal conormal contraction is `4‖c‖²`. -/
theorem sourceHorizontalNonSpectralConormalShort_orbit
    (c : ℂ) :
    sourceHorizontalNonSpectralConormalShort
        (routePJuliaSharedOrientationOrbitBlock c) =
      (sourceHorizontalLiteralConormalShort c : ℂ) := by
  simpa using sourceHorizontalNonSpectralConormalShort_orbit_smul 1 c

/-- Componentwise, unrecompressed conormal admission of the Euler negative and Wold positive
Hahn--Jordan residuals. -/
def sourceHorizontalEulerWoldJordanConormalAdmission
    (c : ℂ) (N : ℕ) : Fin 2 → ℝ :=
  ![-sourceHorizontalEulerWoldJordanNegativeMass N *
      sourceHorizontalLiteralConormalShort c,
    sourceHorizontalEulerWoldJordanPositiveMass N *
      sourceHorizontalLiteralConormalShort c]

/-- Exact finite normalization: positive Hahn--Jordan mass is twice the BV interior third jet. -/
theorem sourceHorizontalEulerWoldJordanPositiveMass_eq_two_mul_interiorThirdJet
    (N : ℕ) :
    sourceHorizontalEulerWoldJordanPositiveMass N =
      2 * sourceHorizontalWoldBVGreenStokesInteriorThirdJet N := by
  rw [sourceHorizontalEulerWoldJordanPositiveMass_eq,
    sourceHorizontalWoldBVGreenStokesInteriorThirdJet,
    sourceHorizontalWoldOrderedNormalizedMoment,
    sourceHorizontalWoldCubicCountertermMoment]
  ring

/-- First admitted component is the literal non-spectral short of the negative Euler action. -/
theorem sourceHorizontalEulerWoldJordanConormalAdmission_action
    (c : ℂ) (N : ℕ) :
    (sourceHorizontalNonSpectralConormalShort
      (sourceHorizontalEulerWoldJordanSelectedPhysicalAction c N)).re =
        sourceHorizontalEulerWoldJordanConormalAdmission c N 0 := by
  rw [sourceHorizontalEulerWoldJordanSelectedPhysicalAction,
    sourceHorizontalNonSpectralConormalShort_orbit_smul]
  simp [sourceHorizontalEulerWoldJordanConormalAdmission]

/-- Second admitted component is the literal non-spectral short of the positive Wold regulator. -/
theorem sourceHorizontalEulerWoldJordanConormalAdmission_regulator
    (c : ℂ) (N : ℕ) :
    (sourceHorizontalNonSpectralConormalShort
      (sourceHorizontalEulerWoldJordanSelectedRegulator c N)).re =
        sourceHorizontalEulerWoldJordanConormalAdmission c N 1 := by
  rw [sourceHorizontalEulerWoldJordanSelectedRegulator,
    sourceHorizontalNonSpectralConormalShort_orbit_smul]
  simp [sourceHorizontalEulerWoldJordanConormalAdmission]

/-- **Finite Green--Stokes co-short law.**  The admitted Wold residual and the literal regularized
Xi endpoint response are complementary parts of two copies of the same conormal short.  This is
exact at every clock and uses no fitted divisor-dependent scale. -/
theorem sourceHorizontalEulerWoldJordanConormalAdmission_endpoint_coshort
    (c : ℂ) (q : XiRightZeroCopy) (N : ℕ) :
    sourceHorizontalEulerWoldJordanConormalAdmission c N 1 +
        sourceZeroHorizontalWoldRegularizedJuliaOrbitResponse c q N =
      2 * sourceHorizontalLiteralConormalShort c := by
  rw [sourceHorizontalEulerWoldJordanConormalAdmission,
    sourceHorizontalEulerWoldJordanPositiveMass_eq_two_mul_interiorThirdJet,
    sourceZeroHorizontalWoldRegularizedJuliaOrbitResponse_eq_endpointThirdJet]
  rw [sourceHorizontalLiteralConormalShort]
  change
    (2 * sourceHorizontalWoldBVGreenStokesInteriorThirdJet N) *
        (4 * Complex.normSq c) +
      8 * Complex.normSq c *
        sourceHorizontalWoldBVGreenStokesEndpointThirdJet N =
      2 * (4 * Complex.normSq c)
  have hconservation :=
    sourceHorizontalWoldBVGreenStokesInteriorThirdJet_add_endpointThirdJet N
  linear_combination (8 * Complex.normSq c) * hconservation

/-- The admitted Wold component is exactly the pre-existing BV interior energy, so the co-short
law identifies both sides of finite Green--Stokes conservation on one conormal fibre. -/
theorem sourceHorizontalEulerWoldJordanConormalAdmission_regulator_eq_interiorEnergy
    (c : ℂ) (N : ℕ) :
    sourceHorizontalEulerWoldJordanConormalAdmission c N 1 =
      sourceHorizontalWoldBVInteriorEnergy c N := by
  rw [sourceHorizontalEulerWoldJordanConormalAdmission,
    sourceHorizontalEulerWoldJordanPositiveMass_eq_two_mul_interiorThirdJet,
    sourceHorizontalLiteralConormalShort,
    sourceHorizontalWoldBVInteriorEnergy]
  norm_num
  ring

/-- The Route-P endpoint response is literally the selected BV ghost energy at finite clock. -/
theorem sourceZeroHorizontalWoldRegularizedJuliaOrbitResponse_eq_ghostEnergy
    (c : ℂ) (q : XiRightZeroCopy) (N : ℕ) :
    sourceZeroHorizontalWoldRegularizedJuliaOrbitResponse c q N =
      sourceHorizontalWoldBVKreinGhostEnergy c N := by
  rw [sourceZeroHorizontalWoldRegularizedJuliaOrbitResponse_eq_endpointThirdJet,
    sourceHorizontalWoldBVKreinGhostEnergy]

/-! ## Cofinal character and exact budget blindness -/

/-- Arbitrary real linear reporter on admitted Euler action, Wold regulator, and endpoint
co-short. -/
def sourceHorizontalEulerWoldJordanConormalLinearReporter
    (a b d : ℝ) (c : ℂ) (q : XiRightZeroCopy) (N : ℕ) : ℝ :=
  a * sourceHorizontalEulerWoldJordanConormalAdmission c N 0 +
    b * sourceHorizontalEulerWoldJordanConormalAdmission c N 1 +
      d * sourceZeroHorizontalWoldRegularizedJuliaOrbitResponse c q N

/-- Complete cofinal character of a linear reporter. -/
def sourceHorizontalEulerWoldJordanConormalCofinalCharacter
    (a b d : ℝ) (c : ℂ) : ℝ :=
  (8 / 3 : ℝ) * Complex.normSq c * (-a + b + 2 * d)

/-- Every linear reporter has one exact source-computable cofinal character. -/
theorem tendsto_sourceHorizontalEulerWoldJordanConormalLinearReporter
    (a b d : ℝ) (c : ℂ) (q : XiRightZeroCopy) :
    Tendsto
      (sourceHorizontalEulerWoldJordanConormalLinearReporter a b d c q)
      atTop
      (nhds (sourceHorizontalEulerWoldJordanConormalCofinalCharacter a b d c)) := by
  have hneg : Tendsto
      (fun N => sourceHorizontalEulerWoldJordanConormalAdmission c N 0)
      atTop
      (nhds (-(2 / 3 : ℝ) * sourceHorizontalLiteralConormalShort c)) := by
    have h := tendsto_sourceHorizontalEulerWoldJordanNegativeMass.neg.mul_const
      (sourceHorizontalLiteralConormalShort c)
    simpa [sourceHorizontalEulerWoldJordanConormalAdmission] using h
  have hpos : Tendsto
      (fun N => sourceHorizontalEulerWoldJordanConormalAdmission c N 1)
      atTop
      (nhds ((2 / 3 : ℝ) * sourceHorizontalLiteralConormalShort c)) := by
    have h := tendsto_sourceHorizontalEulerWoldJordanPositiveMass.mul_const
      (sourceHorizontalLiteralConormalShort c)
    simpa [sourceHorizontalEulerWoldJordanConormalAdmission] using h
  have hendpoint := tendsto_sourceZeroHorizontalWoldRegularizedJuliaOrbitResponse c q
  have h := ((hneg.const_mul a).add (hpos.const_mul b)).add
    (hendpoint.const_mul d)
  convert h using 1
  · funext N
    rw [sourceHorizontalEulerWoldJordanConormalLinearReporter]
  · rw [sourceHorizontalEulerWoldJordanConormalCofinalCharacter,
      sourceHorizontalLiteralConormalShort]
    ring

/-- For a nonzero conormal, cofinal blindness is exactly one coefficient plane. -/
theorem sourceHorizontalEulerWoldJordanConormalCofinalCharacter_eq_zero_iff
    {c : ℂ} (hc : c ≠ 0) (a b d : ℝ) :
    sourceHorizontalEulerWoldJordanConormalCofinalCharacter a b d c = 0 ↔
      -a + b + 2 * d = 0 := by
  rw [sourceHorizontalEulerWoldJordanConormalCofinalCharacter,
    mul_eq_zero]
  have hnorm : Complex.normSq c ≠ 0 := (Complex.normSq_pos.mpr hc).ne'
  norm_num [hnorm]

/-- Exact diagnosis of the existing primitive-budget lane: its compensated energy is the
`(1,-1,1)` conormal reporter. -/
theorem sourceHorizontalEulerWoldJordanConormalLinearReporter_budgeted_eq_compensated
    (c : ℂ) (q : XiRightZeroCopy) (N : ℕ) :
    sourceHorizontalEulerWoldJordanConormalLinearReporter 1 (-1) 1 c q N =
      sourceHorizontalWoldBVKreinEulerGammaCubicCompensatedEnergy c N := by
  rw [sourceHorizontalEulerWoldJordanConormalLinearReporter,
    sourceHorizontalEulerWoldJordanConormalAdmission,
    sourceHorizontalEulerWoldJordanNegativeMass_eq,
    sourceHorizontalEulerWoldJordanPositiveMass_eq,
    sourceHorizontalLiteralConormalShort,
    sourceZeroHorizontalWoldRegularizedJuliaOrbitResponse_eq_ghostEnergy,
    sourceHorizontalWoldBVKreinEulerGammaCubicCompensatedEnergy,
    sourceHorizontalWoldBVKreinSignedSplitEnergy,
    sourceHorizontalWoldBVKreinGhostEnergy,
    sourceHorizontalWoldBVInteriorEnergy,
    sourceHorizontalWoldBVGreenStokesInteriorThirdJet,
    sourceHorizontalWoldOrderedNormalizedMoment,
    sourceHorizontalWoldCubicCountertermMoment,
    sourceHorizontalEulerGammaCubicNormalizedMoment]
  norm_num
  ring

/-- The budgeted reporter lies exactly in the cofinal blind plane.  Hence existing compensated
budget control cannot by itself control the endpoint coordinate; a transverse source reporter is
mathematically necessary. -/
@[simp] theorem sourceHorizontalEulerWoldJordanConormalCofinalCharacter_budgeted_zero
    (c : ℂ) :
    sourceHorizontalEulerWoldJordanConormalCofinalCharacter 1 (-1) 1 c = 0 := by
  rw [sourceHorizontalEulerWoldJordanConormalCofinalCharacter]
  ring

/-! ## Actual Xi-fibre coefficient and source provenance -/

/-- The actual multiplicity copy's coefficient after completed Gamma--Julia residue and canonical
equal splitting. -/
def sourceHorizontalActualXiConormalCoefficient
    (x u : ℝ) (q : XiRightZeroCopy) (r : ℝ) : ℂ :=
  routePPrimitiveGammaJuliaXiCopyForwardCoordinate
    x u q.1.1 r q.1.2

/-- At positive aperture the selected coefficient is the genuine source coupling times Burnol's
actual multiplicity-exact nested-window conormal feature. -/
theorem sourceHorizontalActualXiConormalCoefficient_eq_burnolWindow
    (x u : ℝ) (q : XiRightZeroCopy) {r : ℝ} (hr : 0 < r) :
    sourceHorizontalActualXiConormalCoefficient x u q r =
      routePPrimitiveGammaJuliaXiDescentCoefficient x u *
        xiWardCubicBurnolActualConormalFeature r q.1.1 := by
  rw [sourceHorizontalActualXiConormalCoefficient,
    routePPrimitiveGammaJuliaXiCopyForwardCoordinate_eq,
    xiWardCubicBurnolActualConormalFeature_eq hr]

/-- A nonzero source coupling and nonzero aperture give a genuinely nonzero admitted conormal. -/
theorem sourceHorizontalActualXiConormalCoefficient_ne_zero
    {x u r : ℝ} (q : XiRightZeroCopy)
    (hkappa : routePTwoPrimeJuliaWardNonlocalCoupling x u ≠ 0) (hr : r ≠ 0) :
    sourceHorizontalActualXiConormalCoefficient x u q r ≠ 0 := by
  exact routePPrimitiveGammaJuliaXiCopyForwardCoordinate_ne_zero
    q.1.1 q.1.2 hkappa hr

/-- Consequently the actual literal conormal short is strictly positive. -/
theorem sourceHorizontalLiteralConormalShort_actual_pos
    {x u r : ℝ} (q : XiRightZeroCopy)
    (hkappa : routePTwoPrimeJuliaWardNonlocalCoupling x u ≠ 0) (hr : r ≠ 0) :
    0 < sourceHorizontalLiteralConormalShort
      (sourceHorizontalActualXiConormalCoefficient x u q r) := by
  exact mul_pos (by norm_num)
    (Complex.normSq_pos.mpr
      (sourceHorizontalActualXiConormalCoefficient_ne_zero q hkappa hr))

/-- The actual conormal coefficient depends on divisor support, not the choice of multiplicity
copy in that support fibre. -/
theorem sourceHorizontalActualXiConormalCoefficient_eq_of_support
    (x u r : ℝ) {q s : XiRightZeroCopy} (h : s.1.1 = q.1.1) :
    sourceHorizontalActualXiConormalCoefficient x u s r =
      sourceHorizontalActualXiConormalCoefficient x u q r := by
  rw [sourceHorizontalActualXiConormalCoefficient,
    sourceHorizontalActualXiConormalCoefficient,
    routePPrimitiveGammaJuliaXiCopyForwardCoordinate_eq,
    routePPrimitiveGammaJuliaXiCopyForwardCoordinate_eq, h]

/-- Componentwise admission evaluated on one actual Xi multiplicity copy. -/
def sourceHorizontalActualXiConormalAdmission
    (x u : ℝ) (q : XiRightZeroCopy) (r : ℝ) (N : ℕ) : Fin 2 → ℝ :=
  sourceHorizontalEulerWoldJordanConormalAdmission
    (sourceHorizontalActualXiConormalCoefficient x u q r) N

theorem sourceHorizontalActualXiConormalAdmission_eq_of_support
    (x u r : ℝ) {q s : XiRightZeroCopy} (h : s.1.1 = q.1.1) (N : ℕ) :
    sourceHorizontalActualXiConormalAdmission x u s r N =
      sourceHorizontalActualXiConormalAdmission x u q r N := by
  rw [sourceHorizontalActualXiConormalAdmission,
    sourceHorizontalActualXiConormalAdmission,
    sourceHorizontalActualXiConormalCoefficient_eq_of_support x u r h]

/-- Actual support-fibre summation restores analytic multiplicity after nonlinear shorting. -/
theorem sourceHorizontalActualXiConormalAdmission_fiber_sum
    (x u : ℝ) (q : XiRightZeroCopy) (r : ℝ) (N : ℕ) :
    (∑ s : XiRightSupportFiber q,
      sourceHorizontalActualXiConormalAdmission x u s.1 r N) =
      xiSupportMultiplicity q.1.1 •
        sourceHorizontalActualXiConormalAdmission x u q r N := by
  calc
    (∑ s : XiRightSupportFiber q,
      sourceHorizontalActualXiConormalAdmission x u s.1 r N) =
        ∑ _s : XiRightSupportFiber q,
          sourceHorizontalActualXiConormalAdmission x u q r N := by
            apply Finset.sum_congr rfl
            intro s _hs
            exact sourceHorizontalActualXiConormalAdmission_eq_of_support
              x u r s.2 N
    _ = Fintype.card (XiRightSupportFiber q) •
          sourceHorizontalActualXiConormalAdmission x u q r N := by simp
    _ = xiSupportMultiplicity q.1.1 •
          sourceHorizontalActualXiConormalAdmission x u q r N := by
            rw [routePPrimitiveGammaJuliaXiActualSupportFiber_card]

/-- The already-proved two-residue source landing remains attached to the actual conormal
coefficient chosen above. -/
theorem tendsto_sourceHorizontalActualXiConormalKreinFirstLandingBundle
    (x u : ℝ) (q : XiRightZeroCopy) (r : ℝ) (N : ℕ) :
    Tendsto
      (sourceHorizontalEulerWoldKreinFirstLandingBundle
        (sourceHorizontalActualXiConormalCoefficient x u q r) q N)
      (nhdsWithin
        (criticalMellinXiPole (xiRightZeroCopyConjEquiv q).1.1)
        ({criticalMellinXiPole (xiRightZeroCopyConjEquiv q).1.1}ᶜ))
      (nhds (sourceHorizontalEulerWoldKreinSelectedLandingBundle
        (sourceHorizontalActualXiConormalCoefficient x u q r) q N)) := by
  exact tendsto_sourceHorizontalEulerWoldKreinFirstLandingBundle _ q N

/-- **Source-natural Xi-fibre admission capstone.**  One actual Burnol/Gamma--Julia conormal
coefficient carries both Hahn--Jordan residuals through literal matrix shorting, while its Wold
component and endpoint response obey the finite co-short conservation law. -/
theorem sourceHorizontalActualXiConormalAdmission_capstone
    (x u : ℝ) (q : XiRightZeroCopy) {r : ℝ} (hr : 0 < r) (N : ℕ) :
    sourceHorizontalActualXiConormalCoefficient x u q r =
        routePPrimitiveGammaJuliaXiDescentCoefficient x u *
          xiWardCubicBurnolActualConormalFeature r q.1.1 ∧
    (sourceHorizontalNonSpectralConormalShort
      (sourceHorizontalEulerWoldJordanSelectedPhysicalAction
        (sourceHorizontalActualXiConormalCoefficient x u q r) N)).re =
        sourceHorizontalActualXiConormalAdmission x u q r N 0 ∧
    (sourceHorizontalNonSpectralConormalShort
      (sourceHorizontalEulerWoldJordanSelectedRegulator
        (sourceHorizontalActualXiConormalCoefficient x u q r) N)).re =
        sourceHorizontalActualXiConormalAdmission x u q r N 1 ∧
    sourceHorizontalActualXiConormalAdmission x u q r N 1 +
        sourceZeroHorizontalWoldRegularizedJuliaOrbitResponse
          (sourceHorizontalActualXiConormalCoefficient x u q r) q N =
      2 * sourceHorizontalLiteralConormalShort
        (sourceHorizontalActualXiConormalCoefficient x u q r) := by
  exact ⟨sourceHorizontalActualXiConormalCoefficient_eq_burnolWindow x u q hr,
    sourceHorizontalEulerWoldJordanConormalAdmission_action _ N,
    sourceHorizontalEulerWoldJordanConormalAdmission_regulator _ N,
    sourceHorizontalEulerWoldJordanConormalAdmission_endpoint_coshort _ q N⟩

/-- **Actual-fibre budget classification.**  On every nonzero admitted Xi conormal, the existing
compensated primitive-budget observable is exactly the blind `(1,-1,1)` character, and the whole
cofinal blind plane is `-a+b+2d=0`. -/
theorem sourceHorizontalActualXiConormalBudgetedReporter_blind_plane
    {x u r : ℝ} (q : XiRightZeroCopy)
    (hkappa : routePTwoPrimeJuliaWardNonlocalCoupling x u ≠ 0) (hr : r ≠ 0) :
    (∀ N : ℕ,
      sourceHorizontalEulerWoldJordanConormalLinearReporter 1 (-1) 1
          (sourceHorizontalActualXiConormalCoefficient x u q r) q N =
        sourceHorizontalWoldBVKreinEulerGammaCubicCompensatedEnergy
          (sourceHorizontalActualXiConormalCoefficient x u q r) N) ∧
    sourceHorizontalEulerWoldJordanConormalCofinalCharacter 1 (-1) 1
        (sourceHorizontalActualXiConormalCoefficient x u q r) = 0 ∧
    (∀ a b d : ℝ,
      sourceHorizontalEulerWoldJordanConormalCofinalCharacter a b d
          (sourceHorizontalActualXiConormalCoefficient x u q r) = 0 ↔
        -a + b + 2 * d = 0) := by
  have hc := sourceHorizontalActualXiConormalCoefficient_ne_zero q hkappa hr
  exact ⟨fun N =>
      sourceHorizontalEulerWoldJordanConormalLinearReporter_budgeted_eq_compensated
        _ q N,
    sourceHorizontalEulerWoldJordanConormalCofinalCharacter_budgeted_zero _,
    fun a b d =>
      sourceHorizontalEulerWoldJordanConormalCofinalCharacter_eq_zero_iff
        hc a b d⟩

end

end RHTower
