import GaloisForLFunctions.RHTower.XiHurwitzFESchwarzPairValueRelation
import GaloisForLFunctions.RHTower.PrimeSeamDampingAperture
import GaloisForLFunctions.RHTower.XiRationalHurwitzDyadicRefinement
import GaloisForLFunctions.RHTower.XiHurwitzAnchorJetProjectiveReflection

/-!
# The FE--Schwarz Hurwitz circuit is the finite-value reflection aperture

The continued-Hurwitz differential circuit, cofinal positive damping, bounded rational-Hurwitz
power rays, and exact finite-value refinement laws are pointwise coordinates on the same
horizontal reflection defect.  This file records the direct equivalences, without passing through
an RH hypothesis in either direction.
-/

open Complex

namespace RHTower

noncomputable section

/-- Pointwise differential/value aperture law: FE--Schwarz pair dependence is exactly membership
in every positively damped reflected prime-seam sector. -/
theorem continuedHurwitzFESchwarzPairDependent_iff_allPositivePrimeSeamDamping
    {rho : ℂ} (hstrip : 0 < rho.re ∧ rho.re < 1) :
    ContinuedHurwitzPairDifferentiallyDependent
        (1 - rho) ((starRingEnd ℂ) rho) ↔
      ∀ theta : ℝ, 0 < theta →
        Summable (weightedNatPrimeSeamChargeNormSq theta rho) :=
  (continuedHurwitzFESchwarzPairDifferentiallyDependent_iff_re_eq_half hstrip).trans
    (allPositivePrimeSeamDamping_iff_re_eq_half rho).symm

/-- Pointwise differential/value ray law: one nondegenerate rational-Hurwitz power ray is bounded
exactly when the FE--Schwarz pair is dependent. -/
theorem continuedHurwitzFESchwarzPairDependent_iff_rationalHurwitzPowerEnergyBounded
    {rho : ℂ} (hstrip : 0 < rho.re ∧ rho.re < 1)
    (n : ℕ) (hn : 1 < n) :
    ContinuedHurwitzPairDifferentiallyDependent
        (1 - rho) ((starRingEnd ℂ) rho) ↔
      RationalHurwitzPowerEnergyBounded n rho :=
  (continuedHurwitzFESchwarzPairDifferentiallyDependent_iff_re_eq_half hstrip).trans
    (rationalHurwitzPowerEnergyBounded_iff_re_eq_half hstrip n hn).symm

/-- Pointwise differential/refinement law: disappearance of the nonlinear excess at any genuine
power refinement is exactly FE--Schwarz pair dependence. -/
theorem continuedHurwitzFESchwarzPairDependent_iff_rationalHurwitzPowerLinearRefinement
    {rho : ℂ} (hstrip : 0 < rho.re ∧ rho.re < 1)
    (n : ℕ) (hn : 1 < n) (k : ℕ) (hk : 1 < k) :
    ContinuedHurwitzPairDifferentiallyDependent
        (1 - rho) ((starRingEnd ℂ) rho) ↔
      normalizedRationalHurwitzReflectionEnergy (n ^ k) rho =
        (k : ℝ) ^ 2 * normalizedRationalHurwitzReflectionEnergy n rho :=
  (continuedHurwitzFESchwarzPairDifferentiallyDependent_iff_re_eq_half hstrip).trans
    (normalizedRationalHurwitzReflectionEnergy_pow_eq_linear_iff
      hstrip n hn k hk).symm

/-- Pointwise differential/two-scale law: equality at any two distinct normalized finite Hurwitz
scales is exactly FE--Schwarz pair dependence. -/
theorem continuedHurwitzFESchwarzPairDependent_iff_rationalHurwitzTwoScaleEnergyEqual
    {rho : ℂ} (hstrip : 0 < rho.re ∧ rho.re < 1)
    {m n : ℕ} (hm : 1 < m) (hmn : m < n) :
    ContinuedHurwitzPairDifferentiallyDependent
        (1 - rho) ((starRingEnd ℂ) rho) ↔
      normalizedRationalHurwitzReflectionEnergy m rho =
        normalizedRationalHurwitzReflectionEnergy n rho :=
  (continuedHurwitzFESchwarzPairDifferentiallyDependent_iff_re_eq_half hstrip).trans
    (normalizedRationalHurwitzReflectionEnergy_eq_iff_re_eq_half
      hstrip hm hmn).symm

/-- At an actual Xi zero, the all-order projective anchor-jet relation is exactly the rank-two
FE--Schwarz differential circuit. -/
theorem xiHurwitzAnchorJetProjectiveReflectionCompatible_iff_FESchwarzPairDependent
    {rho : ℂ} (hstrip : 0 < rho.re ∧ rho.re < 1) (hzero : xi rho = 0) :
    XiHurwitzAnchorJetProjectiveReflectionCompatible rho ↔
      ContinuedHurwitzPairDifferentiallyDependent
        (1 - rho) ((starRingEnd ℂ) rho) :=
  (xiHurwitzAnchorJetProjectiveReflectionCompatible_iff_re_eq_half
    hstrip hzero).trans
      (continuedHurwitzFESchwarzPairDifferentiallyDependent_iff_re_eq_half hstrip).symm

/-- Global differential/damping law, proved by lifting the pointwise equivalence over the exact Xi
divisor support.  No RH theorem is used in the proof. -/
theorem xiHurwitzFESchwarzPairCircuit_iff_allPositivePrimeSeamDamping :
    XiHurwitzFESchwarzPairCircuit ↔ XiAllPositivePrimeSeamDamping := by
  constructor
  · intro hcircuit theta htheta rho hzero
    let support : XiDivisorSupport :=
      ⟨rho, mem_xi_divisor_support_of_eq_zero hzero⟩
    exact
      ((continuedHurwitzFESchwarzPairDependent_iff_allPositivePrimeSeamDamping
        (xi_divisor_support_re_mem_open_unit support)).mp (hcircuit support))
        theta htheta
  · intro hdamping rho
    apply
      (continuedHurwitzFESchwarzPairDependent_iff_allPositivePrimeSeamDamping
        (xi_divisor_support_re_mem_open_unit rho)).mpr
    exact fun theta htheta =>
      hdamping theta htheta rho (xi_eq_zero_of_mem_divisor_support rho)

/-- Global differential/bounded-ray law for every nondegenerate modulus. -/
theorem xiHurwitzFESchwarzPairCircuit_iff_rationalHurwitzPowerEnergyBounded
    (n : ℕ) (hn : 1 < n) :
    XiHurwitzFESchwarzPairCircuit ↔
      XiRationalHurwitzPowerEnergyBounded n := by
  constructor <;> intro h rho
  · exact
      (continuedHurwitzFESchwarzPairDependent_iff_rationalHurwitzPowerEnergyBounded
        (xi_divisor_support_re_mem_open_unit rho) n hn).mp (h rho)
  · exact
      (continuedHurwitzFESchwarzPairDependent_iff_rationalHurwitzPowerEnergyBounded
        (xi_divisor_support_re_mem_open_unit rho) n hn).mpr (h rho)

/-- Global differential/power-refinement law at every genuine power. -/
theorem xiHurwitzFESchwarzPairCircuit_iff_rationalHurwitzPowerLinearRefinement
    (n : ℕ) (hn : 1 < n) (k : ℕ) (hk : 1 < k) :
    XiHurwitzFESchwarzPairCircuit ↔
      XiRationalHurwitzPowerLinearRefinement n k := by
  constructor <;> intro h rho
  · exact
      (continuedHurwitzFESchwarzPairDependent_iff_rationalHurwitzPowerLinearRefinement
        (xi_divisor_support_re_mem_open_unit rho) n hn k hk).mp (h rho)
  · exact
      (continuedHurwitzFESchwarzPairDependent_iff_rationalHurwitzPowerLinearRefinement
        (xi_divisor_support_re_mem_open_unit rho) n hn k hk).mpr (h rho)

/-- Global differential/two-scale law at every pair of distinct nontrivial moduli. -/
theorem xiHurwitzFESchwarzPairCircuit_iff_rationalHurwitzTwoScaleEnergyEqual
    {m n : ℕ} (hm : 1 < m) (hmn : m < n) :
    XiHurwitzFESchwarzPairCircuit ↔
      XiRationalHurwitzTwoScaleEnergyEqual m n := by
  constructor <;> intro h rho
  · exact
      (continuedHurwitzFESchwarzPairDependent_iff_rationalHurwitzTwoScaleEnergyEqual
        (xi_divisor_support_re_mem_open_unit rho) hm hmn).mp (h rho)
  · exact
      (continuedHurwitzFESchwarzPairDependent_iff_rationalHurwitzTwoScaleEnergyEqual
        (xi_divisor_support_re_mem_open_unit rho) hm hmn).mpr (h rho)

/-- The global FE--Schwarz circuit is exactly every fixed nondegenerate dyadic finite-value
linearization interface. -/
theorem xiHurwitzFESchwarzPairCircuit_iff_rationalHurwitzDyadicLinearRefinement
    (n : ℕ) (hn : 1 < n) :
    XiHurwitzFESchwarzPairCircuit ↔
      XiRationalHurwitzDyadicLinearRefinement n :=
  (xiHurwitzFESchwarzPairCircuit_iff_rationalHurwitzPowerLinearRefinement
    n hn 2 (by norm_num)).trans
      (xiRationalHurwitzPowerLinearRefinement_two_iff_dyadic n)

/-- The global all-order projective anchor-jet law and the rank-two FE--Schwarz circuit are the
same proposition over the Xi divisor. -/
theorem xiHurwitzAnchorJetProjectiveReflectionLaw_iff_FESchwarzPairCircuit :
    XiHurwitzAnchorJetProjectiveReflectionLaw ↔
      XiHurwitzFESchwarzPairCircuit := by
  constructor <;> intro h rho
  · exact
      (xiHurwitzAnchorJetProjectiveReflectionCompatible_iff_FESchwarzPairDependent
        (xi_divisor_support_re_mem_open_unit rho)
        (xi_eq_zero_of_mem_divisor_support rho)).mp (h rho)
  · exact
      (xiHurwitzAnchorJetProjectiveReflectionCompatible_iff_FESchwarzPairDependent
        (xi_divisor_support_re_mem_open_unit rho)
        (xi_eq_zero_of_mem_divisor_support rho)).mpr (h rho)

end

end RHTower
