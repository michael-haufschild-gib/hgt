import GaloisForLFunctions.RHTower.EulerPrimitiveJointDepthKreinXiLanding
import GaloisForLFunctions.RHTower.CCMCriticalMellinDivisorTomography
import GaloisForLFunctions.RHTower.RoutePCompletedXiConormalBaseResidue

open Complex Filter Function Set WithTop Topology MeasureTheory
open scoped BigOperators ComplexOrder
open GaloisForLFunctions

namespace RHTower

noncomputable section

/-- The completed signed primitive-depth source, before positive Gram formation, carrying the
moving Route-P radial column in the same critical-Mellin coordinate. -/
def frankensteinKreinCCMRoutePSignedConormalColumn (u : ℂ) (r : ℝ) : ℂ :=
  xiGammaEulerPrimitiveJointDepthPoleFilledCompletedTrace u *
    routePXiBaseConormalResidueFeature (u + 1) r

/-- The signed completed primitive-depth trace has residue `i m_rho` at every CCM Xi pole. -/
theorem xiGammaEulerPrimitiveJointDepthPoleFilledCompletedTrace_residue
    (rho : XiDivisorSupport) :
    Tendsto
      (fun u : ℂ => (u - criticalMellinXiPole rho) *
        xiGammaEulerPrimitiveJointDepthPoleFilledCompletedTrace u)
      (nhdsWithin (criticalMellinXiPole rho) ({criticalMellinXiPole rho}ᶜ))
      (nhds (I * (inverseTiltedXiMultiplicity rho : ℂ))) := by
  let p : ℂ := criticalMellinXiPole rho
  change Tendsto
    (fun u : ℂ => (u - p) *
      xiGammaEulerPrimitiveJointDepthPoleFilledCompletedTrace u)
    (nhdsWithin p ({p}ᶜ))
    (nhds (I * (inverseTiltedXiMultiplicity rho : ℂ)))
  have hp : -1 < p.re := by
    simpa only [p] using criticalMellinXiPole_re_gt_neg_one rho
  have hmero : MeromorphicAt regularizedCriticalMellinDefect p :=
    meromorphicOn_regularizedCriticalMellinDefect_rightNegOne p hp
  have htrace := hmero.tendsto_nhds_meromorphicTrailingCoeffAt
  rw [show meromorphicOrderAt regularizedCriticalMellinDefect p =
      ((-1 : ℤ) : WithTop ℤ) by
        simpa only [p] using
          meromorphicOrderAt_regularizedCriticalMellinDefect_eq_neg_one rho] at htrace
  simp only [WithTop.untop₀_coe, neg_neg, zpow_one, smul_eq_mul] at htrace
  rw [show meromorphicTrailingCoeffAt regularizedCriticalMellinDefect p =
      (inverseTiltedXiMultiplicity rho : ℂ) by
        simpa only [p] using
          meromorphicTrailingCoeffAt_regularizedCriticalMellinDefect rho] at htrace
  have hprho : p + 1 = (rho : ℂ) := by
    simpa only [p] using criticalMellinXiPole_add_one rho
  have hrhoPos : 0 < ((rho : ℂ).re) :=
    (xi_divisor_support_re_mem_open_unit rho).1
  have hpoles : ∀ n : ℕ, ((p + 1) / 2) ≠ -(n : ℂ) := by
    intro n hn
    have hre := congrArg Complex.re hn
    rw [hprho] at hre
    simp only [Complex.div_ofNat_re, Complex.neg_re, Complex.natCast_re] at hre
    have hnnonneg : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hdigamma : AnalyticAt ℂ Complex.digamma ((p + 1) / 2) := by
    have hpsi : (fun w => deriv Complex.Gamma w / Complex.Gamma w) =
        Complex.digamma := by
      funext w
      rw [Complex.digamma_def, logDeriv_apply]
    have h := GaloisForLFunctions.analyticAt_iteratedDeriv_logDeriv 0 _ hpoles
    rw [hpsi] at h
    simpa [iteratedDeriv_zero] using h
  have harg : AnalyticAt ℂ (fun u : ℂ => (u + 1) / 2) p := by fun_prop
  have hdigammaComp : AnalyticAt ℂ
      (fun u : ℂ => Complex.digamma ((u + 1) / 2)) p := by
    simpa [Function.comp_def] using
      AnalyticAt.comp (f := fun u : ℂ => (u + 1) / 2) (x := p)
        hdigamma harg
  have hgamma : AnalyticAt ℂ
      (fun u : ℂ => gammaRealLogConnection (u + 1)) p := by
    unfold gammaRealLogConnection
    exact analyticAt_const.neg.add
      (hdigammaComp.div analyticAt_const (by norm_num))
  have htoZero : Tendsto (fun u : ℂ => u - p)
      (nhdsWithin p ({p}ᶜ)) (nhds 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds (by
      simpa using
        (by fun_prop : ContinuousAt (fun u : ℂ => u - p) p).tendsto)
  have hgammaWithin : Tendsto
      (fun u : ℂ => gammaRealLogConnection (u + 1))
      (nhdsWithin p ({p}ᶜ))
      (nhds (gammaRealLogConnection (p + 1))) :=
    tendsto_nhdsWithin_of_tendsto_nhds hgamma.continuousAt.tendsto
  have hgammaZero : Tendsto
      (fun u : ℂ => (u - p) * gammaRealLogConnection (u + 1))
      (nhdsWithin p ({p}ᶜ)) (nhds 0) := by
    simpa using htoZero.mul hgammaWithin
  have hsum := htrace.add hgammaZero
  have hcompleted := hsum.const_mul I
  convert hcompleted using 1
  · funext u
    simp only [xiGammaEulerPrimitiveJointDepthPoleFilledCompletedTrace,
      Pi.mul_apply]
    ring
  · simp

/-- Coefficient-faithful signed source residue: multiplicity and radial column remain in one
carrier, before any Hermitian square. -/
theorem frankensteinKreinCCMRoutePSignedConormalColumn_residue
    (rho : XiDivisorSupport) (r : ℝ) :
    Tendsto
      (fun u : ℂ => (u - criticalMellinXiPole rho) *
        frankensteinKreinCCMRoutePSignedConormalColumn u r)
      (nhdsWithin (criticalMellinXiPole rho) ({criticalMellinXiPole rho}ᶜ))
      (nhds (I * (inverseTiltedXiMultiplicity rho : ℂ) *
        routePXiBaseConormalResidueFeature (rho : ℂ) r)) := by
  have htrace :=
    xiGammaEulerPrimitiveJointDepthPoleFilledCompletedTrace_residue rho
  have hfeature : Tendsto
      (fun u : ℂ => routePXiBaseConormalResidueFeature (u + 1) r)
      (nhdsWithin (criticalMellinXiPole rho) ({criticalMellinXiPole rho}ᶜ))
      (nhds (routePXiBaseConormalResidueFeature (rho : ℂ) r)) := by
    have hcontinuous : ContinuousAt
        (fun u : ℂ => routePXiBaseConormalResidueFeature (u + 1) r)
        (criticalMellinXiPole rho) := by
      unfold routePXiBaseConormalResidueFeature
      fun_prop
    apply tendsto_nhdsWithin_of_tendsto_nhds
    convert hcontinuous.tendsto using 1
    rw [criticalMellinXiPole_add_one]
  have h := htrace.mul hfeature
  simpa [frankensteinKreinCCMRoutePSignedConormalColumn, mul_assoc] using h

/-- Dividing by the signed analytic multiplicity recovers exactly one Route-P base conormal
feature.  No simple-zero premise is used. -/
theorem frankensteinKreinCCMRoutePSignedConormalColumn_normalized_residue
    (rho : XiDivisorSupport) (r : ℝ) :
    Tendsto
      (fun u : ℂ =>
        ((u - criticalMellinXiPole rho) *
          frankensteinKreinCCMRoutePSignedConormalColumn u r) /
            (I * (inverseTiltedXiMultiplicity rho : ℂ)))
      (nhdsWithin (criticalMellinXiPole rho) ({criticalMellinXiPole rho}ᶜ))
      (nhds (routePXiBaseConormalResidueFeature (rho : ℂ) r)) := by
  have hmNat : inverseTiltedXiMultiplicity rho ≠ 0 :=
    Nat.ne_of_gt (inverseTiltedXiMultiplicity_pos rho)
  have hm : (I * (inverseTiltedXiMultiplicity rho : ℂ)) ≠ 0 :=
    mul_ne_zero Complex.I_ne_zero (Nat.cast_ne_zero.mpr hmNat)
  have h :=
    (frankensteinKreinCCMRoutePSignedConormalColumn_residue rho r).div_const
      (I * (inverseTiltedXiMultiplicity rho : ℂ))
  convert h using 1
  field_simp [hm]

/-- Critical-line reflection becomes reflection about `Re u = -1/2` in the signed source's CCM
coordinate. -/
theorem criticalMellinXiPole_lineConj (rho : XiDivisorSupport) :
    criticalMellinXiPole (xiZeroLineConjEquiv rho) =
      -1 - star (criticalMellinXiPole rho) := by
  rw [criticalMellinXiPole, criticalMellinXiPole,
    xiZeroLineConjEquiv_apply]
  simp
  ring

/-- Both reflected Xi orientations are residues of the same signed source family, with their own
exact common analytic multiplicity. -/
theorem frankensteinKreinCCMRoutePSignedConormalColumn_both_orientations
    (rho : XiDivisorSupport) (r : ℝ) :
    Tendsto
        (fun u : ℂ =>
          ((u - criticalMellinXiPole rho) *
            frankensteinKreinCCMRoutePSignedConormalColumn u r) /
              (I * (inverseTiltedXiMultiplicity rho : ℂ)))
        (nhdsWithin (criticalMellinXiPole rho) ({criticalMellinXiPole rho}ᶜ))
        (nhds (routePXiBaseConormalResidueFeature (rho : ℂ) r)) ∧
      Tendsto
        (fun u : ℂ =>
          ((u - criticalMellinXiPole (xiZeroLineConjEquiv rho)) *
            frankensteinKreinCCMRoutePSignedConormalColumn u r) /
              (I * (inverseTiltedXiMultiplicity (xiZeroLineConjEquiv rho) : ℂ)))
        (nhdsWithin (criticalMellinXiPole (xiZeroLineConjEquiv rho))
          ({criticalMellinXiPole (xiZeroLineConjEquiv rho)}ᶜ))
        (nhds (routePXiBaseConormalResidueFeature
          ((xiZeroLineConjEquiv rho : XiDivisorSupport) : ℂ) r)) := by
  exact ⟨frankensteinKreinCCMRoutePSignedConormalColumn_normalized_residue rho r,
    frankensteinKreinCCMRoutePSignedConormalColumn_normalized_residue
      (xiZeroLineConjEquiv rho) r⟩

/-- Exact balanced-wall obstruction: pairing the two retained reflection orientations cancels all
radial exponential damping and leaves the polynomial density `r^(2 : ℕ)`. -/
theorem star_routePXiBaseConormalResidueFeature_mul_lineConj_eq_sq
    (rho : XiDivisorSupport) (r : ℝ) :
    star (routePXiBaseConormalResidueFeature (rho : ℂ) r) *
        routePXiBaseConormalResidueFeature
          ((xiZeroLineConjEquiv rho : XiDivisorSupport) : ℂ) r =
      (r : ℂ) ^ 2 := by
  rw [routePXiBaseConormalResidueFeature,
    routePXiBaseConormalResidueFeature, xiZeroLineConjEquiv_apply]
  change (starRingEnd ℂ)
      ((r : ℂ) * Complex.exp (-(((rho : ℂ) - 1 / 2) * (r : ℂ)))) *
    ((r : ℂ) * Complex.exp (-((1 - star (rho : ℂ) - 1 / 2) * (r : ℂ)))) = _
  rw [map_mul, Complex.conj_ofReal, ← Complex.exp_conj]
  simp only [map_neg, map_mul, map_sub, map_one, map_div₀,
    _root_.map_ofNat, Complex.conj_ofReal]
  calc
    (r : ℂ) * Complex.exp (-((star (rho : ℂ) - 1 / 2) * (r : ℂ))) *
        ((r : ℂ) * Complex.exp
          (-((1 - star (rho : ℂ) - 1 / 2) * (r : ℂ)))) =
      (r : ℂ) ^ 2 *
        (Complex.exp (-((star (rho : ℂ) - 1 / 2) * (r : ℂ))) *
          Complex.exp (-((1 - star (rho : ℂ) - 1 / 2) * (r : ℂ)))) := by ring
    _ = (r : ℂ) ^ 2 * Complex.exp
        (-((star (rho : ℂ) - 1 / 2) * (r : ℂ)) +
          -((1 - star (rho : ℂ) - 1 / 2) * (r : ℂ))) := by
      rw [Complex.exp_add]
    _ = (r : ℂ) ^ 2 := by
      rw [show
        -((star (rho : ℂ) - 1 / 2) * (r : ℂ)) +
            -((1 - star (rho : ℂ) - 1 / 2) * (r : ℂ)) = 0 by ring,
        Complex.exp_zero, mul_one]

/-- The polynomial density exposed at the balanced wall is not integrable on the radial
half-line. -/
theorem not_integrableOn_routePBalancedReflectionPolynomialDensity :
    ¬ IntegrableOn (fun r : ℝ => (r : ℂ) ^ 2) (Ioi 0) := by
  intro h
  have hre : IntegrableOn (fun r : ℝ => ((r : ℂ) ^ 2).re) (Ioi 0) := h.re
  have hre' : IntegrableOn (fun r : ℝ => r ^ 2) (Ioi 0) := by
    refine hre.congr_fun ?_ measurableSet_Ioi
    intro r _
    simp [pow_two]
  have hpow : IntegrableOn (fun r : ℝ => r ^ (2 : ℝ)) (Ioi 0) := by
    simpa [Real.rpow_two] using hre'
  exact not_integrableOn_Ioi_rpow 2 hpow

/-- Hence the two reflection orientations cannot be paired in the ordinary Route-P radial
`L²` carrier.  Signed cancellation must occur before this completion. -/
theorem not_integrableOn_routePBaseConormalReflectionCross
    (rho : XiDivisorSupport) :
    ¬ IntegrableOn
      (fun r : ℝ =>
        star (routePXiBaseConormalResidueFeature (rho : ℂ) r) *
          routePXiBaseConormalResidueFeature
            ((xiZeroLineConjEquiv rho : XiDivisorSupport) : ℂ) r)
      (Ioi 0) := by
  intro h
  apply not_integrableOn_routePBalancedReflectionPolynomialDensity
  exact h.congr_fun
    (fun r _ => star_routePXiBaseConormalResidueFeature_mul_lineConj_eq_sq rho r)
    measurableSet_Ioi

/-- Explicit normalized source-residue value used by the finite Route-P receiver. -/
def frankensteinKreinCCMRoutePNormalizedSourceResidueFeature
    (rho : XiDivisorSupport) (r : ℝ) : ℂ :=
  (I * (inverseTiltedXiMultiplicity rho : ℂ) *
      routePXiBaseConormalResidueFeature (rho : ℂ) r) /
    (I * (inverseTiltedXiMultiplicity rho : ℂ))

theorem frankensteinKreinCCMRoutePNormalizedSourceResidueFeature_eq
    (rho : XiDivisorSupport) (r : ℝ) :
    frankensteinKreinCCMRoutePNormalizedSourceResidueFeature rho r =
      routePXiBaseConormalResidueFeature (rho : ℂ) r := by
  have hmNat : inverseTiltedXiMultiplicity rho ≠ 0 :=
    Nat.ne_of_gt (inverseTiltedXiMultiplicity_pos rho)
  have hm : (I * (inverseTiltedXiMultiplicity rho : ℂ)) ≠ 0 :=
    mul_ne_zero Complex.I_ne_zero (Nat.cast_ne_zero.mpr hmNat)
  rw [frankensteinKreinCCMRoutePNormalizedSourceResidueFeature]
  field_simp [hm]

/-- Finite Gram extracted from the literal signed source residues. -/
def frankensteinKreinCCMRoutePSourceResidueGramMatrix {N : ℕ}
    (q : Fin N → XiRightZeroCopy) : Matrix (Fin N) (Fin N) ℂ :=
  fun i j => ∫ r : ℝ in Ioi 0,
    star (frankensteinKreinCCMRoutePNormalizedSourceResidueFeature (q i).1.1 r) *
      frankensteinKreinCCMRoutePNormalizedSourceResidueFeature (q j).1.1 r

/-- Exact cross-corpus handoff: the signed primitive-depth/CCM source residue Gram is Route-P's
base Cauchy-cube target matrix. -/
theorem frankensteinKreinCCMRoutePSourceResidueGramMatrix_eq
    {N : ℕ} (q : Fin N → XiRightZeroCopy) :
    frankensteinKreinCCMRoutePSourceResidueGramMatrix q =
      routePStrictRightZeroBaseCauchyCubicKernelMatrix q := by
  ext i j
  change (∫ r : ℝ in Ioi 0,
      star (frankensteinKreinCCMRoutePNormalizedSourceResidueFeature (q i).1.1 r) *
        frankensteinKreinCCMRoutePNormalizedSourceResidueFeature (q j).1.1 r) = _
  simp_rw [frankensteinKreinCCMRoutePNormalizedSourceResidueFeature_eq]
  exact congrArg (fun M => M i j)
    (routePStrictRightZeroConormalResidueGramMatrix_eq q)

end

end RHTower
