import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMRadiativeSourceFEVacuumDifferentiableNonlinearDetectorNoGo

/-!
# Real-linear vacuum response cannot scalarize the radiative source FE cocycle

HC94 leaves one regular nonlinear-detector escape: its vacuum first variation might be only
real-linear, including conjugate-linear response. This module closes that survivor.

The existing exact Birmingham--Mokhtari transfer has strictly monotone squared modulus across the
open strip at every unverified height. Together with finite zero verification this proves a new
sharp collision law: reflected and unreflected boundary-transfer moduli agree at a Xi zero exactly
on the critical line. Hence the actual horizon and boundary source-FE gains have equal squared
modulus exactly there.

If an injective real-linear map intertwines the two-channel cocycle with multiplication by one
complex gain `c`, then the real quadratic `X² - 2 Re(c) X + |c|²` annihilates both diagonal gains.
Each gain is therefore `c` or `conj(c)`, so their squared moduli agree. Transfer-modulus rigidity
forces criticality. Exact nonlinear scalarization differentiates to this real-linear intertwiner.

Thus even copy-dependent nonlinear detectors with faithful real-linear vacuum response exist on
every Xi fibre exactly under RH. Off line every such response is non-injective. Survivors are
vacuum-singular response or first-order loss of physical readout information.

`[NEW] [HB NO-GO] [REAL-LINEAR] [CONJUGATE-LINEAR] [NONLINEAR DETECTOR] [RH EQUIVALENCE]`
-/

open Complex Real Filter Topology

namespace RHTower

noncomputable section

/-- Reflected and unreflected exact BM boundary transfers have equal squared modulus at a Xi zero
exactly on the critical wall. -/
theorem d4BMXiSecondHarmonicBoundaryTransfer_normSq_reflect_eq_iff_re_eq_half
    (q : XiZeroCopy) :
    Complex.normSq
        (d4BMXiSecondHarmonicBoundaryTransfer (xiZeroCopyReflectEquiv q)) =
      Complex.normSq (d4BMXiSecondHarmonicBoundaryTransfer q) ↔
    (q.1 : ℂ).re = 1 / 2 := by
  rw [d4BMXiSecondHarmonicBoundaryTransfer_eq_scalar,
    d4BMXiSecondHarmonicBoundaryTransfer_eq_scalar]
  change Complex.normSq
      (d4BMSecondHarmonicTransferOfRho (1 - (q.1 : ℂ))) =
        Complex.normSq (d4BMSecondHarmonicTransferOfRho (q.1 : ℂ)) ↔
    (q.1 : ℂ).re = 1 / 2
  have hstrip := xi_divisor_support_re_mem_open_unit q.1
  by_cases hlow : |(q.1 : ℂ).im| ≤ 243 / 20
  · have hline := xiZeroCopy_re_eq_half_of_verifiedThrough_of_abs_im_le
      (243 / 20) rhVerifiedThrough_twoHundredFortyThree_twentieths q hlow
    constructor
    · intro _
      exact hline
    · intro _
      have hpoint : 1 - (q.1 : ℂ) = (starRingEnd ℂ) (q.1 : ℂ) := by
        apply Complex.ext
        · simp only [sub_re, one_re, Complex.conj_re]
          linarith
        · simp
      rw [hpoint, d4BMSecondHarmonicTransferOfRho_conj,
        Complex.normSq_conj]
  · have him : 13 / 2 < |(q.1 : ℂ).im| := by
      have hhigh : 243 / 20 < |(q.1 : ℂ).im| := lt_of_not_ge hlow
      nlinarith
    constructor
    · intro hcollision
      have htau : 13 / 8 < |(q.1 : ℂ).im / 4| := by
        rw [abs_div]
        norm_num
        nlinarith
      have hmono := strictMonoOn_normSq_d4BMPositiveStripTransferProfile htau
      have hsigma1 : (q.1 : ℂ).re / 4 ∈ Set.Ioo (0 : ℝ) (1 / 4) := by
        constructor <;> nlinarith
      have hsigma2 : (1 - (q.1 : ℂ).re) / 4 ∈ Set.Ioo (0 : ℝ) (1 / 4) := by
        constructor <;> nlinarith
      have hprofile :
          Complex.normSq
              (d4BMPositiveStripTransferProfile ((q.1 : ℂ) / 4)) =
            Complex.normSq (d4BMPositiveStripTransferProfile
              ((1 - (starRingEnd ℂ) (q.1 : ℂ)) / 4)) := by
        rw [d4BMPositiveStripTransferProfile_rho_div_four,
          d4BMPositiveStripTransferProfile_one_sub_conj_div_four,
          d4BMSecondHarmonicTransferOfRho_conj,
          Complex.normSq_conj]
        exact hcollision
      have hu1 : (q.1 : ℂ) / 4 =
          (((((q.1 : ℂ).re / 4 : ℝ) : ℂ) +
            ((((q.1 : ℂ).im / 4 : ℝ) : ℂ) * I))) := by
        apply Complex.ext <;> norm_num [Complex.div_re, Complex.div_im]
      have hu2 : (1 - (starRingEnd ℂ) (q.1 : ℂ)) / 4 =
          ((((((1 - (q.1 : ℂ).re) / 4 : ℝ) : ℂ) +
            ((((q.1 : ℂ).im / 4 : ℝ) : ℂ) * I)))) := by
        apply Complex.ext <;> norm_num [Complex.div_re, Complex.div_im]
      rw [hu1, hu2] at hprofile
      have hsigma := hmono.injOn hsigma1 hsigma2 hprofile
      nlinarith
    · intro hre
      have hpoint : 1 - (q.1 : ℂ) = (starRingEnd ℂ) (q.1 : ℂ) := by
        apply Complex.ext
        · simp only [sub_re, one_re, Complex.conj_re]
          linarith
        · simp
      rw [hpoint, d4BMSecondHarmonicTransferOfRho_conj,
        Complex.normSq_conj]

/-- The two actual physical radiative source-FE gains have equal squared modulus exactly on the
critical wall. -/
theorem normSq_hbXiRadiativeBoundaryCocycle_eq_horizonCocycle_iff_re_eq_half
    (q : XiZeroCopy) :
    Complex.normSq (hbXiPhaseSensitiveUnitRadiativeSourceFEBoundaryCocycle q) =
        Complex.normSq (hbXiPhaseSensitiveUnitRadiativeSourceFECocycle q) ↔
      (q.1 : ℂ).re = 1 / 2 := by
  constructor
  · intro hnorm
    have hH : 0 < Complex.normSq
        (hbXiPhaseSensitiveUnitRadiativeSourceFECocycle q) :=
      Complex.normSq_pos.mpr
        (hbXiPhaseSensitiveUnitRadiativeSourceFECocycle_ne_zero q)
    have hT : 0 < Complex.normSq
        (d4BMXiSecondHarmonicBoundaryTransfer q) :=
      Complex.normSq_pos.mpr
        (d4BMXiSecondHarmonicBoundaryTransfer_ne_zero q)
    have hnorm' := hnorm
    rw [hbXiPhaseSensitiveUnitRadiativeSourceFEBoundaryCocycle,
      Complex.normSq_div, Complex.normSq_mul, Complex.normSq_conj,
      div_eq_iff (ne_of_gt hT)] at hnorm'
    apply
      (d4BMXiSecondHarmonicBoundaryTransfer_normSq_reflect_eq_iff_re_eq_half q).mp
    nlinarith
  · intro hline
    have heq :
        hbXiPhaseSensitiveUnitRadiativeSourceFEBoundaryCocycle q =
          hbXiPhaseSensitiveUnitRadiativeSourceFECocycle q :=
      (hbXiRadiativeBoundaryCocycle_eq_horizonCocycle_iff_re_eq_half q).mpr hline
    rw [heq]

/-- One complex scalar gain seen through a possibly non-complex-linear detector response. -/
def HBXiRadiativeRealDetectorScalarizes
    (linearization :
      HBXiRadiativeDetectorCarrier →ₗ[ℝ] HBXiRadiativeDetectorCarrier)
    (c : ℂ) (q : XiZeroCopy) : Prop :=
  ∀ x : HBXiRadiativeDetectorCarrier,
    linearization (hbXiRadiativeHorizonBoundaryDetectorCocycle q x) =
      c • linearization x

/-- The target scalar multiplication's real characteristic quadratic pulls back through every
injective real-linear scalarizing response. -/
theorem hbXiRadiativeRealDetectorScalarizes_quadratic_annihilates
    (linearization :
      HBXiRadiativeDetectorCarrier →ₗ[ℝ] HBXiRadiativeDetectorCarrier)
    (hfaithful : Function.Injective linearization) (c : ℂ) (q : XiZeroCopy)
    (hscalar : HBXiRadiativeRealDetectorScalarizes linearization c q)
    (x : HBXiRadiativeDetectorCarrier) :
    hbXiRadiativeHorizonBoundaryDetectorCocycle q
          (hbXiRadiativeHorizonBoundaryDetectorCocycle q x) -
        (2 * c.re) • hbXiRadiativeHorizonBoundaryDetectorCocycle q x +
      Complex.normSq c • x = 0 := by
  apply hfaithful
  rw [map_add, map_sub, map_smul, map_smul, map_zero,
    hscalar, hscalar]
  have hc : c ^ (2 : ℕ) - (2 * c.re : ℝ) * c + Complex.normSq c = 0 := by
    rw [← Complex.add_conj c, ← Complex.mul_conj c]
    ring
  apply Prod.ext
  · simp only [Prod.fst_sub, Prod.fst_add, Prod.smul_fst, Prod.fst_zero]
    change c * (c * (linearization x).1) -
      ((2 * c.re : ℝ) : ℂ) * (c * (linearization x).1) +
        (Complex.normSq c : ℂ) * (linearization x).1 = 0
    calc
      c * (c * (linearization x).1) -
          ((2 * c.re : ℝ) : ℂ) * (c * (linearization x).1) +
            (Complex.normSq c : ℂ) * (linearization x).1 =
        (c ^ (2 : ℕ) - (2 * c.re : ℝ) * c + Complex.normSq c) *
          (linearization x).1 := by ring
      _ = 0 := by rw [hc, zero_mul]
  · simp only [Prod.snd_sub, Prod.snd_add, Prod.smul_snd, Prod.snd_zero]
    change c * (c * (linearization x).2) -
      ((2 * c.re : ℝ) : ℂ) * (c * (linearization x).2) +
        (Complex.normSq c : ℂ) * (linearization x).2 = 0
    calc
      c * (c * (linearization x).2) -
          ((2 * c.re : ℝ) : ℂ) * (c * (linearization x).2) +
            (Complex.normSq c : ℂ) * (linearization x).2 =
        (c ^ (2 : ℕ) - (2 * c.re : ℝ) * c + Complex.normSq c) *
          (linearization x).2 := by ring
      _ = 0 := by rw [hc, zero_mul]

/-- The horizon gain is one of the two roots `c`, `conj(c)` allowed by a faithful real-linear
scalarization. -/
theorem hbXiRadiativeRealDetectorScalarizes_horizonGain_eq_or_conj
    (linearization :
      HBXiRadiativeDetectorCarrier →ₗ[ℝ] HBXiRadiativeDetectorCarrier)
    (hfaithful : Function.Injective linearization) (c : ℂ) (q : XiZeroCopy)
    (hscalar : HBXiRadiativeRealDetectorScalarizes linearization c q) :
    hbXiPhaseSensitiveUnitRadiativeSourceFECocycle q = c ∨
      hbXiPhaseSensitiveUnitRadiativeSourceFECocycle q = (starRingEnd ℂ) c := by
  have hpoly := congrArg Prod.fst
    (hbXiRadiativeRealDetectorScalarizes_quadratic_annihilates
      linearization hfaithful c q hscalar hbXiRadiativeHorizonDetectorBasis)
  have hfactor :
      hbXiPhaseSensitiveUnitRadiativeSourceFECocycle q ^ (2 : ℕ) -
          (2 * c.re : ℝ) * hbXiPhaseSensitiveUnitRadiativeSourceFECocycle q +
            Complex.normSq c =
        (hbXiPhaseSensitiveUnitRadiativeSourceFECocycle q - c) *
          (hbXiPhaseSensitiveUnitRadiativeSourceFECocycle q -
            (starRingEnd ℂ) c) := by
    rw [← Complex.add_conj c, ← Complex.mul_conj c]
    ring
  dsimp [hbXiRadiativeHorizonBoundaryDetectorCocycle,
    hbXiRadiativeHorizonDetectorBasis] at hpoly
  have hpoly' : hbXiPhaseSensitiveUnitRadiativeSourceFECocycle q ^ (2 : ℕ) -
      (2 * c.re : ℝ) * hbXiPhaseSensitiveUnitRadiativeSourceFECocycle q +
        Complex.normSq c = 0 := by
    simpa [pow_two] using hpoly
  rw [hfactor] at hpoly'
  rcases mul_eq_zero.mp hpoly' with h | h
  · exact Or.inl (sub_eq_zero.mp h)
  · exact Or.inr (sub_eq_zero.mp h)

/-- The boundary gain is one of the same two conjugate roots. -/
theorem hbXiRadiativeRealDetectorScalarizes_boundaryGain_eq_or_conj
    (linearization :
      HBXiRadiativeDetectorCarrier →ₗ[ℝ] HBXiRadiativeDetectorCarrier)
    (hfaithful : Function.Injective linearization) (c : ℂ) (q : XiZeroCopy)
    (hscalar : HBXiRadiativeRealDetectorScalarizes linearization c q) :
    hbXiPhaseSensitiveUnitRadiativeSourceFEBoundaryCocycle q = c ∨
      hbXiPhaseSensitiveUnitRadiativeSourceFEBoundaryCocycle q =
        (starRingEnd ℂ) c := by
  have hpoly := congrArg Prod.snd
    (hbXiRadiativeRealDetectorScalarizes_quadratic_annihilates
      linearization hfaithful c q hscalar hbXiRadiativeBoundaryDetectorBasis)
  have hfactor :
      hbXiPhaseSensitiveUnitRadiativeSourceFEBoundaryCocycle q ^ (2 : ℕ) -
          (2 * c.re : ℝ) * hbXiPhaseSensitiveUnitRadiativeSourceFEBoundaryCocycle q +
            Complex.normSq c =
        (hbXiPhaseSensitiveUnitRadiativeSourceFEBoundaryCocycle q - c) *
          (hbXiPhaseSensitiveUnitRadiativeSourceFEBoundaryCocycle q -
            (starRingEnd ℂ) c) := by
    rw [← Complex.add_conj c, ← Complex.mul_conj c]
    ring
  dsimp [hbXiRadiativeHorizonBoundaryDetectorCocycle,
    hbXiRadiativeBoundaryDetectorBasis] at hpoly
  have hpoly' : hbXiPhaseSensitiveUnitRadiativeSourceFEBoundaryCocycle q ^ (2 : ℕ) -
      (2 * c.re : ℝ) * hbXiPhaseSensitiveUnitRadiativeSourceFEBoundaryCocycle q +
        Complex.normSq c = 0 := by
    simpa [pow_two] using hpoly
  rw [hfactor] at hpoly'
  rcases mul_eq_zero.mp hpoly' with h | h
  · exact Or.inl (sub_eq_zero.mp h)
  · exact Or.inr (sub_eq_zero.mp h)

/-- Faithful real-linear scalarization forces critical-line placement. -/
theorem hbXiRadiativeFaithfulRealDetectorScalarization_forces_re_eq_half
    (linearization :
      HBXiRadiativeDetectorCarrier →ₗ[ℝ] HBXiRadiativeDetectorCarrier)
    (hfaithful : Function.Injective linearization) (c : ℂ) (q : XiZeroCopy)
    (hscalar : HBXiRadiativeRealDetectorScalarizes linearization c q) :
    (q.1 : ℂ).re = 1 / 2 := by
  apply
    (normSq_hbXiRadiativeBoundaryCocycle_eq_horizonCocycle_iff_re_eq_half q).mp
  rcases hbXiRadiativeRealDetectorScalarizes_horizonGain_eq_or_conj
      linearization hfaithful c q hscalar with hH | hH <;>
    rcases hbXiRadiativeRealDetectorScalarizes_boundaryGain_eq_or_conj
      linearization hfaithful c q hscalar with hB | hB <;>
    simp [hH, hB]

/-- Pointwise faithful real-linear scalarization of the two physical gains. -/
def HBXiRadiativeFaithfulRealDetectorScalarizationAt (q : XiZeroCopy) : Prop :=
  ∃ linearization :
      HBXiRadiativeDetectorCarrier →ₗ[ℝ] HBXiRadiativeDetectorCarrier,
    Function.Injective linearization ∧
      ∃ c : ℂ, HBXiRadiativeRealDetectorScalarizes linearization c q

theorem hbXiRadiativeFaithfulRealDetectorScalarizationAt_iff_re_eq_half
    (q : XiZeroCopy) :
    HBXiRadiativeFaithfulRealDetectorScalarizationAt q ↔
      (q.1 : ℂ).re = 1 / 2 := by
  constructor
  · rintro ⟨linearization, hfaithful, c, hscalar⟩
    exact hbXiRadiativeFaithfulRealDetectorScalarization_forces_re_eq_half
      linearization hfaithful c q hscalar
  · intro hline
    have heq :
        hbXiPhaseSensitiveUnitRadiativeSourceFEBoundaryCocycle q =
          hbXiPhaseSensitiveUnitRadiativeSourceFECocycle q :=
      (hbXiRadiativeBoundaryCocycle_eq_horizonCocycle_iff_re_eq_half q).mpr hline
    refine ⟨LinearMap.id, Function.injective_id,
      hbXiPhaseSensitiveUnitRadiativeSourceFECocycle q, ?_⟩
    intro x
    apply Prod.ext <;>
      simp [hbXiRadiativeHorizonBoundaryDetectorCocycle, heq]

/-- Real-ray vacuum first variation with no complex-linearity assumption. -/
def HBXiRadiativeNonlinearDetectorVacuumRealFirstVariation
    (detector : HBXiRadiativeDetectorCarrier → HBXiRadiativeDetectorCarrier)
    (linearization :
      HBXiRadiativeDetectorCarrier →ₗ[ℝ] HBXiRadiativeDetectorCarrier) : Prop :=
  ∀ x : HBXiRadiativeDetectorCarrier,
    Tendsto
      (fun amplitude : ℝ =>
        (amplitude : ℂ)⁻¹ • detector ((amplitude : ℂ) • x))
      (𝓝[≠] 0) (𝓝 (linearization x))

/-- Exact nonlinear scalarization differentiates to a real-linear intertwiner. -/
theorem hbXiRadiativeNonlinearDetectorVacuumRealFirstVariation_scalarizes
    (detector : HBXiRadiativeDetectorCarrier → HBXiRadiativeDetectorCarrier)
    (linearization :
      HBXiRadiativeDetectorCarrier →ₗ[ℝ] HBXiRadiativeDetectorCarrier)
    (c : ℂ) (q : XiZeroCopy)
    (hlinear :
      HBXiRadiativeNonlinearDetectorVacuumRealFirstVariation detector linearization)
    (hscalar : HBXiRadiativeNonlinearDetectorScalarizes detector c q) :
    HBXiRadiativeRealDetectorScalarizes linearization c q := by
  intro x
  have hleft := hlinear (hbXiRadiativeHorizonBoundaryDetectorCocycle q x)
  have hright := (hlinear x).const_smul c
  have heq :
      (fun amplitude : ℝ =>
        (amplitude : ℂ)⁻¹ • detector
          ((amplitude : ℂ) •
            hbXiRadiativeHorizonBoundaryDetectorCocycle q x)) =
      (fun amplitude : ℝ =>
        c • ((amplitude : ℂ)⁻¹ • detector ((amplitude : ℂ) • x))) := by
    funext amplitude
    rw [← (hbXiRadiativeHorizonBoundaryDetectorCocycle q).map_smul,
      hscalar]
    simp only [smul_smul]
    congr 1
    ring
  rw [heq] at hleft
  exact tendsto_nhds_unique hleft hright

/-- Identity detector has identity real-linear vacuum first variation. -/
theorem hbXiRadiativeNonlinearDetectorVacuumRealFirstVariation_id :
    HBXiRadiativeNonlinearDetectorVacuumRealFirstVariation id
      (LinearMap.id :
        HBXiRadiativeDetectorCarrier →ₗ[ℝ] HBXiRadiativeDetectorCarrier) := by
  intro x
  apply tendsto_const_nhds.congr'
  filter_upwards [self_mem_nhdsWithin] with amplitude hamplitude
  have hamplitude0 : amplitude ≠ 0 := by
    simpa using hamplitude
  have hamplitudeC : (amplitude : ℂ) ≠ 0 := by
    exact_mod_cast hamplitude0
  simp only [id_eq, LinearMap.id_coe]
  apply Prod.ext <;> simp [hamplitudeC]

/-- Existence of an exact nonlinear scalarizer with faithful real-linear vacuum response. -/
def HBXiRadiativeExistsVacuumRealDifferentiableFaithfulDetectorScalarizationAt
    (q : XiZeroCopy) : Prop :=
  ∃ detector : HBXiRadiativeDetectorCarrier → HBXiRadiativeDetectorCarrier,
    ∃ linearization :
        HBXiRadiativeDetectorCarrier →ₗ[ℝ] HBXiRadiativeDetectorCarrier,
      ∃ c : ℂ,
        HBXiRadiativeNonlinearDetectorVacuumRealFirstVariation
          detector linearization ∧
        Function.Injective linearization ∧
        HBXiRadiativeNonlinearDetectorScalarizes detector c q

/-- Faithful real-linear vacuum response exists exactly on the critical wall. -/
theorem hbXiRadiativeExistsVacuumRealDifferentiableFaithfulDetectorScalarizationAt_iff_re_eq_half
    (q : XiZeroCopy) :
    HBXiRadiativeExistsVacuumRealDifferentiableFaithfulDetectorScalarizationAt q ↔
      (q.1 : ℂ).re = 1 / 2 := by
  constructor
  · rintro ⟨detector, linearization, c, hlinear, hfaithful, hscalar⟩
    exact hbXiRadiativeFaithfulRealDetectorScalarization_forces_re_eq_half
      linearization hfaithful c q
      (hbXiRadiativeNonlinearDetectorVacuumRealFirstVariation_scalarizes
        detector linearization c q hlinear hscalar)
  · intro hline
    refine ⟨id, LinearMap.id,
      hbXiPhaseSensitiveUnitRadiativeSourceFECocycle q,
      hbXiRadiativeNonlinearDetectorVacuumRealFirstVariation_id,
      Function.injective_id, ?_⟩
    have heq :
        hbXiPhaseSensitiveUnitRadiativeSourceFEBoundaryCocycle q =
          hbXiPhaseSensitiveUnitRadiativeSourceFECocycle q :=
      (hbXiRadiativeBoundaryCocycle_eq_horizonCocycle_iff_re_eq_half q).mpr hline
    intro x
    apply Prod.ext <;>
      simp [hbXiRadiativeHorizonBoundaryDetectorCocycle, heq]

/-- Sharp off-wall survivor: every exact scalarizing real-linear first variation loses
injectivity. -/
theorem hbXiRadiativeNonlinearDetector_realFirstVariation_not_injective_of_offLine
    (detector : HBXiRadiativeDetectorCarrier → HBXiRadiativeDetectorCarrier)
    (linearization :
      HBXiRadiativeDetectorCarrier →ₗ[ℝ] HBXiRadiativeDetectorCarrier)
    (c : ℂ) (q : XiZeroCopy)
    (hlinear :
      HBXiRadiativeNonlinearDetectorVacuumRealFirstVariation detector linearization)
    (hscalar : HBXiRadiativeNonlinearDetectorScalarizes detector c q)
    (hoff : (q.1 : ℂ).re ≠ 1 / 2) :
    ¬ Function.Injective linearization := by
  intro hfaithful
  apply hoff
  exact hbXiRadiativeFaithfulRealDetectorScalarization_forces_re_eq_half
    linearization hfaithful c q
    (hbXiRadiativeNonlinearDetectorVacuumRealFirstVariation_scalarizes
      detector linearization c q hlinear hscalar)

/-- Copy-dependent nonlinear detectors with faithful real-linear first variations on every Xi
fibre. -/
def HBXiRadiativeGlobalVacuumRealDifferentiableFaithfulDetectorScalarization : Prop :=
  ∃ detector : XiZeroCopy →
      (HBXiRadiativeDetectorCarrier → HBXiRadiativeDetectorCarrier),
    ∃ linearization : XiZeroCopy →
        (HBXiRadiativeDetectorCarrier →ₗ[ℝ] HBXiRadiativeDetectorCarrier),
      ∃ c : XiZeroCopy → ℂ,
        ∀ q : XiZeroCopy,
          HBXiRadiativeNonlinearDetectorVacuumRealFirstVariation
              (detector q) (linearization q) ∧
          Function.Injective (linearization q) ∧
          HBXiRadiativeNonlinearDetectorScalarizes (detector q) (c q) q

theorem hbXiRadiativeGlobalVacuumRealDifferentiableFaithfulDetectorScalarization_iff_rh :
    HBXiRadiativeGlobalVacuumRealDifferentiableFaithfulDetectorScalarization ↔
      RiemannHypothesis := by
  constructor
  · rintro ⟨detector, linearization, c, h⟩
    apply (forall_hbXiPeierlsUnitSourceFEBasisTransport_fixedPairing_iff_rh).mp
    intro q
    apply (hbXiPeierlsUnitSourceFEBasisTransport_fixedPairing_iff q).mpr
    exact hbXiRadiativeFaithfulRealDetectorScalarization_forces_re_eq_half
      (linearization q) (h q).2.1 (c q) q
      (hbXiRadiativeNonlinearDetectorVacuumRealFirstVariation_scalarizes
        (detector q) (linearization q) (c q) q (h q).1 (h q).2.2)
  · intro hRH
    refine ⟨fun _ => id, fun _ => LinearMap.id,
      fun q => hbXiPhaseSensitiveUnitRadiativeSourceFECocycle q, ?_⟩
    intro q
    have hline : (q.1 : ℂ).re = 1 / 2 :=
      (hbXiPeierlsUnitSourceFEBasisTransport_fixedPairing_iff q).mp
        ((forall_hbXiPeierlsUnitSourceFEBasisTransport_fixedPairing_iff_rh).mpr hRH q)
    have heq :
        hbXiPhaseSensitiveUnitRadiativeSourceFEBoundaryCocycle q =
          hbXiPhaseSensitiveUnitRadiativeSourceFECocycle q :=
      (hbXiRadiativeBoundaryCocycle_eq_horizonCocycle_iff_re_eq_half q).mpr hline
    refine ⟨hbXiRadiativeNonlinearDetectorVacuumRealFirstVariation_id,
      Function.injective_id, ?_⟩
    intro x
    apply Prod.ext <;>
      simp [hbXiRadiativeHorizonBoundaryDetectorCocycle, heq]

/-- Closed route certificate for faithful real- and conjugate-linear vacuum response. -/
def D4HBVacuumRealDifferentiableNonlinearDetectorScalarizationRouteKilled : Prop :=
  (∀ q : XiZeroCopy,
    Complex.normSq
        (d4BMXiSecondHarmonicBoundaryTransfer (xiZeroCopyReflectEquiv q)) =
      Complex.normSq (d4BMXiSecondHarmonicBoundaryTransfer q) ↔
        (q.1 : ℂ).re = 1 / 2) ∧
  (∀ q : XiZeroCopy,
    HBXiRadiativeExistsVacuumRealDifferentiableFaithfulDetectorScalarizationAt q ↔
      (q.1 : ℂ).re = 1 / 2) ∧
  (∀ (detector : HBXiRadiativeDetectorCarrier → HBXiRadiativeDetectorCarrier)
      (linearization :
        HBXiRadiativeDetectorCarrier →ₗ[ℝ] HBXiRadiativeDetectorCarrier)
      (c : ℂ) (q : XiZeroCopy),
    HBXiRadiativeNonlinearDetectorVacuumRealFirstVariation detector linearization →
    HBXiRadiativeNonlinearDetectorScalarizes detector c q →
    (q.1 : ℂ).re ≠ 1 / 2 →
      ¬ Function.Injective linearization) ∧
  (HBXiRadiativeGlobalVacuumRealDifferentiableFaithfulDetectorScalarization ↔
    RiemannHypothesis)

/-- Premise-free certificate: real-linear or conjugate-linear first response cannot manufacture
one faithful scalar FE gain off the critical wall. -/
theorem d4HBVacuumRealDifferentiableNonlinearDetectorScalarizationRouteKilled :
    D4HBVacuumRealDifferentiableNonlinearDetectorScalarizationRouteKilled := by
  exact ⟨
    d4BMXiSecondHarmonicBoundaryTransfer_normSq_reflect_eq_iff_re_eq_half,
    hbXiRadiativeExistsVacuumRealDifferentiableFaithfulDetectorScalarizationAt_iff_re_eq_half,
    fun detector linearization c q =>
      hbXiRadiativeNonlinearDetector_realFirstVariation_not_injective_of_offLine
        detector linearization c q,
    hbXiRadiativeGlobalVacuumRealDifferentiableFaithfulDetectorScalarization_iff_rh⟩

end

end RHTower
