import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.GradedSourceConeBoundaryRigidity
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.AllParityCriticalDeficitAndEndpointSobolevLaws
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.WeilEnergyIsUnboundedAtEveryAperture
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.LambdaRingEffectivityAndHeckeLefschetzRigidity

/-!
# Exact arithmetic Riemann–Roch supply at every aperture

The all-parity critical-deficit formula supplies a reserve built from the Gamma term,
archimedean jump energy, horizon energy, and the integrated prime deficit. The graded cone
defined by this reserve has Riemann–Roch at every aperture on the original scaling surface.
The exact formula identifies it with the positive cone. Bézout and ampleness therefore remain
equivalent to nonnegativity of this arithmetic reserve; the representation does not prove its sign.
-/

open MeasureTheory Set Zeta23 RHTower
open GaloisForLFunctions.ArithmeticCompensationTheory
  GaloisForLFunctions.BiScaleUncertainty
  GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
  GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge

noncomputable section

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri

namespace PolarSurface

variable {C : Type*} [AddCommGroup C] [Module ℝ C] (S : PolarSurface C)

/-- Additive closure of the full positive cone already forces Hodge index. -/
theorem positiveCone_add_closed_iff_hodgeIndex :
    (∀ x ∈ S.positiveCone, ∀ y ∈ S.positiveCone, x + y ∈ S.positiveCone) ↔
      S.HodgeIndex := by
  constructor
  · intro hadd p hpH hpV
    by_contra hle
    have hp : 0 < S.pair p p := lt_of_not_ge hle
    let t := Real.sqrt (S.pair p p / 2)
    have ht : t ^ 2 = S.pair p p / 2 := Real.sq_sqrt (by positivity)
    let d := S.H - S.V
    have hsq (a b : ℝ) :
        S.pair (a • p + b • d) (a • p + b • d) =
          a ^ 2 * S.pair p p - 2 * b ^ 2 := by
      simp only [d, map_add, map_sub, map_smul, LinearMap.add_apply,
        LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul,
        S.pair_comm S.H p, S.pair_comm S.V p, hpH, hpV,
        S.pair_H_H, S.pair_V_V, S.pair_H_V, S.pair_V_H]
      ring
    have hdegree (a b : ℝ) : S.pair (a • p + b • d) S.ample = 0 := by
      simp only [S.pair_ample, d, map_add, map_sub, map_smul,
        LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul,
        hpH, hpV, S.pair_H_H, S.pair_V_V, S.pair_H_V, S.pair_V_H]
      ring
    have hx (a : ℝ) (ha : a ^ 2 = 1) : a • p + t • d ∈ S.positiveCone := by
      refine ⟨?_, le_of_eq (hdegree a t).symm⟩
      rw [hsq, ha, one_mul, ht]
      linarith
    have hsum := hadd (1 • p + t • d) (hx 1 (by norm_num))
      ((-1) • p + t • d) (hx (-1) (by norm_num))
    have he : (1 : ℝ) • p + t • d + ((-1 : ℝ) • p + t • d) =
        (0 : ℝ) • p + (2 * t) • d := by
      rw [one_smul, neg_one_smul, zero_smul, zero_add]
      module
    have hnonneg := hsum.1
    rw [he, hsq, zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul, zero_sub] at hnonneg
    nlinarith only [hnonneg, ht, hp]
  · intro hH x hx y hy
    have hxy := S.positiveCone_bezout hH x hx y hy
    refine ⟨?_, ?_⟩
    · simp only [map_add, LinearMap.add_apply, S.pair_comm y x]
      linarith only [hx.1, hy.1, hxy]
    · change 0 ≤ S.pair (x + y) S.ample
      rw [map_add, LinearMap.add_apply]
      exact add_nonneg hx.2 hy.2

end PolarSurface

/-- The exact all-parity arithmetic reserve, with no Weil-form or zero-sum reading in its definition. -/
def criticalDeficitSourceEnergy (r : ℝ) (V : Submodule ℝ realTests) (x : ℝ × ℝ × V) : ℝ :=
  (EF.gammaBracket 0 - 2) * (∫ u, (x.2.2.1 : ℝ → ℝ) u ^ 2) +
    biScaleLevyEnergy (x.2.2.1 : ℝ → ℝ) + 4 * horizonEnergy (x.2.2.1 : ℝ → ℝ) +
    2 * ∫ t in Icc 0 (2 * r),
      ccmPrimeDeficitIncoming t *
        doubleGaugeDerivative (ArchimedeanAnomaly.autocorr (x.2.2.1 : ℝ → ℝ)) t

/-- Effectivity read from ample degree and the exact arithmetic source reserve. -/
def exactArithmeticSourceCone (r : ℝ) (V : Submodule ℝ realTests) : Set (ℝ × ℝ × V) :=
  (scalingSubsurface V).gradedSourceCone (criticalDeficitSourceEnergy r V)

/-- The arithmetic identity represents the defect at every aperture and in every parity. -/
theorem criticalDeficitSourceEnergy_eq_defect {r : ℝ} (hr : 0 ≤ r)
    {V : Submodule ℝ realTests} (hV : V ≤ realTestsAt r) (x : ℝ × ℝ × V) :
    criticalDeficitSourceEnergy r V x = (scalingSubsurface V).defect x x :=
  (scalingSubsurface_defect_eq_levy_add_horizon_add_criticalDeficit hr hV x).symm

/-- The source-defined cone is exactly the positive cone, without a positivity assumption. -/
theorem exactArithmeticSourceCone_eq_positiveCone {r : ℝ} (hr : 0 ≤ r)
    {V : Submodule ℝ realTests} (hV : V ≤ realTestsAt r) :
    exactArithmeticSourceCone r V = (scalingSubsurface V).positiveCone := by
  rw [exactArithmeticSourceCone,
    show criticalDeficitSourceEnergy r V = (fun x => (scalingSubsurface V).defect x x) from
      funext (criticalDeficitSourceEnergy_eq_defect hr hV),
    PolarSurface.gradedSourceCone_defect_eq_positiveCone]

/-- All-aperture source Riemann–Roch on the uncompensated scaling surface, for every real source. -/
theorem exactArithmeticSourceCone_riemannRoch {r : ℝ} (hr : 0 ≤ r)
    {V : Submodule ℝ realTests} (hV : V ≤ realTestsAt r) :
    (scalingSubsurface V).RiemannRochAxiom (exactArithmeticSourceCone r V) := by
  rw [exactArithmeticSourceCone_eq_positiveCone hr hV]
  exact (scalingSubsurface V).positiveCone_riemannRoch

/-- Exact source supply leaves the entire positivity obligation in Bézout. -/
theorem exactArithmeticSourceCone_bezout_iff_hodgeIndex {r : ℝ} (hr : 0 ≤ r)
    {V : Submodule ℝ realTests} (hV : V ≤ realTestsAt r) :
    (scalingSubsurface V).BezoutAxiom (exactArithmeticSourceCone r V) ↔
      (scalingSubsurface V).HodgeIndex := by
  rw [exactArithmeticSourceCone_eq_positiveCone hr hV]
  exact (scalingSubsurface V).hodgeIndex_iff_positiveCone_bezout.symm

/-- Ampleness has the same unresolved sign obligation. -/
theorem exactArithmeticSourceCone_ample_iff_hodgeIndex {r : ℝ} (hr : 0 ≤ r)
    {V : Submodule ℝ realTests} (hV : V ≤ realTestsAt r) :
    (scalingSubsurface V).AmpleAxiom (exactArithmeticSourceCone r V) ↔
      (scalingSubsurface V).HodgeIndex := by
  rw [exactArithmeticSourceCone_eq_positiveCone hr hV]
  exact (scalingSubsurface V).positiveCone_ample_iff_hodgeIndex

/-- The exact remaining Bézout inequality is nonnegativity of the displayed arithmetic reserve. -/
theorem exactArithmeticSourceCone_bezout_iff_source_nonneg {r : ℝ} (hr : 0 ≤ r)
    {V : Submodule ℝ realTests} (hV : V ≤ realTestsAt r) :
    (scalingSubsurface V).BezoutAxiom (exactArithmeticSourceCone r V) ↔
      ∀ x : ℝ × ℝ × V, 0 ≤ criticalDeficitSourceEnergy r V x := by
  rw [exactArithmeticSourceCone_bezout_iff_hodgeIndex hr hV,
    PolarSurface.hodgeIndex_iff_castelnuovoSeveri,
    PolarSurface.castelnuovoSeveri_iff_defect_nonneg]
  simp only [criticalDeficitSourceEnergy_eq_defect hr hV]

/-- The exact all-parity source cone has all-aperture Bézout precisely when RH holds. -/
theorem riemannHypothesis_iff_all_aperture_exactArithmeticSource_bezout :
    RiemannHypothesis ↔ ∀ r : ℝ, 0 < r →
      (scalingSubsurface (realTestsAt r)).BezoutAxiom
        (exactArithmeticSourceCone r (realTestsAt r)) := by
  constructor
  · intro h r hr
    apply (exactArithmeticSourceCone_bezout_iff_hodgeIndex hr.le le_rfl).mpr
    apply (scalingSubsurface_hodgeIndex_iff_weilPair_nonneg _).mpr
    intro f
    exact (WeilSpectral.riemannHypothesis_iff_real_weilPositive.mp h)
      f.1.1 f.1.2.1 f.1.2.2
  · intro h
    apply riemannHypothesis_iff_rightZeros_zeta_eq_empty.mpr
    apply rightZeros_zeta_eq_empty_iff_forall_odd_scalingSubsurface_hodgeIndex.mpr
    intro r hr
    apply (scalingSubsurface_hodgeIndex_iff_weilPair_nonneg _).mpr
    intro f
    have hH := (exactArithmeticSourceCone_bezout_iff_hodgeIndex hr.le le_rfl).mp (h r hr)
    exact (scalingSubsurface_hodgeIndex_iff_weilPair_nonneg _).mp hH ⟨f.1, f.2.1⟩

/-- All-aperture ampleness of this source cone is the same unresolved arithmetic condition. -/
theorem riemannHypothesis_iff_all_aperture_exactArithmeticSource_ample :
    RiemannHypothesis ↔ ∀ r : ℝ, 0 < r →
      (scalingSubsurface (realTestsAt r)).AmpleAxiom
        (exactArithmeticSourceCone r (realTestsAt r)) := by
  rw [riemannHypothesis_iff_all_aperture_exactArithmeticSource_bezout]
  apply forall₂_congr
  intro r hr
  rw [exactArithmeticSourceCone_bezout_iff_hodgeIndex hr.le le_rfl,
    exactArithmeticSourceCone_ample_iff_hodgeIndex hr.le le_rfl]

/-- Exact arithmetic reserves cannot be compressed into finitely many linear source readings. -/
theorem criticalDeficitSourceEnergy_not_finiteLinearReading {r : ℝ} (hr : 0 < r)
    {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (L : realTestsAt r →ₗ[ℝ] V) :
    ¬ ∃ F : V → ℝ, ∀ f : realTestsAt r,
      criticalDeficitSourceEnergy r (realTestsAt r) (0, 0, f) = F (L f) := by
  rintro ⟨F, hF⟩
  obtain ⟨f, hW, hker⟩ := exists_realTestAt_in_ker_weilPair_gt hr (F 0) L
  have hf := hF f
  rw [criticalDeficitSourceEnergy_eq_defect hr.le le_rfl,
    scalingSubsurface_defect_self, hker] at hf
  linarith only [hf, hW]

/-- Every compact real test belongs to a positive support aperture. -/
theorem exists_pos_aperture_of_realTest (f : realTests) :
    ∃ r : ℝ, 0 < r ∧ f ∈ realTestsAt r := by
  obtain ⟨a, ha⟩ := f.2.2.isCompact.isBounded.subset_closedBall (0 : ℝ)
  let r := max a 0 + 1
  have hr : 0 < r := by dsimp only [r]; linarith only [le_max_right a 0]
  have har : a ≤ r := by dsimp only [r]; linarith only [le_max_left a 0]
  refine ⟨r, hr, ?_⟩
  change tsupport f.1 ⊆ Icc (-r) r
  intro u hu
  have hab := ha hu
  rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at hab
  exact abs_le.mp (hab.trans har)

/-- Global arithmetic effectivity obtained by admitting each compact source at a support aperture. -/
def globalExactArithmeticSourceCone : Set ScalingCycle :=
  {x | ∃ r : ℝ, 0 < r ∧ ∃ hf : x.2.2 ∈ realTestsAt r,
    (x.1, x.2.1, ⟨x.2.2, hf⟩) ∈ exactArithmeticSourceCone r (realTestsAt r)}

/-- The aperture presentations glue to the positive cone on the original scaling cycle space. -/
theorem globalExactArithmeticSourceCone_eq_positiveCone :
    globalExactArithmeticSourceCone = scalingSurface.positiveCone := by
  ext x
  constructor
  · rintro ⟨r, hr, hf, hx⟩
    rw [exactArithmeticSourceCone_eq_positiveCone hr.le le_rfl] at hx
    exact hx
  · intro hx
    obtain ⟨r, hr, hf⟩ := exists_pos_aperture_of_realTest x.2.2
    refine ⟨r, hr, hf, ?_⟩
    rw [exactArithmeticSourceCone_eq_positiveCone hr.le le_rfl]
    exact hx

/-- The glued arithmetic-source cone satisfies RR on the complete original scaling surface. -/
theorem globalExactArithmeticSourceCone_riemannRoch :
    scalingSurface.RiemannRochAxiom globalExactArithmeticSourceCone := by
  rw [globalExactArithmeticSourceCone_eq_positiveCone]
  exact scalingSurface.positiveCone_riemannRoch

/-- Global Bézout for the exact arithmetic source presentation is precisely RH. -/
theorem globalExactArithmeticSourceCone_bezout_iff :
    scalingSurface.BezoutAxiom globalExactArithmeticSourceCone ↔ RiemannHypothesis := by
  rw [globalExactArithmeticSourceCone_eq_positiveCone,
    ← scalingSurface.hodgeIndex_iff_positiveCone_bezout, scalingSurface_hodgeIndex_iff]

/-- Global ampleness for the exact arithmetic source presentation is precisely RH. -/
theorem globalExactArithmeticSourceCone_ample_iff :
    scalingSurface.AmpleAxiom globalExactArithmeticSourceCone ↔ RiemannHypothesis := by
  rw [globalExactArithmeticSourceCone_eq_positiveCone,
    scalingSurface.positiveCone_ample_iff_hodgeIndex, scalingSurface_hodgeIndex_iff]

/-- The arithmetic RR set is an additive effective monoid precisely when RH holds. -/
theorem globalExactArithmeticSourceCone_add_closed_iff :
    (∀ x ∈ globalExactArithmeticSourceCone, ∀ y ∈ globalExactArithmeticSourceCone,
      x + y ∈ globalExactArithmeticSourceCone) ↔ RiemannHypothesis := by
  rw [globalExactArithmeticSourceCone_eq_positiveCone,
    scalingSurface.positiveCone_add_closed_iff_hodgeIndex, scalingSurface_hodgeIndex_iff]

/-- The same additive obstruction is already exact at each fixed aperture. -/
theorem exactArithmeticSourceCone_add_closed_iff_hodgeIndex {r : ℝ} (hr : 0 ≤ r)
    {V : Submodule ℝ realTests} (hV : V ≤ realTestsAt r) :
    (∀ x ∈ exactArithmeticSourceCone r V, ∀ y ∈ exactArithmeticSourceCone r V,
      x + y ∈ exactArithmeticSourceCone r V) ↔ (scalingSubsurface V).HodgeIndex := by
  rw [exactArithmeticSourceCone_eq_positiveCone hr hV]
  exact (scalingSubsurface V).positiveCone_add_closed_iff_hodgeIndex

/-- Stability under even one expanding Adams scale carries the full missing sign condition. -/
theorem globalExactArithmeticSourceCone_adams_stable_iff {q : ℝ} (hq : 1 < q) :
    (∀ x ∈ globalExactArithmeticSourceCone, adamsOp q x ∈ globalExactArithmeticSourceCone) ↔
      RiemannHypothesis := by
  constructor
  · intro hstable
    have hdeg : ∀ x ∈ globalExactArithmeticSourceCone,
        0 ≤ scalingSurface.pair x scalingSurface.ample := by
      intro x hx
      rw [globalExactArithmeticSourceCone_eq_positiveCone] at hx
      exact hx.2
    have hnonneg := ((scalingSurface_adams_riemannRoch_iff hq hdeg hstable).mp
      globalExactArithmeticSourceCone_riemannRoch).2
    apply scalingSurface_hodgeIndex_iff.mp
    exact scalingSurface.hodgeIndex_iff_castelnuovoSeveri.mpr
      (scalingSurface.castelnuovoSeveri_iff_defect_nonneg.mpr hnonneg)
  · intro hRH x hx
    have hH := scalingSurface_hodgeIndex_iff.mpr hRH
    have hnn := scalingSurface.castelnuovoSeveri_iff_defect_nonneg.mp
      (scalingSurface.hodgeIndex_iff_castelnuovoSeveri.mp hH)
    rw [globalExactArithmeticSourceCone_eq_positiveCone] at hx ⊢
    have hxsource : x ∈ scalingSurface.sourceCone (fun y => scalingSurface.defect y y) := by
      rw [scalingSurface.sourceCone_eq_positiveCone_of_exact_source hnn (fun _ => rfl)]
      exact hx
    obtain ⟨hxH, hxV, -⟩ := (scalingSurface.mem_sourceCone_iff _ x).mp hxsource
    refine ⟨?_, ?_⟩
    · rw [pair_adamsOp]
      exact hx.1
    · have hq0 : 0 < q := lt_trans zero_lt_one hq
      rw [scalingSurface.pair_ample, pair_adamsOp_H hq0, pair_adamsOp_V hq0]
      positivity

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
