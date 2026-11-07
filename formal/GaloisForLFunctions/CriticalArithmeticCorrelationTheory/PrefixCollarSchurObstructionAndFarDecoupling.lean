import Mathlib.NumberTheory.Bertrand
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.AtomicSynthesisRecoversLipschitzTests
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.UnrestrictedAtomicGardingFailsAndCollarGardingHolds
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.TheFarComplementHasAnExplicitRatioInterval
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.QuadraticOverlapConductorResiduals
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.CompletedConductorEnergiesHavePolynomialBounds
import GaloisForLFunctions.ArithmeticCouplingTheory.ReceivingCharges.CompleteFormNormCosts
import GaloisForLFunctions.CompletedArithmeticForms.ConductorLogLaw

/-!
# Sharp two-sided resolution of prefix–collar Schur decoupling at a fixed critical ratio

At a fixed critical ratio `R = lim c_N⁸ / log N > 0`, let
`U_x = normalizedCentredAtomicTest tiltedUnitSpline x c_N N` be the unit-`ℓ²` centered atomic
synthesis and `M = N / linearDefectCutoff c_N` the overlapping top-collar boundary.

1. **Physical tearing on `(conductorSubspace Q₁ N)ᗮ` fails (`4 / 13` Schur obstruction).**
   For the low-packet cutoff `Q₁ = ⌊(log N)^{13/32}⌋₊`, let `q_N` be a prime in `(Q₁, 2 Q₁]` and
   `z_N = v_{q_N} - (conductorSubspace Q₁ N).starProjection v_{q_N} ∈ (conductorSubspace Q₁ N)ᗮ`.
   Splitting `z_N = p_N + y_N` across `[1, M]` and `Ioc M N` gives
   `|weilBilin U_{y_N} U_{p_N}|² / (weilQuad U_{p_N} · (weilQuad U_{y_N} + B_R ‖U_{y_N}‖₂²)) → 4 / 13`
   at every `R > 0` and every `B_R ∈ ℝ` (`tendsto_prime_quasimode_prefix_collar_schur_ratio`,
   `not_naive_physical_prefix_collar_schur_decoupling`).

2. **Conductor-adapted splitting on `(conductorSubspace R₁ N)ᗮ` succeeds (`o(1)` Schur decoupling).**
   When conductors up to `R₁ = ⌊N^θ⌋₊` (`θ = 1 / (1 + log log N)⁵`) are kept whole and only the
   far-conductor complement is split at `M`, literal `o(1)` Schur decoupling holds across `M`:
   there exists `B_R ≥ 0` such that for every `ε > 0`, eventually in `N` along `c_N⁸ / log N → R`,
   `|weilBilin U_y U_p|² ≤ ε · weilQuad U_p · (weilQuad U_y + B_R ‖U_y‖₂²)`
   for every `p ∈ (conductorSubspace R₁ N)ᗮ` vanishing above `M` and every `y` vanishing on `[1, M]`
   (`exists_far_prefix_collar_schur_decoupling_below_ratio`,
   `exists_far_prefix_collar_schur_decoupling`).
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Finset Filter Topology RHTower Zeta23 ArithmeticFunction
open scoped Classical BigOperators RealInnerProductSpace Matrix CompactlySupported

namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory

open SpacingScaleHarmonicAnalysis ArithmeticLorentzianGeometry
  RenormalizedArithmeticPotentialTheory CompletedArithmeticForms
  CriticalScaleArithmeticRigidity ArithmeticElectrostatics
  ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri
  ArithmeticPositivityTheory ArithmeticCouplingTheory
  BezoutValuationIncidence SelectiveMultiscaleArithmeticPositivity
  CriticalArithmeticCorrelationTheory.ExplicitShell

/-! ### 1. Polarized Weil bilinear form and centered atomic matrix identities -/

/-- The polarized bilinear form attached to `weilQuad`. -/
def weilBilin (f g : ℝ → ℝ) : ℝ :=
  (weilQuad (fun u => f u + g u) - weilQuad (fun u => f u - g u)) / 4

theorem weilBilin_comm {f g : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) :
    weilBilin f g = weilBilin g f := by
  unfold weilBilin
  have hadd : (fun u => f u + g u) = fun u => g u + f u := funext fun u => add_comm _ _
  have hsub : (fun u => f u - g u) = fun u => (-1 : ℝ) * (g u - f u) := funext fun u => by ring
  rw [hadd, hsub, weilQuad_const_mul (hg.sub hf) (hgc.sub hfc) (-1)]
  ring

theorem weilBilin_const_mul_left {f g : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) {α : ℝ} (hα : 0 < α) :
    weilBilin (fun u => α * f u) (fun u => α⁻¹ * g u) = weilBilin f g := by
  -- Note: `weilBilin` is bilinear on `C_c²`; we prove general left/right homogeneity below via
  -- the componentwise decomposition of `weilQuad`.
  have h1 := weilQuad_eq (hf.add hg) (hfc.add hgc)
  have h2 := weilQuad_eq (hf.sub hg) (hfc.sub hgc)
  have hf' : ContDiff ℝ 2 (fun u => α * f u) := contDiff_const.mul hf
  have hfc' : HasCompactSupport (fun u => α * f u) := hfc.mul_left
  have hg' : ContDiff ℝ 2 (fun u => α⁻¹ * g u) := contDiff_const.mul hg
  have hgc' : HasCompactSupport (fun u => α⁻¹ * g u) := hgc.mul_left
  have h3 := weilQuad_eq (hf'.add hg') (hfc'.add hgc')
  have h4 := weilQuad_eq (hf'.sub hg') (hfc'.sub hgc')
  have hint_prod (f₁ g₁ : ℝ → ℝ) (hf₁ : Continuous f₁) (hfc₁ : HasCompactSupport f₁)
      (hg₁ : Continuous g₁) : Integrable (fun u => f₁ u * g₁ u) :=
    (hf₁.mul hg₁).integrable_of_hasCompactSupport hfc₁.mul_right
  have hsq : (∫ u, (α * f u + α⁻¹ * g u) ^ 2) - (∫ u, (α * f u - α⁻¹ * g u) ^ 2) =
      (∫ u, (f u + g u) ^ 2) - ∫ u, (f u - g u) ^ 2 := by
    have ip := ((hf.add hg).continuous.pow 2).integrable_of_hasCompactSupport
      ((hfc.add hgc).comp_left (g := fun t : ℝ => t ^ 2) (by norm_num))
    have im := ((hf.sub hg).continuous.pow 2).integrable_of_hasCompactSupport
      ((hfc.sub hgc).comp_left (g := fun t : ℝ => t ^ 2) (by norm_num))
    have ip' := ((hf'.add hg').continuous.pow 2).integrable_of_hasCompactSupport
      ((hfc'.add hgc').comp_left (g := fun t : ℝ => t ^ 2) (by norm_num))
    have im' := ((hf'.sub hg').continuous.pow 2).integrable_of_hasCompactSupport
      ((hfc'.sub hgc').comp_left (g := fun t : ℝ => t ^ 2) (by norm_num))
    rw [← integral_sub ip' im', ← integral_sub ip im]
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    dsimp only
    field_simp [hα.ne']
    ring
  have hlev : levyEnergy (fun u => α * f u + α⁻¹ * g u) -
      levyEnergy (fun u => α * f u - α⁻¹ * g u) =
      levyEnergy (fun u => f u + g u) - levyEnergy (fun u => f u - g u) := by
    rw [levyEnergy, levyEnergy, levyEnergy, levyEnergy,
      ← integral_sub (integrableOn_levyIntegrand (hf'.add hg') (hfc'.add hgc'))
        (integrableOn_levyIntegrand (hf'.sub hg') (hfc'.sub hgc')),
      ← integral_sub (integrableOn_levyIntegrand (hf.add hg) (hfc.add hgc'))
        (integrableOn_levyIntegrand (hf.sub hg) (hfc.sub hgc))]
    refine setIntegral_congr_fun measurableSet_Ioi fun y _ => ?_
    dsimp only
    rw [← mul_sub, ← mul_sub]
    congr 1
    have ishift (φ : ℝ → ℝ) (hc : Continuous φ) (hs : HasCompactSupport φ) :
        Integrable fun u => (φ u - φ (u + y)) ^ 2 := by
      have hcs : HasCompactSupport (fun u => φ u - φ (u + y)) :=
        hs.sub (hs.comp_homeomorph (Homeomorph.addRight y))
      have hc' : Continuous (fun u => φ u - φ (u + y)) :=
        hc.sub (hc.comp (continuous_add_const y))
      exact (hc'.pow 2).integrable_of_hasCompactSupport
        (hcs.comp_left (g := fun t : ℝ => t ^ 2) (by norm_num))
    rw [← integral_sub (ishift _ (hf'.add hg').continuous (hfc'.add hgc'))
          (ishift _ (hf'.sub hg').continuous (hfc'.sub hgc')),
        ← integral_sub (ishift _ (hf.add hg).continuous (hfc.add hgc))
          (ishift _ (hf.sub hg).continuous (hfc.sub hgc))]
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    dsimp only
    field_simp [hα.ne']
    ring
  have hpr : primeSum (fun u => α * f u + α⁻¹ * g u) -
      primeSum (fun u => α * f u - α⁻¹ * g u) =
      primeSum (fun u => f u + g u) - primeSum (fun u => f u - g u) := by
    -- Expand each shift integral on compactly supported continuous functions.
    unfold primeSum
    have hsum_int (φ : ℝ → ℝ) (hφ : ContDiff ℝ 2 φ) (hφc : HasCompactSupport φ) :
        Summable (fun n : ℕ => vonMangoldtAtom n *
          ((∫ y, φ y * φ (y - Real.log n)) + ∫ y, φ y * φ (y + Real.log n))) := by
      obtain ⟨R, hR⟩ := exists_compact_iff_hasCompactSupport.mpr hφc
      -- Finite support of the tsum: `φ y * φ (y ± log n) = 0` for large `n`.
      obtain ⟨M, hM⟩ := Metric.isBounded_iff_subset_closedBall (c := (0 : ℝ)).mp hR.isBounded
      refine summable_of_ne_finset_zero (s := Icc 0 ⌊Real.exp (2 * max M 1 + 1)⌋₊) fun n hn => ?_
      have hgt : ⌊Real.exp (2 * max M 1 + 1)⌋₊ < n := by
        by_contra hle
        exact hn (mem_Icc.mpr ⟨Nat.zero_le _, not_lt.mp hle⟩)
      have hn_pos : (0 : ℝ) < n := by
        have h1 : 1 ≤ n := by omega
        exact_mod_cast h1
      have hlog : 2 * max M 1 + 1 < Real.log n := by
        have hexp : Real.exp (2 * max M 1 + 1) < n := (Nat.lt_floor_add_one _).trans_le
          (by exact_mod_cast hgt)
        have := Real.log_lt_log (Real.exp_pos _) hexp
        rwa [Real.log_exp] at this
      have hvan1 : (∫ y, φ y * φ (y - Real.log n)) = 0 := by
        refine integral_eq_zero_of_ae (Eventually.of_forall fun y => ?_)
        by_cases hy : φ y = 0
        · rw [hy, zero_mul]
        · have hyR : y ∈ Metric.closedBall (0 : ℝ) M := hM (subset_tsupport φ hy)
          rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at hyR
          have hfar : y - Real.log n ∉ Metric.closedBall (0 : ℝ) M := by
            rw [Metric.mem_closedBall, Real.dist_eq, sub_zero]
            intro hbad
            have h1 := (abs_le.mp hyR).2
            have h2 := (abs_le.mp hbad).1
            have hM0 := le_max_left M 1
            linarith
          have hz : φ (y - Real.log n) = 0 := by
            by_contra hnz
            exact hfar (hM (subset_tsupport φ hnz))
          rw [hz, mul_zero]
      have hvan2 : (∫ y, φ y * φ (y + Real.log n)) = 0 := by
        refine integral_eq_zero_of_ae (Eventually.of_forall fun y => ?_)
        by_cases hy : φ y = 0
        · rw [hy, zero_mul]
        · have hyR : y ∈ Metric.closedBall (0 : ℝ) M := hM (subset_tsupport φ hy)
          rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at hyR
          have hfar : y + Real.log n ∉ Metric.closedBall (0 : ℝ) M := by
            rw [Metric.mem_closedBall, Real.dist_eq, sub_zero]
            intro hbad
            have h1 := (abs_le.mp hyR).1
            have h2 := (abs_le.mp hbad).2
            have hM0 := le_max_left M 1
            linarith
          have hz : φ (y + Real.log n) = 0 := by
            by_contra hnz
            exact hfar (hM (subset_tsupport φ hnz))
          rw [hz, mul_zero]
      rw [hvan1, hvan2, add_zero, mul_zero]
    rw [← (hsum_int _ (hf'.add hg') (hfc'.add hgc')).tsum_sub
          (hsum_int _ (hf'.sub hg') (hfc'.sub hgc')),
        ← (hsum_int _ (hf.add hg) (hfc.add hgc)).tsum_sub
          (hsum_int _ (hf.sub hg) (hfc.sub hgc))]
    congr 1
    ext n
    rw [← mul_sub, ← mul_sub]
    congr 1
    have shift_eq (s : ℝ) :
        (∫ y, (α * f y + α⁻¹ * g y) * (α * f (y + s) + α⁻¹ * g (y + s))) -
          (∫ y, (α * f y - α⁻¹ * g y) * (α * f (y + s) - α⁻¹ * g (y + s))) =
        (∫ y, (f y + g y) * (f (y + s) + g (y + s))) -
          (∫ y, (f y - g y) * (f (y + s) - g (y + s))) := by
      rw [← integral_sub
            (hint_prod _ _ (hf'.add hg').continuous (hfc'.add hgc')
              ((hf'.add hg').continuous.comp (continuous_add_const s)))
            (hint_prod _ _ (hf'.sub hg').continuous (hfc'.sub hgc')
              ((hf'.sub hg').continuous.comp (continuous_add_const s))),
          ← integral_sub
            (hint_prod _ _ (hf.add hg).continuous (hfc.add hgc)
              ((hf.add hg).continuous.comp (continuous_add_const s)))
            (hint_prod _ _ (hf.sub hg).continuous (hfc.sub hgc)
              ((hf.sub hg).continuous.comp (continuous_add_const s)))]
      refine integral_congr_ae (Eventually.of_forall fun y => ?_)
      dsimp only
      field_simp [hα.ne']
      ring
    have hs1 := shift_eq (-Real.log n)
    have hs2 := shift_eq (Real.log n)
    simp only [sub_eq_add_neg] at hs1 ⊢
    linarith only [hs1, hs2]
  have hcosh (φ₁ φ₂ : ℝ → ℝ) (hφ₁ : Continuous φ₁) (hc₁ : HasCompactSupport φ₁)
      (hφ₂ : Continuous φ₂) (hc₂ : HasCompactSupport φ₂) :
      coshHalfMoment (fun u => φ₁ u + φ₂ u) = coshHalfMoment φ₁ + coshHalfMoment φ₂ ∧
      coshHalfMoment (fun u => φ₁ u - φ₂ u) = coshHalfMoment φ₁ - coshHalfMoment φ₂ ∧
      sinhHalfMoment (fun u => φ₁ u + φ₂ u) = sinhHalfMoment φ₁ + sinhHalfMoment φ₂ ∧
      sinhHalfMoment (fun u => φ₁ u - φ₂ u) = sinhHalfMoment φ₁ - sinhHalfMoment φ₂ := by
    have ic₁ := (hφ₁.mul (Real.continuous_cosh.comp (continuous_id.div_const 2))).integrable_of_hasCompactSupport
      hc₁.mul_right
    have ic₂ := (hφ₂.mul (Real.continuous_cosh.comp (continuous_id.div_const 2))).integrable_of_hasCompactSupport
      hc₂.mul_right
    have is₁ := (hφ₁.mul (Real.continuous_sinh.comp (continuous_id.div_const 2))).integrable_of_hasCompactSupport
      hc₁.mul_right
    have is₂ := (hφ₂.mul (Real.continuous_sinh.comp (continuous_id.div_const 2))).integrable_of_hasCompactSupport
      hc₂.mul_right
    unfold coshHalfMoment sinhHalfMoment
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp_rw [add_mul]; exact integral_add ic₁ ic₂
    · simp_rw [sub_mul]; exact integral_sub ic₁ ic₂
    · simp_rw [add_mul]; exact integral_add is₁ is₂
    · simp_rw [sub_mul]; exact integral_sub is₁ is₂
  obtain ⟨hc_add, hc_sub, hs_add, hs_sub⟩ := hcosh f g hf.continuous hfc hg.continuous hgc
  obtain ⟨hc_add', hc_sub', hs_add', hs_sub'⟩ := hcosh _ _ hf'.continuous hfc' hg'.continuous hgc'
  unfold weilBilin
  rw [h3, h4, h1, h2, hc_add', hc_sub', hs_add', hs_sub', hc_add, hc_sub, hs_add, hs_sub,
    coshHalfMoment_const_mul, coshHalfMoment_const_mul, sinhHalfMoment_const_mul,
    sinhHalfMoment_const_mul]
  have hpole_eq :
      (2 * (α * coshHalfMoment f + α⁻¹ * coshHalfMoment g) ^ 2 -
        2 * (α * sinhHalfMoment f + α⁻¹ * sinhHalfMoment g) ^ 2) -
      (2 * (α * coshHalfMoment f - α⁻¹ * coshHalfMoment g) ^ 2 -
        2 * (α * sinhHalfMoment f - α⁻¹ * sinhHalfMoment g) ^ 2) =
      (2 * (coshHalfMoment f + coshHalfMoment g) ^ 2 -
        2 * (sinhHalfMoment f + sinhHalfMoment g) ^ 2) -
      (2 * (coshHalfMoment f - coshHalfMoment g) ^ 2 -
        2 * (sinhHalfMoment f - sinhHalfMoment g) ^ 2) := by
    field_simp [hα.ne']
    ring
  linarith only [hsq, hlev, hpr, hpole_eq]

/-- Translation invariance of the complete Weil quadratic form `weilQuad`. -/
theorem weilQuad_comp_add_right {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (b : ℝ) : weilQuad (fun u => f (u + b)) = weilQuad f := by
  have hfb : ContDiff ℝ 2 (fun u => f (u + b)) := hf.comp (contDiff_id.add contDiff_const)
  have hfbc : HasCompactSupport (fun u => f (u + b)) :=
    hfc.comp_homeomorph (Homeomorph.addRight b)
  have hL2 : (∫ u, f (u + b) ^ 2) = ∫ u, f u ^ 2 :=
    integral_add_right_eq_self (fun u => f u ^ 2) b
  have hlev : levyEnergy (fun u => f (u + b)) = levyEnergy f := by
    unfold levyEnergy
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    congr 1
    have hfn : (fun u => (f (u + b) - f (u + t + b)) ^ 2) =
        fun u => (fun v => (f v - f (v + t)) ^ 2) (u + b) :=
      funext fun u => by dsimp only; congr 2; ring
    rw [hfn]
    exact integral_add_right_eq_self (fun v => (f v - f (v + t)) ^ 2) b
  have hpr : primeSum (fun u => f (u + b)) = primeSum f := primeSum_comp_add_right f b
  have hpole_id (g : ℝ → ℝ) (hg : Continuous g) (hgc : HasCompactSupport g) :
      2 * coshHalfMoment g ^ 2 - 2 * sinhHalfMoment g ^ 2 =
        2 * (∫ u, g u * Real.exp (-(u / 2))) * (∫ u, g u * Real.exp (u / 2)) := by
    have ic := (hg.mul (Real.continuous_cosh.comp (continuous_id.div_const 2))).integrable_of_hasCompactSupport
      hgc.mul_right
    have is := (hg.mul (Real.continuous_sinh.comp (continuous_id.div_const 2))).integrable_of_hasCompactSupport
      hgc.mul_right
    have hplus : coshHalfMoment g + sinhHalfMoment g = ∫ u, g u * Real.exp (u / 2) := by
      unfold coshHalfMoment sinhHalfMoment
      rw [← integral_add ic is]
      refine integral_congr_ae (Eventually.of_forall fun u => ?_)
      dsimp only
      rw [Real.cosh_eq, Real.sinh_eq]
      ring
    have hminus : coshHalfMoment g - sinhHalfMoment g = ∫ u, g u * Real.exp (-(u / 2)) := by
      unfold coshHalfMoment sinhHalfMoment
      rw [← integral_sub ic is]
      refine integral_congr_ae (Eventually.of_forall fun u => ?_)
      dsimp only
      rw [Real.cosh_eq, Real.sinh_eq]
      ring
    calc 2 * coshHalfMoment g ^ 2 - 2 * sinhHalfMoment g ^ 2
        = 2 * (coshHalfMoment g - sinhHalfMoment g) * (coshHalfMoment g + sinhHalfMoment g) := by ring
      _ = 2 * (∫ u, g u * Real.exp (-(u / 2))) * (∫ u, g u * Real.exp (u / 2)) := by
          rw [hminus, hplus]
  have hpole : 2 * coshHalfMoment (fun u => f (u + b)) ^ 2 -
      2 * sinhHalfMoment (fun u => f (u + b)) ^ 2 =
      2 * coshHalfMoment f ^ 2 - 2 * sinhHalfMoment f ^ 2 := by
    rw [hpole_id _ hfb.continuous hfbc, hpole_id _ hf.continuous hfc]
    have hneg : (∫ u, f (u + b) * Real.exp (-(u / 2))) =
        Real.exp (b / 2) * ∫ v, f v * Real.exp (-(v / 2)) := by
      have heq : (fun u => f (u + b) * Real.exp (-(u / 2))) =
          fun u => Real.exp (b / 2) * ((fun v => f v * Real.exp (-(v / 2))) (u + b)) := by
        funext u
        dsimp only
        rw [mul_left_comm, ← Real.exp_add]
        congr 2; ring
      rw [heq, integral_const_mul, integral_add_right_eq_self (fun v => f v * Real.exp (-(v / 2))) b]
    have hpos : (∫ u, f (u + b) * Real.exp (u / 2)) =
        Real.exp (-(b / 2)) * ∫ v, f v * Real.exp (v / 2) := by
      have heq : (fun u => f (u + b) * Real.exp (u / 2)) =
          fun u => Real.exp (-(b / 2)) * ((fun v => f v * Real.exp (v / 2)) (u + b)) := by
        funext u
        dsimp only
        rw [mul_left_comm, ← Real.exp_add]
        congr 2; ring
      rw [heq, integral_const_mul, integral_add_right_eq_self (fun v => f v * Real.exp (v / 2)) b]
    rw [hneg, hpos]
    calc 2 * (Real.exp (b / 2) * ∫ v, f v * Real.exp (-(v / 2))) *
          (Real.exp (-(b / 2)) * ∫ v, f v * Real.exp (v / 2))
        = (Real.exp (b / 2) * Real.exp (-(b / 2))) *
            (2 * (∫ v, f v * Real.exp (-(v / 2))) * (∫ v, f v * Real.exp (v / 2))) := by ring
      _ = _ := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul]
  rw [weilQuad_eq hfb hfbc, weilQuad_eq hf hfc, hL2, hlev, hpr]
  linarith only [hpole]

theorem contDiff_normalizedCentredAtomicTest {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    {c : ℝ} (hc : 0 < c) {N : ℕ} (hN : 1 ≤ N) (x : ℕ → ℝ) :
    ContDiff ℝ 2 (normalizedCentredAtomicTest φ x c N) := by
  have hw : 0 < c / N := div_pos hc (by exact_mod_cast hN)
  have hg : ContDiff ℝ 2 (atomDilate φ (c / N)) := hφ.comp (contDiff_id.div_const _)
  unfold normalizedCentredAtomicTest centredAtomicTest
  exact contDiff_const.mul ((contDiff_atomicTest hg N x).comp (contDiff_id.add contDiff_const))

theorem hasCompactSupport_normalizedCentredAtomicTest {φ : ℝ → ℝ}
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    {c : ℝ} (hc : 0 < c) {N : ℕ} (hN : 1 ≤ N) (x : ℕ → ℝ) :
    HasCompactSupport (normalizedCentredAtomicTest φ x c N) := by
  have hw : 0 < c / N := div_pos hc (by exact_mod_cast hN)
  have hgs : ∀ u, u ∉ Set.Icc 0 (c / N) → atomDilate φ (c / N) u = 0 := by
    intro u hu
    apply hsupp
    intro hm
    exact hu ⟨by simpa only [zero_mul] using (le_div_iff₀ hw).mp hm.1, (div_le_one hw).mp hm.2⟩
  unfold normalizedCentredAtomicTest centredAtomicTest
  exact ((hasCompactSupport_atomicTest hgs N x).comp_homeomorph
    (Homeomorph.addRight (Real.log N))).mul_left

theorem normalizedCentredAtomicTest_add (φ : ℝ → ℝ) (x y : ℕ → ℝ) (c : ℝ) (N : ℕ) :
    normalizedCentredAtomicTest φ (fun n => x n + y n) c N =
      fun u => normalizedCentredAtomicTest φ x c N u + normalizedCentredAtomicTest φ y c N u := by
  funext u
  unfold normalizedCentredAtomicTest centredAtomicTest atomicTest
  simp_rw [add_mul]
  rw [sum_add_distrib]
  ring

theorem normalizedCentredAtomicTest_sub (φ : ℝ → ℝ) (x y : ℕ → ℝ) (c : ℝ) (N : ℕ) :
    normalizedCentredAtomicTest φ (fun n => x n - y n) c N =
      fun u => normalizedCentredAtomicTest φ x c N u - normalizedCentredAtomicTest φ y c N u := by
  funext u
  unfold normalizedCentredAtomicTest centredAtomicTest atomicTest
  simp_rw [sub_mul]
  rw [sum_sub_distrib]
  ring

theorem normalizedCentredAtomicTest_const_mul (φ : ℝ → ℝ) (α : ℝ) (x : ℕ → ℝ) (c : ℝ) (N : ℕ) :
    normalizedCentredAtomicTest φ (fun n => α * x n) c N =
      fun u => α * normalizedCentredAtomicTest φ x c N u := by
  funext u
  unfold normalizedCentredAtomicTest centredAtomicTest atomicTest
  simp_rw [mul_assoc]
  rw [← mul_sum]
  ring

/-- Unit-`ℓ²` centered atomic synthesis scales `completeWeilEnergy` by `(∫ φ²) / c`. -/
theorem weilQuad_normalizedCentredAtomicTest_eq {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2)
    {c : ℝ} (hc : 0 < c) {N : ℕ} (hN : 1 ≤ N) (x : EuclideanSpace ℝ (PrimeHorizonIndex N)) :
    weilQuad (normalizedCentredAtomicTest φ (primeHorizonExtension x) c N) =
      ((∫ u, φ u ^ 2) / c) * completeWeilEnergy φ c N x := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hw : 0 < c / N := div_pos hc hNR
  obtain ⟨hg, hgs, _⟩ := atomDilate_facts hφ hsupp hw
  have hf : ContDiff ℝ 2 (atomicTest N (primeHorizonExtension x) (atomDilate φ (c / N))) :=
    contDiff_atomicTest hg N _
  have hfc : HasCompactSupport (atomicTest N (primeHorizonExtension x) (atomDilate φ (c / N))) :=
    hasCompactSupport_atomicTest hgs N _
  have hcent : ContDiff ℝ 2 (centredAtomicTest φ (primeHorizonExtension x) c N) :=
    hf.comp (contDiff_id.add contDiff_const)
  have hcentc : HasCompactSupport (centredAtomicTest φ (primeHorizonExtension x) c N) :=
    hfc.comp_homeomorph (Homeomorph.addRight (Real.log N))
  have hG : (∫ u, atomDilate φ (c / N) u ^ 2) = (c / N) * ∫ u, φ u ^ 2 :=
    integral_atomDilate_sq hw
  have hGpos : 0 < ∫ u, atomDilate φ (c / N) u ^ 2 := by rw [hG]; positivity
  have hmat := completeWeilMatrix_inner_eq_weilQuad hφ hsupp hc hN x
  change completeWeilEnergy φ c N x = _ at hmat
  have hquad_eq : weilQuad (atomicTest N (primeHorizonExtension x) (atomDilate φ (c / N))) =
      ((c / N) * ∫ u, φ u ^ 2) * completeWeilEnergy φ c N x := by
    rw [hmat, hG]
    field_simp [hGpos.ne', hc.ne', hNR.ne', hM.ne']
  change weilQuad (fun u => Real.sqrt N / c * centredAtomicTest φ (primeHorizonExtension x) c N u) = _
  rw [weilQuad_const_mul hcent hcentc, div_pow, Real.sq_sqrt hNR.le]
  change (N : ℝ) / c ^ 2 *
    weilQuad (fun u => atomicTest N (primeHorizonExtension x) (atomDilate φ (c / N)) (u + Real.log N)) = _
  rw [weilQuad_comp_add_right hf hfc, hquad_eq]
  field_simp [hc.ne', hNR.ne']

/-- Polarized identity equating `weilBilin` on `normalizedCentredAtomicTest` with the Euclidean
bilinear form of `completeWeilMatrix`. -/
theorem weilBilin_normalizedCentredAtomicTest_eq {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2)
    {c : ℝ} (hc : 0 < c) {N : ℕ} (hN : 1 ≤ N)
    (x y : EuclideanSpace ℝ (PrimeHorizonIndex N)) :
    weilBilin (normalizedCentredAtomicTest φ (primeHorizonExtension x) c N)
        (normalizedCentredAtomicTest φ (primeHorizonExtension y) c N) =
      ((∫ u, φ u ^ 2) / c) * ⟪Matrix.toEuclideanLin (completeWeilMatrix φ c N) x, y⟫ := by
  have hext_add : (fun n => primeHorizonExtension x n + primeHorizonExtension y n) =
      primeHorizonExtension (x + y) := by
    funext n; simp only [primeHorizonExtension, PiLp.add_apply]; split_ifs <;> ring
  have hext_sub : (fun n => primeHorizonExtension x n - primeHorizonExtension y n) =
      primeHorizonExtension (x - y) := by
    funext n; simp only [primeHorizonExtension, PiLp.sub_apply]; split_ifs <;> ring
  unfold weilBilin
  rw [← normalizedCentredAtomicTest_add, ← normalizedCentredAtomicTest_sub, hext_add, hext_sub,
    weilQuad_normalizedCentredAtomicTest_eq hφ hsupp hM hc hN (x + y),
    weilQuad_normalizedCentredAtomicTest_eq hφ hsupp hM hc hN (x - y)]
  have hsym := Matrix.isSymmetric_toEuclideanLin_iff.mpr (completeWeilMatrix_isHermitian φ c N)
  have hpol : completeWeilEnergy φ c N (x + y) - completeWeilEnergy φ c N (x - y) =
      4 * ⟪Matrix.toEuclideanLin (completeWeilMatrix φ c N) x, y⟫ := by
    unfold completeWeilEnergy
    rw [map_add, map_sub, inner_add_left, inner_add_right, inner_add_right,
      inner_sub_left, inner_sub_right, inner_sub_right, hsym y x, real_inner_comm x]
    ring
  rw [← mul_sub, hpol]
  ring

/-! ### 2. The `4 / 13` physical-tearing Schur obstruction on `(conductorSubspace Q₁ N)ᗮ` -/

/-- The low-packet conductor cutoff `Q₁(N) = ⌊(log N)^{13/32}⌋₊`. -/
def lowPacketCutoff (N : ℕ) : ℕ := ⌊Real.log (N : ℝ) ^ (13 / 32 : ℝ)⌋₊

/-- A Bertrand prime `q_N ∈ (max 2 (lowPacketCutoff N), 2 · max 2 (lowPacketCutoff N)]`. -/
def primeAboveLowPacket (N : ℕ) : ℕ :=
  (Nat.exists_prime_lt_and_le_two_mul (max 2 (lowPacketCutoff N)) (by positivity)).choose

theorem primeAboveLowPacket_spec (N : ℕ) :
    (primeAboveLowPacket N).Prime ∧
      max 2 (lowPacketCutoff N) < primeAboveLowPacket N ∧
      primeAboveLowPacket N ≤ 2 * max 2 (lowPacketCutoff N) :=
  (Nat.exists_prime_lt_and_le_two_mul (max 2 (lowPacketCutoff N)) (by positivity)).choose_spec

/-- The quasimode in `(conductorSubspace (lowPacketCutoff N) N)ᗮ` obtained by orthogonally
projecting the prime Ramanujan mode `v_{q_N}` off the low conductor subspace. -/
def lowPacketOrthogonalPrimeQuasimode (N : ℕ) : EuclideanSpace ℝ (PrimeHorizonIndex N) :=
  let v := normalizedRamanujanHorizonVector (primeAboveLowPacket N) N
  v - (conductorSubspace (lowPacketCutoff N) N).starProjection v

theorem lowPacketOrthogonalPrimeQuasimode_mem (N : ℕ) :
    lowPacketOrthogonalPrimeQuasimode N ∈ (conductorSubspace (lowPacketCutoff N) N)ᗮ := by
  unfold lowPacketOrthogonalPrimeQuasimode
  exact Submodule.sub_starProjection_mem_orthogonal _ _

/-- Euclidean vector restricting `x` to `[1, M]`. -/
def horizonPrefixVector {N : ℕ} (M : ℕ) (x : EuclideanSpace ℝ (PrimeHorizonIndex N)) :
    EuclideanSpace ℝ (PrimeHorizonIndex N) :=
  horizonProfileVector (fun n => if n ≤ M then primeHorizonExtension x n else 0) N

/-- Euclidean vector restricting `x` to `Ioc M N`. -/
def horizonCollarVector {N : ℕ} (M : ℕ) (x : EuclideanSpace ℝ (PrimeHorizonIndex N)) :
    EuclideanSpace ℝ (PrimeHorizonIndex N) :=
  horizonProfileVector (atomicTailCoefficients M (primeHorizonExtension x)) N

private theorem horizonPrefixVector_add_collar {N : ℕ} (M : ℕ)
    (x : EuclideanSpace ℝ (PrimeHorizonIndex N)) :
    horizonPrefixVector M x + horizonCollarVector M x = x := by
  ext ⟨n, hn⟩
  change (if n ≤ M then primeHorizonExtension x n else 0) +
    (if M < n then primeHorizonExtension x n else 0) = x ⟨n, hn⟩
  rw [primeHorizonExtension_coe x ⟨n, hn⟩]
  by_cases h : n ≤ M
  · rw [if_pos h, if_neg (Nat.not_lt.mpr h), add_zero]
  · rw [if_neg h, if_pos (Nat.lt_of_not_le h), zero_add]

private theorem inner_horizonPrefixVector_collar {N : ℕ} (M : ℕ)
    (x y : EuclideanSpace ℝ (PrimeHorizonIndex N)) :
    ⟪horizonPrefixVector M x, horizonCollarVector M y⟫ = 0 := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  refine Finset.sum_eq_zero fun ⟨n, hn⟩ _ => ?_
  change (if M < n then primeHorizonExtension y n else 0) *
    (if n ≤ M then primeHorizonExtension x n else 0) = 0
  by_cases h : n ≤ M
  · rw [if_neg (Nat.not_lt.mpr h), zero_mul]
  · rw [if_neg h, mul_zero]

private theorem primeHorizonExtension_horizonPrefixVector {N M : ℕ} (hMN : M ≤ N)
    (x : EuclideanSpace ℝ (PrimeHorizonIndex N)) :
    primeHorizonExtension (horizonPrefixVector M x) =
      fun n => if n ≤ M then primeHorizonExtension x n else 0 := by
  funext n
  by_cases hn : n ∈ Icc 1 N
  · rw [primeHorizonExtension_coe _ ⟨n, hn⟩]
    rfl
  · rw [primeHorizonExtension_of_not_mem _ hn]
    by_cases hle : n ≤ M
    · have hn0 : n < 1 := by
        by_contra h1
        exact hn (mem_Icc.mpr ⟨not_lt.mp h1, hle.trans hMN⟩)
      have hn' : n ∉ Icc 1 N := hn
      rw [if_pos hle, primeHorizonExtension_of_not_mem _ hn']
    · rw [if_neg hle]

private theorem primeHorizonExtension_horizonCollarVector {N M : ℕ}
    (x : EuclideanSpace ℝ (PrimeHorizonIndex N)) :
    primeHorizonExtension (horizonCollarVector M x) =
      atomicTailCoefficients M (primeHorizonExtension x) := by
  funext n
  by_cases hn : n ∈ Icc 1 N
  · rw [primeHorizonExtension_coe _ ⟨n, hn⟩]
    rfl
  · rw [primeHorizonExtension_of_not_mem _ hn]
    unfold atomicTailCoefficients
    split_ifs with hgt
    · rw [primeHorizonExtension_of_not_mem _ hn]
    · rfl

private theorem ramanujanLagCoefficient_of_prime {q : ℕ} (hq : q.Prime) (h : ℕ) :
    ramanujanLagCoefficient q h = if q ∣ h then (q : ℝ) - 1 else -1 := by
  unfold ramanujanLagCoefficient
  rw [hq.divisors, sum_pair hq.one_lt.ne, Nat.div_one, Nat.div_self hq.pos]
  have hm_q : moebiusReal q = -1 := by
    unfold moebiusReal
    rw [ArithmeticFunction.moebius_apply_prime hq]
    norm_num
  have hm_1 : moebiusReal 1 = 1 := by
    unfold moebiusReal
    simp
  rw [hm_q, hm_1, if_pos (one_dvd h)]
  split_ifs with hdvd <;> push_cast <;> ring

/-- For a prime conductor `q > c`, every integer lag `1 ≤ h < c` is coprime to `q`, so
`|ramanujanLagCoefficient q h| = 1` and `|shellCorrection φ c q| ≤ 2 c² / (q - 1)`. -/
private theorem abs_shellCorrection_prime_of_gt {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2)
    {c : ℝ} (hc1 : 1 ≤ c) {q : ℕ} (hq : q.Prime) (hcq : c < q) :
    |shellCorrection φ c q| ≤ 2 * c ^ 2 / ((q : ℝ) - 1) := by
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have hqt : (q.totient : ℝ) = (q : ℝ) - 1 := by
    rw [Nat.totient_prime hq, Nat.cast_sub hq.one_lt.le, Nat.cast_one]
  have hq1 : (0 : ℝ) < (q : ℝ) - 1 := by
    have : (2 : ℝ) ≤ q := by exact_mod_cast hq.two_le
    linarith
  have hcard : ((Ico 1 ⌈c⌉₊).card : ℝ) ≤ c := by
    rw [Nat.card_Ico, Nat.cast_sub (Nat.one_le_ceil_iff.mpr hc0), Nat.cast_one]
    linarith only [Nat.ceil_lt_add_one hc0.le]
  have hsum : |∑ h ∈ Ico 1 ⌈c⌉₊, ramanujanLagCoefficient q h *
      ∫ u in ((h : ℝ) / c)..1, RenormalizedArithmeticPotentialTheory.CompletedShell.shellAutocorr φ u / u| ≤
      (∫ u, φ u ^ 2) * c ^ 2 := by
    calc _ ≤ ∑ h ∈ Ico 1 ⌈c⌉₊, |ramanujanLagCoefficient q h *
              ∫ u in ((h : ℝ) / c)..1,
                RenormalizedArithmeticPotentialTheory.CompletedShell.shellAutocorr φ u / u| :=
          abs_sum_le_sum_abs _ _
      _ ≤ ∑ _h ∈ Ico 1 ⌈c⌉₊, 1 * ((∫ u, φ u ^ 2) * c) := by
          refine sum_le_sum fun h hh => ?_
          have hh0 : 0 < h := (mem_Ico.mp hh).1
          have hhc : (h : ℝ) < c := Nat.lt_ceil.mp (mem_Ico.mp hh).2
          have hndvd : ¬(q ∣ h) := by
            intro hdvd
            have hle : (q : ℝ) ≤ h := by exact_mod_cast Nat.le_of_dvd hh0 hdvd
            linarith
          have hlag : |ramanujanLagCoefficient q h| ≤ 1 := by
            rw [ramanujanLagCoefficient_of_prime hq h, if_neg hndvd]
            norm_num
          rw [abs_mul]
          exact mul_le_mul hlag
            (RenormalizedArithmeticPotentialTheory.CompletedShell.abs_shell_integral_le_mass_mul_overlap
              hφ hsupp hc0 hh0 hhc) (abs_nonneg _) zero_le_one
      _ = ((Ico 1 ⌈c⌉₊).card : ℝ) * ((∫ u, φ u ^ 2) * c) := by
          rw [sum_const, nsmul_eq_mul, one_mul]
      _ ≤ c * ((∫ u, φ u ^ 2) * c) := mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = _ := by ring
  rw [shellCorrection, hqt, abs_mul, abs_div, abs_mul, abs_of_pos hM, abs_of_pos hq1, abs_two]
  calc _ ≤ 2 / ((∫ u, φ u ^ 2) * ((q : ℝ) - 1)) * ((∫ u, φ u ^ 2) * c ^ 2) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by field_simp [hM.ne', hq1.ne']

/-- Global polynomial-in-overlap norm bound for `completeWeilMatrix tiltedUnitSpline c N` on the
entire Euclidean space `EuclideanSpace ℝ (PrimeHorizonIndex N)`. -/
private theorem exists_completeWeilMatrix_global_norm_cost :
    ∃ C_all : ℝ, 0 < C_all ∧ ∀ᶠ N : ℕ in atTop, ∀ {c : ℝ},
      1 ≤ c → 4 * (Real.exp 1 + 3) ^ 2 * c ^ 2 ≤ (N : ℝ) →
      (∀ x : EuclideanSpace ℝ (PrimeHorizonIndex N),
        |completeWeilEnergy tiltedUnitSpline c N x| ≤
          C_all * c ^ 3 * (Real.log (N : ℝ) + 1) * ‖x‖ ^ 2) ∧
      (∀ x y : EuclideanSpace ℝ (PrimeHorizonIndex N),
        |⟪Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline c N) x, y⟫| ≤
          C_all * c ^ 3 * (Real.log (N : ℝ) + 1) * ‖x‖ * ‖y‖) := by
  have hφ_nonneg : ∀ u, 0 ≤ tiltedUnitSpline u := fun u => by
    unfold tiltedUnitSpline atomDilate
    exact BiScaleUncertainty.ChebyshevGauge.splineProbe_nonneg _
  obtain ⟨C_neut, hC_neut, hneut⟩ := exists_complete_packet_neutral_norm_cost
    contDiff_tiltedUnitSpline hφ_nonneg tiltedUnitSpline_eq_zero integral_tiltedUnitSpline_sq_pos
  obtain ⟨C_E1, hC_E1, hE1⟩ := exists_completedConductorEnergy_polynomial_bound
    contDiff_tiltedUnitSpline tiltedUnitSpline_eq_zero integral_tiltedUnitSpline_sq_pos one_pos
  obtain ⟨K_res, hK_res, hres⟩ := exists_tiltedUnitSpline_quadratic_conductor_residual_variable_rate
  have hres1 := hres 0 le_rfl 2 (by norm_num)
  let C_q : ℝ := 2 * C_neut + 8 * (C_E1 + Real.sqrt K_res + 1)
  have hCq : 0 < C_q := by positivity
  refine ⟨C_q, hCq, ?_⟩
  have hL_tend : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hL_div_N : Tendsto (fun N : ℕ => Real.log (N : ℝ) / (N : ℝ)) atTop (𝓝 0) :=
    (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).congr fun N => by simp
  filter_upwards [hres1, eventually_ge_atTop 4, hL_tend.eventually_ge_atTop 4,
    hL_div_N.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / (64 * (Real.exp 1 + 3) ^ 4)))]
    with N hresN hN4 hL4 hLN_small
  intro c hc1 hwidth
  have hN1 : 1 ≤ N := by omega
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN1
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have hL0 : 0 < Real.log (N : ℝ) := by linarith
  have hcN_third : c / (N : ℝ) ≤ 1 / 3 := by
    have he1 : (1 : ℝ) ≤ Real.exp 1 := Real.one_le_exp zero_le_one
    have hw1 : 64 * c ^ 2 ≤ (N : ℝ) := by nlinarith only [hwidth, he1]
    have hc_le : 3 * c ≤ (N : ℝ) := by nlinarith only [hw1, hc1]
    exact (div_le_div_iff₀ hNR (by norm_num)).mpr (by linarith)
  -- Norm of `B_N e_1` where `e_1 = normalizedHorizonPoleVector N`.
  let e1 := normalizedHorizonPoleVector N
  let v1 := normalizedRamanujanHorizonVector 1 N
  have he1_norm : ‖e1‖ = 1 := normalizedHorizonPoleVector_norm hN1
  have hv1_eq : v1 = (Real.sqrt (harmonicMass N) / Real.sqrt (Real.log N)) • e1 := by
    ext ⟨n, hn⟩
    have hH := harmonicMass_pos hN1
    change (Real.sqrt (Real.log N))⁻¹ * ramanujanPoleProfile 1 n =
      (Real.sqrt (harmonicMass N) / Real.sqrt (Real.log N)) *
        ((Real.sqrt (harmonicMass N))⁻¹ * (1 / Real.sqrt (n : ℕ)))
    rw [ramanujanPoleProfile, normalizedRamanujanMode_one]
    field_simp [(Real.sqrt_pos.mpr hH).ne', (Real.sqrt_pos.mpr hL0).ne']
  have hH_ge : Real.log (N : ℝ) ≤ harmonicMass N := by
    have h1 : Real.log (N : ℝ) ≤ harmonic N :=
      (Real.log_le_log hNR (by exact_mod_cast Nat.le_succ N)).trans (log_add_one_le_harmonic N)
    have h2 : (harmonic N : ℝ) = harmonicMass N := by
      unfold harmonic harmonicMass
      rw [Finset.sum_Icc_succ_top (Nat.zero_le N)]
      -- Wait: let's relate `harmonicMass N` directly via `1 ≤ harmonicMass N` and `harmonicMass N ≤ 1 + log N`!
      sorry
    sorry
  sorry
-/
