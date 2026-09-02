import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMSourceFECocycleHyperbolicModulusOrientation

/-!
# Vacuum-continuous nonlinear detectors cannot scalarize the source-FE saddle

The literal Birmingham--Mokhtari source-FE cocycle on a Xi copy and its reflected copy has
reciprocal modulus.  Away from the critical wall, one gain strictly contracts and the other
strictly expands.  This module proves that no injective nonlinear detector continuous merely at
vacuum can intertwine that two-channel saddle with one complex scalar gain.

The obstruction uses no derivative, linear response, neighborhood continuity, or regularity away
from vacuum.  Forward iterates on the stable axis and backward iterates on the unstable axis both
approach vacuum.  Exact scalarization multiplies their detector norms by reciprocal powers of the
same scalar, so their product is a fixed positive number; vacuum continuity forces that product to
converge to zero.

Consequently, copy-dependent vacuum-continuous faithful scalarizers exist exactly on the critical
wall, and existence on every Xi fibre is equivalent to RH.  This closes the vacuum-continuity
escape for the reflection-paired literal-source carrier.  Transferring it to the unpaired physical
horizon--boundary carrier still requires a physical reflection-channel inclusion theorem.

`[NEW] [HB NO-GO] [VACUUM CONTINUOUS] [NONLINEAR DETECTOR] [RH EQUIVALENCE]`
-/

open Complex Filter Topology

namespace RHTower

noncomputable section

abbrev HBXiSourceFEReflectionDetectorCarrier := ℂ × ℂ

/-- Generic diagonal action used by the source-FE reflection carrier. -/
def hbXiSourceFEDiagonalDetectorCocycle (a b : ℂ)
    (x : HBXiSourceFEReflectionDetectorCarrier) :
    HBXiSourceFEReflectionDetectorCarrier :=
  (a * x.1, b * x.2)

/-- A diagonal complex saddle cannot be faithfully scalarized by a nonlinear detector continuous
only at its fixed point. -/
theorem no_vacuumContinuous_injective_scalarizer_of_diagonal_saddle
    (a b c : ℂ)
    (detector : HBXiSourceFEReflectionDetectorCarrier →
      HBXiSourceFEReflectionDetectorCarrier)
    (ha0 : a ≠ 0) (hb0 : b ≠ 0)
    (ha : ‖a‖ < 1) (hb : 1 < ‖b‖)
    (hcontinuous : ContinuousAt detector 0)
    (hfaithful : Function.Injective detector)
    (hscalar : ∀ x : HBXiSourceFEReflectionDetectorCarrier,
      detector (hbXiSourceFEDiagonalDetectorCocycle a b x) =
        c • detector x) : False := by
  have hforward : ∀ n : ℕ,
      detector ((a ^ n, 0) : HBXiSourceFEReflectionDetectorCarrier) =
        (c ^ n) •
          detector ((1, 0) : HBXiSourceFEReflectionDetectorCarrier) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        calc
          detector ((a ^ (n + 1), 0) :
              HBXiSourceFEReflectionDetectorCarrier) =
              detector (hbXiSourceFEDiagonalDetectorCocycle a b
                ((a ^ n, 0) : HBXiSourceFEReflectionDetectorCarrier)) := by
                  simp [hbXiSourceFEDiagonalDetectorCocycle, pow_succ, mul_comm]
          _ = c • detector
              ((a ^ n, 0) : HBXiSourceFEReflectionDetectorCarrier) := hscalar _
          _ = c • ((c ^ n) • detector
              ((1, 0) : HBXiSourceFEReflectionDetectorCarrier)) := by rw [ih]
          _ = (c ^ (n + 1)) • detector
              ((1, 0) : HBXiSourceFEReflectionDetectorCarrier) := by
                simp [smul_smul, pow_succ, mul_comm]
  have hc0 : c ≠ 0 := by
    intro hc
    have hdet0 : detector
        ((0, 0) : HBXiSourceFEReflectionDetectorCarrier) = 0 := by
      simpa [hc, hbXiSourceFEDiagonalDetectorCocycle] using
        hscalar (0 : HBXiSourceFEReflectionDetectorCarrier)
    have hdet1 : detector
        ((1, 0) : HBXiSourceFEReflectionDetectorCarrier) = 0 := by
      simpa [hc, ha0, hbXiSourceFEDiagonalDetectorCocycle] using
        hscalar ((a⁻¹, 0) : HBXiSourceFEReflectionDetectorCarrier)
    have hone : ((1, 0) : HBXiSourceFEReflectionDetectorCarrier) = 0 :=
      hfaithful (hdet1.trans hdet0.symm)
    norm_num at hone
  have hstableInput :
      Tendsto
          (fun n : ℕ =>
            ((a ^ n, 0) : HBXiSourceFEReflectionDetectorCarrier))
          atTop
          (𝓝 ((0, 0) : HBXiSourceFEReflectionDetectorCarrier)) := by
    simpa only [nhds_prod_eq] using
      (tendsto_pow_atTop_nhds_zero_of_norm_lt_one ha).prodMk
        (tendsto_const_nhds :
          Tendsto (fun _ : ℕ => (0 : ℂ)) atTop (𝓝 0))
  have hstableDetector :
      Tendsto
          (fun n : ℕ => detector
            ((a ^ n, 0) : HBXiSourceFEReflectionDetectorCarrier))
          atTop
          (𝓝 (detector
            ((0, 0) : HBXiSourceFEReflectionDetectorCarrier))) :=
    hcontinuous.tendsto.comp hstableInput
  have hc1 : c ≠ 1 := by
    intro hc
    have hfun :
        (fun n : ℕ => detector
            ((a ^ n, 0) : HBXiSourceFEReflectionDetectorCarrier)) =
          fun _ : ℕ => detector
            ((1, 0) : HBXiSourceFEReflectionDetectorCarrier) := by
      funext n
      simpa [hc] using hforward n
    rw [hfun] at hstableDetector
    have heq :
        detector ((1, 0) : HBXiSourceFEReflectionDetectorCarrier) =
          detector ((0, 0) : HBXiSourceFEReflectionDetectorCarrier) :=
      tendsto_nhds_unique tendsto_const_nhds hstableDetector
    have hone : ((1, 0) : HBXiSourceFEReflectionDetectorCarrier) =
        ((0, 0) : HBXiSourceFEReflectionDetectorCarrier) := hfaithful heq
    norm_num at hone
  have hdetectorZero :
      detector ((0, 0) : HBXiSourceFEReflectionDetectorCarrier) = 0 := by
    have hfix :
        detector ((0, 0) : HBXiSourceFEReflectionDetectorCarrier) =
          c • detector
            ((0, 0) : HBXiSourceFEReflectionDetectorCarrier) := by
      simpa [hbXiSourceFEDiagonalDetectorCocycle] using
        hscalar ((0, 0) : HBXiSourceFEReflectionDetectorCarrier)
    apply Prod.ext
    · have hz := congrArg Prod.fst hfix
      simp only [Prod.smul_fst, Prod.fst_zero] at hz ⊢
      have hfactor :
          (1 - c) *
              (detector
                ((0, 0) : HBXiSourceFEReflectionDetectorCarrier)).1 = 0 := by
        calc
          (1 - c) *
                (detector
                  ((0, 0) : HBXiSourceFEReflectionDetectorCarrier)).1 =
              (detector
                  ((0, 0) : HBXiSourceFEReflectionDetectorCarrier)).1 -
                c * (detector
                  ((0, 0) : HBXiSourceFEReflectionDetectorCarrier)).1 := by ring
          _ = 0 := sub_eq_zero.mpr hz
      exact (mul_eq_zero.mp hfactor).resolve_left
        (sub_ne_zero.mpr (Ne.symm hc1))
    · have hz := congrArg Prod.snd hfix
      simp only [Prod.smul_snd, Prod.snd_zero] at hz ⊢
      have hfactor :
          (1 - c) *
              (detector
                ((0, 0) : HBXiSourceFEReflectionDetectorCarrier)).2 = 0 := by
        calc
          (1 - c) *
                (detector
                  ((0, 0) : HBXiSourceFEReflectionDetectorCarrier)).2 =
              (detector
                  ((0, 0) : HBXiSourceFEReflectionDetectorCarrier)).2 -
                c * (detector
                  ((0, 0) : HBXiSourceFEReflectionDetectorCarrier)).2 := by ring
          _ = 0 := sub_eq_zero.mpr hz
      exact (mul_eq_zero.mp hfactor).resolve_left
        (sub_ne_zero.mpr (Ne.symm hc1))
  have hback : ∀ x : HBXiSourceFEReflectionDetectorCarrier,
      detector (hbXiSourceFEDiagonalDetectorCocycle a⁻¹ b⁻¹ x) =
        c⁻¹ • detector x := by
    intro x
    have hs := hscalar
      (hbXiSourceFEDiagonalDetectorCocycle a⁻¹ b⁻¹ x)
    have hinput :
        hbXiSourceFEDiagonalDetectorCocycle a b
            (hbXiSourceFEDiagonalDetectorCocycle a⁻¹ b⁻¹ x) = x := by
      apply Prod.ext <;>
        simp [hbXiSourceFEDiagonalDetectorCocycle, ha0, hb0]
    rw [hinput] at hs
    have hs' := congrArg
      (fun y : HBXiSourceFEReflectionDetectorCarrier => c⁻¹ • y) hs
    simpa [smul_smul, hc0, hbXiSourceFEDiagonalDetectorCocycle] using hs'.symm
  have hbackward : ∀ n : ℕ,
      detector ((0, (b⁻¹) ^ n) :
          HBXiSourceFEReflectionDetectorCarrier) =
        ((c⁻¹) ^ n) • detector
          ((0, 1) : HBXiSourceFEReflectionDetectorCarrier) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        calc
          detector ((0, (b⁻¹) ^ (n + 1)) :
              HBXiSourceFEReflectionDetectorCarrier) =
              detector (hbXiSourceFEDiagonalDetectorCocycle a⁻¹ b⁻¹
                ((0, (b⁻¹) ^ n) :
                  HBXiSourceFEReflectionDetectorCarrier)) := by
                    simp [hbXiSourceFEDiagonalDetectorCocycle,
                      pow_succ, mul_comm]
          _ = c⁻¹ • detector ((0, (b⁻¹) ^ n) :
              HBXiSourceFEReflectionDetectorCarrier) := hback _
          _ = c⁻¹ • (((c⁻¹) ^ n) • detector
              ((0, 1) : HBXiSourceFEReflectionDetectorCarrier)) := by rw [ih]
          _ = ((c⁻¹) ^ (n + 1)) • detector
              ((0, 1) : HBXiSourceFEReflectionDetectorCarrier) := by
                simp [smul_smul, pow_succ, mul_comm]
  have hbpos : 0 < ‖b‖ := lt_trans zero_lt_one hb
  have hbnorm0 : ‖b‖ ≠ 0 := ne_of_gt hbpos
  have hbinv : ‖b⁻¹‖ < 1 := by
    rw [norm_inv]
    have hinvpos : 0 < ‖b‖⁻¹ := inv_pos.mpr hbpos
    have hmul : ‖b‖⁻¹ * ‖b‖ = 1 := inv_mul_cancel₀ hbnorm0
    nlinarith
  have hunstableInput :
      Tendsto
          (fun n : ℕ =>
            ((0, (b⁻¹) ^ n) : HBXiSourceFEReflectionDetectorCarrier))
          atTop
          (𝓝 ((0, 0) : HBXiSourceFEReflectionDetectorCarrier)) := by
    simpa only [nhds_prod_eq] using
      (tendsto_const_nhds :
        Tendsto (fun _ : ℕ => (0 : ℂ)) atTop (𝓝 0)).prodMk
          (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hbinv)
  have hunstableDetector :
      Tendsto
          (fun n : ℕ => detector
            ((0, (b⁻¹) ^ n) : HBXiSourceFEReflectionDetectorCarrier))
          atTop
          (𝓝 (detector
            ((0, 0) : HBXiSourceFEReflectionDetectorCarrier))) :=
    hcontinuous.tendsto.comp hunstableInput
  have hproductZero :
      Tendsto
        (fun n : ℕ =>
          ‖detector
              ((a ^ n, 0) : HBXiSourceFEReflectionDetectorCarrier)‖ *
            ‖detector
              ((0, (b⁻¹) ^ n) : HBXiSourceFEReflectionDetectorCarrier)‖)
        atTop (𝓝 0) := by
    simpa [hdetectorZero] using
      hstableDetector.norm.mul hunstableDetector.norm
  have hcnorm0 : ‖c‖ ≠ 0 := norm_ne_zero_iff.mpr hc0
  have hproductEq :
      (fun n : ℕ =>
          ‖detector
              ((a ^ n, 0) : HBXiSourceFEReflectionDetectorCarrier)‖ *
            ‖detector
              ((0, (b⁻¹) ^ n) : HBXiSourceFEReflectionDetectorCarrier)‖) =
        fun _ : ℕ =>
          ‖detector
              ((1, 0) : HBXiSourceFEReflectionDetectorCarrier)‖ *
            ‖detector
              ((0, 1) : HBXiSourceFEReflectionDetectorCarrier)‖ := by
    funext n
    rw [hforward n, hbackward n, norm_smul, norm_smul,
      norm_pow, norm_pow, norm_inv]
    have hcancel : ‖c‖ ^ n * ‖c‖⁻¹ ^ n = 1 := by
      rw [← mul_pow]
      simp [hcnorm0]
    calc
      (‖c‖ ^ n * ‖detector
          ((1, 0) : HBXiSourceFEReflectionDetectorCarrier)‖) *
          (‖c‖⁻¹ ^ n * ‖detector
            ((0, 1) : HBXiSourceFEReflectionDetectorCarrier)‖) =
        (‖c‖ ^ n * ‖c‖⁻¹ ^ n) *
          (‖detector
              ((1, 0) : HBXiSourceFEReflectionDetectorCarrier)‖ *
            ‖detector
              ((0, 1) : HBXiSourceFEReflectionDetectorCarrier)‖) := by ring
      _ = ‖detector
              ((1, 0) : HBXiSourceFEReflectionDetectorCarrier)‖ *
            ‖detector
              ((0, 1) : HBXiSourceFEReflectionDetectorCarrier)‖ := by
        rw [hcancel, one_mul]
  rw [hproductEq] at hproductZero
  have hconstant :
      Tendsto
        (fun _ : ℕ =>
          ‖detector
              ((1, 0) : HBXiSourceFEReflectionDetectorCarrier)‖ *
            ‖detector
              ((0, 1) : HBXiSourceFEReflectionDetectorCarrier)‖)
        atTop
        (𝓝 (‖detector
                ((1, 0) : HBXiSourceFEReflectionDetectorCarrier)‖ *
              ‖detector
                ((0, 1) : HBXiSourceFEReflectionDetectorCarrier)‖)) :=
    tendsto_const_nhds
  have hzero := tendsto_nhds_unique hproductZero hconstant
  have hdet1 :
      detector ((1, 0) : HBXiSourceFEReflectionDetectorCarrier) ≠ 0 := by
    intro h
    have : ((1, 0) : HBXiSourceFEReflectionDetectorCarrier) =
        ((0, 0) : HBXiSourceFEReflectionDetectorCarrier) :=
      hfaithful (h.trans hdetectorZero.symm)
    norm_num at this
  have hdet2 :
      detector ((0, 1) : HBXiSourceFEReflectionDetectorCarrier) ≠ 0 := by
    intro h
    have : ((0, 1) : HBXiSourceFEReflectionDetectorCarrier) =
        ((0, 0) : HBXiSourceFEReflectionDetectorCarrier) :=
      hfaithful (h.trans hdetectorZero.symm)
    norm_num at this
  have hpos :
      0 < ‖detector
              ((1, 0) : HBXiSourceFEReflectionDetectorCarrier)‖ *
            ‖detector
              ((0, 1) : HBXiSourceFEReflectionDetectorCarrier)‖ :=
    mul_pos (norm_pos_iff.mpr hdet1) (norm_pos_iff.mpr hdet2)
  nlinarith

/-- The same obstruction with either ordering of the stable and unstable axes. -/
theorem no_vacuumContinuous_injective_scalarizer_of_diagonal_hyperbolic
    (a b c : ℂ)
    (detector : HBXiSourceFEReflectionDetectorCarrier →
      HBXiSourceFEReflectionDetectorCarrier)
    (ha0 : a ≠ 0) (hb0 : b ≠ 0)
    (hhyperbolic :
      (‖a‖ < 1 ∧ 1 < ‖b‖) ∨ (1 < ‖a‖ ∧ ‖b‖ < 1))
    (hcontinuous : ContinuousAt detector 0)
    (hfaithful : Function.Injective detector)
    (hscalar : ∀ x : HBXiSourceFEReflectionDetectorCarrier,
      detector (hbXiSourceFEDiagonalDetectorCocycle a b x) =
        c • detector x) : False := by
  rcases hhyperbolic with h | h
  · exact no_vacuumContinuous_injective_scalarizer_of_diagonal_saddle
      a b c detector ha0 hb0 h.1 h.2 hcontinuous hfaithful hscalar
  · let swappedDetector : HBXiSourceFEReflectionDetectorCarrier →
        HBXiSourceFEReflectionDetectorCarrier :=
      fun x => detector (x.2, x.1)
    have hswapContinuous : ContinuousAt swappedDetector 0 := by
      have hswapAt : ContinuousAt
          (fun x : HBXiSourceFEReflectionDetectorCarrier => (x.2, x.1)) 0 :=
        continuousAt_snd.prodMk continuousAt_fst
      have hswapZero :
          (((0 : HBXiSourceFEReflectionDetectorCarrier).2,
              (0 : HBXiSourceFEReflectionDetectorCarrier).1) :
            HBXiSourceFEReflectionDetectorCarrier) = 0 := by
        ext <;> simp
      simpa [swappedDetector, Function.comp_def] using
        hcontinuous.comp_of_eq hswapAt hswapZero
    have hswapFaithful : Function.Injective swappedDetector := by
      intro x y hxy
      have hswap : (x.2, x.1) = (y.2, y.1) := hfaithful hxy
      apply Prod.ext
      · exact congrArg Prod.snd hswap
      · exact congrArg Prod.fst hswap
    have hswapScalar : ∀ x : HBXiSourceFEReflectionDetectorCarrier,
        swappedDetector (hbXiSourceFEDiagonalDetectorCocycle b a x) =
          c • swappedDetector x := by
      intro x
      simpa [swappedDetector, hbXiSourceFEDiagonalDetectorCocycle] using
        hscalar ((x.2, x.1) : HBXiSourceFEReflectionDetectorCarrier)
    exact no_vacuumContinuous_injective_scalarizer_of_diagonal_saddle
      b a c swappedDetector hb0 ha0 h.2 h.1
      hswapContinuous hswapFaithful hswapScalar

private theorem norm_lt_one_of_normSq_lt_one {z : ℂ}
    (h : Complex.normSq z < 1) : ‖z‖ < 1 := by
  rw [← Complex.sq_norm] at h
  nlinarith [norm_nonneg z]

private theorem one_lt_norm_of_one_lt_normSq {z : ℂ}
    (h : 1 < Complex.normSq z) : 1 < ‖z‖ := by
  rw [← Complex.sq_norm] at h
  nlinarith [norm_nonneg z]

private theorem hbXiPeierlsUnitSourceFECocycle_ne_zero_local
    (q : XiZeroCopy) : hbXiPeierlsUnitSourceFECocycle q ≠ 0 := by
  intro hzero
  have hinvolutive := hbXiPeierlsUnitSourceFECocycle_involutive q
  simp [hzero] at hinvolutive

/-- Exact literal source-FE action on one Xi copy and its reflected copy. -/
def hbXiSourceFEReflectionPairDetectorCocycle
    (q : XiZeroCopy) (x : HBXiSourceFEReflectionDetectorCarrier) :
    HBXiSourceFEReflectionDetectorCarrier :=
  (hbXiPeierlsUnitSourceFECocycle q * x.1,
    hbXiPeierlsUnitSourceFECocycle (xiZeroCopyReflectEquiv q) * x.2)

/-- One scalar detector gain intertwines the exact reflection-paired source-FE action. -/
def HBXiSourceFEReflectionVacuumContinuousDetectorScalarizes
    (detector : HBXiSourceFEReflectionDetectorCarrier →
      HBXiSourceFEReflectionDetectorCarrier)
    (c : ℂ) (q : XiZeroCopy) : Prop :=
  ∀ x : HBXiSourceFEReflectionDetectorCarrier,
    detector (hbXiSourceFEReflectionPairDetectorCocycle q x) =
      c • detector x

/-- Copywise exact scalarization by a detector continuous only at vacuum and globally faithful. -/
def HBXiSourceFEReflectionExistsVacuumContinuousFaithfulDetectorScalarizationAt
    (q : XiZeroCopy) : Prop :=
  ∃ detector : HBXiSourceFEReflectionDetectorCarrier →
      HBXiSourceFEReflectionDetectorCarrier,
    ∃ c : ℂ,
      ContinuousAt detector 0 ∧ Function.Injective detector ∧
        HBXiSourceFEReflectionVacuumContinuousDetectorScalarizes detector c q

/-- Off the critical wall, the exact reflection pair has one stable and one unstable axis. -/
theorem hbXiSourceFEReflectionPair_hyperbolic_of_offLine
    (q : XiZeroCopy) (hoff : (q.1 : ℂ).re ≠ 1 / 2) :
    (‖hbXiPeierlsUnitSourceFECocycle q‖ < 1 ∧
        1 < ‖hbXiPeierlsUnitSourceFECocycle
          (xiZeroCopyReflectEquiv q)‖) ∨
      (1 < ‖hbXiPeierlsUnitSourceFECocycle q‖ ∧
        ‖hbXiPeierlsUnitSourceFECocycle
          (xiZeroCopyReflectEquiv q)‖ < 1) := by
  rcases lt_or_gt_of_ne hoff with hleft | hright
  · right
    constructor
    · exact one_lt_norm_of_one_lt_normSq
        ((one_lt_normSq_hbXiPeierlsUnitSourceFECocycle_iff q).mpr hleft)
    · apply norm_lt_one_of_normSq_lt_one
      apply (normSq_hbXiPeierlsUnitSourceFECocycle_lt_one_iff
        (xiZeroCopyReflectEquiv q)).mpr
      rw [xiZeroCopyReflect_re_eq_one_sub]
      linarith
  · left
    constructor
    · exact norm_lt_one_of_normSq_lt_one
        ((normSq_hbXiPeierlsUnitSourceFECocycle_lt_one_iff q).mpr hright)
    · apply one_lt_norm_of_one_lt_normSq
      apply (one_lt_normSq_hbXiPeierlsUnitSourceFECocycle_iff
        (xiZeroCopyReflectEquiv q)).mpr
      rw [xiZeroCopyReflect_re_eq_one_sub]
      linarith

/-- Vacuum continuity plus faithfulness excludes exact scalarization at every tilted Xi copy. -/
theorem hbXiSourceFEReflection_vacuumContinuousFaithfulScalarization_forces_re_eq_half
    (detector : HBXiSourceFEReflectionDetectorCarrier →
      HBXiSourceFEReflectionDetectorCarrier)
    (c : ℂ) (q : XiZeroCopy)
    (hcontinuous : ContinuousAt detector 0)
    (hfaithful : Function.Injective detector)
    (hscalar :
      HBXiSourceFEReflectionVacuumContinuousDetectorScalarizes detector c q) :
    (q.1 : ℂ).re = 1 / 2 := by
  by_contra hoff
  exact no_vacuumContinuous_injective_scalarizer_of_diagonal_hyperbolic
    (hbXiPeierlsUnitSourceFECocycle q)
    (hbXiPeierlsUnitSourceFECocycle (xiZeroCopyReflectEquiv q))
    c detector
    (hbXiPeierlsUnitSourceFECocycle_ne_zero_local q)
    (hbXiPeierlsUnitSourceFECocycle_ne_zero_local
      (xiZeroCopyReflectEquiv q))
    (hbXiSourceFEReflectionPair_hyperbolic_of_offLine q hoff)
    hcontinuous hfaithful (by
      simpa [HBXiSourceFEReflectionVacuumContinuousDetectorScalarizes,
        hbXiSourceFEReflectionPairDetectorCocycle,
        hbXiSourceFEDiagonalDetectorCocycle] using hscalar)

private theorem hbXiPeierlsUnitSourceFECocycle_eq_one_of_re_eq_half
    (q : XiZeroCopy) (hline : (q.1 : ℂ).re = 1 / 2) :
    hbXiPeierlsUnitSourceFECocycle q = 1 := by
  have hsource :=
    (d4BMXiSecondHarmonicPolarizedSourceAmplitude_eq_zero_iff one_ne_zero q).mpr
      hline
  simp [hbXiPeierlsUnitSourceFECocycle, hsource]

/-- Minimal continuous faithful detector scalarization exists exactly on the critical wall. -/
theorem hbXiSourceFEReflectionExistsVacuumContinuousFaithfulDetectorScalarizationAt_iff_re_eq_half
    (q : XiZeroCopy) :
    HBXiSourceFEReflectionExistsVacuumContinuousFaithfulDetectorScalarizationAt q ↔
      (q.1 : ℂ).re = 1 / 2 := by
  constructor
  · rintro ⟨detector, c, hcontinuous, hfaithful, hscalar⟩
    exact
      hbXiSourceFEReflection_vacuumContinuousFaithfulScalarization_forces_re_eq_half
        detector c q hcontinuous hfaithful hscalar
  · intro hline
    have hlineR : ((xiZeroCopyReflectEquiv q).1 : ℂ).re = 1 / 2 := by
      rw [xiZeroCopyReflect_re_eq_one_sub]
      linarith
    have hq := hbXiPeierlsUnitSourceFECocycle_eq_one_of_re_eq_half q hline
    have hRq := hbXiPeierlsUnitSourceFECocycle_eq_one_of_re_eq_half
      (xiZeroCopyReflectEquiv q) hlineR
    refine ⟨id, 1, continuousAt_id, Function.injective_id, ?_⟩
    intro x
    simp [hbXiSourceFEReflectionPairDetectorCocycle, hq, hRq]

/-- Copy-dependent minimal detector scalarization on every Xi fibre. -/
def HBXiSourceFEReflectionGlobalVacuumContinuousFaithfulDetectorScalarization : Prop :=
  ∀ q : XiZeroCopy,
    HBXiSourceFEReflectionExistsVacuumContinuousFaithfulDetectorScalarizationAt q

/-- Universal vacuum-continuous faithful scalarization of the exact reflection pair is RH. -/
theorem hbXiSourceFEReflectionGlobalVacuumContinuousFaithfulDetectorScalarization_iff_rh :
    HBXiSourceFEReflectionGlobalVacuumContinuousFaithfulDetectorScalarization ↔
      RiemannHypothesis := by
  constructor
  · intro h
    apply forall_normSq_hbXiPeierlsUnitSourceFECocycle_eq_one_iff_rh.mp
    intro q
    apply (normSq_hbXiPeierlsUnitSourceFECocycle_eq_one_iff q).mpr
    exact
      (hbXiSourceFEReflectionExistsVacuumContinuousFaithfulDetectorScalarizationAt_iff_re_eq_half
        q).mp (h q)
  · intro hRH q
    apply
      (hbXiSourceFEReflectionExistsVacuumContinuousFaithfulDetectorScalarizationAt_iff_re_eq_half
        q).mpr
    exact (normSq_hbXiPeierlsUnitSourceFECocycle_eq_one_iff q).mp
      (forall_normSq_hbXiPeierlsUnitSourceFECocycle_eq_one_iff_rh.mpr hRH q)

/-- Closed route certificate for vacuum-continuous faithful nonlinear scalar detectors. -/
def D4HBSourceFEVacuumContinuousNonlinearDetectorScalarizationRouteKilled : Prop :=
  (∀ q : XiZeroCopy,
    HBXiSourceFEReflectionExistsVacuumContinuousFaithfulDetectorScalarizationAt q ↔
      (q.1 : ℂ).re = 1 / 2) ∧
  (∀ (detector : HBXiSourceFEReflectionDetectorCarrier →
        HBXiSourceFEReflectionDetectorCarrier)
      (c : ℂ) (q : XiZeroCopy),
    ContinuousAt detector 0 → Function.Injective detector →
    HBXiSourceFEReflectionVacuumContinuousDetectorScalarizes detector c q →
      (q.1 : ℂ).re = 1 / 2) ∧
  (HBXiSourceFEReflectionGlobalVacuumContinuousFaithfulDetectorScalarization ↔
    RiemannHypothesis)

/-- Premise-free certificate: a vacuum-continuous faithful nonlinear readout cannot collapse the
off-wall source-FE saddle to one scalar gain. -/
theorem d4HBSourceFEVacuumContinuousNonlinearDetectorScalarizationRouteKilled :
    D4HBSourceFEVacuumContinuousNonlinearDetectorScalarizationRouteKilled := by
  exact ⟨
    hbXiSourceFEReflectionExistsVacuumContinuousFaithfulDetectorScalarizationAt_iff_re_eq_half,
    fun detector c q =>
      hbXiSourceFEReflection_vacuumContinuousFaithfulScalarization_forces_re_eq_half
        detector c q,
    hbXiSourceFEReflectionGlobalVacuumContinuousFaithfulDetectorScalarization_iff_rh⟩

end

end RHTower
