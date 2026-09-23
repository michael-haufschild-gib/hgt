import GaloisForLFunctions.RHTower.ThetaCuspFifthRootCurvatureVelocitySecondLikelihoodReserve
import GaloisForLFunctions.RHTower.VanDerCorputSecond

/-!
# Theta C5 velocity: likelihood Bregman cone and its sharp obstruction

The modular-center C5 velocity core is rewritten in first-atom tangent coordinates minus the
exact Bregman displacement of the higher-atom likelihood.  Strict likelihood convexity places
that displacement in `0 < D < tE`; source cooling sharpens this to `E < 1` and `D < t`.
The first atom supplies the complementary strong-convexity laws `38t ≤ p` and `19t² ≤ Q`.

These facts do not, by themselves, force C5 velocity positivity.  A closed counterexample theorem
kills the entire source-independent cone-transfer route, even with positive second and third jets.
The strongest positive survivor is an exact action-barrier classification: in the
curvature-dominant chamber the source must have positive drive and its exponential action reserve
must pay the explicit slope tax.  Thus the remaining C5-VP1 burden is source-specific coupling,
not generic convex geometry.
-/

open Real Set

namespace RHTower

noncomputable section

/-- First-atom center action relative to the full-source seam tangent. -/
def thetaCuspCenterFirstAtomTangentAction (t : ℝ) : ℝ :=
  2 * (thetaCuspFirstAtomLogDensity 0 - thetaCuspFirstAtomLogDensity t -
    t * thetaCuspLikelihoodSourceLogPartitionJetOne 0)

/-- Derivative of the first-atom tangent action. -/
def thetaCuspCenterFirstAtomTangentSlope (t : ℝ) : ℝ :=
  -2 * (thetaCuspFirstAtomLogJetOne t +
    thetaCuspLikelihoodSourceLogPartitionJetOne 0)

/-- Twice the likelihood Bregman divergence from the modular seam. -/
def thetaCuspCenterLikelihoodBregmanAction (t : ℝ) : ℝ :=
  2 * (thetaCuspLikelihoodSourceLogPartition t -
    thetaCuspLikelihoodSourceLogPartition 0 -
    t * thetaCuspLikelihoodSourceLogPartitionJetOne 0)

/-- Terminal likelihood-score displacement from the modular seam. -/
def thetaCuspCenterLikelihoodBregmanSlope (t : ℝ) : ℝ :=
  2 * (thetaCuspLikelihoodSourceLogPartitionJetOne t -
    thetaCuspLikelihoodSourceLogPartitionJetOne 0)

theorem thetaCuspLikelihoodSourceLogPartitionJetOne_zero_eq_neg_boundarySlope :
    thetaCuspLikelihoodSourceLogPartitionJetOne 0 =
      -thetaCuspFirstAtomBoundaryLogSlope := by
  have h := two_pi_mul_thetaCuspLikelihoodMean_seam
  unfold thetaCuspLikelihoodSourceLogPartitionJetOne
  rw [show thetaCuspSingleAtomReflectionScale 1 0 = Real.pi by
    unfold thetaCuspSingleAtomReflectionScale
    norm_num]
  linarith

theorem thetaCuspFirstAtomBoundaryLogSlope_eq_neg_two_superpotential_zero :
    thetaCuspFirstAtomBoundaryLogSlope =
      -2 * thetaCuspBornWittenSuperpotential 1 0 := by
  have hden : 0 < Real.pi - 3 / 2 := by
    nlinarith [Real.pi_gt_three]
  unfold thetaCuspFirstAtomBoundaryLogSlope
    thetaCuspBornWittenSuperpotential
  rw [thetaCuspBornWittenWeight_eq]
  unfold thetaCuspMorseSuperpotential thetaCuspMorseScale
  norm_num
  have hden' : 2 * Real.pi - 3 ≠ 0 := by nlinarith
  field_simp [hden.ne', hden']
  ring

theorem thetaCuspCenterFirstAtomTangentSlope_eq_superpotentialIncrement
    (t : ℝ) :
    thetaCuspCenterFirstAtomTangentSlope t =
      4 * (thetaCuspBornWittenSuperpotential 1 t -
        thetaCuspBornWittenSuperpotential 1 0) := by
  unfold thetaCuspCenterFirstAtomTangentSlope thetaCuspFirstAtomLogJetOne
  rw [thetaCuspLikelihoodSourceLogPartitionJetOne_zero_eq_neg_boundarySlope,
    thetaCuspFirstAtomBoundaryLogSlope_eq_neg_two_superpotential_zero]
  ring

private theorem thetaCuspLogSource_eq_firstAtomLogDensity_add_likelihood
    {x : ℝ} (hx : 0 ≤ x) :
    thetaCuspLogSource x = Real.log Real.pi +
      thetaCuspFirstAtomLogDensity x +
      thetaCuspLikelihoodSourceLogPartition x := by
  have hB : 0 < thetaCuspLikelihoodCoordinate x :=
    thetaCuspLikelihoodCoordinate_pos hx
  have hfirst : 0 < thetaCuspSourceTerm x 1 := by
    rw [thetaCuspSourceTerm_one_eq_exp_firstAtomLogDensity hx]
    positivity
  have hpart : 0 < thetaCuspLikelihoodPartition
      (thetaCuspLikelihoodCoordinate x) :=
    thetaCuspLikelihoodPartition_pos hB
  unfold thetaCuspLogSource thetaCuspLikelihoodSourceLogPartition
  rw [thetaCuspFullSource_eq_first_mul_likelihoodPartition hB,
    Real.log_mul hfirst.ne' hpart.ne',
    thetaCuspSourceTerm_one_eq_exp_firstAtomLogDensity hx,
    Real.log_mul Real.pi_pos.ne' (Real.exp_pos _).ne', Real.log_exp]

theorem thetaCuspReflectedLogAction_zero_eq_firstAtomTangent_sub_bregman
    {t : ℝ} (ht : 0 ≤ t) :
    thetaCuspReflectedLogAction 0 t =
      thetaCuspCenterFirstAtomTangentAction t -
        thetaCuspCenterLikelihoodBregmanAction t := by
  have hzero := thetaCuspLogSource_eq_firstAtomLogDensity_add_likelihood
    (x := 0) (by norm_num)
  have htlog := thetaCuspLogSource_eq_firstAtomLogDensity_add_likelihood ht
  unfold thetaCuspReflectedLogAction
  rw [zero_add, zero_sub, thetaCuspLogSource_neg, hzero, htlog]
  unfold thetaCuspCenterFirstAtomTangentAction
    thetaCuspCenterLikelihoodBregmanAction
  ring

theorem thetaCuspReflectedLogJetOne_zero_eq_firstAtomTangent_sub_bregman
    {t : ℝ} (ht : 0 < t) :
    thetaCuspReflectedLogJetOne 0 t =
      thetaCuspCenterFirstAtomTangentSlope t -
        thetaCuspCenterLikelihoodBregmanSlope t := by
  rw [thetaCuspReflectedLogJetOne_zero_eq_likelihood ht]
  unfold thetaCuspCenterFirstAtomTangentSlope
    thetaCuspCenterLikelihoodBregmanSlope
  ring

theorem thetaCuspCenterLikelihoodBregmanSlope_pos
    {t : ℝ} (ht : 0 < t) :
    0 < thetaCuspCenterLikelihoodBregmanSlope t := by
  have hmono := strictMonoOn_thetaCuspLikelihoodSourceLogPartitionJetOne
    (show (0 : ℝ) ∈ Ici 0 by simp) (show t ∈ Ici 0 by simp [ht.le]) ht
  unfold thetaCuspCenterLikelihoodBregmanSlope
  linarith

theorem thetaCuspCenterLikelihoodBregmanAction_pos
    {t : ℝ} (ht : 0 < t) :
    0 < thetaCuspCenterLikelihoodBregmanAction t := by
  have hslope :=
    strictConvexOn_thetaCuspLikelihoodSourceLogPartition.lt_slope_of_hasDerivAt
      (show (0 : ℝ) ∈ Ici 0 by simp) (show t ∈ Ici 0 by simp [ht.le]) ht
      (hasDerivAt_thetaCuspLikelihoodSourceLogPartition
        (thetaCuspLikelihoodCoordinate_pos (show (0 : ℝ) ≤ 0 by norm_num)))
  unfold thetaCuspCenterLikelihoodBregmanAction
  rw [slope_def_field] at hslope
  have hslope' :
      thetaCuspLikelihoodSourceLogPartitionJetOne 0 <
        (thetaCuspLikelihoodSourceLogPartition t -
          thetaCuspLikelihoodSourceLogPartition 0) / t := by
    simpa only [sub_zero] using hslope
  have hmul := (lt_div_iff₀ ht).mp hslope'
  linarith

theorem thetaCuspCenterLikelihoodBregmanAction_lt_mul_slope
    {t : ℝ} (ht : 0 < t) :
    thetaCuspCenterLikelihoodBregmanAction t <
      t * thetaCuspCenterLikelihoodBregmanSlope t := by
  have hslope :=
    strictConvexOn_thetaCuspLikelihoodSourceLogPartition.slope_lt_deriv
      (show (0 : ℝ) ∈ Ici 0 by simp) (show t ∈ Ici 0 by simp [ht.le]) ht
      (hasDerivAt_thetaCuspLikelihoodSourceLogPartition
        (thetaCuspLikelihoodCoordinate_pos ht.le)).differentiableAt
  rw [(hasDerivAt_thetaCuspLikelihoodSourceLogPartition
    (thetaCuspLikelihoodCoordinate_pos ht.le)).deriv, slope_def_field] at hslope
  have hslope' :
      (thetaCuspLikelihoodSourceLogPartition t -
        thetaCuspLikelihoodSourceLogPartition 0) / t <
          thetaCuspLikelihoodSourceLogPartitionJetOne t := by
    simpa only [sub_zero] using hslope
  have hmul := (div_lt_iff₀ ht).mp hslope'
  unfold thetaCuspCenterLikelihoodBregmanAction
    thetaCuspCenterLikelihoodBregmanSlope
  nlinarith

theorem thetaCuspLikelihoodSourceLogPartitionJetOne_neg
    {t : ℝ} (ht : 0 ≤ t) :
    thetaCuspLikelihoodSourceLogPartitionJetOne t < 0 := by
  have hscale : 0 < thetaCuspSingleAtomReflectionScale 1 t := by
    unfold thetaCuspSingleAtomReflectionScale
    positivity
  have hmean := thetaCuspLikelihoodMean_pos
    (thetaCuspLikelihoodCoordinate_pos ht)
  unfold thetaCuspLikelihoodSourceLogPartitionJetOne
  nlinarith [mul_pos hscale hmean]

/-- Source-specific anti-collapse law: the entire higher-atom likelihood can remove less than
one unit from the first-atom tangent slope, uniformly on the physical half-line. -/
theorem thetaCuspCenterLikelihoodBregmanSlope_lt_one
    {t : ℝ} (ht : 0 ≤ t) :
    thetaCuspCenterLikelihoodBregmanSlope t < 1 := by
  have hjt := thetaCuspLikelihoodSourceLogPartitionJetOne_neg ht
  have hboundary := thetaCuspFirstAtomBoundaryLogSlope_lt_one_half
  unfold thetaCuspCenterLikelihoodBregmanSlope
  rw [thetaCuspLikelihoodSourceLogPartitionJetOne_zero_eq_neg_boundarySlope]
  nlinarith

/-- The Bregman action deficit is strictly smaller than elapsed source time. -/
theorem thetaCuspCenterLikelihoodBregmanAction_lt_self
    {t : ℝ} (ht : 0 < t) :
    thetaCuspCenterLikelihoodBregmanAction t < t := by
  have hcone := thetaCuspCenterLikelihoodBregmanAction_lt_mul_slope ht
  have hslope := thetaCuspCenterLikelihoodBregmanSlope_lt_one ht.le
  have hscaled :
      t * thetaCuspCenterLikelihoodBregmanSlope t < t * 1 :=
    mul_lt_mul_of_pos_left hslope ht
  linarith

theorem hasDerivAt_thetaCuspCenterFirstAtomTangentAction
    {t : ℝ} (ht : 0 ≤ t) :
    HasDerivAt thetaCuspCenterFirstAtomTangentAction
      (thetaCuspCenterFirstAtomTangentSlope t) t := by
  have hf : HasDerivAt thetaCuspFirstAtomLogDensity
      (thetaCuspFirstAtomLogJetOne t) t := by
    simpa only [thetaCuspFirstAtomLogJetOne] using
      hasDerivAt_thetaCuspFirstAtomLogDensity ht
  have hraw := ((((hasDerivAt_const t
    (thetaCuspFirstAtomLogDensity 0)).sub hf).sub
    ((hasDerivAt_id t).mul_const
      (thetaCuspLikelihoodSourceLogPartitionJetOne 0))).const_mul 2)
  refine (hraw.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun x => ?_)).congr_deriv ?_
  · unfold thetaCuspCenterFirstAtomTangentAction
    simp only [Pi.sub_apply, id_eq]
  · unfold thetaCuspCenterFirstAtomTangentSlope
    ring

theorem hasDerivAt_thetaCuspCenterLikelihoodBregmanAction
    {t : ℝ} (ht : 0 ≤ t) :
    HasDerivAt thetaCuspCenterLikelihoodBregmanAction
      (thetaCuspCenterLikelihoodBregmanSlope t) t := by
  have hg := hasDerivAt_thetaCuspLikelihoodSourceLogPartition
    (thetaCuspLikelihoodCoordinate_pos ht)
  have hraw := (((hg.sub_const
    (thetaCuspLikelihoodSourceLogPartition 0)).sub
    ((hasDerivAt_id t).mul_const
      (thetaCuspLikelihoodSourceLogPartitionJetOne 0))).const_mul 2)
  refine (hraw.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun x => ?_)).congr_deriv ?_
  · unfold thetaCuspCenterLikelihoodBregmanAction
    simp only [Pi.sub_apply, id_eq]
  · unfold thetaCuspCenterLikelihoodBregmanSlope
    ring

theorem thirtyEight_mul_le_thetaCuspCenterFirstAtomTangentSlope
    {t : ℝ} (ht : 0 ≤ t) :
    38 * t ≤ thetaCuspCenterFirstAtomTangentSlope t := by
  have hgap := deriv_lower_length
    (a := 0) (b := t) (lam := 19)
    (g' := fun x : ℝ => 2 * thetaCuspBornWittenSuperpotential 1 x)
    (g'' := thetaCuspBornWittenLogCurvature 1)
    (fun x hx => by
      rw [Set.uIcc_of_le ht] at hx
      exact hasDerivAt_two_thetaCuspBornWittenSuperpotential
        (n := 1) (by norm_num) hx.1)
    (fun x hx => by
      rw [Set.uIcc_of_le ht] at hx
      exact (hasDerivAt_thetaCuspBornWittenLogCurvature
        (n := 1) (by norm_num) hx.1).continuousAt.continuousWithinAt)
    (fun x hx => by
      rw [Set.uIcc_of_le ht] at hx
      exact nineteen_le_thetaCuspBornWittenLogCurvature
        (n := 1) (by norm_num) hx.1)
    Set.left_mem_uIcc Set.right_mem_uIcc ht
  rw [thetaCuspCenterFirstAtomTangentSlope_eq_superpotentialIncrement]
  norm_num at hgap ⊢
  linarith

theorem hasDerivAt_thetaCuspCenterFirstAtomTangentSlope
    {t : ℝ} (ht : 0 ≤ t) :
    HasDerivAt thetaCuspCenterFirstAtomTangentSlope
      (2 * thetaCuspBornWittenLogCurvature 1 t) t := by
  have hW := hasDerivAt_two_thetaCuspBornWittenSuperpotential
    (n := 1) (by norm_num) ht
  have hraw := (hW.sub_const
    (2 * thetaCuspBornWittenSuperpotential 1 0)).const_mul 2
  refine (hraw.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun x => ?_)).congr_deriv ?_
  · rw [thetaCuspCenterFirstAtomTangentSlope_eq_superpotentialIncrement]
    ring
  · ring

theorem nineteen_mul_sq_le_thetaCuspCenterFirstAtomTangentAction
    {t : ℝ} (ht : 0 ≤ t) :
    19 * t ^ (2 : ℕ) ≤ thetaCuspCenterFirstAtomTangentAction t := by
  have hgap := deriv_lower_length
    (a := 0) (b := t) (lam := 0)
    (g' := fun x : ℝ =>
      thetaCuspCenterFirstAtomTangentAction x - 19 * x ^ (2 : ℕ))
    (g'' := fun x : ℝ =>
      thetaCuspCenterFirstAtomTangentSlope x - 38 * x)
    (fun x hx => by
      rw [Set.uIcc_of_le ht] at hx
      have hA := hasDerivAt_thetaCuspCenterFirstAtomTangentAction hx.1
      have hq : HasDerivAt (fun y : ℝ => 19 * y ^ (2 : ℕ)) (38 * x) x := by
        have hraw := ((hasDerivAt_id x).pow 2).const_mul 19
        have hraw' : HasDerivAt (fun y : ℝ => 19 * y ^ (2 : ℕ))
            (19 * (2 * x)) x := by
          simpa only [Pi.pow_apply, id_eq, Nat.cast_ofNat,
            Nat.reduceSubDiff, pow_one, mul_one] using hraw
        exact hraw'.congr_deriv (by ring)
      exact hA.sub hq)
    (fun x hx => by
      rw [Set.uIcc_of_le ht] at hx
      exact (hasDerivAt_thetaCuspCenterFirstAtomTangentSlope hx.1).continuousAt.sub
        (continuousAt_const.mul continuousAt_id) |>.continuousWithinAt)
    (fun x hx => by
      rw [Set.uIcc_of_le ht] at hx
      linarith [thirtyEight_mul_le_thetaCuspCenterFirstAtomTangentSlope hx.1])
    Set.left_mem_uIcc Set.right_mem_uIcc ht
  unfold thetaCuspCenterFirstAtomTangentAction at hgap ⊢
  norm_num at hgap ⊢
  linarith

/-- The literal source center slope retains all but one unit of the strongly convex first-atom
tangent slope. -/
theorem thirtyEight_mul_sub_one_lt_thetaCuspReflectedLogJetOne_zero
    {t : ℝ} (ht : 0 < t) :
    38 * t - 1 < thetaCuspReflectedLogJetOne 0 t := by
  have hp := thirtyEight_mul_le_thetaCuspCenterFirstAtomTangentSlope ht.le
  have hE := thetaCuspCenterLikelihoodBregmanSlope_lt_one ht.le
  rw [thetaCuspReflectedLogJetOne_zero_eq_firstAtomTangent_sub_bregman ht]
  linarith

/-- The literal source center action retains the quadratic first-atom tangent action up to a
strictly sublinear likelihood deficit. -/
theorem nineteen_mul_sq_sub_self_lt_thetaCuspReflectedLogAction_zero
    {t : ℝ} (ht : 0 < t) :
    19 * t ^ (2 : ℕ) - t < thetaCuspReflectedLogAction 0 t := by
  have hQ := nineteen_mul_sq_le_thetaCuspCenterFirstAtomTangentAction ht.le
  have hD := thetaCuspCenterLikelihoodBregmanAction_lt_self ht
  rw [thetaCuspReflectedLogAction_zero_eq_firstAtomTangent_sub_bregman ht.le]
  linarith

theorem exists_c5VelocityActionCore_neg_of_positive_curvatureGap
    {t q₁ q₂ q₃ : ℝ} (ht : 0 < t) (hq₁ : 0 < q₁) (hgap : q₁ ^ (2 : ℕ) < q₂) :
    ∃ A : ℝ, 0 < A ∧ A < t * q₁ ∧
      thetaCuspReflectedActionFifthRootVelocityCore
        (Real.exp A - 1) t q₁ q₂ q₃ < 0 := by
  let f : ℝ → ℝ := fun A =>
    thetaCuspReflectedActionFifthRootVelocityCore
      (Real.exp A - 1) t q₁ q₂ q₃
  have hfcont : ContinuousAt f 0 := by
    unfold f thetaCuspReflectedActionFifthRootVelocityCore
    fun_prop
  have hfirst : 0 < 17 * t * q₁ ^ (2 : ℕ) := by positivity
  have hsecond : 0 < 3 * t ^ (2 : ℕ) * q₁ * (q₂ - q₁ ^ (2 : ℕ)) := by positivity
  have hfzero : f 0 < 0 := by
    unfold f thetaCuspReflectedActionFifthRootVelocityCore
    rw [Real.exp_zero]
    norm_num
    linarith
  have hevent : ∀ᶠ A in nhds 0, f A < 0 :=
    hfcont.eventually_lt continuousAt_const hfzero
  rcases Metric.mem_nhds_iff.mp hevent with ⟨ε, hε, hball⟩
  let A := min (ε / 2) (t * q₁ / 2)
  have htq : 0 < t * q₁ := mul_pos ht hq₁
  have hA : 0 < A := by
    dsimp only [A]
    exact lt_min (half_pos hε) (half_pos htq)
  have hAlt : A < t * q₁ :=
    lt_of_le_of_lt (min_le_right _ _) (half_lt_self htq)
  have hAε : A < ε :=
    lt_of_le_of_lt (min_le_left _ _) (half_lt_self hε)
  refine ⟨A, hA, hAlt, hball ?_⟩
  rw [Metric.mem_ball, Real.dist_eq]
  simpa only [sub_zero, abs_of_pos hA] using hAε

/-- Coefficient multiplying the exponential action reserve in the C5 velocity core. -/
def c5VelocityActionDrive (t q₁ q₂ q₃ : ℝ) : ℝ :=
  39 * q₁ + t * (q₂ - q₁ ^ (2 : ℕ)) +
    5 * t ^ (2 : ℕ) * (q₃ - 3 * q₁ * q₂ + q₁ ^ (3 : ℕ))

/-- Action-independent slope tax in the C5 velocity core. -/
def c5VelocitySlopeTax (t q₁ q₂ : ℝ) : ℝ :=
  17 * t * q₁ ^ (2 : ℕ) + 3 * t ^ (2 : ℕ) * q₁ * (q₂ - q₁ ^ (2 : ℕ))

theorem thetaCuspReflectedActionFifthRootVelocityCore_eq_drive_sub_tax
    (r t q₁ q₂ q₃ : ℝ) :
    thetaCuspReflectedActionFifthRootVelocityCore r t q₁ q₂ q₃ =
      r * c5VelocityActionDrive t q₁ q₂ q₃ -
        c5VelocitySlopeTax t q₁ q₂ := by
  unfold thetaCuspReflectedActionFifthRootVelocityCore
    c5VelocityActionDrive c5VelocitySlopeTax
  ring

/-- Sharp positive survivor of the failed cone-transfer route.  In the curvature-dominant
chamber, C5 velocity is nonnegative exactly when the drive is positive and the literal source
action clears the displayed reserve threshold. -/
theorem c5VelocityActionCore_nonneg_iff_drive_pos_and_reserve
    {A t q₁ q₂ q₃ : ℝ} (hA : 0 < A) (ht : 0 < t)
    (hq₁ : 0 < q₁) (hgap : q₁ ^ (2 : ℕ) < q₂) :
    0 ≤ thetaCuspReflectedActionFifthRootVelocityCore
        (Real.exp A - 1) t q₁ q₂ q₃ ↔
      0 < c5VelocityActionDrive t q₁ q₂ q₃ ∧
        c5VelocitySlopeTax t q₁ q₂ /
            c5VelocityActionDrive t q₁ q₂ q₃ ≤ Real.exp A - 1 := by
  have hr : 0 < Real.exp A - 1 := by
    rw [sub_pos, ← Real.exp_zero]
    exact Real.exp_lt_exp.mpr hA
  have htax : 0 < c5VelocitySlopeTax t q₁ q₂ := by
    unfold c5VelocitySlopeTax
    have hfirst : 0 < 17 * t * q₁ ^ (2 : ℕ) := by positivity
    have hsecond : 0 < 3 * t ^ (2 : ℕ) * q₁ * (q₂ - q₁ ^ (2 : ℕ)) := by positivity
    linarith
  rw [thetaCuspReflectedActionFifthRootVelocityCore_eq_drive_sub_tax]
  constructor
  · intro hcore
    have hdrive : 0 < c5VelocityActionDrive t q₁ q₂ q₃ := by
      by_contra hnot
      have hnonpos : c5VelocityActionDrive t q₁ q₂ q₃ ≤ 0 :=
        le_of_not_gt hnot
      have hprod :
          (Real.exp A - 1) * c5VelocityActionDrive t q₁ q₂ q₃ ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hr.le hnonpos
      linarith
    refine ⟨hdrive, (div_le_iff₀ hdrive).2 ?_⟩
    linarith
  · rintro ⟨hdrive, hreserve⟩
    have hscaled := (div_le_iff₀ hdrive).1 hreserve
    linarith

/-- Candidate source-independent transfer from the strict Bregman chamber, the exact theta
strong-convexity floors, and positive first-atom second/third jets to the C5 velocity core. -/
def C5VelocityStrongTangentBregmanConeTransfer : Prop :=
  ∀ Q p D E q₂ q₃ : ℝ,
    19 ≤ Q → 38 ≤ p → Q < p →
    0 < D → D < E → 0 < E →
    0 < Q - D → Q - D ≤ p - E → 0 < p - E →
    38 ≤ q₂ → 0 < q₃ →
    0 ≤ thetaCuspReflectedActionFifthRootVelocityCore
      (Real.exp (Q - D) - 1) 1 (p - E) q₂ q₃

/-- The strong tangent floors and strict Bregman cone do not transfer C5 positivity.  This
formally kills every source-independent proof using only those inequalities: negative cores
persist at arbitrarily small positive actual action, even with positive second and third jets. -/
theorem not_C5VelocityStrongTangentBregmanConeTransfer :
    ¬ C5VelocityStrongTangentBregmanConeTransfer := by
  intro htransfer
  obtain ⟨A, hA, hAone, hneg⟩ :=
    exists_c5VelocityActionCore_neg_of_positive_curvatureGap
      (t := 1) (q₁ := 1) (q₂ := 38) (q₃ := 1)
      (by norm_num) (by norm_num) (by norm_num)
  have hnonneg := htransfer 19 38 (19 - A) 37 38 1
    (by norm_num) (by norm_num) (by norm_num)
    (by nlinarith) (by nlinarith) (by norm_num)
    (by nlinarith) (by nlinarith) (by norm_num)
    (by norm_num) (by norm_num)
  have hsame :
      thetaCuspReflectedActionFifthRootVelocityCore
          (Real.exp (19 - (19 - A)) - 1) 1 (38 - 37) 38 1 =
        thetaCuspReflectedActionFifthRootVelocityCore
          (Real.exp A - 1) 1 1 38 1 := by
    congr <;> ring
  rw [hsame] at hnonneg
  exact (not_le_of_gt hneg) hnonneg

theorem thetaCuspReflectedLogAction_zero_lt_firstAtomTangentAction
    {t : ℝ} (ht : 0 < t) :
    thetaCuspReflectedLogAction 0 t <
      thetaCuspCenterFirstAtomTangentAction t := by
  rw [thetaCuspReflectedLogAction_zero_eq_firstAtomTangent_sub_bregman ht.le]
  exact sub_lt_self _ (thetaCuspCenterLikelihoodBregmanAction_pos ht)

theorem thetaCuspReflectedLogJetOne_zero_lt_firstAtomTangentSlope
    {t : ℝ} (ht : 0 < t) :
    thetaCuspReflectedLogJetOne 0 t <
      thetaCuspCenterFirstAtomTangentSlope t := by
  rw [thetaCuspReflectedLogJetOne_zero_eq_firstAtomTangent_sub_bregman ht]
  exact sub_lt_self _ (thetaCuspCenterLikelihoodBregmanSlope_pos ht)

theorem thetaCuspCenterFirstAtomTangentAction_lt_t_mul_slope
    {t : ℝ} (ht : 0 < t) :
    thetaCuspCenterFirstAtomTangentAction t <
      t * thetaCuspCenterFirstAtomTangentSlope t := by
  have hA := thetaCuspReflectedLogAction_zero_le_t_mul_jetOne ht
  have hD := thetaCuspCenterLikelihoodBregmanAction_lt_mul_slope ht
  rw [thetaCuspReflectedLogAction_zero_eq_firstAtomTangent_sub_bregman ht.le,
    thetaCuspReflectedLogJetOne_zero_eq_firstAtomTangent_sub_bregman ht] at hA
  nlinarith

theorem thetaCuspCenterFifthRootVelocityFirstAtomCurvatureCore_eq_bregmanCone
    {t : ℝ} (ht : 0 < t) :
    thetaCuspCenterFifthRootVelocityFirstAtomCurvatureCore t =
      thetaCuspReflectedActionFifthRootVelocityCore
        (Real.exp (thetaCuspCenterFirstAtomTangentAction t -
          thetaCuspCenterLikelihoodBregmanAction t) - 1) t
        (thetaCuspCenterFirstAtomTangentSlope t -
          thetaCuspCenterLikelihoodBregmanSlope t)
        (2 * thetaCuspBornWittenLogCurvature 1 t)
        (-2 * thetaCuspFirstAtomLogJetThree t) := by
  unfold thetaCuspCenterFifthRootVelocityFirstAtomCurvatureCore
  rw [thetaCuspReflectedLogAction_zero_eq_firstAtomTangent_sub_bregman ht.le,
    thetaCuspReflectedLogJetOne_zero_eq_firstAtomTangent_sub_bregman ht]

end

end RHTower
