import GaloisForLFunctions.HTGeometry.ChronometricBundleMetricRigidity
import GaloisForLFunctions.HTGeometry.ChronometricQuotientRigidity
import GaloisForLFunctions.HTGeometry.ClockPropagatorSelfCalibration

/-!
# Self-calibrating two-mass rigidity over bundles and modulo frame automorphisms

The two-mass self-calibrating identifiability theorem is stated on coordinate-trivialized fields
with a fixed model cotangent fiber and fixed event labels. Both restrictions are removable.

* The calibration channel is pointwise and the symbol channel is fiberwise, so the whole argument
  lifts verbatim to a family of fibers indexed by the event set — in particular to the tangent
  bundle of a charted smooth manifold and to a coordinate chart carrying a smooth nondegenerate
  symmetric matrix field.
* A clock-label-preserving frame automorphism pulls back calibration as a scalar and the inverse
  metric as a quadratic form; the two-mass observation is equivariant, so the rigidity theorem
  descends to the orbit quotients, replacing equality of gravity operators by equality up to the
  action.
-/

namespace GaloisForLFunctions.HTGeometry

universe u v w

/-- The self-calibrating solution graph is the branch-safe chronometric graph. -/
theorem selfCalibratingGravityGraph_eq_chronometricSolutionGraph
    {Geometry : Type u} {Source : Type v} {Observation : Type w}
    (encode : Geometry → Observation) (law : Geometry → Source) :
    selfCalibratingGravityGraph encode law = chronometricSolutionGraph encode law := rfl

/-! ## Bundle lift -/

/-- A self-calibrating inverse-metric field over a bundle of fibers: an unknown nonzero pointwise
calibration together with a symmetric bilinear form on each fiber. -/
structure BundleSelfCalibratingMetric (Event : Type u) (Fiber : Event → Type v)
    [∀ x, AddCommGroup (Fiber x)] [∀ x, Module ℝ (Fiber x)] where
  /-- Unknown local endpoint-calibration product. -/
  calibration : Event → ℝ
  calibration_ne_zero : ∀ x, calibration x ≠ 0
  /-- Inverse-metric coefficients on the fiber over each event. -/
  form : ∀ x, LinearMap.BilinForm ℝ (Fiber x)
  symmetric : ∀ x u v, form x u v = form x v u

namespace BundleSelfCalibratingMetric

variable {Event : Type u} {Fiber : Event → Type v}
  [∀ x, AddCommGroup (Fiber x)] [∀ x, Module ℝ (Fiber x)]

@[ext] theorem ext {g h : BundleSelfCalibratingMetric Event Fiber}
    (hcalibration : g.calibration = h.calibration) (hform : g.form = h.form) : g = h := by
  cases g
  cases h
  simp_all

/-- Complete two-mass observation over a bundle: the zeroth-order inverse-operator difference and
the calibrated quadratic principal symbol. -/
def twoMassObservation (massSq₁ massSq₂ : ℝ)
    (g : BundleSelfCalibratingMetric Event Fiber) :
    (Event → ℝ) × (∀ x, Fiber x → ℝ) :=
  (fun x => (massSq₁ - massSq₂) * g.calibration x,
    fun x v => g.calibration x * g.form x v v)

/-- **Two masses self-calibrate a complete inverse-metric field over a bundle of fibers.** -/
theorem twoMassObservation_injective {massSq₁ massSq₂ : ℝ} (hmass : massSq₁ ≠ massSq₂) :
    Function.Injective
      (twoMassObservation massSq₁ massSq₂ :
        BundleSelfCalibratingMetric Event Fiber → (Event → ℝ) × (∀ x, Fiber x → ℝ)) := by
  intro g h hdata
  have hfirst := congrArg Prod.fst hdata
  have hsecond := congrArg Prod.snd hdata
  have hmassDifference : massSq₁ - massSq₂ ≠ 0 := sub_ne_zero.mpr hmass
  have hcalibration : g.calibration = h.calibration := by
    funext x
    exact mul_left_cancel₀ hmassDifference (congrFun hfirst x)
  refine ext hcalibration ?_
  funext x
  refine bilinForm_eq_of_diagonal_eq (g.symmetric x) (h.symmetric x) ?_
  intro v
  have hsymbol := congrFun (congrFun hsecond x) v
  change g.calibration x * g.form x v v = h.calibration x * h.form x v v at hsymbol
  rw [hcalibration] at hsymbol
  exact mul_left_cancel₀ (h.calibration_ne_zero x) hsymbol

end BundleSelfCalibratingMetric

/-- **Branch-safe two-mass gravity-operator rigidity over a bundle of fibers.** -/
theorem bundleTwoMassSelfCalibratingRigidity
    {Event : Type u} {Fiber : Event → Type v}
    [∀ x, AddCommGroup (Fiber x)] [∀ x, Module ℝ (Fiber x)]
    {Source : Type w} {massSq₁ massSq₂ : ℝ} (hmass : massSq₁ ≠ massSq₂)
    (law₁ law₂ : BundleSelfCalibratingMetric Event Fiber → Source) :
    chronometricSolutionGraph
          (BundleSelfCalibratingMetric.twoMassObservation massSq₁ massSq₂) law₁ =
        chronometricSolutionGraph
          (BundleSelfCalibratingMetric.twoMassObservation massSq₁ massSq₂) law₂ ↔
      law₁ = law₂ :=
  chronometricSolutionGraph_eq_iff_of_injective
    (BundleSelfCalibratingMetric.twoMassObservation_injective hmass) law₁ law₂

/-! ## Tangent bundle of a charted smooth manifold -/

section TangentBundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  (M : Type*) [TopologicalSpace M] [ChartedSpace H M]

/-- A self-calibrating inverse-metric field on the tangent bundle of a charted manifold. -/
abbrev TangentSelfCalibratingMetric : Type _ :=
  BundleSelfCalibratingMetric M (TangentSpace I)

variable {I M}

/-- **Two masses self-calibrate a tangent-bundle inverse-metric field.** -/
theorem tangentTwoMassObservation_injective {massSq₁ massSq₂ : ℝ} (hmass : massSq₁ ≠ massSq₂) :
    Function.Injective
      (BundleSelfCalibratingMetric.twoMassObservation massSq₁ massSq₂ :
        TangentSelfCalibratingMetric I M → (M → ℝ) × (∀ x : M, TangentSpace I x → ℝ)) :=
  BundleSelfCalibratingMetric.twoMassObservation_injective hmass

/-- **Two-mass gravity-operator rigidity on the tangent bundle of a charted manifold.** -/
theorem tangentTwoMassSelfCalibratingRigidity {Source : Type w}
    {massSq₁ massSq₂ : ℝ} (hmass : massSq₁ ≠ massSq₂)
    (law₁ law₂ : TangentSelfCalibratingMetric I M → Source) :
    chronometricSolutionGraph
          (BundleSelfCalibratingMetric.twoMassObservation massSq₁ massSq₂) law₁ =
        chronometricSolutionGraph
          (BundleSelfCalibratingMetric.twoMassObservation massSq₁ massSq₂) law₂ ↔
      law₁ = law₂ :=
  chronometricSolutionGraph_eq_iff_of_injective (tangentTwoMassObservation_injective hmass)
    law₁ law₂

end TangentBundle

/-! ## Coordinate chart: smooth nondegenerate matrix fields with unknown calibration -/

/-- A smooth chart carrying an unknown nonzero calibration and a smooth nondegenerate symmetric
inverse-metric field. -/
structure SmoothSelfCalibratingChart (d : ℕ) where
  /-- Unknown local endpoint-calibration product. -/
  calibration : (Fin d → ℝ) → ℝ
  contDiff_calibration : ContDiff ℝ (⊤ : ℕ∞) calibration
  calibration_ne_zero : ∀ x, calibration x ≠ 0
  /-- Smooth nondegenerate symmetric inverse-metric coefficients. -/
  inverseMetric : SmoothPseudoMetric d

namespace SmoothSelfCalibratingChart

variable {d : ℕ}

theorem ext' {c₁ c₂ : SmoothSelfCalibratingChart d}
    (hcalibration : c₁.calibration = c₂.calibration)
    (hmetric : c₁.inverseMetric = c₂.inverseMetric) : c₁ = c₂ := by
  obtain ⟨k₁, _, _, m₁⟩ := c₁
  obtain ⟨k₂, _, _, m₂⟩ := c₂
  have hk : k₁ = k₂ := hcalibration
  have hm : m₁ = m₂ := hmetric
  subst hk
  subst hm
  rfl

/-- Complete two-mass chart observation. -/
noncomputable def twoMassObservation (massSq₁ massSq₂ : ℝ) (c : SmoothSelfCalibratingChart d) :
    ((Fin d → ℝ) → ℝ) × ((Fin d → ℝ) → (Fin d → ℝ) → ℝ) :=
  (fun x => (massSq₁ - massSq₂) * c.calibration x,
    fun x v => c.calibration x * c.inverseMetric.squaredInterval x v)

/-- **Two masses self-calibrate a smooth chart inverse-metric field.** -/
theorem twoMassObservation_injective {massSq₁ massSq₂ : ℝ} (hmass : massSq₁ ≠ massSq₂) :
    Function.Injective
      (twoMassObservation massSq₁ massSq₂ : SmoothSelfCalibratingChart d → _) := by
  intro c₁ c₂ hdata
  have hfirst := congrArg Prod.fst hdata
  have hsecond := congrArg Prod.snd hdata
  have hmassDifference : massSq₁ - massSq₂ ≠ 0 := sub_ne_zero.mpr hmass
  have hcalibration : c₁.calibration = c₂.calibration := by
    funext x
    exact mul_left_cancel₀ hmassDifference (congrFun hfirst x)
  refine ext' hcalibration ?_
  refine SmoothPseudoMetric.squaredInterval_injective ?_
  funext x v
  have hsymbol := congrFun (congrFun hsecond x) v
  change c₁.calibration x * c₁.inverseMetric.squaredInterval x v =
    c₂.calibration x * c₂.inverseMetric.squaredInterval x v at hsymbol
  rw [hcalibration] at hsymbol
  exact mul_left_cancel₀ (c₂.calibration_ne_zero x) hsymbol

/-- **Two-mass gravity-operator rigidity in a coordinate chart.** -/
theorem twoMassSelfCalibratingRigidity {Source : Type w}
    {massSq₁ massSq₂ : ℝ} (hmass : massSq₁ ≠ massSq₂)
    (law₁ law₂ : SmoothSelfCalibratingChart d → Source) :
    chronometricSolutionGraph (twoMassObservation massSq₁ massSq₂) law₁ =
        chronometricSolutionGraph (twoMassObservation massSq₁ massSq₂) law₂ ↔
      law₁ = law₂ :=
  chronometricSolutionGraph_eq_iff_of_injective (twoMassObservation_injective hmass) law₁ law₂

end SmoothSelfCalibratingChart

/-! ## Quotient by clock-label-preserving frame automorphisms -/

/-- Complete two-mass observation data, carrying the frame-automorphism action. -/
structure SelfCalibratingObservation (Event : Type u) (Tangent : Type v) where
  /-- Zeroth-order inverse-operator difference. -/
  difference : Event → ℝ
  /-- Calibrated quadratic principal symbol. -/
  symbol : Event → Tangent → ℝ

namespace SelfCalibratingObservation

variable {Event : Type u} {Tangent : Type v}

@[ext] theorem ext {Q R : SelfCalibratingObservation Event Tangent}
    (hdifference : Q.difference = R.difference) (hsymbol : Q.symbol = R.symbol) : Q = R := by
  cases Q
  cases R
  simp_all

end SelfCalibratingObservation

section FrameAction

variable {Event : Type u} {Tangent : Type v} [AddCommGroup Tangent] [Module ℝ Tangent]

instance : MulAction (ClockFrameAut Event Tangent)
    (SelfCalibratingObservation Event Tangent) where
  smul a Q :=
    { difference := fun x => Q.difference (a.base⁻¹ x)
      symbol := fun x v => Q.symbol (a.base⁻¹ x) (ClockFrameAut.pullbackFiber a x v) }
  one_smul Q := by
    refine SelfCalibratingObservation.ext ?_ ?_
    · funext x
      show Q.difference ((1 : ClockFrameAut Event Tangent).base⁻¹ x) = Q.difference x
      simp
    · funext x v
      show Q.symbol ((1 : ClockFrameAut Event Tangent).base⁻¹ x)
          (ClockFrameAut.pullbackFiber 1 x v) = Q.symbol x v
      rw [ClockFrameAut.pullbackFiber_one]
      simp
  mul_smul a b Q := by
    refine SelfCalibratingObservation.ext ?_ ?_
    · funext x
      show Q.difference ((a * b).base⁻¹ x) = Q.difference (b.base⁻¹ (a.base⁻¹ x))
      rw [ClockFrameAut.mul_base, mul_inv_rev]
      rfl
    · funext x v
      show Q.symbol ((a * b).base⁻¹ x) (ClockFrameAut.pullbackFiber (a * b) x v) =
        Q.symbol (b.base⁻¹ (a.base⁻¹ x))
          (ClockFrameAut.pullbackFiber b (a.base⁻¹ x) (ClockFrameAut.pullbackFiber a x v))
      rw [ClockFrameAut.pullbackFiber_mul]
      congr 1

@[simp] theorem selfCalibratingObservation_smul_difference
    (a : ClockFrameAut Event Tangent) (Q : SelfCalibratingObservation Event Tangent)
    (x : Event) : (a • Q).difference x = Q.difference (a.base⁻¹ x) := rfl

@[simp] theorem selfCalibratingObservation_smul_symbol
    (a : ClockFrameAut Event Tangent) (Q : SelfCalibratingObservation Event Tangent)
    (x : Event) (v : Tangent) :
    (a • Q).symbol x v = Q.symbol (a.base⁻¹ x) (ClockFrameAut.pullbackFiber a x v) := rfl

instance : MulAction (ClockFrameAut Event Tangent)
    (SelfCalibratingMetricField Event Tangent) where
  smul a g :=
    { calibration := fun x => g.calibration (a.base⁻¹ x)
      calibration_ne_zero := fun x => g.calibration_ne_zero _
      form := fun x =>
        (g.form (a.base⁻¹ x)).compl₁₂
          ((ClockFrameAut.pullbackFiber a x : Tangent ≃ₗ[ℝ] Tangent) : Tangent →ₗ[ℝ] Tangent)
          ((ClockFrameAut.pullbackFiber a x : Tangent ≃ₗ[ℝ] Tangent) : Tangent →ₗ[ℝ] Tangent)
      symmetric := by
        intro x u v
        simp only [LinearMap.compl₁₂_apply]
        exact g.symmetric _ _ _ }
  one_smul g := by
    refine SelfCalibratingMetricField.ext ?_ ?_
    · funext x
      show g.calibration ((1 : ClockFrameAut Event Tangent).base⁻¹ x) = g.calibration x
      simp
    · funext x
      apply LinearMap.ext
      intro u
      apply LinearMap.ext
      intro v
      show g.form ((1 : ClockFrameAut Event Tangent).base⁻¹ x)
          (ClockFrameAut.pullbackFiber 1 x u) (ClockFrameAut.pullbackFiber 1 x v) =
        g.form x u v
      rw [ClockFrameAut.pullbackFiber_one]
      simp
  mul_smul a b g := by
    refine SelfCalibratingMetricField.ext ?_ ?_
    · funext x
      show g.calibration ((a * b).base⁻¹ x) = g.calibration (b.base⁻¹ (a.base⁻¹ x))
      rw [ClockFrameAut.mul_base, mul_inv_rev]
      rfl
    · funext x
      apply LinearMap.ext
      intro u
      apply LinearMap.ext
      intro v
      show g.form ((a * b).base⁻¹ x) (ClockFrameAut.pullbackFiber (a * b) x u)
          (ClockFrameAut.pullbackFiber (a * b) x v) =
        g.form (b.base⁻¹ (a.base⁻¹ x))
          (ClockFrameAut.pullbackFiber b (a.base⁻¹ x) (ClockFrameAut.pullbackFiber a x u))
          (ClockFrameAut.pullbackFiber b (a.base⁻¹ x) (ClockFrameAut.pullbackFiber a x v))
      rw [ClockFrameAut.pullbackFiber_mul, ClockFrameAut.pullbackFiber_mul]
      congr 1

@[simp] theorem selfCalibratingMetricField_smul_calibration
    (a : ClockFrameAut Event Tangent) (g : SelfCalibratingMetricField Event Tangent)
    (x : Event) : (a • g).calibration x = g.calibration (a.base⁻¹ x) := rfl

@[simp] theorem selfCalibratingMetricField_smul_form
    (a : ClockFrameAut Event Tangent) (g : SelfCalibratingMetricField Event Tangent)
    (x : Event) (u v : Tangent) :
    (a • g).form x u v =
      g.form (a.base⁻¹ x) (ClockFrameAut.pullbackFiber a x u)
        (ClockFrameAut.pullbackFiber a x v) := rfl

/-- Complete two-mass observation as a frame-automorphism module element. -/
def twoMassObservationOf (massSq₁ massSq₂ : ℝ)
    (g : SelfCalibratingMetricField Event Tangent) :
    SelfCalibratingObservation Event Tangent :=
  ⟨fun x => (massSq₁ - massSq₂) * g.calibration x,
    fun x v => g.calibration x * g.form x v v⟩

theorem twoMassObservationOf_injective {massSq₁ massSq₂ : ℝ} (hmass : massSq₁ ≠ massSq₂) :
    Function.Injective
      (twoMassObservationOf massSq₁ massSq₂ :
        SelfCalibratingMetricField Event Tangent → SelfCalibratingObservation Event Tangent) := by
  intro g h hdata
  refine SelfCalibratingMetricField.twoMassObservation_injective hmass ?_
  exact Prod.ext (congrArg SelfCalibratingObservation.difference hdata)
    (congrArg SelfCalibratingObservation.symbol hdata)

/-- **The complete two-mass observation is equivariant for clock frame automorphisms.** -/
theorem twoMassObservationOf_equivariant (massSq₁ massSq₂ : ℝ)
    (a : ClockFrameAut Event Tangent) (g : SelfCalibratingMetricField Event Tangent) :
    twoMassObservationOf massSq₁ massSq₂ (a • g) =
      a • twoMassObservationOf massSq₁ massSq₂ g :=
  rfl

end FrameAction

/-- **Two-mass self-calibrating gravity-operator rigidity modulo frame automorphisms.**

Two arbitrary nonlinear gravity operators, equivariant under relabelling of events and linear
reframing of tangent fibers, have identical two-mass solution graphs on the orbit quotients exactly
when they agree pointwise up to a frame automorphism of the source labels. Unknown local detector
gain, conformal scale and nonlinear solution branches create no residual ambiguity beyond the
frame-automorphism equivalence. -/
theorem twoMassSelfCalibratingRigidity_mod_frameAut
    {Event : Type u} {Tangent : Type v} [AddCommGroup Tangent] [Module ℝ Tangent]
    {Source : Type w} [MulAction (ClockFrameAut Event Tangent) Source]
    {massSq₁ massSq₂ : ℝ} (hmass : massSq₁ ≠ massSq₂)
    {law₁ law₂ : SelfCalibratingMetricField Event Tangent → Source}
    (h₁ : ∀ (a : ClockFrameAut Event Tangent) (g : SelfCalibratingMetricField Event Tangent),
      law₁ (a • g) = a • law₁ g)
    (h₂ : ∀ (a : ClockFrameAut Event Tangent) (g : SelfCalibratingMetricField Event Tangent),
      law₂ (a • g) = a • law₂ g) :
    chronometricSolutionGraph
          (orbitQuotientMap (twoMassObservationOf massSq₁ massSq₂)
            (twoMassObservationOf_equivariant massSq₁ massSq₂))
          (orbitQuotientMap law₁ h₁) =
        chronometricSolutionGraph
          (orbitQuotientMap (twoMassObservationOf massSq₁ massSq₂)
            (twoMassObservationOf_equivariant massSq₁ massSq₂))
          (orbitQuotientMap law₂ h₂) ↔
      ∀ g : SelfCalibratingMetricField Event Tangent,
        ∃ a : ClockFrameAut Event Tangent, law₁ g = a • law₂ g :=
  chronometricSolutionGraph_orbitQuotient_eq_iff
    (twoMassObservationOf_equivariant massSq₁ massSq₂)
    (twoMassObservationOf_injective hmass) h₁ h₂

/-! ### The frame-automorphism quotient is strictly coarser than equality -/

section Nontriviality

variable {Event : Type u} {Tangent : Type v} [AddCommGroup Tangent] [Module ℝ Tangent]

/-- A conformal reframing rescales every calibrated symbol value by `c⁻²` and leaves the
calibration untouched. -/
theorem smul_scaling_selfCalibrating_form (c : ℝ) (hc : c ≠ 0)
    (g : SelfCalibratingMetricField Event Tangent) (x : Event) (u v : Tangent) :
    ((ClockFrameAut.scaling (Event := Event) (Tangent := Tangent) c hc) • g).form x u v =
      c⁻¹ * c⁻¹ * g.form x u v := by
  have hbase : (ClockFrameAut.scaling (Event := Event) (Tangent := Tangent) c hc).base⁻¹ x = x :=
    rfl
  rw [selfCalibratingMetricField_smul_form, ClockFrameAut.pullbackFiber_scaling,
    ClockFrameAut.pullbackFiber_scaling, hbase]
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
  ring

/-- **The action really moves self-calibrating fields.** Hence the quotient rigidity theorem is a
genuine weakening of equality to frame equivalence, not a restatement. -/
theorem smul_scaling_selfCalibrating_ne_self (c : ℝ) (hc : c ≠ 0) (hcsq : c⁻¹ * c⁻¹ ≠ 1)
    (g : SelfCalibratingMetricField Event Tangent) {x : Event} {u v : Tangent}
    (hg : g.form x u v ≠ 0) :
    (ClockFrameAut.scaling (Event := Event) (Tangent := Tangent) c hc) • g ≠ g := by
  intro hEq
  have hcomp :
      ((ClockFrameAut.scaling (Event := Event) (Tangent := Tangent) c hc) • g).form x u v =
        g.form x u v := by rw [hEq]
  rw [smul_scaling_selfCalibrating_form] at hcomp
  refine hcsq ?_
  have hfactor : (c⁻¹ * c⁻¹ - 1) * g.form x u v = 0 := by linarith
  rcases mul_eq_zero.mp hfactor with h | h
  · linarith [sub_eq_zero.mp h]
  · exact absurd h hg

end Nontriviality

end GaloisForLFunctions.HTGeometry
