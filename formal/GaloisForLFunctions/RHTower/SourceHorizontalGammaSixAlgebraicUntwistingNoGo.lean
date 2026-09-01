import GaloisForLFunctions.RHTower.SourceHorizontalGammaSixCovariantStokesFlat
import GaloisForLFunctions.RHTower.SourceGammaChannelResolvedNaturalityNoGo

/-!
# Algebraic untwisting no-go for the source Γ₆ local system

The literal Γ₆ cyclic character is flat for the covariant source differential `t - u`, whereas
fixed-source descent requires `t - 1`.  This file classifies every attempt to bridge that gap by
an automorphism of the existing real cyclic source algebra.

Intertwining the two differentials at the unit forces the generator image to be `t + (u - 1)`.
But `t` is a unit, while every nonzero scalar translate of `t` has a zero under a cyclic character
and therefore is not a unit.  Hence an algebra automorphism can untwist the differential only at
trivial holonomy.  For the physical Γ₆ holonomy, universal algebraic untwisting is exactly the
shared HB/FZZ-P/PW-B/RBH Ward endpoint and RH: it is a receiver, not a missing producer.
-/

open Complex

namespace RHTower

noncomputable section

/-- A real unit determines a multiplicative character of the infinite-cyclic Γ₆ source group. -/
def sourceHorizontalGammaSixCyclicUnitCharacter (x : ℝˣ) :
    SourceHorizontalGammaSixCyclicGroup →* ℝˣ where
  toFun g := x ^ deningerZVal sourceHorizontalGammaSixCyclicGroupEquiv g
  map_one' := by
    simp [deningerZVal]
  map_mul' g h := by
    change x ^ deningerZVal sourceHorizontalGammaSixCyclicGroupEquiv (g * h) = _
    rw [deningerZVal, map_mul]
    change x ^
      (Multiplicative.toAdd (sourceHorizontalGammaSixCyclicGroupEquiv g) +
        Multiplicative.toAdd (sourceHorizontalGammaSixCyclicGroupEquiv h)) = _
    rw [zpow_add]
    rfl

/-- Evaluation of the cyclic source algebra at a nonzero real character value. -/
def sourceHorizontalGammaSixCyclicEval (x : ℝˣ) :
    MonoidAlgebra ℝ SourceHorizontalGammaSixCyclicGroup →+* ℝ :=
  MonoidAlgebra.liftNCRingHom (RingHom.id ℝ)
    ((Units.coeHom ℝ).comp (sourceHorizontalGammaSixCyclicUnitCharacter x))
    (fun _ _ => Commute.all _ _)

@[simp] theorem sourceHorizontalGammaSixCyclicEval_single (x : ℝˣ)
    (g : SourceHorizontalGammaSixCyclicGroup) (c : ℝ) :
    sourceHorizontalGammaSixCyclicEval x (MonoidAlgebra.single g c) =
      c * (x : ℝ) ^ deningerZVal sourceHorizontalGammaSixCyclicGroupEquiv g := by
  rw [sourceHorizontalGammaSixCyclicEval, MonoidAlgebra.liftNCRingHom_single]
  simp [sourceHorizontalGammaSixCyclicUnitCharacter]

@[simp] theorem sourceHorizontalGammaSixCyclicEval_generator (x : ℝˣ) :
    sourceHorizontalGammaSixCyclicEval x
      (MonoidAlgebra.single
        (deningerZGen sourceHorizontalGammaSixCyclicGroupEquiv) 1) = x := by
  simp [sourceHorizontalGammaSixCyclicEval_single, deningerZGen, deningerZVal]

@[simp] theorem sourceHorizontalGammaSixCyclicEval_algebraMap (x : ℝˣ) (c : ℝ) :
    sourceHorizontalGammaSixCyclicEval x
      (algebraMap ℝ
        (MonoidAlgebra ℝ SourceHorizontalGammaSixCyclicGroup) c) = c := by
  change sourceHorizontalGammaSixCyclicEval x
    (MonoidAlgebra.single (1 : SourceHorizontalGammaSixCyclicGroup) c) = c
  simp [sourceHorizontalGammaSixCyclicEval_single, deningerZVal]

/-- The real source group algebra used by the Γ₆ covariant differential. -/
abbrev SourceHorizontalGammaSixSourceAlgebra :=
  MonoidAlgebra ℝ SourceHorizontalGammaSixCyclicGroup

/-- Distinguished cyclic generator `t` inside the source algebra. -/
def sourceHorizontalGammaSixSourceGenerator : SourceHorizontalGammaSixSourceAlgebra :=
  MonoidAlgebra.single
    (deningerZGen sourceHorizontalGammaSixCyclicGroupEquiv) 1

theorem sourceHorizontalGammaSixSourceGenerator_isUnit :
    IsUnit sourceHorizontalGammaSixSourceGenerator := by
  rw [isUnit_iff_exists]
  refine ⟨MonoidAlgebra.single
      (deningerZGen sourceHorizontalGammaSixCyclicGroupEquiv)⁻¹ 1, ?_, ?_⟩
  · change MonoidAlgebra.single
      (deningerZGen sourceHorizontalGammaSixCyclicGroupEquiv) 1 *
        MonoidAlgebra.single
          (deningerZGen sourceHorizontalGammaSixCyclicGroupEquiv)⁻¹ 1 = 1
    rw [MonoidAlgebra.single_mul_single]
    convert (MonoidAlgebra.one_def
      (R := ℝ) (M := SourceHorizontalGammaSixCyclicGroup)).symm using 1
    all_goals simp
  · change MonoidAlgebra.single
      (deningerZGen sourceHorizontalGammaSixCyclicGroupEquiv)⁻¹ 1 *
        MonoidAlgebra.single
          (deningerZGen sourceHorizontalGammaSixCyclicGroupEquiv) 1 = 1
    rw [MonoidAlgebra.single_mul_single]
    convert (MonoidAlgebra.one_def
      (R := ℝ) (M := SourceHorizontalGammaSixCyclicGroup)).symm using 1
    all_goals simp

/-- A nonzero scalar translate of `t` cannot be a source-algebra unit: evaluation at `t = -c`
kills it.  This is the invariant obstructing algebraic holonomy removal. -/
theorem sourceHorizontalGammaSixSourceGenerator_add_algebraMap_not_isUnit
    {c : ℝ} (hc : c ≠ 0) :
    ¬ IsUnit (sourceHorizontalGammaSixSourceGenerator +
      algebraMap ℝ SourceHorizontalGammaSixSourceAlgebra c) := by
  intro hunit
  let x : ℝˣ := Units.mk0 (-c) (neg_ne_zero.mpr hc)
  have himage := hunit.map (sourceHorizontalGammaSixCyclicEval x)
  have heval :
      sourceHorizontalGammaSixCyclicEval x
          (sourceHorizontalGammaSixSourceGenerator +
            algebraMap ℝ SourceHorizontalGammaSixSourceAlgebra c) = 0 := by
    rw [map_add, sourceHorizontalGammaSixCyclicEval_algebraMap]
    rw [show sourceHorizontalGammaSixSourceGenerator = MonoidAlgebra.single
      (deningerZGen sourceHorizontalGammaSixCyclicGroupEquiv) 1 from rfl,
      sourceHorizontalGammaSixCyclicEval_generator]
    simp [x]
  rw [heval] at himage
  exact not_isUnit_zero (show IsUnit (0 : ℝ) from himage)

/-- **Unit-translate classification.**  The translate `t+c` is a unit exactly when `c=0`. -/
theorem sourceHorizontalGammaSixSourceGenerator_add_algebraMap_isUnit_iff (c : ℝ) :
    IsUnit (sourceHorizontalGammaSixSourceGenerator +
      algebraMap ℝ SourceHorizontalGammaSixSourceAlgebra c) ↔ c = 0 := by
  constructor
  · intro hunit
    by_contra hc
    exact sourceHorizontalGammaSixSourceGenerator_add_algebraMap_not_isUnit hc hunit
  · rintro rfl
    simpa using sourceHorizontalGammaSixSourceGenerator_isUnit

/-- An algebraic untwisting is a source-algebra automorphism intertwining the covariant
`t-u` differential with the fixed `t-1` differential on every source chain. -/
def SourceHorizontalGammaSixAlgebraicUntwisting (u : ℝ) : Prop :=
  ∃ φ : SourceHorizontalGammaSixSourceAlgebra ≃ₐ[ℝ]
      SourceHorizontalGammaSixSourceAlgebra,
    ∀ f : SourceHorizontalGammaSixSourceAlgebra,
      φ (sourceHorizontalGammaSixHolonomyBoundary u f) =
        (deningerZBoundary sourceHorizontalGammaSixCyclicGroupEquiv ℝ).hom (φ f)

/-- **Algebraic untwisting rigidity.**  No automorphism of the existing source algebra removes
nontrivial holonomy. -/
theorem sourceHorizontalGammaSixAlgebraicUntwisting_iff (u : ℝ) :
    SourceHorizontalGammaSixAlgebraicUntwisting u ↔ u = 1 := by
  constructor
  · rintro ⟨φ, hφ⟩
    have hone := hφ 1
    have hfixed :
        (deningerZBoundary sourceHorizontalGammaSixCyclicGroupEquiv ℝ).hom
            (1 : SourceHorizontalGammaSixSourceAlgebra) =
          sourceHorizontalGammaSixSourceGenerator - 1 := by
      change (deningerZBoundary sourceHorizontalGammaSixCyclicGroupEquiv ℝ).hom
          (MonoidAlgebra.single (1 : SourceHorizontalGammaSixCyclicGroup) 1) = _
      rw [deningerZBoundary_single, one_smul]
      change MonoidAlgebra.single
          (deningerZGen sourceHorizontalGammaSixCyclicGroupEquiv) 1 -
            MonoidAlgebra.single 1 1 = sourceHorizontalGammaSixSourceGenerator - 1
      rw [← MonoidAlgebra.one_def]
      rfl
    have hsource :
        sourceHorizontalGammaSixHolonomyBoundary u
            (1 : SourceHorizontalGammaSixSourceAlgebra) =
          sourceHorizontalGammaSixSourceGenerator -
            algebraMap ℝ SourceHorizontalGammaSixSourceAlgebra u := by
      rw [sourceHorizontalGammaSixHolonomyBoundary_apply, hfixed,
        Algebra.smul_def, mul_one]
      rw [map_sub, map_one]
      abel
    rw [hsource, map_sub, map_one, φ.commutes, hfixed] at hone
    have hgenerator :
        φ sourceHorizontalGammaSixSourceGenerator =
          sourceHorizontalGammaSixSourceGenerator +
            algebraMap ℝ SourceHorizontalGammaSixSourceAlgebra (u - 1) := by
      rw [map_sub, map_one]
      calc
        φ sourceHorizontalGammaSixSourceGenerator =
            (φ sourceHorizontalGammaSixSourceGenerator -
                algebraMap ℝ SourceHorizontalGammaSixSourceAlgebra u) +
              algebraMap ℝ SourceHorizontalGammaSixSourceAlgebra u := by abel
        _ = (sourceHorizontalGammaSixSourceGenerator - 1) +
              algebraMap ℝ SourceHorizontalGammaSixSourceAlgebra u := by rw [hone]
        _ = sourceHorizontalGammaSixSourceGenerator +
              (algebraMap ℝ SourceHorizontalGammaSixSourceAlgebra u - 1) := by abel
    have hunit : IsUnit (φ sourceHorizontalGammaSixSourceGenerator) :=
      sourceHorizontalGammaSixSourceGenerator_isUnit.map φ.toRingEquiv
    rw [hgenerator] at hunit
    exact sub_eq_zero.mp
      ((sourceHorizontalGammaSixSourceGenerator_add_algebraMap_isUnit_iff
        (u - 1)).1 hunit)
  · rintro rfl
    refine ⟨AlgEquiv.refl, ?_⟩
    intro f
    simp [sourceHorizontalGammaSixHolonomyBoundary]

/-- Algebraic untwisting for the literal Xi-selected Γ₆ holonomy. -/
def SourceHorizontalGammaSixPhysicalAlgebraicUntwisting (q : XiZeroCopy) : Prop :=
  SourceHorizontalGammaSixAlgebraicUntwisting
    (sourceHorizontalGammaSixPhysicalHolonomy q)

theorem sourceHorizontalGammaSixPhysicalAlgebraicUntwisting_iff (q : XiZeroCopy) :
    SourceHorizontalGammaSixPhysicalAlgebraicUntwisting q ↔
      (q.1 : ℂ).re = 1 / 2 := by
  rw [SourceHorizontalGammaSixPhysicalAlgebraicUntwisting,
    sourceHorizontalGammaSixAlgebraicUntwisting_iff]
  rw [← sourceHorizontalGammaSixHolonomyBoundary_eq_deningerZBoundary_iff]
  exact sourceHorizontalGammaSixPhysicalCovariantBoundary_eq_fixed_iff q

/-- Universal algebraic untwisting of all Xi-selected Γ₆ source systems. -/
def EverySourceHorizontalGammaSixPhysicalAlgebraicUntwisting : Prop :=
  ∀ q : XiZeroCopy, SourceHorizontalGammaSixPhysicalAlgebraicUntwisting q

theorem everySourceHorizontalGammaSixPhysicalAlgebraicUntwisting_iff_riemannHypothesis :
    EverySourceHorizontalGammaSixPhysicalAlgebraicUntwisting ↔ RiemannHypothesis := by
  constructor
  · intro huntwist
    apply
      everySourceHorizontalGammaSixPhysicalCovariantBoundary_eq_fixed_iff_riemannHypothesis.mp
    intro q
    apply (sourceHorizontalGammaSixPhysicalCovariantBoundary_eq_fixed_iff q).2
    exact (sourceHorizontalGammaSixPhysicalAlgebraicUntwisting_iff q).1 (huntwist q)
  · intro hRH q
    apply (sourceHorizontalGammaSixPhysicalAlgebraicUntwisting_iff q).2
    exact xi_divisor_support_re_eq_half_of_rh hRH q.1

private theorem sharedFourRouteWardEndpoint_iff_riemannHypothesis_for_algebraicUntwisting :
    SharedFourRouteWardEndpoint ↔ RiemannHypothesis := by
  constructor
  · rintro ⟨hHB, _, _, _⟩
    exact (forall_normSq_hbXiPeierlsUnitSourceFECocycle_eq_one_iff_rh).1 hHB
  · intro hRH
    apply
      everyFrankensteinChannelResolvedGammaJointNaturality_iff_sharedFourRouteWardEndpoint.mp
    exact
      everyFrankensteinChannelResolvedGammaJointNaturality_iff_riemannHypothesis.mpr hRH

/-- Universal algebraic untwisting is exactly the common four-route Ward receiver. -/
theorem everySourceHorizontalGammaSixPhysicalAlgebraicUntwisting_iff_sharedFourRouteWardEndpoint :
    EverySourceHorizontalGammaSixPhysicalAlgebraicUntwisting ↔
      SharedFourRouteWardEndpoint := by
  rw [everySourceHorizontalGammaSixPhysicalAlgebraicUntwisting_iff_riemannHypothesis,
    sharedFourRouteWardEndpoint_iff_riemannHypothesis_for_algebraicUntwisting]

/-- **[SHARED-WARD ALGEBRAIC-UNTWISTING ROUTE-CLASS KILL].**  Every ℝ-algebra
reparametrization of the existing cyclic source is rigid: pointwise untwisting forces trivial
holonomy, and universal physical untwisting is exactly the shared Ward endpoint and RH. -/
theorem sourceHorizontalGammaSixAlgebraicUntwistingRouteKilled :
    (∀ u : ℝ, SourceHorizontalGammaSixAlgebraicUntwisting u ↔ u = 1) ∧
      (EverySourceHorizontalGammaSixPhysicalAlgebraicUntwisting ↔
        SharedFourRouteWardEndpoint) ∧
      (EverySourceHorizontalGammaSixPhysicalAlgebraicUntwisting ↔
        RiemannHypothesis) := by
  exact ⟨sourceHorizontalGammaSixAlgebraicUntwisting_iff,
    everySourceHorizontalGammaSixPhysicalAlgebraicUntwisting_iff_sharedFourRouteWardEndpoint,
    everySourceHorizontalGammaSixPhysicalAlgebraicUntwisting_iff_riemannHypothesis⟩

end

end RHTower
