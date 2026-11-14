import GaloisForLFunctions.RepresentationLifting.CyclicLocalTrace
import GaloisForLFunctions.RepresentationLifting.TraceRestrictionCriterion

/-!
# A globally nonsplit extension invisible on cyclic subgroups

For every odd prime `p`, the cyclic norm construction gives a short exact
self-extension of a `2p`-dimensional `F_p[C_p × C_p]`-module with middle
dimension `4p`. It splits on every cyclic subgroup but not on the whole group.

The lines are indexed by `Option (ZMod p)`, with `none` denoting the additive
axis. Their retraction traces are zero on finite slopes and two on the axis.
The resulting ordinary-cohomology restriction profile holds in every degree:
a scalar class killed by the differential produces one trace class with these
prescribed restrictions. No continuous-cohomology comparison is asserted.
-/

noncomputable section
open CategoryTheory
namespace GaloisForLFunctions.RepresentationLifting

variable (p : ℕ) [Fact p.Prime]


/-- The finite-slope lines and the additive axis in the prime plane. -/
def primePlaneLine (a : Option (ZMod p)) :
    Multiplicative (ZMod p) →* Multiplicative (ZMod p) × Multiplicative (ZMod p) :=
  match a with
  | none => MonoidHom.inr _ _
  | some b => cyclicGraphHom (ZMod p) (Multiplicative (ZMod p)) (cyclicSlopeCharacter (ZMod p) b)

/-- A coordinate left inverse to each parameterized line embedding. -/
def primePlaneLineProjection (a : Option (ZMod p)) :
    Multiplicative (ZMod p) × Multiplicative (ZMod p) →* Multiplicative (ZMod p) :=
  match a with
  | none => MonoidHom.snd _ _
  | some _ => MonoidHom.fst _ _

/-- The retraction trace: two on the additive axis and zero on every finite slope. -/
def primePlaneTraceWeight : Option (ZMod p) → ZMod p
  | none => 2
  | some _ => 0

/-- Each line parameter gives an injective group homomorphism. -/
theorem primePlaneLine_injective (a : Option (ZMod p)) : Function.Injective (primePlaneLine p a) := by
  intro x y h
  cases a with
  | none => exact congrArg Prod.snd h
  | some b => exact congrArg Prod.fst h

/-- Every point lies on a parameterized line, with its coordinate projection as preimage. -/
theorem primePlaneLine_covers_point (x : Multiplicative (ZMod p) × Multiplicative (ZMod p)) :
    ∃ a : Option (ZMod p), primePlaneLine p a (primePlaneLineProjection p a x) = x := by
  by_cases hx : x.1.toAdd = 0
  · refine ⟨none, ?_⟩
    apply Prod.ext
    · exact congrArg Multiplicative.ofAdd hx.symm
    · rfl
  · refine ⟨some (x.2.toAdd / x.1.toAdd), ?_⟩
    apply Prod.ext
    · rfl
    · exact congrArg Multiplicative.ofAdd (div_mul_cancel₀ x.2.toAdd hx)

/-- Every cyclic subgroup inclusion factors through one of the parameterized lines. -/
theorem primePlaneLine_factors_cyclic
    (H : Subgroup (Multiplicative (ZMod p) × Multiplicative (ZMod p))) [IsCyclic H] :
    ∃ (a : Option (ZMod p)) (f : H →* Multiplicative (ZMod p)),
      (primePlaneLine p a).comp f = H.subtype := by
  obtain ⟨a, ha⟩ := primePlaneLine_covers_point p (H.subtype (cyclicRegularGenerator H))
  refine ⟨a, (primePlaneLineProjection p a).comp H.subtype, ?_⟩
  apply MonoidHom.ext
  intro x
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp (cyclicRegularGenerator_generates H x)
  change primePlaneLine p a (primePlaneLineProjection p a (H.subtype (cyclicRegularGenerator H ^ n))) =
    H.subtype (cyclicRegularGenerator H ^ n)
  rw [map_zpow, map_zpow, map_zpow, ha]

theorem primePlane_groupOrder_zero : (Fintype.card (Multiplicative (ZMod p)) : ZMod p) = 0 := by
  simpa only [Fintype.card_multiplicative, ZMod.card] using CharP.cast_eq_zero (ZMod p) p

/-- The odd-prime self-extension splits on every parameterized line. -/
theorem primePlaneSelfExtension_line_splits (hp : p ≠ 2) (a : Option (ZMod p)) :
    ∃ r : Rep.res (primePlaneLine p a) (primePlaneSelfExtension p).X₂ ⟶
        Rep.res (primePlaneLine p a) (primePlaneSelfExtension p).X₁,
      (Rep.resFunctor (primePlaneLine p a)).map (primePlaneSelfExtension p).f ≫ r = 𝟙 _ := by
  cases a with
  | none => exact cyclicSelfExtension_infinity_splits (ZMod p) (Multiplicative (ZMod p))
  | some b =>
      exact cyclicSelfExtension_graph_splits (ZMod p) (Multiplicative (ZMod p))
        (primeField_two_ne_zero p hp) (cyclicSlopeCharacter (ZMod p) b)

/-- The trace profile is independent of the chosen equivariant retraction. -/
theorem primePlaneSelfExtension_line_trace (hp : p ≠ 2) (a : Option (ZMod p))
    (r : Rep.res (primePlaneLine p a) (primePlaneSelfExtension p).X₂ ⟶
      Rep.res (primePlaneLine p a) (primePlaneSelfExtension p).X₁)
    (hr : (Rep.resFunctor (primePlaneLine p a)).map (primePlaneSelfExtension p).f ≫ r = 𝟙 _) :
    LinearMap.trace (ZMod p) (CyclicDetector (ZMod p) (Multiplicative (ZMod p)))
      (((Rep.resFunctor (primePlaneLine p a)).map
        (cyclicSelfExtensionLift (ZMod p) (Multiplicative (ZMod p))) ≫ r).hom.toLinearMap) =
      primePlaneTraceWeight p a := by
  cases a with
  | none => exact cyclicSelfExtension_infinity_trace (ZMod p) (Multiplicative (ZMod p)) r hr
  | some b =>
      exact cyclicSelfExtension_graph_trace (ZMod p) (Multiplicative (ZMod p))
        (primeField_two_ne_zero p hp) (primePlane_groupOrder_zero p)
        (cyclicSlopeCharacter (ZMod p) b) r

/-- Every cyclic subgroup misses the global obstruction to splitting. -/
theorem primePlaneSelfExtension_cyclic_splits (hp : p ≠ 2)
    (H : Subgroup (Multiplicative (ZMod p) × Multiplicative (ZMod p))) [IsCyclic H] :
    ∃ r : Rep.res H.subtype (primePlaneSelfExtension p).X₂ ⟶
        Rep.res H.subtype (primePlaneSelfExtension p).X₁,
      (Rep.resFunctor H.subtype).map (primePlaneSelfExtension p).f ≫ r = 𝟙 _ := by
  obtain ⟨a, f, hf⟩ := primePlaneLine_factors_cyclic p H
  obtain ⟨r, hr⟩ := primePlaneSelfExtension_line_splits p hp a
  let rH : Rep.res H.subtype (primePlaneSelfExtension p).X₂ ⟶
      Rep.res H.subtype (primePlaneSelfExtension p).X₁ := Rep.ofHom ⟨r.hom.toLinearMap, fun h => by
    apply LinearMap.ext
    intro v
    have hc := Rep.hom_comm_apply r (f h) v
    change r.hom (((primePlaneSelfExtension p).X₂).ρ (primePlaneLine p a (f h)) v) =
      ((primePlaneSelfExtension p).X₁).ρ (primePlaneLine p a (f h)) (r.hom v) at hc
    have hh : primePlaneLine p a (f h) = H.subtype h := congrArg (fun j => j h) hf
    rw [hh] at hc
    exact hc⟩
  refine ⟨rH, ?_⟩
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  exact congrArg (fun m => m.hom.toLinearMap) hr

/-- The odd-prime self-extension has no global equivariant retraction. -/
theorem primePlaneSelfExtension_not_split (hp : p ≠ 2) :
    ¬ ∃ r : (primePlaneSelfExtension p).X₂ ⟶ (primePlaneSelfExtension p).X₁,
      (primePlaneSelfExtension p).f ≫ r = 𝟙 _ :=
  cyclicSelfExtension_not_split (ZMod p) (Multiplicative (ZMod p))
    (primeField_two_ne_zero p hp) (primePlane_groupOrder_zero p)

/-- A scalar class killed by the differential has a trace class with the prescribed line restrictions. -/
theorem primePlane_cohomology_trace_profile (hp : p ≠ 2) (n : ℕ)
    (b : groupCohomology
      (Rep.trivial (ZMod p) (Multiplicative (ZMod p) × Multiplicative (ZMod p)) (ZMod p)) n)
    (hb : ((groupCohomology.functor (ZMod p)
      (Multiplicative (ZMod p) × Multiplicative (ZMod p)) n).map
        (scalarHom (cyclicDifferentialHom (ZMod p) (Multiplicative (ZMod p))))).hom b = 0) :
    ∃ γ : groupCohomology
        (Rep.trivial (ZMod p) (Multiplicative (ZMod p) × Multiplicative (ZMod p)) (ZMod p)) n,
      ∀ a : Option (ZMod p),
        ((groupCohomology.resNatTrans (ZMod p) (primePlaneLine p a) n).app
          (Rep.trivial (ZMod p) (Multiplicative (ZMod p) × Multiplicative (ZMod p)) (ZMod p))).hom γ =
        primePlaneTraceWeight p a •
          ((groupCohomology.resNatTrans (ZMod p) (primePlaneLine p a) n).app
            (Rep.trivial (ZMod p) (Multiplicative (ZMod p) × Multiplicative (ZMod p)) (ZMod p))).hom b := by
  have hb' : ((groupCohomology.functor (ZMod p)
      (Multiplicative (ZMod p) × Multiplicative (ZMod p)) n).map
        (scalarHom (cyclicSelfExtensionLift (ZMod p) (Multiplicative (ZMod p)) ≫
          (primePlaneSelfExtension p).g))).hom b = 0 := by
    change ((groupCohomology.functor (ZMod p)
      (Multiplicative (ZMod p) × Multiplicative (ZMod p)) n).map
        (scalarHom (cyclicSelfExtensionLift (ZMod p) (Multiplicative (ZMod p)) ≫
          cyclicSelfExtensionProjection (ZMod p) (Multiplicative (ZMod p))))).hom b = 0
    rw [cyclicSelfExtension_lift_projection]
    exact hb
  obtain ⟨γ, hγ⟩ := shortExact_cohomologyTrace_pullback (primePlaneSelfExtension p)
    (primePlaneSelfExtension_shortExact p)
    (cyclicSelfExtensionLift (ZMod p) (Multiplicative (ZMod p))) n b hb'
  refine ⟨γ, ?_⟩
  intro a
  obtain ⟨r, hr⟩ := primePlaneSelfExtension_line_splits p hp a
  have h := hγ (Multiplicative (ZMod p)) (primePlaneLine p a) r hr
  have ht : LinearMap.trace (ZMod p) (primePlaneSelfExtension p).X₁
      (((Rep.resFunctor (primePlaneLine p a)).map
        (cyclicSelfExtensionLift (ZMod p) (Multiplicative (ZMod p))) ≫ r).hom.toLinearMap) =
      primePlaneTraceWeight p a :=
    primePlaneSelfExtension_line_trace p hp a r hr
  exact h.trans (congrArg (fun c : ZMod p => c •
    ((groupCohomology.resNatTrans (ZMod p) (primePlaneLine p a) n).app
      (Rep.trivial (ZMod p) (Multiplicative (ZMod p) × Multiplicative (ZMod p)) (ZMod p))).hom b) ht)

end GaloisForLFunctions.RepresentationLifting

#print axioms GaloisForLFunctions.RepresentationLifting.primePlaneSelfExtension_cyclic_splits
#print axioms GaloisForLFunctions.RepresentationLifting.primePlaneSelfExtension_not_split
#print axioms GaloisForLFunctions.RepresentationLifting.primePlaneSelfExtension_line_trace
#print axioms GaloisForLFunctions.RepresentationLifting.primePlane_cohomology_trace_profile
