import GaloisForLFunctions.HTGeometry.BohrHullGroup

/-!
# Comparing phase carriers built from different translation distances

The carrier of an almost periodic curve is the completion of the line under its translation
distance.  If one translation distance is uniformly controlled by another, the identity of the line
extends to a continuous map of carriers; if the control holds both ways, the two maps compose to the
identity on a dense set, hence everywhere, and each carrier map is injective.

This is how the carrier built from the restriction to a line and the carrier built from the strip
translates are identified: the line distance is dominated by the strip distance trivially, and
dominates it by the three-line theorem.
-/

open Filter Topology Metric Set

open scoped BoundedContinuousFunction

namespace GaloisForLFunctions

variable {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]

/-- A comparison of translation distances gives a continuous map of carriers over the line. -/
theorem exists_hull_map {f : ℝ →ᵇ E} {g : ℝ →ᵇ F}
    (hunif : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ s t : ℝ,
      dist (translateBC s g) (translateBC t g) < δ →
        dist (translateBC s f) (translateBC t f) < ε) :
    ∃ μ : BohrHull g → BohrHull f, Continuous μ ∧ ∀ t : ℝ, μ (bohrIota g t) = bohrIota f t := by
  have huc : UniformContinuous (fun t : BohrLine g => (BohrLine.of f t.val)) := by
    rw [Metric.uniformContinuous_iff]
    intro ε hε
    obtain ⟨δ, hδ, hδle⟩ := hunif ε hε
    refine ⟨δ, hδ, fun {s t} hst => ?_⟩
    have hs : dist (translateBC s.val g) (translateBC t.val g) < δ := hst
    have := hδle s.val t.val hs
    exact this
  refine ⟨UniformSpace.Completion.map (fun t : BohrLine g => (BohrLine.of f t.val)),
    UniformSpace.Completion.continuous_map, fun t => ?_⟩
  show UniformSpace.Completion.map (fun t : BohrLine g => (BohrLine.of f t.val))
      ((BohrLine.of g t : BohrLine g) : BohrHull g) = bohrIota f t
  rw [UniformSpace.Completion.map_coe huc]
  rfl

/-- **Carriers compared in both directions are isomorphic.**  Two carrier maps over the identity of
the line compose to the identity, so each is injective. -/
theorem injective_of_hull_maps {f : ℝ →ᵇ E} {g : ℝ →ᵇ F}
    {μ : BohrHull g → BohrHull f} (hμ : Continuous μ)
    (hμι : ∀ t : ℝ, μ (bohrIota g t) = bohrIota f t)
    {ν : BohrHull f → BohrHull g} (hν : Continuous ν)
    (hνι : ∀ t : ℝ, ν (bohrIota f t) = bohrIota g t) :
    Function.Injective ν := by
  have hid : ∀ x : BohrHull f, μ (ν x) = x := by
    intro x
    have h1 : Continuous (fun x : BohrHull f => μ (ν x)) := hμ.comp hν
    have h2 : Continuous (fun x : BohrHull f => x) := continuous_id
    refine congrFun (Continuous.ext_on (denseRange_bohrIota f) h1 h2 ?_) x
    rintro y ⟨t, rfl⟩
    show μ (ν (bohrIota f t)) = bohrIota f t
    rw [hνι t, hμι t]
  intro x y hxy
  have h := congrArg μ hxy
  rw [hid x, hid y] at h
  exact h

end GaloisForLFunctions
