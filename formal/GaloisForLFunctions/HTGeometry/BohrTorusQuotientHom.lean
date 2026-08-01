import GaloisForLFunctions.HTGeometry.BohrHullTorusQuotient

/-!
# The torus quotient is a surjective homomorphism

The joint character map attached to a finite frequency packet is multiplicative coordinatewise, so
for a `ℚ`-independent packet of hull frequencies it is a continuous surjective homomorphism of the
phase carrier onto the `r`-torus.

This is the statement the dimension step consumes: the carrier of a function with `r` rationally
independent frequencies covers `𝕋^r` as a topological group.
-/

open Filter Topology

open scoped BoundedContinuousFunction

namespace GaloisForLFunctions

open HTGeometry

noncomputable section

variable {f : ℝ →ᵇ ℂ}

/-- The joint character map is coordinatewise multiplicative. -/
theorem bohrHullCharPacket_add {ι : Type*} {lam : ι → ℝ}
    (hne : ∀ j, IsBohrHullFrequency f (lam j)) (x y : BohrHull f) (j : ι) :
    bohrHullCharPacket f lam (x + y) j
      = bohrHullCharPacket f lam x j * bohrHullCharPacket f lam y j :=
  bohrHullChar_add (hne j) x y

/-- Each coordinate of the joint character map has modulus one. -/
theorem norm_bohrHullCharPacket {ι : Type*} {lam : ι → ℝ}
    (hne : ∀ j, IsBohrHullFrequency f (lam j)) (x : BohrHull f) (j : ι) :
    ‖bohrHullCharPacket f lam x j‖ = 1 :=
  norm_bohrHullChar (hne j) x

/-- **The phase carrier surjects onto the torus of an independent frequency packet, as a
homomorphism.** -/
theorem bohrHull_torus_surjective_hom (htb : HasTotallyBoundedOrbit (fun x => f x))
    {ι : Type*} [Fintype ι] [DecidableEq ι] {lam : ι → ℝ} (hind : LinearIndependent ℚ lam)
    (hne : ∀ j, IsBohrHullFrequency f (lam j)) :
    (∀ x y : BohrHull f, ∀ j : ι, bohrHullCharPacket f lam (x + y) j
        = bohrHullCharPacket f lam x j * bohrHullCharPacket f lam y j) ∧
      (∀ x : BohrHull f, ∀ j : ι, ‖bohrHullCharPacket f lam x j‖ = 1) ∧
      (∀ z : ι → ℂ, (∀ j, ‖z j‖ = 1) →
        ∃ x : BohrHull f, ∀ j : ι, bohrHullCharPacket f lam x j = z j) := by
  refine ⟨fun x y j => bohrHullCharPacket_add hne x y j,
    fun x j => norm_bohrHullCharPacket hne x j, fun z hz => ?_⟩
  exact exists_bohrHull_charPacket_eq_of_norm_one htb hind hne z hz

end

end GaloisForLFunctions
