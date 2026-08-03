import GaloisForLFunctions.RHTower.DeningerBauCohomologyCriterion

/-!
# Unique roots in a product

A product of groups with unique roots has unique roots, componentwise.  This is one of the few
constructions that preserves the property, and so one of the few ways to build a group to feed to
the criterion for the packet's cohomology.

* `deningerUniquelyDivisible_prod` : the binary product.
* `deningerUniquelyDivisible_pi` : an arbitrary product.
-/

namespace RHTower

universe u

variable {E F : Type u} [Group E] [Group F]

/-- **A product of groups with unique roots has unique roots.** -/
theorem deningerUniquelyDivisible_prod (hE : DeningerUniquelyDivisible E)
    (hF : DeningerUniquelyDivisible F) : DeningerUniquelyDivisible (E × F) := by
  intro n hn x
  obtain ⟨a, ha, hauniq⟩ := hE n hn x.1
  obtain ⟨b, hb, hbuniq⟩ := hF n hn x.2
  refine ⟨(a, b), ?_, ?_⟩
  · exact Prod.ext (by simpa using ha) (by simpa using hb)
  · intro y hy
    have h1 : y.1 ^ n = x.1 := congrArg Prod.fst hy
    have h2 : y.2 ^ n = x.2 := congrArg Prod.snd hy
    exact Prod.ext (hauniq y.1 h1) (hbuniq y.2 h2)

/-- **An arbitrary product of groups with unique roots has unique roots.** -/
theorem deningerUniquelyDivisible_pi {ι : Type u} {E : ι → Type u} [∀ i, Group (E i)]
    (hE : ∀ i, DeningerUniquelyDivisible (E i)) :
    DeningerUniquelyDivisible (∀ i, E i) := by
  classical
  intro n hn x
  choose a ha hauniq using fun i => hE i n hn (x i)
  refine ⟨a, funext (fun i => ?_), fun y hy => funext (fun i => ?_)⟩
  · exact ha i
  · exact hauniq i (y i) (congrFun hy i)

end RHTower
