import GaloisForLFunctions.RHTower.Deninger.DeningerBaumslagDegreeOne

/-!
# The rationalization of a free group is projective for uniquely divisible surjections

A surjection onto `Bau(F)` from a group with unique roots always splits when `F` is free: lift the
free generators arbitrarily, extend over the rationalization by its universal property, and the
composite with the surjection is the identity because it agrees with the identity on the generators.

Two consequences.  A central extension of `Bau(F)` whose kernel has unique roots again has unique
roots, so such an extension splits — which is the vanishing of second cohomology with rational
coefficients, in the form that classifies central extensions.

* `deningerUniquelyDivisible_of_central` : a central extension of a group with unique roots by a
  subgroup with unique roots again has unique roots.
* `deningerBauFree_projective` : the splitting.
* `deningerBauFree_centralExtension_splits` : every central extension by a uniquely divisible
  kernel splits.
-/

namespace RHTower

section RationalProjective

universe u w

variable {E : Type w} {G : Type u} [Group E] [Group G]

/-- **A central extension of a group with unique roots by a subgroup with unique roots again has
unique roots.**  The root is corrected by a central root of the discrepancy, and uniqueness comes
from uniqueness downstairs together with torsion-freeness of the kernel. -/
theorem deningerUniquelyDivisible_of_central (π : E →* G) (hπ : Function.Surjective π)
    (hG : DeningerUniquelyDivisible G)
    (hker : DeningerUniquelyDivisible (π.ker : Subgroup E))
    (hcentral : π.ker ≤ Subgroup.center E) :
    DeningerUniquelyDivisible E := by
  intro n hn e
  obtain ⟨g, hg, hguniq⟩ := hG n hn (π e)
  obtain ⟨h, rfl⟩ := hπ g
  have hk : e⁻¹ * h ^ n ∈ π.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, map_pow, hg, inv_mul_cancel]
  obtain ⟨κ, hκ, -⟩ := hker n hn ⟨e⁻¹ * h ^ n, hk⟩
  have hκval : (κ : E) ^ n = e⁻¹ * h ^ n := congrArg Subtype.val hκ
  have hcen : Commute h (κ : E) := Subgroup.mem_center_iff.1 (hcentral κ.2) h
  have hcomm : Commute h ((κ : E)⁻¹) := hcen.inv_right
  have hx : (h * (κ : E)⁻¹) ^ n = e := by
    rw [hcomm.mul_pow, inv_pow, hκval, mul_inv_rev, inv_inv, ← mul_assoc,
      mul_inv_cancel, one_mul]
  refine ⟨h * (κ : E)⁻¹, hx, ?_⟩
  intro y hy
  have hy' : y ^ n = e := hy
  have hpi : π y = π (h * (κ : E)⁻¹) := by
    refine (hguniq (π y) ?_).trans (hguniq (π (h * (κ : E)⁻¹)) ?_).symm
    · show π y ^ n = π e
      rw [← map_pow, hy']
    · show π (h * (κ : E)⁻¹) ^ n = π e
      rw [← map_pow, hx]
  have hc : (h * (κ : E)⁻¹)⁻¹ * y ∈ π.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hpi, inv_mul_cancel]
  set c : E := (h * (κ : E)⁻¹)⁻¹ * y with hcdef
  have hccomm : Commute (h * (κ : E)⁻¹) c :=
    Subgroup.mem_center_iff.1 (hcentral hc) (h * (κ : E)⁻¹)
  have hyc : y = (h * (κ : E)⁻¹) * c := by
    rw [hcdef, mul_inv_cancel_left]
  have hcn : c ^ n = 1 := by
    rw [hyc, hccomm.mul_pow, hx] at hy'
    exact mul_left_cancel (a := e) (by rw [mul_one]; exact hy')
  have hcone : c = 1 := by
    obtain ⟨z, -, huniq⟩ := hker n hn 1
    have h1 : (⟨c, hc⟩ : (π.ker : Subgroup E)) = z :=
      huniq _ (Subtype.ext (by simpa using hcn))
    have h2 : (1 : (π.ker : Subgroup E)) = z := huniq 1 (by simp)
    exact congrArg Subtype.val (h1.trans h2.symm)
  calc y = (h * (κ : E)⁻¹) * c := hyc
    _ = (h * (κ : E)⁻¹) * 1 := by rw [hcone]
    _ = h * (κ : E)⁻¹ := mul_one _

variable {ι : Type u}

/-- **The rationalization of a free group is projective for surjections from groups with unique
roots.**  Lift the free generators, extend over the rationalization, and compare with the identity
on the generators. -/
theorem deningerBauFree_projective (hE : DeningerUniquelyDivisible E)
    (π : E →* DeningerBau (FreeGroup ι)) (hπ : Function.Surjective π) :
    ∃ s : DeningerBau (FreeGroup ι) →* E, π.comp s = MonoidHom.id _ := by
  classical
  choose e he using fun i : ι => hπ (DeningerBau.of (FreeGroup.of i))
  have hbase : ∀ a : FreeGroup ι,
      (π.comp (deningerBauLift hE (FreeGroup.lift e))) (DeningerBau.of a) =
        (DeningerBau.of : FreeGroup ι →* DeningerBau (FreeGroup ι)) a := by
    have hgen : π.comp (FreeGroup.lift e) =
        (DeningerBau.of : FreeGroup ι →* DeningerBau (FreeGroup ι)) := by
      refine FreeGroup.ext_hom _ _ fun i => ?_
      show π (FreeGroup.lift e (FreeGroup.of i)) = _
      rw [FreeGroup.lift_apply_of]
      exact he i
    intro a
    show π (deningerBauLift hE (FreeGroup.lift e) (DeningerBau.of a)) = _
    rw [deningerBauLift_of]
    exact DFunLike.congr_fun hgen a
  refine ⟨deningerBauLift hE (FreeGroup.lift e), ?_⟩
  have h1 := deningerBauLift_unique DeningerBau.uniquelyDivisible
    (DeningerBau.of : FreeGroup ι →* DeningerBau (FreeGroup ι))
    (π.comp (deningerBauLift hE (FreeGroup.lift e))) hbase
  have h2 := deningerBauLift_unique DeningerBau.uniquelyDivisible
    (DeningerBau.of : FreeGroup ι →* DeningerBau (FreeGroup ι)) (MonoidHom.id _) (fun _ => rfl)
  exact h1.trans h2.symm

/-- **Every central extension of the rationalization of a free group with a uniquely divisible
kernel splits.**  This is the vanishing of second cohomology with rational coefficients, in the
form in which second cohomology classifies central extensions. -/
theorem deningerBauFree_centralExtension_splits
    (π : E →* DeningerBau (FreeGroup ι)) (hπ : Function.Surjective π)
    (hker : DeningerUniquelyDivisible (π.ker : Subgroup E))
    (hcentral : π.ker ≤ Subgroup.center E) :
    ∃ s : DeningerBau (FreeGroup ι) →* E, π.comp s = MonoidHom.id _ :=
  deningerBauFree_projective
    (deningerUniquelyDivisible_of_central π hπ DeningerBau.uniquelyDivisible hker hcentral) π hπ

end RationalProjective

end RHTower
