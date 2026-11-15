import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.SetTheory.Cardinal.Finite

/-!
# Fixed points in a quotient by a normalized free action

If `C` normalizes `S`, a transporter in `S` between two `C`-fixed points
centralizes `C` whenever the action of `S` is free at the source. Thus
the relative centralizer describes exactly which fixed points coalesce
in the orbit quotient. A trivial relative centralizer gives injectivity,
also when `S` has one exceptional fixed point and is free elsewhere.
This is the group-action mechanism in Lemma 5.3 of Hu–Ma–Wang,
*New families of maximal curves not covered by the Hermitian curve
and their cyclic automorphism groups*.
-/

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
variable {G X : Type*} [Group G] [MulAction G X]

/-- Normalization makes the action on `S`-orbits well-defined. -/
@[reducible] def normalizedOrbitAction (C S : Subgroup G)
    (hnorm : C ≤ Subgroup.normalizer (S : Set G)) :
    MulAction C (Quotient (MulAction.orbitRel S X)) where
  smul c := Quotient.map' (fun x : X => (c : G) • x) (by
    intro x y hxy
    obtain ⟨s, hs⟩ := hxy
    refine ⟨⟨(c : G) * s * (c : G)⁻¹,
      ((Subgroup.mem_normalizer_iff.mp (hnorm c.property)) s).mp s.property⟩, ?_⟩
    change ((c : G) * s * (c : G)⁻¹) • ((c : G) • y) = (c : G) • x
    rw [mul_smul, inv_smul_smul, mul_smul]
    exact congrArg (fun z : X => (c : G) • z) hs)
  one_smul q := Quotient.inductionOn q (fun x => by
    change Quotient.mk _ ((1 : G) • x) = Quotient.mk _ x
    rw [one_smul])
  mul_smul c d q := Quotient.inductionOn q (fun x => by
    change Quotient.mk _ (((c : G) * (d : G)) • x) =
      Quotient.mk _ ((c : G) • ((d : G) • x))
    rw [mul_smul])

/-- Fixed points for the induced action on the orbit quotient. -/
def normalizedQuotientFixedPoints (C S : Subgroup G)
    (hnorm : C ≤ Subgroup.normalizer (S : Set G)) :
    Set (Quotient (MulAction.orbitRel S X)) :=
  letI := normalizedOrbitAction (X := X) C S hnorm
  MulAction.fixedPoints C (Quotient (MulAction.orbitRel S X))

/-- A fixed point upstairs maps to a fixed point of the induced quotient action. -/
def fixedPointDescent (C S : Subgroup G)
    (hnorm : C ≤ Subgroup.normalizer (S : Set G)) :
    MulAction.fixedPoints C X → normalizedQuotientFixedPoints (X := X) C S hnorm :=
  fun x => ⟨Quotient.mk _ (x : X), fun c =>
    congrArg (Quotient.mk (MulAction.orbitRel S X)) (x.property c)⟩

private theorem eq_of_free_smul (S : Subgroup G) (x : X)
    (hfree : ∀ s ∈ S, s • x = x → s = 1)
    {s t : G} (hs : s ∈ S) (ht : t ∈ S) (he : s • x = t • x) : s = t := by
  apply inv_mul_eq_one.mp
  apply hfree (s⁻¹ * t) (S.mul_mem (S.inv_mem hs) ht)
  rw [mul_smul, ← he, inv_smul_smul]

/-- A transporter between fixed points must centralize the normalizing subgroup. -/
theorem fixed_point_transporter_centralizes (C S : Subgroup G)
    (hnorm : C ≤ Subgroup.normalizer (S : Set G)) {x y : X}
    (hx : x ∈ MulAction.fixedPoints C X) (hy : y ∈ MulAction.fixedPoints C X)
    (hfree : ∀ s ∈ S, s • x = x → s = 1)
    {s : G} (hs : s ∈ S) (hxy : s • x = y) :
    s ∈ Subgroup.centralizer (C : Set G) := by
  apply Subgroup.mem_centralizer_iff.mpr
  intro c hc
  have hmem : c * s * c⁻¹ ∈ S :=
    ((Subgroup.mem_normalizer_iff.mp (hnorm hc)) s).mp hs
  have he : (c * s * c⁻¹) • x = s • x := by
    rw [mul_smul, mul_smul]
    have hi : c⁻¹ • x = x := hx ⟨c⁻¹, C.inv_mem hc⟩
    rw [hi, hxy]
    exact hy ⟨c, hc⟩
  exact mul_inv_eq_iff_eq_mul.mp (eq_of_free_smul S x hfree hmem hs he)

/-- Relative-centralizer orbits classify collisions of fixed points in the quotient. -/
theorem fixed_point_orbit_iff_centralizer_orbit (C S : Subgroup G)
    (hnorm : C ≤ Subgroup.normalizer (S : Set G)) {x y : X}
    (hx : x ∈ MulAction.fixedPoints C X) (hy : y ∈ MulAction.fixedPoints C X)
    (hfree : ∀ s ∈ S, s • x = x → s = 1) :
    y ∈ MulAction.orbit S x ↔
      y ∈ MulAction.orbit ↥(S ⊓ Subgroup.centralizer (C : Set G)) x := by
  constructor
  · rintro ⟨s, hs⟩
    exact ⟨⟨s, s.property, fixed_point_transporter_centralizes C S hnorm hx hy
      hfree s.property hs⟩, hs⟩
  · rintro ⟨s, hs⟩
    exact ⟨⟨s, s.property.1⟩, hs⟩

/-- A trivial relative centralizer separates fixed points wherever the quotient action is free. -/
theorem fixed_points_quotient_injective (C S : Subgroup G)
    (hnorm : C ≤ Subgroup.normalizer (S : Set G))
    (hcent : S ⊓ Subgroup.centralizer (C : Set G) = ⊥)
    (hfree : ∀ x ∈ MulAction.fixedPoints C X, ∀ s ∈ S, s • x = x → s = 1) :
    Function.Injective (fun x : MulAction.fixedPoints C X =>
      Quotient.mk (MulAction.orbitRel S X) (x : X)) := by
  intro x y he
  obtain ⟨s, hs⟩ := Quotient.exact he
  have hc := fixed_point_transporter_centralizes C S hnorm y.property x.property
    (hfree y y.property) s.property hs
  have hone : (s : G) = 1 := by
    apply Subgroup.mem_bot.mp
    rw [← hcent]
    exact ⟨s.property, hc⟩
  apply Subtype.ext
  change (s : G) • (y : X) = (x : X) at hs
  rw [hone, one_smul] at hs
  exact hs.symm

/-- One globally fixed exceptional point does not spoil fixed-point separation. -/
theorem fixed_points_quotient_injective_of_free_away (C S : Subgroup G)
    (hnorm : C ≤ Subgroup.normalizer (S : Set G))
    (hcent : S ⊓ Subgroup.centralizer (C : Set G) = ⊥)
    (P : X) (hP : P ∈ MulAction.fixedPoints S X)
    (hfree : ∀ x, x ≠ P → ∀ s ∈ S, s • x = x → s = 1) :
    Function.Injective (fun x : MulAction.fixedPoints C X =>
      Quotient.mk (MulAction.orbitRel S X) (x : X)) := by
  intro x y he
  obtain ⟨s, hs⟩ := Quotient.exact he
  apply Subtype.ext
  by_cases hy : (y : X) = P
  · change (s : G) • (y : X) = (x : X) at hs
    have hPs : (s : G) • P = P := hP s
    rw [hy, hPs] at hs
    exact hs.symm.trans hy.symm
  · have hc := fixed_point_transporter_centralizes C S hnorm y.property x.property
      (hfree y hy) s.property hs
    have hone : (s : G) = 1 := by
      apply Subgroup.mem_bot.mp
      rw [← hcent]
      exact ⟨s.property, hc⟩
    change (s : G) • (y : X) = (x : X) at hs
    rw [hone, one_smul] at hs
    exact hs.symm

/-- Fixed points give distinct quotient points even in the presence of one fixed exceptional orbit. -/
theorem fixed_points_card_le_quotient_of_free_away (C S : Subgroup G)
    [Finite (Quotient (MulAction.orbitRel S X))]
    (hnorm : C ≤ Subgroup.normalizer (S : Set G))
    (hcent : S ⊓ Subgroup.centralizer (C : Set G) = ⊥)
    (P : X) (hP : P ∈ MulAction.fixedPoints S X)
    (hfree : ∀ x, x ≠ P → ∀ s ∈ S, s • x = x → s = 1) :
    Nat.card (MulAction.fixedPoints C X) ≤ Nat.card (Quotient (MulAction.orbitRel S X)) :=
  Nat.card_le_card_of_injective _
    (fixed_points_quotient_injective_of_free_away C S hnorm hcent P hP hfree)

/-- Fixed-point descent is injective when the only exceptional orbit is fixed. -/
theorem fixedPointDescent_injective_of_free_away (C S : Subgroup G)
    (hnorm : C ≤ Subgroup.normalizer (S : Set G))
    (hcent : S ⊓ Subgroup.centralizer (C : Set G) = ⊥)
    (P : X) (hP : P ∈ MulAction.fixedPoints S X)
    (hfree : ∀ x, x ≠ P → ∀ s ∈ S, s • x = x → s = 1) :
    Function.Injective (fixedPointDescent (X := X) C S hnorm) := by
  intro x y he
  exact fixed_points_quotient_injective_of_free_away C S hnorm hcent P hP hfree
    (congrArg Subtype.val he)

/-- The quotient action has at least as many fixed points as the original action. -/
theorem fixed_points_card_le_quotient_fixed_points (C S : Subgroup G)
    (hnorm : C ≤ Subgroup.normalizer (S : Set G))
    [Finite (normalizedQuotientFixedPoints (X := X) C S hnorm)]
    (hcent : S ⊓ Subgroup.centralizer (C : Set G) = ⊥)
    (P : X) (hP : P ∈ MulAction.fixedPoints S X)
    (hfree : ∀ x, x ≠ P → ∀ s ∈ S, s • x = x → s = 1) :
    Nat.card (MulAction.fixedPoints C X) ≤
      Nat.card (normalizedQuotientFixedPoints (X := X) C S hnorm) :=
  Nat.card_le_card_of_injective _
    (fixedPointDescent_injective_of_free_away C S hnorm hcent P hP hfree)

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri

#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.fixed_point_transporter_centralizes
#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.fixed_point_orbit_iff_centralizer_orbit
#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.fixed_points_quotient_injective
#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.fixed_points_quotient_injective_of_free_away
#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.fixed_points_card_le_quotient_of_free_away
#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.normalizedOrbitAction
#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.fixedPointDescent
#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.fixedPointDescent_injective_of_free_away
#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.fixed_points_card_le_quotient_fixed_points
