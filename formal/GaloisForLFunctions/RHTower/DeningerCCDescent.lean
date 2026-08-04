import GaloisForLFunctions.RHTower.DeningerCCColimit
import GaloisForLFunctions.RHTower.DeningerBaumslagRationalization

/-!
# Mapping the tower into a uniquely divisible group

A uniquely divisible group receiving the starting stage receives every stage: the rooted generator
has a root there, and the amalgam's universal property assembles the two factors.  The maps are
compatible with the embeddings, so they descend to the colimit.

* `deningerZRoot` : the root of an integer exponent in a uniquely divisible group.
* `deningerCCDesc` : the maps out of the stages.
* `deningerCCColimitDesc` : the map out of the colimit.
-/

namespace RHTower

open CategoryTheory Monoid Monoid.PushoutI

universe u

/-- The root of an integer exponent in a uniquely divisible group. -/
noncomputable def deningerZRoot {B : Type u} [Group B] (hB : DeningerUniquelyDivisible B) (N : ℤ)
    (x : B) : B :=
  if 0 < N then deningerRoot hB (N.natAbs - 1) x else (deningerRoot hB (N.natAbs - 1) x)⁻¹

/-- **The root of an integer exponent raised to that exponent is the element.** -/
theorem deningerZRoot_zpow {B : Type u} [Group B] (hB : DeningerUniquelyDivisible B) (N : ℤ)
    (hN : N ≠ 0) (x : B) : (deningerZRoot hB N x) ^ N = x := by
  have hnat : N.natAbs - 1 + 1 = N.natAbs := by omega
  rcases lt_or_gt_of_ne hN with hneg | hpos
  · rw [deningerZRoot, if_neg (by omega)]
    have h1 : N = -(N.natAbs : ℤ) := by omega
    rw [h1, zpow_neg, ← inv_zpow, inv_inv, zpow_natCast, ← hnat]
    exact deningerRoot_pow hB (N.natAbs - 1) x
  · rw [deningerZRoot, if_pos hpos]
    have h1 : N = (N.natAbs : ℤ) := by omega
    rw [h1, zpow_natCast, ← hnat]
    exact deningerRoot_pow hB (N.natAbs - 1) x

namespace RootAdjunction

/-- The factor maps of one step of the descent. -/
noncomputable def deningerCCStepFactors (S : DeningerCCStage.{u}) (p : ℕ) (N : ℤ)
    {B : Type u} [Group B] (hB : DeningerUniquelyDivisible B) (ψ : S.carrier →* B) :
    ∀ i, deningerRootFactor S.carrier i →* B
  | ⟨true⟩ => show deningerRootFactor S.carrier (ULift.up true) →* B from ψ
  | ⟨false⟩ => show deningerRootFactor S.carrier (ULift.up false) →* B from
      (zpowersHom B (deningerZRoot hB N (ψ (deningerCCRoot S p)))).comp
        (MulEquiv.ulift : ULift.{u} (Multiplicative ℤ) ≃* Multiplicative ℤ).toMonoidHom

/-- The base map of one step of the descent. -/
noncomputable def deningerCCStepBase (S : DeningerCCStage.{u}) (p : ℕ)
    {B : Type u} [Group B] (ψ : S.carrier →* B) : ULift.{u} (Multiplicative ℤ) →* B :=
  (zpowersHom B (ψ (deningerCCRoot S p))).comp
    (MulEquiv.ulift : ULift.{u} (Multiplicative ℤ) ≃* Multiplicative ℤ).toMonoidHom

/-- The two maps agree on the base group. -/
theorem deningerCCStepCompat (S : DeningerCCStage.{u}) (p : ℕ) (N : ℤ) (hN : N ≠ 0)
    {B : Type u} [Group B] (hB : DeningerUniquelyDivisible B) (ψ : S.carrier →* B) :
    ∀ i, (deningerCCStepFactors S p N hB ψ i).comp
      (deningerRootMap S.carrier (deningerCCRoot S p) N i) = deningerCCStepBase S p ψ := by
  rintro ⟨b⟩
  refine MonoidHom.ext fun k => ?_
  cases b
  · show (deningerZRoot hB N (ψ (deningerCCRoot S p))) ^
        (Multiplicative.toAdd (MulEquiv.ulift
          (deningerRootMap S.carrier (deningerCCRoot S p) N (ULift.up false) k))) = _
    have hk : Multiplicative.toAdd (MulEquiv.ulift
        (deningerRootMap S.carrier (deningerCCRoot S p) N (ULift.up false) k)) =
        N * Multiplicative.toAdd (MulEquiv.ulift k) := rfl
    rw [hk, zpow_mul, deningerZRoot_zpow hB N hN]
    rfl
  · show ψ (deningerRootMap S.carrier (deningerCCRoot S p) N (ULift.up true) k) = _
    have hk : deningerRootMap S.carrier (deningerCCRoot S p) N (ULift.up true) k =
        (deningerCCRoot S p) ^ (Multiplicative.toAdd (MulEquiv.ulift k)) := rfl
    rw [hk, map_zpow]
    rfl

/-- **One step of the descent**: extending a map to the amalgam, the adjoined root going to the
root of the image. -/
noncomputable def deningerCCStepDesc (S : DeningerCCStage.{u}) (p : ℕ) (N : ℤ) (hN : N ≠ 0)
    {B : Type u} [Group B] (hB : DeningerUniquelyDivisible B) (ψ : S.carrier →* B) :
    PushoutI (deningerRootMap S.carrier (deningerCCRoot S p) N) →* B :=
  PushoutI.lift (deningerCCStepFactors S p N hB ψ) (deningerCCStepBase S p ψ)
    (deningerCCStepCompat S p N hN hB ψ)

/-- **One step of the descent restricts to the map it extends.** -/
theorem deningerCCStepDesc_of (S : DeningerCCStage.{u}) (p : ℕ) (N : ℤ) (hN : N ≠ 0)
    {B : Type u} [Group B] (hB : DeningerUniquelyDivisible B) (ψ : S.carrier →* B)
    (x : S.carrier) :
    deningerCCStepDesc S p N hN hB ψ
      (PushoutI.of (φ := deningerRootMap S.carrier (deningerCCRoot S p) N) (ULift.up true) x) =
      ψ x :=
  PushoutI.lift_of (deningerCCStepFactors S p N hB ψ) (deningerCCStepBase S p ψ)
    (deningerCCStepCompat S p N hN hB ψ) (i := ULift.up true) x

/-- **The maps out of the stages** into a uniquely divisible group receiving the starting stage. -/
noncomputable def deningerCCDesc (S₀ : DeningerCCStage.{u}) (sched : ℕ → ℕ × ℤ)
    (hs : ∀ n, 2 ≤ (sched n).2.natAbs) {B : Type u} [Group B] (hB : DeningerUniquelyDivisible B)
    (f : S₀.carrier →* B) : ∀ n : ℕ, (deningerCCTower S₀ sched n).carrier →* B
  | 0 => f
  | n + 1 => deningerCCStepDesc (deningerCCTower S₀ sched n) (sched n).1 (sched n).2
      (by have := hs n; omega) hB (deningerCCDesc S₀ sched hs hB f n)

/-- **The maps out of the stages are compatible with the embeddings.** -/
theorem deningerCCDesc_embed (S₀ : DeningerCCStage.{u}) (sched : ℕ → ℕ × ℤ)
    (hs : ∀ n, 2 ≤ (sched n).2.natAbs) {B : Type u} [Group B] (hB : DeningerUniquelyDivisible B)
    (f : S₀.carrier →* B) (n : ℕ) (x : (deningerCCTower S₀ sched n).carrier) :
    deningerCCDesc S₀ sched hs hB f (n + 1) (deningerCCEmbed S₀ sched n x) =
      deningerCCDesc S₀ sched hs hB f n x :=
  deningerCCStepDesc_of (deningerCCTower S₀ sched n) (sched n).1 (sched n).2
    (by have := hs n; omega) hB (deningerCCDesc S₀ sched hs hB f n) x

/-- The cocone into a uniquely divisible group. -/
noncomputable def deningerCCCocone (S₀ : DeningerCCStage.{u}) (sched : ℕ → ℕ × ℤ)
    (hs : ∀ n, 2 ≤ (sched n).2.natAbs) {B : Type u} [Group B] (hB : DeningerUniquelyDivisible B)
    (f : S₀.carrier →* B) : Limits.Cocone (deningerCCDiagram S₀ sched) where
  pt := GrpCat.of B
  ι := NatTrans.ofSequence
    (F := deningerCCDiagram S₀ sched)
    (G := (Functor.const ℕ).obj (GrpCat.of B))
    (fun n => GrpCat.ofHom (deningerCCDesc S₀ sched hs hB f n))
    (by
      intro n
      refine GrpCat.hom_ext (MonoidHom.ext fun x => ?_)
      have hstep : ∀ y : (deningerCCTower S₀ sched n).carrier,
          ((deningerCCDiagram S₀ sched).map (homOfLE (Nat.le_succ n))).hom y =
            deningerCCEmbed S₀ sched n y := by
        intro y
        show ((Functor.ofSequence
          (fun k => GrpCat.ofHom (deningerCCEmbed S₀ sched k))).map
            (homOfLE (Nat.le_succ n))).hom y = _
        rw [Functor.ofSequence_map_homOfLE_succ]
        rfl
      show deningerCCDesc S₀ sched hs hB f (n + 1)
        (((deningerCCDiagram S₀ sched).map (homOfLE (Nat.le_succ n))).hom x) = _
      rw [hstep x, deningerCCDesc_embed]
      rfl)

/-- **The map out of the colimit.** -/
noncomputable def deningerCCColimitDesc (S₀ : DeningerCCStage.{u}) (sched : ℕ → ℕ × ℤ)
    (hs : ∀ n, 2 ≤ (sched n).2.natAbs) {B : Type u} [Group B] (hB : DeningerUniquelyDivisible B)
    (f : S₀.carrier →* B) : deningerCCColimit S₀ sched →* B :=
  ((GrpCat.FilteredColimits.colimitCoconeIsColimit (deningerCCDiagram S₀ sched)).desc
    (deningerCCCocone S₀ sched hs hB f)).hom

/-- **The map out of the colimit restricts to the maps out of the stages.** -/
theorem deningerCCColimitDesc_iota (S₀ : DeningerCCStage.{u}) (sched : ℕ → ℕ × ℤ)
    (hs : ∀ n, 2 ≤ (sched n).2.natAbs) {B : Type u} [Group B] (hB : DeningerUniquelyDivisible B)
    (f : S₀.carrier →* B) (n : ℕ) (x : (deningerCCTower S₀ sched n).carrier) :
    deningerCCColimitDesc S₀ sched hs hB f (deningerCCIota S₀ sched n x) =
      deningerCCDesc S₀ sched hs hB f n x := by
  have h := (GrpCat.FilteredColimits.colimitCoconeIsColimit
    (deningerCCDiagram S₀ sched)).fac (deningerCCCocone S₀ sched hs hB f) n
  exact congrArg (fun g : GrpCat.of ((deningerCCTower S₀ sched n).carrier) ⟶ GrpCat.of B =>
    g.hom x) h

end RootAdjunction

end RHTower
