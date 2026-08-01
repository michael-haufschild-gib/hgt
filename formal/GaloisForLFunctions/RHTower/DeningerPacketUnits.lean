import GaloisForLFunctions.RHTower.DeningerPacketFineSmooth
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated

/-!
# The profinite factor of a prime packet

The unit group of a totally disconnected topological monoid is totally disconnected, because it
embeds continuously and injectively into the square of the monoid.  Applied to the `p`-adic
integers — whose metric is ultrametric, hence totally separated — this makes each local unit group
profinite, and a product of them profinite as well.

So the prime-packet unit group `∏_{ℓ ≠ p} ℤ_ℓ^×` is compact Hausdorff and totally disconnected,
which is exactly the hypothesis under which the packet is smoothly fine.

* `deningerTotallyDisconnected_of_injective` : total disconnectedness along a continuous injection.
* `DeningerPacketUnits` : the prime-packet unit group.
* `deningerPacketUnitsFineSmooth` : the packet over it is smoothly fine.
-/

namespace RHTower

open Set
open scoped Manifold ContDiff

section Transfer

/-- **Total disconnectedness passes along a continuous injection.**  A preconnected set maps to a
preconnected set, which is a subsingleton, and injectivity pulls that back. -/
theorem deningerTotallyDisconnected_of_injective {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [TotallyDisconnectedSpace Y] {f : X → Y} (hf : Continuous f)
    (hinj : Function.Injective f) : TotallyDisconnectedSpace X := by
  refine ⟨fun t _ ht => ?_⟩
  have himg : (f '' t).Subsingleton :=
    TotallyDisconnectedSpace.isTotallyDisconnected_univ _ (subset_univ _)
      (ht.image f hf.continuousOn)
  intro x hx y hy
  exact hinj (himg ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩)

/-- **The opposite of a totally disconnected space is totally disconnected.** -/
instance deningerMulOppositeTotallyDisconnected {M : Type*} [TopologicalSpace M]
    [TotallyDisconnectedSpace M] : TotallyDisconnectedSpace Mᵐᵒᵖ :=
  deningerTotallyDisconnected_of_injective (f := MulOpposite.unop)
    MulOpposite.continuous_unop MulOpposite.unop_injective

/-- **The unit group of a totally disconnected monoid is totally disconnected.** -/
instance deningerUnitsTotallyDisconnected {M : Type*} [Monoid M] [TopologicalSpace M]
    [TotallyDisconnectedSpace M] : TotallyDisconnectedSpace Mˣ :=
  deningerTotallyDisconnected_of_injective (f := Units.embedProduct M)
    Units.continuous_embedProduct (Units.embedProduct_injective M)

end Transfer

section PacketUnits

instance deningerPrimesFact (ℓ : Nat.Primes) : Fact (Nat.Prime (ℓ : ℕ)) := ⟨ℓ.2⟩

/-- The prime-packet unit group `∏_{ℓ ≠ p} ℤ_ℓ^×`. -/
def DeningerPacketUnits (p : ℕ) : Type :=
  ∀ ℓ : {ℓ : Nat.Primes // (ℓ : ℕ) ≠ p}, (ℤ_[(ℓ : ℕ)])ˣ

noncomputable instance (p : ℕ) : TopologicalSpace (DeningerPacketUnits p) :=
  inferInstanceAs (TopologicalSpace (∀ ℓ : {ℓ : Nat.Primes // (ℓ : ℕ) ≠ p}, (ℤ_[(ℓ : ℕ)])ˣ))

noncomputable instance (p : ℕ) : CompactSpace (DeningerPacketUnits p) :=
  inferInstanceAs (CompactSpace (∀ ℓ : {ℓ : Nat.Primes // (ℓ : ℕ) ≠ p}, (ℤ_[(ℓ : ℕ)])ˣ))

noncomputable instance (p : ℕ) : T2Space (DeningerPacketUnits p) :=
  inferInstanceAs (T2Space (∀ ℓ : {ℓ : Nat.Primes // (ℓ : ℕ) ≠ p}, (ℤ_[(ℓ : ℕ)])ˣ))

noncomputable instance (p : ℕ) : TotallyDisconnectedSpace (DeningerPacketUnits p) :=
  inferInstanceAs
    (TotallyDisconnectedSpace (∀ ℓ : {ℓ : Nat.Primes // (ℓ : ℕ) ≠ p}, (ℤ_[(ℓ : ℕ)])ˣ))

noncomputable instance (p : ℕ) : CommGroup (DeningerPacketUnits p) :=
  inferInstanceAs (CommGroup (∀ ℓ : {ℓ : Nat.Primes // (ℓ : ℕ) ≠ p}, (ℤ_[(ℓ : ℕ)])ˣ))

noncomputable instance (p : ℕ) : IsTopologicalGroup (DeningerPacketUnits p) :=
  inferInstanceAs
    (IsTopologicalGroup (∀ ℓ : {ℓ : Nat.Primes // (ℓ : ℕ) ≠ p}, (ℤ_[(ℓ : ℕ)])ˣ))

/-- **The prime packet over the unit group is smoothly fine.**  Every open cover of the packet
admits a subordinate partition of unity, locally constant along the unit group and smooth along the
circle. -/
theorem deningerPacketUnitsFineSmooth (p : ℕ) {κ : Type}
    (U : κ → Set (DeningerPacketUnits p × Circle)) (hU : ∀ j, IsOpen (U j))
    (hcov : ∀ q : DeningerPacketUnits p × Circle, ∃ j, q ∈ U j) :
    ∃ (ι : Type) (_ : Fintype ι) (ρ : ι → DeningerPacketUnits p × Circle → ℝ) (g : ι → κ),
      (∀ i, Continuous (ρ i))
        ∧ (∀ (i : ι) (t : Circle),
            IsLocallyConstant fun b : DeningerPacketUnits p => ρ i (b, t))
        ∧ (∀ (i : ι) (b : DeningerPacketUnits p),
            ContMDiff (𝓡 1) 𝓘(ℝ) ∞ fun t : Circle => ρ i (b, t))
        ∧ (∀ q : DeningerPacketUnits p × Circle, ∑ i, ρ i q = 1)
        ∧ ∀ (i : ι) (q : DeningerPacketUnits p × Circle), ρ i q ≠ 0 → q ∈ U (g i) :=
  deningerPacketFineSmooth_circle U hU hcov

end PacketUnits

end RHTower
