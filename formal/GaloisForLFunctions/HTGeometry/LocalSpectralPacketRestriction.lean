import GaloisForLFunctions.HTGeometry.FiniteLocalInteractionFamily

/-!
# Restricting a finite local spectral family to an active interaction packet

Couplings on a finite label packet can be extended by zero to the full interaction universe.
The resulting global affine matrix family is exactly the subtype-indexed active family. These
identities let simple-root germ uniqueness compare one globally labelled eigenvalue branch with
every packet-sector factorization.
-/

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

namespace FiniteLocalInteractionFamily

variable
    {V E : Type*} [Fintype V] [DecidableEq V]
    [DecidableEq E]
    {A : V → Type*} [∀ v, Fintype (A v)] [∀ v, DecidableEq (A v)]

def restrictCouplingToPacket
    (packet : Finset E) (coupling : E → ℂ) :
    {e : E // e ∈ packet} → ℂ :=
  fun e => coupling e.1

def extendCouplingFromPacket
    (packet : Finset E) (coupling : {e : E // e ∈ packet} → ℂ) :
    E → ℂ :=
  fun e => if he : e ∈ packet then coupling ⟨e, he⟩ else 0

theorem extend_restrictCouplingToPacket
    (packet : Finset E) (coupling : E → ℂ) :
    extendCouplingFromPacket packet (restrictCouplingToPacket packet coupling) =
      restrictInteractionPacket packet coupling := by
  funext e
  by_cases he : e ∈ packet <;>
    simp [extendCouplingFromPacket, restrictCouplingToPacket,
      restrictInteractionPacket, he]

/-- Extending subtype couplings by zero produces exactly the active subtype affine family. -/
theorem affineMatrixFamily_extendCouplingFromPacket
    [Fintype E]
    (L : FiniteLocalInteractionFamily V E A)
    (onsite : ∀ v, A v → ℂ)
    (packet : Finset E)
    (coupling : {e : E // e ∈ packet} → ℂ) :
    affineMatrixFamily
        (Matrix.diagonal (onsiteProductEnergy onsite))
        L.globalInteraction
        (extendCouplingFromPacket packet coupling) =
      affineMatrixFamily
        (Matrix.diagonal (onsiteProductEnergy onsite))
        (fun e : {e : E // e ∈ packet} => L.globalInteraction e.1)
        coupling := by
  unfold affineMatrixFamily
  congr 1
  let f : E → Matrix (∀ v, A v) (∀ v, A v) ℂ :=
    fun e => if he : e ∈ packet
      then coupling ⟨e, he⟩ • L.globalInteraction e else 0
  have hfull :
      ∑ e, f e = ∑ e ∈ packet, f e := by
    symm
    apply Finset.sum_subset (Finset.subset_univ packet)
    intro e heuniv henot
    simp [f, henot]
  have hsub :
      ∑ e ∈ packet, f e =
        ∑ e : {e : E // e ∈ packet},
          coupling e • L.globalInteraction e.1 := by
    calc
      ∑ e ∈ packet, f e =
          ∑ e : {e : E // e ∈ packet}, f e.1 :=
        Finset.sum_subtype packet (by simp) f
      _ = _ := by
        apply Finset.sum_congr rfl
        intro e he
        simp [f, e.2]
  calc
    ∑ e, extendCouplingFromPacket packet coupling e •
        L.globalInteraction e =
        ∑ e, f e := by
          apply Finset.sum_congr rfl
          intro e he
          simp [f, extendCouplingFromPacket]
    _ = ∑ e ∈ packet, f e := hfull
    _ = _ := hsub

/-- Activating a packet in the full coupling vector equals restricting to its subtype family. -/
theorem affineMatrixFamily_restrictInteractionPacket
    [Fintype E]
    (L : FiniteLocalInteractionFamily V E A)
    (onsite : ∀ v, A v → ℂ)
    (packet : Finset E) (coupling : E → ℂ) :
    affineMatrixFamily
        (Matrix.diagonal (onsiteProductEnergy onsite))
        L.globalInteraction
        (restrictInteractionPacket packet coupling) =
      affineMatrixFamily
        (Matrix.diagonal (onsiteProductEnergy onsite))
        (fun e : {e : E // e ∈ packet} => L.globalInteraction e.1)
        (restrictCouplingToPacket packet coupling) := by
  rw [← extend_restrictCouplingToPacket]
  exact affineMatrixFamily_extendCouplingFromPacket L onsite packet _

end FiniteLocalInteractionFamily

end GaloisForLFunctions.HTGeometry
