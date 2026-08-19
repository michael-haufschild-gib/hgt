import GaloisForLFunctions.HTGeometry.QuasiAbelianCosetPoincareSeries

/-!
# Nonzero complement translates never meet the packet

The damping multiplier of Abe's extension step must be `ΓH`-*invariant*.  That is periodicity under
a discrete lattice, not constancy along the real directions it spans, so such a multiplier is still
free to separate points of the packet that differ inside those directions.

What it cannot separate is a packet point from a `ΓH`-translate of itself.  This file records that
this never has to happen: for a genuine complement, a *nonzero* complement translate of one packet
point is never `ΓH`-congruent to any packet point.  Distinctness modulo `Γ` — the hypothesis the
card already carries — is exactly what is needed.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- **No collisions.**  For a genuine complement of `ΓH` in `Γ`, a nonzero complement translate of a
packet point is never `ΓH`-congruent to a packet point. -/
theorem packet_translate_not_congruent
    {d c : ℕ} {ΓH Γ : AddSubgroup (Fin d → ℂ)} (hle : ΓH ≤ Γ)
    (comp : (Fin c → ℤ) →+ (Fin d → ℂ)) (hcomp : ∀ z, comp z ∈ Γ)
    (hcompinj : Function.Injective comp)
    (hdisj : ∀ z : Fin c → ℤ, comp z ∈ ΓH → z = 0)
    {I : Type*} {w : I → Fin d → ℂ} (hdistinct : PairwiseDistinctModulo Γ w)
    (i j : I) {z : Fin c → ℤ} (hz : z ≠ 0) :
    (w i + comp z) - w j ∉ ΓH := by
  intro hmem
  by_cases hij : i = j
  · subst hij
    have hcz : comp z ∈ ΓH := by
      have h : (w i + comp z) - w i = comp z := by ring
      rwa [h] at hmem
    exact hz (hdisj z hcz)
  · have hΓ : w i - w j ∈ Γ := by
      have h : w i - w j = ((w i + comp z) - w j) - comp z := by ring
      rw [h]
      exact Γ.sub_mem (hle hmem) (hcomp z)
    exact hdistinct hij hΓ

/-- The same statement in the form the damping multiplier consumes: the packet and its nonzero
complement translates are pairwise distinct modulo `ΓH`. -/
theorem packet_translate_pairwiseDistinct
    {d c : ℕ} {ΓH Γ : AddSubgroup (Fin d → ℂ)} (hle : ΓH ≤ Γ)
    (comp : (Fin c → ℤ) →+ (Fin d → ℂ)) (hcomp : ∀ z, comp z ∈ Γ)
    (hcompinj : Function.Injective comp)
    (hdisj : ∀ z : Fin c → ℤ, comp z ∈ ΓH → z = 0)
    {I : Type*} {w : I → Fin d → ℂ} (hdistinct : PairwiseDistinctModulo Γ w)
    (i j : I) (z : Fin c → ℤ) (h : (w i + comp z) - w j ∈ ΓH) :
    z = 0 ∧ i = j := by
  have hz : z = 0 := by
    by_contra hz
    exact packet_translate_not_congruent hle comp hcomp hcompinj hdisj hdistinct i j hz h
  refine ⟨hz, ?_⟩
  by_contra hij
  refine hdistinct hij ?_
  have hzero : comp z = 0 := by rw [hz, map_zero]
  have hrw : w i - w j = (w i + comp z) - w j := by rw [hzero]; ring
  rw [hrw]
  exact hle h

end

end GaloisForLFunctions.HTGeometry
