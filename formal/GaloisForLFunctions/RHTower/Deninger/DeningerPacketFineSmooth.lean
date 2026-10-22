import GaloisForLFunctions.RHTower.Deninger.DeningerPacketFine
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Geometry.Manifold.Instances.Sphere

/-!
# Smooth fineness of the packet

When the transverse factor is a compact manifold, the subordinate partition of unity assembled
over a clopen partition of the profinite factor is smooth along the transverse factor: over each
piece of the partition the assembled function *is* the transverse function chosen there.

This is the regularity the leafwise sheaf on a packet asks for — locally constant along the
profinite direction, smooth along the circle.

* `deningerPacketFineSmooth` : the subordinate partition of unity, locally constant along the
  profinite factor and smooth along the transverse manifold.
-/

namespace RHTower

open Set TopologicalSpace
open scoped Manifold ContDiff

universe u v w

section PacketFineSmooth

variable {B : Type u} [TopologicalSpace B] [CompactSpace B] [T2Space B]
  [TotallyDisconnectedSpace B]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type v} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [CompactSpace M] [SigmaCompactSpace M] {κ : Type w}

/-- **The packet is smoothly fine.**  Every open cover of a compact profinite factor times a
compact manifold admits a subordinate partition of unity whose members are continuous, locally
constant along the profinite factor, and smooth along the manifold factor. -/
theorem deningerPacketFineSmooth (U : κ → Set (B × M)) (hU : ∀ j, IsOpen (U j))
    (hcov : ∀ p : B × M, ∃ j, p ∈ U j) :
    ∃ (ι : Type (max u v)) (_ : Fintype ι) (ρ : ι → B × M → ℝ) (g : ι → κ),
      (∀ i, Continuous (ρ i))
        ∧ (∀ (i : ι) (t : M), IsLocallyConstant fun b : B => ρ i (b, t))
        ∧ (∀ (i : ι) (b : B), ContMDiff I 𝓘(ℝ) ∞ fun t : M => ρ i (b, t))
        ∧ (∀ p : B × M, ∑ i, ρ i p = 1)
        ∧ ∀ (i : ι) (p : B × M), ρ i p ≠ 0 → p ∈ U (g i) := by
  classical
  obtain ⟨T, C, W, f, hCclopen, hWopen, hbox, hTcov⟩ := deningerBoxRefinement hU hcov
  set ι₀ : Type (max u v) := {q : B × M // q ∈ T} with hι₀
  haveI : Fintype ι₀ := FinsetCoe.fintype T
  set Cs : ι₀ → Set B := fun q => C q.val with hCs
  have hCsClopen : ∀ q : ι₀, IsClopen (Cs q) := fun q => hCclopen q.val
  set A : Finset ι₀ → Set B := fun P => deningerAtom Cs P with hA
  have hAclopen : ∀ P, IsClopen (A P) := fun P => deningerAtom_isClopen hCsClopen P
  have hApart : ∀ b : B, ∃! P : Finset ι₀, b ∈ A P := deningerAtom_existsUnique Cs
  set V : Finset ι₀ → ι₀ → Set M := fun P q => if q ∈ P then W q.val else ∅ with hV
  have hVopen : ∀ P q, IsOpen (V P q) := by
    intro P q
    by_cases h : q ∈ P
    · rw [hV]
      simp only [if_pos h]
      exact hWopen q.val
    · rw [hV]
      simp only [if_neg h]
      exact isOpen_empty
  have hVcover : ∀ (P : Finset ι₀) (b : B), b ∈ A P → (univ : Set M) ⊆ ⋃ q, V P q := by
    intro P b hb t _
    obtain ⟨q, hqT, hq⟩ := hTcov (b, t)
    have hqP : (⟨q, hqT⟩ : ι₀) ∈ P := (hb ⟨q, hqT⟩).mpr hq.1
    refine mem_iUnion.mpr ⟨⟨q, hqT⟩, ?_⟩
    rw [hV]
    simp only [if_pos hqP]
    exact hq.2
  -- a smooth partition of unity on the manifold factor over each piece
  have hpou : ∀ P : Finset ι₀, ∃ ψ : ι₀ → M → ℝ,
      (∀ q, ContMDiff I 𝓘(ℝ) ∞ (ψ q)) ∧ (∀ q t, ψ q t ≠ 0 → t ∈ V P q)
        ∧ ∀ b ∈ A P, ∀ t : M, ∑ q, ψ q t = 1 := by
    intro P
    by_cases hne : (A P).Nonempty
    · obtain ⟨b, hb⟩ := hne
      obtain ⟨φ, hφ⟩ := SmoothPartitionOfUnity.exists_isSubordinate (I := I)
        (s := (univ : Set M)) isClosed_univ (V P) (hVopen P) (hVcover P b hb)
      refine ⟨fun q => φ q, fun q => (φ q).contMDiff, fun q t ht => ?_, fun _ _ t => ?_⟩
      · exact hφ q (subset_tsupport _ ht)
      · rw [← finsum_eq_sum_of_fintype]
        exact φ.sum_eq_one (mem_univ t)
    · refine ⟨fun _ _ => 0, fun _ => contMDiff_const, fun q t ht => absurd rfl ht, ?_⟩
      intro b hb
      exact absurd ⟨b, hb⟩ hne
  choose ψ hψsmooth hψsupp hψsum using hpou
  refine ⟨ι₀, inferInstance, fun q p => deningerTransverseSum A ψ q p, fun q => f q.val,
    fun q => ?_, fun q t => ?_, fun q b => ?_, fun p => ?_, fun q p hne => ?_⟩
  · exact deningerTransverseSum_continuous hAclopen
      (fun P j => (hψsmooth P j).continuous) q
  · exact deningerTransverseSum_locallyConstant hAclopen hApart q t
  · obtain ⟨P, hP, _⟩ := hApart b
    have hfun : (fun t : M => deningerTransverseSum A ψ q (b, t)) = ψ P q := by
      funext t
      exact deningerTransverseSum_eq_of_mem hApart hP q t
    rw [hfun]
    exact hψsmooth P q
  · exact deningerTransverseSum_sum hApart (fun P b hb t => hψsum P b hb t) p
  · refine deningerTransverseSum_subordinate (I := V) (U := fun j : ι₀ => U (f j.val))
      (fun P j t ht => hψsupp P j t ht) ?_ hne
    intro P j
    rintro ⟨b, t⟩ ⟨hbP, htV⟩
    by_cases hjP : j ∈ P
    · have hbC : b ∈ Cs j := deningerAtom_subset hjP hbP
      have htW : t ∈ W j.val := by
        rw [hV] at htV
        simpa only [if_pos hjP] using htV
      exact hbox j.val ⟨hbC, htW⟩
    · rw [hV] at htV
      simp only [if_neg hjP] at htV
      exact absurd htV (notMem_empty t)

end PacketFineSmooth

end RHTower

namespace RHTower

open Set
open scoped Manifold ContDiff

section CircleFactor

universe u w

/-- **The packet with a circle transverse factor is smoothly fine.**  This is the leafwise sheaf
regularity on a prime packet: locally constant along the profinite factor, smooth along the
circle. -/
theorem deningerPacketFineSmooth_circle {B : Type u} [TopologicalSpace B] [CompactSpace B]
    [T2Space B] [TotallyDisconnectedSpace B] {κ : Type w}
    (U : κ → Set (B × Circle)) (hU : ∀ j, IsOpen (U j))
    (hcov : ∀ p : B × Circle, ∃ j, p ∈ U j) :
    ∃ (ι : Type u) (_ : Fintype ι) (ρ : ι → B × Circle → ℝ) (g : ι → κ),
      (∀ i, Continuous (ρ i))
        ∧ (∀ (i : ι) (t : Circle), IsLocallyConstant fun b : B => ρ i (b, t))
        ∧ (∀ (i : ι) (b : B), ContMDiff (𝓡 1) 𝓘(ℝ) ∞ fun t : Circle => ρ i (b, t))
        ∧ (∀ p : B × Circle, ∑ i, ρ i p = 1)
        ∧ ∀ (i : ι) (p : B × Circle), ρ i p ≠ 0 → p ∈ U (g i) :=
  deningerPacketFineSmooth (I := 𝓡 1) U hU hcov

end CircleFactor

end RHTower
