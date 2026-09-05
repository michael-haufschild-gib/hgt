import GaloisForLFunctions.HTGeometry.MultipleSineFacePacketDisjoint
import GaloisForLFunctions.HTGeometry.DifferentialUniformFaceGluing

/-!
# The star of a direction is a union of full orbits

Along a direction inside a face, the face packet is a union of full translation orbits: the packet
splits as the orbit of its slice, the sub-family whose exponent in that direction vanishes.  The
star of a vertex set is the union of the packets of the faces containing it, so it too is an orbit
union.

Distinct exponents give distinct elements: inside one face because the packet family is
differentially independent, hence injective, and across faces because distinct maximal faces have
disjoint packets.  That is exactly the free-translate interface of the gluing engine.
-/

open Filter Set Topology Complex
open scoped Differential

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions Bottcher
open GaloisForLFunctions.MatroidGluing GaloisForLFunctions.MatroidGluing.Rank
open GaloisForLFunctions.MatroidGluing.Meromorphic

noncomputable section

noncomputable local instance msoDecidableEq :
    DecidableEq (meroField (Set.univ : Set ℂ)) := Classical.decEq _

attribute [local instance] ellipticGammaRationalBaseDomain
  ellipticGammaRationalBaseComplexAlgebraMero ellipticGammaRationalBaseComplexDifferential
  ellipticGammaRationalBaseMeroDifferential ellipticGammaRationalBaseMeroCharZero
  ellipticGammaRationalBaseComplexDifferentialAlgebra
  ellipticGammaRationalBaseCoordinateDifferential
  ellipticGammaRationalBaseCoordinateDifferentialAlgebra

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ### Splitting a face shift along one direction -/

omit [Fintype ι] in
theorem faceShift_split (ω : ι → ℂ) {J : Finset ι} {q : ι} (hq : q ∈ J)
    (α : {k // k ∈ J} → ℤ) :
    faceShift ω J α
      = faceShift ω J (fun k => if (k : ι) = q then 0 else α k)
        + (α ⟨q, hq⟩ : ℂ) * ω q := by
  classical
  set α' : {k // k ∈ J} → ℤ := fun k => if (k : ι) = q then 0 else α k with hα'
  have hmem : (⟨q, hq⟩ : {k // k ∈ J}) ∈ J.attach := Finset.mem_attach J _
  have hleft := Finset.add_sum_erase J.attach
    (fun k : {k // k ∈ J} => (α k : ℂ) * ω k) hmem
  have hright := Finset.add_sum_erase J.attach
    (fun k : {k // k ∈ J} => (α' k : ℂ) * ω k) hmem
  have hzero : (α' ⟨q, hq⟩ : ℂ) * ω q = 0 := by
    rw [hα']
    simp
  have hcongr : ∀ k ∈ J.attach.erase (⟨q, hq⟩ : {k // k ∈ J}),
      (α' k : ℂ) * ω k = (α k : ℂ) * ω k := by
    intro k hk
    have hkq : (k : ι) ≠ q := by
      intro hcon
      exact (Finset.mem_erase.mp hk).1 (Subtype.ext hcon)
    rw [hα']
    simp only [if_neg hkq]
  rw [faceShift, faceShift, ← hleft, ← hright, hzero,
    Finset.sum_congr rfl hcongr]
  ring

omit [Fintype ι] in
/-- Overwriting the exponent of one direction adds that many periods to the external shift. -/
theorem faceShift_update (ω : ι → ℂ) {J : Finset ι} {q : ι} (hq : q ∈ J)
    {β : {k // k ∈ J} → ℤ} (hβ : ∀ k : {k // k ∈ J}, (k : ι) = q → β k = 0) (n : ℤ) :
    faceShift ω J (fun k => if (k : ι) = q then n else β k)
      = faceShift ω J β + (n : ℂ) * ω q := by
  classical
  have hsplit := faceShift_split ω hq (fun k => if (k : ι) = q then n else β k)
  have hoff : (fun k : {k // k ∈ J} =>
      if (k : ι) = q then (0 : ℤ) else (if (k : ι) = q then n else β k)) = β := by
    funext k
    by_cases hk : (k : ι) = q
    · rw [if_pos hk, hβ k hk]
    · rw [if_neg hk, if_neg hk]
  have hval : ((if ((⟨q, hq⟩ : {k // k ∈ J}) : ι) = q then n
      else β ⟨q, hq⟩ : ℤ)) = n := by
    simp
  rw [hoff, hval] at hsplit
  exact hsplit

/-! ### The slice of a packet along a direction -/

/-- The slice of a face packet along a direction: the translates whose exponent in that direction
vanishes. -/
def facePacketSlice (ω : ι → ℂ) (hω : ∀ k, 0 < (ω k).im) (J : Finset ι) (q : ι) :
    Set (meroField (Set.univ : Set ℂ)) :=
  if h : (Jᶜ : Finset ι).Nonempty then
    {x | ∃ α : {k // k ∈ J} → ℤ, (∀ k : {k // k ∈ J}, (k : ι) = q → α k = 0) ∧
      x = addTranslationMeroEquiv (faceShift ω J α) (frameSourceMero ω hω (Jᶜ : Finset ι) h)}
  else ∅

theorem facePacketSlice_eq (ω : ι → ℂ) (hω : ∀ k, 0 < (ω k).im) {J : Finset ι} (q : ι)
    (h : (Jᶜ : Finset ι).Nonempty) :
    facePacketSlice ω hω J q
      = {x | ∃ α : {k // k ∈ J} → ℤ, (∀ k : {k // k ∈ J}, (k : ι) = q → α k = 0) ∧
        x = addTranslationMeroEquiv (faceShift ω J α)
          (frameSourceMero ω hω (Jᶜ : Finset ι) h)} := by
  rw [facePacketSlice, dif_pos h]

/-- **A face packet is the full orbit of its slice** along any direction of the face. -/
theorem facePacket_eq_orbitUnion (ω : ι → ℂ) (hω : ∀ k, 0 < (ω k).im) {J : Finset ι} {q : ι}
    (hq : q ∈ J) :
    facePacket ω hω J
      = orbitUnion (meroTranslationPerm (ω q)) (facePacketSlice ω hω J q) := by
  classical
  by_cases h : (Jᶜ : Finset ι).Nonempty
  · rw [facePacket_eq ω hω h, facePacketSlice_eq ω hω q h]
    ext x
    constructor
    · rintro ⟨α, rfl⟩
      set α' : {k // k ∈ J} → ℤ := fun k => if (k : ι) = q then 0 else α k with hα'
      have hα'0 : ∀ k : {k // k ∈ J}, (k : ι) = q → α' k = 0 := by
        intro k hk
        rw [hα']
        simp [hk]
      refine ⟨α ⟨q, hq⟩, addTranslationMeroEquiv (faceShift ω J α')
        (frameSourceMero ω hω (Jᶜ : Finset ι) h), ⟨α', hα'0, rfl⟩, ?_⟩
      rw [meroTranslationPerm_zpow_apply, addTranslationMeroEquiv_add]
      have harg : (α ⟨q, hq⟩ : ℂ) * ω q + faceShift ω J α' = faceShift ω J α := by
        rw [faceShift_split ω hq α, ← hα']
        ring
      rw [harg]
    · rintro ⟨n, y, ⟨β, hβ, rfl⟩, rfl⟩
      refine ⟨fun k => if (k : ι) = q then n else β k, ?_⟩
      rw [meroTranslationPerm_zpow_apply, addTranslationMeroEquiv_add]
      have harg : faceShift ω J (fun k => if (k : ι) = q then n else β k)
          = (n : ℂ) * ω q + faceShift ω J β := by
        rw [faceShift_update ω hq hβ n]
        ring
      exact congrArg (fun t => addTranslationMeroEquiv t
        (frameSourceMero ω hω (Jᶜ : Finset ι) h)) harg
  · rw [facePacket, dif_neg h, facePacketSlice, dif_neg h]
    ext x
    simp [orbitUnion]

/-! ### The star of a direction -/

theorem orbitUnion_biUnion {Ω : Type*} [DecidableEq Ω] (σ : Equiv.Perm Ω)
    {κ : Type*} (s : Finset κ) (B : κ → Set Ω) :
    orbitUnion σ (⋃ i ∈ s, B i) = ⋃ i ∈ s, orbitUnion σ (B i) := by
  ext x
  constructor
  · rintro ⟨n, y, hy, rfl⟩
    obtain ⟨i, hi, hyi⟩ := Set.mem_iUnion₂.mp hy
    exact Set.mem_iUnion₂.mpr ⟨i, hi, ⟨n, y, hyi, rfl⟩⟩
  · intro hx
    obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp hx
    obtain ⟨n, y, hy, rfl⟩ := hxi
    exact ⟨n, y, Set.mem_iUnion₂.mpr ⟨i, hi, hy⟩, rfl⟩

/-- **The star of a direction is an orbit union.** -/
theorem faceStar_eq_orbitUnion (ω : ι → ℂ) (hω : ∀ k, 0 < (ω k).im)
    (faces : Finset (Finset ι)) (A : Finset ι) (q : ι) :
    faceStar faces (facePacket ω hω) (insert q A)
      = orbitUnion (meroTranslationPerm (ω q))
        (⋃ J ∈ faces.filter (fun J => insert q A ⊆ J), facePacketSlice ω hω J q) := by
  classical
  rw [faceStar, orbitUnion_biUnion]
  refine Set.iUnion₂_congr fun J hJ => ?_
  have hJ' := Finset.mem_filter.mp hJ
  exact facePacket_eq_orbitUnion ω hω (hJ'.2 (Finset.mem_insert_self q A))

/-! ### Distinct exponents give distinct elements -/

set_option synthInstance.maxHeartbeats 1000000 in
/-- **Free translates on the star.**  Distinct exponents of a direction give distinct elements of
the star: inside one face because the packet family is injective, across faces because distinct
maximal faces have disjoint packets. -/
theorem facePacketSlice_zpow_injective {μ : ℂ} {rad : ι → ℝ} (hrad : ∀ k, 0 < rad k)
    (hind : LinearIndependent ℚ (fun k => μ * (rad k : ℂ)))
    (hω : ∀ k, 0 < (μ * (rad k : ℂ)).im)
    (faces : Finset (Finset ι)) (hfaces : ∀ J ∈ faces, (Jᶜ : Finset ι).card = 2)
    (A : Finset ι) (q : ι) (m n : ℤ) (y z : meroField (Set.univ : Set ℂ))
    (hy : y ∈ ⋃ J ∈ faces.filter (fun J => insert q A ⊆ J),
      facePacketSlice (fun k => μ * (rad k : ℂ)) hω J q)
    (hz : z ∈ ⋃ J ∈ faces.filter (fun J => insert q A ⊆ J),
      facePacketSlice (fun k => μ * (rad k : ℂ)) hω J q)
    (hyz : (meroTranslationPerm (μ * (rad q : ℂ)) ^ m) y
      = (meroTranslationPerm (μ * (rad q : ℂ)) ^ n) z) :
    m = n := by
  classical
  set ω : ι → ℂ := fun k => μ * (rad k : ℂ) with hωdef
  obtain ⟨J, hJ, hyJ⟩ := Set.mem_iUnion₂.mp hy
  obtain ⟨L, hL, hzL⟩ := Set.mem_iUnion₂.mp hz
  have hJf := Finset.mem_filter.mp hJ
  have hLf := Finset.mem_filter.mp hL
  have hqJ : q ∈ J := hJf.2 (Finset.mem_insert_self q A)
  have hqL : q ∈ L := hLf.2 (Finset.mem_insert_self q A)
  have hJcard : (Jᶜ : Finset ι).card = 2 := hfaces J hJf.1
  have hLcard : (Lᶜ : Finset ι).card = 2 := hfaces L hLf.1
  have hyPacket : (meroTranslationPerm (ω q) ^ m) y ∈ facePacket ω hω J := by
    rw [facePacket_eq_orbitUnion ω hω hqJ]
    exact ⟨m, y, hyJ, rfl⟩
  have hzPacket : (meroTranslationPerm (ω q) ^ n) z ∈ facePacket ω hω L := by
    rw [facePacket_eq_orbitUnion ω hω hqL]
    exact ⟨n, z, hzL, rfl⟩
  have hJL : J = L := by
    by_contra hcon
    have hdis := facePacket_disjoint hrad hind hω hJcard hLcard hcon
    rw [Set.disjoint_left] at hdis
    exact hdis hyPacket (hyz ▸ hzPacket)
  subst hJL
  have hne : (Jᶜ : Finset ι).Nonempty := Finset.card_pos.mp (by rw [hJcard]; norm_num)
  obtain ⟨i, j, hij, hpair⟩ := Finset.card_eq_two.mp hJcard
  have hS : ({i, j} : Finset ι).Nonempty := ⟨i, by simp⟩
  have hi : i ∉ J := Finset.mem_compl.mp (by rw [hpair]; simp)
  have hj : j ∉ J := Finset.mem_compl.mp (by rw [hpair]; simp)
  have hsrc : frameSourceMero ω hω (Jᶜ : Finset ι) hne
      = frameSourceMero ω hω ({i, j} : Finset ι) hS :=
    frameSourceMero_congr _ hω hpair hne hS
  set src : meroField (Set.univ : Set ℂ) :=
    frameSourceMero ω hω ({i, j} : Finset ι) hS with hsrcdef
  have hfam := multipleSineCanonicalFaceOrbit_free hrad hind hω hij hi hj hS
  have hC : DifferentialIndependent ℂ
      (fun α : {k // k ∈ J} → ℤ => addTranslationMeroEquiv (faceShift ω J α) src) :=
    DifferentialIndependent.restrictScalarsTower hfam
  rw [facePacketSlice_eq ω hω q hne, hsrc] at hyJ hzL
  obtain ⟨α, hα, rfl⟩ := hyJ
  obtain ⟨β, hβ, rfl⟩ := hzL
  rw [meroTranslationPerm_zpow_apply, meroTranslationPerm_zpow_apply,
    addTranslationMeroEquiv_add, addTranslationMeroEquiv_add] at hyz
  have hy' : (m : ℂ) * ω q + faceShift ω J α
      = faceShift ω J (fun k => if (k : ι) = q then m else α k) := by
    rw [faceShift_update ω hqJ hα m]
    ring
  have hz' : (n : ℂ) * ω q + faceShift ω J β
      = faceShift ω J (fun k => if (k : ι) = q then n else β k) := by
    rw [faceShift_update ω hqJ hβ n]
    ring
  rw [hy', hz'] at hyz
  have hfun := hC.injective hyz
  have hval := congrFun hfun ⟨q, hqJ⟩
  simpa using hval

end

end GaloisForLFunctions.HTGeometry
