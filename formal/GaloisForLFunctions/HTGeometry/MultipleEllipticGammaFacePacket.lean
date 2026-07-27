import GaloisForLFunctions.HTGeometry.MultipleEllipticGammaFaceHierarchy
import GaloisForLFunctions.HTGeometry.OrbitHeightFreeTranslates
import GaloisForLFunctions.HTGeometry.DifferentialUniformFaceGluing
import GaloisForLFunctions.HTGeometry.EllipticGammaRationalBaseMatroid

/-!
# The external orbit packets of the multiple elliptic-gamma faces

The all-order gluing engine consumes, for each deleted face `J`, a packet of germs closed under the
external translations of that face — the translations by the *deleted* parameters `(τ_j)_{j ∈ J}`.
This file defines that packet and shows that it is, in every deleted direction, a union of full
translation orbits.  That is exactly the presentation the orbit form of the gluing theorem asks
for, so the only remaining input in the star hypotheses is injectivity of the exponent, i.e.
nonresonance.

* `faceShiftLattice` — the integer span of the deleted parameters;
* `multipleEllipticGammaFacePacket` — the orbit packet of a deleted face;
* **`multipleEllipticGammaFacePacket_eq_orbitUnion`** — for every deleted direction the packet is
  the union of the full orbits of its zero-exponent slice;
* **`faceStar_eq_orbitUnion`** — hence the whole star of a direction is an orbit union, which is
  what `differentialRank_uniformFace_nestedStar_diffIndepOn_of_orbit` consumes.
-/

open Filter Topology Set Function Complex
open scoped Differential

namespace GaloisForLFunctions

open Bottcher MatroidGluing MatroidGluing.Rank MatroidGluing.Meromorphic

noncomputable section

noncomputable local instance facePacketMeroDecidableEq :
    DecidableEq (meroField (Set.univ : Set ℂ)) := Classical.decEq _

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## Orbit unions of indexed families -/

theorem orbitUnion_iUnion {Ω : Type*} [DecidableEq Ω] {κ : Type*}
    (σ : Equiv.Perm Ω) (b : κ → Set Ω) :
    orbitUnion σ (⋃ i, b i) = ⋃ i, orbitUnion σ (b i) := by
  ext x
  constructor
  · rintro ⟨n, y, hy, rfl⟩
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hy
    exact Set.mem_iUnion.mpr ⟨i, n, y, hi, rfl⟩
  · intro hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
    obtain ⟨n, y, hy, rfl⟩ := hi
    exact ⟨n, y, Set.mem_iUnion.mpr ⟨i, hy⟩, rfl⟩

theorem orbitUnion_biUnion {Ω : Type*} [DecidableEq Ω] {κ : Type*}
    (σ : Equiv.Perm Ω) (s : Finset κ) (b : κ → Set Ω) :
    orbitUnion σ (⋃ i ∈ s, b i) = ⋃ i ∈ s, orbitUnion σ (b i) := by
  ext x
  constructor
  · rintro ⟨n, y, hy, rfl⟩
    obtain ⟨i, hi, hyi⟩ := Set.mem_iUnion₂.mp hy
    exact Set.mem_iUnion₂.mpr ⟨i, hi, n, y, hyi, rfl⟩
  · intro hx
    obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp hx
    obtain ⟨n, y, hy, rfl⟩ := hxi
    exact ⟨n, y, Set.mem_iUnion₂.mpr ⟨i, hi, hy⟩, rfl⟩

/-! ## The external lattice of a deleted face -/

/-- The integer span of the parameters deleted by the face `J`. -/
def faceShiftLattice (τ : ι → ℂ) (J : Finset ι) : Set ℂ :=
  {g | ∃ n : ι → ℤ, (∀ i, i ∉ J → n i = 0) ∧ g = ∑ i, (n i : ℂ) * τ i}

/-- The slice of the external lattice with vanishing exponent in the direction `q`. -/
def faceShiftLatticeSlice (τ : ι → ℂ) (J : Finset ι) (q : ι) : Set ℂ :=
  {g | ∃ n : ι → ℤ, (∀ i, i ∉ J → n i = 0) ∧ n q = 0 ∧ g = ∑ i, (n i : ℂ) * τ i}

omit [DecidableEq ι] in
theorem faceShiftLatticeSlice_subset (τ : ι → ℂ) (J : Finset ι) (q : ι) :
    faceShiftLatticeSlice τ J q ⊆ faceShiftLattice τ J := by
  rintro g ⟨n, hn, _, hg⟩
  exact ⟨n, hn, hg⟩

theorem faceShiftLattice_add_zsmul (τ : ι → ℂ) (J : Finset ι) {q : ι} (hq : q ∈ J)
    {g : ℂ} (hg : g ∈ faceShiftLattice τ J) (m : ℤ) :
    (m : ℂ) * τ q + g ∈ faceShiftLattice τ J := by
  obtain ⟨n, hn, rfl⟩ := hg
  refine ⟨Function.update n q (n q + m), ?_, ?_⟩
  · intro i hi
    rw [Function.update_apply]
    split
    · next h => exact absurd (h ▸ hq) hi
    · exact hn i hi
  · rw [Finset.sum_congr rfl (fun i _ => rfl)]
    have hsplit : ∀ f : ι → ℤ, ∑ i, (f i : ℂ) * τ i =
        (f q : ℂ) * τ q + ∑ i ∈ Finset.univ.erase q, (f i : ℂ) * τ i := by
      intro f
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ q)]
    rw [hsplit (Function.update n q (n q + m)), hsplit n]
    rw [Function.update_self]
    have hcongr : ∑ i ∈ Finset.univ.erase q, ((Function.update n q (n q + m) i : ℤ) : ℂ) * τ i =
        ∑ i ∈ Finset.univ.erase q, (n i : ℂ) * τ i := by
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]
    rw [hcongr]
    push_cast
    ring

/-- Every external lattice vector splits as a `q`-exponent times `τ q` plus a slice vector. -/
theorem exists_slice_of_mem_faceShiftLattice (τ : ι → ℂ) (J : Finset ι) (q : ι)
    {g : ℂ} (hg : g ∈ faceShiftLattice τ J) :
    ∃ (m : ℤ) (g' : ℂ), g' ∈ faceShiftLatticeSlice τ J q ∧ g = (m : ℂ) * τ q + g' := by
  obtain ⟨n, hn, rfl⟩ := hg
  refine ⟨n q, ∑ i, ((Function.update n q 0 i : ℤ) : ℂ) * τ i,
    ⟨Function.update n q 0, ?_, ?_, rfl⟩, ?_⟩
  · intro i hi
    rw [Function.update_apply]
    split
    · rfl
    · exact hn i hi
  · rw [Function.update_self]
  · have hsplit : ∀ f : ι → ℤ, ∑ i, (f i : ℂ) * τ i =
        (f q : ℂ) * τ q + ∑ i ∈ Finset.univ.erase q, (f i : ℂ) * τ i := by
      intro f
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ q)]
    rw [hsplit (Function.update n q 0), hsplit n, Function.update_self]
    have hcongr : ∑ i ∈ Finset.univ.erase q, ((Function.update n q 0 i : ℤ) : ℂ) * τ i =
        ∑ i ∈ Finset.univ.erase q, (n i : ℂ) * τ i := by
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]
    rw [hcongr]
    push_cast
    ring

/-! ## The packet and its orbit presentation -/

/-- The orbit packet of the deleted face `J`: the face coordinate translated by its external
lattice. -/
def multipleEllipticGammaFacePacket (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) (J : Finset ι) :
    Set (meroField (Set.univ : Set ℂ)) :=
  (fun g => addTranslationMeroEquiv g (multipleEllipticGammaLogDerivFaceMero τ hτ J)) ''
    faceShiftLattice τ J

/-- The zero-exponent slice of the packet in the direction `q`. -/
def multipleEllipticGammaFacePacketSlice (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im)
    (J : Finset ι) (q : ι) : Set (meroField (Set.univ : Set ℂ)) :=
  (fun g => addTranslationMeroEquiv g (multipleEllipticGammaLogDerivFaceMero τ hτ J)) ''
    faceShiftLatticeSlice τ J q

/-- **The packet is a union of full orbits in every deleted direction.** -/
theorem multipleEllipticGammaFacePacket_eq_orbitUnion (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im)
    (J : Finset ι) {q : ι} (hq : q ∈ J) :
    multipleEllipticGammaFacePacket τ hτ J =
      orbitUnion (meroTranslationPerm (τ q)) (multipleEllipticGammaFacePacketSlice τ hτ J q) := by
  ext x
  constructor
  · rintro ⟨g, hg, rfl⟩
    obtain ⟨m, g', hg', rfl⟩ := exists_slice_of_mem_faceShiftLattice τ J q hg
    refine ⟨m, addTranslationMeroEquiv g'
      (multipleEllipticGammaLogDerivFaceMero τ hτ J), ⟨g', hg', rfl⟩, ?_⟩
    rw [meroTranslationPerm_zpow_apply, addTranslationMeroEquiv_add]
  · rintro ⟨m, y, ⟨g', hg', rfl⟩, rfl⟩
    refine ⟨(m : ℂ) * τ q + g',
      faceShiftLattice_add_zsmul τ J hq (faceShiftLatticeSlice_subset τ J q hg') m, ?_⟩
    rw [meroTranslationPerm_zpow_apply, addTranslationMeroEquiv_add]

/-- **The star of a direction is an orbit union.**  Every face of the star contains the direction,
so its packet is a union of full orbits, and a union of orbit unions is an orbit union. -/
theorem faceStar_eq_orbitUnion (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im)
    (faces : Finset (Finset ι)) (A : Finset ι) (q : ι) :
    faceStar faces (multipleEllipticGammaFacePacket τ hτ) (insert q A) =
      orbitUnion (meroTranslationPerm (τ q))
        (⋃ J ∈ faces.filter (fun J => insert q A ⊆ J),
          multipleEllipticGammaFacePacketSlice τ hτ J q) := by
  rw [orbitUnion_biUnion]
  rw [faceStar]
  refine Set.iUnion₂_congr fun J hJ => ?_
  have hqJ : q ∈ J := (Finset.mem_filter.mp hJ).2 (Finset.mem_insert_self q A)
  exact multipleEllipticGammaFacePacket_eq_orbitUnion τ hτ J hqJ

/-! ## The concrete all-order star independence -/

attribute [local instance] ellipticGammaRationalBaseDomain
  ellipticGammaRationalBaseComplexAlgebraMero ellipticGammaRationalBaseComplexDifferential
  ellipticGammaRationalBaseMeroDifferential ellipticGammaRationalBaseMeroCharZero
  ellipticGammaRationalBaseComplexDifferentialAlgebra

/-- **All-order star independence of the multiple elliptic-gamma face packets.**  With the packets
of `multipleEllipticGammaFacePacket` and the genuine additive translations as directions, the two
orbit hypotheses of the gluing theorem are supplied by `faceStar_eq_orbitUnion`, so the total star
is jointly differentially independent over the constants as soon as three analytic inputs hold:
each face packet is atomic, distinct exponents in a star direction give distinct germs
(nonresonance), and off-star translated packets are differentially algebraic over the packet they
came from. -/
theorem multipleEllipticGammaFaceStar_diffIndepOn (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im)
    (faces : Finset (Finset ι)) (s : ℕ)
    (huniform : ∀ J ∈ faces, J.card = s)
    (hAtomic : ∀ J ∈ faces, DiffIndepOn ℂ (multipleEllipticGammaFacePacket τ hτ J))
    (hStarInj : ∀ (A : Finset ι) (q : ι), A.card < s → q ∉ A →
      ∀ (m n : ℤ) (y z : meroField (Set.univ : Set ℂ)),
        y ∈ (⋃ J ∈ faces.filter (fun J => insert q A ⊆ J),
          multipleEllipticGammaFacePacketSlice τ hτ J q) →
        z ∈ (⋃ J ∈ faces.filter (fun J => insert q A ⊆ J),
          multipleEllipticGammaFacePacketSlice τ hτ J q) →
        ((addTranslationMeroDifferentialAlgEquiv (τ q)).toAlgEquiv.toEquiv ^ m) y =
          ((addTranslationMeroDifferentialAlgEquiv (τ q)).toAlgEquiv.toEquiv ^ n) z → m = n)
    (hOffDA : ∀ (A : Finset ι) (q : ι), A.card < s → q ∉ A →
      ∀ t : Finset (meroField (Set.univ : Set ℂ)),
        (↑t : Set (meroField (Set.univ : Set ℂ))) ⊆
          (⋃ J ∈ (faces.filter (fun J => A ⊆ J)).filter (fun J => q ∉ J),
            multipleEllipticGammaFacePacket τ hτ J) →
        ∀ n : ℤ, ∀ z, z ∈ (↑(t.image
            ⇑((addTranslationMeroDifferentialAlgEquiv (τ q)).toAlgEquiv.toEquiv ^ n)) :
            Set (meroField (Set.univ : Set ℂ))) →
          DifferentialAlgebraicOver
            (differentialAdjoin ℂ (↑t : Set (meroField (Set.univ : Set ℂ)))) z) :
    DiffIndepOn ℂ (faceStar faces (multipleEllipticGammaFacePacket τ hτ) ∅) := by
  refine differentialRank_uniformFace_nestedStar_diffIndepOn_of_orbit
    faces (multipleEllipticGammaFacePacket τ hτ)
    (fun q => addTranslationMeroDifferentialAlgEquiv (τ q)) s huniform hAtomic
    (fun A q => ⋃ J ∈ faces.filter (fun J => insert q A ⊆ J),
      multipleEllipticGammaFacePacketSlice τ hτ J q)
    (fun A q _ _ => ?_) (fun A q hA hq => hStarInj A q hA hq) hOffDA
  exact faceStar_eq_orbitUnion τ hτ faces A q

end

end GaloisForLFunctions
