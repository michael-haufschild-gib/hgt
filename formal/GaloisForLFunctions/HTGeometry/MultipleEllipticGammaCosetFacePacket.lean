import GaloisForLFunctions.HTGeometry.MultipleEllipticGammaFacePacket

/-!
# Coset-labelled external packets of the multiple elliptic-gamma faces

`multipleEllipticGammaFacePacket` translates a face coordinate by the *integral* span of its
deleted parameters.  The all-depth compatible pair-face theorem needs the packet translated by an
arbitrary complex shift as well: the label set of the theorem is a set of representatives for
`ℂ / (ℤ + ∑ ℤ τ_i)`, and every finite differential-translation operator decomposes into finitely
many such orbits.

This file introduces the labelled shift set and its packet, and shows that the labelled packet
still has the orbit presentation the all-order gluing engine consumes.  The label is inert for the
gluing: the star of a direction is still a union of full translation orbits.

* `fullPeriodLattice` — the lattice `ℤ + ∑_i ℤ τ_i` of the whole hierarchy;
* `CosetSeparated` — distinct labels differ by a non-period;
* `cosetFaceShiftSet` — the labelled external shift set of a deleted face;
* `cosetFacePacket` — its packet;
* **`cosetFacePacket_eq_orbitUnion`**, **`cosetFaceStar_eq_orbitUnion`** — the orbit presentation;
* **`cosetFaceStar_diffIndepOn`** — the all-order star gluing theorem for labelled packets.
-/

open Filter Topology Set Function Complex
open scoped Differential BigOperators

namespace GaloisForLFunctions

open Bottcher MatroidGluing MatroidGluing.Rank MatroidGluing.Meromorphic

noncomputable section

attribute [local instance] facePacketMeroDecidableEq

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## The full period lattice and separated label sets -/

/-- The full period lattice `ℤ + ∑_i ℤ τ_i` of the hierarchy. -/
def fullPeriodLattice (τ : ι → ℂ) : Set ℂ :=
  {g | ∃ (m : ℤ) (n : ι → ℤ), g = (m : ℂ) + ∑ i, (n i : ℂ) * τ i}

omit [DecidableEq ι] in
theorem zero_mem_fullPeriodLattice (τ : ι → ℂ) : (0 : ℂ) ∈ fullPeriodLattice τ :=
  ⟨0, fun _ => 0, by simp⟩

omit [DecidableEq ι] in
theorem sub_mem_fullPeriodLattice (τ : ι → ℂ) {x y : ℂ}
    (hx : x ∈ fullPeriodLattice τ) (hy : y ∈ fullPeriodLattice τ) :
    x - y ∈ fullPeriodLattice τ := by
  obtain ⟨m, n, rfl⟩ := hx
  obtain ⟨m', n', rfl⟩ := hy
  refine ⟨m - m', fun i => n i - n' i, ?_⟩
  have hs : ∑ i, (((n i - n' i : ℤ)) : ℂ) * τ i =
      (∑ i, (n i : ℂ) * τ i) - ∑ i, (n' i : ℂ) * τ i := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by push_cast; ring
  rw [hs]
  push_cast
  ring

omit [DecidableEq ι] in
theorem add_mem_fullPeriodLattice (τ : ι → ℂ) {x y : ℂ}
    (hx : x ∈ fullPeriodLattice τ) (hy : y ∈ fullPeriodLattice τ) :
    x + y ∈ fullPeriodLattice τ := by
  obtain ⟨m, n, rfl⟩ := hx
  obtain ⟨m', n', rfl⟩ := hy
  refine ⟨m + m', fun i => n i + n' i, ?_⟩
  have hs : ∑ i, (((n i + n' i : ℤ)) : ℂ) * τ i =
      (∑ i, (n i : ℂ) * τ i) + ∑ i, (n' i : ℂ) * τ i := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by push_cast; ring
  rw [hs]
  push_cast
  ring

omit [DecidableEq ι] in
theorem faceShiftLattice_subset_fullPeriodLattice (τ : ι → ℂ) (J : Finset ι) :
    faceShiftLattice τ J ⊆ fullPeriodLattice τ := by
  rintro g ⟨n, -, rfl⟩
  exact ⟨0, n, by simp⟩

/-- A set of external translation labels is *coset separated* when distinct labels differ by a
non-period, i.e. when it injects into `ℂ / (ℤ + ∑_i ℤ τ_i)`. -/
def CosetSeparated (τ : ι → ℂ) (A : Set ℂ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, a ≠ b → (a - b) ∉ fullPeriodLattice τ

omit [DecidableEq ι] in
theorem CosetSeparated.mono {τ : ι → ℂ} {A B : Set ℂ} (h : CosetSeparated τ B) (hAB : A ⊆ B) :
    CosetSeparated τ A := fun a ha b hb hab => h a (hAB ha) b (hAB hb) hab

/-! ## The labelled external shift set of a face -/

/-- The labelled external shift set of the deleted face `J`. -/
def cosetFaceShiftSet (τ : ι → ℂ) (A : Set ℂ) (J : Finset ι) : Set ℂ :=
  {g | ∃ a ∈ A, ∃ h ∈ faceShiftLattice τ J, g = a + h}

/-- Its slice with vanishing exponent in the direction `q`. -/
def cosetFaceShiftSetSlice (τ : ι → ℂ) (A : Set ℂ) (J : Finset ι) (q : ι) : Set ℂ :=
  {g | ∃ a ∈ A, ∃ h ∈ faceShiftLatticeSlice τ J q, g = a + h}

omit [DecidableEq ι] in
theorem cosetFaceShiftSetSlice_subset (τ : ι → ℂ) (A : Set ℂ) (J : Finset ι) (q : ι) :
    cosetFaceShiftSetSlice τ A J q ⊆ cosetFaceShiftSet τ A J := by
  rintro g ⟨a, ha, h, hh, rfl⟩
  exact ⟨a, ha, h, faceShiftLatticeSlice_subset τ J q hh, rfl⟩

theorem cosetFaceShiftSet_add_zsmul (τ : ι → ℂ) (A : Set ℂ) (J : Finset ι) {q : ι} (hq : q ∈ J)
    {g : ℂ} (hg : g ∈ cosetFaceShiftSet τ A J) (m : ℤ) :
    (m : ℂ) * τ q + g ∈ cosetFaceShiftSet τ A J := by
  obtain ⟨a, ha, h, hh, rfl⟩ := hg
  refine ⟨a, ha, (m : ℂ) * τ q + h, faceShiftLattice_add_zsmul τ J hq hh m, by ring⟩

/-- Every labelled shift splits as a `q`-exponent times `τ q` plus a labelled slice vector. -/
theorem exists_slice_of_mem_cosetFaceShiftSet (τ : ι → ℂ) (A : Set ℂ) (J : Finset ι) (q : ι)
    {g : ℂ} (hg : g ∈ cosetFaceShiftSet τ A J) :
    ∃ (m : ℤ) (g' : ℂ), g' ∈ cosetFaceShiftSetSlice τ A J q ∧ g = (m : ℂ) * τ q + g' := by
  obtain ⟨a, ha, h, hh, rfl⟩ := hg
  obtain ⟨m, h', hh', rfl⟩ := exists_slice_of_mem_faceShiftLattice τ J q hh
  exact ⟨m, a + h', ⟨a, ha, h', hh', rfl⟩, by ring⟩

omit [DecidableEq ι] in
/-- **Faithful labelling of the shift set.**  Under coset separation, the label and the lattice
part of a labelled shift are uniquely determined. -/
theorem cosetFaceShiftSet_label_unique (τ : ι → ℂ) {A : Set ℂ} (hA : CosetSeparated τ A)
    (J : Finset ι) {a a' h h' : ℂ} (ha : a ∈ A) (ha' : a' ∈ A)
    (hh : h ∈ faceShiftLattice τ J) (hh' : h' ∈ faceShiftLattice τ J)
    (heq : a + h = a' + h') : a = a' ∧ h = h' := by
  by_cases haa : a = a'
  · subst haa
    exact ⟨rfl, by linear_combination heq⟩
  · exfalso
    refine hA a ha a' ha' haa ?_
    have hsub : a - a' = h' - h := by linear_combination heq
    rw [hsub]
    exact sub_mem_fullPeriodLattice τ (faceShiftLattice_subset_fullPeriodLattice τ J hh')
      (faceShiftLattice_subset_fullPeriodLattice τ J hh)

/-! ## The labelled packet -/

/-- The labelled orbit packet of the deleted face `J`. -/
def cosetFacePacket (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) (A : Set ℂ) (J : Finset ι) :
    Set (meroField (Set.univ : Set ℂ)) :=
  (fun g => addTranslationMeroEquiv g (multipleEllipticGammaLogDerivFaceMero τ hτ J)) ''
    cosetFaceShiftSet τ A J

/-- The zero-exponent slice of the labelled packet in the direction `q`. -/
def cosetFacePacketSlice (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) (A : Set ℂ)
    (J : Finset ι) (q : ι) : Set (meroField (Set.univ : Set ℂ)) :=
  (fun g => addTranslationMeroEquiv g (multipleEllipticGammaLogDerivFaceMero τ hτ J)) ''
    cosetFaceShiftSetSlice τ A J q

theorem cosetFacePacket_eq_facePacket_of_zero (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im)
    (J : Finset ι) :
    cosetFacePacket τ hτ ({0} : Set ℂ) J = multipleEllipticGammaFacePacket τ hτ J := by
  rw [cosetFacePacket, multipleEllipticGammaFacePacket]
  congr 1
  ext g
  constructor
  · rintro ⟨a, ha, h, hh, rfl⟩
    rw [Set.mem_singleton_iff] at ha
    subst ha
    simpa using hh
  · intro hg
    exact ⟨0, rfl, g, hg, by ring⟩

/-- **The labelled packet is a union of full orbits in every deleted direction.** -/
theorem cosetFacePacket_eq_orbitUnion (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) (A : Set ℂ)
    (J : Finset ι) {q : ι} (hq : q ∈ J) :
    cosetFacePacket τ hτ A J =
      orbitUnion (meroTranslationPerm (τ q)) (cosetFacePacketSlice τ hτ A J q) := by
  ext x
  constructor
  · rintro ⟨g, hg, rfl⟩
    obtain ⟨m, g', hg', rfl⟩ := exists_slice_of_mem_cosetFaceShiftSet τ A J q hg
    refine ⟨m, addTranslationMeroEquiv g'
      (multipleEllipticGammaLogDerivFaceMero τ hτ J), ⟨g', hg', rfl⟩, ?_⟩
    rw [meroTranslationPerm_zpow_apply, addTranslationMeroEquiv_add]
  · rintro ⟨m, y, ⟨g', hg', rfl⟩, rfl⟩
    refine ⟨(m : ℂ) * τ q + g',
      cosetFaceShiftSet_add_zsmul τ A J hq (cosetFaceShiftSetSlice_subset τ A J q hg') m, ?_⟩
    rw [meroTranslationPerm_zpow_apply, addTranslationMeroEquiv_add]

/-- **The star of a direction is an orbit union.** -/
theorem cosetFaceStar_eq_orbitUnion (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) (A : Set ℂ)
    (faces : Finset (Finset ι)) (B : Finset ι) (q : ι) :
    faceStar faces (cosetFacePacket τ hτ A) (insert q B) =
      orbitUnion (meroTranslationPerm (τ q))
        (⋃ J ∈ faces.filter (fun J => insert q B ⊆ J),
          cosetFacePacketSlice τ hτ A J q) := by
  rw [orbitUnion_biUnion]
  rw [faceStar]
  refine Set.iUnion₂_congr fun J hJ => ?_
  have hqJ : q ∈ J := (Finset.mem_filter.mp hJ).2 (Finset.mem_insert_self q B)
  exact cosetFacePacket_eq_orbitUnion τ hτ A J hqJ

/-! ## The labelled all-order star theorem -/

attribute [local instance] ellipticGammaRationalBaseDomain
  ellipticGammaRationalBaseComplexAlgebraMero ellipticGammaRationalBaseComplexDifferential
  ellipticGammaRationalBaseMeroDifferential ellipticGammaRationalBaseMeroCharZero
  ellipticGammaRationalBaseComplexDifferentialAlgebra

/-- **All-order star independence for labelled packets.**  The coset label is inert for the
gluing: the orbit hypotheses of the abstract engine are supplied by `cosetFaceStar_eq_orbitUnion`,
so only the three analytic inputs remain. -/
theorem cosetFaceStar_diffIndepOn (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) (A : Set ℂ)
    (faces : Finset (Finset ι)) (s : ℕ)
    (huniform : ∀ J ∈ faces, J.card = s)
    (hAtomic : ∀ J ∈ faces, DiffIndepOn ℂ (cosetFacePacket τ hτ A J))
    (hStarInj : ∀ (B : Finset ι) (q : ι), B.card < s → q ∉ B →
      ∀ (m n : ℤ) (y z : meroField (Set.univ : Set ℂ)),
        y ∈ (⋃ J ∈ faces.filter (fun J => insert q B ⊆ J),
          cosetFacePacketSlice τ hτ A J q) →
        z ∈ (⋃ J ∈ faces.filter (fun J => insert q B ⊆ J),
          cosetFacePacketSlice τ hτ A J q) →
        ((addTranslationMeroDifferentialAlgEquiv (τ q)).toAlgEquiv.toEquiv ^ m) y =
          ((addTranslationMeroDifferentialAlgEquiv (τ q)).toAlgEquiv.toEquiv ^ n) z → m = n)
    (hOffDA : ∀ (B : Finset ι) (q : ι), B.card < s → q ∉ B →
      ∀ t : Finset (meroField (Set.univ : Set ℂ)),
        (↑t : Set (meroField (Set.univ : Set ℂ))) ⊆
          (⋃ J ∈ (faces.filter (fun J => B ⊆ J)).filter (fun J => q ∉ J),
            cosetFacePacket τ hτ A J) →
        ∀ n : ℤ, ∀ z, z ∈ (↑(t.image
            ⇑((addTranslationMeroDifferentialAlgEquiv (τ q)).toAlgEquiv.toEquiv ^ n)) :
            Set (meroField (Set.univ : Set ℂ))) →
          DifferentialAlgebraicOver
            (differentialAdjoin ℂ (↑t : Set (meroField (Set.univ : Set ℂ)))) z) :
    DiffIndepOn ℂ (faceStar faces (cosetFacePacket τ hτ A) ∅) := by
  refine differentialRank_uniformFace_nestedStar_diffIndepOn_of_orbit
    faces (cosetFacePacket τ hτ A)
    (fun q => addTranslationMeroDifferentialAlgEquiv (τ q)) s huniform hAtomic
    (fun B q => ⋃ J ∈ faces.filter (fun J => insert q B ⊆ J),
      cosetFacePacketSlice τ hτ A J q)
    (fun B q _ _ => ?_) (fun B q hB hq => hStarInj B q hB hq) hOffDA
  exact cosetFaceStar_eq_orbitUnion τ hτ A faces B q

end

end GaloisForLFunctions
