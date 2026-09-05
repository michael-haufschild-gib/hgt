import GaloisForLFunctions.HTGeometry.MultipleSineBottomCubeSeparation

/-!
# Separation of the packets of distinct multiple-sine faces

Differencing along the surviving directions of a face collapses its coordinate to that of a maximal
face, modulo the rational coordinate field.  Two distinct faces can be collapsed simultaneously:
either they nest, and then a single maximal face receives a translate from one and a nontrivial
difference cube from the other, or they are incomparable, and then two *distinct* maximal faces
receive difference cubes.  Both configurations are excluded over the bottom layer, so translates of
the coordinates of distinct faces never agree, even modulo `ℂ(z)`.

* **`frameSource_translate_sub_notMem_rational`** — separation of distinct faces;
* **`facePacket_disjoint_of_two_le`** — hence distinct face packets are disjoint.
-/

open Filter Set Topology Complex
open scoped Differential BigOperators

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions Bottcher

noncomputable section

attribute [local instance] ellipticGammaRationalBaseDomain
  ellipticGammaRationalBaseComplexAlgebraMero ellipticGammaRationalBaseComplexDifferential
  ellipticGammaRationalBaseMeroDifferential ellipticGammaRationalBaseMeroCharZero
  ellipticGammaRationalBaseComplexDifferentialAlgebra
  ellipticGammaRationalBaseCoordinateDifferential
  ellipticGammaRationalBaseCoordinateDifferentialAlgebra

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ### The difference cube is additive and preserves the rational base -/

omit [Fintype ι] [DecidableEq ι] in
theorem faceDifferenceCube_sub (ω : ι → ℂ) (U : Finset ι) (g : ℂ)
    (x y : meroField (Set.univ : Set ℂ)) :
    faceDifferenceCube ω U g (x - y)
      = faceDifferenceCube ω U g x - faceDifferenceCube ω U g y := by
  simp only [faceDifferenceCube, map_sub, mul_sub]
  rw [Finset.sum_sub_distrib]

omit [Fintype ι] [DecidableEq ι] in
theorem faceDifferenceCube_add (ω : ι → ℂ) (U : Finset ι) (g : ℂ)
    (x y : meroField (Set.univ : Set ℂ)) :
    faceDifferenceCube ω U g (x + y)
      = faceDifferenceCube ω U g x + faceDifferenceCube ω U g y := by
  simp only [faceDifferenceCube, map_add, mul_add]
  rw [Finset.sum_add_distrib]

omit [Fintype ι] [DecidableEq ι] in
theorem faceDifferenceCube_neg_one_pow_mul (ω : ι → ℂ) (U : Finset ι) (g : ℂ) (m : ℕ)
    (x : meroField (Set.univ : Set ℂ)) :
    faceDifferenceCube ω U g ((-1 : meroField (Set.univ : Set ℂ)) ^ m * x)
      = (-1 : meroField (Set.univ : Set ℂ)) ^ m * faceDifferenceCube ω U g x := by
  simp only [faceDifferenceCube, map_mul, map_pow, map_neg, map_one, Finset.mul_sum]
  exact Finset.sum_congr rfl fun E _ => by ring

omit [Fintype ι] [DecidableEq ι] in
theorem faceDifferenceCube_mem_rationalCoordinateField (ω : ι → ℂ) (U : Finset ι) (g : ℂ)
    {x : meroField (Set.univ : Set ℂ)} (hx : x ∈ meromorphicRationalCoordinateField) :
    faceDifferenceCube ω U g x ∈ meromorphicRationalCoordinateField := by
  rw [faceDifferenceCube]
  refine sum_mem fun E _ => mul_mem ?_ ?_
  · exact pow_mem (neg_mem (one_mem meromorphicRationalCoordinateField)) _
  · exact addTranslationMeroAlgEquiv_mem_rationalCoordinateField _ hx

omit [Fintype ι] [DecidableEq ι] in
theorem faceDifferenceCube_zero_translate (ω : ι → ℂ) (U : Finset ι) (g : ℂ)
    (f : meroField (Set.univ : Set ℂ)) :
    faceDifferenceCube ω U 0 (addTranslationMeroEquiv g f) = faceDifferenceCube ω U g f := by
  rw [faceDifferenceCube_translate, zero_add]

/-! ### Collapsing a face coordinate onto a maximal face -/

set_option synthInstance.maxHeartbeats 1000000 in
/-- **The two-step collapse.**  Differencing first along the surviving directions that separate a
face from a shallower one, then along directions of the shallower face, turns the deeper face
coordinate into a difference cube of the shallower one, modulo the rational coordinate field. -/
theorem faceDifferenceCube_reduce (ω : ι → ℂ) (hω : ∀ k, 0 < (ω k).im)
    {J K : Finset ι} (hJne : (Jᶜ : Finset ι).Nonempty) (hKne : (Kᶜ : Finset ι).Nonempty)
    (V P : Finset ι) (hVJ : Disjoint V J) (hVP : Disjoint V P) (hK : J ∪ V = K) (g : ℂ) :
    faceDifferenceCube ω (V ∪ P) g (frameSourceMero ω hω (Jᶜ : Finset ι) hJne)
        - (-1 : meroField (Set.univ : Set ℂ)) ^ V.card *
          faceDifferenceCube ω P g (frameSourceMero ω hω (Kᶜ : Finset ι) hKne)
      ∈ meromorphicRationalCoordinateField := by
  classical
  have hKne' : ((J ∪ V)ᶜ : Finset ι).Nonempty := by rw [hK]; exact hKne
  have hstep := faceDifferenceCube_frameSource ω hω J hJne g V hVJ hKne'
  set F : meroField (Set.univ : Set ℂ) := frameSourceMero ω hω (Jᶜ : Finset ι) hJne with hF
  set G : meroField (Set.univ : Set ℂ) := frameSourceMero ω hω (Kᶜ : Finset ι) hKne with hG
  have hsrc : frameSourceMero ω hω ((J ∪ V)ᶜ : Finset ι) hKne' = G :=
    frameSourceMero_congr ω hω (by rw [hK]) hKne' hKne
  rw [hsrc] at hstep
  have hsplit : faceDifferenceCube ω (V ∪ P) g F
      = faceDifferenceCube ω P 0 (faceDifferenceCube ω V g F) :=
    faceDifferenceCube_union ω V P hVP g F
  have hdecomp : faceDifferenceCube ω V g F
      = (faceDifferenceCube ω V g F
          - (-1 : meroField (Set.univ : Set ℂ)) ^ V.card * addTranslationMeroEquiv g G)
        + (-1 : meroField (Set.univ : Set ℂ)) ^ V.card * addTranslationMeroEquiv g G := by
    ring
  have hlin : faceDifferenceCube ω P 0 (faceDifferenceCube ω V g F)
      = faceDifferenceCube ω P 0 (faceDifferenceCube ω V g F
            - (-1 : meroField (Set.univ : Set ℂ)) ^ V.card * addTranslationMeroEquiv g G)
        + (-1 : meroField (Set.univ : Set ℂ)) ^ V.card * faceDifferenceCube ω P g G := by
    conv_lhs => rw [hdecomp]
    rw [faceDifferenceCube_add, faceDifferenceCube_neg_one_pow_mul,
      faceDifferenceCube_zero_translate]
  rw [hsplit, hlin]
  have hmem := faceDifferenceCube_mem_rationalCoordinateField ω P 0 hstep
  simpa using hmem

/-! ### Separation of nested faces -/

set_option synthInstance.maxHeartbeats 1000000 in
/-- **Nested faces are separated.**  A translate of a deeper face coordinate never agrees, modulo
the rational coordinate field, with a translate of the coordinate of a strictly shallower face. -/
theorem frameSource_translate_sub_notMem_rational_of_ssubset {μ : ℂ} {rad : ι → ℝ}
    (hrad : ∀ k, 0 < rad k)
    (hind : LinearIndependent ℚ (fun k => μ * (rad k : ℂ)))
    (hω : ∀ k, 0 < (μ * (rad k : ℂ)).im)
    {J L : Finset ι} (hJL : J ⊆ L) (hne : J ≠ L) (hL : 2 ≤ (Lᶜ : Finset ι).card)
    (hneJ : (Jᶜ : Finset ι).Nonempty) (hneL : (Lᶜ : Finset ι).Nonempty)
    {g h : ℂ} (hg : g ∈ faceShiftLattice (fun k => μ * (rad k : ℂ)) J)
    (hh : h ∈ faceShiftLattice (fun k => μ * (rad k : ℂ)) L) :
    addTranslationMeroEquiv g
          (frameSourceMero (fun k => μ * (rad k : ℂ)) hω (Jᶜ : Finset ι) hneJ)
        - addTranslationMeroEquiv h
          (frameSourceMero (fun k => μ * (rad k : ℂ)) hω (Lᶜ : Finset ι) hneL)
      ∉ meromorphicRationalCoordinateField := by
  classical
  set ω : ι → ℂ := fun k => μ * (rad k : ℂ) with hωdef
  intro hcon
  obtain ⟨A, hAsub, hAcard⟩ := Finset.exists_subset_card_eq hL
  set K : Finset ι := Aᶜ with hKdef
  have hKc : (Kᶜ : Finset ι) = A := by rw [hKdef, compl_compl]
  have hKcard : (Kᶜ : Finset ι).card = 2 := by rw [hKc, hAcard]
  have hKne : (Kᶜ : Finset ι).Nonempty := Finset.card_pos.mp (by rw [hKcard]; omega)
  have hLK : L ⊆ K := by
    intro x hx
    rw [hKdef, Finset.mem_compl]
    intro hxA
    exact (Finset.mem_compl.mp (hAsub hxA)) hx
  have hJK : J ⊆ K := hJL.trans hLK
  set V : Finset ι := K \ J with hV
  set W : Finset ι := K \ L with hW
  set P : Finset ι := L \ J with hP
  have hVJ : Disjoint V J := by
    rw [hV, Finset.disjoint_left]
    intro x hx
    exact (Finset.mem_sdiff.mp hx).2
  have hWL : Disjoint W L := by
    rw [hW, Finset.disjoint_left]
    intro x hx
    exact (Finset.mem_sdiff.mp hx).2
  have hWP : Disjoint W P := by
    rw [hW, hP, Finset.disjoint_left]
    intro x hx hxP
    exact (Finset.mem_sdiff.mp hx).2 (Finset.mem_sdiff.mp hxP).1
  have hJV : J ∪ V = K := by
    rw [hV]
    ext x
    simp only [Finset.mem_union, Finset.mem_sdiff]
    exact ⟨fun hx => hx.elim (fun h => hJK h) (fun h => h.1),
      fun hx => by by_cases hxJ : x ∈ J <;> simp [hxJ, hx]⟩
  have hLW : L ∪ W = K := by
    rw [hW]
    ext x
    simp only [Finset.mem_union, Finset.mem_sdiff]
    exact ⟨fun hx => hx.elim (fun h => hLK h) (fun h => h.1),
      fun hx => by by_cases hxL : x ∈ L <;> simp [hxL, hx]⟩
  have hVWP : V = W ∪ P := by
    rw [hV, hW, hP]
    ext x
    simp only [Finset.mem_union, Finset.mem_sdiff]
    constructor
    · rintro ⟨hxK, hxJ⟩
      by_cases hxL : x ∈ L
      · exact Or.inr ⟨hxL, hxJ⟩
      · exact Or.inl ⟨hxK, hxL⟩
    · rintro (⟨hxK, hxL⟩ | ⟨hxL, hxJ⟩)
      · exact ⟨hxK, fun hxJ => hxL (hJL hxJ)⟩
      · exact ⟨hLK hxL, hxJ⟩
  have hPne : P.Nonempty := by
    rw [hP]
    have hss : J ⊂ L := lt_of_le_of_ne hJL hne
    obtain ⟨p, hpL, hpJ⟩ := Finset.exists_of_ssubset hss
    exact ⟨p, Finset.mem_sdiff.mpr ⟨hpL, hpJ⟩⟩
  have hVemptyP : V ∪ ∅ = V := Finset.union_empty V
  -- collapse both sides onto the maximal face `K`
  have hredJ := faceDifferenceCube_reduce ω hω hneJ hKne V (∅ : Finset ι) hVJ
    (by simp) hJV g
  rw [hVemptyP] at hredJ
  have hredL := faceDifferenceCube_reduce ω hω hneL hKne W P hWL hWP hLW h
  rw [← hVWP] at hredL
  have hcube : faceDifferenceCube ω V g
        (frameSourceMero ω hω (Jᶜ : Finset ι) hneJ)
      - faceDifferenceCube ω V h (frameSourceMero ω hω (Lᶜ : Finset ι) hneL)
      ∈ meromorphicRationalCoordinateField := by
    have hmem := faceDifferenceCube_mem_rationalCoordinateField ω V 0 hcon
    rwa [faceDifferenceCube_sub, faceDifferenceCube_zero_translate,
      faceDifferenceCube_zero_translate] at hmem
  have hempty : faceDifferenceCube ω (∅ : Finset ι) g
      (frameSourceMero ω hω (Kᶜ : Finset ι) hKne)
      = addTranslationMeroEquiv g (frameSourceMero ω hω (Kᶜ : Finset ι) hKne) :=
    faceDifferenceCube_empty ω g _
  rw [hempty] at hredJ
  have hfinal : (-1 : meroField (Set.univ : Set ℂ)) ^ V.card *
        addTranslationMeroEquiv g (frameSourceMero ω hω (Kᶜ : Finset ι) hKne)
      - (-1 : meroField (Set.univ : Set ℂ)) ^ W.card *
        faceDifferenceCube ω P h (frameSourceMero ω hω (Kᶜ : Finset ι) hKne)
      ∈ meromorphicRationalCoordinateField := by
    have hid : (-1 : meroField (Set.univ : Set ℂ)) ^ V.card *
          addTranslationMeroEquiv g (frameSourceMero ω hω (Kᶜ : Finset ι) hKne)
        - (-1 : meroField (Set.univ : Set ℂ)) ^ W.card *
          faceDifferenceCube ω P h (frameSourceMero ω hω (Kᶜ : Finset ι) hKne)
        = -(faceDifferenceCube ω V g (frameSourceMero ω hω (Jᶜ : Finset ι) hneJ)
              - (-1 : meroField (Set.univ : Set ℂ)) ^ V.card *
                addTranslationMeroEquiv g (frameSourceMero ω hω (Kᶜ : Finset ι) hKne))
          + (faceDifferenceCube ω V h (frameSourceMero ω hω (Lᶜ : Finset ι) hneL)
              - (-1 : meroField (Set.univ : Set ℂ)) ^ W.card *
                faceDifferenceCube ω P h (frameSourceMero ω hω (Kᶜ : Finset ι) hKne))
          + (faceDifferenceCube ω V g (frameSourceMero ω hω (Jᶜ : Finset ι) hneJ)
              - faceDifferenceCube ω V h
                (frameSourceMero ω hω (Lᶜ : Finset ι) hneL)) := by
      ring
    rw [hid]
    exact add_mem (add_mem (neg_mem hredJ) hredL) hcube
  -- the two collapsed data are separated over the bottom layer
  obtain ⟨p, hpP⟩ := hPne
  have hPK : P ⊆ K := fun x hx => hLK (Finset.mem_sdiff.mp hx).1
  have hgK : g ∈ faceShiftLattice ω K := faceShiftLattice_mono ω hJK hg
  have hhK : h ∈ faceShiftLattice ω K := faceShiftLattice_mono ω hLK hh
  have hωp : ω p ≠ 0 := by
    intro hzero
    have hval : μ * (rad p : ℂ) = 0 := by rw [← congrFun hωdef p]; exact hzero
    have hpos := hω p
    rw [hval] at hpos
    simp at hpos
  rcases eq_or_ne h g with hhg | hhg
  · refine bottom_translate_sub_cube_notMem_rational hrad hind hω hKcard hKne P hPK hgK hhK
      ({p} : Finset ι) (Finset.mem_powerset.mpr (by simpa using hpP)) ?_ V.card W.card hfinal
    rw [Finset.sum_singleton, hhg]
    intro hcon'
    exact hωp (by linear_combination hcon')
  · refine bottom_translate_sub_cube_notMem_rational hrad hind hω hKcard hKne P hPK hgK hhK
      (∅ : Finset ι) (Finset.empty_mem_powerset P) ?_ V.card W.card hfinal
    simpa using hhg

/-! ### Separation of incomparable faces -/

set_option synthInstance.maxHeartbeats 1000000 in
/-- **Incomparable faces are separated.** -/
theorem frameSource_translate_sub_notMem_rational_of_incomparable {μ : ℂ} {rad : ι → ℝ}
    (hrad : ∀ k, 0 < rad k)
    (hind : LinearIndependent ℚ (fun k => μ * (rad k : ℂ)))
    (hω : ∀ k, 0 < (μ * (rad k : ℂ)).im)
    {J L : Finset ι} (hJL : ¬ J ⊆ L) (hLJ : ¬ L ⊆ J)
    (hJ : 2 ≤ (Jᶜ : Finset ι).card) (hL : 2 ≤ (Lᶜ : Finset ι).card)
    (hneJ : (Jᶜ : Finset ι).Nonempty) (hneL : (Lᶜ : Finset ι).Nonempty)
    {g h : ℂ} (hg : g ∈ faceShiftLattice (fun k => μ * (rad k : ℂ)) J)
    (hh : h ∈ faceShiftLattice (fun k => μ * (rad k : ℂ)) L) :
    addTranslationMeroEquiv g
          (frameSourceMero (fun k => μ * (rad k : ℂ)) hω (Jᶜ : Finset ι) hneJ)
        - addTranslationMeroEquiv h
          (frameSourceMero (fun k => μ * (rad k : ℂ)) hω (Lᶜ : Finset ι) hneL)
      ∉ meromorphicRationalCoordinateField := by
  classical
  set ω : ι → ℂ := fun k => μ * (rad k : ℂ) with hωdef
  intro hcon
  have hST : ¬ (Jᶜ : Finset ι) ⊆ (Lᶜ : Finset ι) := by
    intro hsub
    refine hLJ (fun x hxL => ?_)
    by_contra hxJ
    exact (Finset.mem_compl.mp (hsub (Finset.mem_compl.mpr hxJ))) hxL
  have hTS : ¬ (Lᶜ : Finset ι) ⊆ (Jᶜ : Finset ι) := by
    intro hsub
    refine hJL (fun x hxJ => ?_)
    by_contra hxL
    exact (Finset.mem_compl.mp (hsub (Finset.mem_compl.mpr hxL))) hxJ
  obtain ⟨A, B, hAS, hBT, hAcard, hBcard, hAB, hcompat⟩ :=
    exists_compatible_two_subsets_of_incomparable (Jᶜ : Finset ι) (Lᶜ : Finset ι) hJ hL hST hTS
  set K : Finset ι := Aᶜ with hKdef
  set M : Finset ι := Bᶜ with hMdef
  have hKc : (Kᶜ : Finset ι) = A := by rw [hKdef, compl_compl]
  have hMc : (Mᶜ : Finset ι) = B := by rw [hMdef, compl_compl]
  have hKcard : (Kᶜ : Finset ι).card = 2 := by rw [hKc, hAcard]
  have hMcard : (Mᶜ : Finset ι).card = 2 := by rw [hMc, hBcard]
  have hKne : (Kᶜ : Finset ι).Nonempty := Finset.card_pos.mp (by rw [hKcard]; omega)
  have hMne : (Mᶜ : Finset ι).Nonempty := Finset.card_pos.mp (by rw [hMcard]; omega)
  have hKM : K ≠ M := by
    intro hcon'
    exact hAB (by rw [← hKc, ← hMc, hcon'])
  have hJK : J ⊆ K := by
    intro x hx
    rw [hKdef, Finset.mem_compl]
    intro hxA
    exact (Finset.mem_compl.mp (hAS hxA)) hx
  have hLM : L ⊆ M := by
    intro x hx
    rw [hMdef, Finset.mem_compl]
    intro hxB
    exact (Finset.mem_compl.mp (hBT hxB)) hx
  set V : Finset ι := (Jᶜ : Finset ι) \ A with hV
  set W : Finset ι := (Lᶜ : Finset ι) \ B with hW
  have hVJ : Disjoint V J := by
    rw [hV, Finset.disjoint_left]
    intro x hx
    exact Finset.mem_compl.mp (Finset.mem_sdiff.mp hx).1
  have hWL : Disjoint W L := by
    rw [hW, Finset.disjoint_left]
    intro x hx
    exact Finset.mem_compl.mp (Finset.mem_sdiff.mp hx).1
  have hJV : J ∪ V = K := by
    rw [hV, hKdef]
    ext x
    simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_compl]
    constructor
    · rintro (hxJ | ⟨-, hxA⟩)
      · intro hxA
        exact (Finset.mem_compl.mp (hAS hxA)) hxJ
      · exact hxA
    · intro hxA
      by_cases hxJ : x ∈ J
      · exact Or.inl hxJ
      · exact Or.inr ⟨hxJ, hxA⟩
  have hLW : L ∪ W = M := by
    rw [hW, hMdef]
    ext x
    simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_compl]
    constructor
    · rintro (hxL | ⟨-, hxB⟩)
      · intro hxB
        exact (Finset.mem_compl.mp (hBT hxB)) hxL
      · exact hxB
    · intro hxB
      by_cases hxL : x ∈ L
      · exact Or.inl hxL
      · exact Or.inr ⟨hxL, hxB⟩
  have hWsubV : ∀ x ∈ W, x ∉ J → x ∈ V := by
    intro x hxW hxJ
    have hxT : x ∈ (Lᶜ : Finset ι) := (Finset.mem_sdiff.mp hxW).1
    have hxB : x ∉ B := (Finset.mem_sdiff.mp hxW).2
    refine Finset.mem_sdiff.mpr ⟨Finset.mem_compl.mpr hxJ, fun hxA => hxB ?_⟩
    have hxAT : x ∈ A ∩ (Lᶜ : Finset ι) := Finset.mem_inter.mpr ⟨hxA, hxT⟩
    rw [hcompat] at hxAT
    exact (Finset.mem_inter.mp hxAT).1
  have hVsubW : ∀ x ∈ V, x ∉ L → x ∈ W := by
    intro x hxV hxL
    have hxS : x ∈ (Jᶜ : Finset ι) := (Finset.mem_sdiff.mp hxV).1
    have hxA : x ∉ A := (Finset.mem_sdiff.mp hxV).2
    refine Finset.mem_sdiff.mpr ⟨Finset.mem_compl.mpr hxL, fun hxB => hxA ?_⟩
    have hxBS : x ∈ B ∩ (Jᶜ : Finset ι) := Finset.mem_inter.mpr ⟨hxB, hxS⟩
    rw [← hcompat] at hxBS
    exact (Finset.mem_inter.mp hxBS).1
  have hunionJ : V ∪ W = V ∪ (W ∩ J) := by
    ext x
    simp only [Finset.mem_union, Finset.mem_inter]
    constructor
    · rintro (hxV | hxW)
      · exact Or.inl hxV
      · by_cases hxJ : x ∈ J
        · exact Or.inr ⟨hxW, hxJ⟩
        · exact Or.inl (hWsubV x hxW hxJ)
    · rintro (hxV | ⟨hxW, -⟩)
      · exact Or.inl hxV
      · exact Or.inr hxW
  have hunionL : V ∪ W = W ∪ (V ∩ L) := by
    ext x
    simp only [Finset.mem_union, Finset.mem_inter]
    constructor
    · rintro (hxV | hxW)
      · by_cases hxL : x ∈ L
        · exact Or.inr ⟨hxV, hxL⟩
        · exact Or.inl (hVsubW x hxV hxL)
      · exact Or.inl hxW
    · rintro (hxW | ⟨hxV, -⟩)
      · exact Or.inr hxW
      · exact Or.inl hxV
  have hdisjJ : Disjoint V (W ∩ J) := by
    rw [Finset.disjoint_left]
    intro x hxV hxWJ
    exact Finset.disjoint_left.mp hVJ hxV (Finset.mem_inter.mp hxWJ).2
  have hdisjL : Disjoint W (V ∩ L) := by
    rw [Finset.disjoint_left]
    intro x hxW hxVL
    exact Finset.disjoint_left.mp hWL hxW (Finset.mem_inter.mp hxVL).2
  have hredJ := faceDifferenceCube_reduce ω hω hneJ hKne V (W ∩ J) hVJ hdisjJ hJV g
  have hredL := faceDifferenceCube_reduce ω hω hneL hMne W (V ∩ L) hWL hdisjL hLW h
  rw [← hunionJ] at hredJ
  rw [← hunionL] at hredL
  have hcube : faceDifferenceCube ω (V ∪ W) g
        (frameSourceMero ω hω (Jᶜ : Finset ι) hneJ)
      - faceDifferenceCube ω (V ∪ W) h (frameSourceMero ω hω (Lᶜ : Finset ι) hneL)
      ∈ meromorphicRationalCoordinateField := by
    have hmem := faceDifferenceCube_mem_rationalCoordinateField ω (V ∪ W) 0 hcon
    rwa [faceDifferenceCube_sub, faceDifferenceCube_zero_translate,
      faceDifferenceCube_zero_translate] at hmem
  have hfinal : (-1 : meroField (Set.univ : Set ℂ)) ^ V.card *
        faceDifferenceCube ω (W ∩ J) g (frameSourceMero ω hω (Kᶜ : Finset ι) hKne)
      - (-1 : meroField (Set.univ : Set ℂ)) ^ W.card *
        faceDifferenceCube ω (V ∩ L) h (frameSourceMero ω hω (Mᶜ : Finset ι) hMne)
      ∈ meromorphicRationalCoordinateField := by
    have hid : (-1 : meroField (Set.univ : Set ℂ)) ^ V.card *
          faceDifferenceCube ω (W ∩ J) g (frameSourceMero ω hω (Kᶜ : Finset ι) hKne)
        - (-1 : meroField (Set.univ : Set ℂ)) ^ W.card *
          faceDifferenceCube ω (V ∩ L) h (frameSourceMero ω hω (Mᶜ : Finset ι) hMne)
        = -(faceDifferenceCube ω (V ∪ W) g (frameSourceMero ω hω (Jᶜ : Finset ι) hneJ)
              - (-1 : meroField (Set.univ : Set ℂ)) ^ V.card *
                faceDifferenceCube ω (W ∩ J) g
                  (frameSourceMero ω hω (Kᶜ : Finset ι) hKne))
          + (faceDifferenceCube ω (V ∪ W) h (frameSourceMero ω hω (Lᶜ : Finset ι) hneL)
              - (-1 : meroField (Set.univ : Set ℂ)) ^ W.card *
                faceDifferenceCube ω (V ∩ L) h
                  (frameSourceMero ω hω (Mᶜ : Finset ι) hMne))
          + (faceDifferenceCube ω (V ∪ W) g
                (frameSourceMero ω hω (Jᶜ : Finset ι) hneJ)
              - faceDifferenceCube ω (V ∪ W) h
                (frameSourceMero ω hω (Lᶜ : Finset ι) hneL)) := by
      ring
    rw [hid]
    exact add_mem (add_mem (neg_mem hredJ) hredL) hcube
  refine bottom_cube_sub_cube_notMem_rational hrad hind hω hKcard hMcard hKM hKne hMne
    (W ∩ J) (V ∩ L) (fun x hx => hJK (Finset.mem_inter.mp hx).2)
    (fun x hx => hLM (Finset.mem_inter.mp hx).2)
    (faceShiftLattice_mono ω hJK hg) (faceShiftLattice_mono ω hLM hh) V.card W.card hfinal

/-! ### Separation of all distinct faces -/

set_option synthInstance.maxHeartbeats 1000000 in
/-- **Distinct faces are separated.**  Translates of the coordinates of two distinct faces, each
retaining at least two periods, never agree modulo the rational coordinate field. -/
theorem frameSource_translate_sub_notMem_rational {μ : ℂ} {rad : ι → ℝ} (hrad : ∀ k, 0 < rad k)
    (hind : LinearIndependent ℚ (fun k => μ * (rad k : ℂ)))
    (hω : ∀ k, 0 < (μ * (rad k : ℂ)).im)
    {J L : Finset ι} (hJL : J ≠ L)
    (hJ : 2 ≤ (Jᶜ : Finset ι).card) (hL : 2 ≤ (Lᶜ : Finset ι).card)
    (hneJ : (Jᶜ : Finset ι).Nonempty) (hneL : (Lᶜ : Finset ι).Nonempty)
    {g h : ℂ} (hg : g ∈ faceShiftLattice (fun k => μ * (rad k : ℂ)) J)
    (hh : h ∈ faceShiftLattice (fun k => μ * (rad k : ℂ)) L) :
    addTranslationMeroEquiv g
          (frameSourceMero (fun k => μ * (rad k : ℂ)) hω (Jᶜ : Finset ι) hneJ)
        - addTranslationMeroEquiv h
          (frameSourceMero (fun k => μ * (rad k : ℂ)) hω (Lᶜ : Finset ι) hneL)
      ∉ meromorphicRationalCoordinateField := by
  classical
  by_cases hsub : J ⊆ L
  · exact frameSource_translate_sub_notMem_rational_of_ssubset hrad hind hω hsub hJL hL
      hneJ hneL hg hh
  by_cases hsub' : L ⊆ J
  · intro hcon
    refine frameSource_translate_sub_notMem_rational_of_ssubset hrad hind hω hsub' hJL.symm hJ
      hneL hneJ hh hg ?_
    have hneg := neg_mem hcon
    have hid : -(addTranslationMeroEquiv g
          (frameSourceMero (fun k => μ * (rad k : ℂ)) hω (Jᶜ : Finset ι) hneJ)
        - addTranslationMeroEquiv h
          (frameSourceMero (fun k => μ * (rad k : ℂ)) hω (Lᶜ : Finset ι) hneL))
        = addTranslationMeroEquiv h
            (frameSourceMero (fun k => μ * (rad k : ℂ)) hω (Lᶜ : Finset ι) hneL)
          - addTranslationMeroEquiv g
            (frameSourceMero (fun k => μ * (rad k : ℂ)) hω (Jᶜ : Finset ι) hneJ) := by ring
    rwa [hid] at hneg
  · exact frameSource_translate_sub_notMem_rational_of_incomparable hrad hind hω hsub hsub'
      hJ hL hneJ hneL hg hh

set_option synthInstance.maxHeartbeats 1000000 in
/-- **Distinct face packets are disjoint.** -/
theorem facePacket_disjoint_of_two_le {μ : ℂ} {rad : ι → ℝ} (hrad : ∀ k, 0 < rad k)
    (hind : LinearIndependent ℚ (fun k => μ * (rad k : ℂ)))
    (hω : ∀ k, 0 < (μ * (rad k : ℂ)).im)
    {J L : Finset ι} (hJ : 2 ≤ (Jᶜ : Finset ι).card) (hL : 2 ≤ (Lᶜ : Finset ι).card)
    (hJL : J ≠ L) :
    Disjoint (facePacket (fun k => μ * (rad k : ℂ)) hω J)
      (facePacket (fun k => μ * (rad k : ℂ)) hω L) := by
  classical
  have hneJ : (Jᶜ : Finset ι).Nonempty := Finset.card_pos.mp (by omega)
  have hneL : (Lᶜ : Finset ι).Nonempty := Finset.card_pos.mp (by omega)
  rw [Set.disjoint_left]
  intro x hxJ hxL
  rw [facePacket_eq _ hω hneJ] at hxJ
  rw [facePacket_eq _ hω hneL] at hxL
  obtain ⟨α, hα⟩ := hxJ
  obtain ⟨β, hβ⟩ := hxL
  dsimp only at hα hβ
  refine frameSource_translate_sub_notMem_rational hrad hind hω hJL hJ hL hneJ hneL
    (faceShift_mem_faceShiftLattice _ J α) (faceShift_mem_faceShiftLattice _ L β) ?_
  rw [hα, hβ, sub_self]
  exact zero_mem _

end

end GaloisForLFunctions.HTGeometry
