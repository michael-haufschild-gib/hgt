import GaloisForLFunctions.HTGeometry.MultipleSineFacePalette
import GaloisForLFunctions.HTGeometry.FaceDepthRigidity

/-!
# The external lattice of a multiple-sine face, and its difference cubes

The external shifts of a face form the integer span of the periods it deletes.  Writing that span
as the range of the exponent parametrization identifies the packet of a face with a lattice orbit,
and the alternating difference cube along a set of surviving directions collapses the face
coordinate to a deeper one:

```text
∏_{q ∈ U} (T_{ω_q} - 1) T_g F_J = (-1)^{|U|} T_g F_{J ∪ U}   modulo ℂ(z).
```

A ray period family with rationally independent radii is integrally independent together with `1`,
so the whole external-lattice calculus of the face hierarchy applies to it.
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

/-! ### The external lattice is the range of the exponent parametrization -/

theorem faceShift_mem_faceShiftLattice (ω : ι → ℂ) (J : Finset ι) (α : {k // k ∈ J} → ℤ) :
    faceShift ω J α ∈ faceShiftLattice ω J := by
  classical
  set n : ι → ℤ := fun k => if h : k ∈ J then α ⟨k, h⟩ else 0 with hn
  refine ⟨n, fun k hk => by simp [hn, hk], ?_⟩
  have h1 : ∑ k : ι, (n k : ℂ) * ω k = ∑ k ∈ J, (n k : ℂ) * ω k := by
    refine (Finset.sum_subset (Finset.subset_univ J) ?_).symm
    intro k _ hkJ
    simp [hn, hkJ]
  rw [h1, ← Finset.sum_attach J (fun k => (n k : ℂ) * ω k), faceShift]
  exact Finset.sum_congr rfl fun k _ => by simp [hn]

omit [DecidableEq ι] in
theorem exists_faceShift_of_mem_faceShiftLattice (ω : ι → ℂ) {J : Finset ι} {g : ℂ}
    (hg : g ∈ faceShiftLattice ω J) : ∃ α : {k // k ∈ J} → ℤ, faceShift ω J α = g := by
  classical
  obtain ⟨n, hn, rfl⟩ := hg
  refine ⟨fun k => n (k : ι), ?_⟩
  have h1 : ∑ k : ι, (n k : ℂ) * ω k = ∑ k ∈ J, (n k : ℂ) * ω k := by
    refine (Finset.sum_subset (Finset.subset_univ J) ?_).symm
    intro k _ hkJ
    rw [hn k hkJ]
    simp
  rw [h1, ← Finset.sum_attach J (fun k => (n k : ℂ) * ω k), faceShift]

theorem mem_faceShiftLattice_iff (ω : ι → ℂ) (J : Finset ι) (g : ℂ) :
    g ∈ faceShiftLattice ω J ↔ ∃ α : {k // k ∈ J} → ℤ, faceShift ω J α = g :=
  ⟨exists_faceShift_of_mem_faceShiftLattice ω,
    fun ⟨α, hα⟩ => hα ▸ faceShift_mem_faceShiftLattice ω J α⟩

/-! ### A ray family is integrally independent together with `1` -/

omit [DecidableEq ι] in
/-- **Ray families are integrally independent.**  Periods on a common ray with rationally
independent radii admit no integral relation with `1`: a relation would make the direction real. -/
theorem periodsIntegrallyIndependent_ray {μ : ℂ} {rad : ι → ℝ} (_hrad : ∀ k, 0 < rad k)
    (hind : LinearIndependent ℚ (fun k => μ * (rad k : ℂ)))
    (hω : ∀ k, 0 < (μ * (rad k : ℂ)).im) :
    PeriodsIntegrallyIndependent (fun k => μ * (rad k : ℂ)) := by
  classical
  intro m n hrel
  have hsum : ∑ k : ι, (n k : ℂ) * (μ * (rad k : ℂ))
      = μ * ((∑ k : ι, (n k : ℝ) * rad k : ℝ) : ℂ) := by
    push_cast
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [hsum] at hrel
  have hczero : (∑ k : ι, (n k : ℝ) * rad k) = 0 := by
    by_contra hcne
    have hmul : μ * ((∑ k : ι, (n k : ℝ) * rad k : ℝ) : ℂ) = -(m : ℂ) := by
      linear_combination hrel
    have him0 : μ.im * (∑ k : ι, (n k : ℝ) * rad k) = 0 := by
      have hcong := congrArg Complex.im hmul
      simpa using hcong
    have him : μ.im = 0 := by
      rcases mul_eq_zero.mp him0 with h | h
      · exact h
      · exact absurd h hcne
    have hne : Nonempty ι := by
      by_contra hcon
      rw [not_nonempty_iff] at hcon
      exact hcne (by simp)
    obtain ⟨k₀⟩ := hne
    have hpos := hω k₀
    have hzeroim : (μ * (rad k₀ : ℂ)).im = 0 := by
      simp [Complex.mul_im, him]
    rw [hzeroim] at hpos
    exact lt_irrefl 0 hpos
  have hm : (m : ℂ) = 0 := by
    rw [hczero] at hrel
    simpa using hrel
  have hmz : m = 0 := by
    exact_mod_cast hm
  refine ⟨hmz, ?_⟩
  have hzero : ∑ k : ι, ((n k : ℚ)) • (μ * (rad k : ℂ)) = 0 := by
    have hexp : ∀ k : ι, ((n k : ℚ)) • (μ * (rad k : ℂ)) = (n k : ℂ) * (μ * (rad k : ℂ)) := by
      intro k
      rw [Rat.smul_def]
      push_cast
      ring
    rw [Finset.sum_congr rfl (fun k _ => hexp k), hsum, hczero]
    simp
  intro i
  have hall := Fintype.linearIndependent_iff.mp hind _ hzero i
  exact_mod_cast hall

/-! ### The primitive equation at an arbitrary external shift -/

set_option synthInstance.maxHeartbeats 1000000 in
/-- **The primitive equation at an arbitrary shift.**  The translation defect of a translate of a
face coordinate, in a direction outside the face, is the same translate of the deeper face
coordinate, up to a rational function. -/
theorem frameSource_translation_defect_mem (ω : ι → ℂ) (hω : ∀ k, 0 < (ω k).im)
    {J : Finset ι} {q : ι} (hq : q ∉ J) (h2 : 2 ≤ (Jᶜ : Finset ι).card)
    (hne : (Jᶜ : Finset ι).Nonempty) (hne' : ((insert q J)ᶜ : Finset ι).Nonempty) (g : ℂ) :
    addTranslationMeroEquiv (ω q)
          (addTranslationMeroEquiv g (frameSourceMero ω hω (Jᶜ : Finset ι) hne))
        - addTranslationMeroEquiv g (frameSourceMero ω hω (Jᶜ : Finset ι) hne)
        + addTranslationMeroEquiv g (frameSourceMero ω hω ((insert q J)ᶜ : Finset ι) hne')
      ∈ meromorphicRationalCoordinateField := by
  classical
  obtain ⟨r, hr⟩ := canonicalFace_translation_defect ω hω hq h2 hne hne'
  have htrans := congrArg (addTranslationMeroEquiv g) hr
  rw [(addTranslationMeroEquiv g).map_add, (addTranslationMeroEquiv g).map_sub,
    addTranslationMeroEquiv_add] at htrans
  have hcomm : addTranslationMeroEquiv (g + ω q)
        (frameSourceMero ω hω (Jᶜ : Finset ι) hne)
      = addTranslationMeroEquiv (ω q)
        (addTranslationMeroEquiv g (frameSourceMero ω hω (Jᶜ : Finset ι) hne)) := by
    rw [addTranslationMeroEquiv_add]
    have harg : ω q + g = g + ω q := by ring
    rw [harg]
  rw [hcomm] at htrans
  rw [htrans, addTranslationMeroEquiv_ratfuncToMero_by]
  exact (mem_meromorphicRationalCoordinateField_iff _).mpr ⟨ratShiftBy g r, rfl⟩

/-! ### The difference cube collapses a face coordinate to a deeper one -/

set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 1000000 in
/-- **The difference cube of a face coordinate.**  Differencing along a set of surviving directions
collapses a translate of a face coordinate to the same translate of the deeper face coordinate, with
the parity sign, modulo the rational coordinate field. -/
theorem faceDifferenceCube_frameSource (ω : ι → ℂ) (hω : ∀ k, 0 < (ω k).im)
    (J : Finset ι) (hJne : (Jᶜ : Finset ι).Nonempty) (g : ℂ) :
    ∀ U : Finset ι, Disjoint U J → ∀ hne : ((J ∪ U)ᶜ : Finset ι).Nonempty,
      faceDifferenceCube ω U g (frameSourceMero ω hω (Jᶜ : Finset ι) hJne)
          - (-1 : meroField (Set.univ : Set ℂ)) ^ U.card *
            addTranslationMeroEquiv g (frameSourceMero ω hω ((J ∪ U)ᶜ : Finset ι) hne)
        ∈ meromorphicRationalCoordinateField := by
  classical
  intro U
  induction U using Finset.induction_on with
  | empty =>
      intro _ hne
      rw [faceDifferenceCube_empty, Finset.card_empty, pow_zero, one_mul,
        frameSourceMero_congr ω hω (by simp : (J ∪ (∅ : Finset ι))ᶜ = (Jᶜ : Finset ι)) hne hJne,
        sub_self]
      exact zero_mem _
  | @insert q U hqU ih =>
      intro hdisj hne
      have hqJ : q ∉ J := Finset.disjoint_left.mp hdisj (Finset.mem_insert_self q U)
      have hUJ : Disjoint U J := hdisj.mono (Finset.subset_insert q U) (fun _ h => h)
      have hqJU : q ∉ J ∪ U := by
        intro hcon
        rcases Finset.mem_union.mp hcon with h | h
        · exact hqJ h
        · exact hqU h
      have hins : J ∪ insert q U = insert q (J ∪ U) := by
        ext x
        simp only [Finset.mem_union, Finset.mem_insert]
        tauto
      have hqmem : q ∈ ((J ∪ U)ᶜ : Finset ι) := Finset.mem_compl.mpr hqJU
      have hnecompl : ((insert q (J ∪ U))ᶜ : Finset ι).Nonempty := by
        rw [← hins]; exact hne
      have hneU : ((J ∪ U)ᶜ : Finset ι).Nonempty := ⟨q, hqmem⟩
      have h2 : 2 ≤ ((J ∪ U)ᶜ : Finset ι).card := by
        obtain ⟨p, hp⟩ := hnecompl
        rw [Finset.compl_insert] at hp
        have hpq : p ≠ q := (Finset.mem_erase.mp hp).1
        have hpc : p ∈ ((J ∪ U)ᶜ : Finset ι) := Finset.mem_erase.mp hp |>.2
        have hsub : ({p, q} : Finset ι) ⊆ ((J ∪ U)ᶜ : Finset ι) := by
          intro x hx
          rcases Finset.mem_insert.mp hx with rfl | hx
          · exact hpc
          · rw [Finset.mem_singleton.mp hx]; exact hqmem
        have := Finset.card_le_card hsub
        rwa [Finset.card_pair hpq] at this
      have hIH := ih hUJ hneU
      set F : meroField (Set.univ : Set ℂ) := frameSourceMero ω hω (Jᶜ : Finset ι) hJne with hF
      set A : meroField (Set.univ : Set ℂ) := faceDifferenceCube ω U g F with hA
      set B : meroField (Set.univ : Set ℂ) :=
        addTranslationMeroEquiv g (frameSourceMero ω hω ((J ∪ U)ᶜ : Finset ι) hneU) with hB
      set C : meroField (Set.univ : Set ℂ) :=
        addTranslationMeroEquiv g
          (frameSourceMero ω hω ((insert q (J ∪ U))ᶜ : Finset ι) hnecompl) with hC
      have hstep := frameSource_translation_defect_mem ω hω hqJU h2 hneU hnecompl g
      rw [← hB, ← hC] at hstep
      have hcube : faceDifferenceCube ω (insert q U) g F
          = addTranslationMeroEquiv (ω q) A - A :=
        faceDifferenceCube_insert ω U hqU g F
      have hsrc : frameSourceMero ω hω ((J ∪ insert q U)ᶜ : Finset ι) hne
          = frameSourceMero ω hω ((insert q (J ∪ U))ᶜ : Finset ι) hnecompl :=
        frameSourceMero_congr ω hω (by rw [hins]) hne hnecompl
      rw [hcube, hsrc, Finset.card_insert_of_notMem hqU, ← hC, pow_succ]
      have hsign : (-1 : meroField (Set.univ : Set ℂ)) ^ U.card * (-1) * C
          = -((-1 : meroField (Set.univ : Set ℂ)) ^ U.card * C) := by ring
      rw [hsign]
      have hid : addTranslationMeroEquiv (ω q) A - A
            + (-1 : meroField (Set.univ : Set ℂ)) ^ U.card * C
          = (addTranslationMeroEquiv (ω q)
                (A - (-1 : meroField (Set.univ : Set ℂ)) ^ U.card * B)
              - (A - (-1 : meroField (Set.univ : Set ℂ)) ^ U.card * B))
            + (-1 : meroField (Set.univ : Set ℂ)) ^ U.card *
                (addTranslationMeroEquiv (ω q) B - B + C) := by
        rw [map_sub, map_mul, map_pow, map_neg, map_one]
        ring
      rw [sub_neg_eq_add, hid]
      refine add_mem (sub_mem ?_ hIH) ?_
      · exact addTranslationMeroAlgEquiv_mem_rationalCoordinateField (ω q) hIH
      · exact mul_mem (pow_mem (neg_mem (one_mem meromorphicRationalCoordinateField)) _) hstep

end

end GaloisForLFunctions.HTGeometry
