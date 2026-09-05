import GaloisForLFunctions.HTGeometry.MultipleSineFaceLatticeCube

/-!
# Faithful labelling of every multiple-sine face packet

Distinct external shifts give translates of a face coordinate that differ by more than a rational
function — for every face retaining at least two periods, not only for the maximal ones.  Adding a
surviving direction to the face turns a coincidence modulo `ℂ(z)` into a coincidence one layer
deeper, because the primitive equation is exact modulo `ℂ(z)`, so the statement descends to a face
with exactly two surviving periods, where it is the freeness of the canonical double-sine orbit
over the rational coordinate field.

* **`frameSource_translate_injective_mod_rational`** — faithful labelling modulo `ℂ(z)`;
* **`facePacket_label_injective`** — hence the exponent parametrization of a packet is faithful;
* **`facePalette_injective_of_two_le`** — and so is the bilateral palette of any face.
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

/-! ### Membership in the rational coordinate field is differential algebraicity over it -/

theorem differentialAlgebraicOver_of_mem_rationalCoordinateField
    {x : meroField (Set.univ : Set ℂ)} (hx : x ∈ meromorphicRationalCoordinateField) :
    DifferentialAlgebraicOver ↥meromorphicRationalCoordinateField x := by
  have h := differentialAlgebraicOver_algebraMap
    (F := ↥meromorphicRationalCoordinateField) (E := meroField (Set.univ : Set ℂ)) ⟨x, hx⟩
  simpa using h

/-! ### The exponent parametrization of the external shift is faithful -/

theorem faceShift_injective_of_two_survivors {ω : ι → ℂ} (hind : LinearIndependent ℚ ω)
    {J : Finset ι} {i j : ι} (hij : i ≠ j) (hi : i ∉ J) (hj : j ∉ J) :
    Function.Injective (faceShift ω J) := by
  intro α β hαβ
  by_contra hne
  refine faceShift_separated hind hij hi hj hne 0 0 ?_
  rw [hαβ]
  simp

/-- The membership witness of a packet slice. -/
theorem exists_exponent_of_mem_facePacketSlice (ω : ι → ℂ) (hω : ∀ k, 0 < (ω k).im)
    {J : Finset ι} {q : ι} (hne : (Jᶜ : Finset ι).Nonempty)
    {x : meroField (Set.univ : Set ℂ)} (hx : x ∈ facePacketSlice ω hω J q) :
    ∃ α : {k // k ∈ J} → ℤ, (∀ k : {k // k ∈ J}, (k : ι) = q → α k = 0) ∧
      x = addTranslationMeroEquiv (faceShift ω J α)
        (frameSourceMero ω hω (Jᶜ : Finset ι) hne) := by
  rw [facePacketSlice_eq ω hω q hne] at hx
  exact hx

/-! ### Faithful labelling modulo the rational coordinate field -/

set_option synthInstance.maxHeartbeats 1000000 in
/-- Faithful labelling for a face whose complement has a prescribed size, by induction on the
number of surviving periods beyond the second. -/
theorem frameSource_translate_injective_mod_rational_aux {μ : ℂ} {rad : ι → ℝ}
    (hrad : ∀ k, 0 < rad k)
    (hind : LinearIndependent ℚ (fun k => μ * (rad k : ℂ)))
    (hω : ∀ k, 0 < (μ * (rad k : ℂ)).im) :
    ∀ (k : ℕ) (J : Finset ι), (Jᶜ : Finset ι).card = k + 2 →
      ∀ (hne : (Jᶜ : Finset ι).Nonempty) (g g' : ℂ),
        g ∈ faceShiftLattice (fun k => μ * (rad k : ℂ)) J →
        g' ∈ faceShiftLattice (fun k => μ * (rad k : ℂ)) J →
        addTranslationMeroEquiv g
              (frameSourceMero (fun k => μ * (rad k : ℂ)) hω (Jᶜ : Finset ι) hne)
            - addTranslationMeroEquiv g'
              (frameSourceMero (fun k => μ * (rad k : ℂ)) hω (Jᶜ : Finset ι) hne)
          ∈ meromorphicRationalCoordinateField → g = g' := by
  classical
  set ω : ι → ℂ := fun k => μ * (rad k : ℂ) with hωdef
  intro k
  induction k with
  | zero =>
      intro J hcard hne g g' hg hg' hmem
      obtain ⟨i, j, hij, hpair⟩ := Finset.card_eq_two.mp hcard
      have hi : i ∉ J := Finset.mem_compl.mp (by rw [hpair]; simp)
      have hj : j ∉ J := Finset.mem_compl.mp (by rw [hpair]; simp)
      have hS : ({i, j} : Finset ι).Nonempty := ⟨i, by simp⟩
      have hsrc : frameSourceMero ω hω (Jᶜ : Finset ι) hne
          = frameSourceMero ω hω ({i, j} : Finset ι) hS :=
        frameSourceMero_congr _ hω hpair hne hS
      obtain ⟨α, rfl⟩ := exists_faceShift_of_mem_faceShiftLattice ω hg
      obtain ⟨β, rfl⟩ := exists_faceShift_of_mem_faceShiftLattice ω hg'
      by_contra hne'
      have hαβ : α ≠ β := fun hcon => hne' (by rw [hcon])
      have hfam := multipleSineCanonicalFaceOrbit_free hrad hind hω hij hi hj hS
      refine hfam.sub_not_differentialAlgebraic hαβ ?_
      rw [hsrc] at hmem
      exact differentialAlgebraicOver_of_mem_rationalCoordinateField hmem
  | succ k ih =>
      intro J hcard hne g g' hg hg' hmem
      have h2 : 2 ≤ (Jᶜ : Finset ι).card := by omega
      obtain ⟨q, hqc⟩ := id hne
      have hq : q ∉ J := Finset.mem_compl.mp hqc
      have hcard' : ((insert q J)ᶜ : Finset ι).card = k + 2 := by
        rw [Finset.compl_insert, Finset.card_erase_of_mem hqc, hcard]
        omega
      have hne' : ((insert q J)ᶜ : Finset ι).Nonempty :=
        Finset.card_pos.mp (by rw [hcard']; omega)
      have hdg := frameSource_translation_defect_mem ω hω hq h2 hne hne' g
      have hdg' := frameSource_translation_defect_mem ω hω hq h2 hne hne' g'
      have htrans := addTranslationMeroAlgEquiv_mem_rationalCoordinateField (ω q) hmem
      set F : meroField (Set.univ : Set ℂ) :=
        frameSourceMero ω hω (Jᶜ : Finset ι) hne with hF
      set G : meroField (Set.univ : Set ℂ) :=
        frameSourceMero ω hω ((insert q J)ᶜ : Finset ι) hne' with hG
      have hstep : addTranslationMeroEquiv g G - addTranslationMeroEquiv g' G
          ∈ meromorphicRationalCoordinateField := by
        have hid : addTranslationMeroEquiv g G - addTranslationMeroEquiv g' G
            = ((addTranslationMeroEquiv (ω q) (addTranslationMeroEquiv g F)
                  - addTranslationMeroEquiv g F + addTranslationMeroEquiv g G)
                - (addTranslationMeroEquiv (ω q) (addTranslationMeroEquiv g' F)
                  - addTranslationMeroEquiv g' F + addTranslationMeroEquiv g' G))
              - addTranslationMeroEquiv (ω q)
                  (addTranslationMeroEquiv g F - addTranslationMeroEquiv g' F)
              + (addTranslationMeroEquiv g F - addTranslationMeroEquiv g' F) := by
          rw [map_sub]
          ring
        rw [hid]
        exact add_mem (sub_mem (sub_mem hdg hdg') htrans) hmem
      exact ih (insert q J) hcard' hne' g g'
        (faceShiftLattice_mono ω (Finset.subset_insert q J) hg)
        (faceShiftLattice_mono ω (Finset.subset_insert q J) hg') hstep

set_option synthInstance.maxHeartbeats 1000000 in
/-- **Faithful labelling of a face packet modulo the rational base.**  For a face retaining at least
two periods, external shifts whose translates of the face coordinate agree modulo `ℂ(z)` are
equal. -/
theorem frameSource_translate_injective_mod_rational {μ : ℂ} {rad : ι → ℝ}
    (hrad : ∀ k, 0 < rad k)
    (hind : LinearIndependent ℚ (fun k => μ * (rad k : ℂ)))
    (hω : ∀ k, 0 < (μ * (rad k : ℂ)).im)
    {J : Finset ι} (hJ : 2 ≤ (Jᶜ : Finset ι).card) (hne : (Jᶜ : Finset ι).Nonempty)
    {g g' : ℂ} (hg : g ∈ faceShiftLattice (fun k => μ * (rad k : ℂ)) J)
    (hg' : g' ∈ faceShiftLattice (fun k => μ * (rad k : ℂ)) J)
    (hmem : addTranslationMeroEquiv g
          (frameSourceMero (fun k => μ * (rad k : ℂ)) hω (Jᶜ : Finset ι) hne)
        - addTranslationMeroEquiv g'
          (frameSourceMero (fun k => μ * (rad k : ℂ)) hω (Jᶜ : Finset ι) hne)
      ∈ meromorphicRationalCoordinateField) :
    g = g' := by
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hJ
  exact frameSource_translate_injective_mod_rational_aux hrad hind hω k J (by omega) hne g g'
    hg hg' hmem

set_option synthInstance.maxHeartbeats 1000000 in
/-- **Faithful labelling of a face packet.**  Distinct external shifts give distinct translates of
the face coordinate. -/
theorem frameSource_translate_injective {μ : ℂ} {rad : ι → ℝ} (hrad : ∀ k, 0 < rad k)
    (hind : LinearIndependent ℚ (fun k => μ * (rad k : ℂ)))
    (hω : ∀ k, 0 < (μ * (rad k : ℂ)).im)
    {J : Finset ι} (hJ : 2 ≤ (Jᶜ : Finset ι).card) (hne : (Jᶜ : Finset ι).Nonempty)
    {g g' : ℂ} (hg : g ∈ faceShiftLattice (fun k => μ * (rad k : ℂ)) J)
    (hg' : g' ∈ faceShiftLattice (fun k => μ * (rad k : ℂ)) J)
    (heq : addTranslationMeroEquiv g
          (frameSourceMero (fun k => μ * (rad k : ℂ)) hω (Jᶜ : Finset ι) hne)
        = addTranslationMeroEquiv g'
          (frameSourceMero (fun k => μ * (rad k : ℂ)) hω (Jᶜ : Finset ι) hne)) :
    g = g' := by
  refine frameSource_translate_injective_mod_rational hrad hind hω hJ hne hg hg' ?_
  rw [heq, sub_self]
  exact zero_mem _

/-! ### Faithful parametrizations of a packet -/

set_option synthInstance.maxHeartbeats 1000000 in
/-- **The exponent parametrization of a face packet is faithful.** -/
theorem facePacket_label_injective {μ : ℂ} {rad : ι → ℝ} (hrad : ∀ k, 0 < rad k)
    (hind : LinearIndependent ℚ (fun k => μ * (rad k : ℂ)))
    (hω : ∀ k, 0 < (μ * (rad k : ℂ)).im)
    {J : Finset ι} (hJ : 2 ≤ (Jᶜ : Finset ι).card) (hne : (Jᶜ : Finset ι).Nonempty) :
    Function.Injective (fun α : {k // k ∈ J} → ℤ =>
      addTranslationMeroEquiv (faceShift (fun k => μ * (rad k : ℂ)) J α)
        (frameSourceMero (fun k => μ * (rad k : ℂ)) hω (Jᶜ : Finset ι) hne)) := by
  classical
  set ω : ι → ℂ := fun k => μ * (rad k : ℂ) with hωdef
  obtain ⟨P, hPsub, hPcard⟩ := Finset.exists_subset_card_eq hJ
  obtain ⟨i, j, hij, hP⟩ := Finset.card_eq_two.mp hPcard
  have hi : i ∉ J := Finset.mem_compl.mp (hPsub (by rw [hP]; simp))
  have hj : j ∉ J := Finset.mem_compl.mp (hPsub (by rw [hP]; simp))
  intro α β hαβ
  have hshift := frameSource_translate_injective hrad hind hω hJ hne
    (faceShift_mem_faceShiftLattice ω J α) (faceShift_mem_faceShiftLattice ω J β) hαβ
  exact faceShift_injective_of_two_survivors hind hij hi hj hshift

set_option synthInstance.maxHeartbeats 1000000 in
/-- **The bilateral palette of any face is faithful.**  Distinct slice points or distinct exponents
give distinct elements of the packet. -/
theorem facePalette_injective_of_two_le {μ : ℂ} {rad : ι → ℝ} (hrad : ∀ k, 0 < rad k)
    (hind : LinearIndependent ℚ (fun k => μ * (rad k : ℂ)))
    (hω : ∀ k, 0 < (μ * (rad k : ℂ)).im)
    {J : Finset ι} (hJ : 2 ≤ (Jᶜ : Finset ι).card) {q : ι} (hq : q ∈ J) :
    Function.Injective (facePalette (fun k => μ * (rad k : ℂ)) hω J q) := by
  classical
  set ω : ι → ℂ := fun k => μ * (rad k : ℂ) with hωdef
  have hne : (Jᶜ : Finset ι).Nonempty := Finset.card_pos.mp (by omega)
  rintro ⟨y, m⟩ ⟨z, n⟩ hyz
  rw [facePalette_apply, facePalette_apply] at hyz
  obtain ⟨α, hα, hyval⟩ := exists_exponent_of_mem_facePacketSlice ω hω hne y.2
  obtain ⟨β, hβ, hzval⟩ := exists_exponent_of_mem_facePacketSlice ω hω hne z.2
  have hshifteq : ∀ (γ : {k // k ∈ J} → ℤ) (t : ℤ),
      (∀ k : {k // k ∈ J}, (k : ι) = q → γ k = 0) →
      addTranslationMeroEquiv (faceShift ω J (fun k => if (k : ι) = q then t else γ k))
          (frameSourceMero ω hω (Jᶜ : Finset ι) hne)
        = addTranslationMeroEquiv ((t : ℂ) * ω q)
            (addTranslationMeroEquiv (faceShift ω J γ)
              (frameSourceMero ω hω (Jᶜ : Finset ι) hne)) := by
    intro γ t hγ
    have harg : faceShift ω J γ + (t : ℂ) * ω q = (t : ℂ) * ω q + faceShift ω J γ := by ring
    rw [faceShift_update ω hq hγ t, addTranslationMeroEquiv_add, harg]
  have hval : addTranslationMeroEquiv (faceShift ω J (fun k => if (k : ι) = q then m else α k))
        (frameSourceMero ω hω (Jᶜ : Finset ι) hne)
      = addTranslationMeroEquiv (faceShift ω J (fun k => if (k : ι) = q then n else β k))
        (frameSourceMero ω hω (Jᶜ : Finset ι) hne) := by
    rw [hshifteq α m hα, hshifteq β n hβ, ← hyval, ← hzval]
    exact hyz
  have hexp := facePacket_label_injective hrad hind hω hJ hne hval
  have hmn : m = n := by
    have hcong := congrFun hexp ⟨q, hq⟩
    simpa using hcong
  subst hmn
  have hyzval : (y : meroField (Set.univ : Set ℂ)) = (z : meroField (Set.univ : Set ℂ)) :=
    (addTranslationMeroEquiv ((m : ℂ) * ω q)).injective hyz
  exact Prod.ext (Subtype.ext hyzval) rfl

end

end GaloisForLFunctions.HTGeometry
