import GaloisForLFunctions.HTGeometry.MultipleSineAllFaceIndependence

/-!
# The primitive equation of a face

Equation `(9)`: the translation defect of a face coordinate in a direction outside the face is the
coordinate of the next face down, up to a rational function.  For the canonical packets this reads

```text
(T_q - 1) T^a F_J + T^a F_{J ∪ {q}} ∈ ℂ(z),
```

so a face coordinate is a primitive, over the rational base, of the deeper face coordinate.  This
is the compatibility system the layer descent consumes: it turns a hypothetical dependence inside
a face packet into a coboundary equation over the deeper layer.
-/

open Filter Set Topology Complex
open scoped Differential

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

/-! ### The exact primitive equation -/

set_option synthInstance.maxHeartbeats 1000000 in
/-- **The primitive equation of a face.**  The translation defect of the coordinate of a face, in a
direction outside the face, is the coordinate of the next face down, up to a rational function. -/
theorem canonicalFace_translation_defect (ω : ι → ℂ) (hω : ∀ k, 0 < (ω k).im)
    {J : Finset ι} {q : ι} (hq : q ∉ J) (h2 : 2 ≤ (Jᶜ : Finset ι).card)
    (hne : (Jᶜ : Finset ι).Nonempty) (hne' : ((insert q J)ᶜ : Finset ι).Nonempty) :
    ∃ r : RatFunc ℂ,
      addTranslationMeroEquiv (ω q) (frameSourceMero ω hω (Jᶜ : Finset ι) hne)
          - frameSourceMero ω hω (Jᶜ : Finset ι) hne
          + frameSourceMero ω hω ((insert q J)ᶜ : Finset ι) hne'
        = ratMero r := by
  classical
  have hqJ : q ∈ (Jᶜ : Finset ι) := Finset.mem_compl.mpr hq
  have herase : ((insert q J)ᶜ : Finset ι) = (Jᶜ : Finset ι).erase q := Finset.compl_insert
  have hnesub : ((Jᶜ : Finset ι).erase q).Nonempty := by
    rw [← herase]
    exact hne'
  haveI : Nonempty {i : ι // i ∈ (Jᶜ : Finset ι)} := ⟨⟨q, hqJ⟩⟩
  haveI : Nonempty {i : ι // i ∈ (Jᶜ : Finset ι).erase q} :=
    ⟨⟨hnesub.choose, hnesub.choose_spec⟩⟩
  have hladder := multipleSine_ladder_defect_eq ω hω (Jᶜ : Finset ι) q hqJ h2
  refine ⟨subframeLadderRat ω (Jᶜ : Finset ι) q hqJ
      + (frameSignZ (Jᶜ : Finset ι) : RatFunc ℂ) *
        ratReflectBy (frameReflectionPoint ω ((Jᶜ : Finset ι).erase q))
          (subframeLadderRat ω (Jᶜ : Finset ι) q hqJ), ?_⟩
  rw [← hladder]
  have hsrc : frameSourceMero ω hω (Jᶜ : Finset ι) hne
      = multipleSineSourceMero ω hω (Jᶜ : Finset ι) := rfl
  have hsrc' : frameSourceMero ω hω ((insert q J)ᶜ : Finset ι) hne'
      = multipleSineSourceMero ω hω ((Jᶜ : Finset ι).erase q) := by
    rw [frameSourceMero_congr ω hω herase hne' hnesub]
    rfl
  rw [hsrc, hsrc']

/-! ### The primitive equation on packets -/

omit [Fintype ι] [DecidableEq ι] in
/-- The external shift computed from any extension of the exponent vector to all directions. -/
theorem faceShift_eq_sum (ω : ι → ℂ) (J : Finset ι) (α : {k // k ∈ J} → ℤ)
    (C : ι → ℤ) (hC : ∀ k : {k // k ∈ J}, C (k : ι) = α k) :
    faceShift ω J α = ∑ k ∈ J, (C k : ℂ) * ω k := by
  rw [faceShift, ← Finset.sum_attach J (fun k => (C k : ℂ) * ω k)]
  exact Finset.sum_congr rfl (fun k _ => by rw [hC k])

omit [Fintype ι] in
/-- Extending an exponent vector by zero on one more direction does not change the shift. -/
theorem faceShift_extend (ω : ι → ℂ) {J : Finset ι} {q : ι} (hq : q ∉ J)
    (α : {k // k ∈ J} → ℤ) :
    faceShift ω (insert q J)
        (fun k : {k // k ∈ insert q J} =>
          if h : (k : ι) ∈ J then α ⟨(k : ι), h⟩ else 0)
      = faceShift ω J α := by
  classical
  set A : ι → ℤ := fun k => if h : k ∈ J then α ⟨k, h⟩ else 0 with hA
  have hAJ : ∀ k : {k // k ∈ J}, A (k : ι) = α k := by
    intro k
    rw [hA]
    simp only [dif_pos k.2]
  have hAq : A q = 0 := by
    rw [hA]
    simp [hq]
  have hleft : faceShift ω (insert q J)
      (fun k : {k // k ∈ insert q J} => if h : (k : ι) ∈ J then α ⟨(k : ι), h⟩ else 0)
      = ∑ k ∈ insert q J, (A k : ℂ) * ω k := by
    refine faceShift_eq_sum ω (insert q J) _ A ?_
    intro k
    rfl
  have hright : faceShift ω J α = ∑ k ∈ J, (A k : ℂ) * ω k :=
    faceShift_eq_sum ω J α A hAJ
  rw [hleft, hright, Finset.sum_insert hq, hAq]
  simp

/-- The deeper face coordinate, translated by an external shift of the shallower face, is a member
of the deeper face packet. -/
theorem translate_deeper_mem_facePacket (ω : ι → ℂ) (hω : ∀ k, 0 < (ω k).im)
    {J : Finset ι} {q : ι} (hq : q ∉ J) (hne' : ((insert q J)ᶜ : Finset ι).Nonempty)
    (α : {k // k ∈ J} → ℤ) :
    addTranslationMeroEquiv (faceShift ω J α)
        (frameSourceMero ω hω ((insert q J)ᶜ : Finset ι) hne')
      ∈ facePacket ω hω (insert q J) := by
  classical
  rw [facePacket_eq ω hω hne']
  refine ⟨fun k : {k // k ∈ insert q J} =>
    if h : (k : ι) ∈ J then α ⟨(k : ι), h⟩ else 0, ?_⟩
  exact congrArg (fun t => addTranslationMeroEquiv t
    (frameSourceMero ω hω ((insert q J)ᶜ : Finset ι) hne')) (faceShift_extend ω hq α)

set_option synthInstance.maxHeartbeats 1000000 in
/-- **The primitive equation on packets.**  Every external translate of a face coordinate is a
primitive, over the rational coordinate field, of the corresponding translate of the deeper face
coordinate. -/
theorem facePacket_primitive_equation (ω : ι → ℂ) (hω : ∀ k, 0 < (ω k).im)
    {J : Finset ι} {q : ι} (hq : q ∉ J) (h2 : 2 ≤ (Jᶜ : Finset ι).card)
    (hne : (Jᶜ : Finset ι).Nonempty) (hne' : ((insert q J)ᶜ : Finset ι).Nonempty)
    (α : {k // k ∈ J} → ℤ) :
    addTranslationMeroEquiv (ω q)
          (addTranslationMeroEquiv (faceShift ω J α)
            (frameSourceMero ω hω (Jᶜ : Finset ι) hne))
        - addTranslationMeroEquiv (faceShift ω J α)
            (frameSourceMero ω hω (Jᶜ : Finset ι) hne)
        + addTranslationMeroEquiv (faceShift ω J α)
            (frameSourceMero ω hω ((insert q J)ᶜ : Finset ι) hne')
      ∈ meromorphicRationalCoordinateField := by
  classical
  obtain ⟨r, hr⟩ := canonicalFace_translation_defect ω hω hq h2 hne hne'
  set s : ℂ := faceShift ω J α with hs
  have htrans := congrArg (addTranslationMeroEquiv s) hr
  rw [(addTranslationMeroEquiv s).map_add, (addTranslationMeroEquiv s).map_sub,
    addTranslationMeroEquiv_add] at htrans
  have hcomm : addTranslationMeroEquiv (s + ω q)
        (frameSourceMero ω hω (Jᶜ : Finset ι) hne)
      = addTranslationMeroEquiv (ω q)
        (addTranslationMeroEquiv s (frameSourceMero ω hω (Jᶜ : Finset ι) hne)) := by
    rw [addTranslationMeroEquiv_add]
    have harg : ω q + s = s + ω q := by ring
    rw [harg]
  rw [hcomm] at htrans
  rw [htrans, addTranslationMeroEquiv_ratfuncToMero_by]
  exact (mem_meromorphicRationalCoordinateField_iff _).mpr ⟨ratShiftBy s r, rfl⟩

end

end GaloisForLFunctions.HTGeometry
