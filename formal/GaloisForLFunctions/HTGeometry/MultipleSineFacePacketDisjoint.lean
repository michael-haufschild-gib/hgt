import GaloisForLFunctions.HTGeometry.MultipleSineFacePacket

/-!
# Distinct maximal faces carry disjoint packets

The two interfaces of the face-gluing engine already separate the directions of a face from those
of its complement: inside the face a direction is free, outside it a direction is differentially
neutral.  That contrast alone forces the packets of two distinct maximal faces to be disjoint.

If a function belonged to both packets, pick a direction in the complement of the first face that
lies inside the second — two distinct pairs always admit one.  Translating by it moves the function
by a differentially algebraic amount, because the direction is off the first face, and by a
non-algebraic amount, because it is a free direction of the second.  So no such function exists.
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

/-! ### One step in a free direction -/

omit [Fintype ι] [DecidableEq ι] in
theorem faceShift_add (ω : ι → ℂ) (J : Finset ι) (α β : {k // k ∈ J} → ℤ) :
    faceShift ω J (α + β) = faceShift ω J α + faceShift ω J β := by
  rw [faceShift, faceShift, faceShift, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro k _
  show ((α k + β k : ℤ) : ℂ) * ω k = (α k : ℂ) * ω k + (β k : ℂ) * ω k
  push_cast
  ring

omit [Fintype ι] in
/-- The external shift of a single unit vector on the face is the corresponding period. -/
theorem faceShift_single (ω : ι → ℂ) (J : Finset ι) {p : ι} (hp : p ∈ J) :
    faceShift ω J (fun k => if k = (⟨p, hp⟩ : {k // k ∈ J}) then 1 else 0) = ω p := by
  classical
  rw [faceShift]
  have hrw : ∀ k ∈ J.attach,
      (((if k = (⟨p, hp⟩ : {k // k ∈ J}) then 1 else 0 : ℤ)) : ℂ) * ω k
        = if k = (⟨p, hp⟩ : {k // k ∈ J}) then ω p else 0 := by
    intro k _
    by_cases hk : k = (⟨p, hp⟩ : {k // k ∈ J})
    · rw [if_pos hk, if_pos hk, hk]
      push_cast
      ring
    · rw [if_neg hk, if_neg hk]
      push_cast
      ring
  rw [Finset.sum_congr rfl hrw, Finset.sum_ite_eq' J.attach (⟨p, hp⟩ : {k // k ∈ J})
    (fun _ => ω p), if_pos (Finset.mem_attach J _)]

set_option synthInstance.maxHeartbeats 1000000 in
/-- **A free direction is not neutral.**  Translating a member of a maximal-face packet by a period
of the face itself moves it by an amount that is not differentially algebraic. -/
theorem not_differentialAlgebraicOver_facePacket_freeStep
    {μ : ℂ} {rad : ι → ℝ} (hrad : ∀ k, 0 < rad k)
    (hind : LinearIndependent ℚ (fun k => μ * (rad k : ℂ)))
    (hω : ∀ k, 0 < (μ * (rad k : ℂ)).im)
    {J : Finset ι} (hcard : (Jᶜ : Finset ι).card = 2) {p : ι} (hp : p ∈ J)
    {x : meroField (Set.univ : Set ℂ)}
    (hx : x ∈ facePacket (fun k => μ * (rad k : ℂ)) hω J) :
    ¬ DifferentialAlgebraicOver ℂ
      (addTranslationMeroEquiv (μ * (rad p : ℂ)) x - x) := by
  classical
  set ω : ι → ℂ := fun k => μ * (rad k : ℂ) with hωdef
  obtain ⟨i, j, hij, hpair⟩ := Finset.card_eq_two.mp hcard
  have hne : (Jᶜ : Finset ι).Nonempty := by
    rw [hpair]
    exact ⟨i, by simp⟩
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
  rw [facePacket_eq ω hω hne, hsrc] at hx
  obtain ⟨α, rfl⟩ := hx
  set e : {k // k ∈ J} → ℤ := fun k => if k = (⟨p, hp⟩ : {k // k ∈ J}) then 1 else 0 with hedef
  have hstep : addTranslationMeroEquiv (ω p)
        (addTranslationMeroEquiv (faceShift ω J α) src)
      = addTranslationMeroEquiv (faceShift ω J (α + e)) src := by
    rw [addTranslationMeroEquiv_add, faceShift_add, faceShift_single ω J hp]
    have harg : faceShift ω J α + ω p = ω p + faceShift ω J α := by ring
    rw [harg]
  have hane : α + e ≠ α := by
    intro hcon
    have hzero : e = 0 := by
      have := congrArg (fun f => f - α) hcon
      simpa using this
    have hval : e (⟨p, hp⟩ : {k // k ∈ J}) = 0 := by rw [hzero]; rfl
    rw [hedef] at hval
    simp at hval
  intro hDA
  refine hC.sub_not_differentialAlgebraic hane ?_
  rw [← hstep]
  exact hDA

/-! ### Disjointness -/

set_option synthInstance.maxHeartbeats 1000000 in
/-- **Distinct maximal faces have disjoint packets.** -/
theorem facePacket_disjoint {μ : ℂ} {rad : ι → ℝ} (hrad : ∀ k, 0 < rad k)
    (hind : LinearIndependent ℚ (fun k => μ * (rad k : ℂ)))
    (hω : ∀ k, 0 < (μ * (rad k : ℂ)).im)
    {J L : Finset ι} (hJ : (Jᶜ : Finset ι).card = 2) (hL : (Lᶜ : Finset ι).card = 2)
    (hJL : J ≠ L) :
    Disjoint (facePacket (fun k => μ * (rad k : ℂ)) hω J)
      (facePacket (fun k => μ * (rad k : ℂ)) hω L) := by
  classical
  set ω : ι → ℂ := fun k => μ * (rad k : ℂ) with hωdef
  have hcompl : (Jᶜ : Finset ι) ≠ (Lᶜ : Finset ι) := by
    intro h
    exact hJL (by simpa using congrArg (fun s : Finset ι => sᶜ) h)
  have hnotsub : ¬ (Jᶜ : Finset ι) ⊆ (Lᶜ : Finset ι) := by
    intro hsub
    exact hcompl (Finset.eq_of_subset_of_card_le hsub (by rw [hJ, hL]))
  obtain ⟨p, hpJ, hpL⟩ := Finset.not_subset.mp hnotsub
  have hpJ' : p ∉ J := Finset.mem_compl.mp hpJ
  have hpL' : p ∈ L := by
    by_contra hcon
    exact hpL (Finset.mem_compl.mpr hcon)
  rw [Set.disjoint_left]
  intro x hxJ hxL
  have hDA : DifferentialAlgebraicOver ℂ (addTranslationMeroEquiv (ω p) x - x) := by
    have h := differentialAlgebraicOver_facePacket_offStar ω hω hJ hpJ' hxJ 1
    have hcast : (((1 : ℤ) : ℂ)) * ω p = ω p := by
      push_cast
      ring
    rwa [hcast] at h
  exact not_differentialAlgebraicOver_facePacket_freeStep hrad hind hω hL hpL' hxL hDA

end

end GaloisForLFunctions.HTGeometry
