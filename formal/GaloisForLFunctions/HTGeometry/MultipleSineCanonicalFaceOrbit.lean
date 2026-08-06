import GaloisForLFunctions.HTGeometry.MultipleSineFaceOrbitMatroid
import GaloisForLFunctions.HTGeometry.DifferentialFamilyMatroidBaseGauge

/-!
# The canonical face coordinate and its external orbit

The face coordinate of a maximal face is the multiple-sine source of the complementary frame,
`frameSourceMero ω hω {i, j}`, not a source chosen from an existential.  The exact double-sine
difference equations hold for that canonical source shifted by one rational function, and a
rational shift is a base gauge over `ℂ(z)`, so it does not change the represented matroid.

Hence the external orbit of the canonical face coordinate is itself free over `ℂ(z)`.  This is the
form the face-gluing engine consumes: a canonical packet attached to each face, with no choice
data.
-/

open Filter Set Topology Complex
open scoped Differential

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions Bottcher

noncomputable section

local instance mcfDomain : IsDomain (analyticSubring (Set.univ : Set ℂ)) :=
  Bottcher.isDomain_analyticSubring Set.univ isOpen_univ isPreconnected_univ Set.univ_nonempty

local instance mcfComplexAlgebra : Algebra ℂ (meroField (Set.univ : Set ℂ)) :=
  ((algebraMap (analyticSubring (Set.univ : Set ℂ)) (meroField Set.univ)).comp
    (constToAnalytic Set.univ)).toAlgebra

local instance mcfMeroDifferential : Differential (meroField (Set.univ : Set ℂ)) :=
  meroFieldDifferential isOpen_univ isPreconnected_univ Set.univ_nonempty

local instance mcfMeroCharZero : CharZero (meroField (Set.univ : Set ℂ)) :=
  charZero_of_injective_algebraMap
    (algebraMap ℂ (meroField (Set.univ : Set ℂ))).injective

local instance mcfComplexDifferential : Differential ℂ where
  deriv := 0

local instance mcfComplexDifferentialAlgebra :
    DifferentialAlgebra ℂ (meroField (Set.univ : Set ℂ)) :=
  ⟨fun c => by
    rw [deriv_algebraMap_complex_mero]
    change (0 : meroField (Set.univ : Set ℂ)) = algebraMap ℂ (meroField Set.univ) 0
    rw [map_zero]⟩

local instance mcfCoordinateDifferential : Differential meromorphicRationalCoordinateField :=
  derivationClosedDifferential _ meromorphicRationalCoordinateField_derivationClosed

local instance mcfCoordinateDifferentialAlgebra :
    DifferentialAlgebra meromorphicRationalCoordinateField (meroField (Set.univ : Set ℂ)) :=
  ⟨fun x => derivationClosedDifferential_apply meromorphicRationalCoordinateField
    meromorphicRationalCoordinateField_derivationClosed x⟩

/-! ### The ray parent with a supplied source -/

set_option synthInstance.maxHeartbeats 1000000 in
/-- **Ray independence for a given source.**  The ray form of the orbit criterion, stated for a
source that is handed in rather than produced: any source with the two exact cotangent defects for
the ray periods `μ a`, `μ b` has differentially independent translates over `ℂ(z)` along shifts in
distinct classes modulo the period lattice. -/
theorem doubleSineRay_independent_of_source {μ : ℂ} (hμ : μ ≠ 0) {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hirr : Irrational (a / b))
    (M : meroField (Set.univ : Set ℂ)) (cst : ℂ)
    (hM0 : addTranslationMeroEquiv (μ * (a : ℂ)) M - M = -periodCotMero (μ * (b : ℂ)))
    (hM1 : addTranslationMeroEquiv (μ * (b : ℂ)) M - M
      = -periodCotMero (μ * (a : ℂ)) + ratMero (RatFunc.C cst))
    {κ : Type*} [DecidableEq κ] (sh : κ → ℂ)
    (hsep : ∀ i j : κ, i ≠ j → ∀ m n : ℤ,
      sh i - sh j ≠ (m : ℂ) * (μ * (a : ℂ)) + (n : ℂ) * (μ * (b : ℂ))) :
    DifferentialIndependent meromorphicRationalCoordinateField
      (fun j : κ => addTranslationMeroEquiv (sh j) M) := by
  classical
  set ω : Fin 2 → ℂ := ![μ * (a : ℂ), μ * (b : ℂ)] with hωdef
  have hω0 : ω 0 = μ * (a : ℂ) := by simp [hωdef]
  have hω1 : ω 1 = μ * (b : ℂ) := by simp [hωdef]
  have haC : ((a : ℝ) : ℂ) ≠ 0 := by simpa using ne_of_gt ha
  have hbC : ((b : ℝ) : ℂ) ≠ 0 := by simpa using ne_of_gt hb
  have hω0ne : ω 0 ≠ 0 := by
    rw [hω0]
    exact mul_ne_zero hμ haC
  have hω1ne : ω 1 ≠ 0 := by
    rw [hω1]
    exact mul_ne_zero hμ hbC
  set l : Fin 2 → ℂ :=
    ![2 * (Real.pi : ℂ) * Complex.I / (μ * (a : ℂ)),
      2 * (Real.pi : ℂ) * Complex.I / (μ * (b : ℂ))] with hldef
  have hl : LinearIndependent ℚ l :=
    linearIndependent_cylinderFrequencies_ray hμ ha hb hirr
  have hl0 : l 0 = 2 * (Real.pi : ℂ) * Complex.I / ω 0 := by
    rw [hldef, hω0]
    simp
  have hl1 : l 1 = 2 * (Real.pi : ℂ) * Complex.I / ω 1 := by
    rw [hldef, hω1]
    simp
  have hper0 : Complex.exp (l 0 * ω 0) = 1 := by
    rw [hl0, div_mul_cancel₀ _ hω0ne]
    simp
  have hper1 : Complex.exp (l 1 * ω 1) = 1 := by
    rw [hl1, div_mul_cancel₀ _ hω1ne]
    simp
  have hprod : l 1 * ω 0 = 2 * (Real.pi : ℂ) * Complex.I * ((a / b : ℝ) : ℂ) := by
    rw [hl1, hω1, hω0]
    push_cast
    field_simp
  have htor : ∀ n : ℤ, n ≠ 0 → Complex.exp (l 1 * ω 0) ^ n ≠ 1 := by
    intro n hn
    rw [hprod]
    exact exp_two_pi_I_zpow_ne_one hirr hn
  have hfix : ∀ z : meroField (Set.univ : Set ℂ),
      addTranslationMeroEquiv (ω 0) z = z → addTranslationMeroEquiv (ω 1) z = z →
        ∃ w : ℂ, algebraMap ℂ (meroField (Set.univ : Set ℂ)) w = z := by
    intro z h1 h2
    rw [hω0] at h1
    rw [hω1] at h2
    exact exists_constant_of_two_rayPeriods_fixed hμ hirr h1 h2
  have hd0 : addTranslationMeroEquiv (ω 0) M - M = -periodCotMero (ω 1) := by
    rw [hω0, hω1]; exact hM0
  have hd1 : addTranslationMeroEquiv (ω 1) M - M
      = -periodCotMero (ω 0) + ratMero (RatFunc.C cst) := by
    rw [hω0, hω1]; exact hM1
  have hsep' : ∀ p q : κ, p ≠ q → ∀ m n : ℤ,
      sh p - sh q ≠ (m : ℂ) * ω 0 + (n : ℂ) * ω 1 := by
    intro p q hpq m n
    rw [hω0, hω1]
    exact hsep p q hpq m n
  exact doubleSineOrbit_differentialIndependent_rationalBase hl ω hω0ne hω1ne hl0 hl1
    hper0 hper1 htor hfix M cst hd0 hd1 sh hsep'

/-! ### The canonical face coordinate -/

theorem ratMero_mem_rationalCoordinateField (q : ℂ) (t : RatFunc ℂ) :
    addTranslationMeroEquiv q (ratMero t) ∈ meromorphicRationalCoordinateField :=
  addTranslationMeroAlgEquiv_mem_rationalCoordinateField q
    ((mem_meromorphicRationalCoordinateField_iff _).mpr ⟨t, rfl⟩)

set_option synthInstance.maxHeartbeats 1000000 in
/-- **The canonical maximal-face orbit is free.**  For a ray period family with rationally
independent periods, the external translates of the canonical face coordinate
`frameSourceMero ω hω {i, j}` along a face `J` avoiding `i` and `j` are differentially independent
over `ℂ(z)`. -/
theorem multipleSineCanonicalFaceOrbit_free {ι : Type} [Fintype ι] [DecidableEq ι]
    {μ : ℂ} {rad : ι → ℝ} (hrad : ∀ k, 0 < rad k)
    (hind : LinearIndependent ℚ (fun k => μ * (rad k : ℂ)))
    (hω : ∀ k, 0 < (μ * (rad k : ℂ)).im)
    {i j : ι} (hij : i ≠ j) {J : Finset ι} (hi : i ∉ J) (hj : j ∉ J)
    (hS : ({i, j} : Finset ι).Nonempty) :
    DifferentialIndependent meromorphicRationalCoordinateField
      (fun α : {k // k ∈ J} → ℤ =>
        addTranslationMeroEquiv (faceShift (fun k => μ * (rad k : ℂ)) J α)
          (frameSourceMero (fun k => μ * (rad k : ℂ)) hω ({i, j} : Finset ι) hS)) := by
  classical
  set ω : ι → ℂ := fun k => μ * (rad k : ℂ) with hωdef
  have hμ : μ ≠ 0 := by
    intro h
    have hi0 := hω i
    rw [h] at hi0
    simp at hi0
  have hirr : Irrational (rad i / rad j) :=
    irrational_ratio_of_linearIndependent_ray hrad hind hij
  have hcard : ({i, j} : Finset ι).card = 2 := Finset.card_pair hij
  have himem : i ∈ ({i, j} : Finset ι) := by simp
  have hjmem : j ∈ ({i, j} : Finset ι) := by simp
  obtain ⟨t, cst, hd0, hd1⟩ :=
    exists_exact_doubleSine_source ω hω ({i, j} : Finset ι) i j himem hjmem hij hcard hS
  set Mcan : meroField (Set.univ : Set ℂ) :=
    frameSourceMero ω hω ({i, j} : Finset ι) hS with hMcan
  set M : meroField (Set.univ : Set ℂ) := Mcan + ratMero t with hM
  have hsep : ∀ α β : {k // k ∈ J} → ℤ, α ≠ β → ∀ m n : ℤ,
      faceShift ω J α - faceShift ω J β
        ≠ (m : ℂ) * (μ * (rad i : ℂ)) + (n : ℂ) * (μ * (rad j : ℂ)) := by
    intro α β hne m n
    exact faceShift_separated hind hij hi hj hne m n
  have hfam : DifferentialIndependent meromorphicRationalCoordinateField
      (fun α : {k // k ∈ J} → ℤ =>
        addTranslationMeroEquiv (faceShift ω J α) M) :=
    doubleSineRay_independent_of_source hμ (hrad i) (hrad j) hirr M cst hd0 hd1
      (fun α : {k // k ∈ J} → ℤ => faceShift ω J α) hsep
  set base : ({k // k ∈ J} → ℤ) → meromorphicRationalCoordinateField :=
    fun α => ⟨addTranslationMeroEquiv (faceShift ω J α) (ratMero t),
      ratMero_mem_rationalCoordinateField _ t⟩ with hbase
  have hsplit : (fun α : {k // k ∈ J} → ℤ =>
        addTranslationMeroEquiv (faceShift ω J α) Mcan
          + algebraMap meromorphicRationalCoordinateField
            (meroField (Set.univ : Set ℂ)) (base α))
      = fun α : {k // k ∈ J} → ℤ => addTranslationMeroEquiv (faceShift ω J α) M := by
    funext α
    rw [hM, (addTranslationMeroEquiv (faceShift ω J α)).map_add]
    rfl
  have hmatroid := differentialFamilyMatroid_addBase_eq
    (F := meromorphicRationalCoordinateField)
    (fun α : {k // k ∈ J} → ℤ => addTranslationMeroEquiv (faceShift ω J α) Mcan) base
  rw [hsplit] at hmatroid
  rw [differentialFamilyMatroid_eq_freeOn_iff.mpr hfam] at hmatroid
  exact differentialFamilyMatroid_eq_freeOn_iff.mp hmatroid.symm

end

end GaloisForLFunctions.HTGeometry
