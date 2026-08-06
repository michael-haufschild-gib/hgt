import GaloisForLFunctions.HTGeometry.DoubleSineRayMatroid

/-!
# The external orbit of a maximal face

A maximal face `J` of the multiple-sine face complex has a two-element complement `{i, j}`, so its
face coordinate is a double-sine source for the pair of periods `ω i`, `ω j`.  Its external orbit
is indexed by integer vectors on `J`, translating by `∑_{k ∈ J} α_k ω_k`.

Rational independence of the whole period family separates those shifts modulo `ℤ ω_i + ℤ ω_j`:
distinct integer vectors on `J` land in distinct classes, because `i` and `j` are outside `J`.
Hence the external orbit of a maximal face is free.
-/

open Filter Set Topology Complex
open scoped Differential

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions Bottcher

noncomputable section

local instance mfoDomain : IsDomain (analyticSubring (Set.univ : Set ℂ)) :=
  Bottcher.isDomain_analyticSubring Set.univ isOpen_univ isPreconnected_univ Set.univ_nonempty

local instance mfoComplexAlgebra : Algebra ℂ (meroField (Set.univ : Set ℂ)) :=
  ((algebraMap (analyticSubring (Set.univ : Set ℂ)) (meroField Set.univ)).comp
    (constToAnalytic Set.univ)).toAlgebra

local instance mfoMeroDifferential : Differential (meroField (Set.univ : Set ℂ)) :=
  meroFieldDifferential isOpen_univ isPreconnected_univ Set.univ_nonempty

local instance mfoMeroCharZero : CharZero (meroField (Set.univ : Set ℂ)) :=
  charZero_of_injective_algebraMap
    (algebraMap ℂ (meroField (Set.univ : Set ℂ))).injective

local instance mfoComplexDifferential : Differential ℂ where
  deriv := 0

local instance mfoComplexDifferentialAlgebra :
    DifferentialAlgebra ℂ (meroField (Set.univ : Set ℂ)) :=
  ⟨fun c => by
    rw [deriv_algebraMap_complex_mero]
    change (0 : meroField (Set.univ : Set ℂ)) = algebraMap ℂ (meroField Set.univ) 0
    rw [map_zero]⟩

local instance mfoCoordinateDifferential : Differential meromorphicRationalCoordinateField :=
  derivationClosedDifferential _ meromorphicRationalCoordinateField_derivationClosed

local instance mfoCoordinateDifferentialAlgebra :
    DifferentialAlgebra meromorphicRationalCoordinateField (meroField (Set.univ : Set ℂ)) :=
  ⟨fun x => derivationClosedDifferential_apply meromorphicRationalCoordinateField
    meromorphicRationalCoordinateField_derivationClosed x⟩

/-! ### External shifts of a face -/

/-- The external shift of a face attached to an integer vector on it. -/
def faceShift {ι : Type*} (ω : ι → ℂ) (J : Finset ι) (α : {k // k ∈ J} → ℤ) : ℂ :=
  ∑ k ∈ J.attach, (α k : ℂ) * ω k

/-- **Distinct integer vectors on a face give shifts in distinct classes.**  Rational independence
of the whole period family separates them modulo the lattice of the two complementary periods. -/
theorem faceShift_separated {ι : Type} [Fintype ι] [DecidableEq ι]
    {ω : ι → ℂ} (hind : LinearIndependent ℚ ω) {i j : ι} (hij : i ≠ j)
    {J : Finset ι} (hi : i ∉ J) (hj : j ∉ J)
    {α β : {k // k ∈ J} → ℤ} (hne : α ≠ β) (m n : ℤ) :
    faceShift ω J α - faceShift ω J β ≠ (m : ℂ) * ω i + (n : ℂ) * ω j := by
  classical
  intro heq
  set A : ι → ℤ := fun k => if h : k ∈ J then α ⟨k, h⟩ else 0 with hA
  set B : ι → ℤ := fun k => if h : k ∈ J then β ⟨k, h⟩ else 0 with hB
  have hface : ∀ γ : {k // k ∈ J} → ℤ, ∀ C : ι → ℤ,
      (∀ k : {k // k ∈ J}, C (k : ι) = γ k) → (∀ k : ι, k ∉ J → C k = 0) →
      faceShift ω J γ = ∑ k : ι, (C k : ℂ) * ω k := by
    intro γ C hC hC0
    have h1 : faceShift ω J γ = ∑ k ∈ J, (C k : ℂ) * ω k := by
      rw [faceShift, ← Finset.sum_attach J (fun k => (C k : ℂ) * ω k)]
      refine Finset.sum_congr rfl ?_
      intro k _
      rw [hC k]
    rw [h1]
    refine Finset.sum_subset (Finset.subset_univ J) ?_
    intro k _ hkJ
    rw [hC0 k hkJ]
    simp
  have hAface : faceShift ω J α = ∑ k : ι, (A k : ℂ) * ω k := by
    refine hface α A (fun k => ?_) (fun k hk => ?_)
    · rw [hA]
      simp
    · rw [hA]
      simp [hk]
  have hBface : faceShift ω J β = ∑ k : ι, (B k : ℂ) * ω k := by
    refine hface β B (fun k => ?_) (fun k hk => ?_)
    · rw [hB]
      simp
    · rw [hB]
      simp [hk]
  have hsum : ∑ k : ι,
      (((A k - B k : ℤ) : ℚ) - (if k = i then (m : ℚ) else 0)
        - (if k = j then (n : ℚ) else 0)) • ω k = 0 := by
    have hexpand : ∀ k : ι,
        (((A k - B k : ℤ) : ℚ) - (if k = i then (m : ℚ) else 0)
          - (if k = j then (n : ℚ) else 0)) • ω k
        = ((A k : ℂ) * ω k - (B k : ℂ) * ω k)
          - (if k = i then (m : ℂ) * ω k else 0)
          - (if k = j then (n : ℂ) * ω k else 0) := by
      intro k
      rw [Rat.smul_def]
      by_cases h1 : k = i
      · have h2 : k ≠ j := by
          rw [h1]
          exact hij
        rw [if_pos h1, if_neg h2, if_pos h1, if_neg h2]
        push_cast
        ring
      · by_cases h2 : k = j
        · rw [if_neg h1, if_pos h2, if_neg h1, if_pos h2]
          push_cast
          ring
        · rw [if_neg h1, if_neg h2, if_neg h1, if_neg h2]
          push_cast
          ring
    rw [Finset.sum_congr rfl (fun k _ => hexpand k)]
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib]
    rw [Finset.sum_ite_eq' Finset.univ i (fun k => (m : ℂ) * ω k),
      Finset.sum_ite_eq' Finset.univ j (fun k => (n : ℂ) * ω k)]
    rw [if_pos (Finset.mem_univ i), if_pos (Finset.mem_univ j)]
    rw [← hAface, ← hBface]
    rw [heq]
    ring
  have hall := Fintype.linearIndependent_iff.mp hind _ hsum
  obtain ⟨k₀, hk₀⟩ := Function.ne_iff.mp hne
  have hk₀i : (k₀ : ι) ≠ i := fun h => hi (h ▸ k₀.2)
  have hk₀j : (k₀ : ι) ≠ j := fun h => hj (h ▸ k₀.2)
  have h0 := hall (k₀ : ι)
  rw [if_neg hk₀i, if_neg hk₀j, sub_zero, sub_zero] at h0
  have hAk : A (k₀ : ι) = α k₀ := by
    rw [hA]
    simp
  have hBk : B (k₀ : ι) = β k₀ := by
    rw [hB]
    simp
  rw [hAk, hBk] at h0
  have : (α k₀ : ℚ) = (β k₀ : ℚ) := by
    push_cast at h0
    linarith
  exact hk₀ (by exact_mod_cast this)

/-! ### The maximal-face orbit is free -/

theorem irrational_ratio_of_linearIndependent_ray {ι : Type} [DecidableEq ι]
    {μ : ℂ} {r : ι → ℝ} (hr : ∀ k, 0 < r k)
    (hind : LinearIndependent ℚ (fun k => μ * (r k : ℂ))) {i j : ι} (hij : i ≠ j) :
    Irrational (r i / r j) := by
  rintro ⟨q, hq⟩
  have hrj : (r j : ℝ) ≠ 0 := ne_of_gt (hr j)
  have hri : (r i : ℝ) = (q : ℝ) * r j := by
    field_simp at hq
    linarith [hq]
  have hpair : LinearIndependent ℚ ![μ * (r i : ℂ), μ * (r j : ℂ)] := by
    have hinj : Function.Injective (![i, j] : Fin 2 → ι) := by
      intro s t hst
      fin_cases s <;> fin_cases t <;> simp_all
    have hcomp := hind.comp (![i, j] : Fin 2 → ι) hinj
    have hfun : ((fun k => μ * (r k : ℂ)) ∘ (![i, j] : Fin 2 → ι))
        = ![μ * (r i : ℂ), μ * (r j : ℂ)] := by
      funext s
      fin_cases s <;> rfl
    rwa [hfun] at hcomp
  have hrel : (1 : ℚ) • (μ * (r i : ℂ)) + (-q : ℚ) • (μ * (r j : ℂ)) = 0 := by
    rw [Rat.smul_def, Rat.smul_def]
    have : ((r i : ℝ) : ℂ) = ((q : ℚ) : ℂ) * ((r j : ℝ) : ℂ) := by
      rw [show ((r i : ℝ) : ℂ) = (((q : ℝ) * r j : ℝ) : ℂ) by rw [hri]]
      push_cast
      ring
    rw [this]
    push_cast
    ring
  have := (LinearIndependent.pair_iff.mp hpair) 1 (-q) hrel
  exact one_ne_zero this.1

set_option synthInstance.maxHeartbeats 1000000 in
/-- **The external orbit of a maximal face is free.**  For a ray period family with rationally
independent radii and a face `J` whose complement contains the two distinguished indices, the
translates of the double-sine face coordinate by the external shifts of `J` are differentially
independent over `ℂ(z)` and represent the free matroid. -/
theorem multipleSineFaceOrbit_free {ι : Type} [Fintype ι] [DecidableEq ι]
    {μ : ℂ} (hμ : 0 < μ.im) {r : ι → ℝ} (hr : ∀ k, 0 < r k)
    (hind : LinearIndependent ℚ (fun k => μ * (r k : ℂ)))
    {i j : ι} (hij : i ≠ j) {J : Finset ι} (hi : i ∉ J) (hj : j ∉ J) :
    ∃ M : meroField (Set.univ : Set ℂ),
      addTranslationMeroEquiv (μ * (r i : ℂ)) M - M = -periodCotMero (μ * (r j : ℂ)) ∧
        HypertranscendentalOver meromorphicRationalCoordinateField M ∧
        DifferentialIndependent meromorphicRationalCoordinateField
          (fun α : {k // k ∈ J} → ℤ =>
            addTranslationMeroEquiv (faceShift (fun k => μ * (r k : ℂ)) J α) M) ∧
        differentialFamilyMatroid (F := meromorphicRationalCoordinateField)
            (fun α : {k // k ∈ J} → ℤ =>
              addTranslationMeroEquiv (faceShift (fun k => μ * (r k : ℂ)) J α) M)
          = Matroid.freeOn Set.univ := by
  classical
  have hirr : Irrational (r i / r j) :=
    irrational_ratio_of_linearIndependent_ray hr hind hij
  obtain ⟨M, hM0, hMHT, hmatroid, _⟩ :=
    doubleSineRay_rationalBase_matroid hμ (hr i) (hr j) hirr
      (fun α : {k // k ∈ J} → ℤ => faceShift (fun k => μ * (r k : ℂ)) J α)
  have hfree : differentialFamilyMatroid (F := meromorphicRationalCoordinateField)
      (fun α : {k // k ∈ J} → ℤ =>
        addTranslationMeroEquiv (faceShift (fun k => μ * (r k : ℂ)) J α) M)
      = Matroid.freeOn Set.univ := by
    rw [hmatroid]
    refine Matroid.ext_indep (by simp) ?_
    intro I _
    rw [affineCollisionMatroid_indep_iff, Matroid.freeOn_indep_iff]
    constructor
    · intro _
      exact Set.subset_univ I
    · intro _ α _ β _ hframe
      by_contra hne
      obtain ⟨m, n, hclass⟩ :=
        (periodClass_eq_iff ![μ * (r i : ℂ), μ * (r j : ℂ)] _ _).1 hframe
      have hω0 : (![μ * (r i : ℂ), μ * (r j : ℂ)] : Fin 2 → ℂ) 0 = μ * (r i : ℂ) := rfl
      have hω1 : (![μ * (r i : ℂ), μ * (r j : ℂ)] : Fin 2 → ℂ) 1 = μ * (r j : ℂ) := rfl
      rw [hω0, hω1] at hclass
      exact faceShift_separated hind hij hi hj hne m n hclass
  exact ⟨M, hM0, hMHT, differentialFamilyMatroid_eq_freeOn_iff.mp hfree, hfree⟩

end

end GaloisForLFunctions.HTGeometry
