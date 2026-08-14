import GaloisForLFunctions.HTGeometry.MultipleSineFaceLabelDescent

/-!
# Separation of difference cubes over the bottom layer of the multiple sine

The packets of the maximal faces are jointly differentially independent over the rational
coordinate field, hence — together with the constant `1`, which is the empty monomial — linearly
independent over it.  A signed combination of bottom packet elements in which one element occurs
with a nonzero coefficient therefore never lies in `ℂ(z)`.

Two instances carry the face-depth argument: a single translate is never a nontrivial difference
cube of the same bottom coordinate, and difference cubes over two distinct bottom faces never
agree, both modulo `ℂ(z)`.
-/

open Filter Set Topology Complex
open scoped Differential BigOperators

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions Bottcher
open GaloisForLFunctions.MatroidGluing GaloisForLFunctions.MatroidGluing.Rank

noncomputable section

attribute [local instance] ellipticGammaRationalBaseDomain
  ellipticGammaRationalBaseComplexAlgebraMero ellipticGammaRationalBaseComplexDifferential
  ellipticGammaRationalBaseMeroDifferential ellipticGammaRationalBaseMeroCharZero
  ellipticGammaRationalBaseComplexDifferentialAlgebra
  ellipticGammaRationalBaseCoordinateDifferential
  ellipticGammaRationalBaseCoordinateDifferentialAlgebra

/-! ### Adjoining the constant to an algebraically independent family -/

/-- **The constant `1` extends an algebraically independent family to a linearly independent one.**
The constant is the empty monomial, and the monomials in an algebraically independent family are
linearly independent. -/
theorem algebraicIndependent_linearIndependent_option
    {R A σ : Type*} [CommRing R] [CommRing A] [Algebra R A]
    {v : σ → A} (hv : AlgebraicIndependent R v) :
    LinearIndependent R (fun o : Option σ => o.elim 1 v) := by
  classical
  have hbasis : LinearIndependent R
      (fun m : σ →₀ ℕ => (MvPolynomial.monomial m 1 : MvPolynomial σ R)) := by
    simp only [← MvPolynomial.coe_basisMonomials]
    exact (MvPolynomial.basisMonomials σ R).linearIndependent
  have hker : LinearMap.ker
      ((MvPolynomial.aeval v : MvPolynomial σ R →ₐ[R] A) : MvPolynomial σ R →ₗ[R] A) = ⊥ :=
    LinearMap.ker_eq_bot.mpr hv
  have hmap := hbasis.map'
    ((MvPolynomial.aeval v : MvPolynomial σ R →ₐ[R] A) : MvPolynomial σ R →ₗ[R] A) hker
  have hinj : Function.Injective
      (fun o : Option σ => o.elim (0 : σ →₀ ℕ) (fun i => Finsupp.single i 1)) := by
    intro a b hab
    cases a with
    | none =>
        cases b with
        | none => rfl
        | some j => exact absurd hab.symm (by simp)
    | some i =>
        cases b with
        | none => exact absurd hab (by simp)
        | some j =>
            have hs : (Finsupp.single i 1 : σ →₀ ℕ) = Finsupp.single j 1 := hab
            exact congrArg some (Finsupp.single_left_injective one_ne_zero hs)
  have hcomp := hmap.comp _ hinj
  have hfun : (fun o : Option σ => o.elim 1 v)
      = ((⇑((MvPolynomial.aeval v : MvPolynomial σ R →ₐ[R] A) : MvPolynomial σ R →ₗ[R] A))
          ∘ fun m : σ →₀ ℕ => (MvPolynomial.monomial m 1 : MvPolynomial σ R))
        ∘ (fun o : Option σ => o.elim (0 : σ →₀ ℕ) (fun i => Finsupp.single i 1)) := by
    funext o
    cases o with
    | none => simp
    | some i => simp [MvPolynomial.aeval_monomial, Finsupp.prod_single_index]
  rw [hfun]
  exact hcomp

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ### The bottom star and its span -/

/-- The union of the packets of all maximal faces. -/
def sineBottomStar (ω : ι → ℂ) (hω : ∀ k, 0 < (ω k).im) : Set (meroField (Set.univ : Set ℂ)) :=
  faceStar (maximalFaces ι) (facePacket ω hω) ∅

theorem facePacket_subset_sineBottomStar (ω : ι → ℂ) (hω : ∀ k, 0 < (ω k).im) {K : Finset ι}
    (hK : (Kᶜ : Finset ι).card = 2) : facePacket ω hω K ⊆ sineBottomStar ω hω := by
  intro y hy
  exact Set.mem_iUnion₂.mpr
    ⟨K, Finset.mem_filter.mpr ⟨(mem_maximalFaces_iff K).mpr hK, by simp⟩, hy⟩

theorem translate_mem_facePacket (ω : ι → ℂ) (hω : ∀ k, 0 < (ω k).im) {K : Finset ι}
    (hne : (Kᶜ : Finset ι).Nonempty) {g : ℂ} (hg : g ∈ faceShiftLattice ω K) :
    addTranslationMeroEquiv g (frameSourceMero ω hω (Kᶜ : Finset ι) hne)
      ∈ facePacket ω hω K := by
  obtain ⟨α, rfl⟩ := exists_faceShift_of_mem_faceShiftLattice ω hg
  rw [facePacket_eq ω hω hne]
  exact ⟨α, rfl⟩

/-- The span, over the rational coordinate field, of the constants together with all bottom packet
elements except one. -/
def sineBottomSpan (ω : ι → ℂ) (hω : ∀ k, 0 < (ω k).im) (i0 : ↥(sineBottomStar ω hω)) :
    Submodule ↥meromorphicRationalCoordinateField (meroField (Set.univ : Set ℂ)) :=
  Submodule.span ↥meromorphicRationalCoordinateField
    ((fun o : Option ↥(sineBottomStar ω hω) => o.elim 1 Subtype.val) '' (Set.univ \ {some i0}))

theorem mem_sineBottomSpan_of_ne (ω : ι → ℂ) (hω : ∀ k, 0 < (ω k).im)
    {i0 i : ↥(sineBottomStar ω hω)} (hne : i ≠ i0) :
    (i : meroField (Set.univ : Set ℂ)) ∈ sineBottomSpan ω hω i0 := by
  refine Submodule.subset_span ⟨some i, ⟨Set.mem_univ _, ?_⟩, rfl⟩
  simpa using hne

theorem mem_sineBottomSpan_of_mem_rationalCoordinateField (ω : ι → ℂ) (hω : ∀ k, 0 < (ω k).im)
    (i0 : ↥(sineBottomStar ω hω)) {x : meroField (Set.univ : Set ℂ)}
    (hx : x ∈ meromorphicRationalCoordinateField) : x ∈ sineBottomSpan ω hω i0 := by
  have h1 : (1 : meroField (Set.univ : Set ℂ)) ∈ sineBottomSpan ω hω i0 :=
    Submodule.subset_span ⟨none, ⟨Set.mem_univ _, by simp⟩, rfl⟩
  have hsmul := (sineBottomSpan ω hω i0).smul_mem
    (⟨x, hx⟩ : ↥meromorphicRationalCoordinateField) h1
  simpa [Algebra.smul_def] using hsmul

set_option synthInstance.maxHeartbeats 1000000 in
/-- **No bottom packet element lies in the span of the others and the constants.** -/
theorem notMem_sineBottomSpan {μ : ℂ} {rad : ι → ℝ} (hrad : ∀ k, 0 < rad k)
    (hind : LinearIndependent ℚ (fun k => μ * (rad k : ℂ)))
    (hω : ∀ k, 0 < (μ * (rad k : ℂ)).im)
    (i0 : ↥(sineBottomStar (fun k => μ * (rad k : ℂ)) hω)) :
    (i0 : meroField (Set.univ : Set ℂ))
      ∉ sineBottomSpan (fun k => μ * (rad k : ℂ)) hω i0 := by
  have hdiff := multipleSineMaximalFaces_diffIndepOn_rationalBase hrad hind hω
  have halg : AlgebraicIndependent ↥meromorphicRationalCoordinateField
      (Subtype.val : ↥(sineBottomStar (fun k => μ * (rad k : ℂ)) hω)
        → meroField (Set.univ : Set ℂ)) :=
    (show DifferentialIndependent ↥meromorphicRationalCoordinateField
      (Subtype.val : ↥(sineBottomStar (fun k => μ * (rad k : ℂ)) hω)
        → meroField (Set.univ : Set ℂ)) from hdiff).algebraicIndependent
  have hlin := algebraicIndependent_linearIndependent_option halg
  exact linearIndependent_iff_notMem_span.mp hlin (some i0)

/-! ### A translate is never a nontrivial difference cube of the same bottom coordinate -/

set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 1000000 in
/-- **A translate is not a difference cube with a separated term.**  If some term of the cube
differs from the given translate, the two cannot agree modulo the rational coordinate field. -/
theorem bottom_translate_sub_cube_notMem_rational {μ : ℂ} {rad : ι → ℝ} (hrad : ∀ k, 0 < rad k)
    (hind : LinearIndependent ℚ (fun k => μ * (rad k : ℂ)))
    (hω : ∀ k, 0 < (μ * (rad k : ℂ)).im)
    {K : Finset ι} (hK : (Kᶜ : Finset ι).card = 2) (hne : (Kᶜ : Finset ι).Nonempty)
    (U : Finset ι) (hUK : U ⊆ K)
    {g h : ℂ} (hg : g ∈ faceShiftLattice (fun k => μ * (rad k : ℂ)) K)
    (hh : h ∈ faceShiftLattice (fun k => μ * (rad k : ℂ)) K)
    (E0 : Finset ι) (hE0 : E0 ∈ U.powerset)
    (hsep : h + ∑ i ∈ E0, μ * (rad i : ℂ) ≠ g) (m n : ℕ) :
    (-1 : meroField (Set.univ : Set ℂ)) ^ m *
          addTranslationMeroEquiv g
            (frameSourceMero (fun k => μ * (rad k : ℂ)) hω (Kᶜ : Finset ι) hne)
        - (-1 : meroField (Set.univ : Set ℂ)) ^ n *
          faceDifferenceCube (fun k => μ * (rad k : ℂ)) U h
            (frameSourceMero (fun k => μ * (rad k : ℂ)) hω (Kᶜ : Finset ι) hne)
      ∉ meromorphicRationalCoordinateField := by
  classical
  set ω : ι → ℂ := fun k => μ * (rad k : ℂ) with hωdef
  have hQ : PeriodsIntegrallyIndependent ω := periodsIntegrallyIndependent_ray hrad hind hω
  have h2 : 2 ≤ (Kᶜ : Finset ι).card := by omega
  set F : meroField (Set.univ : Set ℂ) := frameSourceMero ω hω (Kᶜ : Finset ι) hne with hF
  have hlabel : ∀ {a b : ℂ}, a ∈ faceShiftLattice ω K → b ∈ faceShiftLattice ω K →
      addTranslationMeroEquiv a F = addTranslationMeroEquiv b F → a = b := by
    intro a b ha hb hab
    exact frameSource_translate_injective hrad hind hω h2 hne ha hb hab
  have hE0K : E0 ⊆ K := fun i hi => hUK (Finset.mem_powerset.mp hE0 hi)
  have hhE0 : h + ∑ i ∈ E0, ω i ∈ faceShiftLattice ω K :=
    faceShiftLattice_add_subsetSum ω K E0 hE0K hh
  set i0 : ↥(sineBottomStar ω hω) :=
    ⟨addTranslationMeroEquiv (h + ∑ i ∈ E0, ω i) F,
      facePacket_subset_sineBottomStar ω hω hK (translate_mem_facePacket ω hω hne hhE0)⟩ with hi0
  set ig : ↥(sineBottomStar ω hω) :=
    ⟨addTranslationMeroEquiv g F,
      facePacket_subset_sineBottomStar ω hω hK (translate_mem_facePacket ω hω hne hg)⟩ with hig
  have hig_ne : ig ≠ i0 := by
    intro hcon
    exact hsep (hlabel hhE0 hg (congrArg (fun x : ↥(sineBottomStar ω hω) =>
      (x : meroField (Set.univ : Set ℂ))) hcon).symm)
  set raw : Finset ι → meroField (Set.univ : Set ℂ) := fun E =>
    (-1 : meroField (Set.univ : Set ℂ)) ^ (U.card - E.card) *
      addTranslationMeroEquiv (h + ∑ i ∈ E, ω i) F with hraw
  have hrest : ∀ E ∈ U.powerset.erase E0, raw E ∈ sineBottomSpan ω hω i0 := by
    intro E hE
    have hEU : E ⊆ U := Finset.mem_powerset.mp (Finset.mem_of_mem_erase hE)
    have hEK : E ⊆ K := fun i hi => hUK (hEU hi)
    have hhE : h + ∑ i ∈ E, ω i ∈ faceShiftLattice ω K :=
      faceShiftLattice_add_subsetSum ω K E hEK hh
    set iE : ↥(sineBottomStar ω hω) :=
      ⟨addTranslationMeroEquiv (h + ∑ i ∈ E, ω i) F,
        facePacket_subset_sineBottomStar ω hω hK (translate_mem_facePacket ω hω hne hhE)⟩ with hiE
    have hEE0 : E ≠ E0 := Finset.ne_of_mem_erase hE
    have hiE_ne : iE ≠ i0 := by
      intro hcon
      have hshift := hlabel hhE hhE0 (congrArg (fun x : ↥(sineBottomStar ω hω) =>
        (x : meroField (Set.univ : Set ℂ))) hcon)
      exact hEE0 (periodSubsetSum_injective ω hQ (add_left_cancel hshift))
    have hmem := mem_sineBottomSpan_of_ne ω hω hiE_ne
    have hsmul := (sineBottomSpan ω hω i0).smul_mem
      (⟨(-1 : meroField (Set.univ : Set ℂ)) ^ (U.card - E.card),
        pow_mem (neg_mem (one_mem meromorphicRationalCoordinateField)) _⟩
        : ↥meromorphicRationalCoordinateField) hmem
    simpa [hraw, hiE, Algebra.smul_def] using hsmul
  intro hcon
  have hcube : (∑ E ∈ U.powerset.erase E0, raw E) + raw E0
      = faceDifferenceCube ω U h F := by
    rw [faceDifferenceCube]
    exact Finset.sum_erase_add U.powerset raw hE0
  have hrawE0 : raw E0 = (-1 : meroField (Set.univ : Set ℂ)) ^ (U.card - E0.card) *
      (i0 : meroField (Set.univ : Set ℂ)) := rfl
  have hig_mem : (ig : meroField (Set.univ : Set ℂ)) ∈ sineBottomSpan ω hω i0 :=
    mem_sineBottomSpan_of_ne ω hω hig_ne
  have hdecomp : (-1 : meroField (Set.univ : Set ℂ)) ^ n * raw E0
      = (-1 : meroField (Set.univ : Set ℂ)) ^ m * (ig : meroField (Set.univ : Set ℂ))
        - ((-1 : meroField (Set.univ : Set ℂ)) ^ m *
              (ig : meroField (Set.univ : Set ℂ))
            - (-1 : meroField (Set.univ : Set ℂ)) ^ n * faceDifferenceCube ω U h F)
        - (-1 : meroField (Set.univ : Set ℂ)) ^ n *
            ∑ E ∈ U.powerset.erase E0, raw E := by
    rw [← hcube]
    ring
  have hmem0 : (-1 : meroField (Set.univ : Set ℂ)) ^ n * raw E0 ∈ sineBottomSpan ω hω i0 := by
    rw [hdecomp]
    refine Submodule.sub_mem _ (Submodule.sub_mem _ ?_ ?_) ?_
    · have hsmul := (sineBottomSpan ω hω i0).smul_mem
        (⟨(-1 : meroField (Set.univ : Set ℂ)) ^ m,
          pow_mem (neg_mem (one_mem meromorphicRationalCoordinateField)) _⟩
          : ↥meromorphicRationalCoordinateField) hig_mem
      simpa [Algebra.smul_def] using hsmul
    · exact mem_sineBottomSpan_of_mem_rationalCoordinateField ω hω i0 hcon
    · have hsum : ∑ E ∈ U.powerset.erase E0, raw E ∈ sineBottomSpan ω hω i0 :=
        Submodule.sum_mem _ hrest
      have hsmul := (sineBottomSpan ω hω i0).smul_mem
        (⟨(-1 : meroField (Set.univ : Set ℂ)) ^ n,
          pow_mem (neg_mem (one_mem meromorphicRationalCoordinateField)) _⟩
          : ↥meromorphicRationalCoordinateField) hsum
      simpa [Algebra.smul_def] using hsmul
  rw [hrawE0] at hmem0
  have hcoeff : ((-1 : meroField (Set.univ : Set ℂ)) ^ n *
      (-1 : meroField (Set.univ : Set ℂ)) ^ (U.card - E0.card)) ≠ 0 := by
    refine mul_ne_zero (pow_ne_zero _ ?_) (pow_ne_zero _ ?_) <;>
      exact neg_ne_zero.mpr one_ne_zero
  have hi0_mem : (i0 : meroField (Set.univ : Set ℂ)) ∈ sineBottomSpan ω hω i0 := by
    have hsmul : ((⟨(-1 : meroField (Set.univ : Set ℂ)) ^ n *
        (-1 : meroField (Set.univ : Set ℂ)) ^ (U.card - E0.card),
        mul_mem (pow_mem (neg_mem (one_mem meromorphicRationalCoordinateField)) _)
          (pow_mem (neg_mem (one_mem meromorphicRationalCoordinateField)) _)⟩
        : ↥meromorphicRationalCoordinateField)) •
          (i0 : meroField (Set.univ : Set ℂ)) ∈ sineBottomSpan ω hω i0 := by
      simpa [Algebra.smul_def, mul_assoc] using hmem0
    have hunit : (⟨(-1 : meroField (Set.univ : Set ℂ)) ^ n *
        (-1 : meroField (Set.univ : Set ℂ)) ^ (U.card - E0.card),
        mul_mem (pow_mem (neg_mem (one_mem meromorphicRationalCoordinateField)) _)
          (pow_mem (neg_mem (one_mem meromorphicRationalCoordinateField)) _)⟩
        : ↥meromorphicRationalCoordinateField) ≠ 0 := by
      intro hzero
      exact hcoeff (congrArg (fun x : ↥meromorphicRationalCoordinateField =>
        (x : meroField (Set.univ : Set ℂ))) hzero)
    exact ((sineBottomSpan ω hω i0).smul_mem_iff hunit).mp hsmul
  exact notMem_sineBottomSpan hrad hind hω i0 hi0_mem

/-! ### Difference cubes over distinct bottom faces are separated -/

set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 1000000 in
/-- **Difference cubes over distinct bottom faces never agree modulo the rational coordinate
field.** -/
theorem bottom_cube_sub_cube_notMem_rational {μ : ℂ} {rad : ι → ℝ} (hrad : ∀ k, 0 < rad k)
    (hind : LinearIndependent ℚ (fun k => μ * (rad k : ℂ)))
    (hω : ∀ k, 0 < (μ * (rad k : ℂ)).im)
    {K M : Finset ι} (hK : (Kᶜ : Finset ι).card = 2) (hM : (Mᶜ : Finset ι).card = 2)
    (hKM : K ≠ M) (hneK : (Kᶜ : Finset ι).Nonempty) (hneM : (Mᶜ : Finset ι).Nonempty)
    (V W : Finset ι) (hVK : V ⊆ K) (hWM : W ⊆ M)
    {g h : ℂ} (hg : g ∈ faceShiftLattice (fun k => μ * (rad k : ℂ)) K)
    (hh : h ∈ faceShiftLattice (fun k => μ * (rad k : ℂ)) M) (m n : ℕ) :
    (-1 : meroField (Set.univ : Set ℂ)) ^ m *
          faceDifferenceCube (fun k => μ * (rad k : ℂ)) V g
            (frameSourceMero (fun k => μ * (rad k : ℂ)) hω (Kᶜ : Finset ι) hneK)
        - (-1 : meroField (Set.univ : Set ℂ)) ^ n *
          faceDifferenceCube (fun k => μ * (rad k : ℂ)) W h
            (frameSourceMero (fun k => μ * (rad k : ℂ)) hω (Mᶜ : Finset ι) hneM)
      ∉ meromorphicRationalCoordinateField := by
  classical
  set ω : ι → ℂ := fun k => μ * (rad k : ℂ) with hωdef
  have hQ : PeriodsIntegrallyIndependent ω := periodsIntegrallyIndependent_ray hrad hind hω
  have h2K : 2 ≤ (Kᶜ : Finset ι).card := by omega
  set FK : meroField (Set.univ : Set ℂ) := frameSourceMero ω hω (Kᶜ : Finset ι) hneK with hFK
  set FM : meroField (Set.univ : Set ℂ) := frameSourceMero ω hω (Mᶜ : Finset ι) hneM with hFM
  have hdisj := facePacket_disjoint hrad hind hω hK hM hKM
  set i0 : ↥(sineBottomStar ω hω) :=
    ⟨addTranslationMeroEquiv g FK,
      facePacket_subset_sineBottomStar ω hω hK (translate_mem_facePacket ω hω hneK hg)⟩ with hi0
  set rawK : Finset ι → meroField (Set.univ : Set ℂ) := fun E =>
    (-1 : meroField (Set.univ : Set ℂ)) ^ (V.card - E.card) *
      addTranslationMeroEquiv (g + ∑ i ∈ E, ω i) FK with hrawK
  set rawM : Finset ι → meroField (Set.univ : Set ℂ) := fun E =>
    (-1 : meroField (Set.univ : Set ℂ)) ^ (W.card - E.card) *
      addTranslationMeroEquiv (h + ∑ i ∈ E, ω i) FM with hrawM
  have hrestK : ∀ E ∈ V.powerset.erase ∅, rawK E ∈ sineBottomSpan ω hω i0 := by
    intro E hE
    have hEV : E ⊆ V := Finset.mem_powerset.mp (Finset.mem_of_mem_erase hE)
    have hEK : E ⊆ K := fun i hi => hVK (hEV hi)
    have hgE : g + ∑ i ∈ E, ω i ∈ faceShiftLattice ω K :=
      faceShiftLattice_add_subsetSum ω K E hEK hg
    set iE : ↥(sineBottomStar ω hω) :=
      ⟨addTranslationMeroEquiv (g + ∑ i ∈ E, ω i) FK,
        facePacket_subset_sineBottomStar ω hω hK (translate_mem_facePacket ω hω hneK hgE)⟩ with hiE
    have hEne : E ≠ ∅ := Finset.ne_of_mem_erase hE
    have hiE_ne : iE ≠ i0 := by
      intro hcon
      have hshift := frameSource_translate_injective hrad hind hω h2K hneK hgE hg
        (congrArg (fun x : ↥(sineBottomStar ω hω) =>
          (x : meroField (Set.univ : Set ℂ))) hcon)
      refine hEne (periodSubsetSum_injective ω hQ ?_)
      have hzero : g + ∑ i ∈ E, ω i = g + ∑ i ∈ (∅ : Finset ι), ω i := by
        simpa using hshift
      exact add_left_cancel hzero
    have hmem := mem_sineBottomSpan_of_ne ω hω hiE_ne
    have hsmul := (sineBottomSpan ω hω i0).smul_mem
      (⟨(-1 : meroField (Set.univ : Set ℂ)) ^ (V.card - E.card),
        pow_mem (neg_mem (one_mem meromorphicRationalCoordinateField)) _⟩
        : ↥meromorphicRationalCoordinateField) hmem
    simpa [hrawK, hiE, Algebra.smul_def] using hsmul
  have hallM : ∀ E ∈ W.powerset, rawM E ∈ sineBottomSpan ω hω i0 := by
    intro E hE
    have hEW : E ⊆ W := Finset.mem_powerset.mp hE
    have hEM : E ⊆ M := fun i hi => hWM (hEW hi)
    have hhE : h + ∑ i ∈ E, ω i ∈ faceShiftLattice ω M :=
      faceShiftLattice_add_subsetSum ω M E hEM hh
    have hmemM : addTranslationMeroEquiv (h + ∑ i ∈ E, ω i) FM ∈ facePacket ω hω M :=
      translate_mem_facePacket ω hω hneM hhE
    set iE : ↥(sineBottomStar ω hω) :=
      ⟨addTranslationMeroEquiv (h + ∑ i ∈ E, ω i) FM,
        facePacket_subset_sineBottomStar ω hω hM hmemM⟩ with hiE
    have hiE_ne : iE ≠ i0 := by
      intro hcon
      have hval : addTranslationMeroEquiv (h + ∑ i ∈ E, ω i) FM
          = addTranslationMeroEquiv g FK := by
        have hc := congrArg (fun x : ↥(sineBottomStar ω hω) =>
          (x : meroField (Set.univ : Set ℂ))) hcon
        simpa [hiE, hi0] using hc
      exact Set.disjoint_left.mp hdisj (translate_mem_facePacket ω hω hneK hg)
        (hval ▸ hmemM)
    have hmem := mem_sineBottomSpan_of_ne ω hω hiE_ne
    have hsmul := (sineBottomSpan ω hω i0).smul_mem
      (⟨(-1 : meroField (Set.univ : Set ℂ)) ^ (W.card - E.card),
        pow_mem (neg_mem (one_mem meromorphicRationalCoordinateField)) _⟩
        : ↥meromorphicRationalCoordinateField) hmem
    simpa [hrawM, hiE, Algebra.smul_def] using hsmul
  intro hcon
  have hcubeK : (∑ E ∈ V.powerset.erase ∅, rawK E) + rawK ∅
      = faceDifferenceCube ω V g FK := by
    rw [faceDifferenceCube]
    exact Finset.sum_erase_add V.powerset rawK (by simp)
  have hcubeM : ∑ E ∈ W.powerset, rawM E = faceDifferenceCube ω W h FM := rfl
  have hraw0 : rawK ∅ = (-1 : meroField (Set.univ : Set ℂ)) ^ V.card *
      (i0 : meroField (Set.univ : Set ℂ)) := by
    simp [hrawK, hi0]
  have hdecomp : (-1 : meroField (Set.univ : Set ℂ)) ^ m * rawK ∅
      = ((-1 : meroField (Set.univ : Set ℂ)) ^ m * faceDifferenceCube ω V g FK
            - (-1 : meroField (Set.univ : Set ℂ)) ^ n * faceDifferenceCube ω W h FM)
        + (-1 : meroField (Set.univ : Set ℂ)) ^ n * ∑ E ∈ W.powerset, rawM E
        - (-1 : meroField (Set.univ : Set ℂ)) ^ m * ∑ E ∈ V.powerset.erase ∅, rawK E := by
    rw [hcubeM, ← hcubeK]
    ring
  have hmem0 : (-1 : meroField (Set.univ : Set ℂ)) ^ m * rawK ∅ ∈ sineBottomSpan ω hω i0 := by
    rw [hdecomp]
    refine Submodule.sub_mem _ (Submodule.add_mem _ ?_ ?_) ?_
    · exact mem_sineBottomSpan_of_mem_rationalCoordinateField ω hω i0 hcon
    · have hsum : ∑ E ∈ W.powerset, rawM E ∈ sineBottomSpan ω hω i0 :=
        Submodule.sum_mem _ hallM
      have hsmul := (sineBottomSpan ω hω i0).smul_mem
        (⟨(-1 : meroField (Set.univ : Set ℂ)) ^ n,
          pow_mem (neg_mem (one_mem meromorphicRationalCoordinateField)) _⟩
          : ↥meromorphicRationalCoordinateField) hsum
      simpa [Algebra.smul_def] using hsmul
    · have hsum : ∑ E ∈ V.powerset.erase ∅, rawK E ∈ sineBottomSpan ω hω i0 :=
        Submodule.sum_mem _ hrestK
      have hsmul := (sineBottomSpan ω hω i0).smul_mem
        (⟨(-1 : meroField (Set.univ : Set ℂ)) ^ m,
          pow_mem (neg_mem (one_mem meromorphicRationalCoordinateField)) _⟩
          : ↥meromorphicRationalCoordinateField) hsum
      simpa [Algebra.smul_def] using hsmul
  rw [hraw0] at hmem0
  have hcoeff : ((-1 : meroField (Set.univ : Set ℂ)) ^ m *
      (-1 : meroField (Set.univ : Set ℂ)) ^ V.card) ≠ 0 := by
    refine mul_ne_zero (pow_ne_zero _ ?_) (pow_ne_zero _ ?_) <;>
      exact neg_ne_zero.mpr one_ne_zero
  have hi0_mem : (i0 : meroField (Set.univ : Set ℂ)) ∈ sineBottomSpan ω hω i0 := by
    have hsmul : ((⟨(-1 : meroField (Set.univ : Set ℂ)) ^ m *
        (-1 : meroField (Set.univ : Set ℂ)) ^ V.card,
        mul_mem (pow_mem (neg_mem (one_mem meromorphicRationalCoordinateField)) _)
          (pow_mem (neg_mem (one_mem meromorphicRationalCoordinateField)) _)⟩
        : ↥meromorphicRationalCoordinateField)) •
          (i0 : meroField (Set.univ : Set ℂ)) ∈ sineBottomSpan ω hω i0 := by
      simpa [Algebra.smul_def, mul_assoc] using hmem0
    have hunit : (⟨(-1 : meroField (Set.univ : Set ℂ)) ^ m *
        (-1 : meroField (Set.univ : Set ℂ)) ^ V.card,
        mul_mem (pow_mem (neg_mem (one_mem meromorphicRationalCoordinateField)) _)
          (pow_mem (neg_mem (one_mem meromorphicRationalCoordinateField)) _)⟩
        : ↥meromorphicRationalCoordinateField) ≠ 0 := by
      intro hzero
      exact hcoeff (congrArg (fun x : ↥meromorphicRationalCoordinateField =>
        (x : meroField (Set.univ : Set ℂ))) hzero)
    exact ((sineBottomSpan ω hω i0).smul_mem_iff hunit).mp hsmul
  exact notMem_sineBottomSpan hrad hind hω i0 hi0_mem

end

end GaloisForLFunctions.HTGeometry
