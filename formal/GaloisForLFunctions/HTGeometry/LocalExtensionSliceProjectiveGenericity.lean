import GaloisForLFunctions.HTGeometry.HermitianLocalExtensionRelationEscape
import GaloisForLFunctions.HTGeometry.RealAffineHermitianFamilyProjectiveGenericity
import GaloisForLFunctions.HTGeometry.SeparableInteractionTemporalDimensionLaw

/-!
# Generic maximal projective rank in the full real local-extension slice

Every real onsite shift and every entry of a real edge matrix is placed in
one finite coordinate vector.  The resulting local-extension Hamiltonian is
an exact real-affine Hermitian family.  The relation-escape witness therefore
upgrades, by polynomial genericity, to a dense residual full-measure law for
the entire finite physical slice.
-/

open Set Topology MeasureTheory

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Number of real coordinates used by all onsite shifts and all entries of
the real edge matrix. -/
abbrev localExtensionSliceParameterCount (ρ : Type*) [Fintype ρ] : ℕ :=
  Fintype.card (Sum ρ (ρ × ρ))

/-- Decode the finite coordinate vector into onsite shifts and a real edge
matrix. -/
def localExtensionSliceParameter
    {ρ : Type*} [Fintype ρ]
    (p : Fin (localExtensionSliceParameterCount ρ) → ℝ) :
    (ρ → ℝ) × Matrix ρ ρ ℝ :=
  (fun r =>
      p (Fintype.equivFin (Sum ρ (ρ × ρ)) (Sum.inl r)),
    fun r s =>
      p (Fintype.equivFin (Sum ρ (ρ × ρ))
        (Sum.inr (r, s))))

/-- Encode onsite shifts and a real edge matrix in the canonical finite
coordinate vector. -/
def localExtensionSliceCoordinates
    {ρ : Type*} [Fintype ρ]
    (p : (ρ → ℝ) × Matrix ρ ρ ℝ) :
    Fin (localExtensionSliceParameterCount ρ) → ℝ :=
  fun i =>
    match (Fintype.equivFin (Sum ρ (ρ × ρ))).symm i with
    | Sum.inl r => p.1 r
    | Sum.inr rs => p.2 rs.1 rs.2

@[simp] theorem localExtensionSliceParameter_coordinates
    {ρ : Type*} [Fintype ρ]
    (p : (ρ → ℝ) × Matrix ρ ρ ℝ) :
    localExtensionSliceParameter
        (localExtensionSliceCoordinates p) = p := by
  apply Prod.ext
  · funext r
    simp [localExtensionSliceParameter,
      localExtensionSliceCoordinates]
  · funext r s
    simp [localExtensionSliceParameter,
      localExtensionSliceCoordinates]

@[simp] theorem localExtensionSliceCoordinates_parameter
    {ρ : Type*} [Fintype ρ]
    (p : Fin (localExtensionSliceParameterCount ρ) → ℝ) :
    localExtensionSliceCoordinates
        (localExtensionSliceParameter p) = p := by
  funext i
  obtain ⟨r | rs, hi⟩ :=
    (Fintype.equivFin (Sum ρ (ρ × ρ))).surjective i
  · subst i
    simp [localExtensionSliceParameter,
      localExtensionSliceCoordinates]
  · subst i
    simp [localExtensionSliceParameter,
      localExtensionSliceCoordinates]

/-- Hamiltonian at one point of the full real onsite-plus-edge extension
slice. -/
def hermitianLocalExtensionSliceMatrix
    {α ρ : Type*} [Fintype ρ]
    [DecidableEq α] [DecidableEq ρ]
    (energy : α → ℝ)
    (transition : Matrix α α ℂ)
    (p : Fin (localExtensionSliceParameterCount ρ) → ℝ) :
    Matrix (α × ρ) (α × ρ) ℂ :=
  localExtensionMatrix
    (fun a => (energy a : ℂ))
    (realLocalExtensionParameter
      (localExtensionSliceParameter p)).1
    transition
    (realLocalExtensionParameter
      (localExtensionSliceParameter p)).2

/-- Center of the affine local-extension slice. -/
def hermitianLocalExtensionSliceBase
    {α ρ : Type*} [Fintype ρ]
    [DecidableEq α] [DecidableEq ρ]
    (energy : α → ℝ)
    (transition : Matrix α α ℂ) :
    Matrix (α × ρ) (α × ρ) ℂ :=
  hermitianLocalExtensionSliceMatrix energy transition 0

/-- Linear part of the local-extension slice after subtracting its
parameter-independent center. -/
def hermitianLocalExtensionSliceLinearMap
    {α ρ : Type*} [Fintype ρ]
    [DecidableEq α] [DecidableEq ρ]
    (energy : α → ℝ)
    (transition : Matrix α α ℂ) :
    (Fin (localExtensionSliceParameterCount ρ) → ℝ) →ₗ[ℝ]
      Matrix (α × ρ) (α × ρ) ℂ where
  toFun p :=
    hermitianLocalExtensionSliceMatrix energy transition p -
      hermitianLocalExtensionSliceBase energy transition
  map_add' p q := by
    ext x y
    by_cases hxy : x = y
    · subst y
      simp [hermitianLocalExtensionSliceMatrix,
        hermitianLocalExtensionSliceBase,
        localExtensionSliceParameter,
        realLocalExtensionParameter, realSymmetricEdge,
        localExtensionMatrix, layeredEnergy, layerMatrixCoupling]
      ring
    · simp [hermitianLocalExtensionSliceMatrix,
        hermitianLocalExtensionSliceBase,
        localExtensionSliceParameter,
        realLocalExtensionParameter, realSymmetricEdge,
        localExtensionMatrix, layerMatrixCoupling, hxy]
      ring
  map_smul' c p := by
    ext x y
    by_cases hxy : x = y
    · subst y
      simp [hermitianLocalExtensionSliceMatrix,
        hermitianLocalExtensionSliceBase,
        localExtensionSliceParameter,
        realLocalExtensionParameter, realSymmetricEdge,
        localExtensionMatrix, layeredEnergy, layerMatrixCoupling]
      ring
    · simp [hermitianLocalExtensionSliceMatrix,
        hermitianLocalExtensionSliceBase,
        localExtensionSliceParameter,
        realLocalExtensionParameter, realSymmetricEdge,
        localExtensionMatrix, layerMatrixCoupling, hxy]
      ring

/-- Canonical generator attached to one finite slice coordinate. -/
def hermitianLocalExtensionSliceGenerator
    {α ρ : Type*} [Fintype ρ]
    [DecidableEq α] [DecidableEq ρ]
    (energy : α → ℝ)
    (transition : Matrix α α ℂ)
    (i : Fin (localExtensionSliceParameterCount ρ)) :
    Matrix (α × ρ) (α × ρ) ℂ :=
  hermitianLocalExtensionSliceLinearMap energy transition
    (Pi.single i 1)

/-- The finite-coordinate local-extension slice is exactly the real affine
span of its canonical coordinate generators. -/
theorem hermitianLocalExtensionSliceMatrix_eq_realAffineMatrix
    {α ρ : Type*} [Fintype ρ]
    [DecidableEq α] [DecidableEq ρ]
    (energy : α → ℝ)
    (transition : Matrix α α ℂ)
    (p : Fin (localExtensionSliceParameterCount ρ) → ℝ) :
    hermitianLocalExtensionSliceMatrix energy transition p =
      realAffineMatrix
        (hermitianLocalExtensionSliceBase energy transition)
        (hermitianLocalExtensionSliceGenerator energy transition)
        p := by
  have hcoordinates :
      p = ∑ i, (p i) •
        (Pi.single i 1 :
          Fin (localExtensionSliceParameterCount ρ) → ℝ) :=
    pi_eq_sum_univ' p
  calc
    hermitianLocalExtensionSliceMatrix energy transition p =
        hermitianLocalExtensionSliceBase energy transition +
          hermitianLocalExtensionSliceLinearMap
            energy transition p := by
      ext x y
      simp [hermitianLocalExtensionSliceLinearMap]
    _ =
        hermitianLocalExtensionSliceBase energy transition +
          hermitianLocalExtensionSliceLinearMap energy transition
            (∑ i, (p i) •
              (Pi.single i 1 :
                Fin (localExtensionSliceParameterCount ρ) → ℝ)) := by
      rw [← hcoordinates]
    _ =
        hermitianLocalExtensionSliceBase energy transition +
          ∑ i, (p i) •
            hermitianLocalExtensionSliceGenerator
              energy transition i := by
      simp [hermitianLocalExtensionSliceGenerator]
    _ =
        realAffineMatrix
          (hermitianLocalExtensionSliceBase energy transition)
          (hermitianLocalExtensionSliceGenerator energy transition)
          p := by
      ext x y
      simp only [realAffineMatrix, Matrix.add_apply,
        Matrix.sum_apply, Matrix.smul_apply, Algebra.smul_def]
      norm_num

/-- Every point of the coordinate slice is Hermitian. -/
theorem hermitianLocalExtensionSliceMatrix_isHermitian
    {α ρ : Type*} [Fintype ρ]
    [DecidableEq α] [DecidableEq ρ]
    (energy : α → ℝ)
    (transition : Matrix α α ℂ)
    (htransition : transition.IsHermitian)
    (p : Fin (localExtensionSliceParameterCount ρ) → ℝ) :
    (hermitianLocalExtensionSliceMatrix
      energy transition p).IsHermitian :=
  localExtensionMatrix_realParameter_isHermitian
    energy transition htransition
    (localExtensionSliceParameter p)

/-- The affine center is Hermitian. -/
theorem hermitianLocalExtensionSliceBase_isHermitian
    {α ρ : Type*} [Fintype ρ]
    [DecidableEq α] [DecidableEq ρ]
    (energy : α → ℝ)
    (transition : Matrix α α ℂ)
    (htransition : transition.IsHermitian) :
    (hermitianLocalExtensionSliceBase (α := α) (ρ := ρ)
      energy transition).IsHermitian :=
  hermitianLocalExtensionSliceMatrix_isHermitian
    (α := α) (ρ := ρ) energy transition htransition
      (0 : Fin (localExtensionSliceParameterCount ρ) → ℝ)

/-- Every canonical coordinate generator is Hermitian. -/
theorem hermitianLocalExtensionSliceGenerator_isHermitian
    {α ρ : Type*} [Fintype ρ]
    [DecidableEq α] [DecidableEq ρ]
    (energy : α → ℝ)
    (transition : Matrix α α ℂ)
    (htransition : transition.IsHermitian)
    (i : Fin (localExtensionSliceParameterCount ρ)) :
    (hermitianLocalExtensionSliceGenerator (α := α) (ρ := ρ)
      energy transition i).IsHermitian :=
  (hermitianLocalExtensionSliceMatrix_isHermitian
      (α := α) (ρ := ρ) energy transition htransition
      (Pi.single i 1)).sub
    (hermitianLocalExtensionSliceBase_isHermitian
      (α := α) (ρ := ρ) energy transition htransition)

/-- A simple maximally projective real root packet is a permutation of the
canonical eigenvalue list of a Hermitian matrix. -/
theorem maximallyProjectiveEnergy_hermitianEigenvalues_of_rootPacket
    {I : Type*} [Fintype I] [DecidableEq I]
    (H : Matrix I I ℂ) (hH : H.IsHermitian)
    (energy : I → ℝ)
    (hmax : MaximallyProjectiveEnergy energy)
    (hroot :
      ∀ i,
        matrixCharpolyRelation (H, (energy i : ℂ)) = 0) :
    MaximallyProjectiveEnergy hH.eigenvalues := by
  have hinjective : Function.Injective energy :=
    hmax.injective
  let rootsPacket : Multiset ℂ :=
    Finset.univ.val.map (fun i => (energy i : ℂ))
  have hpacketNodup : rootsPacket.Nodup := by
    exact Finset.univ.nodup.map
      (fun _ _ h => hinjective (Complex.ofReal_injective h))
  have hcharpolyNe : H.charpoly ≠ 0 :=
    H.charpoly_monic.ne_zero
  have hpacketLe : rootsPacket ≤ H.charpoly.roots := by
    rw [Multiset.le_iff_subset hpacketNodup]
    intro z hz
    rcases Multiset.mem_map.mp hz with ⟨i, hi, rfl⟩
    rw [Polynomial.mem_roots hcharpolyNe]
    change H.charpoly.eval (energy i : ℂ) = 0
    rw [Matrix.eval_charpoly]
    exact hroot i
  have hrootsCard :
      H.charpoly.roots.card = Fintype.card I := by
    rw [Polynomial.splits_iff_card_roots.mp
      (IsAlgClosed.splits H.charpoly)]
    exact H.charpoly_natDegree_eq_dim
  have hpacketCard :
      rootsPacket.card = Fintype.card I := by
    simp [rootsPacket]
  have hpacketEq : rootsPacket = H.charpoly.roots := by
    apply Multiset.eq_of_le_of_card_le hpacketLe
    rw [hrootsCard, hpacketCard]
  have heigenPacket :
      rootsPacket =
        Finset.univ.val.map
          (fun i => (hH.eigenvalues i : ℂ)) := by
    rw [hpacketEq, hH.roots_charpoly_eq_eigenvalues]
    rfl
  have heigenNodup :
      (Finset.univ.val.map
        (fun i => (hH.eigenvalues i : ℂ))).Nodup := by
    rw [← heigenPacket]
    exact hpacketNodup
  have heigenInjective :
      Function.Injective hH.eigenvalues := by
    intro i j hij
    have hcomplex :
        (hH.eigenvalues i : ℂ) =
          (hH.eigenvalues j : ℂ) := by
      exact_mod_cast hij
    have hmapInjective :
        Function.Injective
          (fun i => (hH.eigenvalues i : ℂ)) := by
      intro a b hab
      exact
        (Multiset.nodup_map_iff_inj_on
          Finset.univ.nodup).mp heigenNodup
            a (Finset.mem_univ a)
            b (Finset.mem_univ b) hab
    exact hmapInjective hcomplex
  have hsurj :
      ∀ i, ∃ j, hH.eigenvalues i = energy j := by
    intro i
    have hi :
        (hH.eigenvalues i : ℂ) ∈ rootsPacket := by
      rw [heigenPacket]
      exact Multiset.mem_map.mpr
        ⟨i, Finset.mem_univ i, rfl⟩
    rcases Multiset.mem_map.mp hi with ⟨j, hj, hji⟩
    exact ⟨j, Complex.ofReal_injective hji.symm⟩
  choose σ hσ using hsurj
  have hσInjective : Function.Injective σ := by
    intro i j hij
    apply heigenInjective
    rw [hσ i, hσ j, hij]
  let e : I ≃ I :=
    Equiv.ofBijective σ
      ⟨hσInjective,
        Finite.surjective_of_injective hσInjective⟩
  have heq :
      hH.eigenvalues = fun i => energy (e i) := by
    funext i
    exact hσ i
  rw [heq]
  exact maximallyProjectiveEnergy_equiv e hmax

/-- Parameters at which the actual Hermitian local-extension slice has
maximal projective spectral rank. -/
def hermitianLocalExtensionSliceMaximalSet
    {α ρ : Type*} [Fintype α] [Fintype ρ]
    [DecidableEq α] [DecidableEq ρ]
    (energy : α → ℝ)
    (transition : Matrix α α ℂ)
    (htransition : transition.IsHermitian) :
    Set (Fin (localExtensionSliceParameterCount ρ) → ℝ) :=
  {p |
    MaximallyProjectiveEnergy
      (hermitianLocalExtensionSliceMatrix_isHermitian
        energy transition htransition p).eigenvalues}

/-- The direct physical definition of the maximal set equals the polynomial
real-affine maximal set used by the genericity engine. -/
theorem hermitianLocalExtensionSliceMaximalSet_eq_realAffine
    {α ρ : Type*} [Fintype α] [Fintype ρ]
    [DecidableEq α] [DecidableEq ρ]
    (energy : α → ℝ)
    (transition : Matrix α α ℂ)
    (htransition : transition.IsHermitian) :
    hermitianLocalExtensionSliceMaximalSet
        (α := α) (ρ := ρ) energy transition htransition =
      realAffineHermitianMaximalSet
        (hermitianLocalExtensionSliceBase
          (α := α) (ρ := ρ) energy transition)
        (hermitianLocalExtensionSliceGenerator
          (α := α) (ρ := ρ) energy transition)
        (hermitianLocalExtensionSliceBase_isHermitian
          (α := α) (ρ := ρ) energy transition htransition)
        (hermitianLocalExtensionSliceGenerator_isHermitian
          (α := α) (ρ := ρ) energy transition htransition) := by
  ext p
  unfold hermitianLocalExtensionSliceMaximalSet
  unfold realAffineHermitianMaximalSet
  unfold polynomialHermitianMatrixMaximalSet
  simp only [Set.mem_setOf_eq]
  let hslice :=
    hermitianLocalExtensionSliceMatrix_isHermitian
      energy transition htransition p
  let haffine :=
    realAffineMatrix_isHermitian
      (hermitianLocalExtensionSliceBase energy transition)
      (hermitianLocalExtensionSliceGenerator energy transition)
      (hermitianLocalExtensionSliceBase_isHermitian
        energy transition htransition)
      (hermitianLocalExtensionSliceGenerator_isHermitian
        energy transition htransition) p
  let hpolynomial :
      ((realAffineMatrixPolynomial
          (hermitianLocalExtensionSliceBase energy transition)
          (hermitianLocalExtensionSliceGenerator
            energy transition)).map
        (MvPolynomial.eval₂Hom (RingHom.id ℂ)
          (fun t => (p t : ℂ)))).IsHermitian := by
    rw [eval_realAffineMatrixPolynomial]
    exact haffine
  change
    MaximallyProjectiveEnergy hslice.eigenvalues ↔
      MaximallyProjectiveEnergy hpolynomial.eigenvalues
  have hsliceAffine :
      hermitianLocalExtensionSliceMatrix energy transition p =
        realAffineMatrix
          (hermitianLocalExtensionSliceBase energy transition)
          (hermitianLocalExtensionSliceGenerator energy transition)
          p :=
    hermitianLocalExtensionSliceMatrix_eq_realAffineMatrix
      energy transition p
  have heigen :
      hslice.eigenvalues = hpolynomial.eigenvalues := by
    apply
      (Matrix.IsHermitian.eigenvalues_eq_eigenvalues_iff
        hslice hpolynomial).2
    rw [eval_realAffineMatrixPolynomial]
    exact congrArg Matrix.charpoly hsliceAffine
  rw [heigen]

/-- **Full-slice physical genericity theorem.** For a maximally projective
old finite spectrum and a finite Hermitian transition family whose
cross-layer lift is connected, one real observable combination has a
maximally projective local-extension witness.  Moreover, maximal projective
rank holds on a dense residual full-measure subset of every real onsite
shift and real-symmetric edge coordinate in that same finite slice. -/
theorem
    hermitianLocalExtensionSliceMaximalSet_dense_residual_fullMeasure_of_family
    {α ρ η : Type*} [Fintype α] [Fintype ρ] [Fintype η]
    [DecidableEq α] [DecidableEq ρ] [DecidableEq η]
    [Nonempty α] [Nonempty ρ]
    (energy : α → ℝ) (hmax : MaximallyProjectiveEnergy energy)
    (shift₀ : ρ → ℝ)
    (transition : η → Matrix α α ℂ)
    (htransition : ∀ i, (transition i).IsHermitian)
    (hsimple :
      Function.Injective
        (layeredEnergy
          (fun a => (energy a : ℂ))
          (fun r => (shift₀ r : ℂ))))
    (hlift :
      (crossLayerLiftGraph
        (transitionFamilySupportGraph transition) ρ).Preconnected) :
    ∃ observableCoefficient : η → ℝ,
      let combinedTransition :=
        realMatrixFamilyCombination
          transition observableCoefficient
      let hcombined :
          combinedTransition.IsHermitian :=
        realMatrixFamilyCombination_isHermitian
          transition htransition observableCoefficient
      ∃ p₀ : Fin (localExtensionSliceParameterCount ρ) → ℝ,
        MaximallyProjectiveEnergy
            (hermitianLocalExtensionSliceMatrix_isHermitian
              (α := α) (ρ := ρ)
              energy combinedTransition hcombined p₀).eigenvalues ∧
          Dense
            (hermitianLocalExtensionSliceMaximalSet
              (α := α) (ρ := ρ)
              energy combinedTransition hcombined) ∧
          hermitianLocalExtensionSliceMaximalSet
              (α := α) (ρ := ρ)
              energy combinedTransition hcombined ∈
            residual
              (Fin (localExtensionSliceParameterCount ρ) → ℝ) ∧
          volume
            (hermitianLocalExtensionSliceMaximalSet
              (α := α) (ρ := ρ)
              energy combinedTransition hcombined)ᶜ = 0 := by
  obtain ⟨observableCoefficient, p, extendedEnergy,
      hextendedMax, hextendedInjective, hroot⟩ :=
    exists_hermitianLocalExtension_maximallyProjectiveRealRootPacket_of_family
      energy hmax shift₀ transition htransition hsimple hlift
  let combinedTransition :=
    realMatrixFamilyCombination
      transition observableCoefficient
  let hcombined : combinedTransition.IsHermitian :=
    realMatrixFamilyCombination_isHermitian
      transition htransition observableCoefficient
  let p₀ : Fin (localExtensionSliceParameterCount ρ) → ℝ :=
    localExtensionSliceCoordinates p
  have hrootSlice :
      ∀ i,
        matrixCharpolyRelation
          (hermitianLocalExtensionSliceMatrix
              energy combinedTransition p₀,
            (extendedEnergy i : ℂ)) = 0 := by
    intro i
    simpa [hermitianLocalExtensionSliceMatrix,
      combinedTransition, p₀] using hroot i
  have hsliceMax :
      MaximallyProjectiveEnergy
        (hermitianLocalExtensionSliceMatrix_isHermitian
          energy combinedTransition hcombined p₀).eigenvalues :=
    maximallyProjectiveEnergy_hermitianEigenvalues_of_rootPacket
      (hermitianLocalExtensionSliceMatrix
        energy combinedTransition p₀)
      (hermitianLocalExtensionSliceMatrix_isHermitian
        energy combinedTransition hcombined p₀)
      extendedEnergy hextendedMax hrootSlice
  have hbase :
      (hermitianLocalExtensionSliceBase (α := α) (ρ := ρ)
        energy combinedTransition).IsHermitian :=
    hermitianLocalExtensionSliceBase_isHermitian
      (α := α) (ρ := ρ)
      energy combinedTransition hcombined
  have hgenerator :
      ∀ i,
        (hermitianLocalExtensionSliceGenerator (α := α) (ρ := ρ)
          energy combinedTransition i).IsHermitian :=
    hermitianLocalExtensionSliceGenerator_isHermitian
      (α := α) (ρ := ρ)
      energy combinedTransition hcombined
  let haffine :=
    realAffineMatrix_isHermitian
      (hermitianLocalExtensionSliceBase energy combinedTransition)
      (hermitianLocalExtensionSliceGenerator
        energy combinedTransition)
      hbase hgenerator p₀
  have hsliceAffine :
      hermitianLocalExtensionSliceMatrix
          energy combinedTransition p₀ =
        realAffineMatrix
          (hermitianLocalExtensionSliceBase
            energy combinedTransition)
          (hermitianLocalExtensionSliceGenerator
            energy combinedTransition)
          p₀ :=
    hermitianLocalExtensionSliceMatrix_eq_realAffineMatrix
      energy combinedTransition p₀
  have heigenAffine :
      (hermitianLocalExtensionSliceMatrix_isHermitian
        energy combinedTransition hcombined p₀).eigenvalues =
          haffine.eigenvalues := by
    apply
      (Matrix.IsHermitian.eigenvalues_eq_eigenvalues_iff
        (hermitianLocalExtensionSliceMatrix_isHermitian
          energy combinedTransition hcombined p₀)
        haffine).2
    exact congrArg Matrix.charpoly hsliceAffine
  have haffineMax :
      MaximallyProjectiveEnergy haffine.eigenvalues := by
    rw [← heigenAffine]
    exact hsliceMax
  have hgeneric :=
    realAffineHermitianMaximalSet_dense_residual_fullMeasure
      (hermitianLocalExtensionSliceBase energy combinedTransition)
      (hermitianLocalExtensionSliceGenerator
        energy combinedTransition)
      hbase hgenerator p₀ haffineMax
  refine ⟨observableCoefficient, p₀, hsliceMax, ?_⟩
  rw [hermitianLocalExtensionSliceMaximalSet_eq_realAffine
    energy combinedTransition hcombined]
  exact hgeneric

end

end GaloisForLFunctions.HTGeometry
