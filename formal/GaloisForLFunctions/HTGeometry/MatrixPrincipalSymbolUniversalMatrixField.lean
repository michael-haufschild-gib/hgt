import GaloisForLFunctions.HTGeometry.MatrixPrincipalSymbolUniversalShiftField
import GaloisForLFunctions.HTGeometry.MatrixPrincipalSymbolCommutatorClosure

/-!
# Universal realization of arbitrary matrix principal-symbol towers

The diagonal universal shift field realizes hyperplane arrangements only.  Here the free jet grid
carries a genuinely matrix-weighted shift: each layer is sent to an arbitrary prescribed
`K`-matrix combination of the next layer.  The complete jets of the 0-layer observables then
satisfy the explicit strict-lower-layer packet law on the nose, with ordered symbol products as
diagonal blocks, and the observable family is differentially independent exactly when every
prescribed matrix is invertible.

Consequently every countable union of matrix determinant loci — including irreducible nonlinear
determinantal cones — is the exact varying-derivation dependence spectrum of one concrete rational
differential field.  The rank-3 quadric cone `A₀² = A₁A₂` is realized explicitly; its symbol
pencil has nonzero coefficient curvature, its realizing derivations do not commute, and no
commutator closure of the law family exists.  This locates the exact boundary of the flat
(commutator-closed) class: nonlinear irreducible horizons force curvature.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open Set MvPolynomial

variable {K g ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]

/-- The polynomial-level matrix-weighted shift on the free jet grid. -/
def universalMatrixShiftPolynomialDerivation (M : ℕ → Matrix ι ι K) :
    Derivation K (UniversalShiftPolynomial K ι) (UniversalShiftField K ι) :=
  MvPolynomial.mkDerivation K fun p : ℕ × ι ↦
    ∑ j, M p.1 p.2 j • universalShiftAncestor (K := K) (p.1 + 1) j

/-- The matrix-weighted shift extended to the universal rational field. -/
def universalMatrixShiftDerivation (M : ℕ → Matrix ι ι K) :
    Derivation K (UniversalShiftField K ι) (UniversalShiftField K ι) :=
  fractionRingDerivation (universalMatrixShiftPolynomialDerivation M)

/-- The universal matrix derivation acts on ancestral coordinates by the prescribed matrix
shift. -/
theorem universalMatrixShiftDerivation_ancestor
    (M : ℕ → Matrix ι ι K) (n : ℕ) (i : ι) :
    universalMatrixShiftDerivation M (universalShiftAncestor (K := K) n i) =
      ∑ j, M n i j • universalShiftAncestor (K := K) (n + 1) j := by
  rw [universalMatrixShiftDerivation, universalShiftAncestor, universalShiftEmbedding_apply,
    fractionRingDerivation_algebraMap]
  rw [universalMatrixShiftPolynomialDerivation, MvPolynomial.mkDerivation_X]

/-- The universal grid satisfies the one-step matrix filtration law exactly. -/
theorem universalMatrixShift_filtrationStep
    (M : ℕ → Matrix ι ι K) (n : ℕ) (i : ι) :
    universalMatrixShiftDerivation M (universalShiftAncestor (K := K) n i) -
        ∑ j, M n i j • universalShiftAncestor (K := K) (n + 1) j ∈
      matrixPacketFiltration (K := K)
        (fun m jj ↦ universalShiftAncestor (K := K) m jj) (n + 1) := by
  rw [universalMatrixShiftDerivation_ancestor, sub_self]
  exact Submodule.zero_mem _

/-- The universal matrix derivation kills `K`-constants compatibly with the zero coefficient
derivation. -/
theorem universalMatrixShift_compat (M : ℕ → Matrix ι ι K) (a : K) :
    universalMatrixShiftDerivation M
        (algebraMap K (UniversalShiftField K ι) a) =
      algebraMap K (UniversalShiftField K ι) ((0 : Derivation K K K) a) := by
  simp

/-- The complete jet packet of the 0-layer observables satisfies the explicit strict-lower-layer
packet law with the ordered symbol products as diagonal blocks. -/
theorem universalMatrixShift_principalLowerLaw (M : ℕ → Matrix ι ι K) :
    MatrixPrincipalLowerLaw
      (fun n i ↦ universalShiftAncestor (K := K) n i)
      (fun n i ↦ selectedDerivationJet (universalMatrixShiftDerivation M) n
        (universalShiftAncestor (K := K) 0 i))
      (matrixSymbolLayerProduct M) :=
  matrixPrincipalLowerLaw_of_filtrationStep (0 : Derivation K K K)
    (universalMatrixShiftDerivation M)
    (fun n i ↦ universalShiftAncestor (K := K) n i) M
    (universalMatrixShift_compat M)
    (universalMatrixShift_filtrationStep M)

/-- **Universal matrix realization.**  The 0-layer observable family of the free grid field is
differentially independent for the matrix-weighted shift exactly when every prescribed matrix
symbol is invertible. -/
theorem universalMatrixShift_derivationIndependentOver_iff (M : ℕ → Matrix ι ι K) :
    DerivationIndependentOver K (universalMatrixShiftDerivation M)
        (universalShiftAncestor (K := K) 0) ↔
      ∀ n, (M n).det ≠ 0 :=
  filtrationStep_derivationIndependentOver_iff (0 : Derivation K K K)
    (universalMatrixShiftDerivation M)
    (fun n i ↦ universalShiftAncestor (K := K) n i) M
    (universalMatrixShift_compat M)
    (universalMatrixShift_filtrationStep M)
    universalShiftAncestor_algebraicIndependent

/-- The matrix-weighted shift law selected by each law-space point. -/
def universalMatrixShiftLaw (M : g → ℕ → Matrix ι ι K) :
    g → Derivation K (UniversalShiftField K ι) (UniversalShiftField K ι) :=
  fun A ↦ universalMatrixShiftDerivation (M A)

/-- **Universal matrix spectrum theorem.**  Every countable union of matrix determinant loci is
the exact varying-derivation differential-dependence spectrum of one concrete observable family
in one concrete rational differential field. -/
theorem universalMatrixShiftLaw_dependentSet_eq_characteristicSet
    (M : g → ℕ → Matrix ι ι K) :
    derivationLawDependentSet (K := K) (universalMatrixShiftLaw M)
        (universalShiftAncestor (K := K) 0) =
      {A : g | ∃ n, (M A n).det = 0} :=
  filtrationStep_dependentSet_eq_characteristicSet
    (universalMatrixShiftLaw M) (fun _ ↦ (0 : Derivation K K K))
    (fun n A ↦ M A n)
    (fun n i ↦ universalShiftAncestor (K := K) n i)
    (fun A ↦ universalMatrixShift_compat (M A))
    (fun A ↦ universalMatrixShift_filtrationStep (M A))
    universalShiftAncestor_algebraicIndependent

/-- Ancestral coordinates are nonzero in the universal field. -/
theorem universalShiftAncestor_ne_zero (n : ℕ) (i : ι) :
    universalShiftAncestor (K := K) n i ≠ 0 := by
  intro h
  apply MvPolynomial.X_ne_zero (R := K) (n, i)
  apply universalShiftEmbedding_injective (K := K) (ι := ι)
  rw [h]
  exact (map_zero _).symm

/-! ## The quadric cone: an irreducible nonlinear determinantal horizon -/

/-- The linear symbol pencil whose determinant is the rank-3 quadric `A₀² - A₁A₂`. -/
def quadricConeSymbol (A : Fin 3 → K) : Matrix (Fin 2) (Fin 2) K :=
  !![A 0, A 1; A 2, A 0]

theorem quadricConeSymbol_det (A : Fin 3 → K) :
    (quadricConeSymbol A).det = A 0 * A 0 - A 1 * A 2 := by
  simp [quadricConeSymbol, Matrix.det_fin_two]

/-- **Concrete nonlinear horizon realization.**  The irreducible quadric cone `A₀² = A₁A₂` is the
exact varying-derivation dependence spectrum of a two-observable family in the universal grid
field. -/
theorem universalQuadric_dependentSet :
    derivationLawDependentSet (K := K)
        (universalMatrixShiftLaw fun A _ ↦ quadricConeSymbol A)
        (universalShiftAncestor (K := K) 0) =
      {A : Fin 3 → K | A 0 * A 0 = A 1 * A 2} := by
  rw [universalMatrixShiftLaw_dependentSet_eq_characteristicSet]
  ext A
  constructor
  · rintro ⟨n, hn⟩
    rw [quadricConeSymbol_det] at hn
    exact sub_eq_zero.mp hn
  · intro hA
    exact ⟨0, by rw [quadricConeSymbol_det]; exact sub_eq_zero.mpr hA⟩

/-- The quadric cone contains both off-diagonal axes but not their sum: it is not the carrier of
any vector subspace, hence not a hyperplane-collapse horizon. -/
theorem quadricCone_not_submodule :
    ∀ H : Submodule K (Fin 3 → K),
      (H : Set (Fin 3 → K)) ≠ {A : Fin 3 → K | A 0 * A 0 = A 1 * A 2} := by
  intro H hEq
  let e1 : Fin 3 → K := Pi.single 1 1
  let e2 : Fin 3 → K := Pi.single 2 1
  have he1 : e1 ∈ H := by
    change e1 ∈ (H : Set (Fin 3 → K))
    rw [hEq]
    simp [e1, Pi.single_apply]
  have he2 : e2 ∈ H := by
    change e2 ∈ (H : Set (Fin 3 → K))
    rw [hEq]
    simp [e2, Pi.single_apply]
  have hsum : e1 + e2 ∈ {A : Fin 3 → K | A 0 * A 0 = A 1 * A 2} := by
    rw [← hEq]
    exact H.add_mem he1 he2
  have : (0 : K) = 1 := by
    simpa [e1, e2, Pi.single_apply] using hsum
  exact zero_ne_one this

/-- The two axis derivations realizing the quadric horizon do not commute: the nonlinear horizon
is carried by genuinely noncommuting laws. -/
theorem universalQuadric_noncommuting_witness :
    ¬ Function.Commute
      (universalMatrixShiftLaw (K := K) (fun A _ ↦ quadricConeSymbol A) (Pi.single 1 1))
      (universalMatrixShiftLaw (K := K) (fun A _ ↦ quadricConeSymbol A) (Pi.single 2 1)) := by
  intro hcomm
  have hpoint := hcomm (universalShiftAncestor (K := K) 0 0)
  have hv0 : universalMatrixShiftLaw (K := K) (fun A _ ↦ quadricConeSymbol A) (Pi.single 1 1)
      (universalShiftAncestor (K := K) 0 0) = universalShiftAncestor (K := K) 1 1 := by
    rw [universalMatrixShiftLaw, universalMatrixShiftDerivation_ancestor]
    simp [quadricConeSymbol, Fin.sum_univ_two, Pi.single_apply]
  have hw0 : universalMatrixShiftLaw (K := K) (fun A _ ↦ quadricConeSymbol A) (Pi.single 2 1)
      (universalShiftAncestor (K := K) 0 0) = 0 := by
    rw [universalMatrixShiftLaw, universalMatrixShiftDerivation_ancestor]
    simp [quadricConeSymbol, Fin.sum_univ_two, Pi.single_apply]
  have hwv : universalMatrixShiftLaw (K := K) (fun A _ ↦ quadricConeSymbol A) (Pi.single 2 1)
      (universalShiftAncestor (K := K) 1 1) = universalShiftAncestor (K := K) 2 0 := by
    rw [universalMatrixShiftLaw, universalMatrixShiftDerivation_ancestor]
    simp [quadricConeSymbol, Fin.sum_univ_two, Pi.single_apply]
  have hzero : universalShiftAncestor (K := K) 2 0 = (0 : UniversalShiftField K (Fin 2)) := by
    have hcalc := hpoint
    rw [Function.comp_apply, Function.comp_apply] at hcalc ⊢
    rw [hw0, hv0, hwv, map_zero] at hcalc
    exact hcalc.symm
  exact universalShiftAncestor_ne_zero 2 0 hzero

/-- The quadric symbol pencil has nonzero matrix coefficient principal curvature. -/
theorem quadricConeSymbol_curvature_ne_zero :
    matrixCoefficientPrincipalCurvature
        (fun (_ : ℕ) (A : Fin 3 → K) ↦ quadricConeSymbol A) 0
        (Pi.single 1 1) (Pi.single 2 1) ≠ 0 := by
  intro h
  have h00 : matrixCoefficientPrincipalCurvature
      (fun (_ : ℕ) (A : Fin 3 → K) ↦ quadricConeSymbol A) 0
      (Pi.single 1 1) (Pi.single 2 1) 0 0 = 0 := by
    rw [h]
    rfl
  rw [matrixCoefficientPrincipalCurvature] at h00
  simp only [Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_two] at h00
  rw [show (quadricConeSymbol (K := K) (Pi.single 1 1)) = !![0, 1; 0, 0] by
        simp [quadricConeSymbol, Pi.single_apply],
      show (quadricConeSymbol (K := K) (Pi.single 2 1)) = !![0, 0; 1, 0] by
        simp [quadricConeSymbol, Pi.single_apply]] at h00
  norm_num at h00

/-- The quadric symbol tower is not coefficient-flat. -/
theorem quadricConeSymbol_not_coefficientFlat :
    ¬ MatrixCoefficientPrincipalSymbolFlat
        (fun (_ : ℕ) (A : Fin 3 → K) ↦ quadricConeSymbol A) := by
  intro hflat
  exact quadricConeSymbol_curvature_ne_zero (K := K)
    (((matrixCoefficientPrincipalSymbolFlat_iff_curvature_zero _).mp hflat) 0
      (Pi.single 1 1) (Pi.single 2 1))

/-- **No commutator closure for the quadric law family.**  The universal realization of the
irreducible quadric horizon cannot close under commutator inside the first-order filtered class:
nonlinear irreducible determinantal horizons force curvature. -/
theorem universalQuadric_no_commutatorClosure :
    ¬ ∃ bracket : (Fin 3 → K) → (Fin 3 → K) → (Fin 3 → K),
      ∀ C D : Fin 3 → K, ∀ x : UniversalShiftField K (Fin 2),
        universalMatrixShiftLaw (fun A _ ↦ quadricConeSymbol A) C
            (universalMatrixShiftLaw (fun A _ ↦ quadricConeSymbol A) D x) -
          universalMatrixShiftLaw (fun A _ ↦ quadricConeSymbol A) D
            (universalMatrixShiftLaw (fun A _ ↦ quadricConeSymbol A) C x) =
        universalMatrixShiftLaw (fun A _ ↦ quadricConeSymbol A) (bracket C D) x :=
  no_commutatorClosure_of_matrixCoefficientPrincipalCurvature_ne_zero
    (universalMatrixShiftLaw fun A _ ↦ quadricConeSymbol A)
    (fun _ ↦ (0 : Derivation K K K))
    (fun (_ : ℕ) (A : Fin 3 → K) ↦ quadricConeSymbol A)
    (fun n i ↦ universalShiftAncestor (K := K) n i)
    (fun A ↦ universalMatrixShift_compat _)
    (fun A ↦ universalMatrixShift_filtrationStep _)
    universalShiftAncestor_algebraicIndependent
    0 (Pi.single 1 1) (Pi.single 2 1)
    quadricConeSymbol_curvature_ne_zero

end

end GaloisForLFunctions.HTGeometry
