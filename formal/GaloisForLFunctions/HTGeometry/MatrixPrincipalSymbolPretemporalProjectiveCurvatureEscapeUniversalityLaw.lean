import GaloisForLFunctions.HTGeometry.UniversalQuadricCausalChamberLaw
import GaloisForLFunctions.HTGeometry.MatrixPrincipalSymbolPretemporalUniversalityLaw

/-!
# Pretemporal projective-curvature escape universality

An honest coefficient-flat selected-jet tower with one common algebraically independent source
has no varying-law dependence spectrum, and its zeroth matrix symbol cannot be law-linear.  The
universal quadric tower realizes the exact complementary mechanism: its nonlinear dependence
cone is invariant along every punctured law ray, its causal chamber is nonempty, and the escape
from pretemporal rigidity is witnessed simultaneously by nonzero coefficient curvature,
noncommuting laws, and failure of every subspace horizon.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The complete concrete certificate carried by the universal quadric escape model. -/
def UniversalQuadricProjectiveCurvatureEscapeCertificate : Prop :=
  (matrixPrincipalCausalChamber quadricConeSymbolLinear).Nonempty ∧
    matrixPrincipalCausalChamber quadricConeSymbolLinear ⊆
      {A | DerivationIndependentOver ℝ
        (universalMatrixShiftLaw
          (fun A (_ : ℕ) ↦ quadricConeSymbol A) A)
        (universalShiftAncestor (K := ℝ) 0)} ∧
    derivationLawDependentSet (K := ℝ)
        (universalMatrixShiftLaw
          (fun A (_ : ℕ) ↦ quadricConeSymbol A))
        (universalShiftAncestor (K := ℝ) 0) =
      {A : Fin 3 → ℝ | A 0 * A 0 = A 1 * A 2} ∧
    matrixCoefficientPrincipalCurvature
        (fun (_ : ℕ) (A : Fin 3 → ℝ) ↦ quadricConeSymbol A) 0
        (Pi.single 1 1) (Pi.single 2 1) ≠ 0 ∧
    (∀ H : Submodule ℝ (Fin 3 → ℝ),
      (H : Set (Fin 3 → ℝ)) ≠
        {A : Fin 3 → ℝ | A 0 * A 0 = A 1 * A 2}) ∧
    ¬ ∃ bracket : (Fin 3 → ℝ) → (Fin 3 → ℝ) → (Fin 3 → ℝ),
      ∀ C D : Fin 3 → ℝ, ∀ x : UniversalShiftField ℝ (Fin 2),
        universalMatrixShiftLaw
              (fun A (_ : ℕ) ↦ quadricConeSymbol A) C
            (universalMatrixShiftLaw
              (fun A (_ : ℕ) ↦ quadricConeSymbol A) D x) -
          universalMatrixShiftLaw
              (fun A (_ : ℕ) ↦ quadricConeSymbol A) D
            (universalMatrixShiftLaw
              (fun A (_ : ℕ) ↦ quadricConeSymbol A) C x) =
        universalMatrixShiftLaw
          (fun A (_ : ℕ) ↦ quadricConeSymbol A) (bracket C D) x

/-- The exact nonlinear dependence spectrum and its complementary independent phase are invariant
under every nonzero rescaling of the universal quadric law coordinate. -/
theorem universalQuadric_projectivePhase
    (A : Fin 3 → ℝ) (c : ℝ) (hc : c ≠ 0) :
    ((c • A) ∈
        derivationLawDependentSet (K := ℝ)
          (universalMatrixShiftLaw
            (fun A (_ : ℕ) ↦ quadricConeSymbol A))
          (universalShiftAncestor (K := ℝ) 0) ↔
      A ∈
        derivationLawDependentSet (K := ℝ)
          (universalMatrixShiftLaw
            (fun A (_ : ℕ) ↦ quadricConeSymbol A))
          (universalShiftAncestor (K := ℝ) 0)) ∧
    (DerivationIndependentOver ℝ
        (universalMatrixShiftLaw
          (fun A (_ : ℕ) ↦ quadricConeSymbol A) (c • A))
        (universalShiftAncestor (K := ℝ) 0) ↔
      DerivationIndependentOver ℝ
        (universalMatrixShiftLaw
          (fun A (_ : ℕ) ↦ quadricConeSymbol A) A)
        (universalShiftAncestor (K := ℝ) 0)) := by
  classical
  have hdependent :
      (c • A) ∈
          derivationLawDependentSet (K := ℝ)
            (universalMatrixShiftLaw
              (fun A (_ : ℕ) ↦ quadricConeSymbol A))
            (universalShiftAncestor (K := ℝ) 0) ↔
        A ∈
          derivationLawDependentSet (K := ℝ)
            (universalMatrixShiftLaw
              (fun A (_ : ℕ) ↦ quadricConeSymbol A))
            (universalShiftAncestor (K := ℝ) 0) := by
    rw [universalQuadric_dependentSet]
    simp only [Set.mem_setOf_eq, Pi.smul_apply, smul_eq_mul]
    constructor <;> intro h
    · apply (mul_left_cancel₀ (mul_ne_zero hc hc))
      calc
        c * c * (A 0 * A 0) = (c * A 0) * (c * A 0) := by ring
        _ = (c * A 1) * (c * A 2) := h
        _ = c * c * (A 1 * A 2) := by ring
    · calc
        c * A 0 * (c * A 0) = c * c * (A 0 * A 0) := by ring
        _ = c * c * (A 1 * A 2) := by rw [h]
        _ = c * A 1 * (c * A 2) := by ring
  refine ⟨hdependent, ?_⟩
  simpa only [derivationLawDependentSet, Set.mem_setOf_eq, not_not] using
    not_congr hdependent

/-- The universal quadric supplies the complete projective, curved, noncommutative escape
certificate. -/
theorem universalQuadric_projectiveCurvatureEscapeCertificate :
    UniversalQuadricProjectiveCurvatureEscapeCertificate := by
  obtain ⟨hchamber, hindependent, hspectrum, hcurvature⟩ :=
    universalQuadric_nonemptyCausalChamber_curvedBoundary
  exact ⟨hchamber, hindependent, hspectrum, hcurvature,
    quadricCone_not_submodule, universalQuadric_no_commutatorClosure⟩

variable {k K L h ι : Type*} [Field k] [Field K] [Field L]
  [Algebra k L] [Algebra K L] [Fintype ι] [DecidableEq ι]
  [Nonempty ι] [AddCommGroup h] [Module K h]

/-- **Pretemporal projective-curvature escape universality law.**  Every honest regular
coefficient-flat common-source selected-jet model is rigid: its dependence spectrum is empty and
its zeroth principal symbol cannot be law-linear.  Simultaneously, one concrete universal model
has a nonempty independent causal chamber and a genuinely projective nonlinear dependence cone;
that cone is neither a subspace nor commutator-closed, and its coefficient curvature is nonzero. -/
theorem pretemporalFlat_projectiveCurvatureEscapeUniversality
    (source : ℕ → ι → L) (observable : ι → L)
    (law : h → Derivation k L L)
    (symbol : ℕ → h → Matrix ι ι K)
    (hflat : MatrixCoefficientPrincipalSymbolFlat symbol)
    (e : h) (he : ∀ n, (symbol n e).det ≠ 0)
    (hlaw : ∀ A, MatrixPrincipalLowerLaw source
      (fun n i ↦ selectedDerivationJet (law A) n (observable i))
      (fun n ↦ symbol n A))
    (hsource : AlgebraicIndependent K
      (fun p : ℕ × ι ↦ source p.1 p.2)) :
    (derivationLawDependentSet (K := K) law observable = ∅ ∧
      ∀ S : h →ₗ[K] Matrix ι ι K, ¬ ∀ A, symbol 0 A = S A) ∧
    (∀ (A : Fin 3 → ℝ) (c : ℝ), c ≠ 0 →
      ((c • A) ∈
          derivationLawDependentSet (K := ℝ)
            (universalMatrixShiftLaw
              (fun A (_ : ℕ) ↦ quadricConeSymbol A))
            (universalShiftAncestor (K := ℝ) 0) ↔
        A ∈
          derivationLawDependentSet (K := ℝ)
            (universalMatrixShiftLaw
              (fun A (_ : ℕ) ↦ quadricConeSymbol A))
            (universalShiftAncestor (K := ℝ) 0)) ∧
      (DerivationIndependentOver ℝ
          (universalMatrixShiftLaw
            (fun A (_ : ℕ) ↦ quadricConeSymbol A) (c • A))
          (universalShiftAncestor (K := ℝ) 0) ↔
        DerivationIndependentOver ℝ
          (universalMatrixShiftLaw
            (fun A (_ : ℕ) ↦ quadricConeSymbol A) A)
          (universalShiftAncestor (K := ℝ) 0))) ∧
    UniversalQuadricProjectiveCurvatureEscapeCertificate := by
  exact ⟨pretemporalAnchor_emptySpectrum_and_noLinearZeroSymbol
      source observable law symbol hflat e he hlaw hsource,
    fun A c hc ↦ universalQuadric_projectivePhase A c hc,
    universalQuadric_projectiveCurvatureEscapeCertificate⟩

end

end GaloisForLFunctions.HTGeometry
