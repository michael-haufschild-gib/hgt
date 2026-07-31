import GaloisForLFunctions.HTGeometry.MatrixPrincipalSymbolAbelianRigidity
import Mathlib.LinearAlgebra.Eigenspace.Pi
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable

/-!
# Joint spectral collapse of a regular flat principal tower

Abelian rigidity has a geometric consequence over an algebraically closed field.  At every layer,
the normalized matrix family is a commuting family of endomorphisms, so its joint maximal
generalized eigenspaces span the full observable space.  This is the basis-free simultaneous
triangularization statement behind the factorization of a linear determinant horizon into linear
eigencharacters.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open Submodule

variable {K g ι : Type*} [Field K] [IsAlgClosed K]
  [Fintype ι] [DecidableEq ι]

/-- A normalized principal symbol viewed as an endomorphism of the coordinate fiber. -/
def coefficientNormalizedPrincipalEnd
    (symbol : ℕ → g → Matrix ι ι K) (e : g) (n : ℕ) (A : g) :
    Module.End K (ι → K) :=
  Matrix.toLin' (coefficientNormalizedMatrixPrincipalSymbol symbol e n A)

omit [IsAlgClosed K] in
/-- Normalized principal endomorphisms commute pairwise in a regular flat tower. -/
theorem coefficientNormalizedPrincipalEnd_commute
    (symbol : ℕ → g → Matrix ι ι K)
    (hflat : MatrixCoefficientPrincipalSymbolFlat symbol)
    (e : g) (he : ∀ n, (symbol n e).det ≠ 0)
    (n : ℕ) (A B : g) :
    Commute
      (coefficientNormalizedPrincipalEnd symbol e n A)
      (coefficientNormalizedPrincipalEnd symbol e n B) := by
  have hcomm := coefficientNormalizedMatrixPrincipalSymbol_commute
    symbol hflat e he n A B
  change (Matrix.toLin' (coefficientNormalizedMatrixPrincipalSymbol symbol e n A)).comp
      (Matrix.toLin' (coefficientNormalizedMatrixPrincipalSymbol symbol e n B)) =
    (Matrix.toLin' (coefficientNormalizedMatrixPrincipalSymbol symbol e n B)).comp
      (Matrix.toLin' (coefficientNormalizedMatrixPrincipalSymbol symbol e n A))
  rw [← Matrix.toLin'_mul, ← Matrix.toLin'_mul, hcomm.eq]

/-- The simultaneous maximal generalized eigenspace attached to a candidate joint character. -/
def normalizedPrincipalJointMaxGenEigenspace
    (symbol : ℕ → g → Matrix ι ι K) (e : g) (n : ℕ) (χ : g → K) :
    Submodule K (ι → K) :=
  ⨅ A : g, (coefficientNormalizedPrincipalEnd symbol e n A).maxGenEigenspace (χ A)

omit [IsAlgClosed K] in
/-- Joint generalized eigenspaces of a regular flat tower are independent. -/
theorem normalizedPrincipalJointMaxGenEigenspace_iSupIndep
    (symbol : ℕ → g → Matrix ι ι K)
    (hflat : MatrixCoefficientPrincipalSymbolFlat symbol)
    (e : g) (he : ∀ n, (symbol n e).det ≠ 0)
    (n : ℕ) :
    iSupIndep (normalizedPrincipalJointMaxGenEigenspace symbol e n) := by
  apply Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo
    (coefficientNormalizedPrincipalEnd symbol e n)
  intro A B μ
  exact Module.End.mapsTo_maxGenEigenspace_of_comm
    (coefficientNormalizedPrincipalEnd_commute symbol hflat e he n B A) μ

/-- **Joint spectral collapse.**  Every regular coefficient-flat finite-rank tower is jointly
triangularizable at every layer: the joint maximal generalized eigenspaces of the complete
normalized law family span the observable fiber. -/
theorem coefficientNormalizedPrincipalEnd_jointMaxGenEigenspaces_eq_top
    (symbol : ℕ → g → Matrix ι ι K)
    (hflat : MatrixCoefficientPrincipalSymbolFlat symbol)
    (e : g) (he : ∀ n, (symbol n e).det ≠ 0)
    (n : ℕ) :
    ⨆ χ : g → K, ⨅ A : g,
      (coefficientNormalizedPrincipalEnd symbol e n A).maxGenEigenspace (χ A) = ⊤ := by
  apply Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute
    (coefficientNormalizedPrincipalEnd symbol e n)
  · intro A B _
    exact coefficientNormalizedPrincipalEnd_commute symbol hflat e he n A B
  · intro A
    exact Module.End.iSup_maxGenEigenspace_eq_top
      (coefficientNormalizedPrincipalEnd symbol e n A)

/-! ## Fiberwise joint spectral decomposition -/

omit [IsAlgClosed K] in
/-- Fiberwise simultaneous triangularization.  For a compatible triangularizable family, the
maximal generalized `φ`-eigenspace of one member is exactly the sum of the joint generalized
eigenspaces whose character takes the value `φ` on that member. -/
theorem iSup_jointMaxGenEigenspace_fiber_eq
    {I M : Type*} [AddCommGroup M] [Module K M] [FiniteDimensional K M]
    (f : I → Module.End K M)
    (hmaps : ∀ i j φ,
      Set.MapsTo (f i) ((f j).maxGenEigenspace φ) ((f j).maxGenEigenspace φ))
    (htri : ∀ i, ⨆ μ, (f i).maxGenEigenspace μ = ⊤)
    (i : I) (φ : K) :
    ⨆ (χ : I → K) (_ : χ i = φ), ⨅ j, (f j).maxGenEigenspace (χ j) =
      (f i).maxGenEigenspace φ := by
  have hi (j : I) (ψ : K) :
      Set.MapsTo (f j) ((f i).maxGenEigenspace ψ) ((f i).maxGenEigenspace ψ) :=
    hmaps j i ψ
  have hspan :
      ⨆ χ : I → K, ⨅ j,
        Module.End.maxGenEigenspace ((f j).restrict (hi j φ)) (χ j) = ⊤ := by
    apply Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_forall_mapsTo
    · intro j k μ
      exact Module.End.mapsTo_restrict_maxGenEigenspace_restrict_of_mapsTo
        (f j) (f k) (hi j φ) (hi k φ) (hmaps j k μ)
    · exact fun j ↦ Module.End.genEigenspace_restrict_eq_top _ (htri j)
  have hspanFiber :
      ⨆ (χ : I → K) (_ : χ i = φ), ⨅ j,
        Module.End.maxGenEigenspace ((f j).restrict (hi j φ)) (χ j) = ⊤ := by
    suffices ∀ χ : I → K, χ i ≠ φ →
        ⨅ j, Module.End.maxGenEigenspace ((f j).restrict (hi j φ)) (χ j) = ⊥ by
      rw [iSup_split, biSup_congr this] at hspan
      simpa using hspan
    intro χ hχ
    rw [eq_bot_iff, ← ((f i).maxGenEigenspace φ).ker_subtype, LinearMap.ker,
      ← Submodule.map_le_iff_le_comap,
      ← Submodule.inf_iInf_maxGenEigenspace_of_forall_mapsTo,
      ← disjoint_iff_inf_le]
    exact ((f i).disjoint_genEigenspace hχ.symm _ _).mono_right (iInf_le _ i)
  have hrestrict (χ : I → K) (hχ : χ i = φ) :
      ⨅ j, Module.End.maxGenEigenspace (f j) (χ j) =
        (⨅ j, Module.End.maxGenEigenspace ((f j).restrict (hi j φ)) (χ j)).map
          ((f i).maxGenEigenspace φ).subtype := by
    rw [← hχ, Module.End.iInf_maxGenEigenspace_restrict_map_subtype_eq]
  simp_rw [biSup_congr hrestrict, ← Submodule.map_iSup, hspanFiber, Submodule.map_top,
    Submodule.range_subtype]

/-- At any selected law, each generalized spectral fiber is exactly the sum of the normalized
joint sectors having the corresponding character value. -/
theorem coefficientNormalizedPrincipalEnd_jointFiber_eq
    (symbol : ℕ → g → Matrix ι ι K)
    (hflat : MatrixCoefficientPrincipalSymbolFlat symbol)
    (e : g) (he : ∀ n, (symbol n e).det ≠ 0)
    (n : ℕ) (A : g) (φ : K) :
    ⨆ (χ : g → K) (_ : χ A = φ),
        normalizedPrincipalJointMaxGenEigenspace symbol e n χ =
      (coefficientNormalizedPrincipalEnd symbol e n A).maxGenEigenspace φ := by
  apply iSup_jointMaxGenEigenspace_fiber_eq
    (coefficientNormalizedPrincipalEnd symbol e n)
  · intro B C μ
    exact Module.End.mapsTo_maxGenEigenspace_of_comm
      (coefficientNormalizedPrincipalEnd_commute symbol hflat e he n C B) μ
  · intro B
    exact Module.End.iSup_maxGenEigenspace_eq_top
      (coefficientNormalizedPrincipalEnd symbol e n B)

/-- The finite type of nonzero joint generalized eigencharacters. -/
@[reducible] noncomputable def normalizedPrincipalJointCharacterFintype
    (symbol : ℕ → g → Matrix ι ι K)
    (hflat : MatrixCoefficientPrincipalSymbolFlat symbol)
    (e : g) (he : ∀ n, (symbol n e).det ≠ 0)
    (n : ℕ) :
    Fintype {χ : g → K //
      normalizedPrincipalJointMaxGenEigenspace symbol e n χ ≠ ⊥} :=
  (normalizedPrincipalJointMaxGenEigenspace_iSupIndep symbol hflat e he n).fintypeNeBotOfFiniteDimensional

omit [IsAlgClosed K] in
/-- A rank-`r` regular flat tower has at most `r` nonzero joint generalized eigencharacters. -/
theorem normalizedPrincipalJointCharacter_card_le_rank
    (symbol : ℕ → g → Matrix ι ι K)
    (hflat : MatrixCoefficientPrincipalSymbolFlat symbol)
    (e : g) (he : ∀ n, (symbol n e).det ≠ 0)
    (n : ℕ) :
    letI := normalizedPrincipalJointCharacterFintype symbol hflat e he n
    Fintype.card {χ : g → K //
      normalizedPrincipalJointMaxGenEigenspace symbol e n χ ≠ ⊥} ≤ Fintype.card ι := by
  letI := normalizedPrincipalJointCharacterFintype symbol hflat e he n
  simpa [Module.finrank_fintype_fun_eq_card] using
    (normalizedPrincipalJointMaxGenEigenspace_iSupIndep symbol hflat e he n).subtype_ne_bot_le_finrank

/-! ## Linearity of the joint characters -/

variable {V : Type*} [AddCommGroup V] [Module K V]
variable {h : Type*} [AddCommGroup h] [Module K h]

/-- A nonzero joint generalized eigencharacter of a commuting linear family is automatically a
linear functional on the parameter space. -/
def jointGeneralizedEigencharacterLinearMap
    (f : h →ₗ[K] Module.End K V) (χ : h → K)
    (hne : (⨅ A : h, (f A).maxGenEigenspace (χ A)) ≠ ⊥)
    (hcomm : ∀ A B, Commute (f A) (f B)) : h →ₗ[K] K where
  toFun := χ
  map_add' A B :=
    Module.End.map_add_of_iInf_genEigenspace_ne_bot_of_commute
      f χ ⊤ hne hcomm A B
  map_smul' t A :=
    Module.End.map_smul_of_iInf_genEigenspace_ne_bot
      f χ ⊤ hne t A

omit [IsAlgClosed K] in
@[simp]
theorem jointGeneralizedEigencharacterLinearMap_apply
    (f : h →ₗ[K] Module.End K V) (χ : h → K)
    (hne : (⨅ A : h, (f A).maxGenEigenspace (χ A)) ≠ ⊥)
    (hcomm : ∀ A B, Commute (f A) (f B)) (A : h) :
    jointGeneralizedEigencharacterLinearMap f χ hne hcomm A = χ A :=
  rfl

/-- The normalized endomorphism pencil associated to a linear matrix symbol. -/
def coefficientNormalizedPrincipalEndLinear
    (S : h →ₗ[K] Matrix ι ι K) (e : h) :
    h →ₗ[K] Module.End K (ι → K) :=
  Matrix.toLin'.toLinearMap.comp <|
    (LinearMap.mulLeft K (S e)⁻¹).comp S

omit [IsAlgClosed K] in
@[simp]
theorem coefficientNormalizedPrincipalEndLinear_apply
    (S : h →ₗ[K] Matrix ι ι K) (e A : h) :
    coefficientNormalizedPrincipalEndLinear S e A =
      Matrix.toLin' ((S e)⁻¹ * S A) :=
  rfl

/-- In a flat tower with a linear symbol layer, every nonzero joint generalized eigencharacter is
represented by an actual linear functional on law space. -/
def coefficientNormalizedPrincipalJointCharacterLinearMap
    (symbol : ℕ → h → Matrix ι ι K)
    (hflat : MatrixCoefficientPrincipalSymbolFlat symbol)
    (e : h) (he : ∀ n, (symbol n e).det ≠ 0)
    (n : ℕ) (S : h →ₗ[K] Matrix ι ι K)
    (hS : ∀ A, symbol n A = S A)
    (χ : h → K)
    (hne : normalizedPrincipalJointMaxGenEigenspace symbol e n χ ≠ ⊥) :
    h →ₗ[K] K := by
  have hend : ∀ A,
      coefficientNormalizedPrincipalEnd symbol e n A =
        coefficientNormalizedPrincipalEndLinear S e A := by
    intro A
    simp only [coefficientNormalizedPrincipalEnd,
      coefficientNormalizedPrincipalEndLinear_apply,
      coefficientNormalizedMatrixPrincipalSymbol]
    rw [hS e, hS A]
  apply jointGeneralizedEigencharacterLinearMap
    (coefficientNormalizedPrincipalEndLinear S e) χ
  · simpa only [normalizedPrincipalJointMaxGenEigenspace, ← hend] using hne
  · intro A B
    rw [← hend A, ← hend B]
    exact coefficientNormalizedPrincipalEnd_commute symbol hflat e he n A B

omit [IsAlgClosed K] in
@[simp]
theorem coefficientNormalizedPrincipalJointCharacterLinearMap_apply
    (symbol : ℕ → h → Matrix ι ι K)
    (hflat : MatrixCoefficientPrincipalSymbolFlat symbol)
    (e : h) (he : ∀ n, (symbol n e).det ≠ 0)
    (n : ℕ) (S : h →ₗ[K] Matrix ι ι K)
    (hS : ∀ A, symbol n A = S A)
    (χ : h → K)
    (hne : normalizedPrincipalJointMaxGenEigenspace symbol e n χ ≠ ⊥)
    (A : h) :
    coefficientNormalizedPrincipalJointCharacterLinearMap
      symbol hflat e he n S hS χ hne A = χ A :=
  rfl

end

end GaloisForLFunctions.HTGeometry
