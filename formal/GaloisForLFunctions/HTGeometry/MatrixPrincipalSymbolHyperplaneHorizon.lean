import GaloisForLFunctions.HTGeometry.MatrixPrincipalSymbolAbelianSpectrum
import Mathlib.LinearAlgebra.Eigenspace.Zero

/-!
# Hyperplane collapse of a regular flat principal horizon

For a regular coefficient-flat finite-rank tower, singularity of a normalized principal symbol is
equivalent to the vanishing of one of its nonzero joint generalized eigencharacters.  When the
symbol depends linearly on law space, those characters are linear functionals.  Thus the complete
determinant horizon is not an arbitrary determinantal hypersurface: it is a finite union of at most
the fiber rank many hyperplanes.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open Submodule

variable {K g ι : Type*} [Field K] [IsAlgClosed K]
  [Fintype ι] [DecidableEq ι]

omit [IsAlgClosed K] in
/-- A maximal generalized eigenspace is nonzero exactly when its scalar is an eigenvalue. -/
theorem maxGenEigenspace_ne_bot_iff_hasEigenvalue
    {V : Type*} [AddCommGroup V] [Module K V]
    (f : Module.End K V) (μ : K) :
    f.maxGenEigenspace μ ≠ ⊥ ↔ f.HasEigenvalue μ := by
  constructor
  · intro hmax
    obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff _).mp hmax
    rw [Module.End.mem_maxGenEigenspace] at hx
    obtain ⟨k, hk⟩ := hx
    apply Module.End.hasEigenvalue_of_hasGenEigenvalue (k := k)
    rw [Module.End.hasGenEigenvalue_iff, Submodule.ne_bot_iff]
    refine ⟨x, ?_, hx0⟩
    rw [Module.End.mem_genEigenspace_nat, LinearMap.mem_ker]
    exact hk
  · intro heig hmax
    have hle := Module.End.eigenspace_le_maxGenEigenspace (f := f) (μ := μ)
    rw [hmax] at hle
    exact heig (eq_bot_iff.mpr hle)

/-- **Spectral horizon criterion.**  A normalized symbol is singular exactly when some nonzero
joint generalized eigencharacter vanishes on the selected law. -/
theorem coefficientNormalizedMatrixPrincipalSymbol_det_eq_zero_iff_exists_jointCharacter
    (symbol : ℕ → g → Matrix ι ι K)
    (hflat : MatrixCoefficientPrincipalSymbolFlat symbol)
    (e : g) (he : ∀ n, (symbol n e).det ≠ 0)
    (n : ℕ) (A : g) :
    (coefficientNormalizedMatrixPrincipalSymbol symbol e n A).det = 0 ↔
      ∃ χ : g → K,
        normalizedPrincipalJointMaxGenEigenspace symbol e n χ ≠ ⊥ ∧ χ A = 0 := by
  let fA := coefficientNormalizedPrincipalEnd symbol e n A
  have hdet :
      LinearMap.det fA =
        (coefficientNormalizedMatrixPrincipalSymbol symbol e n A).det := by
    exact LinearMap.det_toLin' _
  constructor
  · intro hzero
    have heig : fA.HasEigenvalue 0 :=
      ((LinearMap.hasEigenvalue_zero_tfae fA).out 3 0).mp (hdet.trans hzero)
    have hmax : fA.maxGenEigenspace 0 ≠ ⊥ :=
      (maxGenEigenspace_ne_bot_iff_hasEigenvalue fA 0).2 heig
    rw [← coefficientNormalizedPrincipalEnd_jointFiber_eq symbol hflat e he n A 0] at hmax
    by_contra hex
    have hall : ∀ χ : g → K, χ A = 0 →
        normalizedPrincipalJointMaxGenEigenspace symbol e n χ = ⊥ := by
      intro χ hχ
      by_contra hne
      exact hex ⟨χ, hne, hχ⟩
    apply hmax
    apply iSup_eq_bot.mpr
    intro χ
    apply iSup_eq_bot.mpr
    intro hχ
    exact hall χ hχ
  · rintro ⟨χ, hχ, hχA⟩
    have hle :
        normalizedPrincipalJointMaxGenEigenspace symbol e n χ ≤
          fA.maxGenEigenspace 0 := by
      change normalizedPrincipalJointMaxGenEigenspace symbol e n χ ≤
        (coefficientNormalizedPrincipalEnd symbol e n A).maxGenEigenspace 0
      simpa [normalizedPrincipalJointMaxGenEigenspace, hχA] using
        (iInf_le
          (fun B : g ↦
            (coefficientNormalizedPrincipalEnd symbol e n B).maxGenEigenspace (χ B)) A)
    have hmax : fA.maxGenEigenspace 0 ≠ ⊥ := by
      intro hbot
      apply hχ
      apply eq_bot_iff.mpr
      simpa [hbot] using hle
    have heig : fA.HasEigenvalue 0 :=
      (maxGenEigenspace_ne_bot_iff_hasEigenvalue fA 0).1 hmax
    have : LinearMap.det fA = 0 :=
      ((LinearMap.hasEigenvalue_zero_tfae fA).out 0 3).mp heig
    exact hdet.symm.trans this

/-- For a linear symbol layer, the spectral horizon criterion is literally a union of kernels of
linear functionals on law space. -/
theorem coefficientNormalizedMatrixPrincipalSymbol_det_eq_zero_iff_exists_linearCharacter
    {h : Type*} [AddCommGroup h] [Module K h]
    (symbol : ℕ → h → Matrix ι ι K)
    (hflat : MatrixCoefficientPrincipalSymbolFlat symbol)
    (e : h) (he : ∀ n, (symbol n e).det ≠ 0)
    (n : ℕ) (S : h →ₗ[K] Matrix ι ι K)
    (hS : ∀ A, symbol n A = S A) (A : h) :
    (coefficientNormalizedMatrixPrincipalSymbol symbol e n A).det = 0 ↔
      ∃ (χ : h → K)
          (hne : normalizedPrincipalJointMaxGenEigenspace symbol e n χ ≠ ⊥),
        coefficientNormalizedPrincipalJointCharacterLinearMap
          symbol hflat e he n S hS χ hne A = 0 := by
  constructor
  · intro hzero
    obtain ⟨χ, hne, hχ⟩ :=
      (coefficientNormalizedMatrixPrincipalSymbol_det_eq_zero_iff_exists_jointCharacter
        symbol hflat e he n A).1 hzero
    exact ⟨χ, hne, by simpa using hχ⟩
  · rintro ⟨χ, hne, hχ⟩
    apply (coefficientNormalizedMatrixPrincipalSymbol_det_eq_zero_iff_exists_jointCharacter
      symbol hflat e he n A).2
    exact ⟨χ, hne, by simpa using hχ⟩

/-- A supported joint character cannot be the zero functional: the regular reference law has an
invertible normalized symbol. -/
theorem coefficientNormalizedPrincipalJointCharacterLinearMap_ne_zero
    {h : Type*} [AddCommGroup h] [Module K h]
    (symbol : ℕ → h → Matrix ι ι K)
    (hflat : MatrixCoefficientPrincipalSymbolFlat symbol)
    (e : h) (he : ∀ n, (symbol n e).det ≠ 0)
    (n : ℕ) (S : h →ₗ[K] Matrix ι ι K)
    (hS : ∀ A, symbol n A = S A)
    (χ : h → K)
    (hne : normalizedPrincipalJointMaxGenEigenspace symbol e n χ ≠ ⊥) :
    coefficientNormalizedPrincipalJointCharacterLinearMap
      symbol hflat e he n S hS χ hne ≠ 0 := by
  intro hzero
  have hχe : χ e = 0 := by
    rw [← coefficientNormalizedPrincipalJointCharacterLinearMap_apply
      symbol hflat e he n S hS χ hne e, hzero]
    rfl
  have hdet :=
    (coefficientNormalizedMatrixPrincipalSymbol_det_eq_zero_iff_exists_jointCharacter
      symbol hflat e he n e).2 ⟨χ, hne, hχe⟩
  have hunit : IsUnit (symbol n e).det := isUnit_iff_ne_zero.mpr (he n)
  rw [coefficientNormalizedMatrixPrincipalSymbol,
    Matrix.nonsing_inv_mul _ hunit, Matrix.det_one] at hdet
  exact one_ne_zero hdet

/-- **General principal-symbol hyperplane theorem.**  At a regular coefficient-flat linear layer,
the original determinant horizon is exactly the union of kernels of the supported joint linear
characters. -/
theorem matrixPrincipalSymbol_det_eq_zero_iff_exists_linearCharacter
    {h : Type*} [AddCommGroup h] [Module K h]
    (symbol : ℕ → h → Matrix ι ι K)
    (hflat : MatrixCoefficientPrincipalSymbolFlat symbol)
    (e : h) (he : ∀ n, (symbol n e).det ≠ 0)
    (n : ℕ) (S : h →ₗ[K] Matrix ι ι K)
    (hS : ∀ A, symbol n A = S A) (A : h) :
    (symbol n A).det = 0 ↔
      ∃ (χ : h → K)
          (hne : normalizedPrincipalJointMaxGenEigenspace symbol e n χ ≠ ⊥),
        coefficientNormalizedPrincipalJointCharacterLinearMap
          symbol hflat e he n S hS χ hne A = 0 := by
  have hSe : (S e).det ≠ 0 := by
    rw [← hS e]
    exact he n
  have hinv : ((S e)⁻¹).det ≠ 0 :=
    (Matrix.isUnit_nonsing_inv_det (S e) (isUnit_iff_ne_zero.mpr hSe)).ne_zero
  have hnormalize :
      (coefficientNormalizedMatrixPrincipalSymbol symbol e n A).det = 0 ↔
        (symbol n A).det = 0 := by
    rw [coefficientNormalizedMatrixPrincipalSymbol, hS e, Matrix.det_mul]
    simp only [mul_eq_zero, hinv, false_or]
  rw [← hnormalize]
  exact coefficientNormalizedMatrixPrincipalSymbol_det_eq_zero_iff_exists_linearCharacter
    symbol hflat e he n S hS A

/-- **Finite hyperplane-collapse theorem.**  The complete singular locus of a regular flat linear
principal-symbol layer is a union of kernels of a finite type of linear characters, and the number
of nonzero joint characters is at most the fiber rank. -/
theorem regularFlatLinearPrincipalSymbol_hyperplaneHorizon
    {h : Type*} [AddCommGroup h] [Module K h]
    (symbol : ℕ → h → Matrix ι ι K)
    (hflat : MatrixCoefficientPrincipalSymbolFlat symbol)
    (e : h) (he : ∀ n, (symbol n e).det ≠ 0)
    (n : ℕ) (S : h →ₗ[K] Matrix ι ι K)
    (hS : ∀ A, symbol n A = S A) :
    letI := normalizedPrincipalJointCharacterFintype symbol hflat e he n
    (∀ A : h, (symbol n A).det = 0 ↔
      ∃ χ : { χ : h → K //
          normalizedPrincipalJointMaxGenEigenspace symbol e n χ ≠ ⊥ },
        coefficientNormalizedPrincipalJointCharacterLinearMap
          symbol hflat e he n S hS χ.1 χ.2 A = 0) ∧
      Fintype.card { χ : h → K //
          normalizedPrincipalJointMaxGenEigenspace symbol e n χ ≠ ⊥ } ≤
        Fintype.card ι := by
  letI := normalizedPrincipalJointCharacterFintype symbol hflat e he n
  constructor
  · intro A
    constructor
    · intro hzero
      obtain ⟨χ, hne, hχ⟩ :=
        (matrixPrincipalSymbol_det_eq_zero_iff_exists_linearCharacter
          symbol hflat e he n S hS A).1 hzero
      exact ⟨⟨χ, hne⟩, hχ⟩
    · rintro ⟨χ, hχ⟩
      exact (matrixPrincipalSymbol_det_eq_zero_iff_exists_linearCharacter
        symbol hflat e he n S hS A).2 ⟨χ.1, χ.2, hχ⟩
  · exact normalizedPrincipalJointCharacter_card_le_rank symbol hflat e he n

/-- **Horizon-capacity bound.**  If a finite family of singular laws is separated by every
supported joint character (one character cannot vanish on two different laws), then the number of
laws is at most the fiber rank. -/
theorem regularFlatLinearPrincipalSymbol_horizonCapacity
    {h I : Type*} [AddCommGroup h] [Module K h] [Fintype I]
    (symbol : ℕ → h → Matrix ι ι K)
    (hflat : MatrixCoefficientPrincipalSymbolFlat symbol)
    (e : h) (he : ∀ n, (symbol n e).det ≠ 0)
    (n : ℕ) (S : h →ₗ[K] Matrix ι ι K)
    (hS : ∀ A, symbol n A = S A)
    (law : I → h)
    (hsingular : ∀ i, (symbol n (law i)).det = 0)
    (hseparate : ∀
      (χ : { χ : h → K //
        normalizedPrincipalJointMaxGenEigenspace symbol e n χ ≠ ⊥ })
      (i j : I),
      coefficientNormalizedPrincipalJointCharacterLinearMap
          symbol hflat e he n S hS χ.1 χ.2 (law i) = 0 →
      coefficientNormalizedPrincipalJointCharacterLinearMap
          symbol hflat e he n S hS χ.1 χ.2 (law j) = 0 →
      i = j) :
    Fintype.card I ≤ Fintype.card ι := by
  letI := normalizedPrincipalJointCharacterFintype symbol hflat e he n
  let C := { χ : h → K //
    normalizedPrincipalJointMaxGenEigenspace symbol e n χ ≠ ⊥ }
  have hexists (i : I) : ∃ χ : C,
      coefficientNormalizedPrincipalJointCharacterLinearMap
        symbol hflat e he n S hS χ.1 χ.2 (law i) = 0 := by
    obtain ⟨χ, hne, hχ⟩ :=
      (matrixPrincipalSymbol_det_eq_zero_iff_exists_linearCharacter
        symbol hflat e he n S hS (law i)).1 (hsingular i)
    exact ⟨⟨χ, hne⟩, hχ⟩
  let select : I → C := fun i ↦ Classical.choose (hexists i)
  have hselect (i : I) :
      coefficientNormalizedPrincipalJointCharacterLinearMap
        symbol hflat e he n S hS (select i).1 (select i).2 (law i) = 0 :=
    Classical.choose_spec (hexists i)
  have hinjective : Function.Injective select := by
    intro i j hij
    apply hseparate (select i) i j (hselect i)
    simpa [hij] using hselect j
  calc
    Fintype.card I ≤ Fintype.card C :=
      Fintype.card_le_of_injective select hinjective
    _ ≤ Fintype.card ι :=
      normalizedPrincipalJointCharacter_card_le_rank symbol hflat e he n

end

end GaloisForLFunctions.HTGeometry
