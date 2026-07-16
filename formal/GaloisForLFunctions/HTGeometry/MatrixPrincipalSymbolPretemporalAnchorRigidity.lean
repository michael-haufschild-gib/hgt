import GaloisForLFunctions.HTGeometry.MatrixPrincipalSymbolDerivationLawHorizon

/-!
# Pretemporal anchor rigidity

Before a selected derivation has acted, its zeroth jet is the observable itself and is therefore
independent of the selected law.  This elementary anchor has a strong consequence that is invisible
in a symbol-only treatment.

If all selected-law jet packets are expressed over one algebraically independent ancestral packet,
their zeroth principal symbols coincide.  Coefficient flatness and one regular law then propagate
this equality through every layer.  Hence an honest regular flat selected-derivation tower has no
law-space dependence horizon at all.

In particular, requiring the zeroth symbol itself to be linear in law space is incompatible with
regularity (for a nonempty principal fibre).  Any nontrivial pretemporal horizon must therefore
enter through curvature, a law-dependent source, loss of regularity, or a different connection law.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open Set

variable {k K L h ι : Type*} [Field k] [Field K] [Field L]
  [Algebra k L] [Algebra K L] [Fintype ι]

/-- Algebraically independent coordinates faithfully detect a finite coefficient matrix. -/
theorem matrixLinearForms_injective_of_algebraicIndependent
    (x : ι → L) (hx : AlgebraicIndependent K x)
    {M N : Matrix ι ι K}
    (hMN : matrixLinearForms M x = matrixLinearForms N x) :
    M = N := by
  have hli : LinearIndependent K x := hx.linearIndependent
  ext i j
  have hrow : M.row i = N.row i := by
    apply hli.fintypeLinearCombination_injective
    have hi := congrFun hMN i
    simpa [Fintype.linearCombination_apply, matrixLinearForms,
      Algebra.smul_def] using hi
  exact congrFun hrow j

/-- The law-independent zeroth jet forces equality of all zeroth principal symbols. -/
theorem selectedDerivation_lowerLaw_zeroSymbol_constant
    (source : ℕ → ι → L) (observable : ι → L)
    (law : h → Derivation k L L)
    (symbol : ℕ → h → Matrix ι ι K)
    (hlaw : ∀ A, MatrixPrincipalLowerLaw source
      (fun n i ↦ selectedDerivationJet (law A) n (observable i))
      (fun n ↦ symbol n A))
    (hsource : AlgebraicIndependent K
      (fun p : ℕ × ι ↦ source p.1 p.2)) :
    ∀ A B, symbol 0 A = symbol 0 B := by
  intro A B
  obtain ⟨RA, hRA, hpacketA⟩ := hlaw A 1
  obtain ⟨RB, hRB, hpacketB⟩ := hlaw B 1
  have hRAzero : RA = 0 := by
    ext p q
    exact hRA p q (by omega)
  have hRBzero : RB = 0 := by
    ext p q
    exact hRB p q (by omega)
  let includeZero : Fin 1 × ι → ℕ × ι := fun p ↦ (0, p.2)
  have hincludeZero : Function.Injective includeZero := by
    rintro ⟨n, i⟩ ⟨m, j⟩ hij
    apply Prod.ext
    · exact Subsingleton.elim _ _
    · exact congrArg (fun z : ℕ × ι ↦ z.2) hij
  have hsourceZero : AlgebraicIndependent K
      (fun p : Fin 1 × ι ↦ source 0 p.2) := by
    simpa [includeZero, Function.comp_def] using
      hsource.comp includeZero hincludeZero
  have hforms :
      matrixLinearForms
          (matrixPrincipalBlockDiagonal (fun n : Fin 1 ↦ symbol n A))
          (fun p : Fin 1 × ι ↦ source 0 p.2) =
        matrixLinearForms
          (matrixPrincipalBlockDiagonal (fun n : Fin 1 ↦ symbol n B))
          (fun p : Fin 1 × ι ↦ source 0 p.2) := by
    rw [hRAzero, zero_add] at hpacketA
    rw [hRBzero, zero_add] at hpacketB
    have htarget :
        (fun p : Fin 1 × ι ↦
            selectedDerivationJet (law A) p.1 (observable p.2)) =
          (fun p : Fin 1 × ι ↦
            selectedDerivationJet (law B) p.1 (observable p.2)) := by
      funext p
      have hp : p.1 = 0 := Subsingleton.elim _ _
      simp [hp, selectedDerivationJet]
    simpa using hpacketA.symm.trans (htarget.trans hpacketB)
  have hblock :
      matrixPrincipalBlockDiagonal (fun n : Fin 1 ↦ symbol n A) =
        matrixPrincipalBlockDiagonal (fun n : Fin 1 ↦ symbol n B) :=
    matrixLinearForms_injective_of_algebraicIndependent
      (fun p : Fin 1 × ι ↦ source 0 p.2) hsourceZero hforms
  ext i j
  have hij := congrFun (congrFun hblock (⟨0, by omega⟩, i)) (⟨0, by omega⟩, j)
  simpa [matrixPrincipalBlockDiagonal] using hij

variable [DecidableEq ι]

/-- A regular coefficient-flat tower whose zeroth symbol is law-independent is law-independent
at every principal layer. -/
theorem matrixCoefficientPrincipalSymbol_constant_of_zeroSymbol_constant
    (symbol : ℕ → h → Matrix ι ι K)
    (hflat : MatrixCoefficientPrincipalSymbolFlat symbol)
    (hzero : ∀ A B, symbol 0 A = symbol 0 B)
    (e : h) (he : ∀ n, (symbol n e).det ≠ 0) :
    ∀ n A, symbol n A = symbol n e := by
  intro n
  induction n with
  | zero =>
      intro A
      exact hzero A e
  | succ n ih =>
      intro A
      have hcross := hflat n A e
      rw [ih A] at hcross
      have hunit : IsUnit (symbol n e).det := isUnit_iff_ne_zero.mpr (he n)
      calc
        symbol (n + 1) A =
            (symbol n e)⁻¹ * (symbol n e * symbol (n + 1) A) := by
          symm
          exact Matrix.nonsing_inv_mul_cancel_left _ _ hunit
        _ = (symbol n e)⁻¹ * (symbol n e * symbol (n + 1) e) := by
          rw [hcross]
        _ = symbol (n + 1) e :=
          Matrix.nonsing_inv_mul_cancel_left _ _ hunit

/-- **Pretemporal no-horizon theorem.**  A common algebraically independent source, honest
selected-derivation jets, coefficient flatness, and one regular law force differential algebraic
independence for every law.  The varying-law dependence spectrum is empty. -/
theorem derivationLawDependentSet_eq_empty_of_pretemporalAnchor
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
    derivationLawDependentSet (K := K) law observable = ∅ := by
  have hzero := selectedDerivation_lowerLaw_zeroSymbol_constant
    source observable law symbol hlaw hsource
  have hconstant := matrixCoefficientPrincipalSymbol_constant_of_zeroSymbol_constant
    symbol hflat hzero e he
  ext A
  change (¬ DerivationIndependentOver K (law A) observable) ↔ False
  have hindependent : DerivationIndependentOver K (law A) observable :=
    (derivationPrincipalLowerLaw_independent_iff
      source observable (law A) (fun n ↦ symbol n A) (hlaw A) hsource).2
        (fun n ↦ by simpa [hconstant n A] using he n)
  exact ⟨fun hnot ↦ hnot hindependent, False.elim⟩

/-- **Hypertranscendence-discriminant curvature theorem.**  In an honest regular common-source
principal realization, the existence of even one differentially dependent law forces nonzero
coefficient curvature at some pair of laws and some layer. -/
theorem exists_matrixCoefficientPrincipalCurvature_ne_zero_of_dependentLaw
    (source : ℕ → ι → L) (observable : ι → L)
    (law : h → Derivation k L L)
    (symbol : ℕ → h → Matrix ι ι K)
    (e : h) (he : ∀ n, (symbol n e).det ≠ 0)
    (hlaw : ∀ A, MatrixPrincipalLowerLaw source
      (fun n i ↦ selectedDerivationJet (law A) n (observable i))
      (fun n ↦ symbol n A))
    (hsource : AlgebraicIndependent K
      (fun p : ℕ × ι ↦ source p.1 p.2))
    (hdependent : ∃ A, ¬ DerivationIndependentOver K (law A) observable) :
    ∃ n A B, matrixCoefficientPrincipalCurvature symbol n A B ≠ 0 := by
  have hnflat : ¬ MatrixCoefficientPrincipalSymbolFlat symbol := by
    intro hflat
    have hempty := derivationLawDependentSet_eq_empty_of_pretemporalAnchor
      source observable law symbol hflat e he hlaw hsource
    obtain ⟨A, hA⟩ := hdependent
    have : A ∈ derivationLawDependentSet (K := K) law observable := hA
    rw [hempty] at this
    exact this
  rw [matrixCoefficientPrincipalSymbolFlat_iff_curvature_zero] at hnflat
  push Not at hnflat
  exact hnflat

variable [Nonempty ι] [AddCommGroup h] [Module K h]

/-- A law-linear zeroth symbol is incompatible with an honest regular selected-derivation lower
law.  This pinpoints why a hyperplane theorem imposed at jet level zero is vacuous. -/
theorem not_regular_linear_zeroSymbol_of_selectedDerivation_lowerLaw
    (source : ℕ → ι → L) (observable : ι → L)
    (law : h → Derivation k L L)
    (symbol : ℕ → h → Matrix ι ι K)
    (hlaw : ∀ A, MatrixPrincipalLowerLaw source
      (fun n i ↦ selectedDerivationJet (law A) n (observable i))
      (fun n ↦ symbol n A))
    (hsource : AlgebraicIndependent K
      (fun p : ℕ × ι ↦ source p.1 p.2))
    (S : h →ₗ[K] Matrix ι ι K)
    (hS : ∀ A, symbol 0 A = S A) :
    ¬ ∃ e : h, (symbol 0 e).det ≠ 0 := by
  intro hex
  obtain ⟨e, he⟩ := hex
  have hzero := selectedDerivation_lowerLaw_zeroSymbol_constant
    source observable law symbol hlaw hsource e 0
  have hsymbolZero : symbol 0 e = 0 := by
    rw [hzero, hS, map_zero]
  rw [hsymbolZero] at he
  exact he (Matrix.det_zero inferInstance)

end

end GaloisForLFunctions.HTGeometry
