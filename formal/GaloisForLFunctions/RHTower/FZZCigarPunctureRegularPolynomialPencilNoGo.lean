import GaloisForLFunctions.RHTower.FZZCigarPunctureFiniteDimensionalBarePencilNoGo

/-!
# FZZ puncture regular polynomial-pencil no-go

This file permits arbitrary polynomial energy dependence in every entry of a fixed finite FZZ
interior pencil.  A nonzero dark vector makes the evaluated determinant vanish, so all mode
energies lie among roots of the determinant polynomial.  If that polynomial is nonzero, the mode
set is finite and an injective Hardy packet one larger than its degree gives an immediate
contradiction to Xi-completeness.

Thus any Xi-complete finite polynomial pencil must be singular in the algebraic sense
`det P = 0` identically.  This is the exact surviving boundary after regular polynomial energy
dependence is eliminated.

`[NEW] [REGULAR-PENCIL NO-GO] [SINGULAR BOUNDARY] [PAPER-PROVED] [LEAN-PROVED]`
-/

open Complex Polynomial

namespace RHTower

noncomputable section

/-- Entrywise evaluation of a complex polynomial matrix pencil. -/
def fzzPuncturePolynomialPencilEval
    {N : ℕ} (P : Matrix (Fin N) (Fin N) (Polynomial ℂ)) (z : ℂ) :
    Matrix (Fin N) (Fin N) ℂ :=
  (Polynomial.evalRingHom z).mapMatrix P

/-- Nonzero evaluated-pencil kernel vector lying in a fixed finite coupling kernel. -/
def FZZPunctureFinitePolynomialDarkMode
    {N Q : ℕ} (P : Matrix (Fin N) (Fin N) (Polynomial ℂ))
    (K : (Fin N → ℂ) →ₗ[ℂ] (Fin Q → ℂ)) (E : ℝ) : Prop :=
  ∃ x : Fin N → ℂ, x ≠ 0 ∧
    (fzzPuncturePolynomialPencilEval P (E : ℂ)).mulVec x = 0 ∧ K x = 0

/-- Every finite polynomial dark-mode energy is a determinant-polynomial root. -/
theorem fzzPunctureFinitePolynomialDarkMode_isRoot_det
    {N Q : ℕ} {P : Matrix (Fin N) (Fin N) (Polynomial ℂ)}
    {K : (Fin N → ℂ) →ₗ[ℂ] (Fin Q → ℂ)} {E : ℝ}
    (hmode : FZZPunctureFinitePolynomialDarkMode P K E) :
    P.det.IsRoot (E : ℂ) := by
  obtain ⟨x, hx, hPx, _hKx⟩ := hmode
  have hcoord : ∃ i : Fin N, x i ≠ 0 := by
    by_contra h
    push Not at h
    apply hx
    funext i
    exact h i
  obtain ⟨i, hi⟩ := hcoord
  have hdet : (fzzPuncturePolynomialPencilEval P (E : ℂ)).det = 0 :=
    Matrix.det_eq_zero_of_mulVec_eq_zero_of_mem_nonZeroDivisors hPx
      (mem_nonZeroDivisors_iff_ne_zero.mpr hi)
  rw [Polynomial.IsRoot]
  calc
    P.det.eval (E : ℂ) =
        ((Polynomial.evalRingHom (E : ℂ)).mapMatrix P).det :=
      (Polynomial.evalRingHom (E : ℂ)).map_det P
    _ = 0 := hdet

/-- A regular finite polynomial pencil has only finitely many real dark-mode energies. -/
theorem finite_fzzPunctureFinitePolynomialDarkMode_of_det_ne_zero
    {N Q : ℕ} {P : Matrix (Fin N) (Fin N) (Polynomial ℂ)}
    {K : (Fin N → ℂ) →ₗ[ℂ] (Fin Q → ℂ)} (hdet : P.det ≠ 0) :
    {E : ℝ | FZZPunctureFinitePolynomialDarkMode P K E}.Finite := by
  have hfinite : {z : ℂ | P.det.IsRoot z}.Finite :=
    Polynomial.finite_setOf_isRoot hdet
  have hreal : {E : ℝ | P.det.IsRoot (E : ℂ)}.Finite :=
    Set.Finite.preimage Complex.ofReal_injective.injOn hfinite
  exact hreal.subset fun E hmode =>
    fzzPunctureFinitePolynomialDarkMode_isRoot_det hmode

/-- Proposed completeness of one finite polynomial pencil for all positive real `XiC` zeros. -/
def FZZPunctureFinitePolynomialPencilXiComplete
    {N Q : ℕ} (P : Matrix (Fin N) (Fin N) (Polynomial ℂ))
    (K : (Fin N → ℂ) →ₗ[ℂ] (Fin Q → ℂ)) : Prop :=
  ∀ E : ℝ, 0 < E → XiC (E : ℂ) = 0 →
    FZZPunctureFinitePolynomialDarkMode P K E

/-- No regular finite polynomial pencil can be Xi-complete. -/
theorem not_fzzPunctureFinitePolynomialPencilXiComplete_of_det_ne_zero
    {N Q : ℕ} (P : Matrix (Fin N) (Fin N) (Polynomial ℂ))
    (K : (Fin N → ℂ) →ₗ[ℂ] (Fin Q → ℂ)) (hdet : P.det ≠ 0) :
    ¬ FZZPunctureFinitePolynomialPencilXiComplete P K := by
  intro hcomplete
  let k : ℕ := P.det.natDegree + 1
  obtain ⟨E, hEpos, hEinj, hEzero⟩ :=
    exists_injective_positive_real_XiC_zero_packet k
  have hroot : ∀ i : Fin k, P.det.IsRoot (E i : ℂ) := by
    intro i
    exact fzzPunctureFinitePolynomialDarkMode_isRoot_det
      (hcomplete (E i) (hEpos i) (hEzero i))
  let f : Fin k → {z : ℂ // z ∈ P.det.roots.toFinset} := fun i =>
    ⟨(E i : ℂ), Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hdet).mpr (hroot i))⟩
  have hf : Function.Injective f := by
    intro i j hij
    apply hEinj
    exact Complex.ofReal_injective (congrArg Subtype.val hij)
  have hcard := Fintype.card_le_of_injective f hf
  have htoFinset := Multiset.toFinset_card_le P.det.roots
  have hroots := Polynomial.card_roots' P.det
  simp only [Fintype.card_fin, Fintype.card_coe] at hcard
  dsimp [k] at hcard
  omega

/-- Xi-completeness forces the determinant polynomial to vanish identically. -/
theorem fzzPunctureFinitePolynomialPencil_det_eq_zero_of_XiComplete
    {N Q : ℕ} {P : Matrix (Fin N) (Fin N) (Polynomial ℂ)}
    {K : (Fin N → ℂ) →ₗ[ℂ] (Fin Q → ℂ)}
    (hcomplete : FZZPunctureFinitePolynomialPencilXiComplete P K) :
    P.det = 0 := by
  by_contra hdet
  exact not_fzzPunctureFinitePolynomialPencilXiComplete_of_det_ne_zero
    P K hdet hcomplete

end

end RHTower
