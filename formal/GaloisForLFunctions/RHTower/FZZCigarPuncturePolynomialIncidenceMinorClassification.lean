import GaloisForLFunctions.RHTower.FZZCigarPunctureRegularPolynomialPencilNoGo
import GaloisForLFunctions.HTGeometry.MvPolynomialMatrixRankDefect

/-!
# FZZ puncture polynomial-incidence minor classification

This file treats every finite polynomial interior equation and coupling constraint as one
rectangular polynomial incidence matrix.  A nonzero dark vector forces every column-maximal minor
to vanish at its energy.  Hardy packets then show that completeness for all positive real `XiC`
zeros makes every such minor vanish identically.

The converse is exact: identically vanishing maximal minors make the evaluated matrix noninjective
at every complex energy.  Hence a fixed finite polynomial incidence model that catches every Xi
zero cannot retain any spectral selectivity; its dark branch persists everywhere.

`[NEW] [SINGULAR-PENCIL RIGIDITY] [SPECTRAL SELECTIVITY COLLAPSE] [PAPER-PROVED] [LEAN-PROVED]`
-/

open Complex Polynomial

namespace RHTower

noncomputable section

/-- Entrywise evaluation of a rectangular complex polynomial incidence matrix. -/
def fzzPuncturePolynomialIncidenceEval
    {R N : ℕ} (A : Matrix (Fin R) (Fin N) (Polynomial ℂ)) (z : ℂ) :
    Matrix (Fin R) (Fin N) ℂ :=
  fun i j => (A i j).eval z

/-- A column-maximal minor of a rectangular polynomial incidence matrix. -/
def fzzPuncturePolynomialIncidenceMinor
    {R N : ℕ} (A : Matrix (Fin R) (Fin N) (Polynomial ℂ))
    (rows : Fin N → Fin R) : Polynomial ℂ :=
  (A.submatrix rows id).det

/-- Evaluation commutes with formation of a column-maximal incidence minor. -/
theorem eval_fzzPuncturePolynomialIncidenceMinor
    {R N : ℕ} (A : Matrix (Fin R) (Fin N) (Polynomial ℂ))
    (rows : Fin N → Fin R) (z : ℂ) :
    (fzzPuncturePolynomialIncidenceMinor A rows).eval z =
      ((fzzPuncturePolynomialIncidenceEval A z).submatrix rows id).det := by
  rw [fzzPuncturePolynomialIncidenceMinor]
  calc
    (A.submatrix rows id).det.eval z =
        (((A.submatrix rows id).map (Polynomial.evalRingHom z))).det :=
      (Polynomial.evalRingHom z).map_det (A.submatrix rows id)
    _ = ((fzzPuncturePolynomialIncidenceEval A z).submatrix rows id).det := rfl

/-- A nonzero vector satisfying every evaluated polynomial incidence row. -/
def FZZPuncturePolynomialIncidenceDarkMode
    {R N : ℕ} (A : Matrix (Fin R) (Fin N) (Polynomial ℂ)) (z : ℂ) : Prop :=
  ∃ x : Fin N → ℂ, x ≠ 0 ∧
    (fzzPuncturePolynomialIncidenceEval A z).mulVec x = 0

/-- A polynomial incidence dark mode is exactly failure of column injectivity. -/
theorem fzzPuncturePolynomialIncidenceDarkMode_iff_not_injective
    {R N : ℕ} {A : Matrix (Fin R) (Fin N) (Polynomial ℂ)} {z : ℂ} :
    FZZPuncturePolynomialIncidenceDarkMode A z ↔
      ¬ Function.Injective (fzzPuncturePolynomialIncidenceEval A z).mulVec := by
  constructor
  · rintro ⟨x, hx, hAx⟩ hinj
    apply hx
    apply hinj
    simpa using hAx
  · intro hnot
    rw [Function.not_injective_iff] at hnot
    obtain ⟨x, y, hxy, hne⟩ := hnot
    refine ⟨x - y, sub_ne_zero.mpr hne, ?_⟩
    rw [Matrix.mulVec_sub, hxy, sub_self]

/-- Every dark-mode energy is a root of every column-maximal minor. -/
theorem fzzPuncturePolynomialIncidenceDarkMode_isRoot_minor
    {R N : ℕ} {A : Matrix (Fin R) (Fin N) (Polynomial ℂ)} {z : ℂ}
    (hmode : FZZPuncturePolynomialIncidenceDarkMode A z)
    (rows : Fin N → Fin R) :
    (fzzPuncturePolynomialIncidenceMinor A rows).IsRoot z := by
  have hnot :=
    fzzPuncturePolynomialIncidenceDarkMode_iff_not_injective.mp hmode
  rw [GaloisForLFunctions.HTGeometry.matrix_mulVec_injective_iff_exists_submatrix_det_ne_zero]
    at hnot
  have hzero :
      ((fzzPuncturePolynomialIncidenceEval A z).submatrix rows id).det = 0 := by
    by_contra hne
    exact hnot ⟨rows, hne⟩
  rw [Polynomial.IsRoot, eval_fzzPuncturePolynomialIncidenceMinor]
  exact hzero

/-- Completeness of one finite polynomial incidence matrix for all positive real `XiC` zeros. -/
def FZZPuncturePolynomialIncidenceXiComplete
    {R N : ℕ} (A : Matrix (Fin R) (Fin N) (Polynomial ℂ)) : Prop :=
  ∀ E : ℝ, 0 < E → XiC (E : ℂ) = 0 →
    FZZPuncturePolynomialIncidenceDarkMode A (E : ℂ)

/-- A polynomial incidence matrix whose dark branch persists at every complex energy. -/
def FZZPuncturePolynomialIncidenceUniversallyDark
    {R N : ℕ} (A : Matrix (Fin R) (Fin N) (Polynomial ℂ)) : Prop :=
  ∀ z : ℂ, FZZPuncturePolynomialIncidenceDarkMode A z

/-- A nonzero maximal minor prevents Xi-completeness. -/
theorem not_fzzPuncturePolynomialIncidenceXiComplete_of_minor_ne_zero
    {R N : ℕ} (A : Matrix (Fin R) (Fin N) (Polynomial ℂ))
    (rows : Fin N → Fin R)
    (hminor : fzzPuncturePolynomialIncidenceMinor A rows ≠ 0) :
    ¬ FZZPuncturePolynomialIncidenceXiComplete A := by
  intro hcomplete
  let p := fzzPuncturePolynomialIncidenceMinor A rows
  let k : ℕ := p.natDegree + 1
  obtain ⟨E, hEpos, hEinj, hEzero⟩ :=
    exists_injective_positive_real_XiC_zero_packet k
  have hroot : ∀ i : Fin k, p.IsRoot (E i : ℂ) := by
    intro i
    exact fzzPuncturePolynomialIncidenceDarkMode_isRoot_minor
      (hcomplete (E i) (hEpos i) (hEzero i)) rows
  let f : Fin k → {z : ℂ // z ∈ p.roots.toFinset} := fun i =>
    ⟨(E i : ℂ), Multiset.mem_toFinset.mpr
      ((Polynomial.mem_roots hminor).mpr (hroot i))⟩
  have hf : Function.Injective f := by
    intro i j hij
    apply hEinj
    exact Complex.ofReal_injective (congrArg Subtype.val hij)
  have hcard := Fintype.card_le_of_injective f hf
  have htoFinset := Multiset.toFinset_card_le p.roots
  have hroots := Polynomial.card_roots' p
  simp only [Fintype.card_fin, Fintype.card_coe] at hcard
  dsimp [k] at hcard
  omega

/-- Xi-completeness forces every column-maximal minor to vanish identically. -/
theorem fzzPuncturePolynomialIncidence_minors_eq_zero_of_XiComplete
    {R N : ℕ} {A : Matrix (Fin R) (Fin N) (Polynomial ℂ)}
    (hcomplete : FZZPuncturePolynomialIncidenceXiComplete A) :
    ∀ rows : Fin N → Fin R,
      fzzPuncturePolynomialIncidenceMinor A rows = 0 := by
  intro rows
  by_contra hminor
  exact not_fzzPuncturePolynomialIncidenceXiComplete_of_minor_ne_zero
    A rows hminor hcomplete

/-- Vanishing of every maximal minor makes the dark branch persist at every energy. -/
theorem fzzPuncturePolynomialIncidence_universallyDark_of_minors_eq_zero
    {R N : ℕ} {A : Matrix (Fin R) (Fin N) (Polynomial ℂ)}
    (hminors : ∀ rows : Fin N → Fin R,
      fzzPuncturePolynomialIncidenceMinor A rows = 0) :
    FZZPuncturePolynomialIncidenceUniversallyDark A := by
  intro z
  rw [fzzPuncturePolynomialIncidenceDarkMode_iff_not_injective]
  rw [GaloisForLFunctions.HTGeometry.matrix_mulVec_injective_iff_exists_submatrix_det_ne_zero]
  push Not
  intro rows
  rw [← eval_fzzPuncturePolynomialIncidenceMinor, hminors rows]
  simp

/-- Universal darkness trivially supplies every positive Xi dark mode. -/
theorem fzzPuncturePolynomialIncidence_xiComplete_of_universallyDark
    {R N : ℕ} {A : Matrix (Fin R) (Fin N) (Polynomial ℂ)}
    (hdark : FZZPuncturePolynomialIncidenceUniversallyDark A) :
    FZZPuncturePolynomialIncidenceXiComplete A := by
  intro E _hE _hXi
  exact hdark (E : ℂ)

/-- Exact maximal-minor classification of finite polynomial Xi-completeness. -/
theorem fzzPuncturePolynomialIncidence_xiComplete_iff_minors_eq_zero
    {R N : ℕ} {A : Matrix (Fin R) (Fin N) (Polynomial ℂ)} :
    FZZPuncturePolynomialIncidenceXiComplete A ↔
      ∀ rows : Fin N → Fin R,
        fzzPuncturePolynomialIncidenceMinor A rows = 0 := by
  constructor
  · exact fzzPuncturePolynomialIncidence_minors_eq_zero_of_XiComplete
  · intro hminors
    exact fzzPuncturePolynomialIncidence_xiComplete_of_universallyDark
      (fzzPuncturePolynomialIncidence_universallyDark_of_minors_eq_zero hminors)

/-- Spectral selectivity collapse: Xi-completeness is exactly all-energy darkness. -/
theorem fzzPuncturePolynomialIncidence_xiComplete_iff_universallyDark
    {R N : ℕ} {A : Matrix (Fin R) (Fin N) (Polynomial ℂ)} :
    FZZPuncturePolynomialIncidenceXiComplete A ↔
      FZZPuncturePolynomialIncidenceUniversallyDark A := by
  constructor
  · intro hcomplete
    exact fzzPuncturePolynomialIncidence_universallyDark_of_minors_eq_zero
      (fzzPuncturePolynomialIncidence_minors_eq_zero_of_XiComplete hcomplete)
  · exact fzzPuncturePolynomialIncidence_xiComplete_of_universallyDark

end

end RHTower
