import GaloisForLFunctions.HTGeometry.LocalLogarithmRigidity

/-!
# The folded generator and its branch ledger

Every real number has a unique representative in the half-open window `(-π, π]` modulo `2π`, and the
displacement is `2π` times an explicit integer.  Folding the energies of a static orbit through that
window produces a Hermitian generator with spectrum inside the window which exponentiates to the same
unitary, and the discarded integers form the branch ledger:

`F(t) = tH - 2π N(t)`,  `e^{-iF(t)} = U(t)`,  `spec F(t) ⊂ (-π, π]`.

The window is half-open on the right, so the wrap is the negation of the symmetric gap, whose own
window is half-open on the left.
-/

open Finset

namespace GaloisForLFunctions.HTGeometry

/-! ## The half-open phase window -/

/-- The symmetric gap lands in `[-π, π)`. -/
theorem phaseGap_zero_mem (y : ℝ) : -Real.pi ≤ phaseGap y 0 ∧ phaseGap y 0 < Real.pi := by
  have hpi := two_pi_pos
  set u : ℝ := y / (2 * Real.pi) with hu
  have hfract : u - (round u : ℝ) = Int.fract (u + 1 / 2) - 1 / 2 := by
    rw [round_eq, Int.fract]
    ring
  have h0 : (0 : ℝ) ≤ Int.fract (u + 1 / 2) := Int.fract_nonneg _
  have h1 : Int.fract (u + 1 / 2) < 1 := Int.fract_lt_one _
  have hval : phaseGap y 0 = 2 * Real.pi * (u - (round u : ℝ)) := by
    rw [phaseGap, sub_zero, hu]
    field_simp
  rw [hval, hfract]
  constructor <;> nlinarith [h0, h1, Real.pi_pos]

/-- **`(15)`: the half-open phase representative.** -/
noncomputable def phaseWrap (x : ℝ) : ℝ := -(phaseGap (-x) 0)

/-- **The branch integer of `(15)`.** -/
noncomputable def branchIndex (x : ℝ) : ℤ := -round (-x / (2 * Real.pi))

theorem phaseWrap_mem (x : ℝ) : -Real.pi < phaseWrap x ∧ phaseWrap x ≤ Real.pi := by
  obtain ⟨h1, h2⟩ := phaseGap_zero_mem (-x)
  constructor
  · rw [phaseWrap]
    linarith
  · rw [phaseWrap]
    linarith

/-- **`(15)`: the displacement is `2π` times the branch integer.** -/
theorem sub_phaseWrap_eq (x : ℝ) : x - phaseWrap x = 2 * Real.pi * (branchIndex x : ℝ) := by
  rw [phaseWrap, branchIndex, phaseGap, sub_zero]
  push_cast
  ring

/-- Folding does not change the exponential. -/
theorem exp_phaseWrap (x : ℝ) :
    Complex.exp (-((phaseWrap x : ℝ) : ℂ) * Complex.I)
      = Complex.exp (-((x : ℝ) : ℂ) * Complex.I) := by
  have hk := sub_phaseWrap_eq x
  rw [Complex.exp_eq_exp_iff_exists_int]
  refine ⟨branchIndex x, ?_⟩
  have hcast : ((phaseWrap x : ℝ) : ℂ) = ((x : ℝ) : ℂ)
      - 2 * (Real.pi : ℂ) * ((branchIndex x : ℤ) : ℂ) := by
    exact_mod_cast congrArg (fun r : ℝ => ((r : ℝ) : ℂ)) (by linarith [hk] :
      phaseWrap x = x - 2 * Real.pi * (branchIndex x : ℝ))
  rw [hcast]
  ring

/-! ## The folded generator in the eigenbasis -/

section Folded

open _root_.Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **`(16)`: the canonical folded Hermitian generator.** -/
noncomputable def foldedGenerator (E : n → ℝ) (t : ℝ) : Matrix n n ℂ :=
  Matrix.diagonal fun j => ((phaseWrap (t * E j) : ℝ) : ℂ)

/-- **`(16)`: the integer branch ledger.** -/
noncomputable def branchLedger (E : n → ℝ) (t : ℝ) : Matrix n n ℂ :=
  Matrix.diagonal fun j => ((branchIndex (t * E j) : ℤ) : ℂ)

omit [Fintype n] in
/-- **`(17)`, first identity**: `F(t) = tH - 2π N(t)`. -/
theorem foldedGenerator_eq (E : n → ℝ) (t : ℝ) :
    foldedGenerator E t
      = ((t : ℝ) : ℂ) • Matrix.diagonal (fun j => ((E j : ℝ) : ℂ))
        - (2 * (Real.pi : ℂ)) • branchLedger E t := by
  ext i j
  by_cases hij : i = j
  · subst hij
    simp only [foldedGenerator, branchLedger, Matrix.sub_apply, Matrix.smul_apply,
      Matrix.diagonal_apply_eq, smul_eq_mul]
    have h := sub_phaseWrap_eq (t * E i)
    have hcast : ((phaseWrap (t * E i) : ℝ) : ℂ)
        = ((t * E i : ℝ) : ℂ) - 2 * (Real.pi : ℂ) * ((branchIndex (t * E i) : ℤ) : ℂ) := by
      exact_mod_cast congrArg (fun r : ℝ => ((r : ℝ) : ℂ)) (by linarith [h] :
        phaseWrap (t * E i) = t * E i - 2 * Real.pi * (branchIndex (t * E i) : ℝ))
    rw [hcast]
    push_cast
    ring
  · simp [foldedGenerator, branchLedger, Matrix.diagonal_apply_ne _ hij]

/-- **`(17)`, second identity**: the folded generator exponentiates to the same orbit. -/
theorem exp_foldedGenerator (E : n → ℝ) (t : ℝ) :
    NormedSpace.exp (Matrix.diagonal fun j => -((phaseWrap (t * E j) : ℝ) : ℂ) * Complex.I)
      = NormedSpace.exp (Matrix.diagonal fun j => -((t * E j : ℝ) : ℂ) * Complex.I) := by
  rw [exp_diagonal_entries, exp_diagonal_entries]
  congr 1
  funext j
  exact exp_phaseWrap (t * E j)

omit [Fintype n] [DecidableEq n] in
/-- **`(17)`, third statement**: the folded spectrum sits in the half-open window. -/
theorem foldedGenerator_spec (E : n → ℝ) (t : ℝ) (j : n) :
    -Real.pi < phaseWrap (t * E j) ∧ phaseWrap (t * E j) ≤ Real.pi :=
  phaseWrap_mem (t * E j)

end Folded

/-! ## Theorem B: the locality fracture -/

section Fracture

variable {n : Type*} [Fintype n]

/-- A spectrum inside the half-open window has diameter strictly below `2π`. -/
theorem diam_lt_of_mem_window (hne : (Finset.univ : Finset n).Nonempty) (κ : n → ℝ)
    (hmem : ∀ j, -Real.pi < κ j ∧ κ j ≤ Real.pi) :
    (Finset.univ.sup' hne κ) - (Finset.univ.inf' hne κ) < 2 * Real.pi := by
  have hsup : (Finset.univ.sup' hne κ) ≤ Real.pi :=
    Finset.sup'_le _ _ fun j _ => (hmem j).2
  obtain ⟨j, _, hjeq⟩ := Finset.exists_mem_eq_inf' hne κ
  have hinf : -Real.pi < Finset.univ.inf' hne κ := by
    rw [hjeq]
    exact (hmem j).1
  linarith

/-- **The folded spectrum has diameter strictly below `2π`.** -/
theorem foldedSpectrum_diam_lt (hne : (Finset.univ : Finset n).Nonempty) (E : n → ℝ) (t : ℝ) :
    (Finset.univ.sup' hne fun j => phaseWrap (t * E j))
      - (Finset.univ.inf' hne fun j => phaseWrap (t * E j)) < 2 * Real.pi :=
  diam_lt_of_mem_window hne _ fun j => phaseWrap_mem (t * E j)

/-- **`(19)`: after one full winding the folded generator cannot be physical.**  If the folded
generator equals `tH + 2πm`, the spectral width is strictly below one winding. -/
theorem abs_mul_width_lt_two_pi_of_physical (hne : (Finset.univ : Finset n).Nonempty)
    (E : n → ℝ) (t : ℝ) {m : ℤ}
    (hphys : ∀ j, phaseWrap (t * E j) = t * E j + 2 * Real.pi * (m : ℝ)) :
    |t| * ((Finset.univ.sup' hne E) - (Finset.univ.inf' hne E)) < 2 * Real.pi := by
  have hfun : (fun j => phaseWrap (t * E j))
      = fun j => t * E j + 2 * Real.pi * (m : ℝ) := by
    funext j
    exact hphys j
  have hlt := foldedSpectrum_diam_lt hne E t
  rw [hfun] at hlt
  rwa [diam_affine hne E t (2 * Real.pi * (m : ℝ))] at hlt

end Fracture


end GaloisForLFunctions.HTGeometry
