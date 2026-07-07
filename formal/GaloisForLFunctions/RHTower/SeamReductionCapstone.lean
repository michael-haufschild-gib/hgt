/-
The seam reduction capstone: a strip ξ-zero is captured by a Hermitian seam generator iff it is on the
critical line.

The seam construction reduces RH to a Hilbert–Pólya statement: the existence of a self-adjoint-after-
shift generator `Θ = ½ + iT` whose characteristic determinant is `ξ`, so that the ξ-zeros are its
spectral points `½ + i·(real eigenvalue)`.  This file states the resulting equivalence in its sharpest
per-zero form and proves it in both directions:

  `RiemannHypothesis ↔ (every strip ξ-zero ρ is a root of the seam determinant of some finite Hermitian
  generator, det(ρ·1 − (½·1 + iT)) = 0)`.

* **(⟸)** — if each strip zero is captured by a Hermitian generator's determinant, then (by
  `strip_zero_of_hermitian_det_line`) it equals `½ + i·(eigenvalue)`, hence lies on `½ + iℝ`; RH follows
  (`rh_of_seam_spectral`).  This is the moonshot's §9→§10 mechanism.
* **(⟹)** — if RH holds, each strip zero is `½ + iλ` with `λ` real, and the `1×1` Hermitian generator
  `T = [λ]` captures it: `det(ρ·1 − (½ + iλ)) = ρ − ½ − iλ = 0`.

So the seam-determinant capture is not merely *sufficient* for the critical-line condition — it is
*equivalent* to it, zero by zero.  This certifies precisely what the finite spine proves and what it
does not: every algebraic and finite-dimensional step of the construction (the crossing-energy law, the
three-sector flat trace `ξ'/ξ`, the McKean–Singer compression, the Moore–Penrose Green homotopy, the
Jacobi resolvent–determinant identity, the acyclic reciprocal caps, the Hermitian→line determinant
bridge) is machine-checked; the single remaining content is the *existence of one generator capturing
all zeros at once* — the infinite-height limit object, which this biconditional shows is logically
equivalent to RH itself, not a finite-fillable gap.
-/
import GaloisForLFunctions.RHTower.SeamDeterminantRH

noncomputable section

namespace RHTower

open Matrix Complex

/-- The `1×1` Hermitian seam generator `[λ]` built from a real number. -/
theorem oneByOne_isHermitian (lam : ℝ) :
    (!![((lam : ℝ) : ℂ)] : Matrix (Fin 1) (Fin 1) ℂ).IsHermitian := by
  rw [Matrix.IsHermitian]
  ext i j
  fin_cases i
  fin_cases j
  simp [Matrix.conjTranspose]

/-- A point on the critical line is captured by the `1×1` Hermitian generator `[λ]`: for
`ρ = ½ + iλ`, the seam determinant `det(ρ·1 − (½·1 + i[λ])) = ρ − ½ − iλ = 0`. -/
theorem oneByOne_capture {ρ : ℂ} {lam : ℝ} (h : ρ = 1 / 2 + (lam : ℂ) * I) :
    (ρ • (1 : Matrix (Fin 1) (Fin 1) ℂ)
        - ((1 / 2 : ℂ) • 1 + Complex.I • !![((lam : ℝ) : ℂ)])).det = 0 := by
  rw [Matrix.det_fin_one]
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_eq, Matrix.add_apply,
    Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, smul_eq_mul, mul_one]
  rw [h]; ring

/-- **The seam reduction capstone.**  The Riemann Hypothesis is equivalent to the seam-determinant
capture of every strip ξ-zero: `RH ↔ (∀ strip zero ρ, ∃ finite Hermitian T, det(ρ·1 − (½·1 + iT)) = 0)`.

Forward: RH puts each zero at `½ + iλ`, captured by the `1×1` generator `[λ]`.  Backward: each captured
zero equals `½ + i·(eigenvalue)`, hence on the line (`strip_zero_of_hermitian_det_line`,
`rh_of_seam_spectral`).  The whole seam construction reduces RH to this capture; the biconditional shows
the capture *is* RH — the residual is the single generator that realizes it at all zeros
simultaneously, the infinite-height limit object. -/
theorem seam_hermitian_capture_iff_rh :
    RiemannHypothesis ↔
      ∀ ρ : ℂ, xi ρ = 0 → 0 < ρ.re → ρ.re < 1 →
        ∃ T : Matrix (Fin 1) (Fin 1) ℂ, T.IsHermitian ∧
          (ρ • (1 : Matrix (Fin 1) (Fin 1) ℂ)
            - ((1 / 2 : ℂ) • 1 + Complex.I • T)).det = 0 := by
  constructor
  · intro hrh ρ hxi h0 h1
    obtain ⟨lam, hlam⟩ := (seam_spectral_iff_rh).mpr hrh ρ hxi h0 h1
    exact ⟨!![((lam : ℝ) : ℂ)], oneByOne_isHermitian lam, oneByOne_capture hlam⟩
  · intro hcap
    apply rh_of_seam_spectral
    intro ρ hxi h0 h1
    obtain ⟨T, hT, hdet⟩ := hcap ρ hxi h0 h1
    exact strip_zero_of_hermitian_det_line T hT ρ hdet

end RHTower
