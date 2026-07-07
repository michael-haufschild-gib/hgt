/-
The determinant bridge to RH: a Hermitian seam generator whose characteristic determinant vanishes at
the strip ξ-zeros forces them onto the critical line.

The seam construction's conclusion (§9–§10) is: the cohomological determinant `sdet(s − Θ_Δ)` is `C·ξ`,
and the reciprocity/positivity of `H_Δ^1` makes the shifted generator `Θ_Δ = ½ + iT_Δ` with `T_Δ`
self-adjoint; hence every ξ-zero, being a spectral point of `Θ_Δ`, lies on `½ + iℝ`.  This file makes
that final implication a theorem in the finite (Hermitian-matrix) model — the model the seam presents
`Θ_Δ` in, via its spectrum (the ξ-zeros), exactly as `SeamResolventDeterminant` reads the resolvent
trace off `diagonal t` and `CarrierPickKernel` builds the Pick carrier from the eigenvalue family.

* `strip_zero_of_hermitian_det_line` — the algebraic core: for a **Hermitian** `T`, if the
  characteristic determinant of the seam generator `Θ = ½·1 + iT` vanishes at `ρ`
  (`det(ρ·1 − (½·1 + iT)) = 0`), then `ρ = ½ + i·(eigenvalue of T)`, so `ρ` has real part `½`.  Proof:
  the spectral theorem diagonalizes `ρ·1 − Θ = U · diagonal(fun k => ρ − ½ − i·τ_k) · U⋆`; the
  determinant is `∏_k (ρ − ½ − i·τ_k)` (conjugation-invariant), which vanishes iff `ρ = ½ + i·τ_k` for
  some real eigenvalue `τ_k`.

* `rh_of_hermitian_determinant` — the master conditional: if a single Hermitian `T` captures every
  strip ξ-zero as a root of its seam characteristic determinant
  (`det(ρ·1 − (½·1 + iT)) = 0` whenever `ξ ρ = 0` in the strip), then the Riemann Hypothesis holds,
  by composing the core with `SeamCrossingTower.rh_of_seam_spectral`.

This is the seam's §9–§10 conclusion, machine-checked: the `sdet = C·ξ` divisor identity (giving
`ξ ρ = 0 → det(ρ·1 − Θ) = 0`, since a nonzero constant does not move the divisor) plus the Hermitian
structure of `Θ − ½` yields the critical-line constraint.  The remaining content is the hypothesis
`hcap` itself — that one Hermitian generator captures all strip zeros — which is the infinite-height
existence statement `seam_spectral_iff_rh` shows is equivalent to RH: no finite `T` captures the
infinitely many zeros, so `hcap` is the limit object, not a finite-fillable gap.
-/
import GaloisForLFunctions.RHTower.SeamCrossingTower
import Mathlib.Analysis.Matrix.Spectrum

noncomputable section

namespace RHTower

open Matrix Complex

variable {N : Type*} [Fintype N] [DecidableEq N]

/-- **The characteristic determinant of a Hermitian seam generator vanishes only on the line.**  For a
Hermitian `T`, the seam generator `Θ = ½·1 + iT` has `det(ρ·1 − Θ) = ∏_k (ρ − ½ − i·τ_k)` over the
real eigenvalues `τ_k` of `T` (spectral theorem + conjugation-invariance of `det`).  So if this
determinant vanishes at `ρ`, then `ρ = ½ + i·τ_k` for some real `τ_k` — `ρ` lies on `½ + iℝ`. -/
theorem strip_zero_of_hermitian_det_line (T : Matrix N N ℂ) (hT : T.IsHermitian) (ρ : ℂ)
    (hdet : (ρ • (1 : Matrix N N ℂ) - ((1 / 2 : ℂ) • 1 + Complex.I • T)).det = 0) :
    ∃ lam : ℝ, ρ = 1 / 2 + (lam : ℂ) * I := by
  set U : Matrix N N ℂ := (hT.eigenvectorUnitary : Matrix N N ℂ) with hUdef
  have hSU : star U * U = 1 := by
    have h := hT.eigenvectorUnitary.2; rwa [Matrix.mem_unitaryGroup_iff'] at h
  have hUS : U * star U = 1 := by
    have h := hT.eigenvectorUnitary.2; rwa [Matrix.mem_unitaryGroup_iff] at h
  have hunit : IsUnit U := Unitary.isUnit_coe
  have hinv : U⁻¹ = star U := Matrix.inv_eq_left_inv hSU
  have hspec : T = U * diagonal (fun i => ((hT.eigenvalues i : ℝ) : ℂ)) * star U := by
    rw [hUdef]; conv_lhs => rw [hT.spectral_theorem]
    rfl
  set D : Matrix N N ℂ := diagonal (fun i => ((hT.eigenvalues i : ℝ) : ℂ)) with hDdef
  have hg : diagonal (fun i => ρ - (1 / 2 + Complex.I * ((hT.eigenvalues i : ℝ) : ℂ)))
      = ρ • (1 : Matrix N N ℂ) - ((1 / 2 : ℂ) • 1 + Complex.I • D) := by
    ext i j
    by_cases h : i = j
    · subst h; simp [hDdef, Matrix.diagonal_apply_eq, Matrix.one_apply_eq]
    · simp [hDdef, Matrix.one_apply_ne h, h]
  have hdiag : ρ • (1 : Matrix N N ℂ) - ((1 / 2 : ℂ) • 1 + Complex.I • T)
      = U * diagonal (fun i => ρ - (1 / 2 + Complex.I * ((hT.eigenvalues i : ℝ) : ℂ))) * star U := by
    rw [hg]; symm
    have hUDU : U * D * star U = T := by rw [hspec]
    calc U * (ρ • (1 : Matrix N N ℂ) - ((1 / 2 : ℂ) • 1 + Complex.I • D)) * star U
        = ρ • (U * 1 * star U)
          - ((1 / 2 : ℂ) • (U * 1 * star U) + Complex.I • (U * D * star U)) := by
          simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_add, Matrix.add_mul,
            Matrix.mul_smul, Matrix.smul_mul]
      _ = ρ • (1 : Matrix N N ℂ) - ((1 / 2 : ℂ) • 1 + Complex.I • T) := by
          rw [Matrix.mul_one, hUS, hUDU]
  rw [hdiag, hinv.symm, Matrix.det_conj hunit, Matrix.det_diagonal] at hdet
  rw [Finset.prod_eq_zero_iff] at hdet
  obtain ⟨i, _, hfac⟩ := hdet
  refine ⟨hT.eigenvalues i, ?_⟩
  have h2 : ρ = 1 / 2 + Complex.I * ((hT.eigenvalues i : ℝ) : ℂ) := sub_eq_zero.mp hfac
  rw [h2]; ring

/-- **A Hermitian seam generator capturing all strip zeros ⟹ RH.**  If a single Hermitian `T`
captures every strip ξ-zero as a root of its seam characteristic determinant — `det(ρ·1 − (½·1 + iT))
= 0` whenever `ξ ρ = 0` with `0 < ρ.re < 1` — then the Riemann Hypothesis holds.  Each such zero is
`½ + i·(eigenvalue of T)` (`strip_zero_of_hermitian_det_line`), hence on the critical line
(`rh_of_seam_spectral`).  This is the seam's §9–§10 determinant conclusion; the hypothesis `hcap` is
the infinite-height spectral capture equivalent to RH (`seam_spectral_iff_rh`). -/
theorem rh_of_hermitian_determinant (T : Matrix N N ℂ) (hT : T.IsHermitian)
    (hcap : ∀ ρ : ℂ, xi ρ = 0 → 0 < ρ.re → ρ.re < 1 →
        (ρ • (1 : Matrix N N ℂ) - ((1 / 2 : ℂ) • 1 + Complex.I • T)).det = 0) :
    RiemannHypothesis := by
  apply rh_of_seam_spectral
  intro ρ hxi h0 h1
  exact strip_zero_of_hermitian_det_line T hT ρ (hcap ρ hxi h0 h1)

/-- **The seam determinant identity `sdet(s − Θ) = C·ξ(s)` ⟹ RH.**  The moonshot's §9 phrasing: if the
seam generator's characteristic determinant is a constant multiple of `ξ` at the strip zeros —
`det(ρ·1 − (½·1 + iT)) = C·ξ ρ` with `T` Hermitian — then the Riemann Hypothesis holds.  At a ξ-zero
the right side is `C·0 = 0`, so the determinant vanishes there and `rh_of_hermitian_determinant`
applies.  This is exactly "the spectral divisor is the `ξ`-divisor ⟹ zeros on the line," the
integrated form of the resolvent-flux identity `Str((s − Θ)⁻¹) = ξ'/ξ`. -/
theorem rh_of_hermitian_determinant_eq_xi (T : Matrix N N ℂ) (hT : T.IsHermitian) (C : ℂ)
    (hdet_eq : ∀ ρ : ℂ, xi ρ = 0 → 0 < ρ.re → ρ.re < 1 →
        (ρ • (1 : Matrix N N ℂ) - ((1 / 2 : ℂ) • 1 + Complex.I • T)).det = C * xi ρ) :
    RiemannHypothesis := by
  apply rh_of_hermitian_determinant T hT
  intro ρ hxi h0 h1
  rw [hdet_eq ρ hxi h0 h1, hxi, mul_zero]

end RHTower
