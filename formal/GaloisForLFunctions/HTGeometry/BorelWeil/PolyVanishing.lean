/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.BorelWeil.PolyRealization
import GaloisForLFunctions.HTGeometry.BorelWeil.Dominance

/-!
# Comparison with the group model, and vanishing in the polynomial model

Restricting a polynomial section to the special linear group gives a section in the group model,
and this restriction is injective: a section is determined on `SL(N,k)` because every invertible
matrix is an `SL` element times a Borel element, and a polynomial vanishing on the invertible
matrices vanishes identically.  Combined with the rank-one vanishing theorem of the group model,
this gives the dominance criterion in the polynomial model as well.

## Main results

* `restrictToSL_mem_bwSections` — the comparison map.
* `eq_zero_of_restrictToSL_eq_zero` — its injectivity.
* `polySections_eq_bot_of_not_antitone`, `polySections_ne_bot_iff_antitone`.
-/

set_option linter.unusedSectionVars false

namespace GaloisForLFunctions.HTGeometry.BorelWeil

open Matrix MvPolynomial

variable {N : ℕ} {k : Type*} [Field k]

theorem truncate_self (A : Matrix (Fin N) (Fin N) k) : truncate N A = A := by
  ext i i'
  exact truncate_apply_of_both i.isLt i'.isLt

theorem matEval_minorPoly_top (g : Matrix (Fin N) (Fin N) k) :
    matEval g (minorPoly N N k) = g.det := by
  rw [matEval_minorPoly, leadingMinorMat, truncate_self]

theorem minorPoly_top_ne_zero : (minorPoly N N k) ≠ 0 := by
  intro h
  have := congrArg (matEval (1 : Matrix (Fin N) (Fin N) k)) h
  rw [matEval_minorPoly_top, matEval_zero, Matrix.det_one] at this
  exact one_ne_zero this

theorem coordEval_apply (p : MvPolynomial (Fin N × Fin N) k)
    (g : SpecialLinearGroup (Fin N) k) :
    coordEval (Fin N) k p g = matEval (g : Matrix (Fin N) (Fin N) k) p := by
  have h := MvPolynomial.comp_aeval (R := k)
    (fun ij : Fin N × Fin N => (coordFun ij.1 ij.2 : SpecialLinearGroup (Fin N) k → k))
    (Pi.evalAlgHom k (fun _ : SpecialLinearGroup (Fin N) k => k) g)
  have h2 := congrFun
    (congrArg (fun φ : MvPolynomial (Fin N × Fin N) k →ₐ[k] k => (φ : _ → k)) h) p
  simpa [coordEval, matEval, coordFun, MvPolynomial.coe_aeval_eq_eval] using h2

/-- The restriction of a polynomial to the special linear group. -/
noncomputable def restrictToSL (p : MvPolynomial (Fin N × Fin N) k) :
    SpecialLinearGroup (Fin N) k → k :=
  fun g => matEval (g : Matrix (Fin N) (Fin N) k) p

theorem restrictToSL_mem_regularFun (p : MvPolynomial (Fin N × Fin N) k) :
    restrictToSL p ∈ regularFun (Fin N) k :=
  ⟨p, funext fun g => (coordEval_apply p g)⟩

theorem isBorelMat_of_mem_borel {b : SpecialLinearGroup (Fin N) k}
    (hb : b ∈ borel (Fin N) k) : IsBorelMat (b : Matrix (Fin N) (Fin N) k) := by
  refine ⟨hb, fun i => ?_⟩
  have hdet : (b : Matrix (Fin N) (Fin N) k).det = 1 := b.2
  rw [Matrix.det_of_upperTriangular hb] at hdet
  have hne : (∏ i : Fin N, (b : Matrix (Fin N) (Fin N) k) i i) ≠ 0 := by
    rw [hdet]; exact one_ne_zero
  exact Finset.prod_ne_zero_iff.mp hne i (Finset.mem_univ i)

/-- **The comparison map.**  Restriction sends polynomial sections to sections in the group
model. -/
theorem restrictToSL_mem_bwSections {lam : Fin N → ℕ} {p : MvPolynomial (Fin N × Fin N) k}
    (hp : p ∈ polySections lam) : restrictToSL p ∈ bwSections lam := by
  refine ⟨restrictToSL_mem_regularFun p, fun g b hb => ?_⟩
  have := hp (g : Matrix (Fin N) (Fin N) k) (b : Matrix (Fin N) (Fin N) k)
    (isBorelMat_of_mem_borel hb)
  simpa [restrictToSL, SpecialLinearGroup.coe_mul, borelChar, borelCharMat] using this

/-- **Injectivity of the comparison map.** -/
theorem eq_zero_of_restrictToSL_eq_zero [Infinite k] {lam : Fin N → ℕ}
    {p : MvPolynomial (Fin N × Fin N) k} (hp : p ∈ polySections lam)
    (h : ∀ g : SpecialLinearGroup (Fin N) k, matEval (g : Matrix (Fin N) (Fin N) k) p = 0) :
    p = 0 := by
  classical
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    refine matEval_injective fun g => ?_
    rw [matEval_zero]
    have hg : g = ((1 : SpecialLinearGroup (Fin 0) k) : Matrix (Fin 0) (Fin 0) k) := by
      ext i
      exact i.elim0
    rw [hg]
    exact h 1
  · -- every invertible matrix factors as an `SL` element times a Borel element
    have hGL : ∀ g : Matrix (Fin N) (Fin N) k, g.det ≠ 0 → matEval g p = 0 := by
      intro g hg
      set i₀ : Fin N := ⟨0, hN⟩ with hi₀
      set B : Matrix (Fin N) (Fin N) k :=
        Matrix.diagonal (fun i => if i = i₀ then g.det else 1) with hB
      have hBdet : B.det = g.det := by
        rw [hB, Matrix.det_diagonal, Finset.prod_eq_single i₀]
        · rw [if_pos rfl]
        · intro r _ hr; rw [if_neg hr]
        · intro hcon; exact absurd (Finset.mem_univ i₀) hcon
      have hBborel : IsBorelMat B := by
        refine ⟨fun i j hij => ?_, fun i => ?_⟩
        · rw [hB]
          exact Matrix.diagonal_apply_ne _ (ne_of_gt hij)
        · rw [hB, Matrix.diagonal_apply_eq]
          by_cases hi : i = i₀
          · rw [if_pos hi]; exact hg
          · rw [if_neg hi]; exact one_ne_zero
      have hBunit : IsUnit B.det := by rw [hBdet]; exact isUnit_iff_ne_zero.mpr hg
      haveI : Invertible B.det := hBunit.invertible
      haveI : Invertible B := Matrix.invertibleOfDetInvertible _
      have hhdet : (g * B⁻¹).det = 1 := by
        rw [Matrix.det_mul, Matrix.det_nonsing_inv, hBdet, Ring.inverse_eq_inv',
          mul_inv_cancel₀ hg]
      set hSL : SpecialLinearGroup (Fin N) k := ⟨g * B⁻¹, hhdet⟩ with hSLdef
      have hgfac : g = (hSL : Matrix (Fin N) (Fin N) k) * B := by
        rw [hSLdef]
        simp only []
        rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hBunit, Matrix.mul_one]
      rw [hgfac, hp _ B hBborel, h hSL, mul_zero]
    -- a polynomial vanishing on the invertible locus vanishes
    have hzero : p * (minorPoly N N k) = 0 := by
      refine matEval_injective fun g => ?_
      rw [matEval_mul, matEval_zero, matEval_minorPoly_top]
      by_cases hg : g.det = 0
      · rw [hg, mul_zero]
      · rw [hGL g hg, zero_mul]
    rcases mul_eq_zero.mp hzero with h1 | h1
    · exact h1
    · exact absurd h1 minorPoly_top_ne_zero

/-- **Vanishing in the polynomial model.** -/
theorem polySections_eq_bot_of_not_antitone [Infinite k] {lam : Fin N → ℕ}
    (hlam : ¬ Antitone lam) : polySections (k := k) lam = ⊥ := by
  refine (Submodule.eq_bot_iff _).mpr fun p hp => ?_
  refine eq_zero_of_restrictToSL_eq_zero hp fun g => ?_
  have hres : restrictToSL p ∈ bwSections (k := k) lam := restrictToSL_mem_bwSections hp
  rw [bwSections_eq_bot_of_not_antitone hlam, Submodule.mem_bot] at hres
  exact congrFun hres g

/-- **The dominance criterion in the polynomial model.** -/
theorem polySections_ne_bot_iff_antitone [Infinite k] {lam : Fin N → ℕ} :
    polySections (k := k) lam ≠ ⊥ ↔ Antitone lam := by
  constructor
  · intro h
    by_contra hcon
    exact h (polySections_eq_bot_of_not_antitone hcon)
  · exact polySections_ne_bot_of_antitone

end GaloisForLFunctions.HTGeometry.BorelWeil
