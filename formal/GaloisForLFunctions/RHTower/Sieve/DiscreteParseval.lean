import GaloisForLFunctions.RHTower.Sieve.HarmonicSineBound

/-!
# Exact discrete Parseval

The exponential rows at the `Q`-th roots of unity are pairwise orthogonal with every diagonal entry
equal to `Q`.  Rescaling by `Q^{-1/2}` makes them orthonormal, and there are `Q` of them in a space
of dimension `Q`, so they form an orthonormal basis.  Parseval then holds with equality:

`∑_{j < Q} |⟪expRow Q (ζ^j), x⟫|² = Q ‖x‖²`.

The factor `Q` is the normalisation, not a convention: the unrescaled rows have squared norm `Q`,
so the orthonormal family is `Q^{-1/2} • expRow`.

Together with the uniform symbol bound of `HarmonicSineBound.lean` this is what converts the
Toeplitz kernel `1/(m-n)` into a bilinear inequality: the quadratic form is an average of the symbol
against `|∑ x_n ζ^{jn}|²`, and Parseval turns that average back into `∑ |x_n|²`.
-/

namespace RHTower.Sieve

open Finset
open scoped InnerProductSpace

/-- The normalised exponential rows at the `Q`-th roots of unity. -/
noncomputable def unitRow (Q : ℕ) (ζ : ℂ) (j : Fin Q) : EuclideanSpace ℂ (Fin Q) :=
  (((Real.sqrt Q)⁻¹ : ℝ) : ℂ) • expRow Q (ζ ^ (j : ℕ))

/-- The normalised rows are orthonormal. -/
theorem orthonormal_unitRow {ζ : ℂ} {Q : ℕ} (hQ : 0 < Q) (hζ : IsPrimitiveRoot ζ Q) :
    Orthonormal ℂ (unitRow Q ζ) := by
  have hQR : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast hQ
  have hsq : Real.sqrt Q * Real.sqrt Q = (Q : ℝ) := Real.mul_self_sqrt hQR.le
  have hsqpos : (0 : ℝ) < Real.sqrt Q := Real.sqrt_pos.2 hQR
  rw [orthonormal_iff_ite]
  intro j k
  rw [unitRow, unitRow, inner_smul_left, inner_smul_right]
  have hconj : (starRingEnd ℂ) (((Real.sqrt Q)⁻¹ : ℝ) : ℂ) = (((Real.sqrt Q)⁻¹ : ℝ) : ℂ) :=
    Complex.conj_ofReal _
  rw [hconj]
  by_cases hjk : j = k
  · subst hjk
    rw [inner_expRow_root_self hQ hζ, if_pos rfl]
    have : (((Real.sqrt Q)⁻¹ : ℝ) : ℂ) * ((((Real.sqrt Q)⁻¹ : ℝ) : ℂ) * (Q : ℂ)) = 1 := by
      have hne : ((Real.sqrt Q : ℝ) : ℂ) ≠ 0 := by
        simp only [ne_eq, Complex.ofReal_eq_zero]
        linarith
      have hQc : ((Q : ℕ) : ℂ) = ((Real.sqrt Q : ℝ) : ℂ) * ((Real.sqrt Q : ℝ) : ℂ) := by
        rw [← Complex.ofReal_mul, hsq]
        norm_num
      rw [hQc]
      push_cast
      field_simp
    rw [this]
  · have hne : (j : ℕ) ≠ (k : ℕ) := fun hcon => hjk (Fin.ext hcon)
    rw [inner_expRow_root_eq_zero hQ hζ j.isLt k.isLt hne, if_neg hjk]
    ring

/-- The normalised rows span. -/
theorem span_unitRow {ζ : ℂ} {Q : ℕ} (hQ : 0 < Q) (hζ : IsPrimitiveRoot ζ Q) :
    ⊤ ≤ Submodule.span ℂ (Set.range (unitRow Q ζ)) := by
  classical
  haveI : Nonempty (Fin Q) := ⟨⟨0, hQ⟩⟩
  have hON := orthonormal_unitRow hQ hζ
  have hcard : Fintype.card (Fin Q) = Module.finrank ℂ (EuclideanSpace ℂ (Fin Q)) := by
    rw [Fintype.card_fin, finrank_euclideanSpace_fin]
  have hcoe : ⇑(basisOfOrthonormalOfCardEqFinrank hON hcard) = unitRow Q ζ :=
    coe_basisOfOrthonormalOfCardEqFinrank hON hcard
  rw [← hcoe]
  exact le_of_eq ((basisOfOrthonormalOfCardEqFinrank hON hcard).span_eq).symm

/-- The normalised rows form an orthonormal basis. -/
noncomputable def rootBasis {ζ : ℂ} {Q : ℕ} (hQ : 0 < Q) (hζ : IsPrimitiveRoot ζ Q) :
    OrthonormalBasis (Fin Q) ℂ (EuclideanSpace ℂ (Fin Q)) :=
  OrthonormalBasis.mk (orthonormal_unitRow hQ hζ) (span_unitRow hQ hζ)

theorem rootBasis_apply {ζ : ℂ} {Q : ℕ} (hQ : 0 < Q) (hζ : IsPrimitiveRoot ζ Q) (j : Fin Q) :
    rootBasis hQ hζ j = unitRow Q ζ j := by
  rw [rootBasis, OrthonormalBasis.coe_mk]

/-- **Exact discrete Parseval.** -/
theorem sum_norm_inner_expRow_root {ζ : ℂ} {Q : ℕ} (hQ : 0 < Q) (hζ : IsPrimitiveRoot ζ Q)
    (x : EuclideanSpace ℂ (Fin Q)) :
    ∑ j : Fin Q, ‖⟪expRow Q (ζ ^ (j : ℕ)), x⟫_ℂ‖ ^ 2 = (Q : ℝ) * ‖x‖ ^ 2 := by
  classical
  have hQR : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast hQ
  have hsq : Real.sqrt Q * Real.sqrt Q = (Q : ℝ) := Real.mul_self_sqrt hQR.le
  have hsqpos : (0 : ℝ) < Real.sqrt Q := Real.sqrt_pos.2 hQR
  set b := rootBasis hQ hζ with hb
  have hbcoe : ∀ j : Fin Q, b j = unitRow Q ζ j := fun j => rootBasis_apply hQ hζ j
  have hpar := b.sum_inner_mul_inner x x
  have hterm : ∀ j : Fin Q, ⟪x, b j⟫_ℂ * ⟪b j, x⟫_ℂ = ((‖⟪b j, x⟫_ℂ‖ ^ 2 : ℝ) : ℂ) := by
    intro j
    rw [← inner_conj_symm x (b j), conj_mul_self]
  rw [Finset.sum_congr rfl (fun j _ => hterm j), inner_self_eq_norm_sq_to_K] at hpar
  have hreal : ∑ j : Fin Q, ‖⟪b j, x⟫_ℂ‖ ^ 2 = ‖x‖ ^ 2 := by
    have hcast : ((∑ j : Fin Q, ‖⟪b j, x⟫_ℂ‖ ^ 2 : ℝ) : ℂ) = ((‖x‖ ^ 2 : ℝ) : ℂ) := by
      rw [Complex.ofReal_sum, hpar]
      norm_cast
    exact_mod_cast hcast
  have hscale : ∀ j : Fin Q,
      ‖⟪b j, x⟫_ℂ‖ ^ 2 = (1 / (Q : ℝ)) * ‖⟪expRow Q (ζ ^ (j : ℕ)), x⟫_ℂ‖ ^ 2 := by
    intro j
    rw [hbcoe j, unitRow, inner_smul_left, Complex.conj_ofReal, norm_mul]
    have hnr : ‖(((Real.sqrt Q)⁻¹ : ℝ) : ℂ)‖ = (Real.sqrt Q)⁻¹ := by
      simp
    rw [hnr, mul_pow]
    have hinv : ((Real.sqrt Q)⁻¹) ^ 2 = 1 / (Q : ℝ) := by
      rw [inv_pow, Real.sq_sqrt hQR.le, one_div]
    rw [hinv]
  rw [Finset.sum_congr rfl (fun j _ => hscale j), ← Finset.mul_sum] at hreal
  field_simp at hreal
  linarith [hreal]

end RHTower.Sieve
