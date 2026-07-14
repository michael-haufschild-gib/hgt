import GaloisForLFunctions.HTGeometry.ExponentialSumDA

/-!
# Directional Vandermonde phase-jet carrier

A finite phase polynomial `f(t) = ∑_j c_j·exp(λ_j·t)` with **distinct** frequencies `λ_j` and not all
coefficients zero cannot be flat: at every base point `t₀` some derivative of order `< r` is nonzero,
where `r` is the number of frequencies.  The jet vector `(f(t₀), f'(t₀), …, f⁽ʳ⁻¹⁾(t₀))` equals the
transposed Vandermonde matrix of the `λ_j` applied to the vector `(c_j·exp(λ_j·t₀))_j`; distinct
frequencies make that matrix invertible, and `exp` never vanishes, so the jet vector is nonzero exactly
when the coefficients are not all zero.

This is the directional finite phase-jet nonvanishing behind the neutral-product boundary of the
signed-archimedean orbit-charge law (eq. 31b–31d, §10 attacks 3 and 5): along the translation
direction a nonzero finite phase polynomial has a uniformly (base-point-independent) nonzero jet of
bounded order `< r`.  In particular the finite exponential carrier `span{exp(kβ·s) : k ≤ N}` — the real
growth layers of a neutral signed Gamma product — is never flat, so a Stokes/flat correction cannot
cancel the whole carrier: it stays projectively scalar.

* `phasePolynomial`, `iteratedDeriv_phasePolynomial` — the carrier and its explicit jet.
* `phaseJet_exists_ne_zero` — the directional Vandermonde nonvanishing (main theorem).
* `phasePolynomial_ne_zero`, `phasePolynomial_ne_zero_fun` — nonzero coefficients ⟹ nonzero function.
* `expLayer_jet_exists_ne_zero` — the specialization to `∑_{k≤N} c_k·exp(kβ·s)`, `β ≠ 0`.
-/

open Complex
open scoped BigOperators Matrix

namespace GaloisForLFunctions

namespace HTGeometry

/-- A finite phase polynomial: `t ↦ ∑_j c_j·exp(λ_j·t)`. -/
noncomputable def phasePolynomial {r : ℕ} (lam c : Fin r → ℂ) : ℂ → ℂ :=
  fun t => ∑ j : Fin r, c j * Complex.exp (lam j * t)

/-- The order-`k` jet of a phase polynomial: `f⁽ᵏ⁾(t) = ∑_j c_j·λ_jᵏ·exp(λ_j·t)`. -/
theorem iteratedDeriv_phasePolynomial {r : ℕ} (lam c : Fin r → ℂ) (k : ℕ) (t : ℂ) :
    iteratedDeriv k (phasePolynomial lam c) t
      = ∑ j : Fin r, c j * lam j ^ k * Complex.exp (lam j * t) := by
  have hdef : phasePolynomial lam c
      = fun t => ∑ j : Fin r, c j * Complex.exp (lam j * t) := rfl
  rw [hdef]
  exact iteratedDeriv_finset_expSum Finset.univ c lam k t

/-- **Directional Vandermonde phase-jet nonvanishing.**  If the frequencies `λ_j` are pairwise
distinct (`lam` injective) and the coefficients are not all zero, then at every base point `t₀` the
phase polynomial has a nonzero jet of order `< r`.  Proof: the jet values solve the transposed
Vandermonde system `V(λ)ᵀ · (c_j·exp(λ_j·t₀))_j`; distinct frequencies make `V(λ)` invertible and
`exp` is nowhere zero, so the coefficient vector — hence the jet vector — is nonzero. -/
theorem phaseJet_exists_ne_zero {r : ℕ} {lam c : Fin r → ℂ}
    (hlam : Function.Injective lam) (hc : c ≠ 0) (t₀ : ℂ) :
    ∃ k : Fin r, iteratedDeriv (k : ℕ) (phasePolynomial lam c) t₀ ≠ 0 := by
  by_contra h
  simp only [not_exists, not_not] at h
  apply hc
  have hvan : (fun j : Fin r => c j * Complex.exp (lam j * t₀)) = 0 := by
    apply Matrix.eq_zero_of_mulVec_eq_zero (M := (Matrix.vandermonde lam)ᵀ)
    · rw [Matrix.det_transpose, Matrix.det_vandermonde_ne_zero_iff]
      exact hlam
    · funext k
      have hrow : ((Matrix.vandermonde lam)ᵀ *ᵥ
            (fun j => c j * Complex.exp (lam j * t₀))) k
          = ∑ j : Fin r, lam j ^ (k : ℕ) * (c j * Complex.exp (lam j * t₀)) := by
        simp [Matrix.mulVec, dotProduct, Matrix.vandermonde, Matrix.transpose_apply]
      rw [Pi.zero_apply, hrow]
      have hk := h k
      rw [iteratedDeriv_phasePolynomial] at hk
      rw [← hk]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      ring
  funext j
  have hj := congrFun hvan j
  simp only [Pi.zero_apply] at hj
  exact (mul_eq_zero.mp hj).resolve_right (Complex.exp_ne_zero _)

/-- A nonzero-coefficient phase polynomial with distinct frequencies is not the zero function: it has
a nonzero value or derivative at every point. -/
theorem phasePolynomial_ne_zero {r : ℕ} {lam c : Fin r → ℂ}
    (hlam : Function.Injective lam) (hc : c ≠ 0) (t₀ : ℂ) :
    ∃ k : Fin r, iteratedDeriv (k : ℕ) (phasePolynomial lam c) t₀ ≠ 0 :=
  phaseJet_exists_ne_zero hlam hc t₀

/-- A nonzero-coefficient phase polynomial with distinct frequencies is not identically zero as a
function. -/
theorem phasePolynomial_ne_zero_fun {r : ℕ} {lam c : Fin r → ℂ}
    (hlam : Function.Injective lam) (hc : c ≠ 0) :
    phasePolynomial lam c ≠ 0 := by
  intro h0
  obtain ⟨k, hk⟩ := phaseJet_exists_ne_zero hlam hc 0
  apply hk
  rw [h0]
  exact iteratedDeriv_const_zero

/-- **Finite exponential-layer nonvanishing.**  For `β ≠ 0`, the finite exponential carrier
`∑_{k ≤ N} c_k·exp(kβ·s)` with not-all-zero coefficients has, at every base point, a nonzero jet of
order `≤ N`: the growth layers `exp(kβ·s)` are the distinct frequencies `kβ`, so this is the
directional Vandermonde nonvanishing.  A flat (Stokes) correction cannot cancel the carrier. -/
theorem expLayer_jet_exists_ne_zero {N : ℕ} {β : ℂ} (hβ : β ≠ 0)
    {c : Fin (N + 1) → ℂ} (hc : c ≠ 0) (t₀ : ℂ) :
    ∃ k : Fin (N + 1),
      iteratedDeriv (k : ℕ) (phasePolynomial (fun k => (k : ℂ) * β) c) t₀ ≠ 0 := by
  refine phaseJet_exists_ne_zero ?_ hc t₀
  intro a b hab
  have hab' : ((a : ℕ) : ℂ) * β = ((b : ℕ) : ℂ) * β := hab
  exact Fin.ext (Nat.cast_injective (mul_right_cancel₀ hβ hab'))

end HTGeometry

end GaloisForLFunctions
