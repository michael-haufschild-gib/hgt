import GaloisForLFunctions.HTGeometry.AlgebraicIntegerSeparation

/-!
# The conjugates of an integer spectral form are bounded by the spectrum

An integer combination of anchored gaps of an algebraic-integer spectrum is again an algebraic
integer, and every complex embedding of it is a combination of the embeddings of the eigenvalues
with the same integer coefficients.  If all coefficients are at most `N` in modulus and all
embeddings of the eigenvalues are at most `R`, the triangle inequality bounds every conjugate of
the form by `2dNR`, where `d` is the number of gaps.

Feeding that bound into the Liouville separation turns a nonvanishing integer spectral form into a
uniform lower bound `(2dNR)^{-(n-1)}` on its distinguished embedding, `n` being the degree of the
field.  No minimum pairwise gap of the spectrum is used, and none would suffice.
-/

open NumberField

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

section SpectralForm

variable {K : Type*} [Field K] [NumberField K] {d : ℕ}

/-- The integer spectral form: an integer combination of the gaps anchored at the first level. -/
def spectralForm (E : Fin (d + 1) → 𝓞 K) (k : Fin d → ℤ) : 𝓞 K :=
  ∑ j, k j • (E j.succ - E 0)

/-- Every complex embedding of the form is the same integer combination of the embeddings of the
eigenvalues. -/
theorem embedding_spectralForm (E : Fin (d + 1) → 𝓞 K) (k : Fin d → ℤ) (σ : K →+* ℂ) :
    σ ((spectralForm E k : 𝓞 K) : K)
      = ∑ j, (k j : ℂ) * (σ ((E j.succ : 𝓞 K) : K) - σ ((E 0 : 𝓞 K) : K)) := by
  classical
  rw [spectralForm]
  push_cast
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_zsmul, map_sub]
  ring

/-- **`(8)`, the conjugate bound.**  Coefficients at most `N` and eigenvalue embeddings at most `R`
force every conjugate of the spectral form below `2dNR`. -/
theorem norm_embedding_spectralForm_le (E : Fin (d + 1) → 𝓞 K) (k : Fin d → ℤ) {N R : ℝ}
    (hN : ∀ j, |(k j : ℝ)| ≤ N) (hR : ∀ (τ : K →+* ℂ) (i : Fin (d + 1)), ‖τ ((E i : 𝓞 K) : K)‖ ≤ R)
    (σ : K →+* ℂ) : ‖σ ((spectralForm E k : 𝓞 K) : K)‖ ≤ 2 * (d : ℝ) * N * R := by
  classical
  have hRnn : 0 ≤ R := le_trans (norm_nonneg _) (hR σ 0)
  have hterm : ∀ j : Fin d,
      ‖(k j : ℂ) * (σ ((E j.succ : 𝓞 K) : K) - σ ((E 0 : 𝓞 K) : K))‖ ≤ N * (2 * R) := by
    intro j
    have hNnn : 0 ≤ N := le_trans (abs_nonneg _) (hN j)
    rw [norm_mul]
    have hk : ‖(k j : ℂ)‖ ≤ N := by
      rw [Complex.norm_intCast]
      exact hN j
    have hdiff : ‖σ ((E j.succ : 𝓞 K) : K) - σ ((E 0 : 𝓞 K) : K)‖ ≤ 2 * R := by
      refine (norm_sub_le _ _).trans ?_
      have h1 := hR σ j.succ
      have h2 := hR σ 0
      linarith
    exact mul_le_mul hk hdiff (norm_nonneg _) hNnn
  calc ‖σ ((spectralForm E k : 𝓞 K) : K)‖
      = ‖∑ j, (k j : ℂ) * (σ ((E j.succ : 𝓞 K) : K) - σ ((E 0 : 𝓞 K) : K))‖ := by
        rw [embedding_spectralForm]
    _ ≤ ∑ j, ‖(k j : ℂ) * (σ ((E j.succ : 𝓞 K) : K) - σ ((E 0 : 𝓞 K) : K))‖ := norm_sum_le _ _
    _ ≤ ∑ _j : Fin d, N * (2 * R) := Finset.sum_le_sum fun j _ => hterm j
    _ = 2 * (d : ℝ) * N * R := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

/-- **`(9)` for the spectral form.**  A nonvanishing integer spectral form with bounded coefficients
and bounded spectrum is bounded below, uniformly, by `(2dNR)^{-(n-1)}`. -/
theorem inv_pow_le_norm_embedding_spectralForm (E : Fin (d + 1) → 𝓞 K) (k : Fin d → ℤ) {N R : ℝ}
    (hN : ∀ j, |(k j : ℝ)| ≤ N) (hR : ∀ (τ : K →+* ℂ) (i : Fin (d + 1)), ‖τ ((E i : 𝓞 K) : K)‖ ≤ R)
    (hpos : 0 < 2 * (d : ℝ) * N * R) (hne : spectralForm E k ≠ 0) (σ₀ : K →+* ℂ) :
    ((2 * (d : ℝ) * N * R) ^ (Fintype.card (K →+* ℂ) - 1))⁻¹
      ≤ ‖σ₀ ((spectralForm E k : 𝓞 K) : K)‖ :=
  inv_pow_le_norm_embedding (spectralForm E k) hne σ₀ hpos
    fun σ _ => norm_embedding_spectralForm_le E k hN hR σ

end SpectralForm

end GaloisForLFunctions.HTGeometry
