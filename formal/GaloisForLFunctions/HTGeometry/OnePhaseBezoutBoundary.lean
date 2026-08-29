import GaloisForLFunctions.HTGeometry.PolynomialProjectiveBoundary

/-!
# The polynomial projective boundary of a one-phase quasianalytic field

Let `E` be a coefficient field of functions on an upper half-plane whose nonzero elements, together
with their reciprocals, grow at most polynomially on upper vertical tubes, and let `u` be a phase
that stays on a fixed circle.  A finite tuple of elements of `E(u)` is normalised by clearing a
common denominator and dividing by the polynomial gcd; the residual tuple is primitive, so it
satisfies a Bezout identity over `E[U]`.

* **Bezout survival.**  The cofactors of a Bezout identity are phase polynomials with coefficients
  of polynomial growth, hence of polynomial growth themselves; evaluating the identity at the height
  `i S` therefore forces one residual component to be at least `C · S^{-M}`.
* **Finite-order survival forces a polynomial jet.**  Translated polynomial jets of a fixed degree
  bound, normalised by the maximum of their coefficients, live on the unit sphere of a fixed
  finite-dimensional space; a subsequence converges to a nonzero polynomial tuple, and the jet error
  `O(S^{-L})` with `L > M` is killed by the normalisation.

Together with the terminal one-point boundary of a polynomial tuple this gives the two-stage carrier
`E(u) → ℂ[z] → ℂ`.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter Polynomial

/-! ## Polynomial growth of a phase polynomial -/

/-- **A phase polynomial with coefficients of polynomial growth has polynomial growth.**  The phase
`u` stays on a fixed circle, so only the finitely many coefficients contribute to the rate. -/
theorem norm_phasePoly_le {N : ℕ} (a : ℕ → ℝ → ℂ) (u : ℝ → ℂ) {B C : ℝ} {M : ℕ}
    (hC0 : 0 ≤ C)
    (hB : ∀ S : ℝ, 1 ≤ S → ‖u S‖ ≤ B)
    (ha : ∀ k, k < N → ∀ S : ℝ, 1 ≤ S → ‖a k S‖ ≤ C * S ^ M) :
    ∀ S : ℝ, 1 ≤ S →
      ‖∑ k ∈ Finset.range N, a k S * u S ^ k‖ ≤ ((N : ℝ) * C * (max B 1) ^ N) * S ^ M := by
  intro S hS
  refine le_trans (norm_sum_le _ _) ?_
  have hmax1 : (1 : ℝ) ≤ max B 1 := le_max_right _ _
  have hterm : ∀ k ∈ Finset.range N, ‖a k S * u S ^ k‖ ≤ C * (max B 1) ^ N * S ^ M := by
    intro k hk
    rw [Finset.mem_range] at hk
    rw [norm_mul, norm_pow]
    have h1 : ‖a k S‖ ≤ C * S ^ M := ha k hk S hS
    have h2 : ‖u S‖ ^ k ≤ (max B 1) ^ N := by
      calc ‖u S‖ ^ k ≤ (max B 1) ^ k :=
            pow_le_pow_left₀ (norm_nonneg _) (le_trans (hB S hS) (le_max_left _ _)) k
        _ ≤ (max B 1) ^ N := pow_le_pow_right₀ hmax1 (le_of_lt hk)
    have hS0 : (0 : ℝ) ≤ S := by linarith
    calc ‖a k S‖ * ‖u S‖ ^ k ≤ (C * S ^ M) * (max B 1) ^ N :=
          mul_le_mul h1 h2 (by positivity) (by positivity)
      _ = C * (max B 1) ^ N * S ^ M := by ring
  calc ∑ k ∈ Finset.range N, ‖a k S * u S ^ k‖
      ≤ ∑ _k ∈ Finset.range N, C * (max B 1) ^ N * S ^ M := Finset.sum_le_sum hterm
    _ = (N : ℝ) * C * (max B 1) ^ N * S ^ M := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        ring

/-! ## Bezout survival -/

/-- **Bezout survival.**  If a tuple satisfies a Bezout identity whose cofactors have polynomial
growth, then at every height some component of the tuple is at least an inverse power. -/
theorem exists_bezout_survival {r : ℕ} (A R : Fin r → ℝ → ℂ) {C₁ : ℝ} {M : ℕ} (hC₁ : 0 < C₁)
    (hbez : ∀ S : ℝ, 1 ≤ S → ∑ j, A j S * R j S = 1)
    (hA : ∀ S : ℝ, 1 ≤ S → ∀ j, ‖A j S‖ ≤ C₁ * S ^ M) :
    ∀ S : ℝ, 1 ≤ S → ∃ j, ((r : ℝ) * C₁)⁻¹ * (S ^ M)⁻¹ ≤ ‖R j S‖ := by
  intro S hS
  have hS0 : (0 : ℝ) < S := by linarith
  have hSM : (0 : ℝ) < S ^ M := by positivity
  have hne : (Finset.univ : Finset (Fin r)).Nonempty := by
    rcases Finset.eq_empty_or_nonempty (Finset.univ : Finset (Fin r)) with hemp | hnon
    · exfalso
      have h0 := hbez S hS
      rw [hemp, Finset.sum_empty] at h0
      exact zero_ne_one h0
    · exact hnon
  obtain ⟨j₀, -, hj₀⟩ := Finset.exists_max_image Finset.univ (fun j => ‖R j S‖) hne
  refine ⟨j₀, ?_⟩
  have hrpos : (0 : ℝ) < (r : ℝ) := by
    obtain ⟨j, -⟩ := hne
    have : 0 < r := j.pos
    exact_mod_cast this
  have hchain : (1 : ℝ) ≤ (r : ℝ) * C₁ * S ^ M * ‖R j₀ S‖ := by
    have h1 : (1 : ℝ) = ‖(1 : ℂ)‖ := by simp
    rw [h1, ← hbez S hS]
    refine le_trans (norm_sum_le _ _) ?_
    have hterm : ∀ j ∈ (Finset.univ : Finset (Fin r)),
        ‖A j S * R j S‖ ≤ C₁ * S ^ M * ‖R j₀ S‖ := by
      intro j _
      rw [norm_mul]
      exact mul_le_mul (hA S hS j) (hj₀ j (Finset.mem_univ j)) (norm_nonneg _) (by positivity)
    calc ∑ j, ‖A j S * R j S‖ ≤ ∑ _j : Fin r, C₁ * S ^ M * ‖R j₀ S‖ :=
          Finset.sum_le_sum hterm
      _ = (r : ℝ) * C₁ * S ^ M * ‖R j₀ S‖ := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring
  have hpos : (0 : ℝ) < (r : ℝ) * C₁ * S ^ M := by positivity
  rw [← mul_inv, ← mul_inv, ← one_div, div_le_iff₀ hpos]
  linarith [hchain]

/-! ## Translated polynomial jets -/

/-- **Translated polynomial jets along a height sequence.**  Each upper translate of `b` agrees, on
every compact tube, with the evaluation of one polynomial of degree at most `d`, up to `K · S n^{-L}`
with a constant depending only on the tube radius. -/
structure TranslatedJets (b : ℂ → ℂ) (S : ℕ → ℝ) (d L : ℕ) where
  /-- The jet polynomial at each height. -/
  poly : ℕ → Polynomial ℂ
  /-- The degree bound is independent of the height. -/
  degree_le : ∀ n, (poly n).natDegree ≤ d
  /-- The jet approximates the translate to order `L` on every tube. -/
  approx : ∀ Rad : ℝ, 0 < Rad → ∃ (K : ℝ) (N : ℕ), ∀ n, N ≤ n → ∀ z : ℂ, ‖z‖ ≤ Rad →
    ‖b (z + (S n : ℂ) * Complex.I) - (poly n).eval z‖ ≤ K * (S n) ^ (-(L : ℝ))

end GaloisForLFunctions.HTGeometry
