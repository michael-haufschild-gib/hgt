import GaloisForLFunctions.HTGeometry.JetPolynomialDatum

/-!
# Jet polynomials with polynomial coefficients

Clearing denominators turns `ℂ(s)` coefficients into polynomial ones, and dividing by a common power
`s^d` of the argument normalizes them: `a(s)/s^d` is standard of defect zero, hence bounded on the
line.  Multiplying the monomial packages by such bounded factors keeps the approximation and the
error orders, so the normalized jet polynomial

`∑_α (a_α(s)/s^d)·∏_i (ψ^{(i+1)})^{e_{α i}}`

is again approximated to every depth by a standard rational function of the minimal weight, and the
datum dichotomy applies to it unchanged.
-/

open Filter Topology Complex

namespace GaloisForLFunctions

variable {σ : ℝ}

/-- **The package with polynomial coefficients.** -/
theorem exists_jetPolyCoeff_package (N M K W d : ℕ) (e : Fin M → Fin N → ℕ)
    (a : Fin M → Polynomial ℂ) (hdeg : ∀ α : Fin M, (a α).natDegree ≤ d)
    (hW : ∀ α : Fin M, W ≤ ∑ i : Fin N, ((i : ℕ) + 1) * e α i) :
    ∃ (F : ℂ → ℂ) (A : ℝ), IsStdRat F W ∧ 1 ≤ A ∧ ∀ σ t : ℝ, 0 < σ → 2 ≤ t →
      ‖(∑ α : Fin M, ((a α).eval ((σ : ℂ) + (t : ℂ) * Complex.I)
            / ((σ : ℂ) + (t : ℂ) * Complex.I) ^ d)
          * ∏ i : Fin N, iteratedDeriv ((i : ℕ) + 1) Complex.digamma
              ((σ : ℂ) + (t : ℂ) * Complex.I) ^ e α i)
          - F ((σ : ℂ) + (t : ℂ) * Complex.I)‖
        ≤ A * (1 / t) ^ (W + K) := by
  classical
  choose F A hstd hA hpkg using fun α : Fin M => exists_monomial_package N K (e α)
  choose C hC hCb using fun α : Fin M =>
    (isStdRat_poly_div_pow (a α) d (hdeg α)).exists_norm_le
  refine ⟨fun x => ∑ α : Fin M, ((a α).eval x / x ^ d) * F α x,
    1 + ∑ α : Fin M, C α * A α, ?_, ?_, fun σ t hσ ht => ?_⟩
  · refine IsStdRat.sum Finset.univ _ fun α _ => ?_
    have hmul := (isStdRat_poly_div_pow (a α) d (hdeg α)).mul (hstd α)
    exact hmul.mono (by have := hW α; omega)
  · have hnn : (0 : ℝ) ≤ ∑ α : Fin M, C α * A α :=
      Finset.sum_nonneg fun α _ => by
        have h1 := hC α
        have h2 := le_trans zero_le_one (hA α)
        positivity
    linarith
  · have htpos : (0 : ℝ) < t := by linarith
    have hu0 : (0 : ℝ) ≤ 1 / t := by positivity
    have hu1 : (1 : ℝ) / t ≤ 1 := by
      rw [div_le_one htpos]
      linarith
    have hsre : (0 : ℝ) < ((σ : ℂ) + (t : ℂ) * Complex.I).re := by simpa using hσ
    have hone : (1 : ℝ) ≤ ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ := by
      have := norm_vertical_add_nat_ge_im (σ := σ) t 0
      simp only [Nat.cast_zero, add_zero] at this
      linarith
    have hcoeff : ∀ α : Fin M, ‖(a α).eval ((σ : ℂ) + (t : ℂ) * Complex.I)
        / ((σ : ℂ) + (t : ℂ) * Complex.I) ^ d‖ ≤ C α := by
      intro α
      have h := hCb α _ hsre hone
      simpa using h
    have hsplit : (∑ α : Fin M, ((a α).eval ((σ : ℂ) + (t : ℂ) * Complex.I)
            / ((σ : ℂ) + (t : ℂ) * Complex.I) ^ d)
          * ∏ i : Fin N, iteratedDeriv ((i : ℕ) + 1) Complex.digamma
              ((σ : ℂ) + (t : ℂ) * Complex.I) ^ e α i)
        - (∑ α : Fin M, ((a α).eval ((σ : ℂ) + (t : ℂ) * Complex.I)
            / ((σ : ℂ) + (t : ℂ) * Complex.I) ^ d) * F α ((σ : ℂ) + (t : ℂ) * Complex.I))
        = ∑ α : Fin M, ((a α).eval ((σ : ℂ) + (t : ℂ) * Complex.I)
            / ((σ : ℂ) + (t : ℂ) * Complex.I) ^ d)
          * ((∏ i : Fin N, iteratedDeriv ((i : ℕ) + 1) Complex.digamma
              ((σ : ℂ) + (t : ℂ) * Complex.I) ^ e α i)
            - F α ((σ : ℂ) + (t : ℂ) * Complex.I)) := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun α _ => ?_
      ring
    show ‖(∑ α : Fin M, ((a α).eval ((σ : ℂ) + (t : ℂ) * Complex.I)
          / ((σ : ℂ) + (t : ℂ) * Complex.I) ^ d)
        * ∏ i : Fin N, iteratedDeriv ((i : ℕ) + 1) Complex.digamma
            ((σ : ℂ) + (t : ℂ) * Complex.I) ^ e α i)
      - ∑ α : Fin M, ((a α).eval ((σ : ℂ) + (t : ℂ) * Complex.I)
          / ((σ : ℂ) + (t : ℂ) * Complex.I) ^ d) * F α ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ _
    rw [hsplit]
    refine le_trans (norm_sum_le _ _) ?_
    have hterm : ∀ α : Fin M, ‖((a α).eval ((σ : ℂ) + (t : ℂ) * Complex.I)
          / ((σ : ℂ) + (t : ℂ) * Complex.I) ^ d)
        * ((∏ i : Fin N, iteratedDeriv ((i : ℕ) + 1) Complex.digamma
            ((σ : ℂ) + (t : ℂ) * Complex.I) ^ e α i)
          - F α ((σ : ℂ) + (t : ℂ) * Complex.I))‖
        ≤ (C α * A α) * (1 / t) ^ (W + K) := by
      intro α
      rw [norm_mul]
      have hpow : (1 / t) ^ ((∑ i : Fin N, ((i : ℕ) + 1) * e α i) + K) ≤ (1 / t) ^ (W + K) :=
        pow_le_pow_of_le_one hu0 hu1 (by have := hW α; omega)
      have hstep : ‖(∏ i : Fin N, iteratedDeriv ((i : ℕ) + 1) Complex.digamma
            ((σ : ℂ) + (t : ℂ) * Complex.I) ^ e α i)
          - F α ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ A α * (1 / t) ^ (W + K) := by
        refine le_trans (hpkg α σ t hσ ht) ?_
        exact mul_le_mul_of_nonneg_left hpow (le_trans zero_le_one (hA α))
      calc ‖(a α).eval ((σ : ℂ) + (t : ℂ) * Complex.I)
              / ((σ : ℂ) + (t : ℂ) * Complex.I) ^ d‖
            * ‖(∏ i : Fin N, iteratedDeriv ((i : ℕ) + 1) Complex.digamma
              ((σ : ℂ) + (t : ℂ) * Complex.I) ^ e α i)
            - F α ((σ : ℂ) + (t : ℂ) * Complex.I)‖
          ≤ C α * (A α * (1 / t) ^ (W + K)) := by
            refine mul_le_mul (hcoeff α) hstep (norm_nonneg _) (hC α)
        _ = (C α * A α) * (1 / t) ^ (W + K) := by ring
    refine le_trans (Finset.sum_le_sum fun α _ => hterm α) ?_
    rw [← Finset.sum_mul]
    have hle : (∑ α : Fin M, C α * A α) ≤ 1 + ∑ α : Fin M, C α * A α := by linarith
    exact mul_le_mul_of_nonneg_right hle (by positivity)

/-- **The datum of a non-flat jet polynomial with polynomial coefficients.** -/
theorem exists_jetPolyCoeff_datum (hσ : 0 < σ) (N M W d : ℕ) (e : Fin M → Fin N → ℕ)
    (a : Fin M → Polynomial ℂ) (hdeg : ∀ α : Fin M, (a α).natDegree ≤ d)
    (hW : ∀ α : Fin M, W ≤ ∑ i : Fin N, ((i : ℕ) + 1) * e α i) {n : ℕ}
    (hnotflat : ¬ IsLineBigO σ n (fun t : ℝ => ∑ α : Fin M,
      ((a α).eval ((σ : ℂ) + (t : ℂ) * Complex.I) / ((σ : ℂ) + (t : ℂ) * Complex.I) ^ d)
        * ∏ i : Fin N, iteratedDeriv ((i : ℕ) + 1) Complex.digamma
          ((σ : ℂ) + (t : ℂ) * Complex.I) ^ e α i)) :
    ∃ (p : ℕ) (c : ℂ), c ≠ 0 ∧
      Tendsto (fun t : ℝ => ((σ : ℂ) + (t : ℂ) * Complex.I) ^ p
        * ∑ α : Fin M, ((a α).eval ((σ : ℂ) + (t : ℂ) * Complex.I)
            / ((σ : ℂ) + (t : ℂ) * Complex.I) ^ d)
          * ∏ i : Fin N, iteratedDeriv ((i : ℕ) + 1) Complex.digamma
            ((σ : ℂ) + (t : ℂ) * Complex.I) ^ e α i)
        atTop (nhds c) := by
  refine exists_datum_of_not_flat hσ W (fun K => ?_) hnotflat
  obtain ⟨F, A, hFstd, hA, hFbound⟩ := exists_jetPolyCoeff_package N M K W d e a hdeg hW
  obtain ⟨P, l, hdegP, hval⟩ := hFstd
  refine ⟨P, l, A, hdegP, le_trans zero_le_one hA, fun t ht => ?_⟩
  have hsre : (0 : ℝ) < ((σ : ℂ) + (t : ℂ) * Complex.I).re := by simpa using hσ
  rw [← hval ((σ : ℂ) + (t : ℂ) * Complex.I) hsre]
  exact hFbound σ t hσ ht

end GaloisForLFunctions
