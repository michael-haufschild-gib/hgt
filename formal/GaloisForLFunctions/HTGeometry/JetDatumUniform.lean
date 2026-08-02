import GaloisForLFunctions.HTGeometry.JetDatumFromNonFlat
import GaloisForLFunctions.HTGeometry.StdRatDatumUniform
import GaloisForLFunctions.HTGeometry.JetPolyCoeffDatum

/-!
# The datum of a non-flat function, uniformly on a vertical tube

The dichotomy that turns a standard approximation into a datum needs the failing power at only *one*
line: the approximating standard rational function is chosen once, independently of the abscissa, so
its numerator either vanishes at that depth — and then the function is flat on **every** line — or it
does not, and its own datum passes to the function on every line at once.

With the uniform extraction of the standard datum this gives the tube form: one exponent `p`, one
nonzero residue `c`, and a height beyond which `s^p·f(σ+it)` is within `ε` of `c` for all abscissas in
the tube simultaneously.
-/

open Filter Set Topology Function

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

/-- On a vertical tube the modulus is at most `(1+M)` times the ordinate. -/
theorem norm_vertical_le_of_le {σ M t : ℝ} (hσ : 0 < σ) (hσM : σ ≤ M) (ht : 1 ≤ t) :
    ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ ≤ (1 + M) * t := by
  have htpos : (0 : ℝ) < t := lt_of_lt_of_le zero_lt_one ht
  have h := norm_add_le ((σ : ℂ)) ((t : ℂ) * Complex.I)
  have h1 : ‖(σ : ℂ)‖ = σ := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hσ]
  have h2 : ‖(t : ℂ) * Complex.I‖ = t := by
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos htpos]
  rw [h1, h2] at h
  nlinarith

/-- **The datum of a non-flat function with abscissa-free standard approximations, uniformly on a
tube.**  The approximants and their constants do not depend on the abscissa; non-flatness is needed
on a single line, and the resulting datum holds uniformly on every tube. -/
theorem exists_uniform_datum_of_not_flat {f : ℝ → ℝ → ℂ} {M σ₀ : ℝ} (hM : 0 < M) (hσ₀ : 0 < σ₀)
    (W : ℕ)
    (happrox : ∀ K : ℕ, ∃ (P : Polynomial ℂ) (l : Multiset ℕ) (A : ℝ),
      P.natDegree + W ≤ Multiset.card l ∧ 0 ≤ A ∧
      ∀ σ t : ℝ, 0 < σ → 2 ≤ t →
        ‖f σ t - P.eval ((σ : ℂ) + (t : ℂ) * Complex.I)
          / shiftProd l ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ A * (1 / t) ^ (W + K))
    {n : ℕ} (hnotflat : ¬ IsLineBigO σ₀ n (f σ₀)) :
    ∃ (p : ℕ) (c : ℂ), c ≠ 0 ∧ ∀ ε : ℝ, 0 < ε → ∃ T : ℝ, ∀ σ t : ℝ, 0 < σ → σ ≤ M → T ≤ t →
      ‖((σ : ℂ) + (t : ℂ) * Complex.I) ^ p * f σ t - c‖ ≤ ε := by
  classical
  obtain ⟨P, l, A, hdeg, hA, hbound⟩ := happrox n
  by_cases hP : P = 0
  · exfalso
    refine hnotflat ?_
    have hz : ∀ t : ℝ, 2 ≤ t → ‖f σ₀ t‖ ≤ A * (1 / t) ^ (W + n) := by
      intro t ht
      have h := hbound σ₀ t hσ₀ ht
      rw [hP] at h
      simpa using h
    exact (isLineBigO_of_bound hσ₀ A (W + n) hA hz).mono (by omega)
  · set p : ℕ := Multiset.card l - P.natDegree with hp
    have hcard : Multiset.card l = P.natDegree + p := by omega
    have hpW : W ≤ p := by omega
    by_cases hcase : p < W + n
    · refine ⟨p, P.leadingCoeff, Polynomial.leadingCoeff_ne_zero.mpr hP, fun ε hε => ?_⟩
      obtain ⟨j, hj⟩ : ∃ j, W + n = p + (j + 1) := ⟨W + n - p - 1, by omega⟩
      obtain ⟨T₁, hT₁⟩ := exists_uniform_height_stdRat_datum P l p hcard (half_pos hε)
      set D : ℝ := A * (1 + M) ^ p with hD
      have hD0 : 0 ≤ D := by positivity
      refine ⟨max (max 2 T₁) (2 * D / ε + 1), fun σ t hσ hσM ht => ?_⟩
      have ht2 : (2 : ℝ) ≤ t := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) ht
      have htT₁ : T₁ ≤ t := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) ht
      have htD : 2 * D / ε + 1 ≤ t := le_trans (le_max_right _ _) ht
      have ht1 : (1 : ℝ) ≤ t := by linarith
      have htpos : (0 : ℝ) < t := by linarith
      set s : ℂ := (σ : ℂ) + (t : ℂ) * Complex.I with hs
      -- split into the approximation error and the standard datum
      have hsplit : s ^ p * f σ t - P.leadingCoeff
          = s ^ p * (f σ t - P.eval s / shiftProd l s)
            + (s ^ p * (P.eval s / shiftProd l s) - P.leadingCoeff) := by
        ring
      rw [hsplit]
      refine le_trans (norm_add_le _ _) ?_
      have herr : ‖s ^ p * (f σ t - P.eval s / shiftProd l s)‖ ≤ D / t := by
        rw [norm_mul, norm_pow]
        have hpow : ‖s‖ ^ p ≤ ((1 + M) * t) ^ p :=
          pow_le_pow_left₀ (norm_nonneg _) (norm_vertical_le_of_le hσ hσM ht1) p
        refine le_trans (mul_le_mul hpow (hbound σ t hσ ht2) (norm_nonneg _) (by positivity)) ?_
        have hEq : ((1 + M) * t) ^ p * (A * (1 / t) ^ (W + n)) = D * (1 / t) ^ (j + 1) := by
          rw [hj, hD, mul_pow, div_pow, one_pow, pow_add, div_pow, one_pow]
          field_simp
        rw [hEq]
        have hpj : (1 / t) ^ (j + 1) ≤ 1 / t := by
          calc (1 / t) ^ (j + 1) ≤ (1 / t) ^ 1 := by
                refine pow_le_pow_of_le_one (by positivity) ?_ (by omega)
                rw [div_le_one htpos]
                exact ht1
            _ = 1 / t := pow_one _
        calc D * (1 / t) ^ (j + 1) ≤ D * (1 / t) := mul_le_mul_of_nonneg_left hpj hD0
          _ = D / t := by rw [mul_one_div]
      have hdat : ‖s ^ p * (P.eval s / shiftProd l s) - P.leadingCoeff‖ ≤ ε / 2 :=
        hT₁ σ t hσ htT₁
      have hDt : D / t ≤ ε / 2 := by
        rw [div_le_div_iff₀ htpos (by norm_num : (0:ℝ) < 2)]
        have h2D : 2 * D / ε ≤ t := by linarith
        rw [div_le_iff₀ hε] at h2D
        nlinarith
      linarith
    · exfalso
      refine hnotflat ?_
      have hstd : IsStdRat (fun x : ℂ => P.eval x / shiftProd l x) (W + n) :=
        ⟨P, l, by omega, fun x _ => rfl⟩
      obtain ⟨C, hC, hCb⟩ := hstd.exists_norm_le
      have hFu : ∀ t : ℝ, 2 ≤ t → ‖P.eval ((σ₀ : ℂ) + (t : ℂ) * Complex.I)
          / shiftProd l ((σ₀ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C * (1 / t) ^ (W + n) := by
        intro t ht
        have htpos : (0 : ℝ) < t := by linarith
        have hsre : (0 : ℝ) < ((σ₀ : ℂ) + (t : ℂ) * Complex.I).re := by simpa using hσ₀
        have hge : t ≤ ‖(σ₀ : ℂ) + (t : ℂ) * Complex.I‖ := norm_vertical_ge_im σ₀ t
        have hone : (1 : ℝ) ≤ ‖(σ₀ : ℂ) + (t : ℂ) * Complex.I‖ := by linarith
        refine le_trans (hCb _ hsre hone) ?_
        have hinv : ‖(σ₀ : ℂ) + (t : ℂ) * Complex.I‖⁻¹ ≤ 1 / t := by
          rw [inv_eq_one_div]
          exact one_div_le_one_div_of_le htpos hge
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hinv (W + n)) hC
      have hfu : ∀ t : ℝ, 2 ≤ t → ‖f σ₀ t‖ ≤ (A + C) * (1 / t) ^ (W + n) := by
        intro t ht
        have hsplit : f σ₀ t = (f σ₀ t - P.eval ((σ₀ : ℂ) + (t : ℂ) * Complex.I)
            / shiftProd l ((σ₀ : ℂ) + (t : ℂ) * Complex.I))
          + P.eval ((σ₀ : ℂ) + (t : ℂ) * Complex.I)
            / shiftProd l ((σ₀ : ℂ) + (t : ℂ) * Complex.I) := by ring
        rw [hsplit]
        refine le_trans (norm_add_le _ _) ?_
        have h1 := hbound σ₀ t hσ₀ ht
        have h2 := hFu t ht
        have hpow0 : (0 : ℝ) ≤ (1 / t) ^ (W + n) := by positivity
        nlinarith
      exact (isLineBigO_of_bound hσ₀ (A + C) (W + n) (by linarith) hfu).mono (by omega)

end

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

/-- **The datum of a non-flat jet polynomial, uniformly on a vertical tube.**  Eq. (19) for constant
coefficients in the tube form: one exponent, one nonzero residue, and a height beyond which the
normalized jet polynomial is within `ε` of that residue for every abscissa in the tube at once.  Only
non-flatness on a single line goes in. -/
theorem exists_uniform_jetPoly_datum {M σ₀ : ℝ} (hM : 0 < M) (hσ₀ : 0 < σ₀)
    (N Mm W : ℕ) (e : Fin Mm → Fin N → ℕ) (a : Fin Mm → ℂ)
    (hW : ∀ α : Fin Mm, W ≤ ∑ i : Fin N, ((i : ℕ) + 1) * e α i) {n : ℕ}
    (hnotflat : ¬ IsLineBigO σ₀ n (fun t : ℝ => ∑ α : Fin Mm, a α * ∏ i : Fin N,
      iteratedDeriv ((i : ℕ) + 1) Complex.digamma ((σ₀ : ℂ) + (t : ℂ) * Complex.I) ^ e α i)) :
    ∃ (p : ℕ) (c : ℂ), c ≠ 0 ∧ ∀ ε : ℝ, 0 < ε → ∃ T : ℝ, ∀ σ t : ℝ, 0 < σ → σ ≤ M → T ≤ t →
      ‖((σ : ℂ) + (t : ℂ) * Complex.I) ^ p
          * (∑ α : Fin Mm, a α * ∏ i : Fin N,
            iteratedDeriv ((i : ℕ) + 1) Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I) ^ e α i)
        - c‖ ≤ ε := by
  refine exists_uniform_datum_of_not_flat (f := fun σ t => ∑ α : Fin Mm, a α * ∏ i : Fin N,
    iteratedDeriv ((i : ℕ) + 1) Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I) ^ e α i)
    hM hσ₀ W (fun K => ?_) hnotflat
  obtain ⟨F, A, hFstd, hA, hFbound⟩ := exists_jetPoly_package N Mm K W e a hW
  obtain ⟨P, l, hdeg, hval⟩ := hFstd
  refine ⟨P, l, A, hdeg, le_trans zero_le_one hA, fun σ t hσ ht => ?_⟩
  have hsre : (0 : ℝ) < ((σ : ℂ) + (t : ℂ) * Complex.I).re := by simpa using hσ
  have hFval := hval ((σ : ℂ) + (t : ℂ) * Complex.I) hsre
  rw [← hFval]
  exact hFbound σ t hσ ht

end

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

/-- **The datum of a non-flat jet polynomial with rational coefficients, uniformly on a vertical
tube.**  Eq. (19) in the tube form for the whole coefficient field: clearing denominators turns the
coefficients into polynomials over a common power `s^d`, and the resulting family is approximated by
abscissa-free standard rational functions, so the uniform dichotomy applies verbatim. -/
theorem exists_uniform_jetPolyCoeff_datum {M σ₀ : ℝ} (hM : 0 < M) (hσ₀ : 0 < σ₀)
    (N Mm W d : ℕ) (e : Fin Mm → Fin N → ℕ) (a : Fin Mm → Polynomial ℂ)
    (hdeg : ∀ α : Fin Mm, (a α).natDegree ≤ d)
    (hW : ∀ α : Fin Mm, W ≤ ∑ i : Fin N, ((i : ℕ) + 1) * e α i) {n : ℕ}
    (hnotflat : ¬ IsLineBigO σ₀ n (fun t : ℝ => ∑ α : Fin Mm,
      ((a α).eval ((σ₀ : ℂ) + (t : ℂ) * Complex.I) / ((σ₀ : ℂ) + (t : ℂ) * Complex.I) ^ d)
        * ∏ i : Fin N, iteratedDeriv ((i : ℕ) + 1) Complex.digamma
          ((σ₀ : ℂ) + (t : ℂ) * Complex.I) ^ e α i)) :
    ∃ (p : ℕ) (c : ℂ), c ≠ 0 ∧ ∀ ε : ℝ, 0 < ε → ∃ T : ℝ, ∀ σ t : ℝ, 0 < σ → σ ≤ M → T ≤ t →
      ‖((σ : ℂ) + (t : ℂ) * Complex.I) ^ p
          * (∑ α : Fin Mm, ((a α).eval ((σ : ℂ) + (t : ℂ) * Complex.I)
              / ((σ : ℂ) + (t : ℂ) * Complex.I) ^ d)
            * ∏ i : Fin N, iteratedDeriv ((i : ℕ) + 1) Complex.digamma
              ((σ : ℂ) + (t : ℂ) * Complex.I) ^ e α i)
        - c‖ ≤ ε := by
  refine exists_uniform_datum_of_not_flat (f := fun σ t => ∑ α : Fin Mm,
    ((a α).eval ((σ : ℂ) + (t : ℂ) * Complex.I) / ((σ : ℂ) + (t : ℂ) * Complex.I) ^ d)
      * ∏ i : Fin N, iteratedDeriv ((i : ℕ) + 1) Complex.digamma
        ((σ : ℂ) + (t : ℂ) * Complex.I) ^ e α i)
    hM hσ₀ W (fun K => ?_) hnotflat
  obtain ⟨F, A, hFstd, hA, hFbound⟩ := exists_jetPolyCoeff_package N Mm K W d e a hdeg hW
  obtain ⟨P, l, hdegP, hval⟩ := hFstd
  refine ⟨P, l, A, hdegP, le_trans zero_le_one hA, fun σ t hσ ht => ?_⟩
  have hsre : (0 : ℝ) < ((σ : ℂ) + (t : ℂ) * Complex.I).re := by simpa using hσ
  rw [← hval ((σ : ℂ) + (t : ℂ) * Complex.I) hsre]
  exact hFbound σ t hσ ht

end

end GaloisForLFunctions.HTGeometry
