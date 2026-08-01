import GaloisForLFunctions.HTGeometry.StdRatDatum
import GaloisForLFunctions.HTGeometry.VerticalFlatness

/-!
# A non-flat function with standard approximations has a datum

Suppose a function on a vertical line is approximated, to every depth, by standard rational
functions of a fixed defect — this is what a jet polynomial does — and suppose it is *not* flat, i.e.
it fails to decay faster than some fixed power.  Then it has a datum: there are `p` and `c ≠ 0` with

`s^p · f(s) → c`.

Either some approximant has a nonzero numerator, in which case its own datum passes to `f` because
the error is of higher order; or every numerator vanishes, in which case `f` is bounded by every
power and is flat, contrary to hypothesis.  The dichotomy is decided at a single depth, chosen from
the failing power itself.
-/

open Filter Topology Complex

namespace GaloisForLFunctions

variable {σ : ℝ}

/-- A bound in powers of `1/t` is a bound in the scale of the line. -/
theorem isLineBigO_of_bound {f : ℝ → ℂ} (hσ : 0 < σ) (B : ℝ) (k : ℕ) (hB : 0 ≤ B)
    (hb : ∀ t : ℝ, 2 ≤ t → ‖f t‖ ≤ B * (1 / t) ^ k) : IsLineBigO σ k f := by
  refine ⟨B * (1 + σ) ^ k, ?_⟩
  filter_upwards [eventually_ge_atTop (2 : ℝ), eventually_norm_vertical_le hσ.le] with t ht hv
  have htpos : (0 : ℝ) < t := by linarith
  calc ‖f t‖ * ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ ^ k
      ≤ (B * (1 / t) ^ k) * ((1 + σ) * t) ^ k := by
        refine mul_le_mul (hb t ht) (pow_le_pow_left₀ (norm_nonneg _) hv k) (by positivity)
          (by positivity)
    _ = B * (1 + σ) ^ k := by
        rw [mul_pow, div_pow, one_pow]
        field_simp
        ring

/-- The powers of `1/t` tend to zero. -/
theorem tendsto_one_div_pow (j : ℕ) (hj : 1 ≤ j) :
    Tendsto (fun t : ℝ => (1 / t) ^ j) atTop (nhds 0) := by
  have hinv : Tendsto (fun t : ℝ => 1 / t) atTop (nhds 0) := tendsto_one_div_atTop_nhds_zero_nat
    |>.comp tendsto_natCast_atTop_atTop |>.congr (fun _ => rfl) |>.mono_left le_rfl
  have := hinv.pow j
  rwa [zero_pow (by omega)] at this

/-- **The datum of a non-flat function with standard approximations.** -/
theorem exists_datum_of_not_flat {f : ℝ → ℂ} (hσ : 0 < σ) (W : ℕ)
    (happrox : ∀ K : ℕ, ∃ (P : Polynomial ℂ) (l : Multiset ℕ) (A : ℝ),
      P.natDegree + W ≤ Multiset.card l ∧ 0 ≤ A ∧
      ∀ t : ℝ, 2 ≤ t → ‖f t - P.eval ((σ : ℂ) + (t : ℂ) * Complex.I)
        / shiftProd l ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ A * (1 / t) ^ (W + K))
    {n : ℕ} (hnotflat : ¬ IsLineBigO σ n f) :
    ∃ (p : ℕ) (c : ℂ), c ≠ 0 ∧
      Tendsto (fun t : ℝ => ((σ : ℂ) + (t : ℂ) * Complex.I) ^ p * f t) atTop (nhds c) := by
  obtain ⟨P, l, A, hdeg, hA, hbound⟩ := happrox n
  by_cases hP : P = 0
  · exfalso
    refine hnotflat ?_
    have hz : ∀ t : ℝ, 2 ≤ t → ‖f t‖ ≤ A * (1 / t) ^ (W + n) := by
      intro t ht
      have h := hbound t ht
      rw [hP] at h
      simpa using h
    exact (isLineBigO_of_bound hσ A (W + n) hA hz).mono (by omega)
  · set p : ℕ := Multiset.card l - P.natDegree with hp
    have hcard : Multiset.card l = P.natDegree + p := by omega
    have hpW : W ≤ p := by omega
    by_cases hcase : p < W + n
    · refine ⟨p, P.leadingCoeff, Polynomial.leadingCoeff_ne_zero.mpr hP, ?_⟩
      have hdatum := tendsto_stdRat_datum hσ P l p hcard
      obtain ⟨j, hj⟩ : ∃ j, W + n = p + (j + 1) := ⟨W + n - p - 1, by omega⟩
      have herr : Tendsto (fun t : ℝ => ((σ : ℂ) + (t : ℂ) * Complex.I) ^ p
          * (f t - P.eval ((σ : ℂ) + (t : ℂ) * Complex.I)
            / shiftProd l ((σ : ℂ) + (t : ℂ) * Complex.I))) atTop (nhds 0) := by
        rw [tendsto_zero_iff_norm_tendsto_zero]
        refine squeeze_zero' (Eventually.of_forall fun t => norm_nonneg _) ?_
          (((tendsto_one_div_pow (j + 1) (by omega)).const_mul (A * (1 + σ) ^ p)).congr
            (fun t => rfl) |>.mono_left le_rfl)
        filter_upwards [eventually_ge_atTop (2 : ℝ), eventually_norm_vertical_le hσ.le]
          with t ht hv
        have htpos : (0 : ℝ) < t := by linarith
        have hpow : ‖((σ : ℂ) + (t : ℂ) * Complex.I) ^ p‖ ≤ ((1 + σ) * t) ^ p := by
          rw [norm_pow]
          exact pow_le_pow_left₀ (norm_nonneg _) hv p
        rw [norm_mul]
        calc ‖((σ : ℂ) + (t : ℂ) * Complex.I) ^ p‖
              * ‖f t - P.eval ((σ : ℂ) + (t : ℂ) * Complex.I)
                / shiftProd l ((σ : ℂ) + (t : ℂ) * Complex.I)‖
            ≤ ((1 + σ) * t) ^ p * (A * (1 / t) ^ (W + n)) := by
              refine mul_le_mul hpow (hbound t ht) (norm_nonneg _) (by positivity)
          _ = (A * (1 + σ) ^ p) * (1 / t) ^ (j + 1) := by
              rw [hj, mul_pow, div_pow, one_pow, pow_add, div_pow, one_pow]
              field_simp
              ring
      have hsum := hdatum.add herr
      rw [add_zero] at hsum
      refine hsum.congr fun t => ?_
      ring
    · exfalso
      refine hnotflat ?_
      have hstd : IsStdRat (fun x : ℂ => P.eval x / shiftProd l x) (W + n) :=
        ⟨P, l, by omega, fun x _ => rfl⟩
      obtain ⟨C, hC, hCb⟩ := hstd.exists_norm_le
      have hFu : ∀ t : ℝ, 2 ≤ t → ‖P.eval ((σ : ℂ) + (t : ℂ) * Complex.I)
          / shiftProd l ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C * (1 / t) ^ (W + n) := by
        intro t ht
        have htpos : (0 : ℝ) < t := by linarith
        have hsre : (0 : ℝ) < ((σ : ℂ) + (t : ℂ) * Complex.I).re := by simpa using hσ
        have hge : t ≤ ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ :=
          norm_vertical_add_nat_ge_im (σ := σ) t 0 |>.trans (by simp)
        have hone : (1 : ℝ) ≤ ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ := by linarith
        refine le_trans (hCb _ hsre hone) ?_
        have hinv : ‖(σ : ℂ) + (t : ℂ) * Complex.I‖⁻¹ ≤ 1 / t := by
          rw [inv_eq_one_div]
          exact one_div_le_one_div_of_le htpos hge
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hinv (W + n)) hC
      have hfu : ∀ t : ℝ, 2 ≤ t → ‖f t‖ ≤ (A + C) * (1 / t) ^ (W + n) := by
        intro t ht
        have hsplit : f t = (f t - P.eval ((σ : ℂ) + (t : ℂ) * Complex.I)
            / shiftProd l ((σ : ℂ) + (t : ℂ) * Complex.I))
          + P.eval ((σ : ℂ) + (t : ℂ) * Complex.I)
            / shiftProd l ((σ : ℂ) + (t : ℂ) * Complex.I) := by ring
        rw [hsplit]
        refine le_trans (norm_add_le _ _) ?_
        have h1 := hbound t ht
        have h2 := hFu t ht
        have hpow0 : (0 : ℝ) ≤ (1 / t) ^ (W + n) := by positivity
        nlinarith
      exact (isLineBigO_of_bound hσ (A + C) (W + n) (by linarith) hfu).mono (by omega)

end GaloisForLFunctions
