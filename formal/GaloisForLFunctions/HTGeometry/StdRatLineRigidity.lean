import GaloisForLFunctions.HTGeometry.JetDatumFromNonFlat
import GaloisForLFunctions.HTGeometry.VerticalFlatness

/-!
# Rigidity of standard rational functions across vertical lines

A rational function has one decay order, visible on every vertical line: if its values on a single
line decay faster than its recorded defect, the defect itself was too small.  Consequently a function
approximated to arbitrary depth by standard rational functions cannot decay faster than every power
on one line without doing so on all of them.

This upgrades line data to half-plane data, which is what turns the algebraic statement "no nonzero
jet polynomial is flat on a half-plane" into the analytic statement "on a fixed line, a nonzero jet
polynomial is not of arbitrarily high decay order".
-/

open Filter Topology Complex

namespace GaloisForLFunctions

variable {σ : ℝ}

/-- **Line decay forces the degree defect.**  A standard rational function whose values on one
vertical line decay faster than its recorded defect has the larger defect. -/
theorem isStdRat_of_line_decay (hσ : 0 < σ) {F : ℂ → ℂ} {W K : ℕ} (hF : IsStdRat F W) {C : ℝ}
    (hbound : ∀ᶠ t : ℝ in atTop,
      ‖F ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C * (1 / t) ^ (W + K)) :
    IsStdRat F (W + K) := by
  obtain ⟨P, l, hdeg, hval⟩ := hF
  by_cases hP : P = 0
  · refine ⟨0, Multiset.replicate (W + K) 0, by simp, fun x hx => ?_⟩
    rw [hval x hx, hP]
    simp
  · by_contra hcon
    have hp : Multiset.card l - P.natDegree < W + K := by
      by_contra h
      exact hcon ⟨P, l, by omega, hval⟩
    set p : ℕ := Multiset.card l - P.natDegree with hpdef
    have hcard : Multiset.card l = P.natDegree + p := by omega
    have hdatum := tendsto_stdRat_datum hσ P l p hcard
    have hzero : Tendsto (fun t : ℝ => ((σ : ℂ) + (t : ℂ) * Complex.I) ^ p
        * (P.eval ((σ : ℂ) + (t : ℂ) * Complex.I)
          / shiftProd l ((σ : ℂ) + (t : ℂ) * Complex.I))) atTop (nhds 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      obtain ⟨j, hj⟩ : ∃ j, W + K = p + (j + 1) := ⟨W + K - p - 1, by omega⟩
      have hlim : Tendsto (fun t : ℝ => (C * (1 + σ) ^ p) * (1 / t) ^ (j + 1)) atTop (nhds 0) := by
        have h := (tendsto_one_div_pow (j + 1) (by omega)).const_mul (C * (1 + σ) ^ p)
        rwa [mul_zero] at h
      refine squeeze_zero' (Eventually.of_forall fun t => norm_nonneg _) ?_ hlim
      filter_upwards [eventually_ge_atTop (2 : ℝ), eventually_norm_vertical_le hσ.le, hbound]
        with t ht hv hb
      have htpos : (0 : ℝ) < t := by linarith
      have hsre : (0 : ℝ) < ((σ : ℂ) + (t : ℂ) * Complex.I).re := by simpa using hσ
      have hpow : ‖((σ : ℂ) + (t : ℂ) * Complex.I) ^ p‖ ≤ ((1 + σ) * t) ^ p := by
        rw [norm_pow]
        exact pow_le_pow_left₀ (norm_nonneg _) hv p
      have hFb : ‖P.eval ((σ : ℂ) + (t : ℂ) * Complex.I)
          / shiftProd l ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C * (1 / t) ^ (W + K) := by
        rw [← hval _ hsre]
        exact hb
      rw [norm_mul]
      calc ‖((σ : ℂ) + (t : ℂ) * Complex.I) ^ p‖
            * ‖P.eval ((σ : ℂ) + (t : ℂ) * Complex.I)
              / shiftProd l ((σ : ℂ) + (t : ℂ) * Complex.I)‖
          ≤ ((1 + σ) * t) ^ p * (C * (1 / t) ^ (W + K)) := by
            refine mul_le_mul hpow hFb (norm_nonneg _) (by positivity)
        _ = (C * (1 + σ) ^ p) * (1 / t) ^ (j + 1) := by
            rw [hj, mul_pow, div_pow, one_pow, pow_add, div_pow, one_pow]
            field_simp
    exact Polynomial.leadingCoeff_ne_zero.mpr hP (tendsto_nhds_unique hdatum hzero)

/-- **From a line to the half-plane.**  A function with standard rational approximations of every
depth that decays faster than every power on one vertical line is flat on every vertical line. -/
theorem isVertFlat_of_isLineBigO_all (hσ : 0 < σ) {W : ℕ} {g : ℂ → ℂ}
    (hpkg : ∀ K : ℕ, ∃ (F : ℂ → ℂ) (A : ℝ), IsStdRat F W ∧ 0 ≤ A ∧ ∀ σ' t : ℝ, 0 < σ' → 2 ≤ t →
      ‖g ((σ' : ℂ) + (t : ℂ) * Complex.I) - F ((σ' : ℂ) + (t : ℂ) * Complex.I)‖
        ≤ A * (1 / t) ^ (W + K))
    (hflat : ∀ n : ℕ, IsLineBigO σ n (fun t : ℝ => g ((σ : ℂ) + (t : ℂ) * Complex.I)))
    {σ₀ : ℝ} (hσ₀ : 0 < σ₀) : IsVertFlat σ₀ g := by
  intro N σ' hσ'
  have hσ'pos : (0 : ℝ) < σ' := lt_of_lt_of_le hσ₀ hσ'
  obtain ⟨F, A, hstd, hA, hpkgK⟩ := hpkg (N + 1)
  obtain ⟨C, hCb⟩ := hflat (W + (N + 1))
  -- the approximation is forced to have the higher defect
  have hline : ∀ᶠ t : ℝ in atTop,
      ‖F ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ (A + C) * (1 / t) ^ (W + (N + 1)) := by
    filter_upwards [eventually_ge_atTop (2 : ℝ), hCb] with t ht hb
    have htpos : (0 : ℝ) < t := by linarith
    have hge : t ≤ ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ :=
      (norm_vertical_add_nat_ge_im (σ := σ) t 0).trans (by simp)
    have hgb : ‖g ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C * (1 / t) ^ (W + (N + 1)) := by
      have hpow : (t : ℝ) ^ (W + (N + 1)) ≤ ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ ^ (W + (N + 1)) :=
        pow_le_pow_left₀ (by linarith) hge _
      have hg0 : (0 : ℝ) ≤ ‖g ((σ : ℂ) + (t : ℂ) * Complex.I)‖ := norm_nonneg _
      have hmul : ‖g ((σ : ℂ) + (t : ℂ) * Complex.I)‖ * t ^ (W + (N + 1)) ≤ C := by
        refine le_trans ?_ hb
        exact mul_le_mul_of_nonneg_left hpow hg0
      rw [div_pow, one_pow, mul_one_div, le_div_iff₀ (by positivity)]
      linarith
    have hsplit : F ((σ : ℂ) + (t : ℂ) * Complex.I)
        = g ((σ : ℂ) + (t : ℂ) * Complex.I)
          - (g ((σ : ℂ) + (t : ℂ) * Complex.I) - F ((σ : ℂ) + (t : ℂ) * Complex.I)) := by
      ring
    rw [hsplit]
    refine le_trans (norm_sub_le _ _) ?_
    have h1 := hpkgK σ t hσ ht
    have h2 : (0 : ℝ) ≤ (1 / t) ^ (W + (N + 1)) := by positivity
    nlinarith
  have hstd' : IsStdRat F (W + (N + 1)) := isStdRat_of_line_decay hσ hstd hline
  obtain ⟨D, hD, hDb⟩ := hstd'.exists_norm_le
  -- transfer the decay to the line σ'
  have hbound : ∀ t : ℝ, 2 ≤ t →
      ‖g ((σ' : ℂ) + (t : ℂ) * Complex.I)‖ ≤ (A + D) * (1 / t) ^ (W + (N + 1)) := by
    intro t ht
    have htpos : (0 : ℝ) < t := by linarith
    have hsre : (0 : ℝ) < ((σ' : ℂ) + (t : ℂ) * Complex.I).re := by simpa using hσ'pos
    have hge : t ≤ ‖(σ' : ℂ) + (t : ℂ) * Complex.I‖ :=
      (norm_vertical_add_nat_ge_im (σ := σ') t 0).trans (by simp)
    have hone : (1 : ℝ) ≤ ‖(σ' : ℂ) + (t : ℂ) * Complex.I‖ := by linarith
    have hFb : ‖F ((σ' : ℂ) + (t : ℂ) * Complex.I)‖ ≤ D * (1 / t) ^ (W + (N + 1)) := by
      refine le_trans (hDb _ hsre hone) ?_
      have hinv : ‖(σ' : ℂ) + (t : ℂ) * Complex.I‖⁻¹ ≤ 1 / t := by
        rw [inv_eq_one_div]
        exact one_div_le_one_div_of_le htpos hge
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hinv _) hD
    have hsplit : g ((σ' : ℂ) + (t : ℂ) * Complex.I)
        = (g ((σ' : ℂ) + (t : ℂ) * Complex.I) - F ((σ' : ℂ) + (t : ℂ) * Complex.I))
          + F ((σ' : ℂ) + (t : ℂ) * Complex.I) := by
      ring
    rw [hsplit]
    refine le_trans (norm_add_le _ _) ?_
    have h1 := hpkgK σ' t hσ'pos ht
    have h2 : (0 : ℝ) ≤ (1 / t) ^ (W + (N + 1)) := by positivity
    nlinarith
  -- and conclude the flat limit on that line
  have hlim : Tendsto (fun t : ℝ => (A + D) * (1 / t) ^ 1) atTop (nhds 0) := by
    have h := (tendsto_one_div_pow 1 (le_refl 1)).const_mul (A + D)
    rwa [mul_zero] at h
  refine squeeze_zero' ((eventually_ge_atTop (0 : ℝ)).mono
    fun t ht => mul_nonneg (pow_nonneg ht N) (norm_nonneg _)) ?_ hlim
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with t ht
  have htpos : (0 : ℝ) < t := by linarith
  have hb := hbound t ht
  have hpow : t ^ N * ((1 / t) ^ (W + (N + 1))) ≤ (1 / t) ^ 1 := by
    have ht0 : t ≠ 0 := by linarith
    have hkey : t ^ N * ((1 / t) ^ (W + (N + 1))) = 1 / t ^ (W + 1) := by
      have h1 : (1 / t) ^ (W + (N + 1)) = 1 / t ^ (W + (N + 1)) := by
        rw [div_pow, one_pow]
      rw [h1, mul_one_div, div_eq_div_iff (by positivity) (by positivity), one_mul, ← pow_add]
      congr 1
      omega
    rw [hkey, pow_one]
    exact one_div_le_one_div_of_le htpos (le_self_pow₀ (by linarith) (by omega))
  calc t ^ N * ‖g ((σ' : ℂ) + (t : ℂ) * Complex.I)‖
      ≤ t ^ N * ((A + D) * (1 / t) ^ (W + (N + 1))) := by
        refine mul_le_mul_of_nonneg_left hb (by positivity)
    _ = (A + D) * (t ^ N * (1 / t) ^ (W + (N + 1))) := by ring
    _ ≤ (A + D) * (1 / t) ^ 1 := by
        refine mul_le_mul_of_nonneg_left hpow (by linarith)

end GaloisForLFunctions
