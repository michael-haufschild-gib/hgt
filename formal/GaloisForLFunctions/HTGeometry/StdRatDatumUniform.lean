import GaloisForLFunctions.HTGeometry.StdRatDatum
import GaloisForLFunctions.HTGeometry.PolygammaUniformLeadingAsymptotic

/-!
# The datum of a standard rational function, uniformly in the abscissa

The extraction step `s^p·P(s)/∏_j(s+j) → leadingCoeff P` is proved on a fixed vertical line.  Its two
factors are elementary and both estimates are *uniform*: a polynomial divided by its degree power
differs from its leading coefficient by `O(1/t)` with a constant depending only on the polynomial,
and a shift product divided by its length power differs from `1` by `O(1/t)` with a constant
depending only on the multiset.  Neither constant sees the abscissa, because the only property of the
line used is `‖σ+it‖ ≥ t`.

So the datum extraction holds uniformly on every vertical tube, which is the form the tube version of
eq. (19) consumes.
-/

open Filter Set Topology Function

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

/-- Uniform form of "a polynomial against its degree power tends to its leading coefficient". -/
theorem exists_uniform_bound_polynomial_mul_inv_pow (P : Polynomial ℂ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ σ t : ℝ, 0 < σ → 1 ≤ t →
      ‖P.eval ((σ : ℂ) + (t : ℂ) * Complex.I)
          * (((σ : ℂ) + (t : ℂ) * Complex.I)⁻¹) ^ P.natDegree - P.leadingCoeff‖ ≤ B / t := by
  classical
  refine ⟨∑ i ∈ Finset.range P.natDegree, ‖P.coeff i‖, by positivity, fun σ t hσ ht => ?_⟩
  set s : ℂ := (σ : ℂ) + (t : ℂ) * Complex.I with hs
  have htpos : (0 : ℝ) < t := lt_of_lt_of_le zero_lt_one ht
  have hsge : t ≤ ‖s‖ := norm_vertical_ge_im σ t
  have hsne : s ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hsge
    linarith
  -- expand the polynomial and cancel the leading term
  have hexpand : P.eval s * (s⁻¹) ^ P.natDegree - P.leadingCoeff
      = ∑ i ∈ Finset.range P.natDegree, P.coeff i * (s⁻¹) ^ (P.natDegree - i) := by
    rw [Polynomial.eval_eq_sum_range, Finset.sum_mul, Finset.sum_range_succ]
    have hterm : ∀ i ∈ Finset.range P.natDegree,
        P.coeff i * s ^ i * (s⁻¹) ^ P.natDegree = P.coeff i * (s⁻¹) ^ (P.natDegree - i) := by
      intro i hi
      have hle : i ≤ P.natDegree := le_of_lt (Finset.mem_range.mp hi)
      have hpow : s ^ P.natDegree = s ^ i * s ^ (P.natDegree - i) := by
        rw [← pow_add]
        congr 1
        omega
      rw [inv_pow, inv_pow, hpow, mul_inv, ← mul_assoc, mul_assoc (P.coeff i),
        mul_inv_cancel₀ (pow_ne_zero i hsne), mul_one]
    rw [Finset.sum_congr rfl hterm]
    have hlead : P.coeff P.natDegree * s ^ P.natDegree * (s⁻¹) ^ P.natDegree = P.leadingCoeff := by
      rw [inv_pow, mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hsne), mul_one]
      rfl
    rw [hlead]
    ring
  rw [hexpand]
  refine le_trans (norm_sum_le _ _) ?_
  rw [Finset.sum_div]
  refine Finset.sum_le_sum fun i hi => ?_
  have hlt : i < P.natDegree := Finset.mem_range.mp hi
  obtain ⟨k, hk⟩ : ∃ k, P.natDegree - i = k + 1 := ⟨P.natDegree - i - 1, by omega⟩
  rw [norm_mul, hk, norm_pow, norm_inv]
  have hinvle : ‖s‖⁻¹ ≤ 1 / t := by
    rw [inv_eq_one_div]
    exact one_div_le_one_div_of_le htpos hsge
  have hpowle : ‖s‖⁻¹ ^ (k + 1) ≤ 1 / t := by
    calc ‖s‖⁻¹ ^ (k + 1) ≤ (1 / t) ^ (k + 1) :=
          pow_le_pow_left₀ (by positivity) hinvle (k + 1)
      _ ≤ (1 / t) ^ (1 : ℕ) := by
          refine pow_le_pow_of_le_one (by positivity) ?_ (by omega)
          rw [div_le_one htpos]
          exact ht
      _ = 1 / t := pow_one _
  calc ‖P.coeff i‖ * ‖s‖⁻¹ ^ (k + 1) ≤ ‖P.coeff i‖ * (1 / t) :=
        mul_le_mul_of_nonneg_left hpowle (norm_nonneg _)
    _ = ‖P.coeff i‖ / t := by rw [mul_one_div]

/-- Uniform form of "a shift product against its length power tends to one". -/
theorem exists_uniform_bound_shiftProd_mul_inv_pow (l : Multiset ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ σ t : ℝ, 0 < σ → 1 ≤ t →
      ‖shiftProd l ((σ : ℂ) + (t : ℂ) * Complex.I)
          * (((σ : ℂ) + (t : ℂ) * Complex.I)⁻¹) ^ Multiset.card l - 1‖ ≤ B / t := by
  classical
  induction l using Multiset.induction_on with
  | empty =>
      refine ⟨0, le_refl 0, fun σ t hσ ht => ?_⟩
      simp [shiftProd]
  | cons j l ih =>
      obtain ⟨B, hB, hbound⟩ := ih
      refine ⟨(j : ℝ) * (1 + B) + B, by positivity, fun σ t hσ ht => ?_⟩
      set s : ℂ := (σ : ℂ) + (t : ℂ) * Complex.I with hs
      have htpos : (0 : ℝ) < t := lt_of_lt_of_le zero_lt_one ht
      have hsge : t ≤ ‖s‖ := norm_vertical_ge_im σ t
      have hsne : s ≠ 0 := by
        intro h0
        rw [h0, norm_zero] at hsge
        linarith
      set X : ℂ := shiftProd l s * (s⁻¹) ^ Multiset.card l with hX
      have hXb : ‖X - 1‖ ≤ B / t := hbound σ t hσ ht
      have hXle : ‖X‖ ≤ 1 + B := by
        have h1 : ‖X‖ ≤ ‖X - 1‖ + 1 := by
          have := norm_add_le (X - 1) 1
          simpa using this
        have h2 : B / t ≤ B := by
          rw [div_le_iff₀ htpos]
          nlinarith
        linarith
      have hexp : shiftProd (j ::ₘ l) s * (s⁻¹) ^ Multiset.card (j ::ₘ l)
          = ((s + (j : ℂ)) * s⁻¹) * X := by
        rw [shiftProd, Multiset.map_cons, Multiset.prod_cons, ← shiftProd, Multiset.card_cons,
          pow_succ, hX]
        ring
      have hfac : (s + (j : ℂ)) * s⁻¹ - 1 = (j : ℂ) * s⁻¹ := by
        rw [add_mul, mul_inv_cancel₀ hsne]
        ring
      have hsplit : shiftProd (j ::ₘ l) s * (s⁻¹) ^ Multiset.card (j ::ₘ l) - 1
          = ((j : ℂ) * s⁻¹) * X + (X - 1) := by
        rw [hexp, ← hfac]
        ring
      rw [hsplit]
      refine le_trans (norm_add_le _ _) ?_
      have hjs : ‖(j : ℂ) * s⁻¹‖ ≤ (j : ℝ) / t := by
        rw [norm_mul, norm_inv, Complex.norm_natCast]
        have hinvle : ‖s‖⁻¹ ≤ 1 / t := by
          rw [inv_eq_one_div]
          exact one_div_le_one_div_of_le htpos hsge
        calc (j : ℝ) * ‖s‖⁻¹ ≤ (j : ℝ) * (1 / t) :=
              mul_le_mul_of_nonneg_left hinvle (by positivity)
          _ = (j : ℝ) / t := by rw [mul_one_div]
      have hfirst : ‖((j : ℂ) * s⁻¹) * X‖ ≤ (j : ℝ) * (1 + B) / t := by
        rw [norm_mul]
        calc ‖(j : ℂ) * s⁻¹‖ * ‖X‖ ≤ ((j : ℝ) / t) * (1 + B) :=
              mul_le_mul hjs hXle (norm_nonneg _) (by positivity)
          _ = (j : ℝ) * (1 + B) / t := by ring
      calc ‖((j : ℂ) * s⁻¹) * X‖ + ‖X - 1‖ ≤ (j : ℝ) * (1 + B) / t + B / t :=
            add_le_add hfirst hXb
        _ = ((j : ℝ) * (1 + B) + B) / t := by ring

/-- **The datum of a standard rational function, uniformly on a vertical tube.**  For every `ε`
there is a height beyond which `s^p·P(s)/∏_j(s+j)` is within `ε` of `leadingCoeff P` simultaneously
for all abscissas `0 < σ ≤ M`. -/
theorem exists_uniform_height_stdRat_datum (P : Polynomial ℂ) (l : Multiset ℕ) (p : ℕ)
    (hcard : Multiset.card l = P.natDegree + p) {ε : ℝ} (hε : 0 < ε) :
    ∃ T : ℝ, ∀ σ t : ℝ, 0 < σ → T ≤ t →
      ‖((σ : ℂ) + (t : ℂ) * Complex.I) ^ p
          * (P.eval ((σ : ℂ) + (t : ℂ) * Complex.I)
            / shiftProd l ((σ : ℂ) + (t : ℂ) * Complex.I)) - P.leadingCoeff‖ ≤ ε := by
  classical
  obtain ⟨B₁, hB₁, hnum⟩ := exists_uniform_bound_polynomial_mul_inv_pow P
  obtain ⟨B₂, hB₂, hden⟩ := exists_uniform_bound_shiftProd_mul_inv_pow l
  -- beyond `2B₂` the denominator factor is at least `1/2`
  set A : ℝ := 2 * B₁ + 2 * ‖P.leadingCoeff‖ * B₂ with hA
  have hA0 : 0 ≤ A := by positivity
  refine ⟨max (max 1 (2 * B₂ + 1)) (A / ε + 1), fun σ t hσ ht => ?_⟩
  have ht1 : (1 : ℝ) ≤ t := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) ht
  have htB : 2 * B₂ + 1 ≤ t := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) ht
  have htA : A / ε + 1 ≤ t := le_trans (le_max_right _ _) ht
  have htpos : (0 : ℝ) < t := lt_of_lt_of_le zero_lt_one ht1
  set s : ℂ := (σ : ℂ) + (t : ℂ) * Complex.I with hs
  have hsge : t ≤ ‖s‖ := norm_vertical_ge_im σ t
  have hsne : s ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hsge
    linarith
  have hsre : (0 : ℝ) < s.re := by
    rw [hs]
    simpa using hσ
  have hden0 : shiftProd l s ≠ 0 := shiftProd_ne_zero hsre l
  set X : ℂ := P.eval s * (s⁻¹) ^ P.natDegree with hX
  set Y : ℂ := shiftProd l s * (s⁻¹) ^ Multiset.card l with hY
  have hXb : ‖X - P.leadingCoeff‖ ≤ B₁ / t := hnum σ t hσ ht1
  have hYb : ‖Y - 1‖ ≤ B₂ / t := hden σ t hσ ht1
  have hYhalf : (1 : ℝ) / 2 ≤ ‖Y‖ := by
    have hB2t : B₂ / t ≤ 1 / 2 := by
      rw [div_le_div_iff₀ htpos (by norm_num : (0:ℝ) < 2)]
      nlinarith
    have h1 : ‖Y - 1‖ ≤ 1 / 2 := le_trans hYb hB2t
    have h2 : (1 : ℝ) - ‖Y‖ ≤ ‖Y - 1‖ := by
      have := norm_sub_norm_le (1 : ℂ) Y
      rw [norm_one] at this
      calc (1 : ℝ) - ‖Y‖ ≤ ‖(1 : ℂ) - Y‖ := this
        _ = ‖Y - 1‖ := norm_sub_rev _ _
    linarith
  have hYne : Y ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hYhalf
    linarith
  -- the quotient equals the datum expression
  have hquot : X / Y = ((σ : ℂ) + (t : ℂ) * Complex.I) ^ p
      * (P.eval ((σ : ℂ) + (t : ℂ) * Complex.I)
        / shiftProd l ((σ : ℂ) + (t : ℂ) * Complex.I)) := by
    rw [hX, hY, hcard, pow_add, ← hs]
    field_simp
    rw [div_pow, one_pow, mul_assoc, div_mul_cancel₀ _ (pow_ne_zero p hsne), mul_one]
  rw [← hquot]
  -- estimate the quotient
  have hXle : ‖X‖ ≤ ‖P.leadingCoeff‖ + B₁ := by
    have h1 : ‖X‖ ≤ ‖X - P.leadingCoeff‖ + ‖P.leadingCoeff‖ := by
      have := norm_add_le (X - P.leadingCoeff) P.leadingCoeff
      simpa using this
    have h2 : B₁ / t ≤ B₁ := by
      rw [div_le_iff₀ htpos]
      nlinarith
    linarith
  have hsplit : X / Y - P.leadingCoeff
      = (X - P.leadingCoeff) / Y + P.leadingCoeff * ((1 - Y) / Y) := by
    field_simp
    ring
  rw [hsplit]
  refine le_trans (norm_add_le _ _) ?_
  have hinvY : ‖Y‖⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ (lt_of_lt_of_le (by norm_num) hYhalf) (by norm_num)]
    calc (2 : ℝ)⁻¹ = 1 / 2 := by norm_num
      _ ≤ ‖Y‖ := hYhalf
  have hfirst : ‖(X - P.leadingCoeff) / Y‖ ≤ 2 * B₁ / t := by
    rw [norm_div, div_eq_mul_inv]
    calc ‖X - P.leadingCoeff‖ * ‖Y‖⁻¹ ≤ (B₁ / t) * 2 :=
          mul_le_mul hXb hinvY (by positivity) (by positivity)
      _ = 2 * B₁ / t := by ring
  have hsecond : ‖P.leadingCoeff * ((1 - Y) / Y)‖ ≤ 2 * ‖P.leadingCoeff‖ * B₂ / t := by
    rw [norm_mul, norm_div, div_eq_mul_inv]
    have h1Y : ‖(1 : ℂ) - Y‖ ≤ B₂ / t := by
      rw [norm_sub_rev]
      exact hYb
    calc ‖P.leadingCoeff‖ * (‖(1 : ℂ) - Y‖ * ‖Y‖⁻¹)
        ≤ ‖P.leadingCoeff‖ * ((B₂ / t) * 2) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul h1Y hinvY (by positivity) (by positivity)) (norm_nonneg _)
      _ = 2 * ‖P.leadingCoeff‖ * B₂ / t := by ring
  have hAbound : 2 * B₁ / t + 2 * ‖P.leadingCoeff‖ * B₂ / t ≤ A / t := by
    rw [hA]
    exact le_of_eq (by ring)
  refine le_trans (le_trans (add_le_add hfirst hsecond) hAbound) ?_
  rw [div_le_iff₀ htpos]
  have hAe : A / ε ≤ t := by linarith
  calc A = (A / ε) * ε := by field_simp
    _ ≤ t * ε := mul_le_mul_of_nonneg_right hAe (le_of_lt hε)
    _ = ε * t := by ring

end

end GaloisForLFunctions.HTGeometry
