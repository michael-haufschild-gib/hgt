import GaloisForLFunctions.MultiplicativePositivityGeometry.ExactFejerBarrier
import GaloisForLFunctions.MultiplicativePositivityGeometry.ZetaBoundaryDivisor

/-!
# The growth-to-forcing law

Interior use of multiplicative positivity. For `σ > 1`, the height function
`u ↦ Re(−ζ'/ζ)(σ + iu)` is even positive definite (`zetaRealLogDeriv_isEvenPosDef`). De la Vallée
Poussin's method evaluates one Gram form of it at `σ = 1 + δ` and inserts three inputs: the pole
`A/δ`, a zero at distance `η` from the line, contributing `−B/(δ+η)`, and a growth bound `G` for the
remaining terms. A zero is excluded when `A/δ + G < B/(δ+η)` for some `δ > 0`.

* `exclusion_iff`: for `A, G, η > 0` and `B ≥ 0`, such a `δ` exists iff `√A + √(Gη) < √B`.
  Equivalently, the certified width is exactly `(√B − √A)²/G` (`exclusion_iff_lt_width`). The
  witness is the geometric mean `δ = √(Aη/G)`; necessity is AM–GM.
* `fejer_width_cap`: take `A = a₀`, `B = a₁` and `G = L·S` with `S ≥ a₁` (height scale `L`). A
  degree-`K` certificate then excludes only `η < (1 − ρ_K^{−1/2})²/L`, where
  `ρ_K = 2cos(π/(K+2))` is the exact Fejér barrier. Degree one excludes nothing
  (`degree_one_excludes_nothing`). Every degree stays strictly below the universal cap
  `(3 − 2√2)/(2L)` (`fejer_width_cap_lt_universal`).
-/

open Filter Topology Real

namespace GaloisForLFunctions.MultiplicativePositivityGeometry

open ArithmeticCastelnuovoSeveri

/-- **Interior positivity.** For `σ > 1`, `u ↦ Re(−ζ'/ζ)(σ + iu)` is even positive definite. -/
theorem zetaRealLogDeriv_isEvenPosDef {σ : ℝ} (hσ : 1 < σ) :
    IsEvenPosDef (fun u => zetaRealLogDeriv σ u) := by
  have hx : 0 < σ - 1 := sub_pos.mpr hσ
  have h : (fun u => zetaRealLogDeriv σ u) =
      cosineTrace (zetaBoundaryWeight (σ - 1)) logFrequency := by
    funext u
    have := zetaRealLogDeriv_eq_cosineTrace hx u
    rwa [show 1 + (σ - 1) = σ by ring] at this
  rw [h]
  exact isEvenPosDef_cosineTrace (zetaBoundaryWeight_nonneg _) (summable_zetaBoundaryWeight hx)
    logFrequency

/-- The exclusion inequality is the quadratic `G δ² + (A + Gη − B) δ + Aη < 0`. -/
theorem exclusion_iff_quadratic {A B G η δ : ℝ} (hδ : 0 < δ) (hη : 0 < η) :
    A / δ + G < B / (δ + η) ↔ G * δ ^ 2 + (A + G * η - B) * δ + A * η < 0 := by
  have hδη : 0 < δ + η := by linarith
  rw [div_add' _ _ _ hδ.ne', div_lt_div_iff₀ hδ hδη]
  constructor <;> intro h <;> nlinarith

/-- **The optimal witness.** If `√A + √(Gη) < √B`, the geometric mean
`δ* = √A √(Gη)/G = √(Aη/G)` excludes the zero. -/
theorem exclusion_at_geometric_mean {A B G η : ℝ} (hA : 0 < A) (hB : 0 ≤ B) (hG : 0 < G)
    (hη : 0 < η) (h : Real.sqrt A + Real.sqrt (G * η) < Real.sqrt B) :
    A / (Real.sqrt A * Real.sqrt (G * η) / G) + G <
      B / (Real.sqrt A * Real.sqrt (G * η) / G + η) := by
  have hs2 : Real.sqrt A ^ 2 = A := Real.sq_sqrt hA.le
  have ht2 : Real.sqrt (G * η) ^ 2 = G * η := Real.sq_sqrt (by positivity)
  have hu2 : Real.sqrt B ^ 2 = B := Real.sq_sqrt hB
  have hs0 : 0 < Real.sqrt A := Real.sqrt_pos.mpr hA
  have ht0 : 0 < Real.sqrt (G * η) := Real.sqrt_pos.mpr (by positivity)
  set δ := Real.sqrt A * Real.sqrt (G * η) / G with hδdef
  have hδ : 0 < δ := by positivity
  have hGδ : G * δ = Real.sqrt A * Real.sqrt (G * η) := by rw [hδdef]; field_simp
  -- At the geometric mean the two outer terms agree: `G δ² = A η`.
  have hAη : A * η = G * δ ^ 2 := by
    have : G * (A * η) = G * (G * δ ^ 2) := by
      rw [show G * (G * δ ^ 2) = (G * δ) ^ 2 by ring, hGδ, mul_pow, hs2, ht2]; ring
    exact mul_left_cancel₀ hG.ne' this
  have hsq : (Real.sqrt A + Real.sqrt (G * η)) ^ 2 < Real.sqrt B ^ 2 := by
    nlinarith [mul_pos (sub_pos.mpr h) (by positivity : 0 < Real.sqrt B + (Real.sqrt A +
      Real.sqrt (G * η)))]
  refine (exclusion_iff_quadratic hδ hη).mpr ?_
  have h3 : G * δ ^ 2 = Real.sqrt A * Real.sqrt (G * η) * δ := by rw [sq, ← mul_assoc, hGδ]
  have hlin : A + G * η - B =
      Real.sqrt A ^ 2 + Real.sqrt (G * η) ^ 2 - Real.sqrt B ^ 2 := by rw [hs2, ht2, hu2]
  rw [hAη, h3, hlin]
  nlinarith [mul_pos hδ (sub_pos.mpr hsq)]

/-- **Growth-to-forcing law.** A zero at distance `η` is excluded by pole weight `A`, zero weight
`B` and growth `G` iff `√A + √(Gη) < √B`. -/
theorem exclusion_iff {A B G η : ℝ} (hA : 0 < A) (hB : 0 ≤ B) (hG : 0 < G) (hη : 0 < η) :
    (∃ δ > 0, A / δ + G < B / (δ + η)) ↔ Real.sqrt A + Real.sqrt (G * η) < Real.sqrt B := by
  have hs2 : Real.sqrt A ^ 2 = A := Real.sq_sqrt hA.le
  have ht2 : Real.sqrt (G * η) ^ 2 = G * η := Real.sq_sqrt (by positivity)
  have hu2 : Real.sqrt B ^ 2 = B := Real.sq_sqrt hB
  have hs0 : 0 < Real.sqrt A := Real.sqrt_pos.mpr hA
  have ht0 : 0 < Real.sqrt (G * η) := Real.sqrt_pos.mpr (by positivity)
  have hu0 : 0 ≤ Real.sqrt B := Real.sqrt_nonneg _
  constructor
  · rintro ⟨δ, hδ, h⟩
    have hq := (exclusion_iff_quadratic hδ hη).mp h
    -- AM–GM: `G δ² + A η ≥ 2 √A √(Gη) δ`.
    have h2 : (Real.sqrt A * Real.sqrt (G * η)) ^ 2 = G * (A * η) := by
      rw [mul_pow, hs2, ht2]; ring
    have h1 : 0 ≤ G * (G * δ ^ 2 + A * η - 2 * Real.sqrt A * Real.sqrt (G * η) * δ) := by
      nlinarith [sq_nonneg (G * δ - Real.sqrt A * Real.sqrt (G * η))]
    have hamgm := (mul_nonneg_iff_of_pos_left hG).mp h1
    have hq' : G * δ ^ 2 + A * η +
        (Real.sqrt A ^ 2 + Real.sqrt (G * η) ^ 2 - Real.sqrt B ^ 2) * δ < 0 := by
      rw [hs2, ht2, hu2]; linarith
    have h3 : δ * ((Real.sqrt A + Real.sqrt (G * η)) ^ 2 - Real.sqrt B ^ 2) < 0 := by nlinarith
    have h4 : (Real.sqrt A + Real.sqrt (G * η)) ^ 2 < Real.sqrt B ^ 2 := by
      by_contra hc
      push Not at hc
      nlinarith [mul_nonneg hδ.le (sub_nonneg.mpr hc)]
    nlinarith
  · intro h
    exact ⟨_, by positivity, exclusion_at_geometric_mean hA hB hG hη h⟩

/-- **The certified width.** Exclusion holds iff `A < B` and `η < (√B − √A)²/G`. -/
theorem exclusion_iff_lt_width {A B G η : ℝ} (hA : 0 < A) (hB : 0 ≤ B) (hG : 0 < G)
    (hη : 0 < η) :
    (∃ δ > 0, A / δ + G < B / (δ + η)) ↔
      A < B ∧ η < (Real.sqrt B - Real.sqrt A) ^ 2 / G := by
  rw [exclusion_iff hA hB hG hη, lt_div_iff₀ hG, mul_comm η G]
  constructor
  · intro h
    have hAB : Real.sqrt A < Real.sqrt B := by linarith [Real.sqrt_nonneg (G * η)]
    refine ⟨(Real.sqrt_lt_sqrt_iff hA.le).mp hAB, ?_⟩
    exact (Real.sqrt_lt' (sub_pos.mpr hAB)).mp (by linarith)
  · rintro ⟨hAB, hw⟩
    have hpos : 0 < Real.sqrt B - Real.sqrt A :=
      sub_pos.mpr ((Real.sqrt_lt_sqrt_iff hA.le).mpr hAB)
    have := (Real.sqrt_lt' hpos).mpr hw
    linarith

/-- The exact Fejér barrier at degree `K ≥ 1` lies in `[1, 2)`. -/
theorem fejer_ratio_mem {K : ℕ} (hK : 1 ≤ K) :
    1 ≤ 2 * Real.cos (π / (K + 2 : ℕ)) ∧ 2 * Real.cos (π / (K + 2 : ℕ)) < 2 := by
  have hN : (3 : ℝ) ≤ (K + 2 : ℕ) := by push_cast; exact_mod_cast (by omega : 3 ≤ K + 2)
  have hpos : 0 < π / (K + 2 : ℕ) := by positivity
  have hle : π / (K + 2 : ℕ) ≤ π / 3 := div_le_div_of_nonneg_left Real.pi_pos.le (by norm_num) hN
  constructor
  · have := Real.cos_le_cos_of_nonneg_of_le_pi hpos.le (by linarith [Real.pi_pos]) hle
    rw [Real.cos_pi_div_three] at this
    linarith
  · have := Real.cos_lt_cos_of_nonneg_of_le_pi le_rfl (by linarith [Real.pi_pos]) hpos
    rw [Real.cos_zero] at this
    linarith

/-- **Degree-`K` width cap.** With growth `L·S`, `S ≥ a₁ > 0`, a nonnegative cosine polynomial
of degree `K` can only exclude zeros at distance `η < (1 − ρ_K^{−1/2})²/L`. -/
theorem fejer_width_cap {a : ℕ → ℝ} {K : ℕ} (hK : 1 ≤ K)
    (hP : ∀ θ, 0 ≤ HTGeometry.cosinePolynomial a K θ) {L S η : ℝ} (hL : 0 < L)
    (ha0 : 0 < a 0) (ha1 : 0 < a 1) (hS : a 1 ≤ S) (hη : 0 < η)
    (hexcl : ∃ δ > 0, a 0 / δ + L * S < a 1 / (δ + η)) :
    η < (1 - 1 / Real.sqrt (2 * Real.cos (π / (K + 2 : ℕ)))) ^ 2 / L := by
  have hρ := cosinePolynomial_first_le_fejer hK hP
  have hρ1 := (fejer_ratio_mem hK).1
  have h := (exclusion_iff ha0 ha1.le (mul_pos hL (ha1.trans_le hS)) hη).mp hexcl
  have hu0 : 0 < Real.sqrt (a 1) := Real.sqrt_pos.mpr ha1
  have hv0 : 0 ≤ Real.sqrt (L * η) := Real.sqrt_nonneg _
  have hr0 : 0 < Real.sqrt (2 * Real.cos (π / (K + 2 : ℕ))) := Real.sqrt_pos.mpr (by linarith)
  -- `√(Lη) √a₁ ≤ √(LSη)` and `√a₁ ≤ √ρ √a₀`.
  have hvu : Real.sqrt (L * η) * Real.sqrt (a 1) ≤ Real.sqrt (L * S * η) := by
    rw [← Real.sqrt_mul (show (0 : ℝ) ≤ L * η by positivity)]
    exact Real.sqrt_le_sqrt (by nlinarith [mul_pos hL hη])
  have hur : Real.sqrt (a 1) ≤
      Real.sqrt (2 * Real.cos (π / (K + 2 : ℕ))) * Real.sqrt (a 0) := by
    rw [← Real.sqrt_mul (show (0 : ℝ) ≤ 2 * Real.cos (π / (K + 2 : ℕ)) by linarith)]
    exact Real.sqrt_le_sqrt hρ
  -- Hence `√(Lη) · √ρ < √ρ − 1`.
  have h0 : Real.sqrt (a 0) + Real.sqrt (L * η) * Real.sqrt (a 1) < Real.sqrt (a 1) := by
    linarith
  have h1 := mul_lt_mul_of_pos_right h0 hr0
  have hkey : Real.sqrt (a 1) * (1 + Real.sqrt (L * η) * Real.sqrt (2 * Real.cos (π / (K + 2 : ℕ)))) <
      Real.sqrt (a 1) * Real.sqrt (2 * Real.cos (π / (K + 2 : ℕ))) := by nlinarith
  have hkey' := lt_of_mul_lt_mul_left hkey hu0.le
  have hv : Real.sqrt (L * η) < 1 - 1 / Real.sqrt (2 * Real.cos (π / (K + 2 : ℕ))) := by
    rw [show 1 - 1 / Real.sqrt (2 * Real.cos (π / (K + 2 : ℕ))) =
        (Real.sqrt (2 * Real.cos (π / (K + 2 : ℕ))) - 1) /
          Real.sqrt (2 * Real.cos (π / (K + 2 : ℕ))) by field_simp, lt_div_iff₀ hr0]
    linarith
  have hsq := mul_self_lt_mul_self hv0 hv
  rw [Real.mul_self_sqrt (by positivity)] at hsq
  rw [lt_div_iff₀ hL, mul_comm]
  nlinarith

/-- **Degree one excludes nothing.** At `K = 1` the barrier is `ρ₁ = 1`, and no zero at positive
distance is excluded. -/
theorem degree_one_excludes_nothing {a : ℕ → ℝ}
    (hP : ∀ θ, 0 ≤ HTGeometry.cosinePolynomial a 1 θ) {L S η : ℝ} (hL : 0 < L)
    (ha0 : 0 < a 0) (ha1 : 0 < a 1) (hS : a 1 ≤ S) (hη : 0 < η) :
    ¬ ∃ δ > 0, a 0 / δ + L * S < a 1 / (δ + η) := by
  intro hexcl
  have h := fejer_width_cap le_rfl hP hL ha0 ha1 hS hη hexcl
  have hρ : 2 * Real.cos (π / ((1 + 2 : ℕ) : ℝ)) = 1 := by
    rw [show ((1 + 2 : ℕ) : ℝ) = 3 by norm_num, Real.cos_pi_div_three]; norm_num
  rw [hρ, Real.sqrt_one, div_one, sub_self] at h
  simp at h
  linarith

/-- **Every finite degree stays below the universal cap.** The degree-`K` width cap is strictly
smaller than `(3 − 2√2)/(2L)`, the cap of the purchase ratio `a₁ ≤ 2a₀`. -/
theorem fejer_width_cap_lt_universal {K : ℕ} (hK : 1 ≤ K) {L : ℝ} (hL : 0 < L) :
    (1 - 1 / Real.sqrt (2 * Real.cos (π / (K + 2 : ℕ)))) ^ 2 / L <
      (3 - 2 * Real.sqrt 2) / (2 * L) := by
  obtain ⟨hρ1, hρ2⟩ := fejer_ratio_mem hK
  set ρ := 2 * Real.cos (π / (K + 2 : ℕ))
  have hr1 : 1 ≤ Real.sqrt ρ := by rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt hρ1
  have hr2 : Real.sqrt ρ < Real.sqrt 2 := (Real.sqrt_lt_sqrt_iff (by linarith)).mpr hρ2
  have ht2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have ht1 : 1 < Real.sqrt 2 := by
    rw [← Real.sqrt_one]; exact (Real.sqrt_lt_sqrt_iff zero_le_one).mpr (by norm_num)
  have hr0 : 0 < Real.sqrt ρ := by linarith
  -- `0 ≤ 1 − 1/√ρ < 1 − 1/√2`, and `(1 − 1/√2)² = (3 − 2√2)/2`.
  have ha : 0 ≤ 1 - 1 / Real.sqrt ρ := by
    rw [sub_nonneg, div_le_one hr0]; exact hr1
  have hb : 1 - 1 / Real.sqrt ρ < 1 - 1 / Real.sqrt 2 := by
    have := one_div_lt_one_div_of_lt hr0 hr2
    linarith
  have hsq := mul_self_lt_mul_self ha hb
  have hval : (1 - 1 / Real.sqrt 2) * (1 - 1 / Real.sqrt 2) = (3 - 2 * Real.sqrt 2) / 2 := by
    field_simp
    nlinarith [ht2]
  rw [hval, ← sq] at hsq
  rw [div_lt_div_iff₀ hL (by positivity)]
  nlinarith

end GaloisForLFunctions.MultiplicativePositivityGeometry
