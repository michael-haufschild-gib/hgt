import GaloisForLFunctions.RHTower.CommonProfileVacuumJoin

/-!
# Exact size of the occupancy defect

The occupancy defect at a modulus is the nonzero-frequency response, so it is bounded by the root
count times the frequency tail mass of the profile divided by the modulus.  For a Schwartz profile
the tail mass at spacing `1/l` grows at most like `l²`, which gives the exact `nu_h(l) * l` shape of
the defect bound with a constant depending only on the profile.

Summing over a dyadic crossing block of primes coprime to a fixed modulus turns that into the exact
crossing bound: the total is at most `4 nu_h(q) q P²` times the profile constant.  No asymptotic
notation and no unspecified constant occurs.
-/

open scoped BigOperators FourierTransform SchwartzMap

noncomputable section

namespace RHTower

/-! ## The frequency tail mass -/

/-- The mass of the reciprocal squares over the nonzero integers. -/
def intInverseSquareSum : ℝ := ∑' m : ℤ, (if m = 0 then 0 else 1 / ((m : ℝ) ^ 2))

theorem summable_intInverseSquare :
    Summable fun m : ℤ => (if m = 0 then 0 else 1 / ((m : ℝ) ^ 2)) := by
  refine ((Real.summable_one_div_int_pow (p := 2)).2 one_lt_two).congr_cofinite ?_
  filter_upwards [Filter.eventually_cofinite_ne (0 : ℤ)] with m hm
  rw [if_neg hm]

theorem intInverseSquareSum_nonneg : 0 ≤ intInverseSquareSum := by
  refine tsum_nonneg fun m => ?_
  by_cases hm : m = 0
  · rw [if_pos hm]
  · rw [if_neg hm]
    positivity

/-- The total mass of the transform sampled on the dual lattice of spacing `1/l`. -/
def fourierTailMass (W : 𝓢(ℝ, ℂ)) (l : ℕ) : ℝ :=
  ∑' m : ℤ, ‖𝓕 (W : ℝ → ℂ) ((m : ℝ) / l)‖

/-- The profile constant controlling every occupancy defect. -/
def profileConstant (W : 𝓢(ℝ, ℂ)) : ℝ :=
  ‖𝓕 (W : ℝ → ℂ) 0‖ + (SchwartzMap.seminorm ℂ 2 0 (𝓕 W)) * intInverseSquareSum

theorem profileConstant_nonneg (W : 𝓢(ℝ, ℂ)) : 0 ≤ profileConstant W := by
  refine add_nonneg (norm_nonneg _) (mul_nonneg (apply_nonneg _ _) intInverseSquareSum_nonneg)

/-- **The tail mass of a Schwartz profile grows at most like the square of the modulus.** -/
theorem fourierTailMass_le (W : 𝓢(ℝ, ℂ)) {l : ℕ} (hl : l ≠ 0) :
    fourierTailMass W l ≤ ‖𝓕 (W : ℝ → ℂ) 0‖ +
      (SchwartzMap.seminorm ℂ 2 0 (𝓕 W)) * (l : ℝ) ^ 2 * intInverseSquareSum := by
  classical
  have hlR : ((l : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hl
  have hsum : Summable fun m : ℤ => ‖𝓕 (W : ℝ → ℂ) ((m : ℝ) / l)‖ :=
    summable_schwartzFrequencyWeight W hl
  have hbound : ∀ m : ℤ, (if m = 0 then 0 else ‖𝓕 (W : ℝ → ℂ) ((m : ℝ) / l)‖) ≤
      (SchwartzMap.seminorm ℂ 2 0 (𝓕 W)) * (l : ℝ) ^ 2 *
        (if m = 0 then 0 else 1 / ((m : ℝ) ^ 2)) := by
    intro m
    by_cases hm : m = 0
    · rw [if_pos hm, if_pos hm, mul_zero]
    · rw [if_neg hm, if_neg hm]
      have hmR : ((m : ℤ) : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hm
      have hx : ‖(m : ℝ) / l‖ ^ 2 * ‖(𝓕 W) ((m : ℝ) / l)‖ ≤
          (SchwartzMap.seminorm ℂ 2 0 (𝓕 W)) :=
        SchwartzMap.norm_pow_mul_le_seminorm ℂ (𝓕 W) 2 ((m : ℝ) / l)
      have hnorm : ‖(m : ℝ) / l‖ ^ 2 = (m : ℝ) ^ 2 / (l : ℝ) ^ 2 := by
        rw [Real.norm_eq_abs, abs_div, div_pow, sq_abs, sq_abs]
      have hpos : 0 < (m : ℝ) ^ 2 / (l : ℝ) ^ 2 := by positivity
      have hcoe : ((𝓕 W : 𝓢(ℝ, ℂ)) : ℝ → ℂ) = 𝓕 (W : ℝ → ℂ) := SchwartzMap.fourier_coe W
      rw [hcoe, hnorm, ← le_div_iff₀' hpos] at hx
      refine le_trans hx (le_of_eq ?_)
      field_simp
  have htail : (∑' m : ℤ, (if m = 0 then 0 else ‖𝓕 (W : ℝ → ℂ) ((m : ℝ) / l)‖)) ≤
      (SchwartzMap.seminorm ℂ 2 0 (𝓕 W)) * (l : ℝ) ^ 2 * intInverseSquareSum := by
    rw [intInverseSquareSum, ← tsum_mul_left]
    refine Summable.tsum_mono ?_ ?_ hbound
    · refine hsum.congr_cofinite ?_
      filter_upwards [Filter.eventually_cofinite_ne (0 : ℤ)] with m hm
      rw [if_neg hm]
    · exact summable_intInverseSquare.mul_left _
  rw [fourierTailMass, hsum.tsum_eq_add_tsum_ite (0 : ℤ)]
  simp only [Int.cast_zero, zero_div]
  linarith [htail]

/-! ## The exact defect bound -/

/-- **The occupancy defect is bounded by the root count times the tail mass over the modulus.** -/
theorem norm_occupancyDefect_le_tailMass (W : 𝓢(ℝ, ℂ)) (Q : CGLPositiveModulus) (h : ℤ) :
    ‖occupancyDefect W Q.value h‖ ≤
      (quadraticCongruenceRootCountTotal Q.value h : ℝ) / (Q.value : ℝ) *
        fourierTailMass W Q.value := by
  classical
  have hq : Q.value ≠ 0 := NeZero.ne Q.value
  have hqR : (0 : ℝ) < (Q.value : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero hq
  have hsum : Summable fun m : ℤ => ‖𝓕 (W : ℝ → ℂ) ((m : ℝ) / Q.value)‖ :=
    summable_schwartzFrequencyWeight W hq
  have hbound : ∀ m : ℤ,
      ‖(if m = 0 then 0 else ((Q.value : ℂ))⁻¹ * (𝓕 (W : ℝ → ℂ) ((m : ℝ) / Q.value) *
        quadraticCongruenceRootSumTotal Q.value h m))‖ ≤
      (quadraticCongruenceRootCountTotal Q.value h : ℝ) / (Q.value : ℝ) *
        ‖𝓕 (W : ℝ → ℂ) ((m : ℝ) / Q.value)‖ := by
    intro m
    have hnn : (0 : ℝ) ≤ ‖𝓕 (W : ℝ → ℂ) ((m : ℝ) / Q.value)‖ := norm_nonneg _
    by_cases hm : m = 0
    · rw [if_pos hm, norm_zero]
      positivity
    · rw [if_neg hm, norm_mul, norm_mul, norm_inv, Complex.norm_natCast]
      have hS := norm_quadraticCongruenceRootSumTotal_le_count Q.value h m
      have hQinv : (0 : ℝ) ≤ ((Q.value : ℝ))⁻¹ := by positivity
      calc ((Q.value : ℝ))⁻¹ * (‖𝓕 (W : ℝ → ℂ) ((m : ℝ) / Q.value)‖ *
              ‖quadraticCongruenceRootSumTotal Q.value h m‖)
          ≤ ((Q.value : ℝ))⁻¹ * (‖𝓕 (W : ℝ → ℂ) ((m : ℝ) / Q.value)‖ *
              (quadraticCongruenceRootCountTotal Q.value h : ℝ)) := by
            gcongr
        _ = (quadraticCongruenceRootCountTotal Q.value h : ℝ) / (Q.value : ℝ) *
              ‖𝓕 (W : ℝ → ℂ) ((m : ℝ) / Q.value)‖ := by
            field_simp
  have hsummable : Summable fun m : ℤ =>
      ‖(if m = 0 then 0 else ((Q.value : ℂ))⁻¹ * (𝓕 (W : ℝ → ℂ) ((m : ℝ) / Q.value) *
        quadraticCongruenceRootSumTotal Q.value h m))‖ := by
    refine Summable.of_nonneg_of_le (fun m => norm_nonneg _) hbound (hsum.mul_left _)
  rw [occupancyDefect_eq_tsum W Q h, fourierTailMass, ← tsum_mul_left]
  exact le_trans (norm_tsum_le_tsum_norm hsummable)
    (Summable.tsum_mono hsummable (hsum.mul_left _) hbound)

/-- **`(PF14)`, exact.**  The occupancy defect of a Schwartz profile at a modulus `l` is at most
the root count times the modulus times the profile constant. -/
theorem norm_occupancyDefect_le (W : 𝓢(ℝ, ℂ)) (Q : CGLPositiveModulus) (h : ℤ) :
    ‖occupancyDefect W Q.value h‖ ≤
      (quadraticCongruenceRootCountTotal Q.value h : ℝ) * (Q.value : ℝ) *
        profileConstant W := by
  have hq : Q.value ≠ 0 := NeZero.ne Q.value
  have hqR : (0 : ℝ) < (Q.value : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hq
  have hq1 : (1 : ℝ) ≤ (Q.value : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.2 hq
  have hnu : (0 : ℝ) ≤ (quadraticCongruenceRootCountTotal Q.value h : ℝ) := Nat.cast_nonneg _
  have hseminorm : (0 : ℝ) ≤ (SchwartzMap.seminorm ℂ 2 0 (𝓕 W)) := apply_nonneg _ _
  refine le_trans (norm_occupancyDefect_le_tailMass W Q h) ?_
  refine le_trans (mul_le_mul_of_nonneg_left (fourierTailMass_le W hq) (by positivity)) ?_
  rw [profileConstant, div_mul_eq_mul_div, div_le_iff₀ hqR]
  have hZ : (0 : ℝ) ≤ intInverseSquareSum := intInverseSquareSum_nonneg
  nlinarith [norm_nonneg (𝓕 (W : ℝ → ℂ) 0), sq_nonneg ((Q.value : ℝ) - 1),
    mul_nonneg hnu (norm_nonneg (𝓕 (W : ℝ → ℂ) 0)),
    mul_nonneg (mul_nonneg hnu hseminorm) hZ]

/-! ## The exact crossing bound -/

theorem quadraticCongruenceRootCountTotal_prime_le {p : ℕ} (hp : p.Prime) (h : ℤ) :
    quadraticCongruenceRootCountTotal p h ≤ 2 := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  rw [quadraticCongruenceRootCountTotal_of_ne_zero hp.ne_zero,
    quadraticCongruenceRootCount_prime hp h]
  split <;> omega

theorem quadraticCongruenceRootCountTotal_crossing_le {p q : ℕ} (hp : p.Prime) (hq : q ≠ 0)
    (hpq : p.Coprime q) (h : ℤ) :
    quadraticCongruenceRootCountTotal (p * q) h ≤ 2 * quadraticCongruenceRootCountTotal q h := by
  rw [quadraticCongruenceRootCountTotal_mul hp.ne_zero hq hpq h]
  exact Nat.mul_le_mul_right _ (quadraticCongruenceRootCountTotal_prime_le hp h)

/-- One crossing term of the dyadic block. -/
theorem norm_occupancyDefect_crossing_le (W : 𝓢(ℝ, ℂ)) {p q P : ℕ} (hp : p.Prime) (hq : q ≠ 0)
    (hpq : p.Coprime q) (hP : p < 2 * P) (h : ℤ) :
    ‖occupancyDefect W (p * q) h‖ ≤
      4 * (quadraticCongruenceRootCountTotal q h : ℝ) * (q : ℝ) * (P : ℝ) *
        profileConstant W := by
  have hpq0 : p * q ≠ 0 := Nat.mul_ne_zero hp.ne_zero hq
  have hbase := norm_occupancyDefect_le W ⟨p * q, Nat.pos_of_ne_zero hpq0⟩ h
  have hC : 0 ≤ profileConstant W := profileConstant_nonneg W
  have hnu : ((quadraticCongruenceRootCountTotal (p * q) h : ℕ) : ℝ) ≤
      2 * (quadraticCongruenceRootCountTotal q h : ℝ) := by
    exact_mod_cast quadraticCongruenceRootCountTotal_crossing_le hp hq hpq h
  have hpqR : ((p * q : ℕ) : ℝ) ≤ 2 * (P : ℝ) * (q : ℝ) := by
    have hple : (p : ℝ) ≤ 2 * (P : ℝ) := by exact_mod_cast Nat.le_of_lt_succ (by omega)
    push_cast
    have hqnn : (0 : ℝ) ≤ (q : ℝ) := Nat.cast_nonneg _
    nlinarith
  refine le_trans hbase ?_
  have hnn1 : (0 : ℝ) ≤ ((quadraticCongruenceRootCountTotal (p * q) h : ℕ) : ℝ) :=
    Nat.cast_nonneg _
  have hnn2 : (0 : ℝ) ≤ ((p * q : ℕ) : ℝ) := Nat.cast_nonneg _
  have hnn3 : (0 : ℝ) ≤ (quadraticCongruenceRootCountTotal q h : ℝ) := Nat.cast_nonneg _
  have hnn4 : (0 : ℝ) ≤ (P : ℝ) := Nat.cast_nonneg _
  have hnn5 : (0 : ℝ) ≤ (q : ℝ) := Nat.cast_nonneg _
  nlinarith [mul_le_mul hnu hpqR hnn2 (by positivity : (0:ℝ) ≤ 2 * (quadraticCongruenceRootCountTotal q h : ℝ))]

/-- **`(SG9)`, exact.**  Over a dyadic crossing block of primes below `2P` coprime to a fixed
modulus `q`, the total occupancy defect is at most `4 nu_h(q) q P²` times the profile constant of
each gap.  No asymptotic notation and no unspecified constant occurs. -/
theorem sum_crossing_norm_occupancyDefect_le (W : ℤ → 𝓢(ℝ, ℂ)) (gaps : Finset ℤ)
    {q P : ℕ} (hq : q ≠ 0) (block : Finset ℕ)
    (hblock : ∀ p ∈ block, p.Prime ∧ p < 2 * P ∧ p.Coprime q)
    (hcard : block.card ≤ P) :
    ∑ h ∈ gaps, ∑ p ∈ block, ‖occupancyDefect (W h) (p * q) h‖ ≤
      ∑ h ∈ gaps, 4 * (quadraticCongruenceRootCountTotal q h : ℝ) * (q : ℝ) * (P : ℝ) ^ 2 *
        profileConstant (W h) := by
  refine Finset.sum_le_sum fun h _ => ?_
  have hbound : ∀ p ∈ block, ‖occupancyDefect (W h) (p * q) h‖ ≤
      4 * (quadraticCongruenceRootCountTotal q h : ℝ) * (q : ℝ) * (P : ℝ) *
        profileConstant (W h) := by
    intro p hp
    obtain ⟨hpp, hpP, hpq⟩ := hblock p hp
    exact norm_occupancyDefect_crossing_le (W h) hpp hq hpq hpP h
  refine le_trans (Finset.sum_le_card_nsmul block _ _ hbound) ?_
  rw [nsmul_eq_mul]
  have hcardR : ((block.card : ℕ) : ℝ) ≤ (P : ℝ) := by exact_mod_cast hcard
  have hnn3 : (0 : ℝ) ≤ (quadraticCongruenceRootCountTotal q h : ℝ) := Nat.cast_nonneg _
  have hnn4 : (0 : ℝ) ≤ (P : ℝ) := Nat.cast_nonneg _
  have hnn5 : (0 : ℝ) ≤ (q : ℝ) := Nat.cast_nonneg _
  have hC : 0 ≤ profileConstant (W h) := profileConstant_nonneg (W h)
  nlinarith [mul_nonneg (mul_nonneg (mul_nonneg hnn3 hnn5) hnn4) hC]

end RHTower
