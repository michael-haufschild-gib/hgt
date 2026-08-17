import GaloisForLFunctions.HTGeometry.NonstationaryPhaseVectorField

/-!
# The soft-light capture floor

A soft spectral filter that keeps every level of weight below its own collision scale removes at
most a quarter of the capture margin: the discarded weight obeys Chebyshev against the collision
mass.  A target that captures the true orbit therefore still captures the filtered orbit with half
the overlap, so its replica moment stays above the capture floor `(a/4)^r`.

The filtered coefficients have squared mass at most the filter threshold, because each of them is
the product of the two spectral weights and the surviving weights are below the threshold.  Finally
the replica floor `r!(8C/a)^r` is below `2^{-r}` at the replica order set by the collision scale,
and a circuit count below `2^{r/2}` survives it.
-/

open Finset

namespace GaloisForLFunctions.HTGeometry

section Removed

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- **`(26)`: the soft filter removes at most a quarter of the capture margin.**  A weighting whose
collision mass is at most `C`, filtered by any profile that is one below the threshold `4C/a`,
loses at most `a/4` of its mass. -/
theorem sum_removed_softWeight_le {p w : I → ℝ}
    (hw0 : ∀ j, 0 ≤ w j) (hw1 : ∀ j, w j ≤ 1) {a C : ℝ} (ha : 0 < a) (hCpos : 0 < C)
    (hkeep : ∀ j, p j ≤ 4 * C / a → w j = 1) (hC : ∑ j, p j ^ 2 ≤ C) :
    ∑ j, (1 - w j) ^ 2 * p j ≤ a / 4 := by
  classical
  set τ : ℝ := 4 * C / a with hτ
  have hτpos : 0 < τ := by rw [hτ]; positivity
  set B : Finset I := Finset.univ.filter fun j => ¬ p j ≤ τ with hB
  have hterm : ∀ j ∈ (Finset.univ : Finset I), (1 - w j) ^ 2 * p j ≤
      if j ∈ B then p j ^ 2 / τ else 0 := by
    intro j _
    by_cases hj : p j ≤ τ
    · have hzero : w j = 1 := hkeep j hj
      have hnotB : j ∉ B := by
        rw [hB, Finset.mem_filter]
        simp [hj]
      rw [if_neg hnotB, hzero]
      simp
    · have hmem : j ∈ B := by
        rw [hB, Finset.mem_filter]
        exact ⟨Finset.mem_univ j, hj⟩
      rw [if_pos hmem]
      have hgt : τ < p j := not_le.mp hj
      have hsq : (1 - w j) ^ 2 ≤ 1 := by nlinarith [hw0 j, hw1 j]
      have hstep : (1 - w j) ^ 2 * p j ≤ p j := by nlinarith [hsq, hgt, hτpos]
      have hcheb : p j ≤ p j ^ 2 / τ := by
        rw [le_div_iff₀ hτpos]
        nlinarith [hgt, hτpos]
      linarith
  calc ∑ j, (1 - w j) ^ 2 * p j
      ≤ ∑ j, if j ∈ B then p j ^ 2 / τ else 0 := Finset.sum_le_sum hterm
    _ = ∑ j ∈ B, p j ^ 2 / τ := by rw [Finset.sum_ite_mem, Finset.univ_inter]
    _ ≤ ∑ j, p j ^ 2 / τ :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          fun i _ _ => by positivity
    _ = (∑ j, p j ^ 2) / τ := by rw [Finset.sum_div]
    _ ≤ C / τ := by
        exact div_le_div_of_nonneg_right hC hτpos.le
    _ = a / 4 := by
        rw [hτ]
        field_simp

omit [DecidableEq I] in
/-- The removed part of a softly filtered coordinate vector carries exactly the removed weight. -/
theorem sum_norm_sub_softFilter_sq (χ : I → ℂ) (w : I → ℝ) :
    ∑ j, ‖χ j - (w j : ℂ) * χ j‖ ^ 2 = ∑ j, (1 - w j) ^ 2 * ‖χ j‖ ^ 2 := by
  refine Finset.sum_congr rfl fun j _ => ?_
  have hfac : χ j - (w j : ℂ) * χ j = ((1 - w j : ℝ) : ℂ) * χ j := by
    push_cast
    ring
  rw [hfac, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-! ## The filtered coefficient mass -/

omit [Fintype I] [DecidableEq I] in
/-- The squared overlap of two coordinate vectors at one level is the product of the two weights. -/
theorem norm_sq_coordOverlap (z χ : I → ℂ) (j : I) :
    ‖(starRingEnd ℂ) (z j) * χ j‖ ^ 2 = ‖z j‖ ^ 2 * ‖χ j‖ ^ 2 := by
  rw [norm_mul, RCLike.norm_conj, mul_pow]

omit [DecidableEq I] in
/-- **`(27a)`: the filtered coefficients have mass at most the threshold.**  Each coefficient is
bounded by the product of the two spectral weights, and the surviving levels have weight below the
threshold, so the total is at most the threshold times the unit target mass. -/
theorem sum_le_threshold_of_product_bound {p q c : I → ℝ} {T : ℝ} (hT : 0 ≤ T)
    (hc : ∀ j, c j ≤ p j * q j) (hp : ∀ j, p j ≤ T) (hq : ∀ j, 0 ≤ q j)
    (hqsum : ∑ j, q j ≤ 1) :
    ∑ j, c j ≤ T := by
  have hstep : ∀ j ∈ (Finset.univ : Finset I), c j ≤ T * q j := by
    intro j _
    exact le_trans (hc j) (by nlinarith [hp j, hq j])
  calc ∑ j, c j ≤ ∑ j, T * q j := Finset.sum_le_sum hstep
    _ = T * ∑ j, q j := by rw [Finset.mul_sum]
    _ ≤ T * 1 := mul_le_mul_of_nonneg_left hqsum hT
    _ = T := mul_one T

end Removed

section Floor

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- **`(27)`: the capture floor survives the filter.**  A unit target whose overlap with the orbit
is at least `√a`, tested against a filtered orbit whose deficit has squared norm at most `a/4`,
still has replica moment at least `(a/4)^r`. -/
theorem capture_floor_le_inner_pow {a : ℝ} (ha : 0 ≤ a) {z ψ Ψ : E} (hz : ‖z‖ = 1)
    (hcap : Real.sqrt a ≤ ‖inner ℂ z ψ‖) (hclose : ‖ψ - Ψ‖ ^ 2 ≤ a / 4) (r : ℕ) :
    (a / 4) ^ r ≤ ‖inner ℂ z Ψ‖ ^ (2 * r) := by
  have hsa : 0 ≤ Real.sqrt a := Real.sqrt_nonneg a
  have hsq : Real.sqrt a ^ 2 = a := Real.sq_sqrt ha
  have hdist : ‖ψ - Ψ‖ ≤ Real.sqrt a / 2 := by
    nlinarith [norm_nonneg (ψ - Ψ), hclose, hsq, hsa]
  have hsplit : inner ℂ z Ψ = inner ℂ z ψ - inner ℂ z (ψ - Ψ) := by
    rw [inner_sub_right]
    ring
  have hsmall : ‖inner ℂ z (ψ - Ψ)‖ ≤ Real.sqrt a / 2 := by
    calc ‖inner ℂ z (ψ - Ψ)‖ ≤ ‖z‖ * ‖ψ - Ψ‖ := norm_inner_le_norm _ _
      _ = ‖ψ - Ψ‖ := by rw [hz, one_mul]
      _ ≤ Real.sqrt a / 2 := hdist
  have hlower : Real.sqrt a / 2 ≤ ‖inner ℂ z Ψ‖ := by
    have htri : ‖inner ℂ z ψ‖ - ‖inner ℂ z (ψ - Ψ)‖ ≤ ‖inner ℂ z ψ - inner ℂ z (ψ - Ψ)‖ :=
      norm_sub_norm_le _ _
    rw [hsplit]
    linarith
  have hsqlower : a / 4 ≤ ‖inner ℂ z Ψ‖ ^ 2 := by
    nlinarith [hlower, hsa, hsq, norm_nonneg (inner ℂ z Ψ)]
  calc (a / 4) ^ r ≤ (‖inner ℂ z Ψ‖ ^ 2) ^ r :=
        pow_le_pow_left₀ (by positivity) hsqlower r
    _ = ‖inner ℂ z Ψ‖ ^ (2 * r) := by rw [← pow_mul]

end Floor

section Arithmetic

/-- **The replica floor at the collision replica order.**  A per-level mass below `1/(2r)` makes the
factorial replica floor at most `2^{-r}`. -/
theorem factorial_mul_pow_le_half_pow {r : ℕ} (hr : 1 ≤ r) {x : ℝ} (hx0 : 0 ≤ x)
    (hx : x ≤ 1 / (2 * (r : ℝ))) :
    (r.factorial : ℝ) * x ^ r ≤ (1 / 2 : ℝ) ^ r := by
  have hrpos : (0 : ℝ) < r := by exact_mod_cast hr
  have hfac : (r.factorial : ℝ) ≤ (r : ℝ) ^ r := by
    exact_mod_cast Nat.factorial_le_pow r
  have hpow : x ^ r ≤ (1 / (2 * (r : ℝ))) ^ r := pow_le_pow_left₀ hx0 hx r
  calc (r.factorial : ℝ) * x ^ r ≤ (r : ℝ) ^ r * (1 / (2 * (r : ℝ))) ^ r :=
        mul_le_mul hfac hpow (by positivity) (by positivity)
    _ = ((r : ℝ) * (1 / (2 * (r : ℝ)))) ^ r := by rw [mul_pow]
    _ = (1 / 2 : ℝ) ^ r := by
        congr 1
        field_simp

/-- A circuit count whose logarithm obeys the replica budget stays below `2^{r/2}`. -/
theorem pow_le_two_rpow_of_log_le {M : ℝ} (hM : 0 < M) {s r : ℕ}
    (h : ((s : ℝ) + 1) * Real.log M ≤ (r : ℝ) / 2 * Real.log 2) :
    M ^ (s + 1) ≤ (2 : ℝ) ^ ((r : ℝ) / 2) := by
  have hMrpow : M ^ (s + 1) = M ^ (((s : ℝ) + 1)) := by
    rw [show ((s : ℝ) + 1) = ((s + 1 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
  rw [hMrpow, Real.rpow_def_of_pos hM, Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 2)]
  refine Real.exp_le_exp.mpr ?_
  calc Real.log M * ((s : ℝ) + 1) = ((s : ℝ) + 1) * Real.log M := by ring
    _ ≤ (r : ℝ) / 2 * Real.log 2 := h
    _ = Real.log 2 * ((r : ℝ) / 2) := by ring

/-- **`(28)`: the completed contribution is below the plateau tail.**  A circuit count below
`2^{r/2}` against a replica floor `2^{-r}` leaves at most `2^{-r/2}`. -/
theorem count_mul_half_pow_le {Ns : ℝ} {r : ℕ}
    (hNsb : Ns ≤ (2 : ℝ) ^ ((r : ℝ) / 2)) :
    Ns * (1 / 2 : ℝ) ^ r ≤ (2 : ℝ) ^ (-((r : ℝ) / 2)) := by
  have h2 : (0 : ℝ) < 2 := by norm_num
  have hhalf : (1 / 2 : ℝ) ^ r = (2 : ℝ) ^ (-(r : ℝ)) := by
    rw [Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2), Real.rpow_natCast]
    rw [one_div, inv_pow]
  have hprod : (2 : ℝ) ^ ((r : ℝ) / 2) * (2 : ℝ) ^ (-(r : ℝ)) = (2 : ℝ) ^ (-((r : ℝ) / 2)) := by
    rw [← Real.rpow_add h2]
    congr 1
    ring
  calc Ns * (1 / 2 : ℝ) ^ r = Ns * (2 : ℝ) ^ (-(r : ℝ)) := by rw [hhalf]
    _ ≤ (2 : ℝ) ^ ((r : ℝ) / 2) * (2 : ℝ) ^ (-(r : ℝ)) :=
        mul_le_mul_of_nonneg_right hNsb (le_of_lt (Real.rpow_pos_of_pos h2 _))
    _ = (2 : ℝ) ^ (-((r : ℝ) / 2)) := hprod

end Arithmetic

end GaloisForLFunctions.HTGeometry
