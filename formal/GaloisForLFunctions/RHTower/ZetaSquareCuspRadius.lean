import GaloisForLFunctions.HTGeometry.CentralBinomialRoot
import GaloisForLFunctions.HTGeometry.ParityLimsupSplit
import GaloisForLFunctions.RHTower.ZetaCuspRadiusConstant

/-!
# The cusp constant of the squared zeta shift lattice

In degree two the shift lattice advances by half-integers, so its coefficients
are given by one formula at even indices and another at odd ones.  Both are the
square of a shifted zeta value divided by a factorial, and the functional
equation turns each into a geometric factor times a bounded-growth remainder.

The factorial ratio `(m!)^(2 : ℕ)/(2m)!` is the reciprocal of the central binomial
coefficient, which is `4^{-m}` up to a polynomial factor.  Combining the two
geometric rates gives `1/(2π) · 1/2 = 1/(4π)` in both parities, so the growth
functional of the squared shift lattice is exactly `1/(4π)` — the cusp constant
of degree two and conductor one.
-/

open Filter Topology
open GaloisForLFunctions.HTGeometry
open scoped ENNReal NNReal

namespace RHTower

section Split

variable {t : ℂ}

/-- The non-oscillating part of the shifted remainder. -/
noncomputable def gpart (t : ℂ) (m : ℕ) : ℝ :=
  ‖2 * (2 * (Real.pi : ℂ)) ^ (-(1 - t))‖
    * ‖Complex.Gamma (1 - t + (m : ℂ)) / Complex.Gamma (1 + (m : ℂ))‖
    * ‖riemannZeta (1 - t + (m : ℂ))‖

theorem gpart_nonneg (t : ℂ) (m : ℕ) : 0 ≤ gpart t m := by
  rw [gpart]
  positivity

theorem norm_zetaShiftRemainder_eq (t : ℂ) (m : ℕ) :
    ‖zetaShiftRemainder t m‖ = gpart t m * cosShift t m := by
  rw [zetaShiftRemainder, norm_mul, norm_mul, norm_mul, gpart, cosShift]
  ring

theorem tendsto_gpart_rpow_inv (hs : ∀ m : ℕ, t ≠ (m : ℂ)) :
    Tendsto (fun m : ℕ => (gpart t m) ^ (1 / (m : ℝ))) atTop (𝓝 1) := by
  have hCpos : 0 < ‖2 * (2 * (Real.pi : ℂ)) ^ (-(1 - t))‖ := by
    rw [norm_pos_iff]
    refine mul_ne_zero two_ne_zero ?_
    exact Complex.cpow_ne_zero_iff.mpr (Or.inl two_pi_ne_zero)
  have hprod := ((tendsto_const_rpow_inv_nat hCpos).mul
    (tendsto_gammaQuotient hs)).mul (tendsto_zetaShiftValue t)
  rw [one_mul, one_mul] at hprod
  refine hprod.congr' ?_
  filter_upwards with m
  rw [gpart, ← Real.mul_rpow (by positivity) (norm_nonneg _),
    ← Real.mul_rpow (by positivity) (norm_nonneg _)]

/-- The squared non-oscillating part is invisible to a rescaled root. -/
theorem tendsto_gpart_sq_rpow_scaled (hs : ∀ m : ℕ, t ≠ (m : ℂ)) {a b : ℕ}
    (ha : 0 < a) :
    Tendsto (fun m : ℕ => ((gpart t m) ^ (2 : ℕ)) ^ (1 / ((a * m + b : ℕ) : ℝ)))
      atTop (𝓝 1) := by
  refine tendsto_rpow_scaled_of_tendsto_rpow_inv (fun m => by positivity) ?_ ha
  have hsq := (tendsto_gpart_rpow_inv hs).mul (tendsto_gpart_rpow_inv hs)
  rw [one_mul] at hsq
  refine hsq.congr' ?_
  filter_upwards with m
  rw [← Real.mul_rpow (gpart_nonneg t m) (gpart_nonneg t m), sq]

theorem cosShift_sq_periodic (t : ℂ) (m : ℕ) :
    (cosShift t (m + 4)) ^ (2 : ℕ) = (cosShift t m) ^ (2 : ℕ) := by
  rw [cosShift_periodic t m]

/-- The squared oscillating factor has rescaled root `limsup` one. -/
theorem limsup_cosShift_sq_rpow_scaled (t : ℂ) {a b : ℕ} (ha : 0 < a) :
    limsup (fun m : ℕ => ((cosShift t m) ^ (2 : ℕ)) ^ (1 / ((a * m + b : ℕ) : ℝ)))
      atTop = 1 := by
  obtain ⟨C, hC⟩ := exists_bound_of_periodic_nat (f := fun m : ℕ => (cosShift t m) ^ (2 : ℕ))
    (p := 4) (by norm_num) (cosShift_sq_periodic t)
  obtain ⟨k₀, hk₀⟩ : ∃ k₀ : ℕ, 0 < (cosShift t k₀) ^ (2 : ℕ) := by
    rcases exists_cosShift_pos t with h | h
    · exact ⟨0, by positivity⟩
    · exact ⟨1, by positivity⟩
  have hCpos : 0 < C := lt_of_lt_of_le hk₀ (hC k₀)
  have hnn : ∀ m : ℕ, (0 : ℝ) ≤ (cosShift t m) ^ (2 : ℕ) := fun m => by positivity
  have hlb : ∃ᶠ m in atTop, (cosShift t k₀) ^ (2 : ℕ) ≤ (cosShift t m) ^ (2 : ℕ) :=
    frequently_le_of_periodic (f := fun m : ℕ => (cosShift t m) ^ (2 : ℕ)) (p := 4)
      (by norm_num) (cosShift_sq_periodic t) k₀
  exact limsup_rpow_scaled_eq_one hCpos hk₀ hnn hC hlb ha

/-- **The squared remainder has rescaled root `limsup` one.** -/
theorem limsup_norm_zetaShiftRemainder_sq_rpow_scaled (hs : ∀ m : ℕ, t ≠ (m : ℂ))
    {a b : ℕ} (ha : 0 < a) :
    limsup (fun m : ℕ => (‖zetaShiftRemainder t m‖ ^ (2 : ℕ))
        ^ (1 / ((a * m + b : ℕ) : ℝ))) atTop = 1 := by
  have hcongr : ∀ m : ℕ, (‖zetaShiftRemainder t m‖ ^ (2 : ℕ))
      ^ (1 / ((a * m + b : ℕ) : ℝ))
      = ((gpart t m) ^ (2 : ℕ)) ^ (1 / ((a * m + b : ℕ) : ℝ))
        * ((cosShift t m) ^ (2 : ℕ)) ^ (1 / ((a * m + b : ℕ) : ℝ)) := by
    intro m
    rw [norm_zetaShiftRemainder_eq, mul_pow,
      Real.mul_rpow (by positivity) (by positivity)]
  rw [limsup_congr (Filter.Eventually.of_forall hcongr)]
  refine limsup_mul_eq_one_of_tendsto_one (tendsto_gpart_sq_rpow_scaled hs ha)
    (fun m => Real.rpow_nonneg (by positivity) _) ?_
    (limsup_cosShift_sq_rpow_scaled t ha)
  obtain ⟨C, hC⟩ := exists_bound_of_periodic_nat
    (f := fun m : ℕ => (cosShift t m) ^ (2 : ℕ)) (p := 4) (by norm_num)
    (cosShift_sq_periodic t)
  obtain ⟨k₀, hk₀⟩ : ∃ k₀ : ℕ, 0 < (cosShift t k₀) ^ (2 : ℕ) := by
    rcases exists_cosShift_pos t with h | h
    · exact ⟨0, by positivity⟩
    · exact ⟨1, by positivity⟩
  have hnn : ∀ m : ℕ, (0 : ℝ) ≤ (cosShift t m) ^ (2 : ℕ) := fun m => by positivity
  have hCpos : (0 : ℝ) < C := lt_of_lt_of_le hk₀ (hC k₀)
  exact isBoundedUnder_rpow_scaled hCpos hnn hC ha

theorem isBoundedUnder_norm_zetaShiftRemainder_sq_rpow_scaled
    (hs : ∀ m : ℕ, t ≠ (m : ℂ)) {a b : ℕ} (ha : 0 < a) :
    IsBoundedUnder (· ≤ ·) atTop (fun m : ℕ => (‖zetaShiftRemainder t m‖ ^ (2 : ℕ))
      ^ (1 / ((a * m + b : ℕ) : ℝ))) := by
  obtain ⟨C, hC⟩ := exists_bound_of_periodic_nat
    (f := fun m : ℕ => (cosShift t m) ^ (2 : ℕ)) (p := 4) (by norm_num)
    (cosShift_sq_periodic t)
  obtain ⟨k₀, hk₀⟩ : ∃ k₀ : ℕ, 0 < (cosShift t k₀) ^ (2 : ℕ) := by
    rcases exists_cosShift_pos t with h | h
    · exact ⟨0, by positivity⟩
    · exact ⟨1, by positivity⟩
  have hnn : ∀ m : ℕ, (0 : ℝ) ≤ (cosShift t m) ^ (2 : ℕ) := fun m => by positivity
  have hCpos : (0 : ℝ) < C := lt_of_lt_of_le hk₀ (hC k₀)
  have hcos := isBoundedUnder_rpow_scaled (b := b) hCpos hnn hC ha
  obtain ⟨B, hB⟩ := id hcos
  rw [Filter.eventually_map] at hB
  have hcongr : ∀ m : ℕ, (‖zetaShiftRemainder t m‖ ^ (2 : ℕ))
      ^ (1 / ((a * m + b : ℕ) : ℝ))
      = ((gpart t m) ^ (2 : ℕ)) ^ (1 / ((a * m + b : ℕ) : ℝ))
        * ((cosShift t m) ^ (2 : ℕ)) ^ (1 / ((a * m + b : ℕ) : ℝ)) := by
    intro m
    rw [norm_zetaShiftRemainder_eq, mul_pow,
      Real.mul_rpow (by positivity) (by positivity)]
  refine ⟨2 * max B 0, ?_⟩
  rw [Filter.eventually_map]
  filter_upwards [(tendsto_gpart_sq_rpow_scaled (b := b) hs ha).eventually_lt_const
    (by norm_num : (1 : ℝ) < 2), hB] with m h2 hBm
  rw [hcongr m]
  exact mul_le_mul h2.le (le_trans hBm (le_max_left _ _))
    (Real.rpow_nonneg (by positivity) _) (by norm_num)

end Split

section Assembly

variable {s₀ : ℂ}

/-- The shift-lattice coefficients of the squared zeta function in degree two. -/
noncomputable def zetaSquareCoeff (s₀ : ℂ) (k : ℕ) : ℂ :=
  (riemannZeta (s₀ - (k : ℂ) / 2)) ^ 2 / (Nat.factorial k : ℂ)

theorem half_shift_even (hs : ∀ k : ℕ, s₀ ≠ (k : ℂ) / 2) (m : ℕ) : s₀ ≠ (m : ℂ) := by
  intro hc
  refine hs (2 * m) ?_
  rw [hc]
  push_cast
  ring

theorem half_shift_odd (hs : ∀ k : ℕ, s₀ ≠ (k : ℂ) / 2) (m : ℕ) :
    s₀ - 1 / 2 ≠ (m : ℂ) := by
  intro hc
  refine hs (2 * m + 1) ?_
  push_cast
  linear_combination hc

theorem centralBinom_ne_zeroC (m : ℕ) : (Nat.centralBinom m : ℂ) ≠ 0 := by
  exact_mod_cast (Nat.centralBinom_pos m).ne'

theorem factorial_ne_zeroC (m : ℕ) : (Nat.factorial m : ℂ) ≠ 0 := by
  exact_mod_cast Nat.factorial_ne_zero m

theorem factorial_two_mul (m : ℕ) :
    (Nat.factorial (2 * m) : ℂ)
      = (Nat.centralBinom m : ℂ) * ((Nat.factorial m : ℂ) * (Nat.factorial m : ℂ)) := by
  exact_mod_cast congrArg (fun n : ℕ => (n : ℂ)) (centralBinom_mul_factorial_sq m).symm

/-- The even coefficients of the degree-two shift lattice. -/
theorem zetaSquareCoeff_even (hs : ∀ k : ℕ, s₀ ≠ (k : ℂ) / 2) (m : ℕ) :
    zetaSquareCoeff s₀ (2 * m)
      = ((2 * (Real.pi : ℂ))⁻¹) ^ (2 * m) * (zetaShiftRemainder s₀ m) ^ 2
        / (Nat.centralBinom m : ℂ) := by
  have hdec := zetaShift_decomposition (half_shift_even hs) m
  have hzeta : riemannZeta (s₀ - (m : ℂ))
      = ((2 * (Real.pi : ℂ))⁻¹) ^ m * zetaShiftRemainder s₀ m
        * (Nat.factorial m : ℂ) := (div_eq_iff (factorial_ne_zeroC m)).mp hdec
  have harg : s₀ - ((2 * m : ℕ) : ℂ) / 2 = s₀ - (m : ℂ) := by push_cast; ring
  rw [zetaSquareCoeff, harg, hzeta, factorial_two_mul]
  have hC := centralBinom_ne_zeroC m
  have hF := factorial_ne_zeroC m
  field_simp
  ring

/-- The odd coefficients of the degree-two shift lattice. -/
theorem zetaSquareCoeff_odd (hs : ∀ k : ℕ, s₀ ≠ (k : ℂ) / 2) (m : ℕ) :
    zetaSquareCoeff s₀ (2 * m + 1)
      = ((2 * (Real.pi : ℂ))⁻¹) ^ (2 * m) * (zetaShiftRemainder (s₀ - 1 / 2) m) ^ 2
        / (((2 * m + 1 : ℕ) : ℂ) * (Nat.centralBinom m : ℂ)) := by
  have hdec := zetaShift_decomposition (half_shift_odd hs) m
  have hzeta : riemannZeta (s₀ - 1 / 2 - (m : ℂ))
      = ((2 * (Real.pi : ℂ))⁻¹) ^ m * zetaShiftRemainder (s₀ - 1 / 2) m
        * (Nat.factorial m : ℂ) := (div_eq_iff (factorial_ne_zeroC m)).mp hdec
  have harg : s₀ - ((2 * m + 1 : ℕ) : ℂ) / 2 = s₀ - 1 / 2 - (m : ℂ) := by
    push_cast
    ring
  have hfacs : (Nat.factorial (2 * m + 1) : ℂ)
      = ((2 * m + 1 : ℕ) : ℂ) * ((Nat.centralBinom m : ℂ)
        * ((Nat.factorial m : ℂ) * (Nat.factorial m : ℂ))) := by
    rw [← factorial_two_mul m]
    have : Nat.factorial (2 * m + 1) = (2 * m + 1) * Nat.factorial (2 * m) :=
      Nat.factorial_succ (2 * m)
    rw [this]
    push_cast
    ring
  rw [zetaSquareCoeff, harg, hzeta, hfacs]
  have hC := centralBinom_ne_zeroC m
  have hF := factorial_ne_zeroC m
  have hodd : ((2 * m + 1 : ℕ) : ℂ) ≠ 0 := by
    have : (2 * m + 1 : ℕ) ≠ 0 := by omega
    exact_mod_cast this
  field_simp
  ring

end Assembly

section Norms

variable {s₀ : ℂ}

/-- The even remainder after extracting the cusp geometric factor. -/
noncomputable def vEven (s₀ : ℂ) (m : ℕ) : ℝ :=
  centralQuot m * ‖zetaShiftRemainder s₀ m‖ ^ (2 : ℕ)

/-- The odd remainder after extracting the cusp geometric factor. -/
noncomputable def vOdd (s₀ : ℂ) (m : ℕ) : ℝ :=
  (4 * Real.pi * centralQuot m / ((2 * m + 1 : ℕ) : ℝ))
    * ‖zetaShiftRemainder (s₀ - 1 / 2) m‖ ^ (2 : ℕ)

theorem vEven_nonneg (s₀ : ℂ) (m : ℕ) : 0 ≤ vEven s₀ m := by
  rw [vEven]
  have := (centralQuot_pos m).le
  positivity

theorem vOdd_nonneg (s₀ : ℂ) (m : ℕ) : 0 ≤ vOdd s₀ m := by
  rw [vOdd]
  have h1 := (centralQuot_pos m).le
  have h2 : (0 : ℝ) ≤ ((2 * m + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  have h3 : (0 : ℝ) ≤ Real.pi := Real.pi_pos.le
  positivity

theorem norm_two_pi_inv : ‖((2 * (Real.pi : ℂ))⁻¹)‖ = 1 / (2 * Real.pi) := by
  rw [norm_inv, one_div]
  congr 1
  simp [abs_of_pos Real.pi_pos]

theorem quarter_pow_identity (m : ℕ) :
    ((1 : ℝ) / (2 * Real.pi)) ^ (2 * m) = ((1 : ℝ) / (4 * Real.pi)) ^ (2 * m) * (4 : ℝ) ^ m := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  rw [pow_mul, pow_mul, ← mul_pow]
  congr 1
  field_simp
  ring

theorem norm_zetaSquareCoeff_even (hs : ∀ k : ℕ, s₀ ≠ (k : ℂ) / 2) (m : ℕ) :
    ‖zetaSquareCoeff s₀ (2 * m)‖
      = ((1 : ℝ) / (4 * Real.pi)) ^ (2 * m) * vEven s₀ m := by
  rw [zetaSquareCoeff_even hs m, norm_div, norm_mul, norm_pow, norm_pow,
    norm_two_pi_inv, Complex.norm_natCast, vEven, centralQuot, quarter_pow_identity]
  have hC : (0 : ℝ) < (Nat.centralBinom m : ℝ) := centralBinom_posR m
  field_simp

theorem norm_zetaSquareCoeff_odd (hs : ∀ k : ℕ, s₀ ≠ (k : ℂ) / 2) (m : ℕ) :
    ‖zetaSquareCoeff s₀ (2 * m + 1)‖
      = ((1 : ℝ) / (4 * Real.pi)) ^ (2 * m + 1) * vOdd s₀ m := by
  rw [zetaSquareCoeff_odd hs m, norm_div, norm_mul, norm_pow, norm_pow, norm_mul,
    norm_two_pi_inv, Complex.norm_natCast, Complex.norm_natCast, vOdd, centralQuot,
    quarter_pow_identity]
  have hC : (0 : ℝ) < (Nat.centralBinom m : ℝ) := centralBinom_posR m
  have hodd : (0 : ℝ) < ((2 * m + 1 : ℕ) : ℝ) := by
    have : 0 < 2 * m + 1 := by omega
    exact_mod_cast this
  have hpine : (Real.pi : ℝ) ≠ 0 := Real.pi_pos.ne'
  field_simp
  have key : (4 * Real.pi) * ((1 : ℝ) / (4 * Real.pi)) ^ (2 * m + 1)
      = ((1 : ℝ) / (4 * Real.pi)) ^ (2 * m) := by
    rw [pow_succ]
    field_simp
  rw [← key]
  ring

end Norms

section Final

variable {s₀ : ℂ}

theorem limsup_vEven (hs : ∀ k : ℕ, s₀ ≠ (k : ℂ) / 2) :
    limsup (fun m : ℕ => (vEven s₀ m) ^ (1 / ((2 * m : ℕ) : ℝ))) atTop = 1 := by
  have hcq : Tendsto (fun m : ℕ => (centralQuot m) ^ (1 / ((2 * m : ℕ) : ℝ)))
      atTop (𝓝 1) := by
    simpa using tendsto_centralQuot_rpow_scaled (a := 2) (b := 0) (by norm_num)
  have hRb : IsBoundedUnder (· ≤ ·) atTop
      (fun m : ℕ => (‖zetaShiftRemainder s₀ m‖ ^ (2 : ℕ)) ^ (1 / ((2 * m : ℕ) : ℝ))) := by
    simpa using isBoundedUnder_norm_zetaShiftRemainder_sq_rpow_scaled
      (t := s₀) (a := 2) (b := 0) (half_shift_even hs) (by norm_num)
  have hRl : limsup (fun m : ℕ =>
      (‖zetaShiftRemainder s₀ m‖ ^ (2 : ℕ)) ^ (1 / ((2 * m : ℕ) : ℝ))) atTop = 1 := by
    simpa using limsup_norm_zetaShiftRemainder_sq_rpow_scaled
      (t := s₀) (a := 2) (b := 0) (half_shift_even hs) (by norm_num)
  have hcongr : ∀ m : ℕ, (vEven s₀ m) ^ (1 / ((2 * m : ℕ) : ℝ))
      = (centralQuot m) ^ (1 / ((2 * m : ℕ) : ℝ))
        * (‖zetaShiftRemainder s₀ m‖ ^ (2 : ℕ)) ^ (1 / ((2 * m : ℕ) : ℝ)) := by
    intro m
    rw [vEven, Real.mul_rpow (centralQuot_pos m).le (by positivity)]
  rw [limsup_congr (Filter.Eventually.of_forall hcongr)]
  exact limsup_mul_eq_one_of_tendsto_one hcq
    (fun m => Real.rpow_nonneg (by positivity) _) hRb hRl

theorem isBoundedUnder_vEven (hs : ∀ k : ℕ, s₀ ≠ (k : ℂ) / 2) :
    IsBoundedUnder (· ≤ ·) atTop
      (fun m : ℕ => (vEven s₀ m) ^ (1 / ((2 * m : ℕ) : ℝ))) := by
  have hcq : Tendsto (fun m : ℕ => (centralQuot m) ^ (1 / ((2 * m : ℕ) : ℝ)))
      atTop (𝓝 1) := by
    simpa using tendsto_centralQuot_rpow_scaled (a := 2) (b := 0) (by norm_num)
  have hRb : IsBoundedUnder (· ≤ ·) atTop
      (fun m : ℕ => (‖zetaShiftRemainder s₀ m‖ ^ (2 : ℕ)) ^ (1 / ((2 * m : ℕ) : ℝ))) := by
    simpa using isBoundedUnder_norm_zetaShiftRemainder_sq_rpow_scaled
      (t := s₀) (a := 2) (b := 0) (half_shift_even hs) (by norm_num)
  obtain ⟨B, hB⟩ := id hRb
  rw [Filter.eventually_map] at hB
  refine ⟨2 * max B 0, ?_⟩
  rw [Filter.eventually_map]
  filter_upwards [hcq.eventually_lt_const (by norm_num : (1 : ℝ) < 2), hB] with m h2 hBm
  rw [vEven, Real.mul_rpow (centralQuot_pos m).le (by positivity)]
  exact mul_le_mul h2.le (le_trans hBm (le_max_left _ _))
    (Real.rpow_nonneg (by positivity) _) (by norm_num)

/-- The polynomial prefactor of the odd remainder. -/
noncomputable def pOdd (m : ℕ) : ℝ :=
  4 * Real.pi * centralQuot m / ((2 * m + 1 : ℕ) : ℝ)

theorem pOdd_pos (m : ℕ) : 0 < pOdd m := by
  have h1 := centralQuot_pos m
  have h2 : (0 : ℝ) < ((2 * m + 1 : ℕ) : ℝ) := by
    have : 0 < 2 * m + 1 := by omega
    exact_mod_cast this
  have h3 : (0 : ℝ) < Real.pi := Real.pi_pos
  rw [pOdd]
  positivity

theorem tendsto_pOdd_rpow :
    Tendsto (fun m : ℕ => (pOdd m) ^ (1 / ((2 * m + 1 : ℕ) : ℝ))) atTop (𝓝 1) := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  refine tendsto_rpow_scaled_of_polynomial_bounds (C₁ := 4 * Real.pi / 3)
    (C₂ := 8 * Real.pi) (B := 1) (fun m => (pOdd_pos m).le) (by positivity)
    (by positivity) ?_ ?_ (by norm_num)
  · filter_upwards [eventually_gt_atTop 0] with m hm
    have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    have hm0 : (0 : ℝ) < (m : ℝ) := by linarith
    have hcast : ((2 * m + 1 : ℕ) : ℝ) = 2 * (m : ℝ) + 1 := by push_cast; ring
    have hden : (0 : ℝ) < 2 * (m : ℝ) + 1 := by linarith
    have hcq := one_le_centralQuot m
    rw [Real.rpow_neg_one, pOdd, hcast, le_div_iff₀ hden]
    have h1 : (m : ℝ)⁻¹ * (2 * (m : ℝ) + 1) ≤ 3 := by
      rw [inv_mul_eq_div, div_le_iff₀ hm0]
      linarith
    have hstep : 4 * Real.pi / 3 * (m : ℝ)⁻¹ * (2 * (m : ℝ) + 1) ≤ 4 * Real.pi := by
      have hpos : (0 : ℝ) ≤ 4 * Real.pi / 3 := by positivity
      calc 4 * Real.pi / 3 * (m : ℝ)⁻¹ * (2 * (m : ℝ) + 1)
          = (4 * Real.pi / 3) * ((m : ℝ)⁻¹ * (2 * (m : ℝ) + 1)) := by ring
        _ ≤ (4 * Real.pi / 3) * 3 := mul_le_mul_of_nonneg_left h1 hpos
        _ = 4 * Real.pi := by ring
    have h2 : 4 * Real.pi ≤ 4 * Real.pi * centralQuot m := by
      nlinarith [hcq, hpi]
    linarith
  · filter_upwards [eventually_gt_atTop 0] with m hm
    have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    have hcast : ((2 * m + 1 : ℕ) : ℝ) = 2 * (m : ℝ) + 1 := by push_cast; ring
    have hden : (0 : ℝ) < 2 * (m : ℝ) + 1 := by linarith
    have hcq := centralQuot_le m hm
    rw [Real.rpow_one, pOdd, hcast, div_le_iff₀ hden]
    have h1 : 4 * Real.pi * centralQuot m ≤ 4 * Real.pi * (2 * (m : ℝ)) :=
      mul_le_mul_of_nonneg_left hcq (by positivity)
    have hm0 : (0 : ℝ) < (m : ℝ) := by linarith
    have hprod : (0 : ℝ) ≤ 16 * Real.pi * (m : ℝ) * (m : ℝ) := by positivity
    have h2 : 4 * Real.pi * (2 * (m : ℝ)) ≤ 8 * Real.pi * (m : ℝ) * (2 * (m : ℝ) + 1) := by
      nlinarith [hprod]
    linarith

theorem limsup_vOdd (hs : ∀ k : ℕ, s₀ ≠ (k : ℂ) / 2) :
    limsup (fun m : ℕ => (vOdd s₀ m) ^ (1 / ((2 * m + 1 : ℕ) : ℝ))) atTop = 1 := by
  have hRb := isBoundedUnder_norm_zetaShiftRemainder_sq_rpow_scaled
    (t := s₀ - 1 / 2) (a := 2) (b := 1) (half_shift_odd hs) (by norm_num)
  have hRl := limsup_norm_zetaShiftRemainder_sq_rpow_scaled
    (t := s₀ - 1 / 2) (a := 2) (b := 1) (half_shift_odd hs) (by norm_num)
  have hcongr : ∀ m : ℕ, (vOdd s₀ m) ^ (1 / ((2 * m + 1 : ℕ) : ℝ))
      = (pOdd m) ^ (1 / ((2 * m + 1 : ℕ) : ℝ))
        * (‖zetaShiftRemainder (s₀ - 1 / 2) m‖ ^ (2 : ℕ))
            ^ (1 / ((2 * m + 1 : ℕ) : ℝ)) := by
    intro m
    rw [vOdd, ← pOdd, Real.mul_rpow (pOdd_pos m).le (by positivity)]
  rw [limsup_congr (Filter.Eventually.of_forall hcongr)]
  exact limsup_mul_eq_one_of_tendsto_one tendsto_pOdd_rpow
    (fun m => Real.rpow_nonneg (by positivity) _) hRb hRl

theorem isBoundedUnder_vOdd (hs : ∀ k : ℕ, s₀ ≠ (k : ℂ) / 2) :
    IsBoundedUnder (· ≤ ·) atTop
      (fun m : ℕ => (vOdd s₀ m) ^ (1 / ((2 * m + 1 : ℕ) : ℝ))) := by
  have hRb := isBoundedUnder_norm_zetaShiftRemainder_sq_rpow_scaled
    (t := s₀ - 1 / 2) (a := 2) (b := 1) (half_shift_odd hs) (by norm_num)
  obtain ⟨B, hB⟩ := id hRb
  rw [Filter.eventually_map] at hB
  refine ⟨2 * max B 0, ?_⟩
  rw [Filter.eventually_map]
  filter_upwards [tendsto_pOdd_rpow.eventually_lt_const (by norm_num : (1 : ℝ) < 2), hB]
    with m h2 hBm
  rw [vOdd, ← pOdd, Real.mul_rpow (pOdd_pos m).le (by positivity)]
  exact mul_le_mul h2.le (le_trans hBm (le_max_left _ _))
    (Real.rpow_nonneg (by positivity) _) (by norm_num)

theorem limsup_parity_even (hs : ∀ k : ℕ, s₀ ≠ (k : ℂ) / 2) :
    limsup (fun m : ℕ =>
        ((‖zetaSquareCoeff s₀ (2 * m)‖₊ ^ (1 / ((2 * m : ℕ) : ℝ)) : ℝ≥0) : ℝ≥0∞))
      atTop = ENNReal.ofReal (1 / (4 * Real.pi)) := by
  have hev : ∀ᶠ m : ℕ in atTop,
      ((‖zetaSquareCoeff s₀ (2 * m)‖₊ ^ (1 / ((2 * m : ℕ) : ℝ)) : ℝ≥0) : ℝ≥0∞)
        = ENNReal.ofReal (1 / (4 * Real.pi))
          * ENNReal.ofReal ((vEven s₀ m) ^ (1 / ((2 * m : ℕ) : ℝ))) := by
    filter_upwards [eventually_gt_atTop 0] with m hm
    have hmR : (0 : ℝ) < ((2 * m : ℕ) : ℝ) := by
      have : 0 < 2 * m := by omega
      exact_mod_cast this
    have hcoef : (((1 : ℝ) / (4 * Real.pi)) ^ (2 * m)) ^ (1 / ((2 * m : ℕ) : ℝ))
        = (1 : ℝ) / (4 * Real.pi) := by
      rw [← Real.rpow_natCast ((1 : ℝ) / (4 * Real.pi)) (2 * m),
        ← Real.rpow_mul (by positivity),
        show ((2 * m : ℕ) : ℝ) * (1 / ((2 * m : ℕ) : ℝ)) = 1 from by field_simp,
        Real.rpow_one]
    rw [coe_nnnorm_rpow_eq_ofReal, norm_zetaSquareCoeff_even hs m,
      Real.mul_rpow (by positivity) (vEven_nonneg s₀ m), hcoef,
      ENNReal.ofReal_mul (by positivity)]
  rw [limsup_congr hev, ENNReal.limsup_const_mul_of_ne_top ENNReal.ofReal_ne_top,
    limsup_ofReal_eq (fun m => Real.rpow_nonneg (vEven_nonneg s₀ m) _)
      (isBoundedUnder_vEven hs), limsup_vEven hs, ENNReal.ofReal_one, mul_one]

theorem limsup_parity_odd (hs : ∀ k : ℕ, s₀ ≠ (k : ℂ) / 2) :
    limsup (fun m : ℕ =>
        ((‖zetaSquareCoeff s₀ (2 * m + 1)‖₊ ^ (1 / ((2 * m + 1 : ℕ) : ℝ)) : ℝ≥0) : ℝ≥0∞))
      atTop = ENNReal.ofReal (1 / (4 * Real.pi)) := by
  have hev : ∀ᶠ m : ℕ in atTop,
      ((‖zetaSquareCoeff s₀ (2 * m + 1)‖₊ ^ (1 / ((2 * m + 1 : ℕ) : ℝ)) : ℝ≥0) : ℝ≥0∞)
        = ENNReal.ofReal (1 / (4 * Real.pi))
          * ENNReal.ofReal ((vOdd s₀ m) ^ (1 / ((2 * m + 1 : ℕ) : ℝ))) := by
    filter_upwards with m
    have hmR : (0 : ℝ) < ((2 * m + 1 : ℕ) : ℝ) := by
      have : 0 < 2 * m + 1 := by omega
      exact_mod_cast this
    have hcoef : (((1 : ℝ) / (4 * Real.pi)) ^ (2 * m + 1)) ^ (1 / ((2 * m + 1 : ℕ) : ℝ))
        = (1 : ℝ) / (4 * Real.pi) := by
      rw [← Real.rpow_natCast ((1 : ℝ) / (4 * Real.pi)) (2 * m + 1),
        ← Real.rpow_mul (by positivity),
        show ((2 * m + 1 : ℕ) : ℝ) * (1 / ((2 * m + 1 : ℕ) : ℝ)) = 1 from by field_simp,
        Real.rpow_one]
    rw [coe_nnnorm_rpow_eq_ofReal, norm_zetaSquareCoeff_odd hs m,
      Real.mul_rpow (by positivity) (vOdd_nonneg s₀ m), hcoef,
      ENNReal.ofReal_mul (by positivity)]
  rw [limsup_congr hev, ENNReal.limsup_const_mul_of_ne_top ENNReal.ofReal_ne_top,
    limsup_ofReal_eq (fun m => Real.rpow_nonneg (vOdd_nonneg s₀ m) _)
      (isBoundedUnder_vOdd hs), limsup_vOdd hs, ENNReal.ofReal_one, mul_one]

/-- **The cusp constant of the squared zeta shift lattice.**  In degree two and
conductor one the factorially normalized shifted values of `ζ²` grow exactly like
`1/(4π)`, matching the spectral prediction `1/(2π Δ(0))` with cusp gap
`Δ(0) = 2`. -/
theorem hadamardLimsup_zetaSquareShift (hs : ∀ k : ℕ, s₀ ≠ (k : ℂ) / 2) :
    hadamardLimsup (zetaSquareCoeff s₀) = ENNReal.ofReal (1 / (4 * Real.pi)) := by
  rw [hadamardLimsup_eq_parity_sup, limsup_parity_even hs, limsup_parity_odd hs,
    sup_idem]

end Final

end RHTower
