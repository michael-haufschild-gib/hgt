import GaloisForLFunctions.ArithmeticDiscreteness.ACuspOfTheBohrLiftForcesNearCoincidences
import GaloisForLFunctions.ArithmeticDiscreteness.EulerProductsCreateTheNearCoincidences
import GaloisForLFunctions.ArithmeticDiscreteness.NearCoincidencesAreJointSmallValues
import GaloisForLFunctions.ArithmeticDiscreteness.ThePrimeFlowIsDiophantineAtTorsionPoints

/-!
# The cusp repels at polynomial scale

A non-product collide-or-repel law. The cusp carrier `D(s) = (1 − 2^{−s})² − (1 − 3^{−s})³` has
near-coincidences at every scale (`cuspCarrier_collision_or_close_pair`); near its cusp they are
separated polynomially in the height (`cusp_local_repulsion`): two zeros `s₁ ≠ s₂` within `1/16`
whose midpoint `c` has `|1 − 2^{−c}|, |1 − 3^{−c}| ≤ r₀` and `|Im c| ≥ 1` satisfy
`|s₁ − s₂|² ≥ κ (2 + |Im c|)^{−K}`.

Mechanism.
* **Joint small values** (`norm_le_of_two_symmetric_zeros`, `norm_deriv_le_of_two_symmetric_zeros`):
  with `h = (s₂ − s₁)/2`, `|D(c)| ≤ E|h|²` and `|D'(c)| ≤ E|h|`.
* **Cusp algebra** (`cusp_algebra`): for `a = 1 − 2^{−c}`, `b = 1 − 3^{−c}` small, `D = a² − b³` and
  `D' = 2a log 2 (1 − a) − 3b² log 3 (1 − b)` give `|a| ≤ α₁|h| + α₂|b|²` and then
  `|b|³ ≤ β|h|²`, `|a|³ ≤ γ|h|²`.
* **The flow** (`flow_coordinate_le`): `|p^{−it} − 1| ≤ 2|1 − p^{−c}|` for `t = Im c`, and the prime
  flow is Diophantine at the torsion point `(1, 1)` (`primeFlow_diophantine_at_torsion`).
-/

open Complex Metric

noncomputable section

namespace GaloisForLFunctions.ArithmeticDiscreteness

theorem hasDerivAt_cuspCarrier (s : ℂ) :
    HasDerivAt cuspCarrier (2 * (1 - (2 : ℂ) ^ (-s)) * (Complex.log 2 * (2 : ℂ) ^ (-s)) -
      3 * (1 - (3 : ℂ) ^ (-s)) ^ 2 * (Complex.log 3 * (3 : ℂ) ^ (-s))) s := by
  have h2 := hasDerivAt_cpow_neg two_ne_zero s
  have h3 := hasDerivAt_cpow_neg three_ne_zero s
  have h := ((h2.const_sub 1).pow 2).sub ((h3.const_sub 1).pow 3)
  unfold cuspCarrier
  exact h.congr_deriv (by push_cast; ring)

theorem differentiable_cuspCarrier : Differentiable ℂ cuspCarrier := fun s =>
  (hasDerivAt_cuspCarrier s).differentiableAt

theorem norm_cuspCarrier_le {z : ℂ} (hz : -2 ≤ z.re) : ‖cuspCarrier z‖ ≤ 1025 := by
  have h2 : ‖(2 : ℂ) ^ (-z)‖ ≤ 4 := by
    rw [norm_two_cpow_neg]
    calc (2 : ℝ) ^ (-z.re) ≤ (2 : ℝ) ^ (2 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = 4 := by norm_num
  have h3 : ‖(3 : ℂ) ^ (-z)‖ ≤ 9 := by
    rw [norm_three_cpow_neg]
    calc (3 : ℝ) ^ (-z.re) ≤ (3 : ℝ) ^ (2 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = 9 := by norm_num
  have ha : ‖1 - (2 : ℂ) ^ (-z)‖ ≤ 5 := (norm_sub_le _ _).trans (by rw [norm_one]; linarith)
  have hb : ‖1 - (3 : ℂ) ^ (-z)‖ ≤ 10 := (norm_sub_le _ _).trans (by rw [norm_one]; linarith)
  unfold cuspCarrier
  calc ‖(1 - (2 : ℂ) ^ (-z)) ^ 2 - (1 - (3 : ℂ) ^ (-z)) ^ 3‖
      ≤ ‖1 - (2 : ℂ) ^ (-z)‖ ^ 2 + ‖1 - (3 : ℂ) ^ (-z)‖ ^ 3 := by
        refine (norm_sub_le _ _).trans ?_; rw [norm_pow, norm_pow]
    _ ≤ 5 ^ 2 + 10 ^ 3 := by gcongr
    _ = 1025 := by norm_num

theorem cube_add_le (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) : (x + y) ^ 3 ≤ 4 * (x ^ 3 + y ^ 3) := by
  nlinarith [mul_nonneg (add_nonneg hx hy) (sq_nonneg (x - y))]

/-- **Cusp algebra.** -/
theorem cusp_algebra {a b : ℂ} {L₂ L₃ E h : ℝ} (hL₂ : 0 < L₂) (hL₃ : 0 < L₃) (hE : 0 ≤ E)
    (hh : 0 ≤ h) (hh1 : h ≤ 1) (ha : ‖a‖ ≤ 1 / 2) (hb : ‖b‖ ≤ 1 / 2)
    (hb' : ‖b‖ ≤ 1 / (4 * (9 * L₃ / (2 * L₂)) ^ 2))
    (hD : ‖a ^ 2 - b ^ 3‖ ≤ E * h ^ 2)
    (hD' : ‖2 * a * ((L₂ : ℂ) * (1 - a)) - 3 * b ^ 2 * ((L₃ : ℂ) * (1 - b))‖ ≤ E * h) :
    ‖b‖ ^ 3 ≤ 2 * (2 * (E / L₂) ^ 2 + E) * h ^ 2 ∧
      ‖a‖ ^ 3 ≤ 4 * ((E / L₂) ^ 3 + (9 * L₃ / (2 * L₂)) ^ 3 *
        (2 * (2 * (E / L₂) ^ 2 + E)) ^ 2) * h ^ 2 := by
  set α₁ := E / L₂ with hα₁
  set α₂ := 9 * L₃ / (2 * L₂) with hα₂
  have hα₁0 : 0 ≤ α₁ := by positivity
  have hα₂0 : 0 < α₂ := by positivity
  set A := ‖a‖ with hA
  set B := ‖b‖ with hB
  have hA0 : 0 ≤ A := norm_nonneg _
  have hB0 : 0 ≤ B := norm_nonneg _
  -- `|a| ≤ α₁ h + α₂ |b|²`
  have h1a : (1 / 2 : ℝ) ≤ ‖1 - a‖ := by
    have := norm_sub_norm_le (1 : ℂ) a; rw [norm_one] at this; linarith
  have h1b : ‖1 - b‖ ≤ 3 / 2 := (norm_sub_le _ _).trans (by rw [norm_one]; linarith)
  have haB : A ≤ α₁ * h + α₂ * B ^ 2 := by
    have hlow : L₂ * A ≤ ‖2 * a * ((L₂ : ℂ) * (1 - a))‖ := by
      calc L₂ * A = 2 * A * (L₂ * (1 / 2)) := by ring
        _ ≤ 2 * A * (L₂ * ‖1 - a‖) := by gcongr
        _ = ‖2 * a * ((L₂ : ℂ) * (1 - a))‖ := by
            rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
              abs_of_pos hL₂, show ‖(2 : ℂ)‖ = 2 by norm_num]
    have hup : ‖3 * b ^ 2 * ((L₃ : ℂ) * (1 - b))‖ ≤ 9 / 2 * L₃ * B ^ 2 := by
      calc ‖3 * b ^ 2 * ((L₃ : ℂ) * (1 - b))‖ = 3 * B ^ 2 * (L₃ * ‖1 - b‖) := by
            rw [norm_mul, norm_mul, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
              abs_of_pos hL₃, show ‖(3 : ℂ)‖ = 3 by norm_num]
        _ ≤ 3 * B ^ 2 * (L₃ * (3 / 2)) := by gcongr
        _ = 9 / 2 * L₃ * B ^ 2 := by ring
    have htri := norm_sub_norm_le (2 * a * ((L₂ : ℂ) * (1 - a)))
      (3 * b ^ 2 * ((L₃ : ℂ) * (1 - b)))
    have : L₂ * A ≤ E * h + 9 / 2 * L₃ * B ^ 2 := by linarith
    have key : A = (L₂ * A) / L₂ := by field_simp
    rw [key]
    calc (L₂ * A) / L₂ ≤ (E * h + 9 / 2 * L₃ * B ^ 2) / L₂ := div_le_div_of_nonneg_right this hL₂.le
      _ = α₁ * h + α₂ * B ^ 2 := by rw [hα₁, hα₂]; field_simp
  -- `|b|³ ≤ β h²`
  have hb3 : B ^ 3 ≤ 2 * (2 * α₁ ^ 2 + E) * h ^ 2 := by
    have h1 : B ^ 3 ≤ A ^ 2 + E * h ^ 2 := by
      have := norm_sub_le (a ^ 2) (a ^ 2 - b ^ 3)
      rw [sub_sub_cancel, norm_pow, norm_pow, ← hA, ← hB] at this
      linarith
    have h2 : A ^ 2 ≤ 2 * α₁ ^ 2 * h ^ 2 + 2 * α₂ ^ 2 * B ^ 4 := by
      have := pow_le_pow_left₀ hA0 haB 2
      nlinarith [sq_nonneg (α₁ * h - α₂ * B ^ 2)]
    have h3 : 2 * α₂ ^ 2 * B ^ 4 ≤ B ^ 3 / 2 := by
      have hα2 : 0 < α₂ ^ 2 := by positivity
      have hBb : B * (4 * α₂ ^ 2) ≤ 1 := by
        rw [le_div_iff₀ (by positivity)] at hb'; linarith
      have : 2 * α₂ ^ 2 * B ^ 4 = (B * (4 * α₂ ^ 2)) * B ^ 3 / 2 := by ring
      rw [this]
      have hB3 : 0 ≤ B ^ 3 := by positivity
      nlinarith
    nlinarith
  refine ⟨hb3, ?_⟩
  -- `|a|³ ≤ γ h²`
  have h4 : A ^ 3 ≤ 4 * ((α₁ * h) ^ 3 + (α₂ * B ^ 2) ^ 3) :=
    (pow_le_pow_left₀ hA0 haB 3).trans (cube_add_le _ _ (by positivity) (by positivity))
  have h5 : (α₂ * B ^ 2) ^ 3 ≤ α₂ ^ 3 * (2 * (2 * α₁ ^ 2 + E)) ^ 2 * h ^ 2 := by
    have hB6 : B ^ 6 ≤ (2 * (2 * α₁ ^ 2 + E) * h ^ 2) ^ 2 := by
      have : B ^ 6 = (B ^ 3) ^ 2 := by ring
      rw [this]; exact pow_le_pow_left₀ (by positivity) hb3 2
    have hh4 : h ^ 4 ≤ h ^ 2 := pow_le_pow_of_le_one hh hh1 (by norm_num)
    have : (α₂ * B ^ 2) ^ 3 = α₂ ^ 3 * B ^ 6 := by ring
    rw [this]
    have hα3 : 0 ≤ α₂ ^ 3 := by positivity
    calc α₂ ^ 3 * B ^ 6 ≤ α₂ ^ 3 * (2 * (2 * α₁ ^ 2 + E) * h ^ 2) ^ 2 :=
          mul_le_mul_of_nonneg_left hB6 hα3
      _ = α₂ ^ 3 * (2 * (2 * α₁ ^ 2 + E)) ^ 2 * h ^ 4 := by ring
      _ ≤ α₂ ^ 3 * (2 * (2 * α₁ ^ 2 + E)) ^ 2 * h ^ 2 :=
          mul_le_mul_of_nonneg_left hh4 (by positivity)
  have h6 : (α₁ * h) ^ 3 ≤ α₁ ^ 3 * h ^ 2 := by
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hh hh1 (by norm_num)) (by positivity)
  calc A ^ 3 ≤ 4 * ((α₁ * h) ^ 3 + (α₂ * B ^ 2) ^ 3) := h4
    _ ≤ 4 * (α₁ ^ 3 * h ^ 2 + α₂ ^ 3 * (2 * (2 * α₁ ^ 2 + E)) ^ 2 * h ^ 2) := by gcongr
    _ = 4 * (α₁ ^ 3 + α₂ ^ 3 * (2 * (2 * α₁ ^ 2 + E)) ^ 2) * h ^ 2 := by ring

/-- **The flow on the line is within twice the distance.** For `t = Im c`,
`|P^{−it} − 1| ≤ 2|1 − P^{−c}|`. -/
theorem flow_coordinate_le {P : ℝ} (hP : 0 < P) (c : ℂ) :
    ‖((P : ℝ) : ℂ) ^ (-((c.im : ℂ) * I)) - 1‖ ≤ 2 * ‖1 - ((P : ℝ) : ℂ) ^ (-c)‖ := by
  have hP0 : ((P : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hP.ne'
  have hsplit : ((P : ℝ) : ℂ) ^ (-c) =
      ((P : ℝ) : ℂ) ^ (-((c.re : ℂ))) * ((P : ℝ) : ℂ) ^ (-((c.im : ℂ) * I)) := by
    rw [← Complex.cpow_add _ _ hP0]
    congr 1
    conv_lhs => rw [← Complex.re_add_im c]
    ring
  have hunit : ‖((P : ℝ) : ℂ) ^ (-((c.im : ℂ) * I))‖ = 1 := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hP]; simp
  have hreal : ((P : ℝ) : ℂ) ^ (-((c.re : ℂ))) = ((P ^ (-c.re) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_neg, Complex.ofReal_cpow hP.le]
  have hmod : |P ^ (-c.re) - 1| ≤ ‖1 - ((P : ℝ) : ℂ) ^ (-c)‖ := by
    have h1 : ‖((P : ℝ) : ℂ) ^ (-c)‖ = P ^ (-c.re) := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hP, neg_re]
    have := abs_norm_sub_norm_le (((P : ℝ) : ℂ) ^ (-c)) 1
    rw [h1, norm_one, norm_sub_rev] at this
    exact this
  have hdiff : ‖((P : ℝ) : ℂ) ^ (-((c.im : ℂ) * I)) - ((P : ℝ) : ℂ) ^ (-c)‖ ≤
      ‖1 - ((P : ℝ) : ℂ) ^ (-c)‖ := by
    have e : ((P : ℝ) : ℂ) ^ (-((c.im : ℂ) * I)) - ((P : ℝ) : ℂ) ^ (-c) =
        ((P : ℝ) : ℂ) ^ (-((c.im : ℂ) * I)) * ((1 - P ^ (-c.re) : ℝ) : ℂ) := by
      rw [hsplit, hreal]; push_cast; ring
    rw [e, norm_mul, hunit, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_sub_comm]
    exact hmod
  calc ‖((P : ℝ) : ℂ) ^ (-((c.im : ℂ) * I)) - 1‖
      ≤ ‖((P : ℝ) : ℂ) ^ (-((c.im : ℂ) * I)) - ((P : ℝ) : ℂ) ^ (-c)‖ +
        ‖((P : ℝ) : ℂ) ^ (-c) - 1‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ ‖1 - ((P : ℝ) : ℂ) ^ (-c)‖ + ‖1 - ((P : ℝ) : ℂ) ^ (-c)‖ := by
        rw [norm_sub_rev (((P : ℝ) : ℂ) ^ (-c)) 1]; linarith
    _ = 2 * ‖1 - ((P : ℝ) : ℂ) ^ (-c)‖ := by ring

/-- Near the cusp the real part is above `−1`. -/
theorem neg_one_lt_re_of_near_cusp {c : ℂ} (h : ‖1 - (2 : ℂ) ^ (-c)‖ ≤ 1 / 2) : -1 < c.re := by
  have h1 : ‖(2 : ℂ) ^ (-c)‖ ≤ 3 / 2 := by
    have h2 := norm_sub_le_norm_sub_add_norm_sub ((2 : ℂ) ^ (-c)) 1 0
    rw [sub_zero, sub_zero, norm_one, norm_sub_rev] at h2
    linarith
  rw [norm_two_cpow_neg] at h1
  by_contra hle
  push Not at hle
  have : (2 : ℝ) ≤ (2 : ℝ) ^ (-c.re) := by
    calc (2 : ℝ) = (2 : ℝ) ^ (1 : ℝ) := by norm_num
      _ ≤ (2 : ℝ) ^ (-c.re) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  linarith

/-- **Joint small values of the cusp carrier.** -/
theorem cusp_joint_small {s₁ s₂ : ℂ} (h₁ : cuspCarrier s₁ = 0) (h₂ : cuspCarrier s₂ = 0)
    (hne : s₁ ≠ s₂) (hclose : ‖s₂ - s₁‖ ≤ 1 / 16) (hre : -1 < ((s₁ + s₂) / 2).re) :
    ‖cuspCarrier ((s₁ + s₂) / 2)‖ ≤ 393600 * ‖(s₂ - s₁) / 2‖ ^ 2 ∧
      ‖deriv cuspCarrier ((s₁ + s₂) / 2)‖ ≤ 393600 * ‖(s₂ - s₁) / 2‖ := by
  set c : ℂ := (s₁ + s₂) / 2 with hc
  set h : ℂ := (s₂ - s₁) / 2 with hh
  have hcm : c - h = s₁ := by rw [hc, hh]; ring
  have hcp : c + h = s₂ := by rw [hc, hh]; ring
  have hh0 : h ≠ 0 := by rw [hh]; exact div_ne_zero (sub_ne_zero.mpr (Ne.symm hne)) two_ne_zero
  have hhn : ‖h‖ ≤ (1 / 4) / 8 := by
    rw [hh, norm_div, show ‖(2 : ℂ)‖ = 2 by norm_num]; linarith
  have hM : ∀ z ∈ closedBall c (2 * (1 / 4)), ‖cuspCarrier z‖ ≤ 1025 := by
    intro z hz
    rw [mem_closedBall, dist_eq_norm] at hz
    have := (abs_re_le_norm (z - c)).trans hz
    rw [sub_re] at this
    exact norm_cuspCarrier_le (by linarith [(abs_le.mp this).1])
  have h1 : cuspCarrier (c - h) = 0 := by rw [hcm]; exact h₁
  have h2 : cuspCarrier (c + h) = 0 := by rw [hcp]; exact h₂
  have hv := norm_le_of_two_symmetric_zeros isOpen_univ differentiable_cuspCarrier.differentiableOn
    (by norm_num : (0 : ℝ) < 1 / 4) (Set.subset_univ _) hM hhn h1 h2
  have hd := norm_deriv_le_of_two_symmetric_zeros isOpen_univ
    differentiable_cuspCarrier.differentiableOn (by norm_num : (0 : ℝ) < 1 / 4)
    (Set.subset_univ _) hM hhn hh0 h1 h2
  constructor
  · calc ‖cuspCarrier c‖ ≤ 24 * 1025 / (1 / 4) ^ 2 * ‖h‖ ^ 2 := hv
      _ = 393600 * ‖h‖ ^ 2 := by norm_num
  · calc ‖deriv cuspCarrier c‖ ≤ 24 * 1025 / (1 / 4) ^ 2 * ‖h‖ := hd
      _ = 393600 * ‖h‖ := by norm_num

theorem max_cube_le (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) : max x y ^ 3 ≤ x ^ 3 + y ^ 3 := by
  rcases le_total x y with h | h
  · rw [max_eq_right h]; nlinarith [pow_nonneg hx 3]
  · rw [max_eq_left h]; nlinarith [pow_nonneg hy 3]

/-- **The cusp repels at polynomial scale.** -/
theorem cusp_local_repulsion :
    ∃ r₀ > 0, ∃ κ K : ℝ, 0 < κ ∧ 0 < K ∧ ∀ s₁ s₂ : ℂ, cuspCarrier s₁ = 0 → cuspCarrier s₂ = 0 →
      s₁ ≠ s₂ → ‖s₂ - s₁‖ ≤ 1 / 16 →
      ‖1 - (2 : ℂ) ^ (-((s₁ + s₂) / 2))‖ ≤ r₀ → ‖1 - (3 : ℂ) ^ (-((s₁ + s₂) / 2))‖ ≤ r₀ →
      1 ≤ |((s₁ + s₂) / 2).im| →
        κ * (2 + |((s₁ + s₂) / 2).im|) ^ (-K) ≤ ‖s₂ - s₁‖ ^ 2 := by
  have hL₂ : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hL₃ : 0 < Real.log 3 := Real.log_pos (by norm_num)
  obtain ⟨α₂, hα₂⟩ : ∃ α₂, α₂ = 9 * Real.log 3 / (2 * Real.log 2) := ⟨_, rfl⟩
  have hα₂0 : 0 < α₂ := by rw [hα₂]; positivity
  obtain ⟨β, hβ⟩ : ∃ β, β = 2 * (2 * (393600 / Real.log 2) ^ 2 + 393600) := ⟨_, rfl⟩
  obtain ⟨γ, hγ⟩ : ∃ γ, γ = 4 * ((393600 / Real.log 2) ^ 3 + α₂ ^ 3 * β ^ 2) := ⟨_, rfl⟩
  have hβ0 : 0 < β := by rw [hβ]; positivity
  have hγ0 : 0 < γ := by rw [hγ]; positivity
  obtain ⟨c₀, C₀, hc₀, hC₀, hflow⟩ := primeFlow_diophantine_at_torsion Nat.prime_two
    Nat.prime_three (by norm_num) (N := 1) one_pos 0 0
  refine ⟨min (1 / 2) (1 / (4 * α₂ ^ 2)), lt_min (by norm_num) (by positivity),
    c₀ ^ 3 / (2 * (β + γ)), 3 * C₀, by positivity, by positivity,
    fun s₁ s₂ h₁ h₂ hne hclose ha hb ht => ?_⟩
  set c : ℂ := (s₁ + s₂) / 2 with hc
  have ha2 : ‖1 - (2 : ℂ) ^ (-c)‖ ≤ 1 / 2 := ha.trans (min_le_left _ _)
  have hb2 : ‖1 - (3 : ℂ) ^ (-c)‖ ≤ 1 / 2 := hb.trans (min_le_left _ _)
  have hb' : ‖1 - (3 : ℂ) ^ (-c)‖ ≤ 1 / (4 * α₂ ^ 2) := hb.trans (min_le_right _ _)
  obtain ⟨hv, hd⟩ := cusp_joint_small h₁ h₂ hne hclose (neg_one_lt_re_of_near_cusp ha2)
  have hhn1 : ‖(s₂ - s₁) / 2‖ ≤ 1 := by
    rw [norm_div, show ‖(2 : ℂ)‖ = 2 by norm_num]; linarith
  -- the cusp algebra at `a = 1 − 2^{−c}`, `b = 1 − 3^{−c}`
  have hderiv : deriv cuspCarrier c =
      2 * (1 - (2 : ℂ) ^ (-c)) * (((Real.log 2 : ℝ) : ℂ) * (1 - (1 - (2 : ℂ) ^ (-c)))) -
        3 * (1 - (3 : ℂ) ^ (-c)) ^ 2 * (((Real.log 3 : ℝ) : ℂ) * (1 - (1 - (3 : ℂ) ^ (-c)))) := by
    have e2 : Complex.log 2 = ((Real.log 2 : ℝ) : ℂ) := by
      rw [Complex.ofReal_log (by norm_num : (0 : ℝ) ≤ 2)]; norm_num
    have e3 : Complex.log 3 = ((Real.log 3 : ℝ) : ℂ) := by
      rw [Complex.ofReal_log (by norm_num : (0 : ℝ) ≤ 3)]; norm_num
    rw [(hasDerivAt_cuspCarrier c).deriv, e2, e3]
    ring
  have hval : cuspCarrier c = (1 - (2 : ℂ) ^ (-c)) ^ 2 - (1 - (3 : ℂ) ^ (-c)) ^ 3 := rfl
  rw [hderiv] at hd
  rw [hval] at hv
  obtain ⟨hB3, hA3⟩ := cusp_algebra hL₂ hL₃ (by norm_num) (norm_nonneg _) hhn1 ha2 hb2
    (by rw [← hα₂]; exact hb') hv hd
  rw [← hβ] at hB3
  rw [← hα₂, ← hβ, ← hγ] at hA3
  -- the flow at `t = Im c`
  have hf2 := flow_coordinate_le (P := 2) (by norm_num) c
  have hf3 := flow_coordinate_le (P := 3) (by norm_num) c
  have hfl := hflow c.im ht
  simp only [Int.cast_zero, mul_zero, zero_div, Complex.ofReal_zero, zero_mul, Complex.exp_zero,
    Nat.cast_ofNat] at hfl
  push_cast at hf2 hf3
  set A := ‖1 - (2 : ℂ) ^ (-c)‖ with hA
  set B := ‖1 - (3 : ℂ) ^ (-c)‖ with hB
  have hX : c₀ * (2 + |c.im|) ^ (-C₀) ≤ 2 * max A B :=
    hfl.trans (max_le (hf2.trans (by gcongr; exact le_max_left _ _))
      (hf3.trans (by gcongr; exact le_max_right _ _)))
  have hX0 : 0 ≤ c₀ * (2 + |c.im|) ^ (-C₀) := by positivity
  have hcube : (c₀ * (2 + |c.im|) ^ (-C₀)) ^ 3 ≤ 8 * (A ^ 3 + B ^ 3) := by
    calc (c₀ * (2 + |c.im|) ^ (-C₀)) ^ 3 ≤ (2 * max A B) ^ 3 := pow_le_pow_left₀ hX0 hX 3
      _ = 8 * max A B ^ 3 := by ring
      _ ≤ 8 * (A ^ 3 + B ^ 3) := by
          gcongr; exact max_cube_le _ _ (norm_nonneg _) (norm_nonneg _)
  have hpow : (c₀ * (2 + |c.im|) ^ (-C₀)) ^ 3 = c₀ ^ 3 * (2 + |c.im|) ^ (-(3 * C₀)) := by
    rw [mul_pow, ← Real.rpow_natCast ((2 + |c.im|) ^ (-C₀)), ← Real.rpow_mul (by positivity)]
    congr 2; push_cast; ring
  have hhs : ‖(s₂ - s₁) / 2‖ ^ 2 = ‖s₂ - s₁‖ ^ 2 / 4 := by
    rw [norm_div, show ‖(2 : ℂ)‖ = 2 by norm_num]; ring
  rw [hpow] at hcube
  rw [hhs] at hB3 hA3
  have hfin : c₀ ^ 3 * (2 + |c.im|) ^ (-(3 * C₀)) ≤ 2 * (β + γ) * ‖s₂ - s₁‖ ^ 2 := by
    nlinarith
  rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  linarith

end GaloisForLFunctions.ArithmeticDiscreteness
