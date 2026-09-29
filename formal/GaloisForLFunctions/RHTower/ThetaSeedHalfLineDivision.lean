import GaloisForLFunctions.RHTower.ThetaZeroDivisionRealization
import GaloisForLFunctions.RHTower.ThetaCuspFinitePrimeFluxWindow

/-!
# Zero division on the literal theta seed and the Euler resolvent

For the literal seed `h = thetaCuspLogSeed`, `h(x) = 2π e^{5x/2} (2π e^{2x} − 3) e^{−π e^{2x}}` is
positive on the physical half-line `x ≥ 0` and satisfies
`h(x+t) ≤ C₀ exp(9t/2 − π e^{2x}(e^{2t} − 1)) h(x)`; hence
`∫₀^∞ t^k e^{ct} h(x+t) dt ≤ K e^{−2(k+1)x} h(x)` for `x ≥ 0`.

* The outward Green operator `T_α g(x) = α ∫₀^∞ sin(αt) g(x+t) dt` preserves the class of
  seed-dominated functions, with `|T_α g| ≤ K e^{−2x} h` and `T_α g / h → 0`.
* The Euler resolvent `R_S g(x) = Σ_{n∈S} n^{−1/2} g(x + log n)` gives `R h = k` (all integers) and
  `R_N h = k_N` (smooth numbers); by Fubini with the majorant `C e^{|Im α| t} k(x+t)`,
  `T_α (R_S g) = R_S (T_α g)` on `x ≥ 0`, and the same holds for finite products of Green operators
  and for real linear combinations.
* On `x ≥ 0` the reflected list divisions of `k` are the plain iterates, so `R (T_L h) = G_L`.
-/
open MeasureTheory Set Filter Topology Complex
open scoped ENNReal NNReal

namespace RHTower

noncomputable section

/-! ## The literal seed on the physical half-line -/

theorem thetaCuspLogSeed_eq (x : ℝ) :
    thetaCuspLogSeed x = 2 * Real.pi * Real.exp (5 * x / 2) * (2 * Real.pi * Real.exp (2 * x) - 3) *
      Real.exp (-(Real.pi * Real.exp (2 * x))) := by
  simp only [thetaCuspLogSeed, thetaCuspSeed]
  have h2 : Real.exp x ^ 2 = Real.exp (2 * x) := by rw [← Real.exp_nat_mul]; norm_num
  have h4 : Real.exp x ^ 4 = Real.exp (2 * x) * Real.exp (2 * x) := by
    rw [← Real.exp_add, ← Real.exp_nat_mul]; ring_nf
  have h5 : Real.exp (5 * x / 2) = Real.exp (x / 2) * Real.exp (2 * x) := by
    rw [← Real.exp_add]; ring_nf
  rw [h2, h4, h5, show -Real.pi * Real.exp (2 * x) = -(Real.pi * Real.exp (2 * x)) by ring]
  ring

theorem thetaCuspLogSeed_pos {x : ℝ} (hx : 0 ≤ x) : 0 < thetaCuspLogSeed x := by
  rw [thetaCuspLogSeed_eq]
  have h1 : 1 ≤ Real.exp (2 * x) := Real.one_le_exp (by linarith)
  have hπ := Real.pi_gt_three
  have : 0 < 2 * Real.pi * Real.exp (2 * x) - 3 := by nlinarith
  positivity

/-- **Seed ratio bound.**  For `x, t ≥ 0`,
`h(x+t) ≤ C₀ exp(9t/2 − π e^{2x}(e^{2t} − 1)) h(x)` with `C₀ = 2π/(2π − 3)`. -/
theorem thetaCuspLogSeed_shift_le {x t : ℝ} (hx : 0 ≤ x) (ht : 0 ≤ t) :
    thetaCuspLogSeed (x + t) ≤ 2 * Real.pi / (2 * Real.pi - 3) *
      Real.exp (9 / 2 * t - Real.pi * Real.exp (2 * x) * (Real.exp (2 * t) - 1)) *
        thetaCuspLogSeed x := by
  have hπ := Real.pi_gt_three
  set u := Real.exp (2 * x) with hu
  have hu1 : 1 ≤ u := Real.one_le_exp (by linarith)
  have hv1 : 1 ≤ Real.exp (2 * t) := Real.one_le_exp (by linarith)
  have hpos : 0 < 2 * Real.pi * u - 3 := by nlinarith
  have hc : 0 < 2 * Real.pi - 3 := by linarith
  rw [thetaCuspLogSeed_eq, thetaCuspLogSeed_eq]
  have e1 : Real.exp (5 * (x + t) / 2) = Real.exp (5 * x / 2) * Real.exp (5 / 2 * t) := by
    rw [← Real.exp_add]; ring_nf
  have e2 : Real.exp (2 * (x + t)) = u * Real.exp (2 * t) := by rw [hu, ← Real.exp_add]; ring_nf
  have e3 : Real.exp (9 / 2 * t - Real.pi * u * (Real.exp (2 * t) - 1)) =
      Real.exp (5 / 2 * t) * Real.exp (2 * t) *
        (Real.exp (-(Real.pi * (u * Real.exp (2 * t)))) / Real.exp (-(Real.pi * u))) := by
    rw [← Real.exp_add, ← Real.exp_sub, ← Real.exp_add]; ring_nf
  rw [e1, e2, e3]
  have hA : 0 < Real.exp (5 * x / 2) := Real.exp_pos _
  have hB : 0 < Real.exp (-(Real.pi * u)) := Real.exp_pos _
  have hE : 0 < Real.exp (-(Real.pi * (u * Real.exp (2 * t)))) := Real.exp_pos _
  have hF : 0 < Real.exp (5 / 2 * t) := Real.exp_pos _
  have key : 2 * Real.pi * (u * Real.exp (2 * t)) - 3 ≤
      2 * Real.pi / (2 * Real.pi - 3) * Real.exp (2 * t) * (2 * Real.pi * u - 3) := by
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, le_div_iff₀ hc]
    nlinarith [mul_nonneg (sub_nonneg.2 hu1) (sub_nonneg.2 hv1)]
  calc 2 * Real.pi * (Real.exp (5 * x / 2) * Real.exp (5 / 2 * t)) *
        (2 * Real.pi * (u * Real.exp (2 * t)) - 3) * Real.exp (-(Real.pi * (u * Real.exp (2 * t))))
      = (2 * Real.pi * Real.exp (5 * x / 2) * Real.exp (5 / 2 * t) *
          Real.exp (-(Real.pi * (u * Real.exp (2 * t))))) *
          (2 * Real.pi * (u * Real.exp (2 * t)) - 3) := by ring
    _ ≤ (2 * Real.pi * Real.exp (5 * x / 2) * Real.exp (5 / 2 * t) *
          Real.exp (-(Real.pi * (u * Real.exp (2 * t))))) *
          (2 * Real.pi / (2 * Real.pi - 3) * Real.exp (2 * t) * (2 * Real.pi * u - 3)) :=
        mul_le_mul_of_nonneg_left key (by positivity)
    _ = _ := by field_simp; rw [hu]

/-! ## Weighted envelope integrals -/

theorem integral_natPow_mul_exp_neg_mul_Ioi (k : ℕ) {c : ℝ} (hc : 0 < c) :
    ∫ t in Ioi (0 : ℝ), t ^ k * Real.exp (-(c * t)) = k.factorial / c ^ (k + 1) := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := (k : ℝ) + 1) (r := c) (by positivity) hc
  simp only [add_sub_cancel_right, Real.rpow_natCast] at h
  rw [h, Real.Gamma_nat_eq_factorial, show (k : ℝ) + 1 = ((k + 1 : ℕ) : ℝ) by norm_num,
    Real.rpow_natCast]
  simp only [one_div, inv_pow]
  ring

theorem integrableOn_natPow_mul_exp_neg_mul_Ioi (k : ℕ) {c : ℝ} (hc : 0 < c) :
    IntegrableOn (fun t : ℝ => t ^ k * Real.exp (-(c * t))) (Ioi 0) := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := (k : ℝ) + 1) (r := c) (by positivity) hc
  have hne : (∫ t : ℝ in Ioi 0, t ^ ((k : ℝ) + 1 - 1) * Real.exp (-(c * t))) ≠ 0 := by
    rw [h]; positivity
  have h2 := Integrable.of_integral_ne_zero hne
  simp only [add_sub_cancel_right, Real.rpow_natCast] at h2
  exact h2

/-- The super-exponential envelope `t^k exp(bt − π(e^{2t} − 1))` is integrable on `(0, ∞)`. -/
theorem integrableOn_seedEnvelope (k : ℕ) (b : ℝ) :
    IntegrableOn (fun t : ℝ => t ^ k * Real.exp (b * t - Real.pi * (Real.exp (2 * t) - 1)))
      (Ioi 0) := by
  have hπ := Real.pi_pos
  refine (((integrable_exp_neg_mul_sq hπ).const_mul
    (k.factorial * Real.exp ((b + 1) ^ 2 / (4 * Real.pi)))).integrableOn).mono'
    ((by fun_prop : Continuous fun t : ℝ =>
      t ^ k * Real.exp (b * t - Real.pi * (Real.exp (2 * t) - 1))).aestronglyMeasurable)
    ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht0 : 0 ≤ t := le_of_lt ht
  rw [Real.norm_of_nonneg (mul_nonneg (pow_nonneg ht0 k) (Real.exp_pos _).le)]
  have hq := Real.quadratic_le_exp_of_nonneg (x := 2 * t) (by linarith)
  have hsq : (b + 1) * t - Real.pi * t ^ 2 ≤ (b + 1) ^ 2 / (4 * Real.pi) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith [sq_nonneg (2 * Real.pi * t - (b + 1))]
  calc t ^ k * Real.exp (b * t - Real.pi * (Real.exp (2 * t) - 1))
      ≤ (k.factorial * Real.exp t) * Real.exp (b * t - Real.pi * (Real.exp (2 * t) - 1)) :=
        mul_le_mul_of_nonneg_right (pow_le_factorial_mul_exp ht0 k) (Real.exp_pos _).le
    _ = k.factorial * Real.exp ((b + 1) * t - Real.pi * (Real.exp (2 * t) - 1)) := by
        rw [mul_assoc, ← Real.exp_add]; ring_nf
    _ ≤ k.factorial * (Real.exp ((b + 1) ^ 2 / (4 * Real.pi)) * Real.exp (-Real.pi * t ^ 2)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        rw [← Real.exp_add]
        refine Real.exp_le_exp.2 ?_
        nlinarith
    _ = _ := by ring

/-- **Weighted seed tail integrals.**  For every `k` and `c`, there is `K` with
`∫₀^∞ t^k e^{ct} h(x+t) dt ≤ K e^{-2(k+1)x} h(x)` for all `x ≥ 0`. -/
theorem exists_integral_pow_exp_seed_shift_le (k : ℕ) (c : ℝ) :
    ∃ K, ∀ x, 0 ≤ x →
      IntegrableOn (fun t => t ^ k * Real.exp (c * t) * thetaCuspLogSeed (x + t)) (Ioi 0) ∧
      ∫ t in Ioi (0 : ℝ), t ^ k * Real.exp (c * t) * thetaCuspLogSeed (x + t) ≤
        K * Real.exp (-(2 * (k + 1) * x)) * thetaCuspLogSeed x := by
  have hπ := Real.pi_gt_three
  set C₀ := 2 * Real.pi / (2 * Real.pi - 3)
  have hC₀ : 0 < C₀ := div_pos (by positivity) (by linarith)
  set B := |c| + 9 / 2
  set J := ∫ t in Ioi (0 : ℝ), t ^ k * Real.exp ((c + 9 / 2) * t - Real.pi * (Real.exp (2 * t) - 1))
  have hJ0 : 0 ≤ J := setIntegral_nonneg measurableSet_Ioi fun t ht =>
    mul_nonneg (pow_nonneg (le_of_lt ht) k) (Real.exp_pos _).le
  refine ⟨max (C₀ * J * (B / Real.pi) ^ (k + 1)) (C₀ * k.factorial / Real.pi ^ (k + 1)),
    fun x hx => ?_⟩
  have hh := thetaCuspLogSeed_pos hx
  have hu1 : 1 ≤ Real.exp (2 * x) := Real.one_le_exp (by linarith)
  -- pointwise domination by the envelope
  have hdom : ∀ t, 0 < t → t ^ k * Real.exp (c * t) * thetaCuspLogSeed (x + t) ≤
      C₀ * thetaCuspLogSeed x * (t ^ k * Real.exp ((c + 9 / 2) * t -
        Real.pi * Real.exp (2 * x) * (Real.exp (2 * t) - 1))) := by
    intro t ht
    have hr := thetaCuspLogSeed_shift_le hx ht.le
    have hpow := pow_nonneg ht.le k
    calc t ^ k * Real.exp (c * t) * thetaCuspLogSeed (x + t)
        ≤ t ^ k * Real.exp (c * t) * (C₀ * Real.exp (9 / 2 * t - Real.pi * Real.exp (2 * x) *
          (Real.exp (2 * t) - 1)) * thetaCuspLogSeed x) :=
          mul_le_mul_of_nonneg_left hr (mul_nonneg hpow (Real.exp_pos _).le)
      _ = _ := by
          rw [show (c + 9 / 2) * t - Real.pi * Real.exp (2 * x) * (Real.exp (2 * t) - 1) =
            c * t + (9 / 2 * t - Real.pi * Real.exp (2 * x) * (Real.exp (2 * t) - 1)) by ring,
            Real.exp_add]
          ring
  have hmeas : AEStronglyMeasurable (fun t => t ^ k * Real.exp (c * t) * thetaCuspLogSeed (x + t))
      (volume.restrict (Ioi 0)) :=
    ((by fun_prop : Continuous fun t : ℝ => t ^ k * Real.exp (c * t)).mul
      (continuous_thetaCuspLogSeed.comp (continuous_const.add continuous_id))).aestronglyMeasurable
  -- the envelope with `e^{2x} ≥ 1`
  have hglob : ∀ t, 0 < t → t ^ k * Real.exp ((c + 9 / 2) * t -
      Real.pi * Real.exp (2 * x) * (Real.exp (2 * t) - 1)) ≤
      t ^ k * Real.exp ((c + 9 / 2) * t - Real.pi * (Real.exp (2 * t) - 1)) := fun t ht => by
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (pow_nonneg ht.le k)
    have hv : 0 ≤ Real.exp (2 * t) - 1 := by linarith [Real.one_le_exp (by linarith : 0 ≤ 2 * t)]
    nlinarith [mul_nonneg (mul_nonneg Real.pi_pos.le (sub_nonneg.2 hu1)) hv]
  have hint : IntegrableOn (fun t => t ^ k * Real.exp (c * t) * thetaCuspLogSeed (x + t))
      (Ioi 0) := by
    refine ((integrableOn_seedEnvelope k (c + 9 / 2)).const_mul (C₀ * thetaCuspLogSeed x)).mono'
      hmeas ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht' : 0 < t := ht
    rw [Real.norm_of_nonneg (mul_nonneg (mul_nonneg (pow_nonneg ht'.le k)
      (Real.exp_pos _).le) (thetaCuspLogSeed_pos (by linarith [hx, ht'.le])).le)]
    exact (hdom t ht').trans (mul_le_mul_of_nonneg_left (hglob t ht') (by positivity))
  refine ⟨hint, ?_⟩
  by_cases hlarge : B ≤ Real.pi * Real.exp (2 * x)
  · -- tail regime: `exp(9t/2 − π e^{2x}(e^{2t}−1)) ≤ exp((9/2 − 2π e^{2x}) t)`
    set a := 2 * Real.pi * Real.exp (2 * x) - (c + 9 / 2)
    have ha : Real.pi * Real.exp (2 * x) ≤ a := by
      have := le_abs_self c
      have hBdef : B = |c| + 9 / 2 := rfl
      simp only [a]; linarith
    have hapos : 0 < a := lt_of_lt_of_le (by positivity) ha
    have hbound : ∀ t, 0 < t → t ^ k * Real.exp (c * t) * thetaCuspLogSeed (x + t) ≤
        C₀ * thetaCuspLogSeed x * (t ^ k * Real.exp (-(a * t))) := by
      intro t ht
      refine (hdom t ht).trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.2 ?_) (pow_nonneg ht.le k)) (by positivity))
      have hq : 2 * t ≤ Real.exp (2 * t) - 1 := by
        linarith [Real.add_one_le_exp (2 * t)]
      have : Real.pi * Real.exp (2 * x) * (2 * t) ≤
          Real.pi * Real.exp (2 * x) * (Real.exp (2 * t) - 1) :=
        mul_le_mul_of_nonneg_left hq (by positivity)
      simp only [a]; nlinarith
    calc ∫ t in Ioi (0 : ℝ), t ^ k * Real.exp (c * t) * thetaCuspLogSeed (x + t)
        ≤ ∫ t in Ioi (0 : ℝ), C₀ * thetaCuspLogSeed x * (t ^ k * Real.exp (-(a * t))) :=
          setIntegral_mono_on hint ((integrableOn_natPow_mul_exp_neg_mul_Ioi k hapos).const_mul _)
            measurableSet_Ioi fun t ht => hbound t ht
      _ = C₀ * thetaCuspLogSeed x * (k.factorial / a ^ (k + 1)) := by
          rw [integral_const_mul, integral_natPow_mul_exp_neg_mul_Ioi k hapos]
      _ ≤ C₀ * thetaCuspLogSeed x * (k.factorial / (Real.pi * Real.exp (2 * x)) ^ (k + 1)) := by
          refine mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left (by positivity)
            (by positivity) (pow_le_pow_left₀ (by positivity) ha _)) (by positivity)
      _ = C₀ * k.factorial / Real.pi ^ (k + 1) * Real.exp (-(2 * (k + 1) * x)) *
            thetaCuspLogSeed x := by
          rw [mul_pow, ← Real.exp_nat_mul, show -(2 * ((k : ℝ) + 1) * x) =
            -(((k + 1 : ℕ) : ℝ) * (2 * x)) by push_cast; ring, Real.exp_neg]
          field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right _ _)
            (Real.exp_pos _).le) hh.le
  · -- compact regime: `e^{-2(k+1)x} ≥ (π/B)^{k+1}`
    push Not at hlarge
    have hB : 0 < B := by positivity
    have hexp : 1 ≤ (B / Real.pi) ^ (k + 1) * Real.exp (-(2 * (k + 1) * x)) := by
      have h1 : 1 ≤ B / Real.pi * Real.exp (-(2 * x)) := by
        rw [Real.exp_neg, ← div_eq_mul_inv, le_div_iff₀ (Real.exp_pos _), one_mul,
          le_div_iff₀ Real.pi_pos]
        linarith
      have h2 : (B / Real.pi) ^ (k + 1) * Real.exp (-(2 * (k + 1) * x)) =
          (B / Real.pi * Real.exp (-(2 * x))) ^ (k + 1) := by
        rw [mul_pow, ← Real.exp_nat_mul]
        congr 2
        push_cast
        ring
      rw [h2]
      exact one_le_pow₀ h1
    calc ∫ t in Ioi (0 : ℝ), t ^ k * Real.exp (c * t) * thetaCuspLogSeed (x + t)
        ≤ ∫ t in Ioi (0 : ℝ), C₀ * thetaCuspLogSeed x *
            (t ^ k * Real.exp ((c + 9 / 2) * t - Real.pi * (Real.exp (2 * t) - 1))) :=
          setIntegral_mono_on hint ((integrableOn_seedEnvelope k _).const_mul _)
            measurableSet_Ioi fun t ht => (hdom t ht).trans
              (mul_le_mul_of_nonneg_left (hglob t ht) (by positivity))
      _ = C₀ * J * thetaCuspLogSeed x := by rw [integral_const_mul]; ring
      _ ≤ C₀ * J * ((B / Real.pi) ^ (k + 1) * Real.exp (-(2 * (k + 1) * x))) *
            thetaCuspLogSeed x := by
          refine mul_le_mul_of_nonneg_right ?_ hh.le
          nlinarith [mul_nonneg hC₀.le hJ0]
      _ ≤ _ := by
          rw [← mul_assoc (C₀ * J)]
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _)
            (Real.exp_pos _).le) hh.le

/-! ## Seed-dominated functions and the outward Green operator -/

/-- The seed `h` as a complex function. -/
def thetaSeedC (x : ℝ) : ℂ := (thetaCuspLogSeed x : ℂ)

/-- Functions on the physical half-line `x ≥ 0` dominated by the seed `h`. -/
structure SeedDominated (g : ℝ → ℂ) : Prop where
  stronglyMeasurable : StronglyMeasurable g
  bound : ∃ C, ∀ y, 0 ≤ y → ‖g y‖ ≤ C * thetaCuspLogSeed y

theorem seedDominated_thetaSeedC : SeedDominated thetaSeedC :=
  ⟨(Complex.continuous_ofReal.comp continuous_thetaCuspLogSeed).stronglyMeasurable, 1, fun y hy => by
    rw [thetaSeedC, Complex.norm_real, Real.norm_of_nonneg (thetaCuspLogSeed_pos hy).le, one_mul]⟩

theorem SeedDominated.exists_bound_nonneg {g : ℝ → ℂ} (hg : SeedDominated g) :
    ∃ C, 0 ≤ C ∧ ∀ y, 0 ≤ y → ‖g y‖ ≤ C * thetaCuspLogSeed y := by
  obtain ⟨C, hC⟩ := hg.bound
  exact ⟨C, (mul_nonneg_iff_of_pos_right (thetaCuspLogSeed_pos le_rfl)).1
    ((norm_nonneg _).trans (hC 0 le_rfl)), hC⟩

theorem SeedDominated.integrableOn_sin_mul {g : ℝ → ℂ} (hg : SeedDominated g) (α : ℂ) {x : ℝ}
    (hx : 0 ≤ x) : IntegrableOn (fun t : ℝ => Complex.sin (α * t) * g (x + t)) (Ioi 0) := by
  obtain ⟨C, hC0, hC⟩ := hg.exists_bound_nonneg
  obtain ⟨K, hK⟩ := exists_integral_pow_exp_seed_shift_le 0 |α.im|
  refine ((hK x hx).1.const_mul C).mono'
    ((by fun_prop : Continuous fun t : ℝ => Complex.sin (α * t)).aestronglyMeasurable.mul
      ((hg.stronglyMeasurable.comp_measurable (measurable_const.add measurable_id)).aestronglyMeasurable))
    ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht' : 0 < t := ht
  rw [norm_mul, pow_zero, one_mul]
  calc ‖Complex.sin (α * t)‖ * ‖g (x + t)‖
      ≤ Real.exp (|α.im| * t) * (C * thetaCuspLogSeed (x + t)) := by
        refine mul_le_mul ?_ (hC _ (by linarith)) (norm_nonneg _) (Real.exp_pos _).le
        simpa [abs_of_pos ht'] using norm_csin_mul_ofReal_le α t
    _ = C * (Real.exp (|α.im| * t) * thetaCuspLogSeed (x + t)) := by ring

/-- **The outward Green operator on seed-dominated functions**: `|T_α g| ≤ K e^{-2x} h` on `x ≥ 0`. -/
theorem SeedDominated.exists_norm_outwardSine_le {g : ℝ → ℂ} (hg : SeedDominated g) (α : ℂ) :
    ∃ K, ∀ x, 0 ≤ x → ‖outwardSine α g x‖ ≤ K * Real.exp (-(2 * x)) * thetaCuspLogSeed x := by
  obtain ⟨C, hC0, hC⟩ := hg.exists_bound_nonneg
  obtain ⟨K, hK⟩ := exists_integral_pow_exp_seed_shift_le 0 |α.im|
  refine ⟨‖α‖ * C * K, fun x hx => ?_⟩
  rw [outwardSine, norm_mul]
  have hb : ∀ᵐ t : ℝ ∂(volume.restrict (Ioi (0 : ℝ))), ‖Complex.sin (α * (t : ℂ)) * g (x + t)‖ ≤
      C * (t ^ 0 * Real.exp (|α.im| * t) * thetaCuspLogSeed (x + t)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht' : 0 < t := ht
    rw [norm_mul, pow_zero, one_mul]
    calc ‖Complex.sin (α * t)‖ * ‖g (x + t)‖
        ≤ Real.exp (|α.im| * t) * (C * thetaCuspLogSeed (x + t)) := by
          refine mul_le_mul ?_ (hC _ (by linarith)) (norm_nonneg _) (Real.exp_pos _).le
          simpa [abs_of_pos ht'] using norm_csin_mul_ofReal_le α t
      _ = _ := by ring
  have hI := norm_integral_le_of_norm_le ((hK x hx).1.const_mul C) hb
  rw [integral_const_mul] at hI
  have h2 := (hK x hx).2
  simp only [Nat.cast_zero, zero_add, mul_one] at h2
  calc ‖α‖ * ‖∫ t in Ioi (0 : ℝ), Complex.sin (α * t) * g (x + t)‖
      ≤ ‖α‖ * (C * ∫ t in Ioi (0 : ℝ), t ^ 0 * Real.exp (|α.im| * t) * thetaCuspLogSeed (x + t)) :=
        mul_le_mul_of_nonneg_left hI (norm_nonneg _)
    _ ≤ ‖α‖ * (C * (K * Real.exp (-(2 * x)) * thetaCuspLogSeed x)) := by
        gcongr
    _ = _ := by ring

theorem stronglyMeasurable_outwardSine {g : ℝ → ℂ} (hg : StronglyMeasurable g) (α : ℂ) :
    StronglyMeasurable (outwardSine α g) := by
  have h : StronglyMeasurable (Function.uncurry fun (x t : ℝ) => Complex.sin (α * t) * g (x + t)) :=
    ((by fun_prop : Continuous fun p : ℝ × ℝ => Complex.sin (α * p.2)).stronglyMeasurable).mul
      (hg.comp_measurable (measurable_fst.add measurable_snd))
  exact (StronglyMeasurable.integral_prod_right (ν := volume.restrict (Ioi (0 : ℝ))) h).const_mul α

theorem seedDominated_outwardSine {g : ℝ → ℂ} (hg : SeedDominated g) (α : ℂ) :
    SeedDominated (outwardSine α g) := by
  obtain ⟨K, hK⟩ := hg.exists_norm_outwardSine_le α
  refine ⟨stronglyMeasurable_outwardSine hg.stronglyMeasurable α, max K 0, fun y hy => ?_⟩
  refine (hK y hy).trans ?_
  have he : Real.exp (-(2 * y)) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  have hh := (thetaCuspLogSeed_pos hy).le
  calc K * Real.exp (-(2 * y)) * thetaCuspLogSeed y ≤ max K 0 * Real.exp (-(2 * y)) *
        thetaCuspLogSeed y := by gcongr; exact le_max_left _ _
    _ ≤ max K 0 * 1 * thetaCuspLogSeed y := by gcongr
    _ = _ := by ring

/-- **Seed tail.**  `T_α g / h → 0` at `+∞` for seed-dominated `g`. -/
theorem SeedDominated.tendsto_outwardSine_div {g : ℝ → ℂ} (hg : SeedDominated g) (α : ℂ) :
    Tendsto (fun x => ‖outwardSine α g x‖ / thetaCuspLogSeed x) atTop (𝓝 0) := by
  obtain ⟨K, hK⟩ := hg.exists_norm_outwardSine_le α
  have hlim : Tendsto (fun x : ℝ => K * Real.exp (-(2 * x))) atTop (𝓝 0) := by
    have := (Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 2))).const_mul K
    simpa [Function.comp] using this
  refine squeeze_zero' ?_ ?_ hlim
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
    exact div_nonneg (norm_nonneg _) (thetaCuspLogSeed_pos hx).le
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
    rw [div_le_iff₀ (thetaCuspLogSeed_pos hx)]
    exact hK x hx

/-! ## The Euler resolvent and its commutation with zero division -/

/-- The Euler resolvent over a set `S` of integers, `R_S g(x) = Σ_{n ∈ S} n^{-1/2} g(x + log n)`:
`S = ℕ` gives the all-integer resolvent and `S` = the `(N+1)`-smooth numbers the finite-prime
resolvent (the term `n = 0` has weight `0`). -/
def seedResolvent (S : Set ℕ) (g : ℝ → ℂ) (x : ℝ) : ℂ :=
  ∑' n : S, ((((n : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * g (x + Real.log (n : ℕ))

theorem rpow_neg_half_mul_thetaCuspLogSeed (n : ℕ) (y : ℝ) :
    (n : ℝ) ^ (-(1 / 2 : ℝ)) * thetaCuspLogSeed (y + Real.log n) = thetaCuspSourceTerm y n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [thetaCuspSourceTerm, thetaCuspSeed]
  · exact invSqrt_mul_logTranslate_thetaCuspLogSeed hn y

theorem thetaCuspSourceTerm_nonneg {y : ℝ} (hy : 0 ≤ y) (n : ℕ) : 0 ≤ thetaCuspSourceTerm y n := by
  rw [← rpow_neg_half_mul_thetaCuspLogSeed]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have hlog := Real.log_nonneg (by exact_mod_cast hn : (1 : ℝ) ≤ n)
    exact mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)
      (thetaCuspLogSeed_pos (by linarith)).le

theorem norm_seedWeight_mul_le {g : ℝ → ℂ} {C : ℝ}
    (hC : ∀ y, 0 ≤ y → ‖g y‖ ≤ C * thetaCuspLogSeed y) {y : ℝ} (hy : 0 ≤ y) (n : ℕ) :
    ‖(((n : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * g (y + Real.log n)‖ ≤ C * thetaCuspSourceTerm y n := by
  rw [← rpow_neg_half_mul_thetaCuspLogSeed]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have hlog := Real.log_nonneg (by exact_mod_cast hn : (1 : ℝ) ≤ n)
    have hw : 0 ≤ (n : ℝ) ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg (Nat.cast_nonneg n) _
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hw]
    calc (n : ℝ) ^ (-(1 / 2 : ℝ)) * ‖g (y + Real.log n)‖ ≤
          (n : ℝ) ^ (-(1 / 2 : ℝ)) * (C * thetaCuspLogSeed (y + Real.log n)) :=
          mul_le_mul_of_nonneg_left (hC _ (by linarith)) hw
      _ = _ := by ring

theorem tsum_subtype_thetaCuspSourceTerm_le (S : Set ℕ) {y : ℝ} (hy : 0 ≤ y) :
    ∑' n : S, thetaCuspSourceTerm y n ≤ thetaCuspFullSource y :=
  ((summable_thetaCuspSourceTerm y).subtype S).tsum_le_tsum_of_inj Subtype.val
    Subtype.val_injective (fun c _ => thetaCuspSourceTerm_nonneg hy c) (fun _ => le_rfl)
    (summable_thetaCuspSourceTerm y)

theorem SeedDominated.summable_seedResolvent {g : ℝ → ℂ} (hg : SeedDominated g) (S : Set ℕ)
    {y : ℝ} (hy : 0 ≤ y) :
    Summable fun n : S => ((((n : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * g (y + Real.log (n : ℕ)) := by
  obtain ⟨C, -, hC⟩ := hg.exists_bound_nonneg
  exact (((summable_thetaCuspSourceTerm y).subtype S).mul_left C).of_norm_bounded
    fun n => norm_seedWeight_mul_le hC hy n

/-- `|R_S g| ≤ C k` on the physical half-line. -/
theorem SeedDominated.norm_seedResolvent_le {g : ℝ → ℂ} {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ y, 0 ≤ y → ‖g y‖ ≤ C * thetaCuspLogSeed y) (S : Set ℕ) {y : ℝ} (hy : 0 ≤ y) :
    ‖seedResolvent S g y‖ ≤ C * thetaCuspFullSource y := by
  have hs : Summable fun n : S => C * thetaCuspSourceTerm y n :=
    ((summable_thetaCuspSourceTerm y).subtype S).mul_left C
  calc ‖seedResolvent S g y‖ ≤ ∑' n : S, C * thetaCuspSourceTerm y n :=
        tsum_of_norm_bounded hs.hasSum fun n => norm_seedWeight_mul_le hC hy n
    _ = C * ∑' n : S, thetaCuspSourceTerm y n := tsum_mul_left
    _ ≤ C * thetaCuspFullSource y :=
        mul_le_mul_of_nonneg_left (tsum_subtype_thetaCuspSourceTerm_le S hy) hC0

/-- **The literal Euler identity** `R h = k` on the whole line. -/
theorem seedResolvent_univ_thetaSeedC (x : ℝ) :
    seedResolvent univ thetaSeedC x = thetaSourceC x := by
  rw [seedResolvent, tsum_univ (f := fun n : ℕ => (((n : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
    thetaSeedC (x + Real.log n)), thetaSourceC, thetaCuspFullSource, Complex.ofReal_tsum]
  refine tsum_congr fun n => ?_
  rw [thetaSeedC, ← Complex.ofReal_mul, rpow_neg_half_mul_thetaCuspLogSeed]

/-- The finite-prime identity `R_N h = k_N`. -/
theorem seedResolvent_smoothNumbers_thetaSeedC (N : ℕ) (x : ℝ) :
    seedResolvent (N + 1).smoothNumbers thetaSeedC x = (finitePrimeThetaCuspSource N x : ℂ) := by
  rw [seedResolvent, finitePrimeThetaCuspSource, Complex.ofReal_tsum]
  refine tsum_congr fun n => ?_
  rw [thetaSeedC, ← Complex.ofReal_mul, rpow_neg_half_mul_thetaCuspLogSeed]

/-- **Zero division commutes with the Euler resolvent** on the physical half-line:
`T_α (R_S g) = R_S (T_α g)` for seed-dominated `g`, every `S` and every `x ≥ 0`.  The sum and the
integral are interchanged by the majorant `C e^{|Im α| t} k(x+t)`. -/
theorem outwardSine_seedResolvent {g : ℝ → ℂ} (hg : SeedDominated g) (S : Set ℕ) (α : ℂ)
    {x : ℝ} (hx : 0 ≤ x) :
    outwardSine α (seedResolvent S g) x = seedResolvent S (outwardSine α g) x := by
  obtain ⟨C, hC0, hC⟩ := hg.exists_bound_nonneg
  set w : ℕ → ℂ := fun n => (((n : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
  set F : S → ℝ → ℂ := fun n t => Complex.sin (α * t) * (w n * g (x + Real.log (n : ℕ) + t))
  have hLHS : ∀ t ∈ Ioi (0 : ℝ), Complex.sin (α * t) * seedResolvent S g (x + t) =
      ∑' n : S, F n t := by
    intro t _
    rw [seedResolvent, ← tsum_mul_left]
    refine tsum_congr fun n => ?_
    simp only [F, w]
    rw [show x + t + Real.log (n : ℕ) = x + Real.log (n : ℕ) + t by ring]
  have hmeas : ∀ n : S, AEStronglyMeasurable (F n) (volume.restrict (Ioi 0)) := fun n =>
    ((by fun_prop : Continuous fun t : ℝ => Complex.sin (α * t)).aestronglyMeasurable.mul
      (aestronglyMeasurable_const.mul
        ((hg.stronglyMeasurable.comp_measurable (measurable_const.add measurable_id))
          |>.aestronglyMeasurable)))
  have hpt : ∀ t, 0 < t → ∀ n : S, ‖F n t‖ ≤
      Real.exp (|α.im| * t) * (C * thetaCuspSourceTerm (x + t) n) := by
    intro t ht n
    simp only [F, w]
    rw [norm_mul, show x + Real.log (n : ℕ) + t = x + t + Real.log (n : ℕ) by ring]
    refine mul_le_mul ?_ (norm_seedWeight_mul_le hC (by linarith) n) (norm_nonneg _)
      (Real.exp_pos _).le
    simpa [abs_of_pos ht] using norm_csin_mul_ofReal_le α t
  have hk : Integrable (fun t : ℝ => Real.exp (|α.im| * |t|) * thetaCuspFullSource (x + t)) := by
    have h := expMomentSource_thetaSourceC.integrable_mul_shift
      (w := fun t : ℝ => ((Real.exp (|α.im| * |t|) : ℝ) : ℂ)) (by fun_prop)
      (fun t => by rw [Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]) x
    refine h.norm.congr (Eventually.of_forall fun t => ?_)
    simp only [thetaSourceC, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le,
      Real.norm_of_nonneg (thetaCuspFullSource_pos _).le]
  have hfin : ∑' n : S, ∫⁻ t in Ioi (0 : ℝ), ‖F n t‖ₑ ≠ ⊤ := by
    rw [← lintegral_tsum fun n => (hmeas n).enorm]
    refine ne_of_lt (lt_of_le_of_lt (lintegral_mono_ae ?_)
      ((hk.const_mul C).integrableOn (s := Ioi 0)).lintegral_lt_top)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht' : 0 < t := ht
    have hsum : Summable fun n : S => ‖F n t‖ :=
      ((((summable_thetaCuspSourceTerm (x + t)).subtype S).mul_left C).mul_left
        (Real.exp (|α.im| * t))).of_nonneg_of_le (fun _ => norm_nonneg _) (hpt t ht')
    simp_rw [← ofReal_norm]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => norm_nonneg _) hsum]
    refine ENNReal.ofReal_le_ofReal ?_
    calc ∑' n : S, ‖F n t‖ ≤ ∑' n : S, Real.exp (|α.im| * t) * (C * thetaCuspSourceTerm (x + t) n) :=
          hsum.tsum_le_tsum (hpt t ht') ((((summable_thetaCuspSourceTerm (x + t)).subtype S).mul_left
            C).mul_left _)
      _ = Real.exp (|α.im| * t) * (C * ∑' n : S, thetaCuspSourceTerm (x + t) n) := by
          rw [tsum_mul_left, tsum_mul_left]
      _ ≤ Real.exp (|α.im| * t) * (C * thetaCuspFullSource (x + t)) := by
          gcongr
          exact tsum_subtype_thetaCuspSourceTerm_le S (by linarith)
      _ = C * (Real.exp (|α.im| * |t|) * thetaCuspFullSource (x + t)) := by
          rw [abs_of_pos ht']; ring
  rw [outwardSine, setIntegral_congr_fun measurableSet_Ioi hLHS, integral_tsum hmeas hfin,
    seedResolvent, ← tsum_mul_left]
  refine tsum_congr fun n => ?_
  simp only [F, outwardSine]
  rw [← integral_const_mul, ← integral_const_mul, ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  simp only
  ring

/-! ## Finite iterates on the physical half-line -/

/-- Successive outward divisions of a base function `f` along a list, without reflection. -/
def halfListDivision : List ℂ → (ℝ → ℂ) → ℝ → ℂ
  | [], f => f
  | β :: L, f => outwardSine β (halfListDivision L f)

theorem outwardSine_congr {f g : ℝ → ℂ} (α : ℂ) {x : ℝ} (h : ∀ y, x ≤ y → f y = g y) :
    outwardSine α f x = outwardSine α g x := by
  unfold outwardSine
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  rw [h _ (by linarith [(mem_Ioi.1 ht).le])]

theorem halfListDivision_congr (L : List ℂ) {f g : ℝ → ℂ} (h : ∀ y, 0 ≤ y → f y = g y) :
    ∀ x, 0 ≤ x → halfListDivision L f x = halfListDivision L g x := by
  induction L with
  | nil => exact h
  | cons β L ih =>
    intro x hx
    exact outwardSine_congr β fun y hy => ih y (hx.trans hy)

theorem seedDominated_halfListDivision (L : List ℂ) {g : ℝ → ℂ} (hg : SeedDominated g) :
    SeedDominated (halfListDivision L g) := by
  induction L with
  | nil => exact hg
  | cons β L ih => exact seedDominated_outwardSine ih β

/-- **Finite products of Green operators commute with every Euler resolvent** on `x ≥ 0`. -/
theorem seedResolvent_halfListDivision (L : List ℂ) {g : ℝ → ℂ} (hg : SeedDominated g)
    (S : Set ℕ) : ∀ x, 0 ≤ x →
      seedResolvent S (halfListDivision L g) x = halfListDivision L (seedResolvent S g) x := by
  induction L with
  | nil => exact fun _ _ => rfl
  | cons β L ih =>
    intro x hx
    rw [halfListDivision, halfListDivision,
      ← outwardSine_seedResolvent (seedDominated_halfListDivision L hg) S β hx]
    exact outwardSine_congr β fun y hy => ih y (hx.trans hy)

/-- On the physical half-line the reflected list divisions of `k` are the plain iterates. -/
theorem thetaListDivision_eq_halfListDivision (L : List ℂ) :
    ∀ x, 0 ≤ x → thetaListDivision L x = halfListDivision L thetaSourceC x := by
  induction L with
  | nil => exact fun _ _ => rfl
  | cons β L ih =>
    intro x hx
    show zeroDivision β (thetaListDivision L) x = outwardSine β (halfListDivision L thetaSourceC) x
    rw [zeroDivision, abs_of_nonneg hx]
    exact outwardSine_congr β fun y hy => ih y (hx.trans hy)

/-- The seed divisions `T_{β₁} ⋯ T_{β_j} h`. -/
def seedListDivision (L : List ℂ) : ℝ → ℂ := halfListDivision L thetaSeedC

theorem seedDominated_seedListDivision (L : List ℂ) : SeedDominated (seedListDivision L) :=
  seedDominated_halfListDivision L seedDominated_thetaSeedC

/-- **Seed transfer of list divisions.**  `R (T_L h) = T_L k = G_L` on `x ≥ 0`, where `G_L` is the
reflected list division of `k`. -/
theorem seedResolvent_seedListDivision (L : List ℂ) {x : ℝ} (hx : 0 ≤ x) :
    seedResolvent univ (seedListDivision L) x = thetaListDivision L x := by
  rw [seedListDivision, seedResolvent_halfListDivision L seedDominated_thetaSeedC univ x hx,
    thetaListDivision_eq_halfListDivision L x hx]
  exact halfListDivision_congr L (fun y _ => seedResolvent_univ_thetaSeedC y) x hx

/-- The finite-prime version: `R_N (T_L h) = T_L k_N` on `x ≥ 0`. -/
theorem seedResolvent_smoothNumbers_seedListDivision (N : ℕ) (L : List ℂ) {x : ℝ} (hx : 0 ≤ x) :
    seedResolvent (N + 1).smoothNumbers (seedListDivision L) x =
      halfListDivision L (fun y => (finitePrimeThetaCuspSource N y : ℂ)) x := by
  rw [seedListDivision, seedResolvent_halfListDivision L seedDominated_thetaSeedC _ x hx]
  exact halfListDivision_congr L (fun y _ => seedResolvent_smoothNumbers_thetaSeedC N y) x hx

/-- Nonempty seed divisions are `O(e^{-2x})` relative to `h` and tend to zero relative to `h`. -/
theorem seedListDivision_tail (β : ℂ) (L : List ℂ) :
    (∃ K, ∀ x, 0 ≤ x → ‖seedListDivision (β :: L) x‖ ≤ K * Real.exp (-(2 * x)) *
      thetaCuspLogSeed x) ∧
    Tendsto (fun x => ‖seedListDivision (β :: L) x‖ / thetaCuspLogSeed x) atTop (𝓝 0) :=
  ⟨(seedDominated_seedListDivision L).exists_norm_outwardSine_le β,
    (seedDominated_seedListDivision L).tendsto_outwardSine_div β⟩

/-! ## Linearity of the resolvent -/

theorem seedResolvent_finset_sum {ι : Type*} (s : Finset ι) {g : ι → ℝ → ℂ}
    (hg : ∀ i ∈ s, SeedDominated (g i)) (c : ι → ℂ) (S : Set ℕ) {x : ℝ} (hx : 0 ≤ x) :
    seedResolvent S (fun y => ∑ i ∈ s, c i * g i y) x = ∑ i ∈ s, c i * seedResolvent S (g i) x := by
  unfold seedResolvent
  simp_rw [Finset.mul_sum]
  rw [Summable.tsum_finsetSum fun i hi => ?_]
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [← tsum_mul_left]
    exact tsum_congr fun n => by ring
  · exact ((hg i hi).summable_seedResolvent S hx).mul_left (c i) |>.congr fun n => by ring

theorem seedResolvent_re {g : ℝ → ℂ} (hg : SeedDominated g) (S : Set ℕ) {x : ℝ} (hx : 0 ≤ x) :
    seedResolvent S (fun y => ((g y).re : ℂ)) x = ((seedResolvent S g x).re : ℂ) := by
  unfold seedResolvent
  rw [Complex.re_tsum (hg.summable_seedResolvent S hx), Complex.ofReal_tsum]
  refine tsum_congr fun n => ?_
  rw [← Complex.ofReal_mul, Complex.re_ofReal_mul]

/-! ## The literal statements -/

/-- **Absolute convergence.**  For a seed-dominated `g` (in particular every finite seed division)
and `x ≥ 0`, the resolvent series converges absolutely and the Green integral converges absolutely. -/
theorem SeedDominated.absolute_convergence {g : ℝ → ℂ} (hg : SeedDominated g) (S : Set ℕ) (α : ℂ)
    {x : ℝ} (hx : 0 ≤ x) :
    Summable (fun n : S => ‖((((n : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * g (x + Real.log (n : ℕ))‖) ∧
      IntegrableOn (fun t : ℝ => Complex.sin (α * t) * g (x + t)) (Ioi 0) := by
  obtain ⟨C, -, hC⟩ := hg.exists_bound_nonneg
  exact ⟨(((summable_thetaCuspSourceTerm x).subtype S).mul_left C).of_nonneg_of_le
    (fun _ => norm_nonneg _) fun n => norm_seedWeight_mul_le hC hx n, hg.integrableOn_sin_mul α hx⟩

/-- `T_α (R h) = R (T_α h)` on `x ≥ 0`, where `R h = k`. -/
theorem outwardSine_thetaSourceC_eq_seedResolvent (α : ℂ) {x : ℝ} (hx : 0 ≤ x) :
    outwardSine α thetaSourceC x = seedResolvent univ (outwardSine α thetaSeedC) x := by
  rw [← outwardSine_seedResolvent seedDominated_thetaSeedC univ α hx]
  exact outwardSine_congr α fun y _ => (seedResolvent_univ_thetaSeedC y).symm

/-- `T_α (R_N h) = R_N (T_α h)` on `x ≥ 0`, where `R_N h = k_N`. -/
theorem outwardSine_finitePrimeSource_eq_seedResolvent (N : ℕ) (α : ℂ) {x : ℝ} (hx : 0 ≤ x) :
    outwardSine α (fun y => (finitePrimeThetaCuspSource N y : ℂ)) x =
      seedResolvent (N + 1).smoothNumbers (outwardSine α thetaSeedC) x := by
  rw [← outwardSine_seedResolvent seedDominated_thetaSeedC _ α hx]
  exact outwardSine_congr α fun y _ => (seedResolvent_smoothNumbers_thetaSeedC N y).symm

end

end RHTower
