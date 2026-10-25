import GaloisForLFunctions.HTGeometry.HamburgerLaplaceIdentity

/-!
# Hamburger's Laplace step for arbitrary frequencies

Let `1 ≤ λ_n` be frequencies and `a_n` coefficients with `Σ ‖a_n‖/λ_n² < ∞`, and put

`θ(x) = Σ a_n e^{-π λ_n² x}`,   `L(t) = Σ a_n t/(π(λ_n² + t²))`,   `F(t) = Σ a_n e^{-2π λ_n t}`.

**Laplace identity** (`freqSeries_eq_of_freqTheta_relation`).  If
`θ(x) = x^{-1/2} θ(1/x) + α + β x^{-1/2}` for all `x > 0`, then `L(t) = F(t) + α/(π t) + β` on
the whole half-plane `Re t > 0`.  On the positive axis this is the Laplace transform of the theta
relation against `e^{-π t² x}` (partial fractions on one side, the half-integral Laplace–Bessel
formula on the other); both sides are holomorphic on `Re t > 0`, so the identity extends.

**Residues on the imaginary axis** (`tendsto_mul_freqSeries_atom`,
`tendsto_mul_freqSeries_gap`).  `L` has simple poles at `t = ±iλ_n`.  If `λ_m = τ` and the other
frequencies stay a fixed proportion away from `τ`, then `ε L(ε + iτ) → a_m/(2π)` as `ε → 0⁺`; if no
frequency equals `τ`, then `ε L(ε + iτ) → 0`.  Through the identity this reads the Abel means of
`a_n e^{-2πiλ_n τ}`: the Bohr spectrum of a measure satisfying the theta relation is its support.
This generalizes the `ℕ`-frequency step of Hamburger's theorem (`HamburgerLaplaceIdentity`).
-/

open Complex MeasureTheory Filter Topology Set

noncomputable section

namespace GaloisForLFunctions.HTGeometry.FreqHamburger

/-- `θ(x) = Σ a_n e^{-π λ_n² x}`. -/
def freqTheta (a : ℕ → ℂ) (lam : ℕ → ℝ) (x : ℝ) : ℂ :=
  ∑' n : ℕ, a n * ((Real.exp (-Real.pi * lam n ^ 2 * x) : ℝ) : ℂ)

/-- The partial-fraction series `L(t) = Σ a_n t/(π(λ_n² + t²))`. -/
def freqSeries (a : ℕ → ℂ) (lam : ℕ → ℝ) (t : ℂ) : ℂ :=
  ∑' n : ℕ, a n * t / ((Real.pi : ℂ) * ((lam n : ℂ) ^ 2 + t ^ 2))

/-- The exponential series `F(t) = Σ a_n e^{-2π λ_n t}`. -/
def freqDual (a : ℕ → ℂ) (lam : ℕ → ℝ) (t : ℂ) : ℂ :=
  ∑' n : ℕ, a n * cexp (-(2 * Real.pi * (lam n : ℂ) * t))

variable {a : ℕ → ℂ} {lam : ℕ → ℝ}

/-! ## The theta series -/

theorem exp_neg_le_inv {u : ℝ} (hu : 0 < u) : Real.exp (-u) ≤ u⁻¹ := by
  rw [Real.exp_neg]
  exact inv_anti₀ hu (by linarith [Real.add_one_le_exp u])

theorem norm_thetaTerm_le (hlam : ∀ n, 1 ≤ lam n) {x : ℝ} (hx : 0 < x) (n : ℕ) :
    ‖a n * ((Real.exp (-Real.pi * lam n ^ 2 * x) : ℝ) : ℂ)‖ ≤
      (Real.pi * x)⁻¹ * (‖a n‖ / lam n ^ 2) := by
  have hl : 0 < lam n := lt_of_lt_of_le one_pos (hlam n)
  have hu : 0 < Real.pi * lam n ^ 2 * x := by positivity
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  have h := exp_neg_le_inv hu
  rw [neg_mul, neg_mul] at *
  calc ‖a n‖ * Real.exp (-(Real.pi * lam n ^ 2 * x)) ≤ ‖a n‖ * (Real.pi * lam n ^ 2 * x)⁻¹ :=
        mul_le_mul_of_nonneg_left h (norm_nonneg _)
    _ = (Real.pi * x)⁻¹ * (‖a n‖ / lam n ^ 2) := by
        field_simp

theorem summable_norm_thetaTerm (hlam : ∀ n, 1 ≤ lam n)
    (ha : Summable fun n => ‖a n‖ / lam n ^ 2) {x : ℝ} (hx : 0 < x) :
    Summable fun n => ‖a n * ((Real.exp (-Real.pi * lam n ^ 2 * x) : ℝ) : ℂ)‖ :=
  (ha.mul_left _).of_nonneg_of_le (fun _ => norm_nonneg _) (norm_thetaTerm_le hlam hx)

/-- `‖θ(x)‖ ≤ (π x)⁻¹ Σ ‖a_n‖/λ_n²`. -/
theorem norm_freqTheta_le (hlam : ∀ n, 1 ≤ lam n)
    (ha : Summable fun n => ‖a n‖ / lam n ^ 2) {x : ℝ} (hx : 0 < x) :
    ‖freqTheta a lam x‖ ≤ (Real.pi * x)⁻¹ * ∑' n, ‖a n‖ / lam n ^ 2 := by
  unfold freqTheta
  refine (norm_tsum_le_tsum_norm (summable_norm_thetaTerm hlam ha hx)).trans ?_
  rw [← tsum_mul_left]
  exact (summable_norm_thetaTerm hlam ha hx).tsum_le_tsum (norm_thetaTerm_le hlam hx)
    (ha.mul_left _)

theorem continuousOn_freqTheta (hlam : ∀ n, 1 ≤ lam n)
    (ha : Summable fun n => ‖a n‖ / lam n ^ 2) : ContinuousOn (freqTheta a lam) (Ioi 0) := by
  have hloc : ∀ δ : ℝ, 0 < δ → ContinuousOn (freqTheta a lam) (Ioi δ) := by
    intro δ hδ
    refine continuousOn_tsum (fun n => by fun_prop) (ha.mul_left ((Real.pi * δ)⁻¹))
      fun n x hx => ?_
    have hxδ : δ < x := hx
    refine (norm_thetaTerm_le hlam (hδ.trans hxδ) n).trans
      (mul_le_mul_of_nonneg_right ?_ (by positivity))
    exact inv_anti₀ (by positivity) (by nlinarith [Real.pi_pos])
  intro x hx
  have hx0 : (0 : ℝ) < x := hx
  exact ((hloc (x / 2) (by positivity)).continuousAt
    (Ioi_mem_nhds (by linarith))).continuousWithinAt

/-! ## The Laplace transform on the positive axis -/

theorem hasSum_integral_freqTheta_mul_exp (hlam : ∀ n, 1 ≤ lam n)
    (ha : Summable fun n => ‖a n‖ / lam n ^ 2) {t : ℝ} (ht : 0 < t) :
    HasSum (fun n : ℕ => a n / ((Real.pi * (lam n ^ 2 + t ^ 2) : ℝ) : ℂ))
      (∫ x in Ioi (0 : ℝ), freqTheta a lam x * ((Real.exp (-(Real.pi * t ^ 2) * x) : ℝ) : ℂ)) := by
  set F : ℕ → ℝ → ℂ := fun n x =>
    a n * ((Real.exp (-(Real.pi * (lam n ^ 2 + t ^ 2)) * x) : ℝ) : ℂ) with hF
  have hk : ∀ n : ℕ, 0 < Real.pi * (lam n ^ 2 + t ^ 2) := fun n => by positivity
  have hFint : ∀ n : ℕ, Integrable (F n) (volume.restrict (Ioi 0)) := fun n =>
    ((integrableOn_Ioi_exp_neg_mul (hk n)).ofReal).const_mul _
  have hFnorm : ∀ n : ℕ, ∫ x in Ioi (0 : ℝ), ‖F n x‖ =
      ‖a n‖ / (Real.pi * (lam n ^ 2 + t ^ 2)) := by
    intro n
    have : ∀ x : ℝ, ‖F n x‖ = ‖a n‖ * Real.exp (-(Real.pi * (lam n ^ 2 + t ^ 2)) * x) := by
      intro x
      rw [hF, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    simp_rw [this]
    rw [integral_const_mul, integral_Ioi_exp_neg_mul (hk n), mul_one_div]
  have hsum : Summable fun n : ℕ => ∫ x in Ioi (0 : ℝ), ‖F n x‖ := by
    simp_rw [hFnorm]
    refine (ha.mul_left (1 / Real.pi)).of_nonneg_of_le
      (fun n => div_nonneg (norm_nonneg _) (hk n).le) fun n => ?_
    have hl : 0 < lam n := lt_of_lt_of_le one_pos (hlam n)
    rw [div_le_iff₀ (hk n)]
    calc ‖a n‖ = 1 / Real.pi * (‖a n‖ / lam n ^ 2) * (Real.pi * lam n ^ 2) := by field_simp
      _ ≤ 1 / Real.pi * (‖a n‖ / lam n ^ 2) * (Real.pi * (lam n ^ 2 + t ^ 2)) := by
        gcongr
        nlinarith [sq_nonneg t]
  have h := MeasureTheory.hasSum_integral_of_summable_integral_norm hFint hsum
  have hval : ∀ n : ℕ, ∫ x in Ioi (0 : ℝ), F n x =
      a n / ((Real.pi * (lam n ^ 2 + t ^ 2) : ℝ) : ℂ) := by
    intro n
    rw [hF, integral_const_mul, integral_complex_ofReal, integral_Ioi_exp_neg_mul (hk n)]
    push_cast
    ring
  have hsumF : ∀ x ∈ Ioi (0 : ℝ), ∑' n : ℕ, F n x =
      freqTheta a lam x * ((Real.exp (-(Real.pi * t ^ 2) * x) : ℝ) : ℂ) := by
    intro x hx
    rw [freqTheta, ← tsum_mul_right]
    refine tsum_congr fun n => ?_
    rw [hF, mul_assoc, ← ofReal_mul, ← Real.exp_add]
    ring_nf
  simp_rw [hval] at h
  rwa [setIntegral_congr_fun measurableSet_Ioi hsumF] at h

theorem hasSum_integral_dual_freqTheta_mul_exp (hlam : ∀ n, 1 ≤ lam n)
    (ha : Summable fun n => ‖a n‖ / lam n ^ 2) {t : ℝ} (ht : 0 < t) :
    HasSum (fun n : ℕ => a n * ((1 / t * Real.exp (-(2 * Real.pi * lam n * t)) : ℝ) : ℂ))
      (∫ x in Ioi (0 : ℝ), (x : ℂ) ^ (-(1 / 2 : ℂ)) * freqTheta a lam x⁻¹ *
        ((Real.exp (-(Real.pi * t ^ 2) * x) : ℝ) : ℂ)) := by
  set F : ℕ → ℝ → ℂ := fun n x => a n * ((x ^ (-(1 / 2 : ℝ)) *
    Real.exp (-(Real.pi * lam n ^ 2 / x) - Real.pi * t ^ 2 * x) : ℝ) : ℂ) with hF
  have hm : ∀ n : ℕ, (0 : ℝ) < lam n := fun n => lt_of_lt_of_le one_pos (hlam n)
  have hFint : ∀ n : ℕ, Integrable (F n) (volume.restrict (Ioi 0)) := fun n =>
    ((integrableOn_rpow_neg_half_mul_exp_theta_dual (hm n) ht).ofReal).const_mul _
  have hFnorm : ∀ n : ℕ, ∫ x in Ioi (0 : ℝ), ‖F n x‖ =
      ‖a n‖ * (1 / t * Real.exp (-(2 * Real.pi * lam n * t))) := by
    intro n
    have : ∀ x ∈ Ioi (0 : ℝ), ‖F n x‖ = ‖a n‖ * (x ^ (-(1 / 2 : ℝ)) *
        Real.exp (-(Real.pi * lam n ^ 2 / x) - Real.pi * t ^ 2 * x)) := by
      intro x hx
      have hx0 : (0 : ℝ) < x := hx
      rw [hF, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    rw [setIntegral_congr_fun measurableSet_Ioi this, integral_const_mul,
      integral_rpow_neg_half_mul_exp_theta_dual (hm n) ht]
  have hsum : Summable fun n : ℕ => ∫ x in Ioi (0 : ℝ), ‖F n x‖ := by
    simp_rw [hFnorm]
    refine (ha.mul_left (1 / t / (2 * Real.pi ^ 2 * t ^ 2))).of_nonneg_of_le
      (fun n => by positivity) fun n => ?_
    have hy : 0 < 2 * Real.pi * lam n * t := by have := hm n; positivity
    have he := exp_neg_le_two_div_sq hy
    have hl := hm n
    calc ‖a n‖ * (1 / t * Real.exp (-(2 * Real.pi * lam n * t)))
        ≤ ‖a n‖ * (1 / t * (2 / (2 * Real.pi * lam n * t) ^ 2)) := by gcongr
      _ = 1 / t / (2 * Real.pi ^ 2 * t ^ 2) * (‖a n‖ / lam n ^ 2) := by
        field_simp
  have h := MeasureTheory.hasSum_integral_of_summable_integral_norm hFint hsum
  have hval : ∀ n : ℕ, ∫ x in Ioi (0 : ℝ), F n x =
      a n * ((1 / t * Real.exp (-(2 * Real.pi * lam n * t)) : ℝ) : ℂ) := by
    intro n
    rw [hF, integral_const_mul, integral_complex_ofReal,
      integral_rpow_neg_half_mul_exp_theta_dual (hm n) ht]
  have hsumF : ∀ x ∈ Ioi (0 : ℝ), ∑' n : ℕ, F n x =
      (x : ℂ) ^ (-(1 / 2 : ℂ)) * freqTheta a lam x⁻¹ *
        ((Real.exp (-(Real.pi * t ^ 2) * x) : ℝ) : ℂ) := by
    intro x hx
    have hx0 : (0 : ℝ) < x := hx
    have hcpow : (x : ℂ) ^ (-(1 / 2 : ℂ)) = ((x ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) := by
      rw [Complex.ofReal_cpow hx0.le]
      push_cast
      ring_nf
    rw [freqTheta, ← tsum_mul_left, ← tsum_mul_right]
    refine tsum_congr fun n => ?_
    rw [hF, hcpow]
    beta_reduce
    rw [show -(Real.pi * lam n ^ 2 / x) - Real.pi * t ^ 2 * x =
      -Real.pi * lam n ^ 2 * x⁻¹ + -(Real.pi * t ^ 2) * x by ring, Real.exp_add]
    push_cast
    ring
  simp_rw [hval] at h
  rwa [setIntegral_congr_fun measurableSet_Ioi hsumF] at h

theorem integrableOn_dual_freqTheta_mul_exp (hlam : ∀ n, 1 ≤ lam n)
    (ha : Summable fun n => ‖a n‖ / lam n ^ 2) {t : ℝ} (ht : 0 < t) :
    IntegrableOn (fun x : ℝ => (x : ℂ) ^ (-(1 / 2 : ℂ)) * freqTheta a lam x⁻¹ *
      ((Real.exp (-(Real.pi * t ^ 2) * x) : ℝ) : ℂ)) (Ioi 0) := by
  set S : ℝ := ∑' n, ‖a n‖ / lam n ^ 2 with hSdef
  have hdom : IntegrableOn (fun x : ℝ => x ^ (1 / 2 : ℝ) *
      Real.exp (-(Real.pi * t ^ 2) * x ^ (1 : ℝ))) (Ioi 0) :=
    integrableOn_rpow_mul_exp_neg_mul_rpow (by norm_num) le_rfl (by positivity)
  refine (hdom.const_mul (S / Real.pi)).mono' ?_ ((ae_restrict_iff' measurableSet_Ioi).mpr
    (Eventually.of_forall fun x hx => ?_))
  · refine ContinuousOn.aestronglyMeasurable (fun x hx => ?_) measurableSet_Ioi
    have hx0 : (0 : ℝ) < x := hx
    refine ContinuousAt.continuousWithinAt ?_
    refine ((continuousAt_ofReal_cpow_const _ _ (Or.inr hx0.ne')).mul ?_).mul ?_
    · exact ((continuousOn_freqTheta hlam ha).continuousAt
        (Ioi_mem_nhds (inv_pos.mpr hx0))).comp (continuousAt_inv₀ hx0.ne')
    · exact (by fun_prop : Continuous fun x : ℝ =>
        ((Real.exp (-(Real.pi * t ^ 2) * x) : ℝ) : ℂ)).continuousAt
  · have hx0 : (0 : ℝ) < x := hx
    have hθ := norm_freqTheta_le hlam ha (inv_pos.mpr hx0)
    rw [← hSdef] at hθ
    have hinv : (Real.pi * x⁻¹)⁻¹ = x / Real.pi := by field_simp
    rw [hinv] at hθ
    rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx0, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.rpow_one]
    have hre : (-(1 / 2 : ℂ)).re = -(1 / 2 : ℝ) := by norm_num
    rw [hre]
    have hpow : x ^ (-(1 / 2 : ℝ)) * x = x ^ (1 / 2 : ℝ) := by
      rw [← Real.rpow_add_one hx0.ne']
      norm_num
    calc x ^ (-(1 / 2 : ℝ)) * ‖freqTheta a lam x⁻¹‖ * Real.exp (-(Real.pi * t ^ 2) * x)
        ≤ x ^ (-(1 / 2 : ℝ)) * (x / Real.pi * S) * Real.exp (-(Real.pi * t ^ 2) * x) := by
          gcongr
      _ = S / Real.pi * (x ^ (-(1 / 2 : ℝ)) * x * Real.exp (-(Real.pi * t ^ 2) * x)) := by
          ring
      _ = S / Real.pi * (x ^ (1 / 2 : ℝ) * Real.exp (-(Real.pi * t ^ 2) * x)) := by rw [hpow]

/-- **The Laplace identity on the positive axis.** -/
theorem freqSeries_eq_of_freqTheta_relation_ofReal (hlam : ∀ n, 1 ≤ lam n)
    (ha : Summable fun n => ‖a n‖ / lam n ^ 2) {α β : ℂ}
    (htheta : ∀ x : ℝ, 0 < x → freqTheta a lam x =
      (x : ℂ) ^ (-(1 / 2 : ℂ)) * freqTheta a lam x⁻¹ + α + β * (x : ℂ) ^ (-(1 / 2 : ℂ)))
    {t : ℝ} (ht : 0 < t) :
    freqSeries a lam t = freqDual a lam t + α / (Real.pi * t) + β := by
  set e : ℝ → ℂ := fun x => ((Real.exp (-(Real.pi * t ^ 2) * x) : ℝ) : ℂ) with he_def
  have hB : 0 < Real.pi * t ^ 2 := by positivity
  have he_int : IntegrableOn e (Ioi 0) := (integrableOn_Ioi_exp_neg_mul hB).ofReal
  have hhe_eq : ∀ x ∈ Ioi (0 : ℝ), (x : ℂ) ^ (-(1 / 2 : ℂ)) * e x =
      ((x ^ ((1 / 2 : ℝ) - 1) * Real.exp (-((Real.pi * t ^ 2) * x)) : ℝ) : ℂ) := by
    intro x hx
    have hx0 : (0 : ℝ) < x := hx
    rw [he_def, Complex.ofReal_mul, Complex.ofReal_cpow hx0.le]
    push_cast
    ring_nf
  have hhe_int : IntegrableOn (fun x : ℝ => (x : ℂ) ^ (-(1 / 2 : ℂ)) * e x) (Ioi 0) := by
    have h : IntegrableOn (fun x : ℝ => x ^ ((1 / 2 : ℝ) - 1) *
        Real.exp (-(Real.pi * t ^ 2) * x ^ (1 : ℝ))) (Ioi 0) :=
      integrableOn_rpow_mul_exp_neg_mul_rpow (by norm_num) le_rfl hB
    have h' : IntegrableOn (fun x : ℝ => ((x ^ ((1 / 2 : ℝ) - 1) *
        Real.exp (-((Real.pi * t ^ 2) * x)) : ℝ) : ℂ)) (Ioi 0) := by
      have := Integrable.ofReal (𝕜 := ℂ) h
      simp only [Real.rpow_one, neg_mul] at this
      exact this
    exact IntegrableOn.congr_fun h' (fun x hx => (hhe_eq x hx).symm) measurableSet_Ioi
  have hD_int := integrableOn_dual_freqTheta_mul_exp hlam ha ht
  have hI0 : ∫ x in Ioi (0 : ℝ), e x = ((1 / (Real.pi * t ^ 2) : ℝ) : ℂ) := by
    rw [he_def, integral_complex_ofReal, integral_Ioi_exp_neg_mul hB]
  have hIh : ∫ x in Ioi (0 : ℝ), (x : ℂ) ^ (-(1 / 2 : ℂ)) * e x = ((1 / t : ℝ) : ℂ) := by
    rw [setIntegral_congr_fun measurableSet_Ioi hhe_eq, integral_complex_ofReal,
      integral_Ioi_rpow_neg_half_mul_exp_neg_mul_sq ht]
  have hpt : ∀ x ∈ Ioi (0 : ℝ), freqTheta a lam x * e x =
      (x : ℂ) ^ (-(1 / 2 : ℂ)) * freqTheta a lam x⁻¹ * e x +
        (α * e x + β * ((x : ℂ) ^ (-(1 / 2 : ℂ)) * e x)) := by
    intro x hx
    rw [htheta x hx]
    ring
  have hsplit : ∫ x in Ioi (0 : ℝ), freqTheta a lam x * e x =
      (∫ x in Ioi (0 : ℝ), (x : ℂ) ^ (-(1 / 2 : ℂ)) * freqTheta a lam x⁻¹ * e x) +
        (α * ∫ x in Ioi (0 : ℝ), e x) +
          β * ∫ x in Ioi (0 : ℝ), (x : ℂ) ^ (-(1 / 2 : ℂ)) * e x := by
    have h1 : ∫ x in Ioi (0 : ℝ), ((x : ℂ) ^ (-(1 / 2 : ℂ)) * freqTheta a lam x⁻¹ * e x +
        (α * e x + β * ((x : ℂ) ^ (-(1 / 2 : ℂ)) * e x))) =
        (∫ x in Ioi (0 : ℝ), (x : ℂ) ^ (-(1 / 2 : ℂ)) * freqTheta a lam x⁻¹ * e x) +
          ∫ x in Ioi (0 : ℝ), (α * e x + β * ((x : ℂ) ^ (-(1 / 2 : ℂ)) * e x)) :=
      integral_add hD_int ((he_int.const_mul α).add (hhe_int.const_mul β))
    have h2 : ∫ x in Ioi (0 : ℝ), (α * e x + β * ((x : ℂ) ^ (-(1 / 2 : ℂ)) * e x)) =
        (∫ x in Ioi (0 : ℝ), α * e x) +
          ∫ x in Ioi (0 : ℝ), β * ((x : ℂ) ^ (-(1 / 2 : ℂ)) * e x) :=
      integral_add (he_int.const_mul α) (hhe_int.const_mul β)
    rw [setIntegral_congr_fun measurableSet_Ioi hpt, h1, h2, integral_const_mul,
      integral_const_mul]
    ring
  have hL := (hasSum_integral_freqTheta_mul_exp hlam ha ht).tsum_eq
  have hD := (hasSum_integral_dual_freqTheta_mul_exp hlam ha ht).tsum_eq
  rw [hsplit, ← hD, hI0, hIh] at hL
  have ht0 : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hser : freqSeries a lam t = (t : ℂ) * ∑' n : ℕ,
      a n / ((Real.pi * (lam n ^ 2 + t ^ 2) : ℝ) : ℂ) := by
    rw [freqSeries, ← tsum_mul_left]
    refine tsum_congr fun n => ?_
    push_cast
    ring
  have hdual : ∑' n : ℕ, a n * ((1 / t * Real.exp (-(2 * Real.pi * lam n * t)) : ℝ) : ℂ) =
      (1 / (t : ℂ)) * freqDual a lam t := by
    rw [freqDual, ← tsum_mul_left]
    refine tsum_congr fun n => ?_
    push_cast
    ring
  rw [hser, hL, hdual]
  push_cast
  field_simp

/-! ## Holomorphy and the identity on the half-plane -/

/-- On `|t - t₀| < Re t₀/2`, `‖m² + t²‖ ≥ c m²` for real `m ≥ 0`. -/
theorem norm_sq_add_sq_ge_on_ball {t₀ t : ℂ} (h0 : 0 < t₀.re)
    (ht : t ∈ Metric.ball t₀ (t₀.re / 2)) {m : ℝ} (hm0 : 0 ≤ m) :
    min (3 / 4) ((t₀.re / 2) ^ 2 / (4 * (‖t₀‖ + t₀.re / 2) ^ 2)) * m ^ 2 ≤
      ‖(m : ℂ) ^ 2 + t ^ 2‖ := by
  set δ : ℝ := t₀.re / 2 with hδ
  set R : ℝ := ‖t₀‖ + δ with hR
  have hδpos : 0 < δ := by rw [hδ]; linarith
  have hRpos : 0 < R := by rw [hR]; linarith [norm_nonneg t₀]
  rw [Metric.mem_ball, dist_eq_norm] at ht
  have hre : δ < t.re := by
    have h1 := abs_re_le_norm (t - t₀)
    rw [sub_re, abs_le] at h1
    linarith [h1.1]
  have hnorm : ‖t‖ ≤ R := by
    have := norm_le_norm_add_norm_sub' t t₀
    rw [hR]
    have h2 : ‖t - t₀‖ = ‖t₀ - t‖ := norm_sub_rev _ _
    linarith
  rcases le_or_gt (2 * R) m with hm | hm
  · have h1 : ‖(m : ℂ) ^ 2‖ = m ^ 2 := by rw [norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hm0]
    have h2 : ‖t ^ 2‖ ≤ R ^ 2 := by
      rw [norm_pow]
      exact pow_le_pow_left₀ (norm_nonneg t) hnorm 2
    have h3 := norm_sub_le ((m : ℂ) ^ 2 + t ^ 2) (t ^ 2)
    rw [add_sub_cancel_right, h1] at h3
    have h4 : R ^ 2 ≤ m ^ 2 / 4 := by nlinarith
    calc min (3 / 4) (δ ^ 2 / (4 * R ^ 2)) * m ^ 2 ≤ 3 / 4 * m ^ 2 :=
          mul_le_mul_of_nonneg_right (min_le_left _ _) (by positivity)
      _ ≤ ‖(m : ℂ) ^ 2 + t ^ 2‖ := by nlinarith
  · have hfac : (m : ℂ) ^ 2 + t ^ 2 = (t - (m : ℂ) * I) * (t + (m : ℂ) * I) := by
      ring_nf
      rw [I_sq]
      ring
    have h1 : t.re ≤ ‖t - (m : ℂ) * I‖ := by
      have := abs_re_le_norm (t - (m : ℂ) * I)
      simp at this
      exact (le_abs_self _).trans this
    have h2 : t.re ≤ ‖t + (m : ℂ) * I‖ := by
      have := abs_re_le_norm (t + (m : ℂ) * I)
      simp at this
      exact (le_abs_self _).trans this
    have h3 : δ ^ 2 ≤ ‖(m : ℂ) ^ 2 + t ^ 2‖ := by
      rw [hfac, norm_mul]
      have : δ * δ ≤ t.re * t.re := mul_le_mul hre.le hre.le hδpos.le (by linarith)
      nlinarith
    have h4 : m ^ 2 ≤ 4 * R ^ 2 := by nlinarith
    calc min (3 / 4) (δ ^ 2 / (4 * R ^ 2)) * m ^ 2 ≤ δ ^ 2 / (4 * R ^ 2) * m ^ 2 :=
          mul_le_mul_of_nonneg_right (min_le_right _ _) (by positivity)
      _ ≤ δ ^ 2 / (4 * R ^ 2) * (4 * R ^ 2) := by gcongr
      _ = δ ^ 2 := by field_simp
      _ ≤ _ := h3

theorem differentiableOn_freqSeries (hlam : ∀ n, 1 ≤ lam n)
    (ha : Summable fun n => ‖a n‖ / lam n ^ 2) :
    DifferentiableOn ℂ (freqSeries a lam) {t : ℂ | 0 < t.re} := by
  intro t₀ ht₀
  have h0 : 0 < t₀.re := ht₀
  set c : ℝ := min (3 / 4) ((t₀.re / 2) ^ 2 / (4 * (‖t₀‖ + t₀.re / 2) ^ 2)) with hc
  set R : ℝ := ‖t₀‖ + t₀.re / 2 with hR
  have hcpos : 0 < c := lt_min (by norm_num) (by positivity)
  have hRpos : 0 < R := by rw [hR]; linarith [norm_nonneg t₀]
  have hden : ∀ n : ℕ, ∀ t ∈ Metric.ball t₀ (t₀.re / 2),
      c * lam n ^ 2 ≤ ‖(lam n : ℂ) ^ 2 + t ^ 2‖ :=
    fun n t ht => norm_sq_add_sq_ge_on_ball h0 ht (by linarith [hlam n])
  have hU : DifferentiableOn ℂ (freqSeries a lam) (Metric.ball t₀ (t₀.re / 2)) := by
    refine differentiableOn_tsum_of_summable_norm (ha.mul_left (R / (Real.pi * c)))
      (fun n => ?_) Metric.isOpen_ball (fun n t ht => ?_)
    · refine DifferentiableOn.div (by fun_prop) (by fun_prop) fun t ht => ?_
      have hl : 0 < lam n := lt_of_lt_of_le one_pos (hlam n)
      have hpos : 0 < ‖(lam n : ℂ) ^ 2 + t ^ 2‖ :=
        lt_of_lt_of_le (by positivity) (hden n t ht)
      exact mul_ne_zero (by exact_mod_cast Real.pi_ne_zero) (norm_pos_iff.mp hpos)
    · have hl : 0 < lam n := lt_of_lt_of_le one_pos (hlam n)
      have hpos : 0 < c * lam n ^ 2 := by positivity
      have htR : ‖t‖ ≤ R := by
        rw [Metric.mem_ball, dist_eq_norm] at ht
        have := norm_le_norm_add_norm_sub' t t₀
        have h2 : ‖t - t₀‖ = ‖t₀ - t‖ := norm_sub_rev _ _
        rw [hR]
        linarith
      rw [norm_div, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos Real.pi_pos, div_le_iff₀ (mul_pos Real.pi_pos
          (lt_of_lt_of_le hpos (hden n t ht)))]
      calc ‖a n‖ * ‖t‖ ≤ ‖a n‖ * R := mul_le_mul_of_nonneg_left htR (norm_nonneg _)
        _ = R / (Real.pi * c) * (‖a n‖ / lam n ^ 2) * (Real.pi * (c * lam n ^ 2)) := by
            field_simp
        _ ≤ R / (Real.pi * c) * (‖a n‖ / lam n ^ 2) *
              (Real.pi * ‖(lam n : ℂ) ^ 2 + t ^ 2‖) := by
            gcongr
            exact hden n t ht
  exact (hU.differentiableAt (Metric.ball_mem_nhds t₀ (by positivity))).differentiableWithinAt

theorem differentiableOn_freqDual (hlam : ∀ n, 1 ≤ lam n)
    (ha : Summable fun n => ‖a n‖ / lam n ^ 2) :
    DifferentiableOn ℂ (freqDual a lam) {t : ℂ | 0 < t.re} := by
  intro t₀ ht₀
  have h0 : 0 < t₀.re := ht₀
  set δ : ℝ := t₀.re / 2 with hδ
  have hδpos : 0 < δ := by rw [hδ]; linarith
  have hV : IsOpen {t : ℂ | δ < t.re} := isOpen_lt continuous_const Complex.continuous_re
  have hU : DifferentiableOn ℂ (freqDual a lam) {t : ℂ | δ < t.re} := by
    refine differentiableOn_tsum_of_summable_norm
      (ha.mul_left (1 / (2 * Real.pi ^ 2 * δ ^ 2))) (fun n => by fun_prop) hV
      (fun n t ht => ?_)
    have ht' : δ < t.re := ht
    have hl : 0 < lam n := lt_of_lt_of_le one_pos (hlam n)
    have hre : (-(2 * (Real.pi : ℂ) * (lam n : ℂ) * t)).re = -(2 * Real.pi * lam n * t.re) := by
      simp [mul_re]
    rw [norm_mul, Complex.norm_exp, hre]
    have hy : 0 < 2 * Real.pi * lam n * δ := by positivity
    have h1 : Real.exp (-(2 * Real.pi * lam n * t.re)) ≤ Real.exp (-(2 * Real.pi * lam n * δ)) := by
      rw [Real.exp_le_exp, neg_le_neg_iff]
      gcongr
    have h2 := exp_neg_le_two_div_sq hy
    calc ‖a n‖ * Real.exp (-(2 * Real.pi * lam n * t.re))
        ≤ ‖a n‖ * (2 / (2 * Real.pi * lam n * δ) ^ 2) :=
          mul_le_mul_of_nonneg_left (h1.trans h2) (norm_nonneg _)
      _ = 1 / (2 * Real.pi ^ 2 * δ ^ 2) * (‖a n‖ / lam n ^ 2) := by
          field_simp
  exact (hU.differentiableAt (hV.mem_nhds (by show δ < t₀.re; rw [hδ]; linarith))).differentiableWithinAt

/-- **The Laplace identity on the half-plane** `Re t > 0`. -/
theorem freqSeries_eq_of_freqTheta_relation (hlam : ∀ n, 1 ≤ lam n)
    (ha : Summable fun n => ‖a n‖ / lam n ^ 2) {α β : ℂ}
    (htheta : ∀ x : ℝ, 0 < x → freqTheta a lam x =
      (x : ℂ) ^ (-(1 / 2 : ℂ)) * freqTheta a lam x⁻¹ + α + β * (x : ℂ) ^ (-(1 / 2 : ℂ)))
    {t : ℂ} (ht : 0 < t.re) :
    freqSeries a lam t = freqDual a lam t + α / (Real.pi * t) + β := by
  set U : Set ℂ := {t : ℂ | 0 < t.re} with hU
  have hUo : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hf : AnalyticOnNhd ℂ (freqSeries a lam) U :=
    (differentiableOn_freqSeries hlam ha).analyticOnNhd hUo
  have hg : AnalyticOnNhd ℂ (fun t : ℂ => freqDual a lam t + α / (Real.pi * t) + β) U := by
    refine DifferentiableOn.analyticOnNhd ?_ hUo
    refine ((differentiableOn_freqDual hlam ha).add ?_).add (differentiableOn_const _)
    refine DifferentiableOn.div (differentiableOn_const _) (by fun_prop) fun t ht => ?_
    have ht' : 0 < t.re := ht
    refine mul_ne_zero (by exact_mod_cast Real.pi_ne_zero) fun h => ?_
    rw [h, zero_re] at ht'
    exact lt_irrefl _ ht'
  have h1U : (1 : ℂ) ∈ U := by simp [hU]
  have hfreq : ∃ᶠ z in 𝓝[≠] (1 : ℂ),
      freqSeries a lam z = freqDual a lam z + α / (Real.pi * z) + β := by
    set u : ℕ → ℂ := fun k => ((1 + 1 / ((k : ℝ) + 1) : ℝ) : ℂ) with hu
    have hlim : Tendsto u atTop (𝓝[≠] (1 : ℂ)) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, Eventually.of_forall fun k => ?_⟩
      · have h := (tendsto_one_div_add_atTop_nhds_zero_nat).const_add (1 : ℝ)
        rw [add_zero] at h
        have h2 := (Complex.continuous_ofReal.tendsto 1).comp h
        rw [Complex.ofReal_one] at h2
        exact h2
      · simp only [Set.mem_compl_iff, Set.mem_singleton_iff, hu]
        intro h
        have h' : (1 + 1 / ((k : ℝ) + 1) : ℝ) = 1 := by exact_mod_cast h
        have : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
        linarith
    refine hlim.frequently (Frequently.of_forall fun k => ?_)
    have hk : (0 : ℝ) < 1 + 1 / ((k : ℝ) + 1) := by positivity
    exact freqSeries_eq_of_freqTheta_relation_ofReal hlam ha htheta hk
  exact hf.eqOn_of_preconnected_of_frequently_eq hg (convex_halfSpace_re_gt 0).isPreconnected
    h1U hfreq ht

end GaloisForLFunctions.HTGeometry.FreqHamburger
