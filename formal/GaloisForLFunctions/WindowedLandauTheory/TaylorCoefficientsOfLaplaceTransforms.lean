import Mathlib

/-!
# Taylor coefficients of a Laplace transform

For a measurable `g` with `‖g u‖ ≤ C e^{bu}` the Laplace transform `Φ(s) = ∫₀^∞ g(u) e^{-su} du` is
holomorphic on `Re s > b`, and its Taylor coefficients there are kernel integrals,

```text
(-1)^k Φ^(k)(s) / k!  =  ∫₀^∞ g(u) u^k e^{-su} / k! du        (`taylorCoeff_eq_laplaceCoeff`).
```

The real kernel `u^k e^{-au}/k!` has mass `a^{-(k+1)}` (`integral_taylorKernel`) and concentrates
at `u = k/a`. For a window `[U, (1+δ)U]` and `k` with `k/a` at its centre, exponential
tilting bounds the mass outside the window (`integral_taylorKernel_diff_Icc_le`); once `a` is
large against `b` the gain beats the ratio `((a+b)/a)^k` (`exists_taylorKernel_tail_le`).
-/

open MeasureTheory Set Complex Filter Topology

namespace WindowedLandauTheory

noncomputable section

/-! ## The Taylor kernel -/

/-- The Taylor kernel `u^k e^{-au} / k!`. -/
def taylorKernel (k : ℕ) (a u : ℝ) : ℝ := u ^ k * Real.exp (-a * u) / (k.factorial : ℝ)

theorem taylorKernel_nonneg (k : ℕ) (a : ℝ) {u : ℝ} (hu : 0 ≤ u) : 0 ≤ taylorKernel k a u := by
  unfold taylorKernel
  positivity

/-- The Taylor kernel has mass `a^{-(k+1)}` on `(0,∞)`. -/
theorem integral_taylorKernel (k : ℕ) {a : ℝ} (ha : 0 < a) :
    ∫ u in Ioi (0 : ℝ), taylorKernel k a u = (a ^ (k + 1))⁻¹ := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := (k : ℝ) + 1) (r := a) (by positivity) ha
  rw [Real.Gamma_nat_eq_factorial] at h
  have hfun : ∀ u ∈ Ioi (0 : ℝ), taylorKernel k a u =
      u ^ ((k : ℝ) + 1 - 1) * Real.exp (-(a * u)) / (k.factorial : ℝ) := by
    intro u _
    unfold taylorKernel
    rw [add_sub_cancel_right, Real.rpow_natCast, neg_mul]
  have hk : (k.factorial : ℝ) ≠ 0 := by positivity
  rw [setIntegral_congr_fun measurableSet_Ioi hfun, integral_div, h, mul_div_assoc, div_self hk,
    mul_one, one_div, Real.inv_rpow ha.le, show ((k : ℝ) + 1) = ((k + 1 : ℕ) : ℝ) by push_cast; ring,
    Real.rpow_natCast]

theorem integrableOn_taylorKernel (k : ℕ) {a : ℝ} (ha : 0 < a) :
    IntegrableOn (taylorKernel k a) (Ioi 0) := by
  refine Integrable.of_integral_ne_zero ?_
  rw [integral_taylorKernel k ha]
  positivity

/-- Exponential tilting: the kernel mass outside a window `[U, V]`. -/
theorem integral_taylorKernel_diff_Icc_le (k : ℕ) {a l : ℝ} (U V : ℝ) (hl : 0 ≤ l) (hla : l < a) :
    ∫ u in Ioi (0 : ℝ) \ Icc U V, taylorKernel k a u ≤
      Real.exp (-(l * V)) * ((a - l) ^ (k + 1))⁻¹ + Real.exp (l * U) * ((a + l) ^ (k + 1))⁻¹ := by
  have ha : 0 < a := lt_of_le_of_lt hl hla
  set h : ℝ → ℝ := fun u =>
    Real.exp (-(l * V)) * taylorKernel k (a - l) u + Real.exp (l * U) * taylorKernel k (a + l) u
    with hh
  have hint : IntegrableOn h (Ioi 0) :=
    ((integrableOn_taylorKernel k (sub_pos.mpr hla)).const_mul _).add
      ((integrableOn_taylorKernel k (by linarith)).const_mul _)
  have hsub : Ioi (0 : ℝ) \ Icc U V ⊆ Ioi 0 := fun _ hu => hu.1
  have hmeas : MeasurableSet (Ioi (0 : ℝ) \ Icc U V) := measurableSet_Ioi.diff measurableSet_Icc
  have hpt : ∀ u ∈ Ioi (0 : ℝ) \ Icc U V, taylorKernel k a u ≤ h u := by
    rintro u ⟨hu, hout⟩
    have hu0 : (0 : ℝ) < u := hu
    have hk : (0 : ℝ) < (k.factorial : ℝ) := by positivity
    have hpow : 0 ≤ u ^ k := by positivity
    have n1 := taylorKernel_nonneg k (a - l) hu0.le
    have n2 := taylorKernel_nonneg k (a + l) hu0.le
    rcases lt_or_ge V u with hVu | hVu
    · -- above the window: tilt by `e^{-l(u - V)} ≤ 1`
      have e : taylorKernel k a u =
          Real.exp (-(l * u)) * taylorKernel k (a - l) u := by
        unfold taylorKernel
        rw [show -a * u = -(l * u) + -(a - l) * u by ring, Real.exp_add]
        ring
      have hexp : Real.exp (-(l * u)) ≤ Real.exp (-(l * V)) :=
        Real.exp_le_exp.mpr (by nlinarith)
      rw [e, hh]
      have := mul_le_mul_of_nonneg_right hexp n1
      have := mul_nonneg (Real.exp_pos (l * U)).le n2
      linarith
    · -- below the window: tilt by `e^{-l(U - u)} ≤ 1`
      have huU : u < U := by
        by_contra hcon
        exact hout ⟨not_lt.mp hcon, hVu⟩
      have e : taylorKernel k a u =
          Real.exp (l * u) * taylorKernel k (a + l) u := by
        unfold taylorKernel
        rw [show -a * u = l * u + -(a + l) * u by ring, Real.exp_add]
        ring
      have hexp : Real.exp (l * u) ≤ Real.exp (l * U) :=
        Real.exp_le_exp.mpr (by nlinarith)
      rw [e, hh]
      have := mul_le_mul_of_nonneg_right hexp n2
      have := mul_nonneg (Real.exp_pos (-(l * V))).le n1
      linarith
  have hnn : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] h := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with u hu
    have hu0 : (0 : ℝ) ≤ u := le_of_lt hu
    exact add_nonneg (mul_nonneg (Real.exp_pos _).le (taylorKernel_nonneg k _ hu0))
      (mul_nonneg (Real.exp_pos _).le (taylorKernel_nonneg k _ hu0))
  calc ∫ u in Ioi (0 : ℝ) \ Icc U V, taylorKernel k a u
      ≤ ∫ u in Ioi (0 : ℝ) \ Icc U V, h u :=
        setIntegral_mono_on ((integrableOn_taylorKernel k ha).mono_set hsub) (hint.mono_set hsub)
          hmeas hpt
    _ ≤ ∫ u in Ioi (0 : ℝ), h u :=
        setIntegral_mono_set hint hnn (Eventually.of_forall hsub)
    _ = Real.exp (-(l * V)) * ((a - l) ^ (k + 1))⁻¹ +
          Real.exp (l * U) * ((a + l) ^ (k + 1))⁻¹ := by
        rw [hh, integral_add ((integrableOn_taylorKernel k (sub_pos.mpr hla)).const_mul _)
          ((integrableOn_taylorKernel k (by linarith)).const_mul _), integral_const_mul,
          integral_const_mul, integral_taylorKernel k (sub_pos.mpr hla),
          integral_taylorKernel k (by linarith)]

/-- If `σ ≤ c e^t` and `x + k t ≤ y` then `e^x c^{-(k+1)} ≤ (e^y / c) σ^{-k}`. -/
theorem exp_mul_inv_pow_le {σ c t x y : ℝ} (hσ : 0 < σ) (hc : 0 < c) (h : σ ≤ c * Real.exp t)
    (k : ℕ) (hxy : x + k * t ≤ y) :
    Real.exp x * (c ^ (k + 1))⁻¹ ≤ c⁻¹ * Real.exp y / σ ^ k := by
  have h1 : σ ^ k ≤ c ^ k * Real.exp (k * t) := by
    calc σ ^ k ≤ (c * Real.exp t) ^ k := pow_le_pow_left₀ hσ.le h k
      _ = c ^ k * Real.exp (k * t) := by rw [mul_pow, ← Real.exp_nat_mul]
  have h2 : Real.exp x * Real.exp (k * t) ≤ Real.exp y := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr hxy
  have hck : 0 < c ^ k := pow_pos hc k
  rw [le_div_iff₀ (pow_pos hσ k), pow_succ, mul_inv]
  calc Real.exp x * ((c ^ k)⁻¹ * c⁻¹) * σ ^ k
      ≤ Real.exp x * ((c ^ k)⁻¹ * c⁻¹) * (c ^ k * Real.exp (k * t)) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = c⁻¹ * (Real.exp x * Real.exp (k * t)) := by
        field_simp
    _ ≤ c⁻¹ * Real.exp y := mul_le_mul_of_nonneg_left h2 (inv_pos.mpr hc).le

/-- **Kernel mass outside a window.** For every window shape `δ` and growth exponent `b` there is
a decay rate `a ≥ 1` such that for each window `[U, (1+δ)U]` some `k ≥ U` has kernel mass
at most `C (a+b)^{-k}` outside the window. -/
theorem exists_taylorKernel_tail_le {δ b : ℝ} (hδ : 0 < δ) (hb : 0 ≤ b) :
    ∃ a : ℝ, 1 ≤ a ∧ ∃ C : ℝ, ∀ U : ℝ, 1 ≤ U → ∃ k : ℕ, U ≤ k ∧
      ∫ u in Ioi (0 : ℝ) \ Icc U ((1 + δ) * U), taylorKernel k a u ≤ C / (a + b) ^ k := by
  -- the window is `[U, m(1+τ)U]` with centre `mU` and `m(1-τ) = 1`
  set τ : ℝ := δ / (2 + δ) with hτ
  have hτ0 : 0 < τ := by positivity
  have hτ1 : τ < 1 := by rw [hτ, div_lt_one (by linarith)]; linarith
  set m : ℝ := 1 + δ / 2 with hm
  have hm1 : 1 ≤ m := by rw [hm]; linarith
  have hm0 : 0 < m := by linarith
  have hmτ : m * (1 - τ) = 1 := by rw [hm, hτ]; field_simp; ring
  have hmτ' : m * (1 + τ) = 1 + δ := by rw [hm, hτ]; field_simp; ring
  set ε : ℝ := τ / 3 with hε
  have hε0 : 0 < ε := by positivity
  have hε1 : ε < 1 := by rw [hε]; linarith
  set a : ℝ := max 1 (6 * b / τ ^ 2) with ha
  have ha1 : 1 ≤ a := le_max_left _ _
  have ha0 : 0 < a := by linarith
  have hba : b / a ≤ τ ^ 2 / 6 := by
    rw [div_le_iff₀ ha0]
    have h1 : 6 * b / τ ^ 2 ≤ a := le_max_right _ _
    rw [div_le_iff₀ (by positivity)] at h1
    linarith
  have hba0 : 0 ≤ b / a := div_nonneg hb ha0.le
  set l : ℝ := ε * a with hl
  have hl0 : 0 ≤ l := by positivity
  have hla : l < a := by rw [hl]; nlinarith
  have hal : 0 < a - l := sub_pos.mpr hla
  have hσ : 0 < a + b := by linarith
  -- `a + b ≤ a e^{b/a}`
  have hab : a + b ≤ a * Real.exp (b / a) := by
    have := Real.add_one_le_exp (b / a)
    calc a + b = a * (b / a + 1) := by field_simp; ring
      _ ≤ a * Real.exp (b / a) := mul_le_mul_of_nonneg_left this ha0.le
  -- the two tilts: `a = (a - l)(1 + ε/(1-ε)) = (a + l)(1 - ε/(1+ε))`
  have hup : a + b ≤ (a - l) * Real.exp (b / a + ε / (1 - ε)) := by
    have h1 := Real.add_one_le_exp (ε / (1 - ε))
    have h2 : a = (a - l) * (ε / (1 - ε) + 1) := by
      rw [hl]; field_simp [sub_ne_zero.mpr hε1.ne']; ring
    have h3 : a ≤ (a - l) * Real.exp (ε / (1 - ε)) := by
      calc a = (a - l) * (ε / (1 - ε) + 1) := h2
        _ ≤ (a - l) * Real.exp (ε / (1 - ε)) := mul_le_mul_of_nonneg_left h1 hal.le
    calc a + b ≤ a * Real.exp (b / a) := hab
      _ ≤ (a - l) * Real.exp (ε / (1 - ε)) * Real.exp (b / a) :=
          mul_le_mul_of_nonneg_right h3 (Real.exp_pos _).le
      _ = (a - l) * Real.exp (b / a + ε / (1 - ε)) := by
          rw [mul_assoc, ← Real.exp_add, add_comm]
  have hlo : a + b ≤ (a + l) * Real.exp (b / a - ε / (1 + ε)) := by
    have h1 := Real.add_one_le_exp (-(ε / (1 + ε)))
    have h2 : a = (a + l) * (-(ε / (1 + ε)) + 1) := by
      rw [hl]; field_simp; ring
    have h3 : a ≤ (a + l) * Real.exp (-(ε / (1 + ε))) := by
      calc a = (a + l) * (-(ε / (1 + ε)) + 1) := h2
        _ ≤ (a + l) * Real.exp (-(ε / (1 + ε))) := mul_le_mul_of_nonneg_left h1 (by linarith)
    calc a + b ≤ a * Real.exp (b / a) := hab
      _ ≤ (a + l) * Real.exp (-(ε / (1 + ε))) * Real.exp (b / a) :=
          mul_le_mul_of_nonneg_right h3 (Real.exp_pos _).le
      _ = (a + l) * Real.exp (b / a - ε / (1 + ε)) := by
          rw [mul_assoc, ← Real.exp_add]; congr 2; ring
  -- the tilts lose less than the window gains
  have hgain_up : b / a + ε / (1 - ε) ≤ ε * (1 + τ) := by
    have key : (ε + τ ^ 2 / 6) * (1 - ε) - ε = τ ^ 2 * (1 - τ) / 18 := by rw [hε]; ring
    have h1 : ε / (1 - ε) ≤ ε + τ ^ 2 / 6 := by
      rw [div_le_iff₀ (by linarith)]
      linarith [mul_nonneg (sq_nonneg τ) (sub_nonneg.mpr hτ1.le)]
    have p : ε * (1 + τ) = ε + τ ^ 2 / 3 := by rw [hε]; ring
    rw [p]
    linarith
  have hgain_lo : b / a - ε / (1 + ε) + ε * (1 - τ) ≤ 0 := by
    have key : ε * (1 - ε) * (1 + ε) = ε - ε * ε ^ 2 := by ring
    have h1 : ε * (1 - ε) ≤ ε / (1 + ε) := by
      rw [le_div_iff₀ (by linarith), key]
      linarith [mul_nonneg hε0.le (sq_nonneg ε)]
    have p1 : ε * (1 - ε) = ε - τ ^ 2 / 9 := by rw [hε]; ring
    have p2 : ε * (1 - τ) = ε - τ ^ 2 / 3 := by rw [hε]; ring
    rw [p1] at h1
    rw [p2]
    linarith [sq_nonneg τ]
  refine ⟨a, ha1, (a - l)⁻¹ * Real.exp (ε * (1 + τ)) + (a + l)⁻¹ * Real.exp 0, fun U hU => ?_⟩
  have hU0 : 0 < U := by linarith
  set k : ℕ := ⌈a * m * U⌉₊ with hk
  have hk1 : a * m * U ≤ k := Nat.le_ceil _
  have hk2 : (k : ℝ) < a * m * U + 1 := Nat.ceil_lt_add_one (by positivity)
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  refine ⟨k, ?_, ?_⟩
  · have : U ≤ a * m * U := by
      have : 1 ≤ a * m := one_le_mul_of_one_le_of_one_le ha1 hm1
      nlinarith
    linarith
  · refine (integral_taylorKernel_diff_Icc_le k U ((1 + δ) * U) hl0 hla).trans ?_
    rw [add_div]
    refine add_le_add ?_ ?_
    · -- above: `l (1+δ) U = ε (1+τ) a m U ≥ ε (1+τ) (k - 1)`
      refine exp_mul_inv_pow_le hσ hal hup k ?_
      have e : l * ((1 + δ) * U) = ε * (1 + τ) * (a * m * U) := by rw [hl, ← hmτ']; ring
      rw [e]
      have hE0 : 0 ≤ ε * (1 + τ) := mul_nonneg hε0.le (by linarith)
      have h1 : ε * (1 + τ) * ((k : ℝ) - 1) ≤ ε * (1 + τ) * (a * m * U) :=
        mul_le_mul_of_nonneg_left (by linarith) hE0
      have h2 : (k : ℝ) * (b / a + ε / (1 - ε)) ≤ k * (ε * (1 + τ)) :=
        mul_le_mul_of_nonneg_left hgain_up hk0
      linarith
    · -- below: `l U = ε (1-τ) a m U ≤ ε (1-τ) k`
      refine exp_mul_inv_pow_le hσ (by linarith) hlo k ?_
      have e : l * U = ε * (1 - τ) * (a * m * U) := by
        rw [hl]
        calc ε * a * U = ε * a * U * (m * (1 - τ)) := by rw [hmτ, mul_one]
          _ = ε * (1 - τ) * (a * m * U) := by ring
      rw [e]
      have hE0 : 0 ≤ ε * (1 - τ) := mul_nonneg hε0.le (by linarith)
      have h1 : ε * (1 - τ) * (a * m * U) ≤ ε * (1 - τ) * k :=
        mul_le_mul_of_nonneg_left hk1 hE0
      have h2 : (k : ℝ) * (b / a - ε / (1 + ε) + ε * (1 - τ)) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hk0 hgain_lo
      linarith

/-! ## Derivatives of a Laplace transform -/

/-- The integrand `g(u) (-u)^k e^{-zu}` is dominated by `C u^k e^{-(Re z - b)u}`. -/
theorem norm_laplaceTerm_le {g : ℝ → ℂ} {C b : ℝ}
    (hgC : ∀ u, 0 < u → ‖g u‖ ≤ C * Real.exp (b * u)) (k : ℕ) (z : ℂ) {u : ℝ} (hu : 0 < u) :
    ‖g u * (-(u : ℂ)) ^ k * cexp (-z * u)‖ ≤ C * (u ^ k * Real.exp (-(z.re - b) * u)) := by
  rw [norm_mul, norm_mul, norm_pow, norm_neg, Complex.norm_real, Real.norm_of_nonneg hu.le,
    Complex.norm_exp]
  have hre : (-z * (u : ℂ)).re = -z.re * u := by simp
  rw [hre]
  have h2 : Real.exp (b * u) * (u ^ k * Real.exp (-z.re * u)) =
      u ^ k * Real.exp (-(z.re - b) * u) := by
    rw [mul_left_comm, ← Real.exp_add]
    congr 2
    ring
  calc ‖g u‖ * u ^ k * Real.exp (-z.re * u)
      ≤ C * Real.exp (b * u) * u ^ k * Real.exp (-z.re * u) := by
        gcongr
        exact hgC u hu
    _ = C * (u ^ k * Real.exp (-(z.re - b) * u)) := by rw [← h2]; ring

theorem aestronglyMeasurable_laplaceTerm {g : ℝ → ℂ}
    (hg : AEStronglyMeasurable g (volume.restrict (Ioi (0 : ℝ)))) (k : ℕ) (z : ℂ) :
    AEStronglyMeasurable (fun u : ℝ => g u * (-(u : ℂ)) ^ k * cexp (-z * u))
      (volume.restrict (Ioi (0 : ℝ))) :=
  (hg.mul (by fun_prop : Continuous fun u : ℝ => (-(u : ℂ)) ^ k).aestronglyMeasurable).mul
    (by fun_prop : Continuous fun u : ℝ => cexp (-z * u)).aestronglyMeasurable

/-- `u^k e^{-cu}` is integrable on `(0,∞)` for `c > 0`. -/
theorem integrableOn_pow_mul_exp (k : ℕ) {c : ℝ} (hc : 0 < c) :
    IntegrableOn (fun u : ℝ => u ^ k * Real.exp (-c * u)) (Ioi 0) := by
  have h : IntegrableOn (fun u : ℝ => (k.factorial : ℝ) * taylorKernel k c u) (Ioi 0) :=
    (integrableOn_taylorKernel k hc).const_mul (k.factorial : ℝ)
  refine IntegrableOn.congr_fun h (fun u _ => ?_) measurableSet_Ioi
  unfold taylorKernel
  field_simp

theorem integrableOn_laplaceTerm {g : ℝ → ℂ}
    (hg : AEStronglyMeasurable g (volume.restrict (Ioi (0 : ℝ)))) {C b : ℝ}
    (hgC : ∀ u, 0 < u → ‖g u‖ ≤ C * Real.exp (b * u)) (k : ℕ) {z : ℂ} (hz : b < z.re) :
    IntegrableOn (fun u : ℝ => g u * (-(u : ℂ)) ^ k * cexp (-z * u)) (Ioi 0) := by
  refine Integrable.mono' ((integrableOn_pow_mul_exp k (sub_pos.mpr hz)).const_mul C)
    (aestronglyMeasurable_laplaceTerm hg k z) ?_
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with u hu
  exact norm_laplaceTerm_le hgC k z hu

/-- Differentiation under the Laplace integral. -/
theorem hasDerivAt_laplaceTerm {g : ℝ → ℂ}
    (hg : AEStronglyMeasurable g (volume.restrict (Ioi (0 : ℝ)))) {C b : ℝ}
    (hgC : ∀ u, 0 < u → ‖g u‖ ≤ C * Real.exp (b * u)) (k : ℕ) {s : ℂ} (hs : b < s.re) :
    HasDerivAt (fun z : ℂ => ∫ u in Ioi (0 : ℝ), g u * (-(u : ℂ)) ^ k * cexp (-z * u))
      (∫ u in Ioi (0 : ℝ), g u * (-(u : ℂ)) ^ (k + 1) * cexp (-s * u)) s := by
  set ε : ℝ := (s.re - b) / 2 with hε
  have hε0 : 0 < ε := by rw [hε]; linarith
  have hC0 : 0 ≤ C := by
    have h := hgC 1 one_pos
    have : 0 ≤ C * Real.exp (b * 1) := (norm_nonneg _).trans h
    exact nonneg_of_mul_nonneg_left this (Real.exp_pos _)
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioi (0 : ℝ)))
    (F := fun (z : ℂ) (u : ℝ) => g u * (-(u : ℂ)) ^ k * cexp (-z * u))
    (F' := fun (z : ℂ) (u : ℝ) => g u * (-(u : ℂ)) ^ (k + 1) * cexp (-z * u))
    (bound := fun u : ℝ => C * (u ^ (k + 1) * Real.exp (-ε * u)))
    (Metric.ball_mem_nhds s hε0)
    (Eventually.of_forall fun z => aestronglyMeasurable_laplaceTerm hg k z)
    (integrableOn_laplaceTerm hg hgC k hs)
    (aestronglyMeasurable_laplaceTerm hg (k + 1) s) ?_
    ((integrableOn_pow_mul_exp (k + 1) hε0).const_mul C) ?_).2
  · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with u hu z hz
    have hu0 : (0 : ℝ) < u := hu
    refine (norm_laplaceTerm_le hgC (k + 1) z hu0).trans ?_
    have hzre : b + ε < z.re := by
      have h1 := Complex.abs_re_le_norm (z - s)
      rw [Metric.mem_ball, Complex.dist_eq] at hz
      rw [Complex.sub_re] at h1
      have h2 := (abs_le.mp h1).1
      rw [hε] at hz ⊢
      linarith
    have hexp : Real.exp (-(z.re - b) * u) ≤ Real.exp (-ε * u) :=
      Real.exp_le_exp.mpr (by nlinarith)
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hexp (by positivity)) hC0
  · filter_upwards with u z _
    show HasDerivAt (fun z : ℂ => g u * (-(u : ℂ)) ^ k * cexp (-z * u))
      (g u * (-(u : ℂ)) ^ (k + 1) * cexp (-z * u)) z
    have h1 : HasDerivAt (fun z : ℂ => cexp (-z * u)) (cexp (-z * u) * (-(u : ℂ))) z := by
      have h0 : HasDerivAt (fun z : ℂ => -z * (u : ℂ)) (-(u : ℂ)) z := by
        simpa using (hasDerivAt_id z).neg.mul_const (u : ℂ)
      exact h0.cexp
    have h2 := h1.const_mul (g u * (-(u : ℂ)) ^ k)
    rw [show g u * (-(u : ℂ)) ^ (k + 1) * cexp (-z * u) =
      g u * (-(u : ℂ)) ^ k * (cexp (-z * u) * (-(u : ℂ))) by ring]
    exact h2

/-- **Derivatives of a Laplace transform**: `Φ^(k)(s) = ∫₀^∞ g(u) (-u)^k e^{-su} du` on
`Re s > b`. -/
theorem iteratedDeriv_laplace {g : ℝ → ℂ}
    (hg : AEStronglyMeasurable g (volume.restrict (Ioi (0 : ℝ)))) {C b : ℝ}
    (hgC : ∀ u, 0 < u → ‖g u‖ ≤ C * Real.exp (b * u)) (k : ℕ) {s : ℂ} (hs : b < s.re) :
    iteratedDeriv k (fun z : ℂ => ∫ u in Ioi (0 : ℝ), g u * cexp (-z * u)) s =
      ∫ u in Ioi (0 : ℝ), g u * (-(u : ℂ)) ^ k * cexp (-s * u) := by
  induction k generalizing s with
  | zero => simp
  | succ k ih =>
    rw [iteratedDeriv_succ]
    have hopen : ∀ᶠ z in 𝓝 s, b < z.re :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs
    have heq : iteratedDeriv k (fun z : ℂ => ∫ u in Ioi (0 : ℝ), g u * cexp (-z * u)) =ᶠ[𝓝 s]
        fun z => ∫ u in Ioi (0 : ℝ), g u * (-(u : ℂ)) ^ k * cexp (-z * u) :=
      hopen.mono fun z hz => ih hz
    rw [heq.deriv_eq]
    exact (hasDerivAt_laplaceTerm hg hgC k hs).deriv

/-- The coefficient integral `∫₀^∞ g(u) u^k e^{-su} / k! du`. -/
def laplaceCoeff (g : ℝ → ℂ) (k : ℕ) (s : ℂ) : ℂ :=
  ∫ u in Ioi (0 : ℝ), g u * ((u : ℂ) ^ k * cexp (-s * u) / (k.factorial : ℂ))

/-- **Taylor coefficients of a Laplace transform.** If `Φ` is the Laplace transform of `g` on
`Re z > b`, then `(-1)^k Φ^(k)(s)/k!` is the coefficient integral. -/
theorem taylorCoeff_eq_laplaceCoeff {g : ℝ → ℂ}
    (hg : AEStronglyMeasurable g (volume.restrict (Ioi (0 : ℝ)))) {C b : ℝ}
    (hgC : ∀ u, 0 < u → ‖g u‖ ≤ C * Real.exp (b * u)) {Φ : ℂ → ℂ}
    (hΦ : ∀ z : ℂ, b < z.re → Φ z = ∫ u in Ioi (0 : ℝ), g u * cexp (-z * u)) (k : ℕ) {s : ℂ}
    (hs : b < s.re) :
    (-1) ^ k * iteratedDeriv k Φ s / (k.factorial : ℂ) = laplaceCoeff g k s := by
  have hopen : ∀ᶠ z in 𝓝 s, b < z.re :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs
  have heq : Φ =ᶠ[𝓝 s] fun z : ℂ => ∫ u in Ioi (0 : ℝ), g u * cexp (-z * u) :=
    hopen.mono fun z hz => hΦ z hz
  rw [heq.iteratedDeriv_eq, iteratedDeriv_laplace hg hgC k hs, laplaceCoeff, ← integral_const_mul,
    ← integral_div]
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  have h1 : (-1 : ℂ) ^ k * (-(u : ℂ)) ^ k = (u : ℂ) ^ k := by
    rw [← mul_pow]; simp
  simp only
  rw [← h1]
  ring

end

end WindowedLandauTheory
