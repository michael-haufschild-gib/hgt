import GaloisForLFunctions.RHTower.PrimeBlindCarlsonThreshold

/-!
# Integer blindness under logarithmic room: the exact constant `π/2`

Let `w` be measurable on `ℝ` with Dirichlet moments `∫ w(t) n^{-it} dt` vanishing at every `n` of a
set `N ⊆ [2, ∞)`.  The transform `G(ζ) = ∫ w(t) e^{-it log ζ} dt` lives on `Re ζ > 0`; the decay
`e^{-(π/2)|t|}` of `w` is the boundary of its existence.

**Theorem** (`fourier_eq_zero_of_dirichletMoment_eq_zero_logRoom`,
`fourier_eq_zero_of_integerMoment_eq_zero_logRoom`).  If for some `0 ≤ K < π/2`
`∫ |w(t)| e^{(π/2)|t| - K|t|/log(|t|+3)} dt < ∞` and `Σ_{n ∈ N} 1/(n log n) = ∞` (for instance all
`n ≥ 2`, `not_summable_one_div_mul_log`), then the Fourier transform of `w` vanishes.

The room `K|t|/log|t|` is far beyond Carlson's `√|t|`: the transform may grow like `exp(e^{K/δ})` at
angle `δ` from the imaginary axis.  Composing with the narrowing `u ↦ u / log u`
(`re_div_log_pos_and_le`) keeps the angle `≥ (π/2)/(log|u| + 2)`, so `log |G|` grows like
`|u|^{2K/π}` on the narrowed boundary; for `2K/π < 1` the circle averages stay bounded
(`circleAverage_rpow_neg_norm_one_sub_le`).  The narrowing moves the node `n` to `x_n ≈ n log n`
(`exists_div_log_eq`), and `Σ 1/(n log n) = ∞` violates the Blaschke condition
(`summable_log_inv_of_circleAverage_le`).

**Analytic form and finitely many exceptions** (`eqOn_zero_of_logRoom_growth`,
`eqOn_zero_of_logRoom_growth_off_finite`).  The argument only uses an analytic `G` on `Re ζ > 0`
with `|G(ζ)| ≤ A e^{K e^{K/δ}} (1 + |ζ|)^c`; the polynomial factor is absorbed by circle averages of
`|1 - z|^{-1/2}`.  Multiplying by `∏_{f ∈ F}(ζ - f)` shows that vanishing outside a finite set `F`
already forces `G ≡ 0`.  Hence a test blind at every integer `n ≥ 2` except finitely many is blind
at all of them (`dirichletMoment_eq_zero_of_cofinite_logRoom`): `n₀`-selective tests do not exist
under logarithmic room `K < π/2`.

The constant is exact: for `K > π/2` the function `sin(πζ) e^{-πcζ log ζ}` with `1/c + π/2 < K`
yields a nonzero `w`, blind at every integer, with `|w(t)| ≤ e^{-(π/2)|t| + K|t|/log|t|}` for large
`|t|`.  The threshold of the room is therefore `(π/2)|t|/log|t|`: a blind `w` cannot decay faster than
`e^{-(π/2)(|t| - |t|/log|t|)}`.  Applied to a weight `Ξ² h` blind at every integer `n ≥ 2`, whose
`Ξ²` decays like `|t|^{7/2}|ζ(1/2+it)|² e^{-(π/2)|t|}`, the multiplier `h` satisfies
`∫ |t|^{7/2} |ζ(1/2+it)|² |h(t)| e^{-K|t|/log(|t|+3)} dt = ∞` for every `K < π/2`.
-/

open Metric Real Filter Topology MeasureTheory Set Complex

noncomputable section

namespace RHTower.PrimeBlindCarlson

/-- For `L ≥ 4` and `|ψ| ≤ π/2`: `L cos ψ + ψ sin ψ ≥ π/2`. -/
theorem pi_div_two_le_mul_cos_add {L ψ : ℝ} (hL : 4 ≤ L) (hψ : |ψ| ≤ π / 2) :
    π / 2 ≤ L * Real.cos ψ + ψ * Real.sin ψ := by
  have hsym : ψ * Real.sin ψ = |ψ| * Real.sin |ψ| := by
    rcases abs_cases ψ with ⟨h, -⟩ | ⟨h, -⟩
    · rw [h]
    · rw [h, Real.sin_neg]; ring
  rw [hsym, ← Real.cos_abs ψ]
  obtain ⟨s, hs⟩ : ∃ s, |ψ| = π / 2 - s := ⟨π / 2 - |ψ|, by ring⟩
  have hs0 : 0 ≤ s := by linarith
  have hs1 : s ≤ π / 2 := by have := abs_nonneg ψ; linarith
  rw [hs, Real.cos_pi_div_two_sub, Real.sin_pi_div_two_sub]
  have hsin := Real.mul_le_sin hs0 hs1
  have hcos := Real.one_sub_sq_div_two_le_cos (x := s)
  have hπ1 := Real.pi_gt_three
  have hπ2 := Real.pi_lt_d2
  have hA : 0 ≤ π / 2 - s := by linarith
  have h1 : L * (2 / π * s) ≤ L * Real.sin s := mul_le_mul_of_nonneg_left hsin (by linarith)
  have h2 : (π / 2 - s) * (1 - s ^ 2 / 2) ≤ (π / 2 - s) * Real.cos s :=
    mul_le_mul_of_nonneg_left hcos hA
  have h8 : (2.5 : ℝ) ≤ 8 / π := by rw [le_div_iff₀ (by positivity)]; nlinarith
  have h3 : 2.5 * s ≤ L * (2 / π * s) := by
    have e1 : L * (2 / π * s) = (L * 2) * (s / π) := by ring
    have e2 : 8 / π * s = 8 * (s / π) := by ring
    have hsπ : 0 ≤ s / π := by positivity
    have : 8 * (s / π) ≤ (L * 2) * (s / π) := mul_le_mul_of_nonneg_right (by linarith) hsπ
    nlinarith [mul_le_mul_of_nonneg_right h8 hs0]
  nlinarith [mul_nonneg hs0 hs0, mul_nonneg (mul_nonneg hs0 hs0) hs0]

/-- `K s / log(s+3) - δ s ≤ K e^{K/δ}` for `s ≥ 0`. -/
theorem mul_div_log_sub_le {K δ s : ℝ} (hK : 0 ≤ K) (hδ : 0 < δ) (hs : 0 ≤ s) :
    K * s / Real.log (s + 3) - δ * s ≤ K * Real.exp (K / δ) := by
  have hlog3 : 1 ≤ Real.log (s + 3) := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9; linarith
  have hlogpos : 0 < Real.log (s + 3) := by linarith
  have hKexp : 0 ≤ K * Real.exp (K / δ) := mul_nonneg hK (Real.exp_pos _).le
  rcases le_or_gt (K / δ) (Real.log (s + 3)) with h | h
  · have : K * s / Real.log (s + 3) ≤ δ * s := by
      rw [div_le_iff₀ hlogpos]
      have h' : K ≤ δ * Real.log (s + 3) := by rwa [div_le_iff₀ hδ, mul_comm] at h
      nlinarith
    linarith
  · have hsexp : s ≤ Real.exp (K / δ) := by
      have := (Real.log_lt_iff_lt_exp (by linarith)).mp h
      linarith
    have : K * s / Real.log (s + 3) ≤ K * s := by
      rw [div_le_iff₀ hlogpos]; nlinarith [mul_nonneg hK hs]
    nlinarith [mul_le_mul_of_nonneg_left hsexp hK]

/-- The critical weight with logarithmic room `K`: `e^{(π/2)|t| - K|t|/log(|t|+3)}`. -/
def logRoomWeight (K t : ℝ) : ℝ := Real.exp (π / 2 * |t| - K * |t| / Real.log (|t| + 3))

theorem logRoomWeight_nonneg (K t : ℝ) : 0 ≤ logRoomWeight K t := (Real.exp_pos _).le

/-- `e^{(π/2 - δ)|t|} ≤ ω_K(t) e^{K e^{K/δ}}`. -/
theorem exp_le_logRoomWeight_mul {K δ : ℝ} (hK : 0 ≤ K) (hδ : 0 < δ) (t : ℝ) :
    Real.exp ((π / 2 - δ) * |t|) ≤ logRoomWeight K t * Real.exp (K * Real.exp (K / δ)) := by
  unfold logRoomWeight
  rw [← Real.exp_add]
  refine Real.exp_le_exp.mpr ?_
  have := mul_div_log_sub_le hK hδ (abs_nonneg t)
  linarith

theorem dominatesSubcritical_logRoomWeight {K : ℝ} (hK : 0 ≤ K) :
    DominatesSubcritical (logRoomWeight K) := by
  intro c hc
  obtain ⟨K₁, -, hK₁⟩ := exists_rpow_mul_exp_neg_le (b := 1) zero_le_one
  refine ⟨Real.exp (K * Real.exp (K / (c / 2))) * (Real.exp (c / 2) * (c / 2) ^ (-(1 : ℝ)) * K₁),
    fun t => ?_⟩
  have hs : 0 ≤ |t| := abs_nonneg t
  have hkey := one_add_rpow_mul_exp_neg_le hK₁ (half_pos hc) hs
  rw [Real.rpow_one] at hkey
  have hsup := mul_div_log_sub_le hK (half_pos hc) hs
  have heq : (1 + |t|) * Real.exp ((π / 2 - c) * |t|) =
      logRoomWeight K t * ((1 + |t|) *
        Real.exp (K * |t| / Real.log (|t| + 3) - c / 2 * |t| + -(c / 2 * |t|))) := by
    unfold logRoomWeight
    rw [show (π / 2 - c) * |t| = (π / 2 * |t| - K * |t| / Real.log (|t| + 3)) +
      (K * |t| / Real.log (|t| + 3) - c / 2 * |t| + -(c / 2 * |t|)) by ring, Real.exp_add]
    ring
  rw [heq]
  refine mul_le_mul_of_nonneg_left ?_ (logRoomWeight_nonneg K t)
  rw [Real.exp_add]
  calc (1 + |t|) * (Real.exp (K * |t| / Real.log (|t| + 3) - c / 2 * |t|) *
        Real.exp (-(c / 2 * |t|)))
      ≤ (1 + |t|) * (Real.exp (K * Real.exp (K / (c / 2))) * Real.exp (-(c / 2 * |t|))) := by
        gcongr
    _ = Real.exp (K * Real.exp (K / (c / 2))) * ((1 + |t|) * Real.exp (-(c / 2 * |t|))) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hkey (Real.exp_pos _).le

variable {w : ℝ → ℂ}

/-- **Growth with logarithmic room.**  `|G(ζ)| ≤ B e^{K e^{K/(π/2 - |arg ζ|)}}`. -/
theorem norm_logFourier_le_logRoom {K : ℝ} (hK : 0 ≤ K)
    (hroom : Integrable fun t => ‖w t‖ * logRoomWeight K t) {ζ : ℂ} (hζ : 0 < ζ.re) :
    ‖logFourier w ζ‖ ≤ (∫ t, ‖w t‖ * logRoomWeight K t) *
      Real.exp (K * Real.exp (K / (π / 2 - |ζ.arg|))) := by
  set η := π / 2 - |ζ.arg| with hη
  have hη0 : 0 < η := by
    have := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hζ); linarith
  unfold logFourier
  rw [← integral_mul_const]
  refine norm_integral_le_of_norm_le (hroom.mul_const _) ?_
  filter_upwards with t
  rw [norm_mul, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  exact (norm_cexp_log_le_of_abs_arg_le (a := π / 2 - η) (by rw [hη]; ring_nf; rfl) t).trans
    (exp_le_logRoomWeight_mul hK hη0 t)

/-! ## The logarithmic narrowing `u ↦ u / log u` -/

/-- For `Re u > 0` and `log |u| ≥ 4`, `u / log u` lies in the right half-plane at angular distance
at least `(π/2)/(log |u| + 2)` from the imaginary axis. -/
theorem re_div_log_pos_and_le {u : ℂ} (hu : 0 < u.re) (hL : 4 ≤ Real.log ‖u‖) :
    0 < (u / Complex.log u).re ∧
      π / 2 / (Real.log ‖u‖ + 2) ≤ π / 2 - |(u / Complex.log u).arg| := by
  have hu0 : u ≠ 0 := by rintro rfl; simp at hu
  set L := Real.log ‖u‖ with hLdef
  have hψ : |u.arg| < π / 2 := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hu)
  have hvre : (Complex.log u).re = L := Complex.log_re u
  have hvim : (Complex.log u).im = u.arg := Complex.log_im u
  have hnv_le : ‖Complex.log u‖ ≤ L + 2 := by
    have h := Complex.norm_le_abs_re_add_abs_im (Complex.log u)
    rw [hvre, hvim, abs_of_nonneg (by linarith : (0 : ℝ) ≤ L)] at h
    have : |u.arg| ≤ 2 := by have := Real.pi_lt_d2; linarith
    linarith
  have hnv_ge : L ≤ ‖Complex.log u‖ := by rw [← hvre]; exact Complex.re_le_norm _
  have hnv : 0 < ‖Complex.log u‖ := by linarith
  have hkey := pi_div_two_le_mul_cos_add hL hψ.le
  have hre : (u / Complex.log u).re =
      ‖u‖ * (L * Real.cos u.arg + u.arg * Real.sin u.arg) / ‖Complex.log u‖ ^ 2 := by
    rw [Complex.div_re, Complex.normSq_eq_norm_sq, hvre, hvim]
    nth_rewrite 1 [← Complex.norm_mul_cos_arg u]
    nth_rewrite 1 [← Complex.norm_mul_sin_arg u]
    ring
  have hX : 0 < L * Real.cos u.arg + u.arg * Real.sin u.arg := by
    linarith [Real.pi_pos]
  have hpos : 0 < (u / Complex.log u).re := by
    rw [hre]; have := norm_pos_iff.mpr hu0; positivity
  refine ⟨hpos, le_trans ?_ (re_div_norm_le_pi_div_two_sub_abs_arg hpos)⟩
  rw [hre, norm_div]
  have hnu : 0 < ‖u‖ := norm_pos_iff.mpr hu0
  have heq : ‖u‖ * (L * Real.cos u.arg + u.arg * Real.sin u.arg) / ‖Complex.log u‖ ^ 2 /
      (‖u‖ / ‖Complex.log u‖) = (L * Real.cos u.arg + u.arg * Real.sin u.arg) /
        ‖Complex.log u‖ := by
    field_simp
  rw [heq]
  calc π / 2 / (L + 2) ≤ π / 2 / ‖Complex.log u‖ :=
        div_le_div_of_nonneg_left (by positivity) hnv hnv_le
    _ ≤ _ := div_le_div_of_nonneg_right hkey hnv.le

/-! ## Circle averages of `|1 - z|^{-γ}`, `γ < 1` -/

theorem norm_one_sub_circleMap_ge {R θ : ℝ} (hR : 1 / 2 ≤ R) (hR1 : R < 1) (h0 : 0 ≤ θ)
    (h2 : θ ≤ 2 * π) :
    (2 * (1 - R) + min θ (2 * π - θ)) / π ≤ ‖1 - circleMap 0 R θ‖ := by
  set u := min θ (2 * π - θ) with hu
  have hu0 : 0 ≤ u := le_min h0 (by linarith)
  have hπ := Real.pi_gt_three
  have hL0 : 0 < (2 * (1 - R) + u) / π := div_pos (by linarith) (by linarith)
  have hsq := norm_one_sub_circleMap_sq R θ
  have hcos := one_sub_cos_ge h0 h2
  refine (pow_le_pow_iff_left₀ hL0.le (norm_nonneg _) two_ne_zero).mp ?_
  rw [hsq, div_pow]
  have hπ2 : 9 < π ^ 2 := by nlinarith
  rw [div_le_iff₀ (by positivity)]
  have h1 : 2 * R * (1 - Real.cos θ) ≥ 2 / π ^ 2 * u ^ 2 := by
    have : 2 / π ^ 2 * u ^ 2 ≤ 2 * R * (2 / π ^ 2 * u ^ 2) := by
      have : 0 ≤ 2 / π ^ 2 * u ^ 2 := by positivity
      nlinarith
    nlinarith
  have h3 : 2 / π ^ 2 * u ^ 2 * π ^ 2 = 2 * u ^ 2 := by field_simp
  nlinarith [sq_nonneg (2 * (1 - R) - u)]

/-- On `|z| = R ≥ 1/2`: `|1 - z|^{-γ} ≤ π((2(1-R) + θ)^{-γ} + (2(1-R) + 2π - θ)^{-γ})`. -/
theorem rpow_neg_norm_one_sub_circleMap_le {γ R θ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1)
    (hR : 1 / 2 ≤ R) (hR1 : R < 1) (h0 : 0 ≤ θ) (h2 : θ ≤ 2 * π) :
    ‖1 - circleMap 0 R θ‖ ^ (-γ) ≤
      π * ((2 * (1 - R) + θ) ^ (-γ) + (2 * (1 - R) + (2 * π - θ)) ^ (-γ)) := by
  set u := min θ (2 * π - θ) with hu
  have hu0 : 0 ≤ u := le_min h0 (by linarith)
  have hπ := Real.pi_gt_three
  have hε : 0 < 2 * (1 - R) := by linarith
  have hL0 : 0 < (2 * (1 - R) + u) / π := div_pos (by linarith) (by linarith)
  have hge := norm_one_sub_circleMap_ge hR hR1 h0 h2
  have h1 : ‖1 - circleMap 0 R θ‖ ^ (-γ) ≤ ((2 * (1 - R) + u) / π) ^ (-γ) :=
    Real.rpow_le_rpow_of_nonpos hL0 hge (by linarith)
  have h2' : ((2 * (1 - R) + u) / π) ^ (-γ) = π ^ γ * (2 * (1 - R) + u) ^ (-γ) := by
    rw [Real.div_rpow (by linarith) (by linarith), Real.rpow_neg (by linarith : (0 : ℝ) ≤ π)]
    field_simp
  have hπγ : π ^ γ ≤ π := by
    calc π ^ γ ≤ π ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) hγ1
      _ = π := Real.rpow_one π
  have hA : 0 ≤ (2 * (1 - R) + θ) ^ (-γ) := Real.rpow_nonneg (by linarith) _
  have hB : 0 ≤ (2 * (1 - R) + (2 * π - θ)) ^ (-γ) := Real.rpow_nonneg (by linarith) _
  have hu' : (2 * (1 - R) + u) ^ (-γ) ≤
      (2 * (1 - R) + θ) ^ (-γ) + (2 * (1 - R) + (2 * π - θ)) ^ (-γ) := by
    rcases min_choice θ (2 * π - θ) with h | h <;> rw [hu, h] <;> linarith
  have hC : 0 ≤ (2 * (1 - R) + u) ^ (-γ) := Real.rpow_nonneg (by linarith) _
  calc ‖1 - circleMap 0 R θ‖ ^ (-γ) ≤ π ^ γ * (2 * (1 - R) + u) ^ (-γ) := h1.trans h2'.le
    _ ≤ π * (2 * (1 - R) + u) ^ (-γ) := mul_le_mul_of_nonneg_right hπγ hC
    _ ≤ _ := mul_le_mul_of_nonneg_left hu' (by linarith)

theorem integral_rpow_neg_shift_le {γ ε : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (hε : 0 < ε)
    (hε1 : ε ≤ 1) :
    ∫ θ in (0 : ℝ)..2 * π, (ε + θ) ^ (-γ) ≤ (1 + 2 * π) / (1 - γ) := by
  have h := intervalIntegral.integral_comp_add_left (fun x : ℝ => x ^ (-γ)) ε (a := 0)
    (b := 2 * π)
  simp only [add_zero] at h
  rw [h, integral_rpow (Or.inl (by linarith)), show -γ + 1 = 1 - γ by ring]
  have hπ := Real.pi_gt_three
  have h1γ : 0 < 1 - γ := by linarith
  have hb : (ε + 2 * π) ^ (1 - γ) ≤ 1 + 2 * π := by
    calc (ε + 2 * π) ^ (1 - γ) ≤ (ε + 2 * π) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
      _ ≤ 1 + 2 * π := by rw [Real.rpow_one]; linarith
  have ha : 0 ≤ ε ^ (1 - γ) := Real.rpow_nonneg hε.le _
  rw [div_le_div_iff_of_pos_right h1γ]
  linarith

theorem integral_rpow_neg_shift_reflect_le {γ ε : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (hε : 0 < ε)
    (hε1 : ε ≤ 1) :
    ∫ θ in (0 : ℝ)..2 * π, (ε + (2 * π - θ)) ^ (-γ) ≤ (1 + 2 * π) / (1 - γ) := by
  have h := intervalIntegral.integral_comp_sub_left (fun x : ℝ => (ε + x) ^ (-γ)) (2 * π)
    (a := 0) (b := 2 * π)
  simp only [sub_zero, sub_self] at h
  rw [h]
  exact integral_rpow_neg_shift_le hγ0 hγ1 hε hε1

/-- **Bounded circle averages.**  `avg_{|z| = R} |1 - z|^{-γ} ≤ (1 + 2π)/(1 - γ)` for `0 ≤ γ < 1`
and `1/2 ≤ R < 1`, uniformly in `R`. -/
theorem circleAverage_rpow_neg_norm_one_sub_le {γ R : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (hR : 1 / 2 ≤ R) (hR1 : R < 1) :
    Real.circleAverage (fun z => ‖1 - z‖ ^ (-γ)) 0 R ≤ (1 + 2 * π) / (1 - γ) := by
  set ε := 2 * (1 - R) with hε
  have hε0 : 0 < ε := by rw [hε]; linarith
  have hε1 : ε ≤ 1 := by rw [hε]; linarith
  have hπ := Real.pi_gt_three
  have hne : ∀ θ : ℝ, 1 - circleMap 0 R θ ≠ 0 := by
    intro θ h
    have : circleMap 0 R θ = 1 := by linear_combination -h
    have hn := norm_circleMap_zero R θ
    rw [this, norm_one, abs_of_pos (by linarith)] at hn
    linarith
  have hi1 : IntervalIntegrable (fun θ => ‖1 - circleMap 0 R θ‖ ^ (-γ)) volume 0 (2 * π) := by
    refine Continuous.intervalIntegrable ?_ _ _
    exact Continuous.rpow_const (continuous_const.sub (continuous_circleMap 0 R)).norm
      fun θ => Or.inl (norm_ne_zero_iff.mpr (hne θ))
  have hcA : ContinuousOn (fun θ : ℝ => (ε + θ) ^ (-γ)) (uIcc 0 (2 * π)) := by
    refine ContinuousOn.rpow_const (f := fun θ : ℝ => ε + θ) (by fun_prop) fun θ hθ => Or.inl ?_
    rw [uIcc_of_le (by positivity)] at hθ; show ε + θ ≠ 0; linarith [hθ.1]
  have hcB : ContinuousOn (fun θ : ℝ => (ε + (2 * π - θ)) ^ (-γ)) (uIcc 0 (2 * π)) := by
    refine ContinuousOn.rpow_const (f := fun θ : ℝ => ε + (2 * π - θ)) (by fun_prop)
      fun θ hθ => Or.inl ?_
    rw [uIcc_of_le (by positivity)] at hθ; show ε + (2 * π - θ) ≠ 0; linarith [hθ.2]
  have hi2 : IntervalIntegrable (fun θ => π * ((ε + θ) ^ (-γ) + (ε + (2 * π - θ)) ^ (-γ)))
      volume 0 (2 * π) :=
    ((hcA.intervalIntegrable).add (hcB.intervalIntegrable)).const_mul π
  have hmono := intervalIntegral.integral_mono_on Real.two_pi_pos.le hi1 hi2 fun θ hθ =>
    rpow_neg_norm_one_sub_circleMap_le hγ0 hγ1.le hR hR1 hθ.1 hθ.2
  have hI : ∫ θ in (0 : ℝ)..2 * π, π * ((ε + θ) ^ (-γ) + (ε + (2 * π - θ)) ^ (-γ)) ≤
      π * (2 * ((1 + 2 * π) / (1 - γ))) := by
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_add hcA.intervalIntegrable hcB.intervalIntegrable]
    have := integral_rpow_neg_shift_le hγ0 hγ1 hε0 hε1
    have := integral_rpow_neg_shift_reflect_le hγ0 hγ1 hε0 hε1
    have hπ0 : 0 ≤ π := by linarith
    nlinarith
  rw [Real.circleAverage_def, smul_eq_mul]
  calc (2 * π)⁻¹ * ∫ θ in (0 : ℝ)..2 * π, ‖1 - circleMap 0 R θ‖ ^ (-γ)
      ≤ (2 * π)⁻¹ * (π * (2 * ((1 + 2 * π) / (1 - γ)))) :=
        mul_le_mul_of_nonneg_left (hmono.trans hI) (by positivity)
    _ = (1 + 2 * π) / (1 - γ) := by field_simp

/-! ## Jensen's formula with bounded circle averages -/

/-- **Blaschke condition from bounded circle averages.**  If `f` is analytic on the unit disc, not
identically zero, with `avg_{|z| = R} log |f| ≤ B` for `1/2 ≤ R < 1`, then its zeros `a n`
(`n ∈ N`, injective, nonzero) satisfy `Σ_{n ∈ N} log(1/|a n|) < ∞`. -/
theorem summable_log_inv_of_circleAverage_le {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f (ball 0 1))
    {B : ℝ} (havg : ∀ R : ℝ, 1 / 2 ≤ R → R < 1 →
      Real.circleAverage (fun z => Real.log ‖f z‖) 0 R ≤ B)
    (hne : ∃ z ∈ ball (0 : ℂ) 1, f z ≠ 0) {a : ℕ → ℂ} {N : Set ℕ} (hinj : Set.InjOn a N)
    (ha : ∀ n ∈ N, ‖a n‖ < 1 ∧ a n ≠ 0 ∧ f (a n) = 0) :
    Summable (N.indicator fun n => Real.log ‖a n‖⁻¹) := by
  classical
  have hconn : IsConnected (ball (0 : ℂ) 1) := (convex_ball 0 1).isConnected (by simp)
  obtain ⟨z₀, hz₀, hfz₀⟩ := hne
  have hord : ∀ u ∈ ball (0 : ℂ) 1, analyticOrderAt f u ≠ ⊤ := by
    have h0 : analyticOrderAt f z₀ ≠ ⊤ := by
      rw [(hf z₀ hz₀).analyticOrderAt_eq_zero.mpr hfz₀]; exact ENat.zero_ne_top
    intro u hu
    exact (hf.exists_analyticOrderAt_ne_top_iff_forall hconn).mp ⟨⟨z₀, hz₀⟩, h0⟩ ⟨u, hu⟩
  have h0ball : (0 : ℂ) ∈ ball (0 : ℂ) 1 := by simp
  obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp (hord 0 h0ball)
  have hdiv0 : ∀ R : ℝ, 0 < R → R < 1 →
      (MeromorphicOn.divisor f (closedBall 0 |R|) 0 : ℝ) = k := by
    intro R hR0 hR1
    rw [MeromorphicOn.AnalyticOnNhd.divisor_apply (hf.mono (by
        rw [abs_of_pos hR0]; exact closedBall_subset_ball hR1)) (by simp), ← hk]
    simp
  set C := B + k * Real.log 2 - Real.log ‖meromorphicTrailingCoeffAt f 0‖ + 1 with hC
  have hpartial : ∀ S : Finset ℕ, (∀ n ∈ S, n ∈ N) →
      ∑ n ∈ S, Real.log (‖a n‖⁻¹) ≤ max C 0 := by
    intro S hS
    rcases S.eq_empty_or_nonempty with hSe | hSne
    · rw [hSe, Finset.sum_empty]; exact le_max_right _ _
    obtain ⟨n₁, hn₁, hmax⟩ := S.exists_max_image (fun n => ‖a n‖) hSne
    set R : ℝ := max (max (1 / 2) (Real.exp (-(1 / ((S.card : ℝ) + 1))))) ‖a n₁‖ with hR
    have hRhalf : 1 / 2 ≤ R := le_trans (le_max_left _ _) (le_max_left _ _)
    have hRexp : Real.exp (-(1 / ((S.card : ℝ) + 1))) ≤ R :=
      le_trans (le_max_right _ _) (le_max_left _ _)
    have hR0 : 0 < R := lt_of_lt_of_le (by norm_num) hRhalf
    have hR1 : R < 1 := by
      refine max_lt (max_lt (by norm_num) ?_) (ha n₁ (hS n₁ hn₁)).1
      have : (0 : ℝ) < 1 / ((S.card : ℝ) + 1) := by positivity
      have h := Real.exp_lt_exp.mpr (show -(1 / ((S.card : ℝ) + 1)) < 0 by linarith)
      rwa [Real.exp_zero] at h
    have hT : ∀ u ∈ S.image a, ‖u‖ ≤ R ∧ u ≠ 0 ∧ f u = 0 := by
      intro u hu
      obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hu
      obtain ⟨-, han0, hfan⟩ := ha n (hS n hn)
      exact ⟨(hmax n hn).trans (le_max_right _ _), han0, hfan⟩
    have hJ := sum_log_le_of_circleAverage_le hf hord hR0 hR1 (havg R hRhalf hR1) _ hT
    rw [hdiv0 R hR0 hR1, Finset.sum_image (fun x hx y hy h => hinj (hS x hx) (hS y hy) h)] at hJ
    have hsplit : ∑ n ∈ S, Real.log (R * ‖a n‖⁻¹) =
        S.card * Real.log R + ∑ n ∈ S, Real.log (‖a n‖⁻¹) := by
      rw [Finset.sum_congr rfl (fun n hn => Real.log_mul hR0.ne'
        (inv_ne_zero (norm_ne_zero_iff.mpr (ha n (hS n hn)).2.1))),
        Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
    have hlogR : -1 ≤ (S.card : ℝ) * Real.log R := by
      have h1 : -(1 / ((S.card : ℝ) + 1)) ≤ Real.log R := by
        rw [← Real.log_exp (-(1 / ((S.card : ℝ) + 1)))]
        exact Real.log_le_log (Real.exp_pos _) hRexp
      have hc : (0 : ℝ) ≤ S.card := Nat.cast_nonneg _
      have h2 : (S.card : ℝ) * (1 / ((S.card : ℝ) + 1)) ≤ 1 := by
        rw [mul_one_div, div_le_one (by positivity)]; linarith
      nlinarith
    have hklog : -((k : ℝ) * Real.log R) ≤ k * Real.log 2 := by
      have h1 : -Real.log 2 ≤ Real.log R := by
        rw [← Real.log_inv, show (2 : ℝ)⁻¹ = 1 / 2 by norm_num]
        exact Real.log_le_log (by norm_num) hRhalf
      have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg _
      nlinarith
    have : ∑ n ∈ S, Real.log (‖a n‖⁻¹) ≤ C := by rw [hC]; linarith
    exact this.trans (le_max_left _ _)
  have hnn : 0 ≤ N.indicator (fun n => Real.log ‖a n‖⁻¹) := by
    intro n
    by_cases hn : n ∈ N
    · rw [Set.indicator_of_mem hn]
      have h2 := norm_pos_iff.mpr (ha n hn).2.1
      exact Real.log_nonneg ((one_le_inv₀ h2).mpr (ha n hn).1.le)
    · simp [hn]
  refine summable_of_sum_le (c := max C 0) hnn fun s => ?_
  have : ∑ n ∈ s, N.indicator (fun n : ℕ => Real.log (‖a n‖⁻¹)) n =
      ∑ n ∈ s.filter (· ∈ N), Real.log (‖a n‖⁻¹) := by
    rw [Finset.sum_filter]
    exact Finset.sum_congr rfl fun n _ => by simp [Set.indicator_apply]
  rw [this]
  exact hpartial _ fun n hn => (Finset.mem_filter.mp hn).2

/-! ## Real disc nodes and preimages under `x / log x` -/

/-- The disc point corresponding to a real `y` under `ζ = (1+z)/(1-z)`. -/
def realNode (y : ℝ) : ℂ := ((y : ℂ) - 1) / ((y : ℂ) + 1)

theorem realNode_eq_ofReal (y : ℝ) : realNode y = (((y - 1) / (y + 1) : ℝ) : ℂ) := by
  unfold realNode; push_cast; rfl

theorem norm_realNode {y : ℝ} (hy : 1 ≤ y) : ‖realNode y‖ = (y - 1) / (y + 1) := by
  rw [realNode_eq_ofReal, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
  exact div_nonneg (by linarith) (by linarith)

theorem norm_realNode_lt_one {y : ℝ} (hy : 1 ≤ y) : ‖realNode y‖ < 1 := by
  rw [norm_realNode hy, div_lt_one (by linarith)]; linarith

theorem realNode_ne_zero {y : ℝ} (hy : 1 < y) : realNode y ≠ 0 := by
  intro h
  have := norm_realNode hy.le
  rw [h, norm_zero] at this
  have : (y - 1) / (y + 1) > 0 := div_pos (by linarith) (by linarith)
  linarith

theorem cayley_realNode {y : ℝ} (hy : 0 < y) : cayley (realNode y) = y := by
  unfold cayley realNode
  have h1 : (y : ℂ) + 1 ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  have h2 : (1 : ℂ) - ((y : ℂ) - 1) / ((y : ℂ) + 1) ≠ 0 := by
    rw [show (1 : ℂ) - ((y : ℂ) - 1) / ((y : ℂ) + 1) = 2 / ((y : ℂ) + 1) by field_simp; ring]
    exact div_ne_zero two_ne_zero h1
  field_simp
  ring

/-- `log((y+1)/(y-1)) ≥ 2/(y+1)` for `y > 1`. -/
theorem two_div_le_log_inv_realNode {y : ℝ} (hy : 1 < y) :
    2 / (y + 1) ≤ Real.log (‖realNode y‖⁻¹) := by
  rw [norm_realNode hy.le, inv_div]
  have hpos : 0 < (y + 1) / (y - 1) := div_pos (by linarith) (by linarith)
  have hl := Real.one_sub_inv_le_log_of_pos hpos
  rw [inv_div] at hl
  have : 1 - (y - 1) / (y + 1) = 2 / (y + 1) := by field_simp; ring
  linarith

theorem two_mul_log_le_self {v : ℝ} (hv : 0 < v) : 2 * Real.log v ≤ v := by
  have h := Real.log_le_sub_one_of_pos (half_pos hv)
  have h2 : Real.log v = Real.log 2 + Real.log (v / 2) := by
    rw [← Real.log_mul (by norm_num) (by positivity)]; ring_nf
  have := Real.log_two_lt_d9
  linarith

/-- Every `v ≥ W + 2` is `x / log x` for some `x ∈ [W + 2, v²]`. -/
theorem exists_div_log_eq {W v : ℝ} (hW : 1 ≤ W) (hv : W + 2 ≤ v) :
    ∃ x, W + 2 ≤ x ∧ x ≤ v ^ 2 ∧ x / Real.log x = v := by
  have hv3 : 3 ≤ v := by linarith
  have hab : W + 2 ≤ v ^ 2 := by nlinarith
  have hlogpos : ∀ x ∈ Icc (W + 2) (v ^ 2), 0 < Real.log x :=
    fun x hx => Real.log_pos (by linarith [hx.1])
  have hcont : ContinuousOn (fun x => x / Real.log x) (Icc (W + 2) (v ^ 2)) :=
    continuousOn_id.div (Real.continuousOn_log.mono fun x hx => by
      simp only [mem_compl_iff, mem_singleton_iff]; linarith [hx.1])
      fun x hx => (hlogpos x hx).ne'
  have hlo : (W + 2) / Real.log (W + 2) ≤ v := by
    have h1 : 1 ≤ Real.log (W + 2) := by
      rw [Real.le_log_iff_exp_le (by linarith)]; have := Real.exp_one_lt_d9; linarith
    calc (W + 2) / Real.log (W + 2) ≤ W + 2 := div_le_self (by linarith) h1
      _ ≤ v := hv
  have hhi : v ≤ v ^ 2 / Real.log (v ^ 2) := by
    have hlv : 0 < Real.log v := Real.log_pos (by linarith)
    rw [Real.log_pow, le_div_iff₀ (by positivity)]
    have := two_mul_log_le_self (by linarith : 0 < v)
    push_cast; nlinarith
  obtain ⟨x, hx, hxv⟩ := intermediate_value_Icc hab hcont ⟨hlo, hhi⟩
  exact ⟨x, hx.1, hx.2, hxv⟩

/-! ## The logarithmic Carlson threshold -/

/-- `log(1 + x) ≤ 2√x` for `x ≥ 0`. -/
theorem log_one_add_le_two_mul_sqrt {x : ℝ} (hx : 0 ≤ x) :
    Real.log (1 + x) ≤ 2 * Real.sqrt x := by
  set s := Real.sqrt x with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg x
  have hx' : x = s ^ 2 := (Real.sq_sqrt hx).symm
  have h1 : 1 + x ≤ (1 + s) ^ 2 := by rw [hx']; nlinarith
  calc Real.log (1 + x) ≤ Real.log ((1 + s) ^ 2) := Real.log_le_log (by positivity) h1
    _ = 2 * Real.log (1 + s) := by rw [Real.log_pow]; push_cast; ring
    _ ≤ 2 * s := by
        have := Real.log_le_sub_one_of_pos (show 0 < 1 + s by linarith)
        linarith

/-- **Logarithmic Carlson threshold for analytic functions.**  Let `G` be analytic on `Re ζ > 0`
with `|G(ζ)| ≤ A e^{K e^{K/(π/2 - |arg ζ|)}} (1 + |ζ|)^c` for some `0 ≤ K < π/2`, and let `G`
vanish on a set `N ⊆ [2, ∞)` with `Σ_{n ∈ N} 1/(n log n) = ∞`.  Then `G ≡ 0`.

`G` is composed with `Ψ(z) = u/log u`, `u = e⁴ + (1+z)/(1-z)`.  The narrowing keeps `Ψ(z)` at angle
`≥ (π/2)/(log|u| + 2)` from the imaginary axis, so `log |G(Ψ(z))| ≤ log A + D |1-z|^{-2K/π} +
D' |1-z|^{-1/2}`, whose circle averages are bounded because `2K/π < 1`.  The node `n` has the real
preimage `x_n ∈ [e⁴+2, n²]` with `x_n/log x_n = n`; its disc distance is `≍ 1/(n log n)`, so the
Blaschke condition fails. -/
theorem eqOn_zero_of_logRoom_growth {G : ℂ → ℂ} (hG : AnalyticOnNhd ℂ G rightHalf) {K A : ℝ}
    (c : ℕ) (hK0 : 0 ≤ K) (hK : K < π / 2)
    (hgrowth : ∀ ζ : ℂ, 0 < ζ.re →
      ‖G ζ‖ ≤ A * Real.exp (K * Real.exp (K / (π / 2 - |ζ.arg|))) * (1 + ‖ζ‖) ^ c)
    {N : Set ℕ} (hN2 : ∀ n ∈ N, 2 ≤ n)
    (hdiv : ¬ Summable (N.indicator fun n : ℕ => 1 / ((n : ℝ) * Real.log n)))
    (hz : ∀ n ∈ N, G n = 0) : EqOn G 0 rightHalf := by
  classical
  set W : ℝ := Real.exp 4 with hW
  have hW1 : 1 ≤ W := Real.one_le_exp (by norm_num)
  have hπ := Real.pi_gt_three
  -- the narrowing map `Ψ(z) = u/log u`, `u = W + (1+z)/(1-z)`
  set u : ℂ → ℂ := fun z => (W : ℂ) + cayley z with hu
  set Ψ : ℂ → ℂ := fun z => u z / Complex.log (u z) with hΨ
  have hure : ∀ z : ℂ, ‖z‖ < 1 → W < (u z).re := fun z hz => by
    simp only [hu, Complex.add_re, Complex.ofReal_re]; linarith [re_cayley_pos hz]
  have hulog : ∀ z : ℂ, ‖z‖ < 1 → 4 ≤ Real.log ‖u z‖ := fun z hz => by
    have h1 : W ≤ ‖u z‖ := (hure z hz).le.trans (Complex.re_le_norm _)
    calc (4 : ℝ) = Real.log W := by rw [hW, Real.log_exp]
      _ ≤ _ := Real.log_le_log (Real.exp_pos 4) h1
  have hΨmem : ∀ z : ℂ, ‖z‖ < 1 → 0 < (Ψ z).re ∧
      π / 2 / (Real.log ‖u z‖ + 2) ≤ π / 2 - |(Ψ z).arg| :=
    fun z hz => re_div_log_pos_and_le (by linarith [hure z hz]) (hulog z hz)
  have hlogne : ∀ z : ℂ, ‖z‖ < 1 → Complex.log (u z) ≠ 0 := fun z hz h => by
    have h4 := hulog z hz
    have h2 : (Complex.log (u z)).re = Real.log ‖u z‖ := Complex.log_re _
    rw [h, Complex.zero_re] at h2; linarith
  set f : ℂ → ℂ := fun z => G (Ψ z) with hf
  have hfan : AnalyticOnNhd ℂ f (ball 0 1) := by
    intro z hz1
    have hz1' : ‖z‖ < 1 := by simpa using hz1
    have hc : AnalyticAt ℂ u z :=
      analyticAt_const.add ((analyticAt_const.add analyticAt_id).div
        (analyticAt_const.sub analyticAt_id) (one_sub_ne_zero_of_norm_lt hz1'))
    have hslit : u z ∈ Complex.slitPlane :=
      Complex.mem_slitPlane_iff.mpr (Or.inl (by linarith [hure z hz1']))
    have hΨa : AnalyticAt ℂ Ψ z := hc.div (hc.clog hslit) (hlogne z hz1')
    exact AnalyticAt.comp (g := G) (f := Ψ) (hG _ (hΨmem z hz1').1) hΨa
  -- growth on circles
  set γ : ℝ := 2 * K / π with hγ
  have hγ0 : 0 ≤ γ := by positivity
  have hγ1 : γ < 1 := by rw [hγ, div_lt_one (by positivity)]; linarith
  set A' := max A 1 with hA
  have hA1 : 1 ≤ A' := le_max_right _ _
  set D := K * Real.exp (2 * γ) * (2 * (W + 1)) ^ γ with hD
  have hD0 : 0 ≤ D := by positivity
  set D₂ := 2 * c * Real.sqrt (2 * (W + 1)) with hD₂
  have hD₂0 : 0 ≤ D₂ := by positivity
  have hpt : ∀ z : ℂ, ‖z‖ < 1 → Real.log ‖f z‖ ≤
      Real.log A' + D * ‖1 - z‖ ^ (-γ) + D₂ * ‖1 - z‖ ^ (-(1 / 2 : ℝ)) := by
    intro z hz
    have hlogA : 0 ≤ Real.log A' := Real.log_nonneg hA1
    have hn1 : 0 < ‖1 - z‖ := norm_pos_iff.mpr (one_sub_ne_zero_of_norm_lt hz)
    have hrest : 0 ≤ D * ‖1 - z‖ ^ (-γ) := mul_nonneg hD0 (Real.rpow_nonneg hn1.le _)
    have hrest₂ : 0 ≤ D₂ * ‖1 - z‖ ^ (-(1 / 2 : ℝ)) :=
      mul_nonneg hD₂0 (Real.rpow_nonneg hn1.le _)
    rcases eq_or_ne (f z) 0 with h0 | h0
    · rw [h0, norm_zero, Real.log_zero]; linarith
    obtain ⟨hre, hδ⟩ := hΨmem z hz
    set L := Real.log ‖u z‖ with hL
    set δ := π / 2 - |(Ψ z).arg| with hδdef
    have hL4 := hulog z hz
    have hδ0 : 0 < π / 2 / (L + 2) := by
      have : 0 < L + 2 := by linarith
      positivity
    have hδpos : 0 < δ := lt_of_lt_of_le hδ0 hδ
    have hKδ : K / δ ≤ γ * (L + 2) := by
      calc K / δ ≤ K / (π / 2 / (L + 2)) := div_le_div_of_nonneg_left hK0 hδ0 hδ
        _ = γ * (L + 2) := by rw [hγ]; field_simp
    have hnu : 0 < ‖u z‖ := lt_of_lt_of_le (by linarith [hure z hz]) (Complex.re_le_norm _)
    have hexp : Real.exp (K / δ) ≤ Real.exp (2 * γ) * ‖u z‖ ^ γ := by
      rw [Real.rpow_def_of_pos hnu, ← Real.exp_add, ← hL]
      refine Real.exp_le_exp.mpr ?_
      have : γ * (L + 2) = 2 * γ + L * γ := by ring
      linarith
    have hcay : ‖cayley z‖ ≤ 2 * ‖1 - z‖⁻¹ := by
      rw [cayley, norm_div, div_eq_mul_inv]
      refine mul_le_mul_of_nonneg_right ?_ (by positivity)
      exact (norm_add_le _ _).trans (by rw [norm_one]; linarith)
    have hn12 : ‖1 - z‖ ≤ 2 := (norm_sub_le _ _).trans (by rw [norm_one]; linarith)
    have hinv : 1 / 2 ≤ ‖1 - z‖⁻¹ := by
      rw [one_div]; exact inv_anti₀ hn1 hn12
    have hnorm : ‖u z‖ ≤ 2 * (W + 1) * ‖1 - z‖⁻¹ := by
      have h1 : ‖u z‖ ≤ W + 2 * ‖1 - z‖⁻¹ := by
        refine (norm_add_le _ _).trans ?_
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]; linarith
      nlinarith
    have hpow : ‖u z‖ ^ γ ≤ (2 * (W + 1)) ^ γ * ‖1 - z‖ ^ (-γ) := by
      calc ‖u z‖ ^ γ ≤ (2 * (W + 1) * ‖1 - z‖⁻¹) ^ γ :=
            Real.rpow_le_rpow hnu.le hnorm hγ0
        _ = (2 * (W + 1)) ^ γ * ‖1 - z‖ ^ (-γ) := by
            rw [Real.mul_rpow (by positivity) (by positivity), Real.inv_rpow hn1.le,
              Real.rpow_neg hn1.le]
    -- the polynomial factor
    have hlogu1 : 1 ≤ ‖Complex.log (u z)‖ := by
      have h2 : (Complex.log (u z)).re = L := Complex.log_re _
      have := Complex.re_le_norm (Complex.log (u z))
      linarith
    have hΨnorm : ‖Ψ z‖ ≤ ‖u z‖ := by
      show ‖u z / Complex.log (u z)‖ ≤ ‖u z‖
      rw [norm_div]
      exact div_le_self (norm_nonneg _) hlogu1
    have hsqrt : Real.sqrt ‖u z‖ ≤ Real.sqrt (2 * (W + 1)) * ‖1 - z‖ ^ (-(1 / 2 : ℝ)) := by
      calc Real.sqrt ‖u z‖ ≤ Real.sqrt (2 * (W + 1) * ‖1 - z‖⁻¹) := Real.sqrt_le_sqrt hnorm
        _ = Real.sqrt (2 * (W + 1)) * ‖1 - z‖ ^ (-(1 / 2 : ℝ)) := by
            rw [Real.sqrt_mul (by positivity), Real.sqrt_eq_rpow, Real.sqrt_eq_rpow,
              Real.inv_rpow hn1.le, Real.rpow_neg hn1.le]
    have hpoly : (c : ℝ) * Real.log (1 + ‖Ψ z‖) ≤ D₂ * ‖1 - z‖ ^ (-(1 / 2 : ℝ)) := by
      have h1 := log_one_add_le_two_mul_sqrt (norm_nonneg (Ψ z))
      have h2 : Real.sqrt ‖Ψ z‖ ≤ Real.sqrt ‖u z‖ := Real.sqrt_le_sqrt hΨnorm
      have hc0 : (0 : ℝ) ≤ c := Nat.cast_nonneg c
      calc (c : ℝ) * Real.log (1 + ‖Ψ z‖) ≤ c * (2 * Real.sqrt ‖u z‖) := by
            gcongr; linarith
        _ ≤ c * (2 * (Real.sqrt (2 * (W + 1)) * ‖1 - z‖ ^ (-(1 / 2 : ℝ)))) := by gcongr
        _ = D₂ * ‖1 - z‖ ^ (-(1 / 2 : ℝ)) := by rw [hD₂]; ring
    have hbound := hgrowth (Ψ z) hre
    have hbound' : ‖f z‖ ≤ A' * Real.exp (K * Real.exp (K / δ)) * (1 + ‖Ψ z‖) ^ c :=
      hbound.trans (by gcongr; exact le_max_left _ _)
    calc Real.log ‖f z‖ ≤ Real.log (A' * Real.exp (K * Real.exp (K / δ)) * (1 + ‖Ψ z‖) ^ c) :=
          Real.log_le_log (norm_pos_iff.mpr h0) hbound'
      _ = Real.log A' + K * Real.exp (K / δ) + c * Real.log (1 + ‖Ψ z‖) := by
          rw [Real.log_mul (by positivity) (by positivity),
            Real.log_mul (by positivity) (Real.exp_pos _).ne', Real.log_exp, Real.log_pow]
      _ ≤ Real.log A' + K * (Real.exp (2 * γ) * ((2 * (W + 1)) ^ γ * ‖1 - z‖ ^ (-γ))) +
          D₂ * ‖1 - z‖ ^ (-(1 / 2 : ℝ)) := by
          gcongr
          exact hexp.trans (mul_le_mul_of_nonneg_left hpow (Real.exp_pos _).le)
      _ = Real.log A' + D * ‖1 - z‖ ^ (-γ) + D₂ * ‖1 - z‖ ^ (-(1 / 2 : ℝ)) := by rw [hD]; ring
  have havg : ∀ R : ℝ, 1 / 2 ≤ R → R < 1 →
      Real.circleAverage (fun z => Real.log ‖f z‖) 0 R ≤
        Real.log A' + D * ((1 + 2 * π) / (1 - γ)) + D₂ * ((1 + 2 * π) / (1 - 1 / 2)) := by
    intro R hR hR1
    have hR0 : 0 < R := by linarith
    have hRabs : |R| = R := abs_of_pos hR0
    have hsph : sphere (0 : ℂ) |R| ⊆ ball 0 1 := by rw [hRabs]; exact sphere_subset_ball hR1
    have hcf : CircleIntegrable (fun z => Real.log ‖f z‖) 0 R :=
      (hfan.mono hsph).meromorphicOn.circleIntegrable_log_norm
    have hcg : ∀ e : ℝ, CircleIntegrable (fun z : ℂ => ‖1 - z‖ ^ (-e)) 0 R := by
      intro e
      refine ContinuousOn.circleIntegrable hR0.le ?_
      refine ContinuousOn.rpow_const (f := fun z : ℂ => ‖1 - z‖) (by fun_prop)
        fun z hz => Or.inl ?_
      rw [mem_sphere_zero_iff_norm] at hz
      refine norm_ne_zero_iff.mpr fun h => ?_
      have : z = 1 := by linear_combination -h
      rw [this, norm_one] at hz; linarith
    have hsum : (fun z : ℂ => Real.log A' + D * ‖1 - z‖ ^ (-γ) +
        D₂ * ‖1 - z‖ ^ (-(1 / 2 : ℝ))) = ((fun _ => Real.log A') +
          D • (fun z : ℂ => ‖1 - z‖ ^ (-γ))) + D₂ • (fun z : ℂ => ‖1 - z‖ ^ (-(1 / 2 : ℝ))) := by
      funext z; simp [smul_eq_mul]
    have hc1 : CircleIntegrable ((fun _ => Real.log A') +
        D • (fun z : ℂ => ‖1 - z‖ ^ (-γ))) 0 R :=
      (circleIntegrable_const _ 0 R).add (hcg γ).const_smul
    have hcs : CircleIntegrable (fun z : ℂ => Real.log A' + D * ‖1 - z‖ ^ (-γ) +
        D₂ * ‖1 - z‖ ^ (-(1 / 2 : ℝ))) 0 R := by
      rw [hsum]; exact hc1.add (hcg (1 / 2)).const_smul
    have hmono := Real.circleAverage_mono hcf hcs fun z hz => hpt z (by
      rw [hRabs, mem_sphere_zero_iff_norm] at hz; rw [hz]; exact hR1)
    have havg' : Real.circleAverage (fun z : ℂ => Real.log A' + D * ‖1 - z‖ ^ (-γ) +
        D₂ * ‖1 - z‖ ^ (-(1 / 2 : ℝ))) 0 R =
        Real.log A' + D * Real.circleAverage (fun z : ℂ => ‖1 - z‖ ^ (-γ)) 0 R +
          D₂ * Real.circleAverage (fun z : ℂ => ‖1 - z‖ ^ (-(1 / 2 : ℝ))) 0 R := by
      rw [hsum, Real.circleAverage_add hc1 (hcg (1 / 2)).const_smul,
        Real.circleAverage_add (circleIntegrable_const _ 0 R) (hcg γ).const_smul,
        Real.circleAverage_const, Real.circleAverage_smul, Real.circleAverage_smul,
        smul_eq_mul, smul_eq_mul]
    rw [havg'] at hmono
    have h1 := mul_le_mul_of_nonneg_left
      (circleAverage_rpow_neg_norm_one_sub_le hγ0 hγ1 hR hR1) hD0
    have h2 := mul_le_mul_of_nonneg_left
      (circleAverage_rpow_neg_norm_one_sub_le (γ := 1 / 2) (by norm_num) (by norm_num) hR hR1)
      hD₂0
    linarith
  -- the narrowing on the real axis
  have hΨnode : ∀ y : ℝ, W + 2 ≤ y → Ψ (realNode (y - W)) = ((y / Real.log y : ℝ) : ℂ) := by
    intro y hy
    have hy0 : 0 < y - W := by linarith
    have hu' : u (realNode (y - W)) = (y : ℂ) := by
      simp only [hu, cayley_realNode hy0]; push_cast; ring
    show u (realNode (y - W)) / Complex.log (u (realNode (y - W))) = _
    rw [hu', ← Complex.ofReal_log (by linarith), ← Complex.ofReal_div]
  -- the nodes `x_n / log x_n = n`
  have hex : ∀ n : ℕ, W + 2 ≤ (n : ℝ) →
      ∃ y, W + 2 ≤ y ∧ y ≤ (n : ℝ) ^ 2 ∧ y / Real.log y = n :=
    fun n hn => exists_div_log_eq hW1 hn
  set xs : ℕ → ℝ := fun n =>
    if h : W + 2 ≤ (n : ℝ) then Classical.choose (hex n h) else 0 with hxs
  have hxs_spec : ∀ n : ℕ, W + 2 ≤ (n : ℝ) →
      W + 2 ≤ xs n ∧ xs n ≤ (n : ℝ) ^ 2 ∧ xs n / Real.log (xs n) = n := by
    intro n hn
    simp only [hxs, dif_pos hn]
    exact Classical.choose_spec (hex n hn)
  set a : ℕ → ℂ := fun n => realNode (xs n - W) with ha
  set N' : Set ℕ := {n | n ∈ N ∧ W + 2 ≤ (n : ℝ)} with hN'
  have hnodes : ∀ n ∈ N', ‖a n‖ < 1 ∧ a n ≠ 0 ∧ f (a n) = 0 := by
    intro n hn
    obtain ⟨h1, -, h3⟩ := hxs_spec n hn.2
    refine ⟨norm_realNode_lt_one (by linarith), realNode_ne_zero (by linarith), ?_⟩
    show G (Ψ (realNode (xs n - W))) = 0
    rw [hΨnode _ h1, h3, Complex.ofReal_natCast]
    exact hz n hn.1
  have hinj : Set.InjOn a N' := by
    intro m hm n hn hmn
    have hm1 := (hxs_spec m hm.2).1
    have hn1 := (hxs_spec n hn.2).1
    have h := congrArg cayley hmn
    simp only [ha, cayley_realNode (by linarith : 0 < xs m - W),
      cayley_realNode (by linarith : 0 < xs n - W)] at h
    have hx : xs m = xs n := by have := Complex.ofReal_injective h; linarith
    have hm3 := (hxs_spec m hm.2).2.2
    have hn3 := (hxs_spec n hn.2).2.2
    rw [hx] at hm3
    exact_mod_cast hm3.symm.trans hn3
  -- `f ≡ 0`
  have hf0 : ∀ z ∈ ball (0 : ℂ) 1, f z = 0 := by
    by_contra hcon
    push Not at hcon
    have hsum := summable_log_inv_of_circleAverage_le hfan havg hcon hinj hnodes
    apply hdiv
    set g : ℕ → ℝ := fun n => 1 / ((n : ℝ) * Real.log n) with hg
    have hgnn : ∀ n ∈ N, 0 ≤ g n := by
      intro n hn
      have h2 : (2 : ℝ) ≤ n := by exact_mod_cast hN2 n hn
      have := Real.log_pos (by linarith : (1 : ℝ) < n)
      simp only [hg]; positivity
    have hle : ∀ n ∈ N', g n ≤ Real.log ‖a n‖⁻¹ := by
      intro n hn
      obtain ⟨h1, h2, h3⟩ := hxs_spec n hn.2
      have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hN2 n hn.1
      have hlogn : 0 < Real.log n := Real.log_pos (by linarith)
      have hxpos : 0 < xs n := by linarith
      have hlogx : 0 < Real.log (xs n) := Real.log_pos (by linarith)
      have hxeq : xs n = n * Real.log (xs n) := by
        field_simp at h3; linarith
      have hlogle : Real.log (xs n) ≤ 2 * Real.log n := by
        calc Real.log (xs n) ≤ Real.log ((n : ℝ) ^ 2) := Real.log_le_log hxpos h2
          _ = 2 * Real.log n := by rw [Real.log_pow]; push_cast; ring
      have hxle : xs n ≤ 2 * (n * Real.log n) := by
        rw [hxeq]; nlinarith
      have hnode := two_div_le_log_inv_realNode (by linarith : 1 < xs n - W)
      have hstep : g n ≤ 2 / (xs n - W + 1) := by
        simp only [hg]
        rw [div_le_div_iff₀ (by positivity) (by linarith)]
        nlinarith
      exact hstep.trans hnode
    have hfin : Summable ((N \ N').indicator g) := by
      refine summable_of_ne_finset_zero (s := Finset.range (⌈W + 2⌉₊)) fun n hn => ?_
      rw [Finset.mem_range, not_lt] at hn
      have hn' : W + 2 ≤ (n : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hn)
      rw [Set.indicator_of_notMem]
      rintro ⟨hnN, hnN'⟩
      exact hnN' ⟨hnN, hn'⟩
    refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) (hsum.add hfin)
    · by_cases hn : n ∈ N
      · rw [Set.indicator_of_mem hn]; exact hgnn n hn
      · simp [hn]
    · by_cases hn : n ∈ N
      · rw [Set.indicator_of_mem hn]
        by_cases hn' : n ∈ N'
        · rw [Set.indicator_of_mem hn', Set.indicator_of_notMem (fun h => h.2 hn')]
          linarith [hle n hn']
        · rw [Set.indicator_of_notMem hn', Set.indicator_of_mem (show n ∈ N \ N' from ⟨hn, hn'⟩), zero_add]
      · rw [Set.indicator_of_notMem hn]
        have h1 : 0 ≤ N'.indicator (fun n => Real.log ‖a n‖⁻¹) n := by
          by_cases hn' : n ∈ N'
          · rw [Set.indicator_of_mem hn']
            exact Real.log_nonneg ((one_le_inv₀ (norm_pos_iff.mpr (hnodes n hn').2.1)).mpr
              (hnodes n hn').1.le)
          · simp [hn']
        have h2 : 0 ≤ (N \ N').indicator g n := by simp [Set.indicator_of_notMem, hn]
        linarith
  -- `G` vanishes on the real ray `[W + 2, ∞)`, hence everywhere
  have hGv : ∀ v : ℝ, W + 2 ≤ v → G (v : ℂ) = 0 := by
    intro v hv
    obtain ⟨y, hy1, -, hyv⟩ := exists_div_log_eq hW1 hv
    have hz : realNode (y - W) ∈ ball (0 : ℂ) 1 := by
      rw [mem_ball_zero_iff]; exact norm_realNode_lt_one (by linarith)
    have h := hf0 _ hz
    simp only [hf] at h
    rwa [hΨnode y hy1, hyv] at h
  show EqOn G 0 rightHalf
  set z₀ : ℂ := ((W + 3 : ℝ) : ℂ) with hz₀def
  have hz₀ : z₀ ∈ rightHalf := by
    show 0 < z₀.re; rw [hz₀def, Complex.ofReal_re]; linarith
  refine hG.eqOn_zero_of_preconnected_of_frequently_eq_zero isPreconnected_rightHalf hz₀ ?_
  have ht : Tendsto (fun k : ℕ => ((W + 3 + 1 / ((k : ℝ) + 1) : ℝ) : ℂ)) atTop (𝓝[≠] z₀) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, Eventually.of_forall fun k => ?_⟩
    · have h := (tendsto_one_div_add_atTop_nhds_zero_nat).const_add (W + 3)
      rw [add_zero] at h
      exact (Complex.continuous_ofReal.tendsto _).comp h
    · simp only [mem_compl_iff, mem_singleton_iff, hz₀def]
      intro h
      have h' := Complex.ofReal_injective h
      have : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
      linarith
  exact ht.frequently (Frequently.of_forall fun k => hGv _ (by
    have : (0 : ℝ) ≤ 1 / ((k : ℝ) + 1) := by positivity
    linarith))

/-- **Integer blindness under logarithmic room.**  Let `0 ≤ K < π/2`, let
`∫ |w(t)| e^{(π/2)|t| - K|t|/log(|t|+3)} dt < ∞`, and let `N ⊆ [2, ∞)` satisfy
`Σ_{n ∈ N} 1/(n log n) = ∞` (for instance all `n ≥ 2`).  If `∫ w(t) n^{-it} dt = 0` for every
`n ∈ N`, the Fourier transform of `w` vanishes. -/
theorem fourier_eq_zero_of_dirichletMoment_eq_zero_logRoom {K : ℝ} (hK0 : 0 ≤ K)
    (hK : K < π / 2) {N : Set ℕ} (hN2 : ∀ n ∈ N, 2 ≤ n)
    (hdiv : ¬ Summable (N.indicator fun n : ℕ => 1 / ((n : ℝ) * Real.log n)))
    (hwm : AEStronglyMeasurable w volume)
    (hroom : Integrable fun t => ‖w t‖ * logRoomWeight K t)
    (hmom : ∀ n ∈ N, ∫ t, w t * cexp (-(I * t) * Real.log n) = 0) (x : ℝ) :
    ∫ t, w t * cexp (-(I * t) * x) = 0 :=
  fourier_eq_zero_of_eqOn (eqOn_zero_of_logRoom_growth
    (analyticOnNhd_logFourier (dominatesSubcritical_logRoomWeight hK0) hwm hroom) 0 hK0 hK
    (fun ζ hζ => by simpa using norm_logFourier_le_logRoom hK0 hroom hζ) hN2 hdiv
    (fun n hn => by rw [logFourier_natCast]; exact hmom n hn)) x

/-- `Σ_{n=2}^{X} 1/(n log n) ≥ log log (X+1) - log log 2`. -/
theorem log_log_le_sum_one_div_mul_log (X : ℕ) (hX : 2 ≤ X) :
    Real.log (Real.log ((X : ℝ) + 1)) - Real.log (Real.log ((2 : ℕ) : ℝ)) ≤
      ∑ n ∈ Finset.Icc 2 X, 1 / ((n : ℝ) * Real.log n) := by
  have hstep : ∀ n : ℕ, 2 ≤ n → Real.log (Real.log ((n : ℝ) + 1)) - Real.log (Real.log n) ≤
      1 / ((n : ℝ) * Real.log n) := by
    intro n hn
    have h2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
    have hl : 0 < Real.log n := Real.log_pos (by linarith)
    have hl1 : 0 < Real.log ((n : ℝ) + 1) := Real.log_pos (by linarith)
    rw [← Real.log_div hl1.ne' hl.ne']
    refine (Real.log_le_sub_one_of_pos (div_pos hl1 hl)).trans ?_
    have hd : Real.log ((n : ℝ) + 1) - Real.log n ≤ 1 / n := by
      rw [← Real.log_div (by positivity) (by positivity)]
      refine (Real.log_le_sub_one_of_pos (by positivity)).trans (le_of_eq ?_)
      field_simp; ring
    rw [div_sub_one hl.ne']
    calc (Real.log ((n : ℝ) + 1) - Real.log n) / Real.log n ≤ (1 / n) / Real.log n :=
          div_le_div_of_nonneg_right hd hl.le
      _ = 1 / ((n : ℝ) * Real.log n) := by field_simp
  induction X, hX using Nat.le_induction with
  | base =>
    rw [Finset.Icc_self, Finset.sum_singleton]
    exact hstep 2 le_rfl
  | succ X hX ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    have := hstep (X + 1) (by omega)
    push_cast at this ⊢
    linarith

/-- `Σ_{n ≥ 2} 1/(n log n) = ∞`. -/
theorem not_summable_one_div_mul_log :
    ¬ Summable ({n : ℕ | 2 ≤ n}.indicator fun n : ℕ => 1 / ((n : ℝ) * Real.log n)) := by
  intro hs
  have hnn : ∀ n, 0 ≤ {n : ℕ | 2 ≤ n}.indicator (fun n : ℕ => 1 / ((n : ℝ) * Real.log n)) n := by
    intro n
    by_cases hn : n ∈ {n : ℕ | 2 ≤ n}
    · rw [Set.indicator_of_mem hn]
      have h2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
      have := Real.log_pos (by linarith : (1 : ℝ) < n)
      positivity
    · simp [hn]
  set T := ∑' n, {n : ℕ | 2 ≤ n}.indicator (fun n : ℕ => 1 / ((n : ℝ) * Real.log n)) n
  have hbound : ∀ X : ℕ, 2 ≤ X → Real.log (Real.log ((X : ℝ) + 1)) ≤
      T + Real.log (Real.log ((2 : ℕ) : ℝ)) := by
    intro X hX
    have h1 := log_log_le_sum_one_div_mul_log X hX
    have h2 : ∑ n ∈ Finset.Icc 2 X, 1 / ((n : ℝ) * Real.log n) ≤ T := by
      have : ∑ n ∈ Finset.Icc 2 X, 1 / ((n : ℝ) * Real.log n) =
          ∑ n ∈ Finset.Icc 2 X, {n : ℕ | 2 ≤ n}.indicator
            (fun n : ℕ => 1 / ((n : ℝ) * Real.log n)) n :=
        Finset.sum_congr rfl fun n hn => by
          rw [Set.indicator_of_mem (show n ∈ ({n : ℕ | 2 ≤ n} : Set ℕ) from
            (Finset.mem_Icc.mp hn).1)]
      rw [this]
      exact hs.sum_le_tsum _ fun n _ => hnn n
    exact sub_le_iff_le_add.mp (h1.trans h2)
  have hlim : Tendsto (fun X : ℕ => Real.log (Real.log ((X : ℝ) + 1))) atTop atTop :=
    Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp
      (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop))
  obtain ⟨X, hX1, hX2⟩ := ((hlim.eventually (eventually_gt_atTop
    (T + Real.log (Real.log ((2 : ℕ) : ℝ))))).and (eventually_ge_atTop 2)).exists
  exact absurd (hbound X hX2) (not_le.mpr hX1)

/-- **Finitely many exceptional nodes change nothing.**  Under the growth hypothesis of
`eqOn_zero_of_logRoom_growth`, vanishing on `N` outside a finite set `F` already forces `G ≡ 0`:
multiply by `∏_{f ∈ F}(ζ - f)`, which costs only the polynomial factor `(1 + |ζ|)^{|F|}`. -/
theorem eqOn_zero_of_logRoom_growth_off_finite {G : ℂ → ℂ} (hG : AnalyticOnNhd ℂ G rightHalf)
    {K A : ℝ} (c : ℕ) (hK0 : 0 ≤ K) (hK : K < π / 2)
    (hgrowth : ∀ ζ : ℂ, 0 < ζ.re →
      ‖G ζ‖ ≤ A * Real.exp (K * Real.exp (K / (π / 2 - |ζ.arg|))) * (1 + ‖ζ‖) ^ c)
    {N : Set ℕ} (hN2 : ∀ n ∈ N, 2 ≤ n)
    (hdiv : ¬ Summable (N.indicator fun n : ℕ => 1 / ((n : ℝ) * Real.log n)))
    (F : Finset ℕ) (hz : ∀ n ∈ N, n ∉ F → G n = 0) : EqOn G 0 rightHalf := by
  classical
  set P : ℂ → ℂ := fun ζ => ∏ f ∈ F, (ζ - (f : ℂ)) with hP
  have hPd : Differentiable ℂ P := by rw [hP]; fun_prop
  have hG' : AnalyticOnNhd ℂ (fun ζ => G ζ * P ζ) rightHalf := fun ζ hζ =>
    (hG ζ hζ).mul (hPd.analyticAt ζ)
  set C := ∏ f ∈ F, (1 + (f : ℝ)) with hC
  have hPnorm : ∀ ζ : ℂ, ‖P ζ‖ ≤ C * (1 + ‖ζ‖) ^ F.card := by
    intro ζ
    rw [hP, norm_prod, hC, ← Finset.prod_const, ← Finset.prod_mul_distrib]
    refine Finset.prod_le_prod (fun f _ => norm_nonneg _) fun f _ => ?_
    have hf : (0 : ℝ) ≤ f := Nat.cast_nonneg f
    calc ‖ζ - (f : ℂ)‖ ≤ ‖ζ‖ + f := by
          refine (norm_sub_le _ _).trans ?_; rw [Complex.norm_natCast]
      _ ≤ (1 + f) * (1 + ‖ζ‖) := by nlinarith [norm_nonneg ζ]
  have hgrowth' : ∀ ζ : ℂ, 0 < ζ.re → ‖G ζ * P ζ‖ ≤
      (A * C) * Real.exp (K * Real.exp (K / (π / 2 - |ζ.arg|))) * (1 + ‖ζ‖) ^ (c + F.card) := by
    intro ζ hζ
    have h1 := hgrowth ζ hζ
    have h2 := hPnorm ζ
    rw [norm_mul]
    calc ‖G ζ‖ * ‖P ζ‖ ≤ (A * Real.exp (K * Real.exp (K / (π / 2 - |ζ.arg|))) * (1 + ‖ζ‖) ^ c) *
          (C * (1 + ‖ζ‖) ^ F.card) :=
          mul_le_mul h1 h2 (norm_nonneg _) ((norm_nonneg _).trans h1)
      _ = _ := by rw [pow_add]; ring
  have hz' : ∀ n ∈ N, G n * P n = 0 := by
    intro n hn
    by_cases hnF : n ∈ F
    · have hPn : P n = 0 := Finset.prod_eq_zero (f := fun f : ℕ => (n : ℂ) - (f : ℂ)) hnF
        (sub_self _)
      rw [hPn, mul_zero]
    · rw [hz n hn hnF, zero_mul]
  have h0 := eqOn_zero_of_logRoom_growth hG' (c + F.card) hK0 hK hgrowth' hN2 hdiv hz'
  -- `G` vanishes off `F`; the real points `1/2 + 1/(k+3)` avoid `F` and accumulate at `1/2`
  have hoff : ∀ x : ℝ, 0 < x → x < 1 → G (x : ℂ) = 0 := by
    intro x hx0 hx1
    have hxmem : (x : ℂ) ∈ rightHalf := by show 0 < (x : ℂ).re; rw [Complex.ofReal_re]; exact hx0
    have hPx : P x ≠ 0 := by
      rw [hP, Finset.prod_ne_zero_iff]
      intro f _ h
      have hxf : x = f := by
        have := congrArg Complex.re (sub_eq_zero.mp h)
        simpa using this
      rcases Nat.eq_zero_or_pos f with hf | hf
      · rw [hf] at hxf; simp at hxf; linarith
      · have : (1 : ℝ) ≤ f := by exact_mod_cast hf
        linarith
    have := h0 hxmem
    simp only [Pi.zero_apply] at this
    exact (mul_eq_zero.mp this).resolve_right hPx
  have hz₀ : ((1 / 2 : ℝ) : ℂ) ∈ rightHalf := by
    show 0 < ((1 / 2 : ℝ) : ℂ).re; rw [Complex.ofReal_re]; norm_num
  refine hG.eqOn_zero_of_preconnected_of_frequently_eq_zero isPreconnected_rightHalf hz₀ ?_
  have ht : Tendsto (fun k : ℕ => ((1 / 2 + 1 / ((k : ℝ) + 3) : ℝ) : ℂ)) atTop
      (𝓝[≠] ((1 / 2 : ℝ) : ℂ)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, Eventually.of_forall fun k => ?_⟩
    · have h := (tendsto_one_div_add_atTop_nhds_zero_nat.comp
        (tendsto_add_atTop_nat 2)).const_add (1 / 2 : ℝ)
      rw [add_zero] at h
      have h' : Tendsto (fun k : ℕ => (1 / 2 : ℝ) + 1 / ((k : ℝ) + 3)) atTop (𝓝 (1 / 2)) := by
        refine h.congr fun k => ?_
        simp only [Function.comp_apply]; push_cast; ring
      exact (Complex.continuous_ofReal.tendsto _).comp h'
    · simp only [mem_compl_iff, mem_singleton_iff]
      intro h
      have h' := Complex.ofReal_injective h
      have : (0 : ℝ) < 1 / ((k : ℝ) + 3) := by positivity
      linarith
  exact ht.frequently (Frequently.of_forall fun k => hoff _ (by positivity) (by
    have : 1 / ((k : ℝ) + 3) ≤ 1 / 3 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
    linarith))

/-- **Selective tests do not exist below the threshold.**  If
`∫ |w(t)| e^{(π/2)|t| - K|t|/log(|t|+3)} dt < ∞` with `0 ≤ K < π/2`, and the Dirichlet moments
`∫ w(t) n^{-it} dt` vanish for all `n` in a set `N` with `Σ_{n ∈ N} 1/(n log n) = ∞` except at
finitely many `n`, then the Fourier transform of `w` vanishes identically; in particular the
exceptional moments vanish as well. -/
theorem fourier_eq_zero_of_dirichletMoment_eq_zero_off_finite_logRoom {K : ℝ} (hK0 : 0 ≤ K)
    (hK : K < π / 2) {N : Set ℕ} (hN2 : ∀ n ∈ N, 2 ≤ n)
    (hdiv : ¬ Summable (N.indicator fun n : ℕ => 1 / ((n : ℝ) * Real.log n)))
    (hwm : AEStronglyMeasurable w volume)
    (hroom : Integrable fun t => ‖w t‖ * logRoomWeight K t) (F : Finset ℕ)
    (hmom : ∀ n ∈ N, n ∉ F → ∫ t, w t * cexp (-(I * t) * Real.log n) = 0) (x : ℝ) :
    ∫ t, w t * cexp (-(I * t) * x) = 0 :=
  fourier_eq_zero_of_eqOn (eqOn_zero_of_logRoom_growth_off_finite
    (analyticOnNhd_logFourier (dominatesSubcritical_logRoomWeight hK0) hwm hroom) 0 hK0 hK
    (fun ζ hζ => by simpa using norm_logFourier_le_logRoom hK0 hroom hζ) hN2 hdiv F
    (fun n hn hnF => by rw [logFourier_natCast]; exact hmom n hn hnF)) x

/-- **No `n₀`-selective test under logarithmic room.**  If `0 ≤ K < π/2`,
`∫ |w(t)| e^{(π/2)|t| - K|t|/log(|t|+3)} dt < ∞`, and `∫ w(t) n^{-it} dt = 0` for every integer
`n ≥ 2` outside a finite set `F`, then `∫ w(t) m^{-it} dt = 0` for every `m ≥ 1`. -/
theorem dirichletMoment_eq_zero_of_cofinite_logRoom {K : ℝ} (hK0 : 0 ≤ K) (hK : K < π / 2)
    (hwm : AEStronglyMeasurable w volume)
    (hroom : Integrable fun t => ‖w t‖ * logRoomWeight K t) (F : Finset ℕ)
    (hmom : ∀ n : ℕ, 2 ≤ n → n ∉ F → ∫ t, w t * cexp (-(I * t) * Real.log n) = 0)
    {m : ℕ} (hm : 1 ≤ m) : ∫ t, w t * cexp (-(I * t) * Real.log m) = 0 := by
  have h0 := eqOn_zero_of_logRoom_growth_off_finite
    (analyticOnNhd_logFourier (dominatesSubcritical_logRoomWeight hK0) hwm hroom) 0 hK0 hK
    (fun ζ hζ => by simpa using norm_logFourier_le_logRoom hK0 hroom hζ) (N := {n | 2 ≤ n})
    (fun _ hn => hn) not_summable_one_div_mul_log F
    (fun n hn hnF => by rw [logFourier_natCast]; exact hmom n hn hnF)
  have hmem : ((m : ℕ) : ℂ) ∈ rightHalf := by
    show 0 < ((m : ℕ) : ℂ).re
    rw [Complex.natCast_re]; exact_mod_cast hm
  have := h0 hmem
  rwa [Pi.zero_apply, logFourier_natCast] at this

/-- **Logarithmic Carlson threshold at the integers.**  If
`∫ |w(t)| e^{(π/2)|t| - K|t|/log(|t|+3)} dt < ∞` for some `0 ≤ K < π/2`, and
`∫ w(t) n^{-it} dt = 0` for every integer `n ≥ 2`, the Fourier transform of `w` vanishes. -/
theorem fourier_eq_zero_of_integerMoment_eq_zero_logRoom {K : ℝ} (hK0 : 0 ≤ K)
    (hK : K < π / 2) (hwm : AEStronglyMeasurable w volume)
    (hroom : Integrable fun t => ‖w t‖ * logRoomWeight K t)
    (hmom : ∀ n : ℕ, 2 ≤ n → ∫ t, w t * cexp (-(I * t) * Real.log n) = 0) (x : ℝ) :
    ∫ t, w t * cexp (-(I * t) * x) = 0 :=
  fourier_eq_zero_of_dirichletMoment_eq_zero_logRoom hK0 hK (N := {n | 2 ≤ n}) (fun _ hn => hn)
    not_summable_one_div_mul_log hwm hroom (fun n hn => hmom n hn) x

end RHTower.PrimeBlindCarlson
