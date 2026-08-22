import Mathlib

/-!
# The quasi-Riesz intersite coupling coefficients

Zhong--Malomed--Yan, *Dynamics of discrete solitons in the fractional discrete nonlinear
Schrödinger equation with the quasi-Riesz derivative*, arXiv:2407.12441, Section II A.

The quasi-Riesz fractional discrete derivative of Lévy index `α` is the lattice operator whose
symbol on the Fourier torus `k ∈ [-π, π]` is `|k|^α`.  Expanding that symbol against the lattice
characters produces the intersite coupling coefficients of the paper's equation (10),

`D_ℓ^{(α)} = (1/π) ∫_0^π cos(ℓ k) k^α dk`,

which this file introduces and evaluates.

## Main results

* `quasiRieszCoupling` — equation (10).
* `quasiRieszCoupling_neg` — the coefficients are even in the site separation, `D_{-ℓ} = D_ℓ`.
* `quasiRieszCoupling_zero_index` — the self-coupling `D_0^{(α)} = π^α / (α + 1)`.
* `quasiRieszCoupling_alpha_zero` — at `α = 0` every nonlocal coefficient vanishes, as the paper
  remarks below equation (10).
* `quasiRieszCoupling_integration_by_parts` — equation (10), second form:
  `D_ℓ^{(α)} = -(α/(π ℓ)) ∫_0^π sin(ℓ k) k^{α-1} dk`.
* `quasiRieszCoupling_one`, `quasiRieszCoupling_two` — the closed forms behind equations (14) and
  (11): `D_ℓ^{(1)} = ((-1)^ℓ - 1)/(π ℓ²)` and `D_ℓ^{(2)} = 2(-1)^ℓ/ℓ²`.
-/

open MeasureTheory Set Filter Topology intervalIntegral

namespace GaloisForLFunctions.HTGeometry.FDNLS

/-! ## Elementary derivative and integrability lemmas -/

/-- The derivative of `k ↦ sin (L k)`. -/
theorem hasDerivAt_sinLin (L x : ℝ) :
    HasDerivAt (fun k : ℝ => Real.sin (L * k)) (Real.cos (L * x) * L) x := by
  simpa using ((hasDerivAt_id x).const_mul L).sin

/-- The derivative of `k ↦ cos (L k)`. -/
theorem hasDerivAt_cosLin (L x : ℝ) :
    HasDerivAt (fun k : ℝ => Real.cos (L * k)) (-Real.sin (L * x) * L) x := by
  simpa using ((hasDerivAt_id x).const_mul L).cos

/-- The real power `x ↦ x ^ α` is continuous on all of `ℝ` as soon as `0 ≤ α`. -/
theorem continuous_rpow_const {α : ℝ} (hα : 0 ≤ α) : Continuous fun x : ℝ => x ^ α :=
  continuous_iff_continuousAt.2 fun x => Real.continuousAt_rpow_const x α (Or.inr hα)

theorem continuous_cosLin (L : ℝ) : Continuous fun k : ℝ => Real.cos (L * k) :=
  Real.continuous_cos.comp (continuous_const.mul continuous_id)

theorem continuous_sinLin (L : ℝ) : Continuous fun k : ℝ => Real.sin (L * k) :=
  Real.continuous_sin.comp (continuous_const.mul continuous_id)

/-- The integrand of equation (10) is interval integrable for every nonnegative Lévy index. -/
theorem cos_rpow_intervalIntegrable {α : ℝ} (hα : 0 ≤ α) (L a b : ℝ) :
    IntervalIntegrable (fun k : ℝ => Real.cos (L * k) * k ^ α) volume a b :=
  ((continuous_cosLin L).mul (continuous_rpow_const hα)).intervalIntegrable a b

/-- The integrand of the integrated-by-parts form of equation (10) is interval integrable for every
positive Lévy index: the singularity `k^{α-1}` at the origin is integrable. -/
theorem sin_rpow_intervalIntegrable {α : ℝ} (hα : 0 < α) (L a b : ℝ) :
    IntervalIntegrable (fun k : ℝ => Real.sin (L * k) * k ^ (α - 1)) volume a b := by
  have hbase : IntervalIntegrable (fun x : ℝ => x ^ (α - 1)) volume a b :=
    intervalIntegrable_rpow' (by linarith)
  refine hbase.mono_fun ?_ ?_
  · exact ((continuous_sinLin L).measurable.mul
      (measurable_id.pow_const (α - 1))).aestronglyMeasurable
  · filter_upwards with k
    simp only [norm_mul, Real.norm_eq_abs]
    have h1 : |Real.sin (L * k)| ≤ 1 := Real.abs_sin_le_one _
    nlinarith [abs_nonneg (k ^ (α - 1)), abs_nonneg (Real.sin (L * k))]

/-- The primitive used for the integration by parts of equation (10). -/
theorem hasDerivAt_sinRpowPrimitive {α : ℝ} {L : ℝ} (hL : L ≠ 0) {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (fun k : ℝ => Real.sin (L * k) * k ^ α / L)
      (Real.cos (L * x) * x ^ α + α / L * (Real.sin (L * x) * x ^ (α - 1))) x := by
  have h2 : HasDerivAt (fun k : ℝ => k ^ α) (α * x ^ (α - 1)) x :=
    Real.hasDerivAt_rpow_const (Or.inl hx)
  have h3 := ((hasDerivAt_sinLin L x).mul h2).div_const L
  simp only [Pi.mul_def] at h3
  refine h3.congr_deriv ?_
  field_simp

/-! ## The coupling coefficients -/

/-- **Equation (10).**  The intersite coupling coefficient of the quasi-Riesz fractional discrete
derivative with Lévy index `α`, at site separation `ℓ`. -/
noncomputable def quasiRieszCoupling (α : ℝ) (ℓ : ℤ) : ℝ :=
  (1 / Real.pi) * ∫ k in (0:ℝ)..Real.pi, Real.cos ((ℓ : ℝ) * k) * k ^ α

/-- **Equation (10), evenness.**  `D_{-ℓ}^{(α)} = D_ℓ^{(α)}`. -/
theorem quasiRieszCoupling_neg (α : ℝ) (ℓ : ℤ) :
    quasiRieszCoupling α (-ℓ) = quasiRieszCoupling α ℓ := by
  unfold quasiRieszCoupling
  congr 1
  refine intervalIntegral.integral_congr fun k _ => ?_
  simp [neg_mul, Real.cos_neg]

/-- **The self-coupling coefficient.**  `D_0^{(α)} = π^α / (α + 1)`. -/
theorem quasiRieszCoupling_zero_index {α : ℝ} (hα : -1 < α) :
    quasiRieszCoupling α 0 = Real.pi ^ α / (α + 1) := by
  have hpi : (0:ℝ) < Real.pi := Real.pi_pos
  have h1 : ∫ k in (0:ℝ)..Real.pi, Real.cos (((0:ℤ) : ℝ) * k) * k ^ α
      = ∫ k in (0:ℝ)..Real.pi, k ^ α := by
    refine intervalIntegral.integral_congr fun k _ => ?_
    simp
  have h2 : ∫ k in (0:ℝ)..Real.pi, k ^ α
      = (Real.pi ^ (α + 1) - (0:ℝ) ^ (α + 1)) / (α + 1) := integral_rpow (Or.inl hα)
  have hz : (0:ℝ) ^ (α + 1) = 0 := Real.zero_rpow (by linarith)
  have hsplit : Real.pi ^ (α + 1) = Real.pi ^ α * Real.pi := Real.rpow_add_one (ne_of_gt hpi) α
  unfold quasiRieszCoupling
  rw [h1, h2, hz, hsplit]
  field_simp
  ring

/-- **At `α = 0` every genuinely nonlocal coefficient vanishes**, as the paper records immediately
below equation (10). -/
theorem quasiRieszCoupling_alpha_zero {ℓ : ℤ} (hℓ : ℓ ≠ 0) : quasiRieszCoupling 0 ℓ = 0 := by
  have hl : ((ℓ : ℝ)) ≠ 0 := Int.cast_ne_zero.2 hℓ
  have h1 : ∫ k in (0:ℝ)..Real.pi, Real.cos ((ℓ : ℝ) * k) * k ^ (0:ℝ)
      = ∫ k in (0:ℝ)..Real.pi, Real.cos ((ℓ : ℝ) * k) := by
    refine intervalIntegral.integral_congr fun k _ => ?_
    simp
  have hd : ∀ k : ℝ, HasDerivAt (fun x : ℝ => Real.sin ((ℓ : ℝ) * x) / (ℓ : ℝ))
      (Real.cos ((ℓ : ℝ) * k)) k := by
    intro k
    refine ((hasDerivAt_sinLin ((ℓ : ℝ)) k).div_const ((ℓ : ℝ))).congr_deriv ?_
    field_simp
  have h2 : ∫ k in (0:ℝ)..Real.pi, Real.cos ((ℓ : ℝ) * k)
      = Real.sin ((ℓ : ℝ) * Real.pi) / (ℓ : ℝ) - Real.sin ((ℓ : ℝ) * 0) / (ℓ : ℝ) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hd x)
      ((continuous_cosLin ((ℓ : ℝ))).intervalIntegrable _ _)
  have hsin : Real.sin ((ℓ : ℝ) * Real.pi) = 0 := Real.sin_int_mul_pi ℓ
  unfold quasiRieszCoupling
  rw [h1, h2, hsin]
  simp

/-! ## The integrated-by-parts form -/

/-- Integration by parts on `[0, π]`, in the raw integral form.  The boundary term at `π` is killed
by `sin (L π) = 0`, and the one at `0` by `0^α = 0`. -/
theorem integral_cos_mul_rpow_eq {α : ℝ} (hα : 0 < α) {L : ℝ} (hL : L ≠ 0)
    (hLpi : Real.sin (L * Real.pi) = 0) :
    ∫ k in (0:ℝ)..Real.pi, Real.cos (L * k) * k ^ α
      = -(α / L) * ∫ k in (0:ℝ)..Real.pi, Real.sin (L * k) * k ^ (α - 1) := by
  set g : ℝ → ℝ := fun k => Real.sin (L * k) * k ^ α / L with hg
  set G : ℝ → ℝ := fun k => Real.cos (L * k) * k ^ α + α / L * (Real.sin (L * k) * k ^ (α - 1))
    with hG
  have hcontRpow : Continuous fun x : ℝ => x ^ α := continuous_rpow_const hα.le
  have hcontg : Continuous g := ((continuous_sinLin L).mul hcontRpow).div_const L
  have hint1 : IntervalIntegrable (fun k : ℝ => Real.cos (L * k) * k ^ α) volume 0 Real.pi :=
    cos_rpow_intervalIntegrable hα.le L 0 Real.pi
  have hint2 : IntervalIntegrable (fun k : ℝ => Real.sin (L * k) * k ^ (α - 1)) volume 0 Real.pi :=
    sin_rpow_intervalIntegrable hα L 0 Real.pi
  have hintG : IntervalIntegrable G volume 0 Real.pi := hint1.add (hint2.const_mul _)
  have hsub : ∫ y in (0:ℝ)..Real.pi, G y = g Real.pi - g 0 := by
    refine intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le Real.pi_pos.le
      hcontg.continuousOn (fun x hx => ?_) hintG
    exact (hasDerivAt_sinRpowPrimitive hL (ne_of_gt hx.1)).hasDerivWithinAt
  have hgpi : g Real.pi = 0 := by simp [hg, hLpi]
  have hg0 : g 0 = 0 := by simp [hg]
  have hsplit : ∫ y in (0:ℝ)..Real.pi, G y
      = (∫ k in (0:ℝ)..Real.pi, Real.cos (L * k) * k ^ α)
        + α / L * ∫ k in (0:ℝ)..Real.pi, Real.sin (L * k) * k ^ (α - 1) := by
    rw [hG, intervalIntegral.integral_add hint1 (hint2.const_mul _),
      intervalIntegral.integral_const_mul]
  rw [hsplit, hgpi, hg0] at hsub
  linarith [hsub]

/-- **Equation (10), second form.**  For `ℓ ≠ 0` and `α > 0`,
`D_ℓ^{(α)} = -(α/(π ℓ)) ∫_0^π sin(ℓ k) k^{α-1} dk`. -/
theorem quasiRieszCoupling_integration_by_parts {α : ℝ} (hα : 0 < α) {ℓ : ℤ} (hℓ : ℓ ≠ 0) :
    quasiRieszCoupling α ℓ
      = -(α / (Real.pi * (ℓ : ℝ))) * ∫ k in (0:ℝ)..Real.pi,
          Real.sin ((ℓ : ℝ) * k) * k ^ (α - 1) := by
  have hl : ((ℓ : ℝ)) ≠ 0 := Int.cast_ne_zero.2 hℓ
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  unfold quasiRieszCoupling
  rw [integral_cos_mul_rpow_eq hα hl (Real.sin_int_mul_pi ℓ)]
  field_simp

/-! ## Closed-form primitives at integer Lévy index -/

/-- `∫_0^b k cos(L k) dk` in closed form. -/
theorem integral_lin_mul_cos {L : ℝ} (hL : L ≠ 0) (b : ℝ) :
    ∫ k in (0:ℝ)..b, Real.cos (L * k) * k
      = b * Real.sin (L * b) / L + Real.cos (L * b) / L ^ 2 - 1 / L ^ 2 := by
  have hd : ∀ x ∈ uIcc (0:ℝ) b,
      HasDerivAt (fun k : ℝ => k * Real.sin (L * k) / L + Real.cos (L * k) / L ^ 2)
        (Real.cos (L * x) * x) x := by
    intro x _
    have h1 := ((hasDerivAt_id x).mul (hasDerivAt_sinLin L x)).div_const L
    have h2 := (hasDerivAt_cosLin L x).div_const (L ^ 2)
    have h3 := h1.add h2
    simp only [Pi.mul_def, id] at h3
    refine h3.congr_deriv ?_
    field_simp
    ring
  have hint : IntervalIntegrable (fun k : ℝ => Real.cos (L * k) * k) volume 0 b :=
    ((continuous_cosLin L).mul continuous_id).intervalIntegrable _ _
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hint]
  simp

/-- `∫_0^b k² cos(L k) dk` in closed form. -/
theorem integral_sq_mul_cos {L : ℝ} (hL : L ≠ 0) (b : ℝ) :
    ∫ k in (0:ℝ)..b, Real.cos (L * k) * k ^ 2
      = b ^ 2 * Real.sin (L * b) / L + 2 * b * Real.cos (L * b) / L ^ 2
        - 2 * Real.sin (L * b) / L ^ 3 := by
  have hd : ∀ x ∈ uIcc (0:ℝ) b,
      HasDerivAt (fun k : ℝ => k ^ 2 * Real.sin (L * k) / L + 2 * k * Real.cos (L * k) / L ^ 2
          - 2 * Real.sin (L * k) / L ^ 3)
        (Real.cos (L * x) * x ^ 2) x := by
    intro x _
    have hx2 : HasDerivAt (fun k : ℝ => k ^ 2) (2 * x) x := by
      simpa using (hasDerivAt_pow 2 x)
    have h1 := (hx2.mul (hasDerivAt_sinLin L x)).div_const L
    have h2 := (((hasDerivAt_id x).const_mul (2:ℝ)).mul (hasDerivAt_cosLin L x)).div_const (L ^ 2)
    have h3 := ((hasDerivAt_sinLin L x).const_mul (2:ℝ)).div_const (L ^ 3)
    have h4 := (h1.add h2).sub h3
    simp only [Pi.mul_def, id] at h4
    refine h4.congr_deriv ?_
    field_simp
    ring
  have hint : IntervalIntegrable (fun k : ℝ => Real.cos (L * k) * k ^ 2) volume 0 b :=
    ((continuous_cosLin L).mul (continuous_pow 2)).intervalIntegrable _ _
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hint]
  simp

/-! ## The Lévy indices `α = 1` and `α = 2` -/

/-- **Equation (14).**  At `α = 1` the nonlocal coefficients are `((-1)^ℓ - 1)/(π ℓ²)`: they vanish
at every even separation and equal `-2/(π ℓ²)` at every odd one. -/
theorem quasiRieszCoupling_one {ℓ : ℤ} (hℓ : ℓ ≠ 0) :
    quasiRieszCoupling 1 ℓ = ((-1 : ℝ) ^ ℓ - 1) / (Real.pi * (ℓ : ℝ) ^ 2) := by
  have hl : ((ℓ : ℝ)) ≠ 0 := Int.cast_ne_zero.2 hℓ
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  have hrw : ∫ k in (0:ℝ)..Real.pi, Real.cos ((ℓ : ℝ) * k) * k ^ (1:ℝ)
      = ∫ k in (0:ℝ)..Real.pi, Real.cos ((ℓ : ℝ) * k) * k := by
    refine intervalIntegral.integral_congr fun k _ => ?_
    rw [Real.rpow_one]
  unfold quasiRieszCoupling
  rw [hrw, integral_lin_mul_cos hl Real.pi, Real.sin_int_mul_pi ℓ, Real.cos_int_mul_pi ℓ]
  field_simp
  ring

/-- **Equation (11).**  At `α = 2` the nonlocal coefficients are `2(-1)^ℓ/ℓ²`: the inverse-square
long-range coupling of the paper's integer-order lattice. -/
theorem quasiRieszCoupling_two {ℓ : ℤ} (hℓ : ℓ ≠ 0) :
    quasiRieszCoupling 2 ℓ = 2 * (-1 : ℝ) ^ ℓ / (ℓ : ℝ) ^ 2 := by
  have hl : ((ℓ : ℝ)) ≠ 0 := Int.cast_ne_zero.2 hℓ
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  have hrw : ∫ k in (0:ℝ)..Real.pi, Real.cos ((ℓ : ℝ) * k) * k ^ (2:ℝ)
      = ∫ k in (0:ℝ)..Real.pi, Real.cos ((ℓ : ℝ) * k) * k ^ 2 := by
    refine intervalIntegral.integral_congr fun k _ => ?_
    rw [show (2:ℝ) = ((2:ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  unfold quasiRieszCoupling
  rw [hrw, integral_sq_mul_cos hl Real.pi, Real.sin_int_mul_pi ℓ, Real.cos_int_mul_pi ℓ]
  field_simp
  ring

/-- The self-coupling at `α = 1`: the `π/2 u_n` term of equation (14). -/
theorem quasiRieszCoupling_one_zero : quasiRieszCoupling 1 0 = Real.pi / 2 := by
  rw [quasiRieszCoupling_zero_index (by norm_num : (-1:ℝ) < 1), Real.rpow_one]
  norm_num

/-- The self-coupling at `α = 2`: the `π²/3 u_n` term of equation (11). -/
theorem quasiRieszCoupling_two_zero : quasiRieszCoupling 2 0 = Real.pi ^ 2 / 3 := by
  rw [quasiRieszCoupling_zero_index (by norm_num : (-1:ℝ) < 2),
    show (2:ℝ) = ((2:ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  norm_num

/-- At `α = 1` the even separations decouple entirely: `D_{2m}^{(1)} = 0` for `m ≠ 0`.  This is the
statement, in the paper's words below equation (14), that site `n` is coupled to `n ± 1, n ± 3, …`
but not to `n ± 2, n ± 4, …`. -/
theorem quasiRieszCoupling_one_even {m : ℤ} (hm : m ≠ 0) : quasiRieszCoupling 1 (2 * m) = 0 := by
  have h2m : (2 * m) ≠ 0 := by omega
  rw [quasiRieszCoupling_one h2m]
  have : ((-1 : ℝ)) ^ (2 * m) = 1 := by
    rw [zpow_mul]
    norm_num
  rw [this]
  simp

/-- At `α = 1` the odd separations carry the full coupling: `D_{2m+1}^{(1)} = -2/(π (2m+1)²)`. -/
theorem quasiRieszCoupling_one_odd (m : ℤ) :
    quasiRieszCoupling 1 (2 * m + 1) = -(2 / (Real.pi * ((2 * m + 1 : ℤ) : ℝ) ^ 2)) := by
  have h : (2 * m + 1) ≠ 0 := by omega
  rw [quasiRieszCoupling_one h]
  have hsign : ((-1 : ℝ)) ^ (2 * m + 1) = -1 := by
    rw [zpow_add₀ (by norm_num : (-1:ℝ) ≠ 0), zpow_mul]
    norm_num
  rw [hsign]
  ring

end GaloisForLFunctions.HTGeometry.FDNLS
