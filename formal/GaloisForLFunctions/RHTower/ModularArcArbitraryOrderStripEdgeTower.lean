import GaloisForLFunctions.RHTower.ModularArcForwardTwoScaleAllIntegerBlind

/-!
# Arbitrary-order strip-edge vanishing tower for pole-filtered modular arc witnesses

In `ModularArcTwoScaleHyperbolicWitness` and `ModularArcTwoScaleStripEdgeVanishing`, applying a
single hyperbolic dilation-filter step to `arcLineAtomicVector (log k) ν` upgraded strip-edge
vanishing from `O(1/2 − l)` to `O((1/2 − l)²)` while squaring the blind sublattice modulus from
`k²` to `k⁴` and preserving self-reciprocity and critical-line positive definiteness.

In this module we formalize the **universal hyperbolic dilation-filter endofunctor**
`(hyperbolicFilterVec m, hyperbolicFilterDeriv m, hyperbolicFilterProfile m)` and iterate it to
construct an infinite tower `(arcLineTowerVector k d ν, arcLineTowerDeriv k d ν, arcLineTowerProfile k d ν)`
indexed by `d ∈ ℕ`.

## Main results

1. **Universal one-step preservation laws for `hyperbolicFilter`:**
   For any integer `m ≥ 1`, `(hyperbolicFilterVec m, hyperbolicFilterDeriv m, hyperbolicFilterProfile m)`
   preserves differentiation (`hasDerivAt_hyperbolicFilterVec`), even/odd parity, exact `x ↦ 1/x`
   self-reciprocity (`hyperbolicFilterVec_inv`), the log-profile bridge
   (`exp_half_mul_hyperbolicFilterVec`), the `O(e^{−3|v|/2})` Weil decay class
   (`abs_hyperbolicFilterProfile_le`), and zero mean (`integral_hyperbolicFilterVec_eq_zero`).
2. **Universal spectral & sublattice induction laws:**
   - `integral_cos_mul_hyperbolicFilterProfile_pos`: for `m ≥ 2`, preserves strict positive
     definiteness on the critical line (`∀ τ ∈ ℝ, 0 < ∫ cos(τv) P(v) dv`).
   - `abs_integral_exp_mul_hyperbolicFilterProfile_le`: increments the strip-edge vanishing order
     `O((1/2 − l)^d) ↦ O((1/2 − l)^{d+1})` on `l ∈ [0, 1/2)`.
   - `integral_hyperbolicFilterDeriv_mul_sin_sublattice_eq_zero`: multiplies the blind sublattice
     modulus `N ↦ m² N`, mapping `N`-sublattice blindness to `(m² N)`-sublattice blindness.
3. **Arbitrary-order tower (`arcLineTowerVector k d ν`, `d ∈ ℕ`):**
   For every integer `k ≥ 2` and every order `d ∈ ℕ`, `arcLineTowerVector k d ν` is an even,
   strictly self-reciprocal, zero-mean, strictly positive definite function in the `O(e^{−3|v|/2})`
   Weil decay class that is identically blind on the infinite `k^{2(d+1)}`-sublattice
   `arcFreq (k^{2(d+1)}(j+1) − 1)` (`j ∈ ℕ`) and vanishes to **order `d + 1`** at the critical
   strip edge `l → (1/2)⁻`:
   `|∫ e^{lv} P_{k,d}(v) dv| ≤ 10 · ν.real univ · (log k)² · (2 log k)^d · (1/2 − l)^{d+1}`,
   so that its `d`-th divided difference `(∫ e^{lv} P_{k,d}(v) dv) / (1/2 − l)^d → 0` on
   `𝓝[<] (1/2)` (`exists_arbitraryOrder_stripEdge_sublattice_arcWitness`).
-/

open MeasureTheory Set Filter Topology
open GaloisForLFunctions.HTGeometry RHTower.BesselKZero

namespace RHTower

noncomputable section

/-! ### The universal hyperbolic dilation-filter operator at integer scale `m` -/

/-- The hyperbolic dilation-filter operator on line vectors at integer scale `m`:
`(ℋ_m f)(x) = f(x) − (1 / (2 cosh(log m))) (m⁻¹ f(x / m²) + m f(m² x))`. -/
def hyperbolicFilterVec (m : ℕ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  f x - (1 / (2 * Real.cosh (Real.log m))) *
    ((m : ℝ)⁻¹ * f (x * ((m : ℝ) ^ 2)⁻¹) + (m : ℝ) * f ((m : ℝ) ^ 2 * x))

/-- The hyperbolic dilation-filter operator on derivatives at integer scale `m`:
`(ℋ_m' f')(x) = f'(x) − (1 / (2 cosh(log m))) (m⁻³ f'(x / m²) + m³ f'(m² x))`. -/
def hyperbolicFilterDeriv (m : ℕ) (f' : ℝ → ℝ) (x : ℝ) : ℝ :=
  f' x - (1 / (2 * Real.cosh (Real.log m))) *
    (((m : ℝ) ^ 3)⁻¹ * f' (x * ((m : ℝ) ^ 2)⁻¹) + (m : ℝ) ^ 3 * f' ((m : ℝ) ^ 2 * x))

/-- The hyperbolic dilation-filter operator on log-scale profiles at integer scale `m`:
`(ℋ_m^{prof} P)(v) = P(v) − (1 / (2 cosh(log m))) (P(v − 2 log m) + P(v + 2 log m))`. -/
def hyperbolicFilterProfile (m : ℕ) (P : ℝ → ℝ) (v : ℝ) : ℝ :=
  P v - (1 / (2 * Real.cosh (Real.log m))) * (P (v - 2 * Real.log m) + P (v + 2 * Real.log m))

theorem hasDerivAt_hyperbolicFilterVec (m : ℕ) {f f' : ℝ → ℝ}
    (hf : ∀ x, HasDerivAt f (f' x) x) (x : ℝ) :
    HasDerivAt (hyperbolicFilterVec m f) (hyperbolicFilterDeriv m f' x) x := by
  have hc1 : HasDerivAt (fun x' : ℝ => x' * ((m : ℝ) ^ 2)⁻¹) (((m : ℝ) ^ 2)⁻¹) x := by
    simpa using (hasDerivAt_id x).mul_const (((m : ℝ) ^ 2)⁻¹)
  have hc2 : HasDerivAt (fun x' : ℝ => (m : ℝ) ^ 2 * x') ((m : ℝ) ^ 2) x := by
    simpa using (hasDerivAt_id x).const_mul ((m : ℝ) ^ 2)
  have h1 := ((hf (x * ((m : ℝ) ^ 2)⁻¹)).comp x hc1).const_mul ((m : ℝ)⁻¹)
  have h2 := ((hf ((m : ℝ) ^ 2 * x)).comp x hc2).const_mul (m : ℝ)
  have h := (hf x).sub ((h1.add h2).const_mul (1 / (2 * Real.cosh (Real.log m))))
  refine h.congr_deriv ?_
  unfold hyperbolicFilterDeriv
  ring

theorem hyperbolicFilterVec_neg (m : ℕ) {f : ℝ → ℝ} (heven : ∀ x, f (-x) = f x) (x : ℝ) :
    hyperbolicFilterVec m f (-x) = hyperbolicFilterVec m f x := by
  unfold hyperbolicFilterVec
  rw [neg_mul, mul_neg, heven, heven, heven]

theorem hyperbolicFilterDeriv_neg (m : ℕ) {f' : ℝ → ℝ} (hodd : ∀ x, f' (-x) = -f' x) (x : ℝ) :
    hyperbolicFilterDeriv m f' (-x) = -hyperbolicFilterDeriv m f' x := by
  unfold hyperbolicFilterDeriv
  rw [neg_mul, mul_neg, hodd, hodd, hodd]
  ring

theorem hyperbolicFilterProfile_neg (m : ℕ) {P : ℝ → ℝ} (heven : ∀ v, P (-v) = P v) (v : ℝ) :
    hyperbolicFilterProfile m P (-v) = hyperbolicFilterProfile m P v := by
  unfold hyperbolicFilterProfile
  have h1 : P (-v - 2 * Real.log m) = P (v + 2 * Real.log m) := by
    rw [← heven (v + 2 * Real.log m)]; congr 1; ring
  have h2 : P (-v + 2 * Real.log m) = P (v - 2 * Real.log m) := by
    rw [← heven (v - 2 * Real.log m)]; congr 1; ring
  rw [heven, h1, h2, add_comm (P (v + 2 * Real.log m))]

/-- **Self-reciprocity preservation:** if `f(1/x) = |x| f(x)`, then
`hyperbolicFilterVec m f (1/x) = |x| hyperbolicFilterVec m f x`. -/
theorem hyperbolicFilterVec_inv {m : ℕ} (hm : 1 ≤ m) {f : ℝ → ℝ}
    (hinv : ∀ x, x ≠ 0 → f (1 / x) = |x| * f x) {x : ℝ} (hx : x ≠ 0) :
    hyperbolicFilterVec m f (1 / x) = |x| * hyperbolicFilterVec m f x := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (lt_of_lt_of_le zero_lt_one hm)
  have hmne : (m : ℝ) ≠ 0 := hmpos.ne'
  have hy1 : (m : ℝ) ^ 2 * x ≠ 0 := mul_ne_zero (pow_ne_zero 2 hmne) hx
  have hy2 : x * ((m : ℝ) ^ 2)⁻¹ ≠ 0 := mul_ne_zero hx (inv_ne_zero (pow_ne_zero 2 hmne))
  have e1 : 1 / x * ((m : ℝ) ^ 2)⁻¹ = 1 / ((m : ℝ) ^ 2 * x) := by field_simp
  have e2 : (m : ℝ) ^ 2 * (1 / x) = 1 / (x * ((m : ℝ) ^ 2)⁻¹) := by field_simp
  unfold hyperbolicFilterVec
  rw [hinv x hx, e1, hinv _ hy1, e2, hinv _ hy2,
    abs_mul, abs_mul, abs_of_pos (pow_pos hmpos 2),
    abs_of_pos (inv_pos.mpr (pow_pos hmpos 2))]
  field_simp
  ring

theorem exp_half_mul_hyperbolicFilterVec {m : ℕ} (hm : 1 ≤ m) {f P : ℝ → ℝ}
    (hprof : ∀ v, Real.exp (v / 2) * f (Real.exp v) = P v) (v : ℝ) :
    Real.exp (v / 2) * hyperbolicFilterVec m f (Real.exp v) =
      hyperbolicFilterProfile m P v := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (lt_of_lt_of_le zero_lt_one hm)
  have he2_inv : ((m : ℝ) ^ 2)⁻¹ = Real.exp (-(2 * Real.log m)) := by
    rw [Real.exp_neg, show (2 : ℝ) * Real.log m = ((2 : ℕ) : ℝ) * Real.log m by norm_num,
      Real.exp_nat_mul, Real.exp_log hmpos]
  have he2 : (m : ℝ) ^ 2 = Real.exp (2 * Real.log m) := by
    rw [show (2 : ℝ) * Real.log m = ((2 : ℕ) : ℝ) * Real.log m by norm_num,
      Real.exp_nat_mul, Real.exp_log hmpos]
  have e1 : Real.exp v * ((m : ℝ) ^ 2)⁻¹ = Real.exp (v - 2 * Real.log m) := by
    rw [he2_inv, ← Real.exp_add]; ring_nf
  have e2 : Real.exp (v / 2) * (m : ℝ)⁻¹ = Real.exp ((v - 2 * Real.log m) / 2) := by
    rw [show (v - 2 * Real.log m) / 2 = v / 2 - Real.log m by ring,
      sub_eq_add_neg, Real.exp_add, Real.exp_neg, Real.exp_log hmpos]
  have e3 : (m : ℝ) ^ 2 * Real.exp v = Real.exp (v + 2 * Real.log m) := by
    rw [he2, ← Real.exp_add]; ring_nf
  have e4 : Real.exp (v / 2) * (m : ℝ) = Real.exp ((v + 2 * Real.log m) / 2) := by
    rw [show (v + 2 * Real.log m) / 2 = v / 2 + Real.log m by ring,
      Real.exp_add, Real.exp_log hmpos]
  unfold hyperbolicFilterVec hyperbolicFilterProfile
  rw [mul_sub, hprof v, ← mul_left_comm, mul_add,
    ← mul_assoc (Real.exp (v / 2)), e2, e1, hprof (v - 2 * Real.log m),
    ← mul_assoc (Real.exp (v / 2)), e4, e3, hprof (v + 2 * Real.log m)]

theorem abs_hyperbolicFilterProfile_le {m : ℕ} (hm : 1 ≤ m) {P : ℝ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hP : ∀ v, |P v| ≤ C * Real.exp (-(3 * |v| / 2))) (v : ℝ) :
    |hyperbolicFilterProfile m P v| ≤
      C * (1 + (m : ℝ) ^ 3) * Real.exp (-(3 * |v| / 2)) := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (lt_of_lt_of_le zero_lt_one hm)
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hexp3 : Real.exp (3 * Real.log m) = (m : ℝ) ^ 3 := by
    rw [show (3 : ℝ) * Real.log m = ((3 : ℕ) : ℝ) * Real.log m by norm_num,
      Real.exp_nat_mul, Real.exp_log hmpos]
  have hlog : |2 * Real.log m| = 2 * Real.log m :=
    abs_of_nonneg (mul_nonneg zero_le_two (Real.log_nonneg hm1))
  have hshift1 : Real.exp (-(3 * |v - 2 * Real.log m| / 2)) ≤
      (m : ℝ) ^ 3 * Real.exp (-(3 * |v| / 2)) := by
    rw [← hexp3, ← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    have habs := abs_sub_abs_le_abs_sub v (2 * Real.log m)
    linarith
  have hshift2 : Real.exp (-(3 * |v + 2 * Real.log m| / 2)) ≤
      (m : ℝ) ^ 3 * Real.exp (-(3 * |v| / 2)) := by
    rw [← hexp3, ← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    have habs := abs_sub_abs_le_abs_sub v (-(2 * Real.log m))
    rw [sub_neg_eq_add, abs_neg] at habs
    linarith
  have h1 : |P (v - 2 * Real.log m)| ≤ C * (m : ℝ) ^ 3 * Real.exp (-(3 * |v| / 2)) := by
    calc |P (v - 2 * Real.log m)|
        ≤ C * Real.exp (-(3 * |v - 2 * Real.log m| / 2)) := hP _
      _ ≤ C * ((m : ℝ) ^ 3 * Real.exp (-(3 * |v| / 2))) :=
          mul_le_mul_of_nonneg_left hshift1 hC
      _ = C * (m : ℝ) ^ 3 * Real.exp (-(3 * |v| / 2)) := by ring
  have h2 : |P (v + 2 * Real.log m)| ≤ C * (m : ℝ) ^ 3 * Real.exp (-(3 * |v| / 2)) := by
    calc |P (v + 2 * Real.log m)|
        ≤ C * Real.exp (-(3 * |v + 2 * Real.log m| / 2)) := hP _
      _ ≤ C * ((m : ℝ) ^ 3 * Real.exp (-(3 * |v| / 2))) :=
          mul_le_mul_of_nonneg_left hshift2 hC
      _ = C * (m : ℝ) ^ 3 * Real.exp (-(3 * |v| / 2)) := by ring
  have hcosh : 1 / (2 * Real.cosh (Real.log m)) ≤ 1 / 2 := by
    have := Real.one_le_cosh (Real.log m)
    rw [div_le_div_iff₀ (by positivity) zero_lt_two]
    linarith
  have hsum : |(1 / (2 * Real.cosh (Real.log m))) *
      (P (v - 2 * Real.log m) + P (v + 2 * Real.log m))| ≤
      C * (m : ℝ) ^ 3 * Real.exp (-(3 * |v| / 2)) := by
    rw [abs_mul, abs_of_pos (by positivity)]
    calc 1 / (2 * Real.cosh (Real.log m)) * |P (v - 2 * Real.log m) + P (v + 2 * Real.log m)|
        ≤ (1 / 2) * (|P (v - 2 * Real.log m)| + |P (v + 2 * Real.log m)|) :=
          mul_le_mul hcosh (abs_add_le _ _) (abs_nonneg _) (by norm_num)
      _ ≤ (1 / 2) * (C * (m : ℝ) ^ 3 * Real.exp (-(3 * |v| / 2)) +
            C * (m : ℝ) ^ 3 * Real.exp (-(3 * |v| / 2))) := by gcongr
      _ = C * (m : ℝ) ^ 3 * Real.exp (-(3 * |v| / 2)) := by ring
  unfold hyperbolicFilterProfile
  have h0 := hP v
  have hsub := abs_sub (P v) ((1 / (2 * Real.cosh (Real.log m))) *
    (P (v - 2 * Real.log m) + P (v + 2 * Real.log m)))
  linarith

theorem integrable_hyperbolicFilterVec {m : ℕ} (hm : 1 ≤ m) {f : ℝ → ℝ} (hf : Integrable f) :
    Integrable (hyperbolicFilterVec m f) := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (lt_of_lt_of_le zero_lt_one hm)
  have h1 := (hf.comp_mul_right' (inv_ne_zero (pow_ne_zero 2 hmpos.ne'))).const_mul ((m : ℝ)⁻¹)
  have h2 := (hf.comp_mul_left' (pow_ne_zero 2 hmpos.ne')).const_mul (m : ℝ)
  exact hf.sub ((h1.add h2).const_mul _)

theorem integrable_hyperbolicFilterDeriv {m : ℕ} (hm : 1 ≤ m) {f' : ℝ → ℝ} (hf' : Integrable f') :
    Integrable (hyperbolicFilterDeriv m f') := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (lt_of_lt_of_le zero_lt_one hm)
  have h1 := (hf'.comp_mul_right' (inv_ne_zero (pow_ne_zero 2 hmpos.ne'))).const_mul
    (((m : ℝ) ^ 3)⁻¹)
  have h2 := (hf'.comp_mul_left' (pow_ne_zero 2 hmpos.ne')).const_mul ((m : ℝ) ^ 3)
  exact hf'.sub ((h1.add h2).const_mul _)

theorem integrable_hyperbolicFilterProfile (m : ℕ) {P : ℝ → ℝ} (hP : Integrable P) :
    Integrable (hyperbolicFilterProfile m P) :=
  hP.sub (((hP.comp_sub_right (2 * Real.log m)).add
    (hP.comp_add_right (2 * Real.log m))).const_mul _)

theorem integral_hyperbolicFilterVec_eq_zero {m : ℕ} (hm : 1 ≤ m) {f : ℝ → ℝ}
    (hf : Integrable f) (h0 : ∫ x, f x = 0) :
    ∫ x, hyperbolicFilterVec m f x = 0 := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (lt_of_lt_of_le zero_lt_one hm)
  have h1 : Integrable fun x => (m : ℝ)⁻¹ * f (x * ((m : ℝ) ^ 2)⁻¹) :=
    (hf.comp_mul_right' (inv_ne_zero (pow_ne_zero 2 hmpos.ne'))).const_mul ((m : ℝ)⁻¹)
  have h2 : Integrable fun x => (m : ℝ) * f ((m : ℝ) ^ 2 * x) :=
    (hf.comp_mul_left' (pow_ne_zero 2 hmpos.ne')).const_mul (m : ℝ)
  have h01 : Integrable fun x =>
      f x - (1 / (2 * Real.cosh (Real.log m))) * ((m : ℝ)⁻¹ * f (x * ((m : ℝ) ^ 2)⁻¹)) :=
    hf.sub (h1.const_mul _)
  have e : hyperbolicFilterVec m f = fun x =>
      f x - (1 / (2 * Real.cosh (Real.log m))) * ((m : ℝ)⁻¹ * f (x * ((m : ℝ) ^ 2)⁻¹)) -
        (1 / (2 * Real.cosh (Real.log m))) * ((m : ℝ) * f ((m : ℝ) ^ 2 * x)) := by
    funext x; unfold hyperbolicFilterVec; ring
  rw [e, integral_sub h01 (h2.const_mul _),
    integral_sub hf (h1.const_mul _),
    integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul,
    Measure.integral_comp_mul_right f (((m : ℝ) ^ 2)⁻¹),
    Measure.integral_comp_mul_left f ((m : ℝ) ^ 2)]
  simp [h0]

/-! ### Universal one-step spectral, strip-edge, and sublattice induction laws -/

theorem integral_cos_mul_shift_of_even {P : ℝ → ℝ} (hP : Integrable P)
    (heven : ∀ v, P (-v) = P v) (τ w : ℝ) :
    ∫ v, Real.cos (τ * v) * P (v - w) =
      Real.cos (τ * w) * ∫ v, Real.cos (τ * v) * P v := by
  have hc : Integrable fun v => Real.cos (τ * v) * P v :=
    hP.bdd_mul (by fun_prop) (Eventually.of_forall fun v => by
      rw [Real.norm_eq_abs]; exact Real.abs_cos_le_one _)
  have hs : Integrable fun v => Real.sin (τ * v) * P v :=
    hP.bdd_mul (by fun_prop) (Eventually.of_forall fun v => by
      rw [Real.norm_eq_abs]; exact Real.abs_sin_le_one _)
  have hodd : ∫ v, Real.sin (τ * v) * P v = 0 := by
    have h := integral_neg_eq_self (fun v => Real.sin (τ * v) * P v) volume
    have e : (fun v => Real.sin (τ * -v) * P (-v)) =
        fun v => -(Real.sin (τ * v) * P v) := by
      funext v; rw [heven, mul_neg, Real.sin_neg]; ring
    rw [e, integral_neg] at h
    linarith
  rw [← integral_add_right_eq_self (μ := volume)
    (fun v => Real.cos (τ * v) * P (v - w)) w]
  have e : ∀ v, Real.cos (τ * (v + w)) * P (v + w - w) =
      Real.cos (τ * w) * (Real.cos (τ * v) * P v) -
        Real.sin (τ * w) * (Real.sin (τ * v) * P v) := by
    intro v; rw [add_sub_cancel_right, mul_add, Real.cos_add]; ring
  simp_rw [e]
  rw [integral_sub (hc.const_mul _) (hs.const_mul _), integral_const_mul, integral_const_mul,
    hodd, mul_zero, sub_zero]

theorem integral_cos_mul_hyperbolicFilterProfile (m : ℕ) {P : ℝ → ℝ} (hP : Integrable P)
    (heven : ∀ v, P (-v) = P v) (τ : ℝ) :
    ∫ v, Real.cos (τ * v) * hyperbolicFilterProfile m P v =
      (1 - Real.cos (τ * (2 * Real.log m)) / Real.cosh (Real.log m)) *
        ∫ v, Real.cos (τ * v) * P v := by
  have hc : Integrable fun v => Real.cos (τ * v) * P v :=
    hP.bdd_mul (by fun_prop) (Eventually.of_forall fun v => by
      rw [Real.norm_eq_abs]; exact Real.abs_cos_le_one _)
  have hc1 : Integrable fun v => Real.cos (τ * v) * P (v - 2 * Real.log m) :=
    (hP.comp_sub_right (2 * Real.log m)).bdd_mul (by fun_prop) (Eventually.of_forall fun v => by
      rw [Real.norm_eq_abs]; exact Real.abs_cos_le_one _)
  have hc2 : Integrable fun v => Real.cos (τ * v) * P (v + 2 * Real.log m) :=
    (hP.comp_add_right (2 * Real.log m)).bdd_mul (by fun_prop) (Eventually.of_forall fun v => by
      rw [Real.norm_eq_abs]; exact Real.abs_cos_le_one _)
  have hc01 : Integrable fun v =>
      Real.cos (τ * v) * P v -
        (1 / (2 * Real.cosh (Real.log m))) * (Real.cos (τ * v) * P (v - 2 * Real.log m)) :=
    hc.sub (hc1.const_mul _)
  have e : (fun v => Real.cos (τ * v) * hyperbolicFilterProfile m P v) = fun v =>
      Real.cos (τ * v) * P v -
        (1 / (2 * Real.cosh (Real.log m))) * (Real.cos (τ * v) * P (v - 2 * Real.log m)) -
        (1 / (2 * Real.cosh (Real.log m))) * (Real.cos (τ * v) * P (v + 2 * Real.log m)) := by
    funext v; unfold hyperbolicFilterProfile; ring
  have e2 : ∫ v, Real.cos (τ * v) * P (v + 2 * Real.log m) =
      Real.cos (τ * (2 * Real.log m)) * ∫ v, Real.cos (τ * v) * P v := by
    have esub : (fun v => Real.cos (τ * v) * P (v + 2 * Real.log m)) =
        fun v => Real.cos (τ * v) * P (v - (-(2 * Real.log m))) := by
      funext v; rw [sub_neg_eq_add]
    rw [esub, integral_cos_mul_shift_of_even hP heven, mul_neg, Real.cos_neg]
  rw [e, integral_sub hc01 (hc2.const_mul _),
    integral_sub hc (hc1.const_mul _),
    integral_const_mul, integral_const_mul,
    integral_cos_mul_shift_of_even hP heven, e2]
  ring

theorem integral_cos_mul_hyperbolicFilterProfile_pos {m : ℕ} (hm : 2 ≤ m) {P : ℝ → ℝ}
    (hP : Integrable P) (heven : ∀ v, P (-v) = P v) {τ : ℝ}
    (hpos : 0 < ∫ v, Real.cos (τ * v) * P v) :
    0 < ∫ v, Real.cos (τ * v) * hyperbolicFilterProfile m P v := by
  have hmgt1 : (1 : ℝ) < m := by exact_mod_cast (lt_of_lt_of_le one_lt_two hm)
  have hb : 0 < Real.log m := Real.log_pos hmgt1
  rw [integral_cos_mul_hyperbolicFilterProfile m hP heven]
  refine mul_pos ?_ hpos
  have hC : 1 < Real.cosh (Real.log m) := Real.one_lt_cosh.mpr hb.ne'
  have hlt : Real.cos (τ * (2 * Real.log m)) / Real.cosh (Real.log m) < 1 := by
    rw [div_lt_one (Real.cosh_pos _)]
    linarith [Real.cos_le_one (τ * (2 * Real.log m))]
  linarith

theorem integrable_exp_mul_hyperbolicFilterProfile (m : ℕ) {P : ℝ → ℝ} {l : ℝ}
    (hP : Integrable fun v => Real.exp (l * v) * P v) :
    Integrable fun v => Real.exp (l * v) * hyperbolicFilterProfile m P v := by
  have hshift : ∀ w, Integrable fun v => Real.exp (l * v) * P (v - w) := fun w => by
    have h := (hP.comp_sub_right w).const_mul (Real.exp (l * w))
    refine h.congr (Eventually.of_forall fun v => ?_)
    simp only
    rw [show l * v = l * w + l * (v - w) by ring, Real.exp_add]; ring
  have h1 := hshift (2 * Real.log m)
  have h2 : Integrable fun v => Real.exp (l * v) * P (v + 2 * Real.log m) := by
    have e : (fun v => Real.exp (l * v) * P (v + 2 * Real.log m)) =
        fun v => Real.exp (l * v) * P (v - (-(2 * Real.log m))) := by
      funext v; rw [sub_neg_eq_add]
    rw [e]; exact hshift (-(2 * Real.log m))
  have e : (fun v => Real.exp (l * v) * hyperbolicFilterProfile m P v) = fun v =>
      Real.exp (l * v) * P v -
        (1 / (2 * Real.cosh (Real.log m))) * (Real.exp (l * v) * P (v - 2 * Real.log m)) -
        (1 / (2 * Real.cosh (Real.log m))) * (Real.exp (l * v) * P (v + 2 * Real.log m)) := by
    funext v; unfold hyperbolicFilterProfile; ring
  rw [e]
  exact (hP.sub (h1.const_mul _)).sub (h2.const_mul _)

theorem integral_exp_mul_hyperbolicFilterProfile (m : ℕ) {P : ℝ → ℝ} {l : ℝ}
    (hP : Integrable fun v => Real.exp (l * v) * P v) :
    ∫ v, Real.exp (l * v) * hyperbolicFilterProfile m P v =
      (1 - Real.cosh (l * (2 * Real.log m)) / Real.cosh (Real.log m)) *
        ∫ v, Real.exp (l * v) * P v := by
  have hshift : ∀ w, Integrable fun v => Real.exp (l * v) * P (v - w) := fun w => by
    have h := (hP.comp_sub_right w).const_mul (Real.exp (l * w))
    refine h.congr (Eventually.of_forall fun v => ?_)
    simp only
    rw [show l * v = l * w + l * (v - w) by ring, Real.exp_add]; ring
  have hishift : ∀ w, ∫ v, Real.exp (l * v) * P (v - w) =
      Real.exp (l * w) * ∫ v, Real.exp (l * v) * P v := fun w => by
    rw [← integral_add_right_eq_self (μ := volume)
      (fun v => Real.exp (l * v) * P (v - w)) w, ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun v => ?_)
    simp only
    rw [add_sub_cancel_right, show l * (v + w) = l * w + l * v by ring, Real.exp_add]; ring
  have h1 := hshift (2 * Real.log m)
  have h2 : Integrable fun v => Real.exp (l * v) * P (v + 2 * Real.log m) := by
    have e : (fun v => Real.exp (l * v) * P (v + 2 * Real.log m)) =
        fun v => Real.exp (l * v) * P (v - (-(2 * Real.log m))) := by
      funext v; rw [sub_neg_eq_add]
    rw [e]; exact hshift (-(2 * Real.log m))
  have h01 : Integrable fun v =>
      Real.exp (l * v) * P v -
        (1 / (2 * Real.cosh (Real.log m))) * (Real.exp (l * v) * P (v - 2 * Real.log m)) :=
    hP.sub (h1.const_mul _)
  have e : (fun v => Real.exp (l * v) * hyperbolicFilterProfile m P v) = fun v =>
      Real.exp (l * v) * P v -
        (1 / (2 * Real.cosh (Real.log m))) * (Real.exp (l * v) * P (v - 2 * Real.log m)) -
        (1 / (2 * Real.cosh (Real.log m))) * (Real.exp (l * v) * P (v + 2 * Real.log m)) := by
    funext v; unfold hyperbolicFilterProfile; ring
  have e2 : ∫ v, Real.exp (l * v) * P (v + 2 * Real.log m) =
      Real.exp (-(l * (2 * Real.log m))) * ∫ v, Real.exp (l * v) * P v := by
    have esub : (fun v => Real.exp (l * v) * P (v + 2 * Real.log m)) =
        fun v => Real.exp (l * v) * P (v - (-(2 * Real.log m))) := by
      funext v; rw [sub_neg_eq_add]
    rw [esub, hishift, mul_neg]
  rw [e, integral_sub h01 (h2.const_mul _),
    integral_sub hP (h1.const_mul _),
    integral_const_mul, integral_const_mul,
    hishift, e2, Real.cosh_eq (l * (2 * Real.log m))]
  ring

/-- **Inductive strip-edge vanishing order increment (`d ↦ d + 1`):**
Each application of `hyperbolicFilterProfile m` multiplies the strip Laplace/Mellin bound by
`2 log m · (1/2 − l)`, incrementing the strip-edge vanishing exponent by `+1`. -/
theorem abs_integral_exp_mul_hyperbolicFilterProfile_le {m : ℕ} (hm : 1 ≤ m) {P : ℝ → ℝ}
    {l : ℝ} (hl0 : 0 ≤ l) (hl : l ≤ 1 / 2)
    (hP : Integrable fun v => Real.exp (l * v) * P v)
    {D : ℝ} {d : ℕ} (hbound : |∫ v, Real.exp (l * v) * P v| ≤ D * (1 / 2 - l) ^ d) :
    |∫ v, Real.exp (l * v) * hyperbolicFilterProfile m P v| ≤
      (2 * Real.log m * D) * (1 / 2 - l) ^ (d + 1) := by
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hb2 : 0 ≤ 2 * Real.log m := mul_nonneg zero_le_two (Real.log_nonneg hm1)
  obtain ⟨hlo, hhi⟩ := one_sub_cosh_div_le hb2 hl0 hl
  have hdiv : 2 * Real.log m / 2 = Real.log m := by ring
  rw [hdiv] at hlo hhi
  rw [integral_exp_mul_hyperbolicFilterProfile m hP, abs_mul, abs_of_nonneg hlo]
  calc (1 - Real.cosh (l * (2 * Real.log m)) / Real.cosh (Real.log m)) *
        |∫ v, Real.exp (l * v) * P v|
      ≤ (2 * Real.log m * (1 / 2 - l)) * (D * (1 / 2 - l) ^ d) :=
        mul_le_mul hhi hbound (abs_nonneg _) (by positivity)
    _ = (2 * Real.log m * D) * (1 / 2 - l) ^ (d + 1) := by rw [pow_succ]; ring

/-- **Inductive sublattice blindness multiplication (`N ↦ m² N`):**
If `f'` is blind on the `N`-sublattice `arcFreq (N(j+1) − 1)`, then `hyperbolicFilterDeriv m f'`
is blind on the `(m² N)`-sublattice `arcFreq (m² N(j+1) − 1)` for all `j ∈ ℕ`. -/
theorem integral_hyperbolicFilterDeriv_mul_sin_sublattice_eq_zero {m N : ℕ}
    (hm : 1 ≤ m) (hN : 1 ≤ N) {f' : ℝ → ℝ} (hf' : Integrable f')
    (hblind : ∀ j : ℕ, ∫ x, f' x * Real.sin (arcFreq (N * (j + 1) - 1) * x) = 0)
    (j : ℕ) :
    ∫ x, hyperbolicFilterDeriv m f' x *
      Real.sin (arcFreq ((m ^ 2 * N) * (j + 1) - 1) * x) = 0 := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (lt_of_lt_of_le zero_lt_one hm)
  have hmne : (m : ℝ) ≠ 0 := hmpos.ne'
  have hm2 : 1 ≤ m ^ 2 := Nat.one_le_pow 2 m hm
  set c := arcFreq ((m ^ 2 * N) * (j + 1) - 1)
  have h0_int : Integrable fun x => f' x * Real.sin (c * x) :=
    hf'.mul_bdd (by fun_prop) (Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs]; exact Real.abs_sin_le_one _)
  have h1_int : Integrable fun x =>
      ((m : ℝ) ^ 3)⁻¹ * f' (x * ((m : ℝ) ^ 2)⁻¹) * Real.sin (c * x) :=
    ((hf'.comp_mul_right' (inv_ne_zero (pow_ne_zero 2 hmne))).const_mul _).mul_bdd
      (by fun_prop) (Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs]; exact Real.abs_sin_le_one _)
  have h2_int : Integrable fun x =>
      (m : ℝ) ^ 3 * f' ((m : ℝ) ^ 2 * x) * Real.sin (c * x) :=
    ((hf'.comp_mul_left' (pow_ne_zero 2 hmne)).const_mul _).mul_bdd
      (by fun_prop) (Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs]; exact Real.abs_sin_le_one _)
  have h0_eq : ∫ x, f' x * Real.sin (c * x) = 0 := by
    have heq : (m ^ 2 * N) * (j + 1) - 1 = N * ((m ^ 2 * (j + 1) - 1) + 1) - 1 := by
      have h1 : 1 ≤ m ^ 2 * (j + 1) := Nat.mul_pos hm2 (Nat.succ_pos j)
      rw [Nat.sub_add_cancel h1]; ring_nf
    change ∫ x, f' x * Real.sin (arcFreq ((m ^ 2 * N) * (j + 1) - 1) * x) = 0
    rw [heq]
    exact hblind _
  have h1_eq : ∫ x, ((m : ℝ) ^ 3)⁻¹ * f' (x * ((m : ℝ) ^ 2)⁻¹) * Real.sin (c * x) = 0 := by
    have hfreq : c * (m : ℝ) ^ 2 = arcFreq (N * ((m ^ 4 * (j + 1) - 1) + 1) - 1) := by
      have h1 : 1 ≤ m ^ 4 * (j + 1) := Nat.mul_pos (Nat.one_le_pow 4 m hm) (Nat.succ_pos j)
      have h2 : 1 ≤ (m ^ 2 * N) * (j + 1) :=
        Nat.mul_pos (Nat.mul_pos hm2 hN) (Nat.succ_pos j)
      rw [Nat.sub_add_cancel h1]
      change arcFreq ((m ^ 2 * N) * (j + 1) - 1) * (m : ℝ) ^ 2 = _
      rw [show (m : ℝ) ^ 2 = ((m ^ 2 : ℕ) : ℝ) by push_cast; ring,
        arcFreq_mul_nat hm2, Nat.sub_add_cancel h2]
      congr 1; ring_nf
    have e : (fun x => ((m : ℝ) ^ 3)⁻¹ * f' (x * ((m : ℝ) ^ 2)⁻¹) * Real.sin (c * x)) =
        fun x => ((m : ℝ) ^ 3)⁻¹ * (f' (x * ((m : ℝ) ^ 2)⁻¹) *
          Real.sin (arcFreq (N * ((m ^ 4 * (j + 1) - 1) + 1) - 1) * (x * ((m : ℝ) ^ 2)⁻¹))) := by
      funext x
      rw [← hfreq]
      have hx : c * (m : ℝ) ^ 2 * (x * ((m : ℝ) ^ 2)⁻¹) = c * x := by field_simp
      rw [hx]; ring
    rw [e, integral_const_mul, Measure.integral_comp_mul_right
      (fun t => f' t * Real.sin (arcFreq (N * ((m ^ 4 * (j + 1) - 1) + 1) - 1) * t))
      (((m : ℝ) ^ 2)⁻¹), hblind _, smul_zero, mul_zero]
  have h2_eq : ∫ x, (m : ℝ) ^ 3 * f' ((m : ℝ) ^ 2 * x) * Real.sin (c * x) = 0 := by
    have hfreq : c / (m : ℝ) ^ 2 = arcFreq (N * (j + 1) - 1) := by
      have h1 : 1 ≤ N * (j + 1) := Nat.mul_pos hN (Nat.succ_pos j)
      have heq : (m ^ 2 * N) * (j + 1) - 1 = ((N * (j + 1) - 1) + 1) * m ^ 2 - 1 := by
        rw [Nat.sub_add_cancel h1]; ring_nf
      change arcFreq ((m ^ 2 * N) * (j + 1) - 1) / (m : ℝ) ^ 2 = _
      rw [heq, ← arcFreq_mul_nat hm2 (N * (j + 1) - 1)]
      push_cast; field_simp
    have e : (fun x => (m : ℝ) ^ 3 * f' ((m : ℝ) ^ 2 * x) * Real.sin (c * x)) =
        fun x => (m : ℝ) ^ 3 * (f' ((m : ℝ) ^ 2 * x) *
          Real.sin (arcFreq (N * (j + 1) - 1) * ((m : ℝ) ^ 2 * x))) := by
      funext x
      rw [← hfreq]
      have hx : c / (m : ℝ) ^ 2 * ((m : ℝ) ^ 2 * x) = c * x := by field_simp
      rw [hx]; ring
    rw [e, integral_const_mul, Measure.integral_comp_mul_left
      (fun t => f' t * Real.sin (arcFreq (N * (j + 1) - 1) * t)) ((m : ℝ) ^ 2),
      hblind j, smul_zero, mul_zero]
  have h01_int : Integrable fun x =>
      f' x * Real.sin (c * x) -
        (1 / (2 * Real.cosh (Real.log m))) *
          (((m : ℝ) ^ 3)⁻¹ * f' (x * ((m : ℝ) ^ 2)⁻¹) * Real.sin (c * x)) :=
    h0_int.sub (h1_int.const_mul _)
  have e : (fun x => hyperbolicFilterDeriv m f' x * Real.sin (c * x)) = fun x =>
      f' x * Real.sin (c * x) -
        (1 / (2 * Real.cosh (Real.log m))) *
          (((m : ℝ) ^ 3)⁻¹ * f' (x * ((m : ℝ) ^ 2)⁻¹) * Real.sin (c * x)) -
        (1 / (2 * Real.cosh (Real.log m))) *
          ((m : ℝ) ^ 3 * f' ((m : ℝ) ^ 2 * x) * Real.sin (c * x)) := by
    funext x; unfold hyperbolicFilterDeriv; ring
  rw [e, integral_sub h01_int (h2_int.const_mul _),
    integral_sub h0_int (h1_int.const_mul _),
    integral_const_mul, integral_const_mul, h0_eq, h1_eq, h2_eq,
    mul_zero, sub_zero, sub_zero]

/-! ### The arbitrary-order iterated tower `(arcLineTowerVector k d ν, d ∈ ℕ)` -/

/-- Level `d` of the iterated hyperbolic pole-filtered modular arc line vector tower. -/
def arcLineTowerVector (k : ℕ) : ℕ → Measure ArcParam → ℝ → ℝ
  | 0, ν => arcLineAtomicVector (Real.log k) ν
  | d + 1, ν => hyperbolicFilterVec k (arcLineTowerVector k d ν)

/-- Level `d` derivative of the iterated tower. -/
def arcLineTowerDeriv (k : ℕ) : ℕ → Measure ArcParam → ℝ → ℝ
  | 0, ν => arcLineAtomicDeriv (Real.log k) ν
  | d + 1, ν => hyperbolicFilterDeriv k (arcLineTowerDeriv k d ν)

/-- Level `d` log-scale profile of the iterated tower. -/
def arcLineTowerProfile (k : ℕ) : ℕ → Measure ArcParam → ℝ → ℝ
  | 0, ν => arcLineAtomicProfile (Real.log k) ν
  | d + 1, ν => hyperbolicFilterProfile k (arcLineTowerProfile k d ν)

theorem hasDerivAt_arcLineTowerVector (k d : ℕ) (ν : Measure ArcParam) [IsFiniteMeasure ν] :
    ∀ x, HasDerivAt (arcLineTowerVector k d ν) (arcLineTowerDeriv k d ν x) x := by
  induction d with
  | zero => exact hasDerivAt_arcLineAtomicVector (Real.log k) ν
  | succ d ih => exact hasDerivAt_hyperbolicFilterVec k ih

theorem arcLineTowerVector_neg_of_map_arcNeg (k d : ℕ) {ν : Measure ArcParam}
    (hν : ν.map arcNeg = ν) :
    ∀ x, arcLineTowerVector k d ν (-x) = arcLineTowerVector k d ν x := by
  induction d with
  | zero => exact arcLineAtomicVector_neg_of_map_arcNeg (Real.log k) hν
  | succ d ih => exact hyperbolicFilterVec_neg k ih

theorem arcLineTowerProfile_neg (k d : ℕ) (ν : Measure ArcParam) :
    ∀ v, arcLineTowerProfile k d ν (-v) = arcLineTowerProfile k d ν v := by
  induction d with
  | zero => exact arcLineAtomicProfile_neg (Real.log k) ν
  | succ d ih => exact hyperbolicFilterProfile_neg k ih

theorem arcLineTowerVector_inv {k : ℕ} (hk : 1 ≤ k) (d : ℕ) (ν : Measure ArcParam) :
    ∀ x, x ≠ 0 → arcLineTowerVector k d ν (1 / x) = |x| * arcLineTowerVector k d ν x := by
  induction d with
  | zero => exact fun x hx => arcLineAtomicVector_inv (Real.log k) ν hx
  | succ d ih => exact fun x hx => hyperbolicFilterVec_inv hk ih hx

theorem exp_half_mul_arcLineTowerVector {k : ℕ} (hk : 1 ≤ k) (d : ℕ) (ν : Measure ArcParam) :
    ∀ v, Real.exp (v / 2) * arcLineTowerVector k d ν (Real.exp v) =
      arcLineTowerProfile k d ν v := by
  induction d with
  | zero => exact exp_half_mul_arcLineAtomicVector (Real.log k) ν
  | succ d ih => exact exp_half_mul_hyperbolicFilterVec hk ih

theorem integrable_arcLineTowerVector {k : ℕ} (hk : 1 ≤ k) (d : ℕ)
    {ν : Measure ArcParam} [IsFiniteMeasure ν] (hν : ν.map arcNeg = ν) :
    Integrable (arcLineTowerVector k d ν) := by
  induction d with
  | zero =>
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
    exact integrable_arcLineAtomicVector (Real.log_nonneg hk1) hν
  | succ d ih => exact integrable_hyperbolicFilterVec hk ih

theorem integrable_arcLineTowerDeriv {k : ℕ} (hk : 1 ≤ k) (d : ℕ)
    (ν : Measure ArcParam) [IsFiniteMeasure ν] :
    Integrable (arcLineTowerDeriv k d ν) := by
  induction d with
  | zero => exact integrable_arcLineAtomicDeriv (Real.log k) ν
  | succ d ih => exact integrable_hyperbolicFilterDeriv hk ih

theorem integrable_arcLineTowerProfile (k d : ℕ) (ν : Measure ArcParam) [IsFiniteMeasure ν] :
    Integrable (arcLineTowerProfile k d ν) := by
  induction d with
  | zero => exact integrable_arcLineAtomicProfile (Real.log k) ν
  | succ d ih => exact integrable_hyperbolicFilterProfile k ih

theorem integral_arcLineTowerVector_eq_zero {k : ℕ} (hk : 1 ≤ k) (d : ℕ)
    {ν : Measure ArcParam} [IsFiniteMeasure ν] (hν : ν.map arcNeg = ν) :
    ∫ x, arcLineTowerVector k d ν x = 0 := by
  induction d with
  | zero =>
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
    exact integral_arcLineAtomicVector_eq_zero (Real.log_nonneg hk1) hν
  | succ d ih =>
    exact integral_hyperbolicFilterVec_eq_zero hk (integrable_arcLineTowerVector hk d hν) ih

/-- **Strict positive definiteness on the critical line at every tower level `d ∈ ℕ`.** -/
theorem integral_cos_mul_arcLineTowerProfile_pos {k : ℕ} (hk : 2 ≤ k) (d : ℕ)
    (ν : Measure ArcParam) [IsFiniteMeasure ν]
    (hpd : ∀ τ : ℝ, 0 < ∫ v, Real.cos (τ * v) * arcPoissonProfile ν v) (τ : ℝ) :
    0 < ∫ v, Real.cos (τ * v) * arcLineTowerProfile k d ν v := by
  induction d with
  | zero =>
    have hkgt1 : (1 : ℝ) < k := by exact_mod_cast (lt_of_lt_of_le one_lt_two hk)
    exact integral_cos_mul_arcLineAtomicProfile_pos (Real.log_pos hkgt1) ν hpd τ
  | succ d ih =>
    exact integral_cos_mul_hyperbolicFilterProfile_pos hk
      (integrable_arcLineTowerProfile k d ν) (arcLineTowerProfile_neg k d ν) ih

theorem integrable_exp_mul_arcLineTowerProfile (k d : ℕ)
    {ν : Measure ArcParam} [IsFiniteMeasure ν] (hν : ν.map arcNeg = ν)
    {l : ℝ} (hl0 : 0 ≤ l) (hl : l < 1 / 2) :
    Integrable fun v => Real.exp (l * v) * arcLineTowerProfile k d ν v := by
  induction d with
  | zero => exact integrable_exp_mul_arcLineAtomicProfile (Real.log k) hν hl0 hl
  | succ d ih => exact integrable_exp_mul_hyperbolicFilterProfile k ih

/-- **Arbitrary-order `(1/2 − l)^{d+1}` strip-edge vanishing bound at tower level `d ∈ ℕ`.** -/
theorem abs_integral_exp_mul_arcLineTowerProfile_le {k : ℕ} (hk : 1 ≤ k) (d : ℕ)
    {ν : Measure ArcParam} [IsFiniteMeasure ν] (hν : ν.map arcNeg = ν)
    {l : ℝ} (hl0 : 0 ≤ l) (hl : l < 1 / 2) :
    |∫ v, Real.exp (l * v) * arcLineTowerProfile k d ν v| ≤
      10 * ν.real univ * (Real.log k) ^ 2 * (2 * Real.log k) ^ d *
        (1 / 2 - l) ^ (d + 1) := by
  induction d with
  | zero =>
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
    have hb : 0 ≤ Real.log k := Real.log_nonneg hk1
    obtain ⟨hlo, hhi⟩ := one_sub_cosh_div_le hb hl0 hl.le
    have hQ := abs_integral_exp_mul_arcPoissonProfile_le hν hl0 hl
    have hκ : 0 < 1 / 2 - l := by linarith
    change |∫ v, Real.exp (l * v) * arcLineAtomicProfile (Real.log k) ν v| ≤ _
    rw [integral_exp_mul_arcLineAtomicProfile (Real.log k) hν hl0 hl, abs_mul,
      abs_of_nonneg (sq_nonneg _), pow_zero, mul_one, pow_one]
    calc (1 - Real.cosh (l * Real.log k) / Real.cosh (Real.log k / 2)) ^ 2 *
          |∫ v, Real.exp (l * v) * arcPoissonProfile ν v|
        ≤ (Real.log k * (1 / 2 - l)) ^ 2 * (10 * ν.real univ / (1 / 2 - l)) :=
          mul_le_mul (pow_le_pow_left₀ hlo hhi 2) hQ (abs_nonneg _) (sq_nonneg _)
      _ = 10 * ν.real univ * (Real.log k) ^ 2 * (1 / 2 - l) := by field_simp
  | succ d ih =>
    have hstep := abs_integral_exp_mul_hyperbolicFilterProfile_le hk hl0 hl.le
      (integrable_exp_mul_arcLineTowerProfile k d hν hl0 hl) ih
    refine hstep.trans_eq ?_
    rw [pow_succ]
    ring

/-- **Order-`d` divided-difference vanishing at the strip edge `l → (1/2)⁻`.** -/
theorem tendsto_div_pow_integral_exp_mul_arcLineTowerProfile_nhdsWithin
    {k : ℕ} (hk : 1 ≤ k) (d : ℕ)
    {ν : Measure ArcParam} [IsFiniteMeasure ν] (hν : ν.map arcNeg = ν) :
    Tendsto (fun l : ℝ =>
      (∫ v, Real.exp (l * v) * arcLineTowerProfile k d ν v) / (1 / 2 - l) ^ d)
      (𝓝[<] (1 / 2)) (𝓝 0) := by
  set D := 10 * ν.real univ * (Real.log k) ^ 2 * (2 * Real.log k) ^ d
  have hlin : Tendsto (fun l : ℝ => D * (1 / 2 - l)) (𝓝[<] (1 / 2)) (𝓝 0) := by
    have hcont : Continuous fun l : ℝ => D * (1 / 2 - l) := by fun_prop
    have h := (hcont.continuousAt (x := (1 / 2 : ℝ))).tendsto.mono_left
      (nhdsWithin_le_nhds (s := Iio (1 / 2 : ℝ)))
    rwa [sub_self, mul_zero] at h
  refine squeeze_zero_norm' ?_ hlin
  have hmem : Ioo (0 : ℝ) (1 / 2) ∈ 𝓝[<] (1 / 2 : ℝ) :=
    Ioo_mem_nhdsLT (by norm_num : (0 : ℝ) < 1 / 2)
  filter_upwards [hmem] with l hl
  have hκ : 0 < 1 / 2 - l := by linarith [hl.2]
  have hpow : 0 < (1 / 2 - l) ^ d := pow_pos hκ d
  rw [Real.norm_eq_abs, abs_div, abs_of_pos hpow, div_le_iff₀ hpow]
  calc |∫ v, Real.exp (l * v) * arcLineTowerProfile k d ν v|
      ≤ D * (1 / 2 - l) ^ (d + 1) :=
        abs_integral_exp_mul_arcLineTowerProfile_le hk d hν hl.1.le hl.2
    _ = D * (1 / 2 - l) * (1 / 2 - l) ^ d := by rw [pow_succ']; ring

/-- **Exact `k^{2(d+1)}`-sublattice blindness at tower level `d ∈ ℕ`.** -/
theorem integral_arcLineTowerDeriv_mul_sin_sublattice_eq_zero
    {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hblind : ∀ n : ℕ, ∫ t, arcLineDeriv ν t * Real.sin (arcFreq n * t) = 0)
    {k : ℕ} (hk : 1 ≤ k) (d j : ℕ) :
    ∫ x, arcLineTowerDeriv k d ν x *
      Real.sin (arcFreq (k ^ (2 * (d + 1)) * (j + 1) - 1) * x) = 0 := by
  induction d generalizing j with
  | zero =>
    simpa [arcLineTowerDeriv] using integral_arcLineAtomicDeriv_log_mul_sin_sq_mul_eq_zero hblind hk j
  | succ d ih =>
    have hpow : k ^ (2 * (d + 1 + 1)) = k ^ 2 * k ^ (2 * (d + 1)) := by
      rw [show 2 * (d + 1 + 1) = 2 + 2 * (d + 1) by ring, pow_add]
    rw [hpow]
    exact integral_hyperbolicFilterDeriv_mul_sin_sublattice_eq_zero hk
      (Nat.one_le_pow _ k hk) (integrable_arcLineTowerDeriv hk d ν) ih j

/-- **Master unconditional arbitrary-order strip-edge and sublattice tower theorem.**
There exists a finite nonzero `arcNeg`-symmetric measure `ν` on the modular bottom arc such that
for every integer `k ≥ 2` and every order `d ∈ ℕ`, `arcLineTowerVector k d ν` is an even,
strictly self-reciprocal, zero-mean, strictly positive definite function on the critical line
whose derivative is blind along the infinite `k^{2(d+1)}`-sublattice and whose strip
Laplace/Mellin transform vanishes to order `(1/2 − l)^{d+1}` at the critical strip edge
`l → (1/2)⁻`, with vanishing `d`-th divided difference on `𝓝[<] (1/2)`. -/
theorem exists_arbitraryOrder_stripEdge_sublattice_arcWitness :
    ∃ ν : Measure ArcParam, IsFiniteMeasure ν ∧ ν ≠ 0 ∧ ν.map arcNeg = ν ∧
      ∀ k : ℕ, 2 ≤ k → ∀ d : ℕ,
        (∀ x, arcLineTowerVector k d ν (-x) = arcLineTowerVector k d ν x) ∧
        (∀ x, x ≠ 0 → arcLineTowerVector k d ν (1 / x) =
          |x| * arcLineTowerVector k d ν x) ∧
        ∫ x, arcLineTowerVector k d ν x = 0 ∧
        (∀ j : ℕ, ∫ x, arcLineTowerDeriv k d ν x *
          Real.sin (arcFreq (k ^ (2 * (d + 1)) * (j + 1) - 1) * x) = 0) ∧
        (∀ τ : ℝ, 0 < ∫ v, Real.cos (τ * v) * arcLineTowerProfile k d ν v) ∧
        (∀ l : ℝ, 0 ≤ l → l < 1 / 2 →
          |∫ v, Real.exp (l * v) * arcLineTowerProfile k d ν v| ≤
            10 * ν.real univ * (Real.log k) ^ 2 * (2 * Real.log k) ^ d *
              (1 / 2 - l) ^ (d + 1)) ∧
        Tendsto (fun l : ℝ =>
          (∫ v, Real.exp (l * v) * arcLineTowerProfile k d ν v) / (1 / 2 - l) ^ d)
          (𝓝[<] (1 / 2)) (𝓝 0) := by
  obtain ⟨ν, hfin, hne, hsym, hblind_whittaker, hpd⟩ := exists_arcWitness
  have hblind : ∀ n : ℕ, ∫ t, arcLineDeriv ν t * Real.sin (arcFreq n * t) = 0 := fun n => by
    rw [integral_arcLineDeriv_mul_sin, (hblind_whittaker n).1, mul_zero, neg_zero]
  refine ⟨ν, hfin, hne, hsym, fun k hk d => ?_⟩
  have hk1 : 1 ≤ k := by omega
  exact ⟨arcLineTowerVector_neg_of_map_arcNeg k d hsym,
    arcLineTowerVector_inv hk1 d ν,
    integral_arcLineTowerVector_eq_zero hk1 d hsym,
    integral_arcLineTowerDeriv_mul_sin_sublattice_eq_zero hblind hk1 d,
    integral_cos_mul_arcLineTowerProfile_pos hk d ν hpd,
    fun l hl0 hl => abs_integral_exp_mul_arcLineTowerProfile_le hk1 d hsym hl0 hl,
    tendsto_div_pow_integral_exp_mul_arcLineTowerProfile_nhdsWithin hk1 d hsym⟩

end

end RHTower
