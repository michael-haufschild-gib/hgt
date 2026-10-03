import GaloisForLFunctions.RHTower.ChebyshevSchmidtOmega

/-!
# The Chebyshev window identity of the lag function

With `E = ψ - id`, `I(x) = ∫_x^∞ E(t) t^{-2} dt`, `S` the trivial-zero series and `Φ` the real lag
function, for `x > 1`

```text
Φ(log x) √x = -x I(x) - log 2π + S(x),
```

so the integral of `E(t) t^{-2}` over any window `(a, b]`, `1 < a ≤ b`, is a difference of lag
values.  A one-sided bound `E ≥ -A√t` (resp. `E ≤ A√t`) on a window `[X, Xe^h]` therefore
controls the lag difference

```text
Δ_h(v) = Φ(v + h) e^{-h/2} - Φ(v):     Δ_h(log X) ≥ -A h - 4/√X     (resp. ≤ A h + 4/√X).
```
-/

open MeasureTheory Set Filter Topology
open scoped Chebyshev

namespace RHTower

noncomputable section

theorem exp_neg_half_log {x : ℝ} (hx : 0 < x) : Real.exp (-Real.log x / 2) = 1 / Real.sqrt x := by
  have h1 : Real.exp (Real.log x / 2) = Real.sqrt x := by
    symm
    rw [Real.sqrt_eq_iff_mul_self_eq hx.le (Real.exp_pos _).le, ← Real.exp_add,
      show Real.log x / 2 + Real.log x / 2 = Real.log x by ring, Real.exp_log hx]
  rw [show -Real.log x / 2 = -(Real.log x / 2) by ring, Real.exp_neg, h1, one_div]

/-- **The lag function as a Chebyshev tail.**  `Φ(log x) √x = -x I(x) - log 2π + S(x)`. -/
theorem weilLagFunctionReal_log_mul_sqrt {x : ℝ} (hx : 1 < x) :
    weilLagFunctionReal (Real.log x) * Real.sqrt x
      = -(x * ∫ t in Ioi x, chebyshevError t / t ^ 2) - Real.log (2 * Real.pi)
        + trivialZeroSeriesReal x := by
  have hx0 : 0 < x := by linarith
  have hL : 0 < Real.log x := Real.log_pos hx
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx0
  rw [weilLagFunctionReal_eq_prime_side hL, Real.exp_log hx0, exp_neg_half_log hx0]
  have hdev := mertensDeviation_eq hx.le
  rw [← mertensSum_eq_Icc_zero] at hdev
  have hE : chebyshevError x = Chebyshev.psi x - x := rfl
  have h1 : x * (mertensSum ⌊x⌋₊ - Real.log x + Real.eulerMascheroniConstant)
      = chebyshevError x - x * ∫ t in Ioi x, chebyshevError t / t ^ 2 := by
    rw [hdev]; field_simp
  rw [h1, hE]
  field_simp
  ring

/-- The tail integral in terms of the lag function. -/
theorem integral_Ioi_chebyshevError_div_sq_eq {x : ℝ} (hx : 1 < x) :
    ∫ t in Ioi x, chebyshevError t / t ^ 2
      = (-(weilLagFunctionReal (Real.log x) * Real.sqrt x) - Real.log (2 * Real.pi)
        + trivialZeroSeriesReal x) / x := by
  have hx0 : 0 < x := by linarith
  have h := weilLagFunctionReal_log_mul_sqrt hx
  rw [eq_div_iff hx0.ne']
  linarith

/-- The window integral is the difference of the tails. -/
theorem integral_Ioc_chebyshevError_div_sq {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    ∫ t in Ioc a b, chebyshevError t / t ^ 2
      = (∫ t in Ioi a, chebyshevError t / t ^ 2) - ∫ t in Ioi b, chebyshevError t / t ^ 2 := by
  have hint : IntegrableOn (fun t : ℝ => chebyshevError t / t ^ 2) (Ioi 1) :=
    integrableOn_chebyshevError_div_sq
  have hsplit := setIntegral_union (μ := volume) (f := fun t : ℝ => chebyshevError t / t ^ 2)
    Set.Ioc_disjoint_Ioi_same measurableSet_Ioi
    (hint.mono_set (Ioc_subset_Ioi_self.trans (Ioi_subset_Ioi ha)))
    (hint.mono_set (Ioi_subset_Ioi (le_trans ha hab)))
  rw [Set.Ioc_union_Ioi_eq_Ioi hab] at hsplit
  linarith

/-- `|S(x) - log 2π| ≤ 2` for `x ≥ 1`. -/
theorem abs_trivialZeroSeriesReal_sub_log_two_pi_le {x : ℝ} (hx : 1 ≤ x) :
    |trivialZeroSeriesReal x - Real.log (2 * Real.pi)| ≤ 2 := by
  have hS0 := trivialZeroSeriesReal_nonneg hx
  have hS1 := trivialZeroSeriesReal_le_one hx
  have hl1 := one_lt_log_two_pi
  have hl2 : Real.log (2 * Real.pi) ≤ 2 := by
    rw [Real.log_le_iff_le_exp (by positivity)]
    have h1 := Real.pi_lt_d2
    have h2 : (7.38 : ℝ) ≤ Real.exp 2 := by
      have := Real.exp_one_gt_d9
      have h3 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
      nlinarith
    linarith
  rw [abs_le]; constructor <;> linarith

/-- The algebra of the window identity, with `X = s²` and `b = s² e²`. -/
theorem lag_window_algebra {s e Φ₁ Φ₂ l S₁ S₂ : ℝ} (hs : 0 < s) (he : 0 < e) :
    s * ((-(Φ₁ * s) - l + S₁) / s ^ 2 - (-(Φ₂ * (s * e)) - l + S₂) / (s ^ 2 * e ^ 2))
      = Φ₂ * e⁻¹ - Φ₁ + s * ((S₁ - l) / s ^ 2 - (S₂ - l) / (s ^ 2 * e ^ 2)) := by
  field_simp
  ring

/-- **The window identity.**  For `1 < X` and `h > 0`, with `u = log X`,

`√X ∫_{(X, Xe^h]} E t^{-2} = Φ(u + h) e^{-h/2} - Φ(u) + R`,     `|R| ≤ 4/√X`. -/
theorem lag_window_identity {X h : ℝ} (hX : 1 < X) (hh : 0 ≤ h) :
    ∃ R : ℝ, |R| ≤ 4 / Real.sqrt X ∧
      Real.sqrt X * ∫ t in Ioc X (X * Real.exp h), chebyshevError t / t ^ 2
        = weilLagFunctionReal (Real.log X + h) * Real.exp (-(h / 2))
          - weilLagFunctionReal (Real.log X) + R := by
  have hX0 : 0 < X := by linarith
  have heh : 1 ≤ Real.exp h := Real.one_le_exp hh
  set b := X * Real.exp h with hb
  have hb1 : 1 < b := by rw [hb]; nlinarith
  have hb0 : 0 < b := by linarith
  have hXb : X ≤ b := by rw [hb]; nlinarith
  have hlogb : Real.log b = Real.log X + h := by
    rw [hb, Real.log_mul hX0.ne' (Real.exp_pos _).ne', Real.log_exp]
  have hsqb : Real.sqrt b = Real.sqrt X * Real.exp (h / 2) := by
    have he : Real.sqrt (Real.exp h) = Real.exp (h / 2) := by
      rw [Real.sqrt_eq_iff_mul_self_eq (Real.exp_pos _).le (Real.exp_pos _).le, ← Real.exp_add]
      congr 1; ring
    rw [hb, Real.sqrt_mul hX0.le, he]
  rw [integral_Ioc_chebyshevError_div_sq hX.le hXb]
  rw [integral_Ioi_chebyshevError_div_sq_eq hX, integral_Ioi_chebyshevError_div_sq_eq hb1, hlogb]
  have hsX : 0 < Real.sqrt X := Real.sqrt_pos.mpr hX0
  have hsqX : Real.sqrt X * Real.sqrt X = X := Real.mul_self_sqrt hX0.le
  have hEh : Real.exp (h / 2) * Real.exp (-(h / 2)) = 1 := by rw [← Real.exp_add]; simp
  set R := Real.sqrt X * ((trivialZeroSeriesReal X - Real.log (2 * Real.pi)) / X
      - (trivialZeroSeriesReal b - Real.log (2 * Real.pi)) / b) with hR
  refine ⟨R, ?_, ?_⟩
  · have h1 := abs_trivialZeroSeriesReal_sub_log_two_pi_le hX.le
    have h2 := abs_trivialZeroSeriesReal_sub_log_two_pi_le hb1.le
    have h3 : |(trivialZeroSeriesReal X - Real.log (2 * Real.pi)) / X| ≤ 2 / X := by
      rw [abs_div, abs_of_pos hX0]; exact div_le_div_of_nonneg_right h1 hX0.le
    have h4 : |(trivialZeroSeriesReal b - Real.log (2 * Real.pi)) / b| ≤ 2 / X := by
      rw [abs_div, abs_of_pos hb0]
      exact le_trans (div_le_div_of_nonneg_right h2 hb0.le) (div_le_div_of_nonneg_left
        (by norm_num) hX0 hXb)
    have h5 : |R| ≤ Real.sqrt X * (4 / X) := by
      rw [hR, abs_mul, abs_of_pos hsX]
      refine mul_le_mul_of_nonneg_left ?_ hsX.le
      calc |(trivialZeroSeriesReal X - Real.log (2 * Real.pi)) / X
            - (trivialZeroSeriesReal b - Real.log (2 * Real.pi)) / b|
          ≤ |(trivialZeroSeriesReal X - Real.log (2 * Real.pi)) / X|
            + |(trivialZeroSeriesReal b - Real.log (2 * Real.pi)) / b| := abs_sub _ _
        _ ≤ 2 / X + 2 / X := add_le_add h3 h4
        _ = 4 / X := by ring
    have h6 : Real.sqrt X * (4 / X) = 4 / Real.sqrt X := by
      have h7 : Real.sqrt X / X = 1 / Real.sqrt X := by
        rw [div_eq_div_iff hX0.ne' hsX.ne']; linarith [hsqX]
      calc Real.sqrt X * (4 / X) = 4 * (Real.sqrt X / X) := by ring
        _ = 4 / Real.sqrt X := by rw [h7]; ring
    linarith
  · have hX2 : Real.sqrt X ^ 2 = X := Real.sq_sqrt hX0.le
    have heh2 : Real.exp (h / 2) ^ 2 = Real.exp h := by
      rw [← Real.exp_nat_mul]; push_cast; ring_nf
    have hbe : X * Real.exp (h / 2) ^ 2 = b := by rw [heh2]
    have key := lag_window_algebra (s := Real.sqrt X) (e := Real.exp (h / 2))
      (Φ₁ := weilLagFunctionReal (Real.log X)) (Φ₂ := weilLagFunctionReal (Real.log X + h))
      (l := Real.log (2 * Real.pi)) (S₁ := trivialZeroSeriesReal X)
      (S₂ := trivialZeroSeriesReal b) hsX (Real.exp_pos _)
    rw [hX2, hbe] at key
    rw [hsqb, hR, Real.exp_neg]
    rw [show -(weilLagFunctionReal (Real.log X) * Real.sqrt X) - Real.log (2 * Real.pi)
        + trivialZeroSeriesReal X = -(weilLagFunctionReal (Real.log X) * Real.sqrt X)
        - Real.log (2 * Real.pi) + trivialZeroSeriesReal X from rfl]
    linarith [key]


/-- `√X ∫_{(X, Xe^h]} √t/t² dt = 2(1 - e^{-h/2}) ≤ h`. -/
theorem sqrt_mul_integral_Ioc_sqrt_div_sq_le {X h : ℝ} (hX : 0 < X) (hh : 0 ≤ h) :
    Real.sqrt X * ∫ t in Ioc X (X * Real.exp h), Real.sqrt t / t ^ 2 ≤ h ∧
      0 ≤ ∫ t in Ioc X (X * Real.exp h), Real.sqrt t / t ^ 2 := by
  have heh : 1 ≤ Real.exp h := Real.one_le_exp hh
  set b := X * Real.exp h with hb
  have hb0 : 0 < b := by positivity
  have hXb : X ≤ b := by rw [hb]; nlinarith
  have hsplit := setIntegral_union (μ := volume) (f := fun t : ℝ => Real.sqrt t / t ^ 2)
    Set.Ioc_disjoint_Ioi_same measurableSet_Ioi
    ((integrableOn_Ioi_sqrt_div_sq hX).mono_set Ioc_subset_Ioi_self)
    ((integrableOn_Ioi_sqrt_div_sq hX).mono_set (Ioi_subset_Ioi hXb))
  rw [Set.Ioc_union_Ioi_eq_Ioi hXb, integral_Ioi_sqrt_div_sq hX,
    integral_Ioi_sqrt_div_sq hb0] at hsplit
  have hsqb : Real.sqrt b = Real.sqrt X * Real.exp (h / 2) := by
    have he : Real.sqrt (Real.exp h) = Real.exp (h / 2) := by
      rw [Real.sqrt_eq_iff_mul_self_eq (Real.exp_pos _).le (Real.exp_pos _).le, ← Real.exp_add]
      congr 1; ring
    rw [hb, Real.sqrt_mul hX.le, he]
  have hsX : 0 < Real.sqrt X := Real.sqrt_pos.mpr hX
  have heh2 : 1 ≤ Real.exp (h / 2) := Real.one_le_exp (by linarith)
  have hJ : ∫ t in Ioc X b, Real.sqrt t / t ^ 2 = 2 / Real.sqrt X - 2 / Real.sqrt b := by linarith
  have hval : Real.sqrt X * (2 / Real.sqrt X - 2 / Real.sqrt b)
      = 2 * (1 - Real.exp (-(h / 2))) := by
    rw [hsqb, Real.exp_neg]; field_simp
  have hexp : 1 - h / 2 ≤ Real.exp (-(h / 2)) := by
    have := Real.add_one_le_exp (-(h / 2)); linarith
  refine ⟨?_, ?_⟩
  · rw [hJ, hval]; linarith
  · rw [hJ, hsqb]
    have : 2 / (Real.sqrt X * Real.exp (h / 2)) ≤ 2 / Real.sqrt X :=
      div_le_div_of_nonneg_left (by norm_num) hsX (by nlinarith)
    linarith

/-- **Prime side, lower window.**  If `-A√t ≤ E(t)` on `(X, Xe^h]` then
`Δ_h(log X) ≥ -A h - 4/√X`. -/
theorem lagDifference_ge_of_chebyshevError_lower {X h A : ℝ} (hX : 1 < X) (hh : 0 ≤ h)
    (hA : 0 ≤ A) (hlow : ∀ t ∈ Ioc X (X * Real.exp h), -(A * Real.sqrt t) ≤ chebyshevError t) :
    -(A * h) - 4 / Real.sqrt X
      ≤ weilLagFunctionReal (Real.log X + h) * Real.exp (-(h / 2))
        - weilLagFunctionReal (Real.log X) := by
  obtain ⟨R, hR, hid⟩ := lag_window_identity hX hh
  have hX0 : 0 < X := by linarith
  have hsX : 0 < Real.sqrt X := Real.sqrt_pos.mpr hX0
  obtain ⟨hJ, hJ0⟩ := sqrt_mul_integral_Ioc_sqrt_div_sq_le hX0 hh
  have hint1 : IntegrableOn (fun t : ℝ => chebyshevError t / t ^ 2) (Ioc X (X * Real.exp h)) :=
    integrableOn_chebyshevError_div_sq.mono_set (Ioc_subset_Ioi_self.trans (Ioi_subset_Ioi hX.le))
  have hint2 : IntegrableOn (fun t : ℝ => -A * (Real.sqrt t / t ^ 2)) (Ioc X (X * Real.exp h)) :=
    ((integrableOn_Ioi_sqrt_div_sq hX0).mono_set Ioc_subset_Ioi_self).const_mul (-A)
  have hmono := setIntegral_mono_on hint2 hint1 measurableSet_Ioc (fun t ht => by
    have ht0 : 0 < t := lt_trans hX0 ht.1
    have h1 := hlow t ht
    have h2 : -A * (Real.sqrt t / t ^ 2) = -(A * Real.sqrt t) / t ^ 2 := by ring
    rw [h2]
    exact div_le_div_of_nonneg_right h1 (by positivity))
  rw [integral_const_mul] at hmono
  have h3 := mul_le_mul_of_nonneg_left hmono hsX.le
  have h4 : Real.sqrt X * (-A * ∫ t in Ioc X (X * Real.exp h), Real.sqrt t / t ^ 2)
      = -A * (Real.sqrt X * ∫ t in Ioc X (X * Real.exp h), Real.sqrt t / t ^ 2) := by ring
  rw [h4] at h3
  have h5 : -A * h ≤ -A * (Real.sqrt X * ∫ t in Ioc X (X * Real.exp h), Real.sqrt t / t ^ 2) := by
    nlinarith
  have hR' := (abs_le.mp hR).2
  linarith

/-- **Prime side, upper window.**  If `E(t) ≤ A√t` on `(X, Xe^h]` then
`Δ_h(log X) ≤ A h + 4/√X`. -/
theorem lagDifference_le_of_chebyshevError_upper {X h A : ℝ} (hX : 1 < X) (hh : 0 ≤ h)
    (hA : 0 ≤ A) (hup : ∀ t ∈ Ioc X (X * Real.exp h), chebyshevError t ≤ A * Real.sqrt t) :
    weilLagFunctionReal (Real.log X + h) * Real.exp (-(h / 2)) - weilLagFunctionReal (Real.log X)
      ≤ A * h + 4 / Real.sqrt X := by
  obtain ⟨R, hR, hid⟩ := lag_window_identity hX hh
  have hX0 : 0 < X := by linarith
  have hsX : 0 < Real.sqrt X := Real.sqrt_pos.mpr hX0
  obtain ⟨hJ, hJ0⟩ := sqrt_mul_integral_Ioc_sqrt_div_sq_le hX0 hh
  have hint1 : IntegrableOn (fun t : ℝ => chebyshevError t / t ^ 2) (Ioc X (X * Real.exp h)) :=
    integrableOn_chebyshevError_div_sq.mono_set (Ioc_subset_Ioi_self.trans (Ioi_subset_Ioi hX.le))
  have hint2 : IntegrableOn (fun t : ℝ => A * (Real.sqrt t / t ^ 2)) (Ioc X (X * Real.exp h)) :=
    ((integrableOn_Ioi_sqrt_div_sq hX0).mono_set Ioc_subset_Ioi_self).const_mul A
  have hmono := setIntegral_mono_on hint1 hint2 measurableSet_Ioc (fun t ht => by
    have ht0 : 0 < t := lt_trans hX0 ht.1
    have h1 := hup t ht
    have h2 : A * (Real.sqrt t / t ^ 2) = A * Real.sqrt t / t ^ 2 := by ring
    rw [h2]
    exact div_le_div_of_nonneg_right h1 (by positivity))
  rw [integral_const_mul] at hmono
  have h3 := mul_le_mul_of_nonneg_left hmono hsX.le
  have h4 : Real.sqrt X * (A * ∫ t in Ioc X (X * Real.exp h), Real.sqrt t / t ^ 2)
      = A * (Real.sqrt X * ∫ t in Ioc X (X * Real.exp h), Real.sqrt t / t ^ 2) := by ring
  rw [h4] at h3
  have h5 : A * (Real.sqrt X * ∫ t in Ioc X (X * Real.exp h), Real.sqrt t / t ^ 2) ≤ A * h :=
    mul_le_mul_of_nonneg_left hJ hA
  have hR' := (abs_le.mp hR).1
  linarith

end

end RHTower
