import GaloisForLFunctions.RHTower.LittlewoodParameters
import GaloisForLFunctions.RHTower.WeilLagFunctionGrowthLower
import GaloisForLFunctions.RHTower.TransverseEquilibrium
import GaloisForLFunctions.RHTower.DivisorSliceFreePart
import GaloisForLFunctions.RHTower.XiHedenmalmMultiplicityChain

/-!
# Littlewood's oscillation theorem

```text
ψ(x) - x < -c √x · log log log x      for arbitrarily large x,      c = 1/(70π³),
```

unconditionally; under RH also `ψ(x) - x > c √x log log log x` infinitely often.

**Under RH.**  For large `y` put `h = 1/y`, `T = y²`, `Q = ⌈y²⌉` and use Dirichlet's theorem to find
`u = ky`, `1 ≤ k ≤ Q^{N_T}`, in phase with every zero `|γ| ≤ T`.  The aligned lag difference is
`Δ_{1/y}(u) ≤ -(1/(5π³)) log y / y` (`eventually_littlewood_zero_side_lower`).  If
`ψ(t) - t ≥ -A√t` on `(e^u, e^{u+1/y}]` with `A = log y/(10π³)`, the window identity gives
`Δ_{1/y}(u) ≥ -A/y - 4e^{-u/2}`, which is incompatible for large `y`.  Since
`log u ≤ N_T log Q + log y ≤ y⁷`, every `t` in the window has `log log log t ≤ 7 log y`, so the
failure point has `ψ(t) - t < -(1/(70π³))√t log log log t`.

**Without RH.**  A bound `ψ(t) - t ≥ -c√t log log log t` gives `Φ(L) ≤ M e^{aL}` for every `a > 0`,
so every zero has real part at most `½ + a` (`re_le_half_add_of_weilLagFunctionReal_le_exp`), which
is RH.
-/

open MeasureTheory Set Filter Topology

namespace RHTower

noncomputable section

/-- The polynomial ceiling of the alignment exponent. -/
theorem eventually_littlewood_size : ∀ᶠ y : ℝ in atTop,
    1 + 8 * (1 + (y ^ 2) ^ 2) * (xiLineTwoLogDerivConstant + Real.log 4) * Real.log (y ^ 2 + 1)
      + Real.log y ≤ y ^ 7 := by
  have hC0 := xiLineTwoLogDerivConstant_nonneg
  have hlog4 : Real.log 4 ≤ 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    have := Real.log_two_lt_d9; push_cast; linarith
  filter_upwards [eventually_ge_atTop (32 * (xiLineTwoLogDerivConstant + 2) + 4)] with y hy
  have hy4 : 4 ≤ y := by linarith
  have hy0 : 0 < y := by linarith
  have hl1 : Real.log (y ^ 2 + 1) ≤ y ^ 2 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < y ^ 2 + 1 by positivity); linarith
  have hl2 : Real.log y ≤ y := by
    have := Real.log_le_sub_one_of_pos hy0; linarith
  have hl0 : 0 ≤ Real.log (y ^ 2 + 1) := Real.log_nonneg (by nlinarith)
  have hA : 0 ≤ xiLineTwoLogDerivConstant + Real.log 4 := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ 4 by norm_num); linarith
  have hy41 : 1 + (y ^ 2) ^ 2 ≤ 2 * y ^ 4 := by
    have h1 : (1 : ℝ) ≤ y ^ 4 := one_le_pow₀ (by linarith)
    have h2 : (y ^ 2) ^ 2 = y ^ 4 := by ring
    linarith
  have h1 : 8 * (1 + (y ^ 2) ^ 2) * (xiLineTwoLogDerivConstant + Real.log 4) * Real.log (y ^ 2 + 1)
      ≤ 8 * (2 * y ^ 4) * (xiLineTwoLogDerivConstant + 2) * y ^ 2 := by
    have hstep1 : 8 * (1 + (y ^ 2) ^ 2) ≤ 8 * (2 * y ^ 4) := by linarith
    have hstep2 : xiLineTwoLogDerivConstant + Real.log 4 ≤ xiLineTwoLogDerivConstant + 2 := by
      linarith
    exact mul_le_mul (mul_le_mul hstep1 hstep2 hA (by positivity)) hl1 hl0 (by positivity)
  have h2 : 8 * (2 * y ^ 4) * (xiLineTwoLogDerivConstant + 2) * y ^ 2
      = 16 * (xiLineTwoLogDerivConstant + 2) * y ^ 6 := by ring
  have hy6 : 0 ≤ y ^ 6 := by positivity
  have h3 : 16 * (xiLineTwoLogDerivConstant + 2) * y ^ 6 ≤ y / 2 * y ^ 6 :=
    mul_le_mul_of_nonneg_right (by linarith) hy6
  have h4 : y / 2 * y ^ 6 = y ^ 7 / 2 := by ring
  have h5 : 1 + y ≤ y ^ 7 / 2 := by
    have : y ≤ y ^ 6 := by
      calc y = y ^ 1 := (pow_one y).symm
        _ ≤ y ^ 6 := pow_le_pow_right₀ (by linarith) (by norm_num)
    nlinarith
  linarith

/-- In a window `(e^u, e^{u+1/y}]` with `1 + log u ≤ y⁷`, `log log log t ≤ 7 log y`. -/
theorem logLogLog_le_of_window {y u t : ℝ} (hu : 4 ≤ u) (hy : 1 ≤ y) (ht1 : u < Real.log t)
    (ht2 : Real.log t ≤ u + 1 / y) (hlogu : 1 + Real.log u ≤ y ^ 7) :
    Real.log (Real.log (Real.log t)) ≤ 7 * Real.log y := by
  have hu0 : 0 < u := by linarith
  have hlt : 0 < Real.log t := by linarith
  have hy1 : 1 / y ≤ u := by
    rw [div_le_iff₀ (by linarith)]; nlinarith
  have hll : Real.log (Real.log t) ≤ 1 + Real.log u := by
    have h1 := Real.log_le_log hlt (show Real.log t ≤ 2 * u by linarith)
    rw [Real.log_mul (by norm_num) hu0.ne'] at h1
    have h2 : Real.log 2 ≤ 1 := by have := Real.log_two_lt_d9; linarith
    linarith
  have hll0 : 0 < Real.log (Real.log t) := by
    apply Real.log_pos; linarith
  have h7 : Real.log (Real.log (Real.log t)) ≤ Real.log (y ^ 7) :=
    Real.log_le_log hll0 (by linarith)
  rw [Real.log_pow] at h7
  push_cast at h7
  linarith

/-- The alignment point is at most `y·Q^{N}` and so `1 + log u ≤ y⁷`. -/
theorem one_add_log_le_of_aligned {y : ℝ} (hy : 1 ≤ y) {k : ℕ} (hk1 : 1 ≤ k)
    (hkQ : k ≤ ⌈y ^ 2⌉₊ ^ (xiCopiesBelow (y ^ 2)).card)
    (hsize : 1 + 8 * (1 + (y ^ 2) ^ 2) * (xiLineTwoLogDerivConstant + Real.log 4)
      * Real.log (y ^ 2 + 1) + Real.log y ≤ y ^ 7) :
    1 + Real.log ((k : ℝ) * y) ≤ y ^ 7 := by
  have hk : (1 : ℝ) ≤ k := by exact_mod_cast hk1
  have hy0 : 0 < y := by linarith
  have hQ1 : (1 : ℝ) ≤ (⌈y ^ 2⌉₊ : ℝ) := by
    have := Nat.le_ceil (y ^ 2); nlinarith
  have hQle : (⌈y ^ 2⌉₊ : ℝ) ≤ y ^ 2 + 1 := (Nat.ceil_lt_add_one (by positivity)).le
  have hlogk : Real.log k ≤ (xiCopiesBelow (y ^ 2)).card * Real.log (y ^ 2 + 1) := by
    have h1 : (k : ℝ) ≤ (⌈y ^ 2⌉₊ : ℝ) ^ (xiCopiesBelow (y ^ 2)).card := by exact_mod_cast hkQ
    have h2 := Real.log_le_log (by linarith) h1
    rw [Real.log_pow] at h2
    have h3 : Real.log (⌈y ^ 2⌉₊ : ℝ) ≤ Real.log (y ^ 2 + 1) := Real.log_le_log (by linarith) hQle
    have h4 : (0 : ℝ) ≤ (xiCopiesBelow (y ^ 2)).card := by positivity
    nlinarith
  have hcard := card_xiCopiesBelow_le (y ^ 2)
  have hl0 : 0 ≤ Real.log (y ^ 2 + 1) := Real.log_nonneg (by nlinarith)
  have hmul := mul_le_mul_of_nonneg_right hcard hl0
  rw [Real.log_mul (by linarith) hy0.ne']
  linarith

/-- `8e^{-y/2} < (1/(10π³)) log y / y` for large `y`. -/
theorem eventually_exp_neg_half_lt : ∀ᶠ y : ℝ in atTop,
    8 * Real.exp (-(y / 2)) < littlewoodConst / 2 * (Real.log y / y) := by
  have hc := littlewoodConst_pos
  filter_upwards [eventually_ge_atTop (3 : ℝ), eventually_gt_atTop (128 / littlewoodConst)]
    with y hy3 hyc
  have hy0 : 0 < y := by linarith
  have hlog1 : 1 ≤ Real.log y := by
    rw [Real.le_log_iff_exp_le hy0]; have := Real.exp_one_lt_d9; linarith
  have hquad : (y / 2) ^ 2 / 2 ≤ Real.exp (y / 2) := by
    have := Real.pow_div_factorial_le_exp (y / 2) (by positivity) 2
    simpa using this
  have he : Real.exp (-(y / 2)) = (Real.exp (y / 2))⁻¹ := Real.exp_neg _
  rw [he]
  have hpos := Real.exp_pos (y / 2)
  rw [← div_eq_mul_inv, div_lt_iff₀ hpos]
  have h1 : littlewoodConst / 2 * (1 / y) ≤ littlewoodConst / 2 * (Real.log y / y) :=
    mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hlog1 hy0.le) (by positivity)
  have h2 : 8 < littlewoodConst / 2 * (1 / y) * ((y / 2) ^ 2 / 2) := by
    have : littlewoodConst / 2 * (1 / y) * ((y / 2) ^ 2 / 2) = littlewoodConst * y / 16 := by
      field_simp; ring
    rw [this, lt_div_iff₀ (by norm_num)]
    rw [div_lt_iff₀ hc] at hyc
    linarith
  have h3 := mul_le_mul h1 hquad (by positivity) (by positivity)
  linarith

/-- **Littlewood, lower side, under RH.** -/
theorem frequently_chebyshevError_lt_littlewood_of_riemannHypothesis (hRH : RiemannHypothesis) :
    ∃ᶠ x : ℝ in atTop, chebyshevError x
      < -(littlewoodConst / 14 * Real.sqrt x * Real.log (Real.log (Real.log x))) := by
  rw [Filter.frequently_atTop]
  intro x₀
  have hc := littlewoodConst_pos
  obtain ⟨y, ⟨⟨⟨⟨hz, hy4⟩, hsize⟩, hyx⟩, hcontra⟩⟩ :=
    ((((eventually_littlewood_zero_side_lower hRH).and (eventually_ge_atTop (4 : ℝ))).and
      eventually_littlewood_size).and
      (eventually_ge_atTop (Real.log (max x₀ 1) + 1))).and eventually_exp_neg_half_lt |>.exists
  have hy0 : 0 < y := by linarith
  have hQ1 : 1 ≤ ⌈y ^ 2⌉₊ := by
    have : (1 : ℝ) ≤ (⌈y ^ 2⌉₊ : ℝ) := by have := Nat.le_ceil (y ^ 2); nlinarith
    exact_mod_cast this
  obtain ⟨k, hk1, hkQ, halign⟩ := exists_aligned_multiple (y ^ 2) y ⌈y ^ 2⌉₊ hQ1
  set u : ℝ := (k : ℝ) * y with hu
  have hk : (1 : ℝ) ≤ k := by exact_mod_cast hk1
  have hyu : y ≤ u := by rw [hu]; nlinarith
  have hΔ := hz u halign
  have hlogu := one_add_log_le_of_aligned (by linarith) hk1 hkQ hsize
  rw [← hu] at hlogu
  set X := Real.exp u with hX
  have hX1 : 1 < X := by rw [hX]; exact Real.one_lt_exp_iff.mpr (by linarith)
  have hlogX : Real.log X = u := by rw [hX, Real.log_exp]
  have hXx₀ : x₀ ≤ X := by
    have h1 : Real.log (max x₀ 1) ≤ u := by linarith
    have h2 : max x₀ 1 ≤ X := by
      rw [hX, ← Real.exp_log (show 0 < max x₀ 1 by positivity)]
      exact Real.exp_le_exp.mpr h1
    exact le_trans (le_max_left _ _) h2
  by_contra hno
  push Not at hno
  set A := littlewoodConst / 2 * Real.log y with hA
  have hlogy0 : 0 ≤ Real.log y := Real.log_nonneg (by linarith)
  have hA0 : 0 ≤ A := by positivity
  have hlow : ∀ t ∈ Ioc X (X * Real.exp (1 / y)), -(A * Real.sqrt t) ≤ chebyshevError t := by
    intro t ht
    have ht0 : 0 < t := lt_trans (by linarith) ht.1
    have hge := hno t (le_trans hXx₀ ht.1.le)
    have hlt1 : u < Real.log t := by
      rw [← hlogX]; exact Real.log_lt_log (by linarith) ht.1
    have hlt2 : Real.log t ≤ u + 1 / y := by
      have h1 := Real.log_le_log ht0 ht.2
      rw [Real.log_mul (x := X) (y := Real.exp (1 / y)) (by linarith) (Real.exp_pos _).ne'] at h1
      have h2 : Real.log (Real.exp (1 / y)) = 1 / y := Real.log_exp _
      linarith
    have hlll := logLogLog_le_of_window (by linarith) (by linarith) hlt1 hlt2 hlogu
    have hs := Real.sqrt_nonneg t
    have hbound : littlewoodConst / 14 * Real.sqrt t * Real.log (Real.log (Real.log t))
        ≤ A * Real.sqrt t := by
      rw [hA]
      have : littlewoodConst / 14 * Real.log (Real.log (Real.log t))
          ≤ littlewoodConst / 2 * Real.log y := by nlinarith
      nlinarith
    linarith
  have hprime := lagDifference_ge_of_chebyshevError_lower hX1 (by positivity) hA0 hlow
  rw [hlogX] at hprime
  have hsqX : 4 / Real.sqrt X ≤ 4 * Real.exp (-(y / 2)) := by
    have hs : Real.sqrt X = Real.exp (u / 2) := by
      rw [hX, Real.sqrt_eq_iff_mul_self_eq (Real.exp_pos _).le (Real.exp_pos _).le,
        ← Real.exp_add]
      congr 1; ring
    rw [hs, div_eq_mul_inv, ← Real.exp_neg]
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) (by norm_num)
  have hAy : A * (1 / y) = littlewoodConst / 2 * (Real.log y / y) := by rw [hA]; ring
  have hcy : littlewoodConst * (Real.log y / y)
      = littlewoodConst / 2 * (Real.log y / y) + littlewoodConst / 2 * (Real.log y / y) := by ring
  have hep := Real.exp_pos (-(y / 2))
  linarith


/-- The contradiction on an upper window. -/
theorem littlewood_upper_core {y v : ℝ} (hy5 : 5 ≤ y) (hv4 : 4 ≤ v) (hvy : y - 1 / 5 ≤ v)
    (hlogv : 1 + Real.log v ≤ y ^ 7)
    (hΔ : littlewoodConst * (Real.log y / y)
      ≤ weilLagFunctionReal (v + 1 / y) * Real.exp (-(1 / y / 2)) - weilLagFunctionReal v)
    (hcontra : 8 * Real.exp (-(y / 2)) < littlewoodConst / 2 * (Real.log y / y))
    (hup0 : ∀ t ∈ Ioc (Real.exp v) (Real.exp v * Real.exp (1 / y)),
      chebyshevError t ≤ littlewoodConst / 14 * Real.sqrt t * Real.log (Real.log (Real.log t))) :
    False := by
  have hc := littlewoodConst_pos
  have hy0 : 0 < y := by linarith
  set X := Real.exp v with hX
  have hX1 : 1 < X := by rw [hX]; exact Real.one_lt_exp_iff.mpr (by linarith)
  have hlogX : Real.log X = v := by rw [hX, Real.log_exp]
  set A := littlewoodConst / 2 * Real.log y with hA
  have hlogy0 : 0 ≤ Real.log y := Real.log_nonneg (by linarith)
  have hA0 : 0 ≤ A := by positivity
  have hup : ∀ t ∈ Ioc X (X * Real.exp (1 / y)), chebyshevError t ≤ A * Real.sqrt t := by
    intro t ht
    have ht0 : 0 < t := lt_trans (by linarith) ht.1
    have hle := hup0 t ht
    have hlt1 : v < Real.log t := by
      rw [← hlogX]; exact Real.log_lt_log (by linarith) ht.1
    have hlt2 : Real.log t ≤ v + 1 / y := by
      have h1 := Real.log_le_log ht0 ht.2
      rw [Real.log_mul (x := X) (y := Real.exp (1 / y)) (by linarith) (Real.exp_pos _).ne'] at h1
      have h2 : Real.log (Real.exp (1 / y)) = 1 / y := Real.log_exp _
      linarith
    have hlll := logLogLog_le_of_window hv4 (by linarith) hlt1 hlt2 hlogv
    have hs := Real.sqrt_nonneg t
    have hbound : littlewoodConst / 14 * Real.sqrt t * Real.log (Real.log (Real.log t))
        ≤ A * Real.sqrt t := by
      rw [hA]
      have : littlewoodConst / 14 * Real.log (Real.log (Real.log t))
          ≤ littlewoodConst / 2 * Real.log y := by nlinarith
      nlinarith
    linarith
  have hprime := lagDifference_le_of_chebyshevError_upper hX1 (by positivity) hA0 hup
  rw [hlogX] at hprime
  have hsqX : 4 / Real.sqrt X ≤ 8 * Real.exp (-(y / 2)) := by
    have hs : Real.sqrt X = Real.exp (v / 2) := by
      rw [hX, Real.sqrt_eq_iff_mul_self_eq (Real.exp_pos _).le (Real.exp_pos _).le,
        ← Real.exp_add]
      congr 1; ring
    rw [hs, div_eq_mul_inv, ← Real.exp_neg]
    have h1 : Real.exp (-(v / 2)) ≤ Real.exp (-(y / 2) + 1 / 10) :=
      Real.exp_le_exp.mpr (by linarith)
    rw [Real.exp_add] at h1
    have h2 : Real.exp (1 / 10) ≤ 2 := by
      have h4 : Real.exp (1 / 10) ^ 2 ≤ Real.exp 1 := by
        rw [← Real.exp_nat_mul]; exact Real.exp_le_exp.mpr (by norm_num)
      have := Real.exp_one_lt_d9
      nlinarith [Real.exp_pos (1 / 10 : ℝ)]
    have hep := Real.exp_pos (-(y / 2))
    nlinarith
  have hAy : A * (1 / y) = littlewoodConst / 2 * (Real.log y / y) := by rw [hA]; ring
  have hcy : littlewoodConst * (Real.log y / y)
      = littlewoodConst / 2 * (Real.log y / y) + littlewoodConst / 2 * (Real.log y / y) := by ring
  linarith

/-- **Littlewood, upper side, under RH.** -/
theorem frequently_littlewood_lt_chebyshevError_of_riemannHypothesis (hRH : RiemannHypothesis) :
    ∃ᶠ x : ℝ in atTop,
      littlewoodConst / 14 * Real.sqrt x * Real.log (Real.log (Real.log x)) < chebyshevError x := by
  rw [Filter.frequently_atTop]
  intro x₀
  have hc := littlewoodConst_pos
  obtain ⟨y, ⟨⟨⟨⟨hz, hy5⟩, hsize⟩, hyx⟩, hcontra⟩⟩ :=
    ((((eventually_littlewood_zero_side_upper hRH).and (eventually_ge_atTop (5 : ℝ))).and
      eventually_littlewood_size).and
      (eventually_ge_atTop (Real.log (max x₀ 1) + 2))).and eventually_exp_neg_half_lt |>.exists
  have hy0 : 0 < y := by linarith
  have hQ1 : 1 ≤ ⌈y ^ 2⌉₊ := by
    have : (1 : ℝ) ≤ (⌈y ^ 2⌉₊ : ℝ) := by have := Nat.le_ceil (y ^ 2); nlinarith
    exact_mod_cast this
  obtain ⟨k, hk1, hkQ, halign⟩ := exists_aligned_multiple (y ^ 2) y ⌈y ^ 2⌉₊ hQ1
  have hk : (1 : ℝ) ≤ k := by exact_mod_cast hk1
  have hyu : y ≤ (k : ℝ) * y := by nlinarith
  have hΔ := hz ((k : ℝ) * y) halign
  have hlogu := one_add_log_le_of_aligned (by linarith) hk1 hkQ hsize
  have hy15 : 1 / y ≤ 1 / 5 := by rw [div_le_div_iff₀ hy0 (by norm_num)]; linarith
  have h1y : 0 < 1 / y := by positivity
  have hv4 : 4 ≤ (k : ℝ) * y - 1 / y := by linarith
  have hlogv : 1 + Real.log ((k : ℝ) * y - 1 / y) ≤ y ^ 7 := by
    have : Real.log ((k : ℝ) * y - 1 / y) ≤ Real.log ((k : ℝ) * y) :=
      Real.log_le_log (by linarith) (by linarith)
    linarith
  have hΔ' : littlewoodConst * (Real.log y / y)
      ≤ weilLagFunctionReal (((k : ℝ) * y - 1 / y) + 1 / y) * Real.exp (-(1 / y / 2))
        - weilLagFunctionReal ((k : ℝ) * y - 1 / y) := by
    rw [show ((k : ℝ) * y - 1 / y) + 1 / y = (k : ℝ) * y by ring]; exact hΔ
  have hXx₀ : x₀ ≤ Real.exp ((k : ℝ) * y - 1 / y) := by
    have h1 : Real.log (max x₀ 1) ≤ (k : ℝ) * y - 1 / y := by linarith
    have h2 : max x₀ 1 ≤ Real.exp ((k : ℝ) * y - 1 / y) := by
      rw [← Real.exp_log (show 0 < max x₀ 1 by positivity)]
      exact Real.exp_le_exp.mpr h1
    exact le_trans (le_max_left _ _) h2
  by_contra hno
  push Not at hno
  exact littlewood_upper_core hy5 hv4 (by linarith) hlogv hΔ' hcontra
    (fun t ht => hno t (le_trans hXx₀ ht.1.le))

/-- `log log log x ≤ log x` once `log x ≥ e`. -/
theorem logLogLog_le_log {x : ℝ} (hx : Real.exp 1 ≤ Real.log x) :
    Real.log (Real.log (Real.log x)) ≤ Real.log x := by
  have hL0 : 0 < Real.log x := lt_of_lt_of_le (Real.exp_pos 1) hx
  have hLL : 1 ≤ Real.log (Real.log x) := by rw [Real.le_log_iff_exp_le hL0]; exact hx
  have h1 : Real.log (Real.log (Real.log x)) ≤ Real.log (Real.log x) - 1 :=
    Real.log_le_sub_one_of_pos (by linarith)
  have h2 : Real.log (Real.log x) ≤ Real.log x - 1 := Real.log_le_sub_one_of_pos hL0
  linarith

/-- **Without RH: a lower bound `-c√x log log log x` forces every zero to the left of `½ + a`.** -/
theorem re_le_half_add_of_chebyshevError_ge_logLogLog {c a : ℝ} (hc : 0 ≤ c) (ha0 : 0 < a)
    (ha : a < 1 / 2)
    (h : ∀ᶠ x : ℝ in atTop, -(c * Real.sqrt x * Real.log (Real.log (Real.log x)))
      ≤ chebyshevError x) (q : XiZeroCopy) :
    (q.1 : ℂ).re ≤ 1 / 2 + a := by
  obtain ⟨x₀, hx₀⟩ := eventually_atTop.mp (h.and (Real.tendsto_log_atTop.eventually_ge_atTop
    (Real.exp 1)))
  set x₁ := max x₀ (Real.exp (Real.exp 1)) + 1 with hx₁
  have hx₁1 : 1 < x₁ := by
    have := Real.exp_pos (Real.exp 1); rw [hx₁]; linarith [le_max_right x₀ (Real.exp (Real.exp 1))]
  -- the pointwise power bound
  have hpow : ∀ t, x₁ ≤ t → -(c / a * t ^ (1 / 2 + a)) ≤ chebyshevError t := by
    intro t ht
    have ht0 : 0 < t := by linarith
    obtain ⟨h1, h2⟩ := hx₀ t (le_trans (le_trans (le_max_left _ _) (by linarith)) ht)
    have hlll := logLogLog_le_log h2
    have hlog := Real.log_le_rpow_div ht0.le ha0
    have hsq : Real.sqrt t * t ^ a = t ^ (1 / 2 + a) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_add ht0]
    have hs := Real.sqrt_nonneg t
    have hb : c * Real.sqrt t * Real.log (Real.log (Real.log t)) ≤ c / a * t ^ (1 / 2 + a) := by
      have h3 : Real.log (Real.log (Real.log t)) ≤ t ^ a / a := le_trans hlll hlog
      calc c * Real.sqrt t * Real.log (Real.log (Real.log t))
          ≤ c * Real.sqrt t * (t ^ a / a) := mul_le_mul_of_nonneg_left h3 (by positivity)
        _ = c / a * (Real.sqrt t * t ^ a) := by ring
        _ = c / a * t ^ (1 / 2 + a) := by rw [hsq]
    linarith
  -- the tail integral
  have htail : ∀ x, x₁ ≤ x →
      -(c / a * (x ^ (a - 1 / 2) / (1 / 2 - a))) ≤ ∫ t in Ioi x, chebyshevError t / t ^ 2 := by
    intro x hx
    have hx0 : 0 < x := by linarith
    have hint : IntegrableOn (fun t : ℝ => chebyshevError t / t ^ 2) (Ioi x) :=
      integrableOn_chebyshevError_div_sq.mono_set (Ioi_subset_Ioi (by linarith))
    have hint2 : IntegrableOn (fun t : ℝ => -(c / a) * t ^ (a - 3 / 2)) (Ioi x) :=
      (integrableOn_Ioi_rpow_of_lt (by linarith) hx0).const_mul _
    have hmono := setIntegral_mono_on hint2 hint measurableSet_Ioi (fun t ht => by
      have ht0 : 0 < t := lt_trans hx0 ht
      have h1 := hpow t (le_trans hx (le_of_lt ht))
      have h2 : -(c / a) * t ^ (a - 3 / 2) = -(c / a * t ^ (1 / 2 + a)) / t ^ 2 := by
        rw [show a - 3 / 2 = (1 / 2 + a) - 2 by ring, Real.rpow_sub ht0, Real.rpow_two]
        ring
      rw [h2]
      exact div_le_div_of_nonneg_right h1 (by positivity))
    rw [integral_const_mul, integral_Ioi_rpow_of_lt (by linarith) hx0,
      show a - 3 / 2 + 1 = a - 1 / 2 by ring] at hmono
    have hd : -x ^ (a - 1 / 2) / (a - 1 / 2) = x ^ (a - 1 / 2) / (1 / 2 - a) := by
      rw [div_eq_div_iff (by linarith) (by linarith)]; ring
    have hneg : -(c / a) * (-x ^ (a - 1 / 2) / (a - 1 / 2))
        = -(c / a * (x ^ (a - 1 / 2) / (1 / 2 - a))) := by
      rw [hd]; ring
    linarith
  -- the exponential growth bound for large lags
  set K := c / (a * (1 / 2 - a)) + 1 with hK
  have hK0 : 0 ≤ K := by
    have : 0 ≤ c / (a * (1 / 2 - a)) := div_nonneg hc (mul_nonneg ha0.le (by linarith))
    linarith
  have hlarge : ∀ L, Real.log x₁ ≤ L → weilLagFunctionReal L ≤ K * Real.exp (a * L) := by
    intro L hL
    have hx1L : x₁ ≤ Real.exp L := by
      rw [← Real.exp_log (show 0 < x₁ by linarith)]; exact Real.exp_le_exp.mpr hL
    set x := Real.exp L with hxdef
    have hx1 : 1 < x := by linarith
    have hx0 : 0 < x := by linarith
    have hlogx : Real.log x = L := by rw [hxdef, Real.log_exp]
    have hid := weilLagFunctionReal_log_mul_sqrt hx1
    rw [hlogx] at hid
    have ht := htail x hx1L
    have hS := trivialZeroSeriesReal_le_one hx1.le
    have hl := one_lt_log_two_pi
    have hsx : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx0
    have hxa : x ^ a = Real.exp (a * L) := by
      rw [hxdef, ← Real.exp_mul]; ring_nf
    have hxa' : x * x ^ (a - 1 / 2) = Real.sqrt x * x ^ a := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_one_add' hx0.le (by linarith), ← Real.rpow_add hx0]
      ring_nf
    -- Φ(L)√x ≤ (c/a)x·x^{a-1/2}/(1/2-a) + 1
    have h1 : weilLagFunctionReal L * Real.sqrt x
        ≤ c / a * (x * x ^ (a - 1 / 2)) / (1 / 2 - a) + 1 := by
      have hxI := mul_le_mul_of_nonneg_left ht hx0.le
      have : x * (c / a * (x ^ (a - 1 / 2) / (1 / 2 - a)))
          = c / a * (x * x ^ (a - 1 / 2)) / (1 / 2 - a) := by ring
      linarith
    rw [hxa'] at h1
    have h2 : weilLagFunctionReal L ≤ c / (a * (1 / 2 - a)) * x ^ a + 1 / Real.sqrt x := by
      rw [← mul_le_mul_iff_of_pos_right hsx]
      have : (c / (a * (1 / 2 - a)) * x ^ a + 1 / Real.sqrt x) * Real.sqrt x
          = c / a * (Real.sqrt x * x ^ a) / (1 / 2 - a) + 1 := by
        field_simp
      rw [this]; exact h1
    have h3 : 1 / Real.sqrt x ≤ x ^ a := by
      have hxa1 : 1 ≤ x ^ a := Real.one_le_rpow hx1.le ha0.le
      have hsx1 : 1 ≤ Real.sqrt x := by rw [Real.le_sqrt (by norm_num) hx0.le]; linarith
      have : 1 / Real.sqrt x ≤ 1 := by rw [div_le_one hsx]; exact hsx1
      linarith
    rw [← hxa]
    nlinarith
  -- the compact range
  obtain ⟨L₀, hL₀mem, hL₀max⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := Real.log x₁)).exists_isMaxOn
    ⟨0, ⟨le_refl 0, (Real.log_pos hx₁1).le⟩⟩
    (Complex.continuous_re.comp continuous_weilLagFunction_unconditional).continuousOn
  set B := weilLagFunctionReal L₀ with hB
  have hM : ∀ L, 0 ≤ L → weilLagFunctionReal L ≤ max K |B| * Real.exp (a * L) := by
    intro L hL
    have hexp1 : 1 ≤ Real.exp (a * L) := Real.one_le_exp (by positivity)
    rcases le_or_gt (Real.log x₁) L with hbig | hsmall
    · have := hlarge L hbig
      have : K * Real.exp (a * L) ≤ max K |B| * Real.exp (a * L) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le
      linarith
    · have h1 : weilLagFunctionReal L ≤ B := hL₀max ⟨hL, hsmall.le⟩
      have h2 : B ≤ |B| := le_abs_self B
      have h3 : |B| ≤ max K |B| := le_max_right _ _
      have h4 : max K |B| ≤ max K |B| * Real.exp (a * L) := by
        have : 0 ≤ max K |B| := le_trans (abs_nonneg B) h3
        nlinarith
      linarith
  exact re_le_half_add_of_weilLagFunctionReal_le_exp ha0.le ha hM q

/-- **Without RH: a lower bound `-c√x log log log x` forces RH.** -/
theorem riemannHypothesis_of_chebyshevError_ge_logLogLog {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ᶠ x : ℝ in atTop, -(c * Real.sqrt x * Real.log (Real.log (Real.log x)))
      ≤ chebyshevError x) : RiemannHypothesis := by
  have hle : ∀ q : XiZeroCopy, (q.1 : ℂ).re ≤ 1 / 2 := by
    intro q
    refine le_of_forall_pos_lt_add fun ε hε => ?_
    have h1 := re_le_half_add_of_chebyshevError_ge_logLogLog hc (a := min (ε / 2) (1 / 4))
      (lt_min (by linarith) (by norm_num)) (lt_of_le_of_lt (min_le_right _ _) (by norm_num)) h q
    have h2 := min_le_left (ε / 2) (1 / 4)
    linarith
  have hρ : ∀ ρ : XiDivisorSupport, (ρ : ℂ).re ≤ 1 / 2 := by
    intro ρ
    exact hle ⟨ρ, ⟨0, xiSupportMultiplicity_pos ρ⟩⟩
  refine riemannHypothesis_of_forall_re_eq (c := 1 / 2) fun ρ => ?_
  have h1 := hρ ρ
  have h2 := hρ (supportPartner ρ)
  rw [supportPartner_re] at h2
  linarith

/-- **Littlewood's oscillation theorem, lower side.**  Unconditionally,
`ψ(x) - x < -(1/(70π³)) √x log log log x` for arbitrarily large `x`. -/
theorem frequently_chebyshevPsi_sub_lt_littlewood :
    ∃ᶠ x : ℝ in atTop, Chebyshev.psi x - x
      < -(littlewoodConst / 14 * Real.sqrt x * Real.log (Real.log (Real.log x))) := by
  by_cases hRH : RiemannHypothesis
  · exact frequently_chebyshevError_lt_littlewood_of_riemannHypothesis hRH
  · by_contra hno
    rw [Filter.not_frequently] at hno
    exact hRH (riemannHypothesis_of_chebyshevError_ge_logLogLog
      (by have := littlewoodConst_pos; positivity)
      (hno.mono fun x hx => le_of_not_gt hx))


/-- **Without RH: an upper bound `c√x log log log x` forces every zero to the left of `½ + a`.** -/
theorem re_le_half_add_of_chebyshevError_le_logLogLog {c a : ℝ} (hc : 0 ≤ c) (ha0 : 0 < a)
    (ha : a < 1 / 2)
    (h : ∀ᶠ x : ℝ in atTop, chebyshevError x
      ≤ c * Real.sqrt x * Real.log (Real.log (Real.log x))) (q : XiZeroCopy) :
    (q.1 : ℂ).re ≤ 1 / 2 + a := by
  obtain ⟨x₀, hx₀⟩ := eventually_atTop.mp (h.and (Real.tendsto_log_atTop.eventually_ge_atTop
    (Real.exp 1)))
  set x₁ := max x₀ (Real.exp (Real.exp 1)) + 1 with hx₁
  have hx₁1 : 1 < x₁ := by
    have := Real.exp_pos (Real.exp 1); rw [hx₁]; linarith [le_max_right x₀ (Real.exp (Real.exp 1))]
  have hpow : ∀ t, x₁ ≤ t → chebyshevError t ≤ c / a * t ^ (1 / 2 + a) := by
    intro t ht
    have ht0 : 0 < t := by linarith
    obtain ⟨h1, h2⟩ := hx₀ t (le_trans (le_trans (le_max_left _ _) (by linarith)) ht)
    have hlll := logLogLog_le_log h2
    have hlog := Real.log_le_rpow_div ht0.le ha0
    have hsq : Real.sqrt t * t ^ a = t ^ (1 / 2 + a) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_add ht0]
    have hs := Real.sqrt_nonneg t
    have hb : c * Real.sqrt t * Real.log (Real.log (Real.log t)) ≤ c / a * t ^ (1 / 2 + a) := by
      have h3 : Real.log (Real.log (Real.log t)) ≤ t ^ a / a := le_trans hlll hlog
      calc c * Real.sqrt t * Real.log (Real.log (Real.log t))
          ≤ c * Real.sqrt t * (t ^ a / a) := mul_le_mul_of_nonneg_left h3 (by positivity)
        _ = c / a * (Real.sqrt t * t ^ a) := by ring
        _ = c / a * t ^ (1 / 2 + a) := by rw [hsq]
    linarith
  have htail : ∀ x, x₁ ≤ x →
      ∫ t in Ioi x, chebyshevError t / t ^ 2 ≤ c / a * (x ^ (a - 1 / 2) / (1 / 2 - a)) := by
    intro x hx
    have hx0 : 0 < x := by linarith
    have hint : IntegrableOn (fun t : ℝ => chebyshevError t / t ^ 2) (Ioi x) :=
      integrableOn_chebyshevError_div_sq.mono_set (Ioi_subset_Ioi (by linarith))
    have hint2 : IntegrableOn (fun t : ℝ => c / a * t ^ (a - 3 / 2)) (Ioi x) :=
      (integrableOn_Ioi_rpow_of_lt (by linarith) hx0).const_mul _
    have hmono := setIntegral_mono_on hint hint2 measurableSet_Ioi (fun t ht => by
      have ht0 : 0 < t := lt_trans hx0 ht
      have h1 := hpow t (le_trans hx (le_of_lt ht))
      have h2 : c / a * t ^ (a - 3 / 2) = c / a * t ^ (1 / 2 + a) / t ^ 2 := by
        rw [show a - 3 / 2 = (1 / 2 + a) - 2 by ring, Real.rpow_sub ht0, Real.rpow_two]
        ring
      rw [h2]
      exact div_le_div_of_nonneg_right h1 (by positivity))
    rw [integral_const_mul, integral_Ioi_rpow_of_lt (by linarith) hx0,
      show a - 3 / 2 + 1 = a - 1 / 2 by ring] at hmono
    have hd : -x ^ (a - 1 / 2) / (a - 1 / 2) = x ^ (a - 1 / 2) / (1 / 2 - a) := by
      rw [div_eq_div_iff (by linarith) (by linarith)]; ring
    rw [hd] at hmono
    exact hmono
  set K := c / (a * (1 / 2 - a)) + 3 with hK
  have hlarge : ∀ L, Real.log x₁ ≤ L → -(K * Real.exp (a * L)) ≤ weilLagFunctionReal L := by
    intro L hL
    have hx1L : x₁ ≤ Real.exp L := by
      rw [← Real.exp_log (show 0 < x₁ by linarith)]; exact Real.exp_le_exp.mpr hL
    set x := Real.exp L with hxdef
    have hx1 : 1 < x := by linarith
    have hx0 : 0 < x := by linarith
    have hlogx : Real.log x = L := by rw [hxdef, Real.log_exp]
    have hid := weilLagFunctionReal_log_mul_sqrt hx1
    rw [hlogx] at hid
    have ht := htail x hx1L
    have hS := trivialZeroSeriesReal_nonneg hx1.le
    have hl : Real.log (2 * Real.pi) ≤ 3 := by
      have h := abs_trivialZeroSeriesReal_sub_log_two_pi_le hx1.le
      have h1 := trivialZeroSeriesReal_le_one hx1.le
      rw [abs_le] at h; linarith [h.1]
    have hsx : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx0
    have hxa : x ^ a = Real.exp (a * L) := by
      rw [hxdef, ← Real.exp_mul]; ring_nf
    have hxa' : x * x ^ (a - 1 / 2) = Real.sqrt x * x ^ a := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_one_add' hx0.le (by linarith), ← Real.rpow_add hx0]
      ring_nf
    have h1 : -(c / a * (x * x ^ (a - 1 / 2)) / (1 / 2 - a)) - 3
        ≤ weilLagFunctionReal L * Real.sqrt x := by
      have hxI := mul_le_mul_of_nonneg_left ht hx0.le
      have : x * (c / a * (x ^ (a - 1 / 2) / (1 / 2 - a)))
          = c / a * (x * x ^ (a - 1 / 2)) / (1 / 2 - a) := by ring
      linarith
    rw [hxa'] at h1
    have h2 : -(c / (a * (1 / 2 - a)) * x ^ a) - 3 / Real.sqrt x ≤ weilLagFunctionReal L := by
      rw [← mul_le_mul_iff_of_pos_right hsx]
      have : (-(c / (a * (1 / 2 - a)) * x ^ a) - 3 / Real.sqrt x) * Real.sqrt x
          = -(c / a * (Real.sqrt x * x ^ a) / (1 / 2 - a)) - 3 := by
        field_simp
      rw [this]; exact h1
    have h3 : 3 / Real.sqrt x ≤ 3 * x ^ a := by
      have hxa1 : 1 ≤ x ^ a := Real.one_le_rpow hx1.le ha0.le
      have hsx1 : 1 ≤ Real.sqrt x := by rw [Real.le_sqrt (by norm_num) hx0.le]; linarith
      have : 3 / Real.sqrt x ≤ 3 := by rw [div_le_iff₀ hsx]; linarith
      linarith
    rw [← hxa]
    nlinarith
  obtain ⟨L₀, hL₀mem, hL₀min⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := Real.log x₁)).exists_isMinOn
    ⟨0, ⟨le_refl 0, (Real.log_pos hx₁1).le⟩⟩
    (Complex.continuous_re.comp continuous_weilLagFunction_unconditional).continuousOn
  set B := weilLagFunctionReal L₀ with hB
  have hK0 : 0 ≤ K := by
    have : 0 ≤ c / (a * (1 / 2 - a)) := div_nonneg hc (mul_nonneg ha0.le (by linarith))
    linarith
  have hM : ∀ L, 0 ≤ L → -(max K |B| * Real.exp (a * L)) ≤ weilLagFunctionReal L := by
    intro L hL
    have hexp1 : 1 ≤ Real.exp (a * L) := Real.one_le_exp (by positivity)
    rcases le_or_gt (Real.log x₁) L with hbig | hsmall
    · have := hlarge L hbig
      have : K * Real.exp (a * L) ≤ max K |B| * Real.exp (a * L) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le
      linarith
    · have h1 : B ≤ weilLagFunctionReal L := hL₀min ⟨hL, hsmall.le⟩
      have h2 : -|B| ≤ B := neg_abs_le B
      have h3 : |B| ≤ max K |B| := le_max_right _ _
      have h4 : max K |B| ≤ max K |B| * Real.exp (a * L) := by
        have : 0 ≤ max K |B| := le_trans (abs_nonneg B) h3
        nlinarith
      linarith
  exact re_le_half_add_of_neg_exp_le_weilLagFunctionReal ha0.le ha hM q

/-- **Without RH: an upper bound `c√x log log log x` forces RH.** -/
theorem riemannHypothesis_of_chebyshevError_le_logLogLog {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ᶠ x : ℝ in atTop, chebyshevError x
      ≤ c * Real.sqrt x * Real.log (Real.log (Real.log x))) : RiemannHypothesis := by
  have hle : ∀ q : XiZeroCopy, (q.1 : ℂ).re ≤ 1 / 2 := by
    intro q
    refine le_of_forall_pos_lt_add fun ε hε => ?_
    have h1 := re_le_half_add_of_chebyshevError_le_logLogLog hc (a := min (ε / 2) (1 / 4))
      (lt_min (by linarith) (by norm_num)) (lt_of_le_of_lt (min_le_right _ _) (by norm_num)) h q
    have h2 := min_le_left (ε / 2) (1 / 4)
    linarith
  have hρ : ∀ ρ : XiDivisorSupport, (ρ : ℂ).re ≤ 1 / 2 := by
    intro ρ
    exact hle ⟨ρ, ⟨0, xiSupportMultiplicity_pos ρ⟩⟩
  refine riemannHypothesis_of_forall_re_eq (c := 1 / 2) fun ρ => ?_
  have h1 := hρ ρ
  have h2 := hρ (supportPartner ρ)
  rw [supportPartner_re] at h2
  linarith

/-- **Littlewood's oscillation theorem, upper side.**  Unconditionally,
`ψ(x) - x > (1/(70π³)) √x log log log x` for arbitrarily large `x`. -/
theorem frequently_littlewood_lt_chebyshevPsi_sub :
    ∃ᶠ x : ℝ in atTop, littlewoodConst / 14 * Real.sqrt x * Real.log (Real.log (Real.log x))
      < Chebyshev.psi x - x := by
  by_cases hRH : RiemannHypothesis
  · exact frequently_littlewood_lt_chebyshevError_of_riemannHypothesis hRH
  · by_contra hno
    rw [Filter.not_frequently] at hno
    exact hRH (riemannHypothesis_of_chebyshevError_le_logLogLog
      (by have := littlewoodConst_pos; positivity)
      (hno.mono fun x hx => le_of_not_gt hx))

/-- **Littlewood's theorem (1914).**  `ψ(x) - x = Ω±(√x log log log x)`: with `c = 1/(70π³)`,
both `ψ(x) - x < -c√x log log log x` and `ψ(x) - x > c√x log log log x` hold for arbitrarily
large `x`. -/
theorem chebyshevPsi_sub_omega_pm_littlewood :
    (∃ᶠ x : ℝ in atTop, Chebyshev.psi x - x
      < -(littlewoodConst / 14 * Real.sqrt x * Real.log (Real.log (Real.log x))))
    ∧ ∃ᶠ x : ℝ in atTop, littlewoodConst / 14 * Real.sqrt x * Real.log (Real.log (Real.log x))
      < Chebyshev.psi x - x :=
  ⟨frequently_chebyshevPsi_sub_lt_littlewood, frequently_littlewood_lt_chebyshevPsi_sub⟩

end

end RHTower
