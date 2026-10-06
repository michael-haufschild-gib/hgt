import GaloisForLFunctions.RHTower.VerticalProgressionFirstMoment
import GaloisForLFunctions.RHTower.Sieve.TwistedSelbergRatioForms

/-!
# The ratio forms of the mollified second moment

For coprime `a, b ≥ 1`, the quadruples `(m, n, h, k)` with `nk/(mh) = a/b` enter the mollified
second moment of `ζ` through

`F(a,b,t) = Σ_{h,k ≤ N} b(h)b(k)(ha,kb)/(hk) · 𝓗(t(ha,kb)²/(2π·ha·kb))`,  `𝓗(x) = Σ_{s≥1} s^{−1}V(s²/x)`,

with the linear mollifier `b(h) = μ(h) log(N/h)/log N`.

* **Splitting** (`ratioForm_eq`, `norm_ratioErr_le`):
  `F = (½ log(t/2πab) + γ) S₀(a,b) + ½ S₁(a,b) + E`, `‖E‖ ≤ C (2πN²ab/t)^{1/4} Σ_{h,k}(ha,kb)/(hk)`,
  since `𝓗(x) = ½ log x + γ + O(x^{−1/4})` and `log x = log(t/2πab) + log((ha,kb)²/(hk))`.
* With `N = ⌊T^θ⌋`, `0 < θ < ½`, uniformly for `t ∈ [c₁T, c₂T]`:
  - **diagonal** (`ratioForm_one_one_uniform`): `F(1,1,t) → ½ + 1/(2θ)`;
  - **cancellation** (`ratioForm_uniform_of_ne`): `F(a,b,t) → 0` for fixed coprime `(a,b) ≠ (1,1)`;
  - **envelope** (`exists_norm_ratioForm_le`): `‖F(a,b,t)‖ ≤ C (ab)^{1/3}` for all coprime `a, b`.
-/

open Complex MeasureTheory Set Filter Topology Asymptotics
open scoped BigOperators

namespace RHTower.VerticalAP

noncomputable section

/-! ## Definitions and the splitting -/

/-- The weight `w_{hk} = b(h)b(k)(ha,kb)/(hk)`. -/
def ratioWeight (N a b h k : ℕ) : ℝ :=
  Sieve.linearMollifierCoeff N h * Sieve.linearMollifierCoeff N k *
    ((Nat.gcd (h * a) (k * b) : ℕ) : ℝ) / ((h : ℝ) * (k : ℝ))

/-- The argument `x_{hk}(t) = t (ha,kb)²/(2π·ha·kb)`. -/
def ratioArg (a b h k : ℕ) (t : ℝ) : ℝ :=
  t * ((Nat.gcd (h * a) (k * b) : ℕ) : ℝ) ^ 2 /
    (2 * Real.pi * ((h : ℝ) * a * ((k : ℝ) * b)))

/-- `F(a,b,t) = Σ_{h,k ≤ N} w_{hk} 𝓗(x_{hk}(t))`. -/
def ratioForm (N a b : ℕ) (t : ℝ) : ℂ :=
  ∑ h ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N,
    (ratioWeight N a b h k : ℂ) * ZetaNotch.diagHarm (ratioArg a b h k t)

/-- The remainder `E = Σ w_{hk} (𝓗(x) − ½ log x − γ)`. -/
def ratioErr (N a b : ℕ) (t : ℝ) : ℂ :=
  ∑ h ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N, (ratioWeight N a b h k : ℂ) *
    (ZetaNotch.diagHarm (ratioArg a b h k t) -
      ((Real.log (ratioArg a b h k t) : ℂ) / 2 + Real.eulerMascheroniConstant))

theorem gcd_mul_pos {a b h k : ℕ} (ha : 0 < a) (hh : 0 < h) :
    (0 : ℝ) < ((Nat.gcd (h * a) (k * b) : ℕ) : ℝ) := by
  exact_mod_cast Nat.gcd_pos_of_pos_left _ (Nat.mul_pos hh ha)

theorem ratioArg_pos {a b h k : ℕ} (ha : 0 < a) (hb : 0 < b) (hh : 0 < h) (hk : 0 < k) {t : ℝ}
    (ht : 0 < t) : 0 < ratioArg a b h k t := by
  have := gcd_mul_pos (b := b) (k := k) ha hh
  unfold ratioArg
  have : (0 : ℝ) < a := by exact_mod_cast ha
  have : (0 : ℝ) < b := by exact_mod_cast hb
  have : (0 : ℝ) < h := by exact_mod_cast hh
  have : (0 : ℝ) < k := by exact_mod_cast hk
  positivity

theorem log_ratioArg {a b h k : ℕ} (ha : 0 < a) (hb : 0 < b) (hh : 0 < h) (hk : 0 < k) {t : ℝ}
    (ht : 0 < t) :
    Real.log (ratioArg a b h k t) = Real.log (t / (2 * Real.pi * a * b)) +
      Real.log (((Nat.gcd (h * a) (k * b) : ℕ) : ℝ) ^ 2 / ((h : ℝ) * k)) := by
  have hg := gcd_mul_pos (b := b) (k := k) ha hh
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hhR : (0 : ℝ) < h := by exact_mod_cast hh
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  rw [← Real.log_mul (by positivity) (by positivity)]
  congr 1
  unfold ratioArg
  field_simp

/-- **The splitting** `F = (½ log(t/2πab) + γ) S₀ + ½ S₁ + E`. -/
theorem ratioForm_eq (N : ℕ) {a b : ℕ} (ha : 0 < a) (hb : 0 < b) {t : ℝ} (ht : 0 < t) :
    ratioForm N a b t =
      (((Real.log (t / (2 * Real.pi * a * b)) / 2 + Real.eulerMascheroniConstant) *
          Sieve.twistForm₀ N a b + Sieve.twistForm₁ N a b / 2 : ℝ) : ℂ) + ratioErr N a b t := by
  have hmain : ∀ h ∈ Finset.Icc 1 N, ∀ k ∈ Finset.Icc 1 N,
      (ratioWeight N a b h k : ℂ) * ZetaNotch.diagHarm (ratioArg a b h k t) =
        (((Real.log (t / (2 * Real.pi * a * b)) / 2 + Real.eulerMascheroniConstant) *
            ratioWeight N a b h k + ratioWeight N a b h k *
              Real.log (((Nat.gcd (h * a) (k * b) : ℕ) : ℝ) ^ 2 / ((h : ℝ) * k)) / 2 : ℝ) : ℂ) +
          (ratioWeight N a b h k : ℂ) * (ZetaNotch.diagHarm (ratioArg a b h k t) -
            ((Real.log (ratioArg a b h k t) : ℂ) / 2 + Real.eulerMascheroniConstant)) := by
    intro h hh k hk
    have hx := log_ratioArg ha hb (Finset.mem_Icc.mp hh).1 (Finset.mem_Icc.mp hk).1 ht
    have h1 : (ratioWeight N a b h k : ℂ) *
        ((Real.log (ratioArg a b h k t) : ℂ) / 2 + Real.eulerMascheroniConstant) =
        (((Real.log (t / (2 * Real.pi * a * b)) / 2 + Real.eulerMascheroniConstant) *
            ratioWeight N a b h k + ratioWeight N a b h k *
              Real.log (((Nat.gcd (h * a) (k * b) : ℕ) : ℝ) ^ 2 / ((h : ℝ) * k)) / 2 : ℝ) : ℂ) := by
      rw [hx]
      push_cast
      ring
    rw [← h1]
    ring
  unfold ratioForm ratioErr
  rw [Finset.sum_congr rfl fun h hh => Finset.sum_congr rfl fun k hk => hmain h hh k hk]
  simp only [Finset.sum_add_distrib]
  congr 1
  simp only [← Complex.ofReal_sum]
  congr 1
  unfold Sieve.twistForm₀ Sieve.twistForm₁
  rw [Finset.mul_sum, Finset.sum_div, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [Finset.mul_sum, Finset.sum_div, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  unfold ratioWeight
  ring

/-- **The remainder bound** `‖E‖ ≤ C (2πN²ab/t)^{1/4} Σ (ha,kb)/(hk)`. -/
theorem norm_ratioErr_le {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ x : ℝ, 0 < x →
      ‖ZetaNotch.diagHarm x - ((Real.log x : ℂ) / 2 + Real.eulerMascheroniConstant)‖ ≤ C * x ^ (-(1 / 4) : ℝ))
    (N : ℕ) {a b : ℕ} (ha : 0 < a) (hb : 0 < b) {t : ℝ} (ht : 0 < t) :
    ‖ratioErr N a b t‖ ≤ C * (2 * Real.pi * N ^ 2 * a * b / t) ^ (1 / 4 : ℝ) *
      ∑ h ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N,
        ((Nat.gcd (h * a) (k * b) : ℕ) : ℝ) / ((h : ℝ) * k) := by
  set Y : ℝ := 2 * Real.pi * N ^ 2 * a * b / t with hY
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  rw [Finset.mul_sum]
  unfold ratioErr
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun h hh => ?_)
  rw [Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k hk => ?_)
  obtain ⟨hh1, hhN⟩ := Finset.mem_Icc.mp hh
  obtain ⟨hk1, hkN⟩ := Finset.mem_Icc.mp hk
  have hhR : (0 : ℝ) < h := by exact_mod_cast hh1
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk1
  have hNR : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hg := gcd_mul_pos (b := b) (k := k) ha hh1
  have hg1 : (1 : ℝ) ≤ ((Nat.gcd (h * a) (k * b) : ℕ) : ℝ) := by
    exact_mod_cast Nat.gcd_pos_of_pos_left _ (Nat.mul_pos hh1 ha)
  have hx := ratioArg_pos ha hb hh1 hk1 ht
  have hY0 : 0 < Y := by rw [hY]; positivity
  have hYx : Y⁻¹ ≤ ratioArg a b h k t := by
    rw [hY, inv_div]
    unfold ratioArg
    have hhN' : (h : ℝ) ≤ N := by exact_mod_cast hhN
    have hkN' : (k : ℝ) ≤ N := by exact_mod_cast hkN
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have e1 : (h : ℝ) * a * (k * b) ≤ N ^ 2 * a * b := by
      have : (h : ℝ) * k ≤ N * N := mul_le_mul hhN' hkN' hkR.le hNR.le
      nlinarith [mul_pos haR hbR]
    have e2 : (1 : ℝ) ≤ ((Nat.gcd (h * a) (k * b) : ℕ) : ℝ) ^ 2 := one_le_pow₀ hg1
    have e3 : 0 < 2 * Real.pi := by positivity
    nlinarith [mul_le_mul_of_nonneg_left e1 (mul_nonneg e3.le ht.le),
      mul_le_mul_of_nonneg_left e2 (mul_nonneg (mul_nonneg e3.le (by positivity : (0:ℝ) ≤ N ^ 2 * a * b)) ht.le)]
  have hpow : ratioArg a b h k t ^ (-(1 / 4) : ℝ) ≤ Y ^ (1 / 4 : ℝ) := by
    calc ratioArg a b h k t ^ (-(1 / 4) : ℝ) ≤ Y⁻¹ ^ (-(1 / 4) : ℝ) :=
          Real.rpow_le_rpow_of_nonpos (inv_pos.mpr hY0) hYx (by norm_num)
      _ = Y ^ (1 / 4 : ℝ) := by
          rw [Real.inv_rpow hY0.le, Real.rpow_neg hY0.le, inv_inv]
  have hw : |ratioWeight N a b h k| ≤ ((Nat.gcd (h * a) (k * b) : ℕ) : ℝ) / ((h : ℝ) * k) := by
    unfold ratioWeight
    rw [abs_div, abs_mul, abs_mul, abs_of_pos hg, abs_of_pos (mul_pos hhR hkR)]
    have h1 := abs_linearMollifierCoeff_le_one hh
    have h2 := abs_linearMollifierCoeff_le_one hk
    gcongr
    calc |Sieve.linearMollifierCoeff N h| * |Sieve.linearMollifierCoeff N k| *
          ((Nat.gcd (h * a) (k * b) : ℕ) : ℝ)
        ≤ 1 * 1 * ((Nat.gcd (h * a) (k * b) : ℕ) : ℝ) := by gcongr
      _ = _ := by ring
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  calc |ratioWeight N a b h k| * ‖ZetaNotch.diagHarm (ratioArg a b h k t) -
        ((Real.log (ratioArg a b h k t) : ℂ) / 2 + Real.eulerMascheroniConstant)‖
      ≤ (((Nat.gcd (h * a) (k * b) : ℕ) : ℝ) / ((h : ℝ) * k)) * (C * Y ^ (1 / 4 : ℝ)) :=
        mul_le_mul hw ((hC _ hx).trans (mul_le_mul_of_nonneg_left hpow hC0)) (norm_nonneg _)
          (by positivity)
    _ = C * Y ^ (1 / 4 : ℝ) * (((Nat.gcd (h * a) (k * b) : ℕ) : ℝ) / ((h : ℝ) * k)) := by ring

/-! ## Asymptotic scales -/

theorem one_add_log_pow_mul_rpow_neg_tendsto (n : ℕ) {κ : ℝ} (hκ : 0 < κ) :
    Tendsto (fun T : ℝ => (1 + Real.log T) ^ n * T ^ (-κ)) atTop (𝓝 0) := by
  have h := (isLittleO_log_rpow_rpow_atTop (n : ℝ) hκ).tendsto_div_nhds_zero
  have h2 := h.const_mul ((2 : ℝ) ^ n)
  rw [mul_zero] at h2
  refine squeeze_zero' ?_ ?_ h2
  · filter_upwards [eventually_ge_atTop 1] with T hT
    have := Real.log_nonneg hT
    positivity
  · filter_upwards [eventually_ge_atTop (Real.exp 1)] with T hT
    have hT0 : 0 < T := (Real.exp_pos 1).trans_le hT
    have hlog : 1 ≤ Real.log T := by rwa [Real.le_log_iff_exp_le hT0]
    rw [Real.rpow_natCast, Real.rpow_neg hT0.le, ← div_eq_mul_inv]
    rw [mul_div_assoc']
    gcongr
    calc (1 + Real.log T) ^ n ≤ (2 * Real.log T) ^ n := by gcongr; linarith
      _ = 2 ^ n * Real.log T ^ n := by ring

theorem eventually_two_le_rpow {θ : ℝ} (hθ : 0 < θ) : ∀ᶠ T : ℝ in atTop, 2 ≤ T ^ θ :=
  (tendsto_rpow_atTop hθ).eventually (eventually_ge_atTop 2)

/-- `θ log T − log 2 ≤ log ⌊T^θ⌋ ≤ θ log T` once `T^θ ≥ 2`. -/
theorem log_molLen_bounds {θ T : ℝ} (hT : 1 ≤ T) (h2 : 2 ≤ T ^ θ) :
    θ * Real.log T - Real.log 2 ≤ Real.log (molLen θ T) ∧
      Real.log (molLen θ T) ≤ θ * Real.log T := by
  have hT0 : 0 < T := by linarith
  have hle : (molLen θ T : ℝ) ≤ T ^ θ := molLen_le hT0.le
  have hge : T ^ θ / 2 ≤ (molLen θ T : ℝ) := by
    have := Nat.lt_floor_add_one (T ^ θ)
    unfold molLen
    linarith
  have hpos : 0 < (molLen θ T : ℝ) := by linarith
  rw [← Real.log_rpow hT0]
  constructor
  · rw [← Real.log_div (by positivity) (by norm_num)]
    exact Real.log_le_log (by positivity) hge
  · exact Real.log_le_log hpos hle

theorem tendsto_log_molLen {θ : ℝ} (hθ : 0 < θ) :
    Tendsto (fun T : ℝ => Real.log (molLen θ T)) atTop atTop :=
  Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp (tendsto_molLen hθ))

/-- The centring constant: `|½ log(t/2π) + γ − log ⌊T^θ⌋/(2θ)| ≤ D` for `t ∈ [c₁T, c₂T]`. -/
theorem exists_centre_bound {θ c₁ c₂ : ℝ} (hθ : 0 < θ) (hc₁ : 0 < c₁) (hc : c₁ ≤ c₂) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ᶠ T : ℝ in atTop, ∀ t ∈ Icc (c₁ * T) (c₂ * T),
      |Real.log (t / (2 * Real.pi)) / 2 + Real.eulerMascheroniConstant -
        Real.log (molLen θ T) / (2 * θ)| ≤ D := by
  refine ⟨(|Real.log c₁| + |Real.log c₂|) / 2 + Real.log (2 * Real.pi) / 2 +
    Real.eulerMascheroniConstant + Real.log 2 / (2 * θ), ?_, ?_⟩
  · have : (0 : ℝ) ≤ Real.eulerMascheroniConstant := by
      linarith [Real.one_half_lt_eulerMascheroniConstant]
    have : 0 ≤ Real.log (2 * Real.pi) := Real.log_nonneg (by nlinarith [Real.pi_gt_three])
    have : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    positivity
  filter_upwards [eventually_ge_atTop 1, eventually_two_le_rpow hθ] with T hT h2 t ht
  obtain ⟨hL1, hL2⟩ := log_molLen_bounds hT h2
  have hT0 : 0 < T := by linarith
  obtain ⟨ht1, ht2⟩ := ht
  have ht0 : 0 < t := lt_of_lt_of_le (by positivity) ht1
  have hlt1 : Real.log c₁ + Real.log T ≤ Real.log t := by
    rw [← Real.log_mul hc₁.ne' hT0.ne']; exact Real.log_le_log (by positivity) ht1
  have hlt2 : Real.log t ≤ Real.log c₂ + Real.log T := by
    rw [← Real.log_mul (by linarith) hT0.ne']; exact Real.log_le_log ht0 ht2
  have hdiv : Real.log (t / (2 * Real.pi)) = Real.log t - Real.log (2 * Real.pi) :=
    Real.log_div ht0.ne' (by positivity)
  have hθ2 : (0 : ℝ) < 2 * θ := by positivity
  have hq1 : Real.log (molLen θ T) / (2 * θ) ≤ Real.log T / 2 := by
    rw [div_le_iff₀ hθ2]; nlinarith
  have hq2 : Real.log T / 2 - Real.log 2 / (2 * θ) ≤ Real.log (molLen θ T) / (2 * θ) := by
    rw [le_div_iff₀ hθ2]
    have : (Real.log T / 2 - Real.log 2 / (2 * θ)) * (2 * θ) = θ * Real.log T - Real.log 2 := by
      field_simp
    linarith
  have hγ : (0 : ℝ) ≤ Real.eulerMascheroniConstant := by
    linarith [Real.one_half_lt_eulerMascheroniConstant]
  have hpi : 0 ≤ Real.log (2 * Real.pi) := Real.log_nonneg (by nlinarith [Real.pi_gt_three])
  have h2' : 0 ≤ Real.log 2 / (2 * θ) := by
    have : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    positivity
  rw [abs_le]
  constructor
  · nlinarith [neg_abs_le (Real.log c₁), neg_abs_le (Real.log c₂), le_abs_self (Real.log c₁),
      le_abs_self (Real.log c₂)]
  · nlinarith [neg_abs_le (Real.log c₁), neg_abs_le (Real.log c₂), le_abs_self (Real.log c₁),
      le_abs_self (Real.log c₂)]

/-- The remainder scale `(2πN²/t)^{1/4}(1 + log T)³ → 0` uniformly on `[c₁T, c₂T]`. -/
theorem eventually_remainder_scale_le {θ c₁ c₂ : ℝ} (hθ : θ < 1 / 2)
    (hc₁ : 0 < c₁) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ T : ℝ in atTop, ∀ t ∈ Icc (c₁ * T) (c₂ * T),
      (2 * Real.pi * (molLen θ T : ℝ) ^ 2 / t) ^ (1 / 4 : ℝ) * (1 + Real.log T) ^ 3 ≤ ε := by
  set κ : ℝ := (1 - 2 * θ) / 4 with hκ
  have hκ0 : 0 < κ := by rw [hκ]; linarith
  have hlim := (one_add_log_pow_mul_rpow_neg_tendsto 3 hκ0).const_mul
    ((2 * Real.pi / c₁) ^ (1 / 4 : ℝ))
  rw [mul_zero] at hlim
  filter_upwards [hlim.eventually (ge_mem_nhds hε), eventually_ge_atTop 1] with T hT hT1 t ht
  have hT0 : 0 < T := by linarith
  have ht0 : 0 < t := lt_of_lt_of_le (by positivity) ht.1
  have hN : (molLen θ T : ℝ) ≤ T ^ θ := molLen_le hT0.le
  have hN0 : (0 : ℝ) ≤ molLen θ T := Nat.cast_nonneg _
  have hbase : 2 * Real.pi * (molLen θ T : ℝ) ^ 2 / t ≤ (2 * Real.pi / c₁) * T ^ (-(4 * κ)) := by
    have hT2 : (molLen θ T : ℝ) ^ 2 ≤ T ^ (2 * θ) := by
      rw [show (2 : ℝ) * θ = θ * 2 by ring, Real.rpow_mul hT0.le]
      rw [Real.rpow_two]
      exact pow_le_pow_left₀ hN0 hN 2
    have hexp : T ^ (-(4 * κ)) = T ^ (2 * θ) / T := by
      rw [show -(4 * κ) = 2 * θ - 1 by rw [hκ]; ring, Real.rpow_sub hT0, Real.rpow_one]
    rw [hexp, div_le_iff₀ ht0]
    calc 2 * Real.pi * (molLen θ T : ℝ) ^ 2 ≤ 2 * Real.pi * T ^ (2 * θ) := by gcongr
      _ = 2 * Real.pi / c₁ * (T ^ (2 * θ) / T) * (c₁ * T) := by field_simp
      _ ≤ 2 * Real.pi / c₁ * (T ^ (2 * θ) / T) * t := by gcongr; exact ht.1
  have hpos : 0 ≤ 2 * Real.pi * (molLen θ T : ℝ) ^ 2 / t := by positivity
  calc (2 * Real.pi * (molLen θ T : ℝ) ^ 2 / t) ^ (1 / 4 : ℝ) * (1 + Real.log T) ^ 3
      ≤ ((2 * Real.pi / c₁) * T ^ (-(4 * κ))) ^ (1 / 4 : ℝ) * (1 + Real.log T) ^ 3 := by
        have := Real.log_nonneg hT1
        gcongr
    _ = (2 * Real.pi / c₁) ^ (1 / 4 : ℝ) * ((1 + Real.log T) ^ 3 * T ^ (-κ)) := by
        rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hT0.le]
        ring_nf
    _ ≤ ε := hT

/-! ## The remainder on the scale `[c₁T, c₂T]` -/

theorem one_add_log_mul_le {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    1 + (x + y) ≤ (1 + x) * (1 + y) := by nlinarith

/-- `‖E‖ ≤ C (ab)^{1/4} d(ab)(1 + log ab) · (2πN²/t)^{1/4}(1 + log T)³` for `N = ⌊T^θ⌋`. -/
theorem norm_ratioErr_le_scale {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ x : ℝ, 0 < x →
      ‖ZetaNotch.diagHarm x - ((Real.log x : ℂ) / 2 + Real.eulerMascheroniConstant)‖ ≤
        C * x ^ (-(1 / 4) : ℝ))
    {θ T t : ℝ} (hθ : θ ≤ 1) (hT : 1 ≤ T) (hN : 1 ≤ molLen θ T) (ht : 0 < t) {a b : ℕ}
    (hab : Nat.Coprime a b) (ha : 0 < a) (hb : 0 < b) :
    ‖ratioErr (molLen θ T) a b t‖ ≤
      C * (((a * b : ℕ) : ℝ) ^ (1 / 4 : ℝ) * (((a * b).divisors.card : ℝ) *
        (1 + Real.log ((a * b : ℕ) : ℝ)))) *
        ((2 * Real.pi * (molLen θ T : ℝ) ^ 2 / t) ^ (1 / 4 : ℝ) * (1 + Real.log T) ^ 3) := by
  set N := molLen θ T with hNdef
  have hT0 : 0 < T := by linarith
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hlogN : Real.log N ≤ Real.log T := by
    refine Real.log_le_log (by linarith) ((molLen_le hT0.le).trans ?_)
    calc T ^ θ ≤ T ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hT hθ
      _ = T := Real.rpow_one T
  have hlogN0 : 0 ≤ Real.log N := Real.log_nonneg hNR
  have hab1 : (1 : ℝ) ≤ ((a * b : ℕ) : ℝ) := by exact_mod_cast Nat.mul_pos ha hb
  have hlogab : 0 ≤ Real.log ((a * b : ℕ) : ℝ) := Real.log_nonneg hab1
  have hsum := Sieve.sum_gcd_mul_div_le hab ha hb N
  have hlogNab : Real.log ((N * a * b : ℕ) : ℝ) = Real.log N + Real.log ((a * b : ℕ) : ℝ) := by
    rw [show N * a * b = N * (a * b) by ring, Nat.cast_mul,
      Real.log_mul (by positivity) (by positivity)]
  rw [hlogNab] at hsum
  have hsum' : ∑ h ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N,
      ((Nat.gcd (h * a) (k * b) : ℕ) : ℝ) / ((h : ℝ) * k) ≤
        ((a * b).divisors.card : ℝ) * (1 + Real.log ((a * b : ℕ) : ℝ)) * (1 + Real.log T) ^ 3 := by
    refine hsum.trans ?_
    have e1 : (1 + Real.log N) ≤ 1 + Real.log T := by linarith
    have e2 := one_add_log_mul_le hlogN0 hlogab
    have hd : (0 : ℝ) ≤ ((a * b).divisors.card : ℝ) := Nat.cast_nonneg _
    calc ((a * b).divisors.card : ℝ) * (1 + Real.log N) ^ 2 *
          (1 + (Real.log N + Real.log ((a * b : ℕ) : ℝ)))
        ≤ ((a * b).divisors.card : ℝ) * (1 + Real.log N) ^ 2 *
            ((1 + Real.log N) * (1 + Real.log ((a * b : ℕ) : ℝ))) := by gcongr
      _ = ((a * b).divisors.card : ℝ) * (1 + Real.log ((a * b : ℕ) : ℝ)) *
            (1 + Real.log N) ^ 3 := by ring
      _ ≤ _ := by gcongr
  have hE := norm_ratioErr_le hC0 hC N ha hb ht
  have hsplit : (2 * Real.pi * N ^ 2 * a * b / t) ^ (1 / 4 : ℝ) =
      ((a * b : ℕ) : ℝ) ^ (1 / 4 : ℝ) * (2 * Real.pi * (N : ℝ) ^ 2 / t) ^ (1 / 4 : ℝ) := by
    rw [← Real.mul_rpow (by positivity) (by positivity)]
    congr 1
    push_cast
    ring
  rw [hsplit] at hE
  refine hE.trans ?_
  have h0 : 0 ≤ C * (((a * b : ℕ) : ℝ) ^ (1 / 4 : ℝ) *
      (2 * Real.pi * (N : ℝ) ^ 2 / t) ^ (1 / 4 : ℝ)) := by positivity
  calc C * (((a * b : ℕ) : ℝ) ^ (1 / 4 : ℝ) * (2 * Real.pi * (N : ℝ) ^ 2 / t) ^ (1 / 4 : ℝ)) *
        ∑ h ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N,
          ((Nat.gcd (h * a) (k * b) : ℕ) : ℝ) / ((h : ℝ) * k)
      ≤ C * (((a * b : ℕ) : ℝ) ^ (1 / 4 : ℝ) * (2 * Real.pi * (N : ℝ) ^ 2 / t) ^ (1 / 4 : ℝ)) *
          (((a * b).divisors.card : ℝ) * (1 + Real.log ((a * b : ℕ) : ℝ)) *
            (1 + Real.log T) ^ 3) := mul_le_mul_of_nonneg_left hsum' h0
    _ = _ := by ring

/-! ## The three uniform statements -/

theorem twistForm₀_one_one (N : ℕ) : Sieve.twistForm₀ N 1 1 = Sieve.linearMollifierForm₀ N := by
  simp [Sieve.twistForm₀, Sieve.linearMollifierForm₀]

theorem twistForm₁_one_one (N : ℕ) : Sieve.twistForm₁ N 1 1 = Sieve.linearMollifierForm₁ N := by
  simp [Sieve.twistForm₁, Sieve.linearMollifierForm₁]

/-- The main part `(½ log(t/2πab) + γ) S₀ + ½ S₁` against the centring `log ⌊T^θ⌋/(2θ)`. -/
theorem abs_main_sub_le {θ D L S₀ S₁ c ℓ : ℝ} (hθ : 0 < θ) (hL : 1 ≤ L) (hℓ : 0 ≤ ℓ)
    (hc : |c - L / (2 * θ)| ≤ D) :
    |(c - ℓ / 2) * S₀ + S₁ / 2| ≤ (1 / (2 * θ) + D + ℓ / 2) * |S₀ * L| + |S₁| / 2 := by
  have hL0 : 0 < L := by linarith
  have hD : 0 ≤ D := (abs_nonneg _).trans hc
  have hcL : |(c - ℓ / 2) / L| ≤ 1 / (2 * θ) + D + ℓ / 2 := by
    rw [abs_div, abs_of_pos hL0, div_le_iff₀ hL0]
    have h1 : |c - ℓ / 2| ≤ L / (2 * θ) + D + ℓ / 2 := by
      have := abs_sub (c - L / (2 * θ)) (ℓ / 2 - L / (2 * θ))
      have e : c - ℓ / 2 = (c - L / (2 * θ)) - (ℓ / 2 - L / (2 * θ)) := by ring
      rw [e]
      have h2 : |ℓ / 2 - L / (2 * θ)| ≤ ℓ / 2 + L / (2 * θ) := by
        rw [abs_le]; constructor <;> nlinarith [div_nonneg hL0.le (by linarith : (0:ℝ) ≤ 2 * θ)]
      linarith
    have h3 : L / (2 * θ) = 1 / (2 * θ) * L := by ring
    nlinarith [div_nonneg hL0.le (by linarith : (0:ℝ) ≤ 2 * θ)]
  calc |(c - ℓ / 2) * S₀ + S₁ / 2| ≤ |(c - ℓ / 2) * S₀| + |S₁ / 2| := abs_add_le _ _
    _ = |(c - ℓ / 2) / L| * |S₀ * L| + |S₁| / 2 := by
        rw [abs_div, abs_div, abs_two, abs_mul, abs_mul, abs_of_pos hL0]
        field_simp
    _ ≤ (1 / (2 * θ) + D + ℓ / 2) * |S₀ * L| + |S₁| / 2 := by
        gcongr

theorem log_div_two_pi_mul {t : ℝ} (ht : 0 < t) {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    Real.log (t / (2 * Real.pi * a * b)) =
      Real.log (t / (2 * Real.pi)) - Real.log ((a * b : ℕ) : ℝ) := by
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  rw [← Real.log_div (by positivity) (by positivity)]
  congr 1
  push_cast
  field_simp

/-- **The diagonal ratio form.** `F(1,1,t) → ½ + 1/(2θ)` uniformly on `[c₁T, c₂T]`. -/
theorem ratioForm_one_one_uniform {θ c₁ c₂ : ℝ} (hθ0 : 0 < θ) (hθ : θ < 1 / 2) (hc₁ : 0 < c₁)
    (hc : c₁ ≤ c₂) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ T : ℝ in atTop, ∀ t ∈ Icc (c₁ * T) (c₂ * T),
      ‖ratioForm (molLen θ T) 1 1 t - ((1 / 2 + 1 / (2 * θ) : ℝ) : ℂ)‖ ≤ ε := by
  obtain ⟨C, hC0, hC⟩ := ZetaNotch.exists_norm_diagHarm_sub_le
  obtain ⟨D, hD0, hDev⟩ := exists_centre_bound hθ0 hc₁ hc
  set ε' : ℝ := ε / (1 / (2 * θ) + 4 + C) with hε'
  have hden : 0 < 1 / (2 * θ) + 4 + C := by positivity
  have hε'0 : 0 < ε' := div_pos hε hden
  have hS₀ := (Sieve.tendsto_linearMollifierForm₀_mul_log.comp (tendsto_molLen hθ0)).eventually
    (Metric.closedBall_mem_nhds 1 (lt_min hε'0 one_pos))
  have hS₁ := (Sieve.tendsto_linearMollifierForm₁.comp (tendsto_molLen hθ0)).eventually
    (Metric.closedBall_mem_nhds 1 hε'0)
  have hLD := (tendsto_log_molLen hθ0).eventually (eventually_ge_atTop (max 1 (D / ε')))
  have hN1 := (tendsto_molLen hθ0).eventually (eventually_ge_atTop 2)
  filter_upwards [hDev, hS₀, hS₁, hLD, hN1, eventually_ge_atTop 1,
    eventually_remainder_scale_le (c₂ := c₂) hθ hc₁ hε'0] with T hT hT₀ hT₁ hTL hTN hT1 hTE t ht
  have hT0 : 0 < T := by linarith
  have ht0 : 0 < t := lt_of_lt_of_le (by positivity) ht.1
  set N := molLen θ T
  set L := Real.log N
  have hL1 : 1 ≤ L := (le_max_left _ _).trans hTL
  have hL0 : 0 < L := by linarith
  have hDL : D ≤ ε' * L := by
    have := (le_max_right _ _).trans hTL
    rwa [div_le_iff₀ hε'0, mul_comm] at this
  simp only [Function.comp, Real.dist_eq] at hT₀ hT₁
  have hS₀' : |Sieve.linearMollifierForm₀ N * L - 1| ≤ ε' := hT₀.trans (min_le_left _ _)
  have hS₀1 : |Sieve.linearMollifierForm₀ N * L - 1| ≤ 1 := hT₀.trans (min_le_right _ _)
  have hE := norm_ratioErr_le_scale (θ := θ) (T := T) hC0 hC (by linarith) hT1 (by omega) ht0
    (Nat.coprime_one_left 1) one_pos one_pos
  simp only [mul_one, Nat.divisors_one, Finset.card_singleton, Nat.cast_one, Real.log_one,
    add_zero, Real.one_rpow] at hE
  rw [ratioForm_eq N one_pos one_pos ht0, twistForm₀_one_one, twistForm₁_one_one]
  have hcentre := hT t ht
  set c := Real.log (t / (2 * Real.pi)) / 2 + Real.eulerMascheroniConstant
  have hmain : |(Real.log (t / (2 * Real.pi * (1 : ℕ) * (1 : ℕ))) / 2 +
      Real.eulerMascheroniConstant) * Sieve.linearMollifierForm₀ N +
        Sieve.linearMollifierForm₁ N / 2 - (1 / 2 + 1 / (2 * θ))| ≤ ε' * (1 / (2 * θ) + 4) := by
    have e : (Real.log (t / (2 * Real.pi * (1 : ℕ) * (1 : ℕ))) / 2 +
        Real.eulerMascheroniConstant) * Sieve.linearMollifierForm₀ N +
          Sieve.linearMollifierForm₁ N / 2 - (1 / 2 + 1 / (2 * θ)) =
        (Sieve.linearMollifierForm₀ N * L - 1) / (2 * θ) +
          (c - L / (2 * θ)) / L * (Sieve.linearMollifierForm₀ N * L) +
            (Sieve.linearMollifierForm₁ N - 1) / 2 := by
      simp only [Nat.cast_one, mul_one, c]
      field_simp
      ring
    rw [e]
    have hθ2 : (0 : ℝ) < 2 * θ := by positivity
    have h1 : |(Sieve.linearMollifierForm₀ N * L - 1) / (2 * θ)| ≤ ε' * (1 / (2 * θ)) := by
      rw [abs_div, abs_of_pos hθ2, div_le_iff₀ hθ2]
      field_simp
      linarith
    have h2 : |(c - L / (2 * θ)) / L * (Sieve.linearMollifierForm₀ N * L)| ≤ ε' * 2 := by
      rw [abs_mul, abs_div, abs_of_pos hL0]
      have hb : |Sieve.linearMollifierForm₀ N * L| ≤ 2 := by
        have := abs_sub_abs_le_abs_sub (Sieve.linearMollifierForm₀ N * L) 1
        rw [abs_one] at this
        linarith
      have hq : |c - L / (2 * θ)| / L ≤ ε' := by
        rw [div_le_iff₀ hL0]; linarith
      exact mul_le_mul hq hb (abs_nonneg _) hε'0.le
    have h3 : |(Sieve.linearMollifierForm₁ N - 1) / 2| ≤ ε' := by
      rw [abs_div, abs_two]; linarith [abs_nonneg (Sieve.linearMollifierForm₁ N - 1)]
    refine (abs_add_three _ _ _).trans ?_
    nlinarith
  calc ‖((((Real.log (t / (2 * Real.pi * (1 : ℕ) * (1 : ℕ))) / 2 +
          Real.eulerMascheroniConstant) * Sieve.linearMollifierForm₀ N +
            Sieve.linearMollifierForm₁ N / 2 : ℝ) : ℂ) + ratioErr N 1 1 t) -
        ((1 / 2 + 1 / (2 * θ) : ℝ) : ℂ)‖
      ≤ ‖(((Real.log (t / (2 * Real.pi * (1 : ℕ) * (1 : ℕ))) / 2 +
          Real.eulerMascheroniConstant) * Sieve.linearMollifierForm₀ N +
            Sieve.linearMollifierForm₁ N / 2 - (1 / 2 + 1 / (2 * θ)) : ℝ) : ℂ)‖ +
          ‖ratioErr N 1 1 t‖ := by
        rw [Complex.ofReal_sub, show ∀ x y z : ℂ, x + y - z = (x - z) + y from fun x y z => by
          ring]
        exact norm_add_le _ _
    _ ≤ ε' * (1 / (2 * θ) + 4) + C * ε' := by
        rw [Complex.norm_real, Real.norm_eq_abs]
        gcongr
        exact hE.trans (mul_le_mul_of_nonneg_left (hTE t ht) hC0)
    _ = ε := by rw [hε']; field_simp

/-- **Cancellation.** For fixed coprime `(a,b) ≠ (1,1)`, `F(a,b,t) → 0` uniformly on
`[c₁T, c₂T]`. -/
theorem ratioForm_uniform_of_ne {θ c₁ c₂ : ℝ} (hθ0 : 0 < θ) (hθ : θ < 1 / 2) (hc₁ : 0 < c₁)
    (hc : c₁ ≤ c₂) {a b : ℕ} (hab : Nat.Coprime a b) (ha : 0 < a) (hb : 0 < b)
    (hab1 : 1 < a ∨ 1 < b) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ T : ℝ in atTop, ∀ t ∈ Icc (c₁ * T) (c₂ * T), ‖ratioForm (molLen θ T) a b t‖ ≤ ε := by
  obtain ⟨C, hC0, hC⟩ := ZetaNotch.exists_norm_diagHarm_sub_le
  obtain ⟨D, hD0, hDev⟩ := exists_centre_bound hθ0 hc₁ hc
  set ℓ : ℝ := Real.log ((a * b : ℕ) : ℝ)
  have hℓ : 0 ≤ ℓ := Real.log_nonneg (by exact_mod_cast Nat.mul_pos ha hb)
  set A : ℝ := 1 / (2 * θ) + D + ℓ / 2
  have hA : 0 ≤ A := by positivity
  set B : ℝ := ((a * b : ℕ) : ℝ) ^ (1 / 4 : ℝ) * (((a * b).divisors.card : ℝ) * (1 + ℓ))
  have hB : 0 ≤ B := by positivity
  set ε' : ℝ := ε / (A + 1 + C * B + 1) with hε'
  have hden : 0 < A + 1 + C * B + 1 := by positivity
  have hε'0 : 0 < ε' := div_pos hε hden
  have hS₀ := ((Sieve.tendsto_twistForm₀_mul_log hab ha hb hab1).comp (tendsto_molLen hθ0)).eventually
    (Metric.closedBall_mem_nhds 0 hε'0)
  have hS₁ := ((Sieve.tendsto_twistForm₁ hab ha hb hab1).comp (tendsto_molLen hθ0)).eventually
    (Metric.closedBall_mem_nhds 0 hε'0)
  have hLD := (tendsto_log_molLen hθ0).eventually (eventually_ge_atTop 1)
  have hN1 := (tendsto_molLen hθ0).eventually (eventually_ge_atTop 2)
  filter_upwards [hDev, hS₀, hS₁, hLD, hN1, eventually_ge_atTop 1,
    eventually_remainder_scale_le (c₂ := c₂) hθ hc₁ hε'0] with T hT hT₀ hT₁ hTL hTN hT1 hTE t ht
  have ht0 : 0 < t := lt_of_lt_of_le (by positivity) ht.1
  set N := molLen θ T
  simp only [Function.comp, Real.dist_eq, sub_zero]
    at hT₀ hT₁
  have hE := norm_ratioErr_le_scale (θ := θ) (T := T) hC0 hC (by linarith) hT1 (by omega) ht0
    hab ha hb
  rw [ratioForm_eq N ha hb ht0, log_div_two_pi_mul ht0 ha hb]
  have hmain := abs_main_sub_le (S₀ := Sieve.twistForm₀ N a b) (S₁ := Sieve.twistForm₁ N a b)
    hθ0 hTL hℓ (hT t ht)
  have e : (Real.log (t / (2 * Real.pi)) - ℓ) / 2 + Real.eulerMascheroniConstant =
      Real.log (t / (2 * Real.pi)) / 2 + Real.eulerMascheroniConstant - ℓ / 2 := by ring
  rw [e]
  calc ‖((((Real.log (t / (2 * Real.pi)) / 2 + Real.eulerMascheroniConstant - ℓ / 2) *
          Sieve.twistForm₀ N a b + Sieve.twistForm₁ N a b / 2 : ℝ) : ℂ) + ratioErr N a b t)‖
      ≤ |(Real.log (t / (2 * Real.pi)) / 2 + Real.eulerMascheroniConstant - ℓ / 2) *
          Sieve.twistForm₀ N a b + Sieve.twistForm₁ N a b / 2| + ‖ratioErr N a b t‖ := by
        refine (norm_add_le _ _).trans ?_
        rw [Complex.norm_real, Real.norm_eq_abs]
    _ ≤ A * ε' + ε' / 2 + C * B * ε' := by
        gcongr
        · refine hmain.trans ?_
          gcongr
        · calc ‖ratioErr N a b t‖ ≤ C * B * ((2 * Real.pi * (N : ℝ) ^ 2 / t) ^ (1 / 4 : ℝ) *
                (1 + Real.log T) ^ 3) := hE
            _ = C * (B * ((2 * Real.pi * (N : ℝ) ^ 2 / t) ^ (1 / 4 : ℝ) *
                (1 + Real.log T) ^ 3)) := by ring
            _ ≤ C * (B * ε') :=
                mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hTE t ht) hB) hC0
            _ = C * B * ε' := by ring
    _ ≤ ε := by
        rw [hε']
        have : A * (ε / (A + 1 + C * B + 1)) + ε / (A + 1 + C * B + 1) / 2 +
            C * B * (ε / (A + 1 + C * B + 1)) =
            ε * ((A + 1 / 2 + C * B) / (A + 1 + C * B + 1)) := by field_simp
        rw [this]
        refine mul_le_of_le_one_right hε.le ?_
        rw [div_le_one hden]
        linarith

/-! ## The polynomial envelope -/

theorem two_pow_card_primeFactors_le_card_divisors {n : ℕ} (hn : n ≠ 0) :
    (2 : ℝ) ^ n.primeFactors.card ≤ n.divisors.card := by
  rw [Nat.card_divisors hn, ← Finset.prod_const]
  push_cast
  refine Finset.prod_le_prod (fun _ _ => by norm_num) fun p hp => ?_
  have h1 : 1 ≤ n.factorization p :=
    Nat.one_le_iff_ne_zero.mpr ((Sieve.factorization_ne_zero_iff_mem_primeFactors n p).mpr hp)
  have : (1 : ℝ) ≤ n.factorization p := by exact_mod_cast h1
  linarith

theorem one_add_log_le_rpow {x : ℝ} (hx : 1 ≤ x) {ε : ℝ} (hε : 0 < ε) :
    1 + Real.log x ≤ (1 + 1 / ε) * x ^ ε := by
  have h1 : 1 ≤ x ^ ε := Real.one_le_rpow hx hε.le
  have h2 := Real.log_le_rpow_div (by linarith : (0 : ℝ) ≤ x) hε
  have : x ^ ε / ε = 1 / ε * x ^ ε := by ring
  nlinarith

theorem card_divisors_le_rpow' {n : ℕ} (hn : 0 < n) :
    (n.divisors.card : ℝ) ≤ Sieve.divisorBoundConst (1 / 100) * (n : ℝ) ^ (1 / 100 : ℝ) :=
  Sieve.card_divisors_le_rpow (by norm_num) hn.ne'

theorem twistSize_le_rpow {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    Sieve.twistSize a b ≤
      Sieve.divisorBoundConst (1 / 100) ^ 5 * ((a * b : ℕ) : ℝ) ^ (3 / 100 : ℝ) := by
  set D := Sieve.divisorBoundConst (1 / 100)
  have hD : 0 ≤ D := (Sieve.divisorBoundConst_pos (by norm_num)).le
  have haR : (0 : ℝ) ≤ a := Nat.cast_nonneg _
  have hbR : (0 : ℝ) ≤ b := Nat.cast_nonneg _
  have hab := card_divisors_le_rpow' (Nat.mul_pos ha hb)
  have hda := card_divisors_le_rpow' ha
  have hdb := card_divisors_le_rpow' hb
  have h2a := two_pow_card_primeFactors_le_card_divisors ha.ne'
  have h2b := two_pow_card_primeFactors_le_card_divisors hb.ne'
  unfold Sieve.twistSize
  have hba : ((b.divisors.card : ℝ) * a.divisors.card) ≤
      D * (b : ℝ) ^ (1 / 100 : ℝ) * (D * (a : ℝ) ^ (1 / 100 : ℝ)) :=
    mul_le_mul hdb hda (Nat.cast_nonneg _) (by positivity)
  have h2 : (2 : ℝ) ^ b.primeFactors.card * 2 ^ a.primeFactors.card ≤
      D * (b : ℝ) ^ (1 / 100 : ℝ) * (D * (a : ℝ) ^ (1 / 100 : ℝ)) :=
    (mul_le_mul h2b h2a (by positivity) (Nat.cast_nonneg _)).trans hba
  have hprod : (b : ℝ) ^ (1 / 100 : ℝ) * (a : ℝ) ^ (1 / 100 : ℝ) =
      ((a * b : ℕ) : ℝ) ^ (1 / 100 : ℝ) := by
    rw [← Real.mul_rpow hbR haR]; push_cast; ring_nf
  calc ((a * b).divisors.card : ℝ) * ((b.divisors.card : ℝ) * a.divisors.card) *
        ((2 : ℝ) ^ b.primeFactors.card * 2 ^ a.primeFactors.card)
      ≤ (D * ((a * b : ℕ) : ℝ) ^ (1 / 100 : ℝ)) *
          (D * (b : ℝ) ^ (1 / 100 : ℝ) * (D * (a : ℝ) ^ (1 / 100 : ℝ))) *
          (D * (b : ℝ) ^ (1 / 100 : ℝ) * (D * (a : ℝ) ^ (1 / 100 : ℝ))) := by
        gcongr
    _ = D ^ 5 * (((a * b : ℕ) : ℝ) ^ (1 / 100 : ℝ) * ((a * b : ℕ) : ℝ) ^ (1 / 100 : ℝ) *
          ((a * b : ℕ) : ℝ) ^ (1 / 100 : ℝ)) := by
        rw [← hprod]; ring
    _ = D ^ 5 * ((a * b : ℕ) : ℝ) ^ (3 / 100 : ℝ) := by
        rw [← Real.rpow_add' (Nat.cast_nonneg _) (by norm_num),
          ← Real.rpow_add' (Nat.cast_nonneg _) (by norm_num)]
        norm_num

/-- **The polynomial envelope** `‖F(a,b,t)‖ ≤ C (ab)^{1/3}`, uniformly in coprime `a, b` and
`t ∈ [c₁T, c₂T]`. -/
theorem exists_norm_ratioForm_le {θ c₁ c₂ : ℝ} (hθ0 : 0 < θ) (hθ : θ < 1 / 2) (hc₁ : 0 < c₁)
    (hc : c₁ ≤ c₂) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ T : ℝ in atTop, ∀ a b : ℕ, Nat.Coprime a b → 0 < a → 0 < b →
      ∀ t ∈ Icc (c₁ * T) (c₂ * T),
        ‖ratioForm (molLen θ T) a b t‖ ≤ C * ((a * b : ℕ) : ℝ) ^ (1 / 3 : ℝ) := by
  obtain ⟨CH, hCH0, hCH⟩ := ZetaNotch.exists_norm_diagHarm_sub_le
  obtain ⟨D, hD0, hDev⟩ := exists_centre_bound hθ0 hc₁ hc
  obtain ⟨M, hM0, hMev⟩ := Sieve.exists_twistForm_envelope
  set Dv := Sieve.divisorBoundConst (1 / 100)
  have hDv : 0 ≤ Dv := (Sieve.divisorBoundConst_pos (by norm_num)).le
  set C₁ : ℝ := (1 / (2 * θ) + D + 2) * M
  have hC₁ : 0 ≤ C₁ := by positivity
  refine ⟨C₁ * (101 * Dv ^ 5) + CH * (101 * Dv), by positivity, ?_⟩
  have hLD := (tendsto_log_molLen hθ0).eventually (eventually_ge_atTop 1)
  have hN1 := (tendsto_molLen hθ0).eventually (eventually_ge_atTop 2)
  have hMT := (tendsto_molLen hθ0).eventually hMev
  filter_upwards [hDev, hMT, hLD, hN1, eventually_ge_atTop 1,
    eventually_remainder_scale_le (c₂ := c₂) hθ hc₁ one_pos] with T hT hTM hTL hTN hT1 hTE
    a b hab ha hb t ht
  have ht0 : 0 < t := lt_of_lt_of_le (by positivity) ht.1
  set N := molLen θ T
  set ℓ : ℝ := Real.log ((a * b : ℕ) : ℝ)
  have hab1 : (1 : ℝ) ≤ ((a * b : ℕ) : ℝ) := by exact_mod_cast Nat.mul_pos ha hb
  have hℓ : 0 ≤ ℓ := Real.log_nonneg hab1
  set L := Real.log N
  have hL0 : 0 < L := by linarith
  obtain ⟨hS₀, hS₁⟩ := hTM a b hab ha hb
  have hK0 := Sieve.twistSize_nonneg a b
  have hE := norm_ratioErr_le_scale (θ := θ) (T := T) hCH0 hCH (by linarith) hT1 (by omega) ht0
    hab ha hb
  have hE' : ‖ratioErr N a b t‖ ≤ CH * (((a * b : ℕ) : ℝ) ^ (1 / 4 : ℝ) *
      (((a * b).divisors.card : ℝ) * (1 + ℓ))) := by
    refine hE.trans ?_
    have : 0 ≤ CH * (((a * b : ℕ) : ℝ) ^ (1 / 4 : ℝ) * (((a * b).divisors.card : ℝ) * (1 + ℓ))) := by
      positivity
    calc _ ≤ CH * (((a * b : ℕ) : ℝ) ^ (1 / 4 : ℝ) * (((a * b).divisors.card : ℝ) * (1 + ℓ))) * 1 :=
          mul_le_mul_of_nonneg_left (hTE t ht) this
      _ = _ := mul_one _
  rw [ratioForm_eq N ha hb ht0, log_div_two_pi_mul ht0 ha hb]
  have hmain := abs_main_sub_le (S₀ := Sieve.twistForm₀ N a b) (S₁ := Sieve.twistForm₁ N a b)
    hθ0 hTL hℓ (hT t ht)
  have e : (Real.log (t / (2 * Real.pi)) - ℓ) / 2 + Real.eulerMascheroniConstant =
      Real.log (t / (2 * Real.pi)) / 2 + Real.eulerMascheroniConstant - ℓ / 2 := by ring
  rw [e]
  have hS₀' : |Sieve.twistForm₀ N a b * L| ≤ M * Sieve.twistSize a b := by
    rw [abs_mul, abs_of_pos hL0]; exact hS₀
  have hmain' : |(Real.log (t / (2 * Real.pi)) / 2 + Real.eulerMascheroniConstant - ℓ / 2) *
      Sieve.twistForm₀ N a b + Sieve.twistForm₁ N a b / 2| ≤ C₁ * ((1 + ℓ) * Sieve.twistSize a b) := by
    refine hmain.trans ?_
    have hA : 1 / (2 * θ) + D + ℓ / 2 ≤ (1 / (2 * θ) + D + 1) * (1 + ℓ) := by
      have : 0 ≤ 1 / (2 * θ) + D := by positivity
      nlinarith
    calc (1 / (2 * θ) + D + ℓ / 2) * |Sieve.twistForm₀ N a b * L| + |Sieve.twistForm₁ N a b| / 2
        ≤ ((1 / (2 * θ) + D + 1) * (1 + ℓ)) * (M * Sieve.twistSize a b) +
            M * ((1 + ℓ) * Sieve.twistSize a b) / 2 := by
          gcongr
      _ ≤ C₁ * ((1 + ℓ) * Sieve.twistSize a b) := by
          have hx : 0 ≤ M * ((1 + ℓ) * Sieve.twistSize a b) := by positivity
          have e1 : ((1 / (2 * θ) + D + 1) * (1 + ℓ)) * (M * Sieve.twistSize a b) =
              (1 / (2 * θ) + D + 1) * (M * ((1 + ℓ) * Sieve.twistSize a b)) := by ring
          have e2 : C₁ * ((1 + ℓ) * Sieve.twistSize a b) =
              (1 / (2 * θ) + D + 2) * (M * ((1 + ℓ) * Sieve.twistSize a b)) := by ring
          rw [e1, e2]
          nlinarith
  have hlogab := one_add_log_le_rpow hab1 (ε := 1 / 100) (by norm_num)
  have hK := twistSize_le_rpow ha hb
  have hd := card_divisors_le_rpow' (Nat.mul_pos ha hb)
  have hab0 : (0 : ℝ) ≤ ((a * b : ℕ) : ℝ) := Nat.cast_nonneg _
  have hP1 : (1 + ℓ) * Sieve.twistSize a b ≤ 101 * Dv ^ 5 * ((a * b : ℕ) : ℝ) ^ (1 / 3 : ℝ) := by
    calc (1 + ℓ) * Sieve.twistSize a b
        ≤ ((1 + 1 / (1 / 100)) * ((a * b : ℕ) : ℝ) ^ (1 / 100 : ℝ)) *
            (Dv ^ 5 * ((a * b : ℕ) : ℝ) ^ (3 / 100 : ℝ)) :=
          mul_le_mul hlogab hK hK0 (by positivity)
      _ = 101 * Dv ^ 5 * ((a * b : ℕ) : ℝ) ^ (4 / 100 : ℝ) := by
          rw [show (4 / 100 : ℝ) = 1 / 100 + 3 / 100 by norm_num, Real.rpow_add' hab0 (by norm_num)]
          ring
      _ ≤ 101 * Dv ^ 5 * ((a * b : ℕ) : ℝ) ^ (1 / 3 : ℝ) :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hab1 (by norm_num))
            (by positivity)
  have hP2 : ((a * b : ℕ) : ℝ) ^ (1 / 4 : ℝ) * (((a * b).divisors.card : ℝ) * (1 + ℓ)) ≤
      101 * Dv * ((a * b : ℕ) : ℝ) ^ (1 / 3 : ℝ) := by
    calc ((a * b : ℕ) : ℝ) ^ (1 / 4 : ℝ) * (((a * b).divisors.card : ℝ) * (1 + ℓ))
        ≤ ((a * b : ℕ) : ℝ) ^ (1 / 4 : ℝ) * ((Dv * ((a * b : ℕ) : ℝ) ^ (1 / 100 : ℝ)) *
            ((1 + 1 / (1 / 100)) * ((a * b : ℕ) : ℝ) ^ (1 / 100 : ℝ))) := by
          gcongr
      _ = 101 * Dv * ((a * b : ℕ) : ℝ) ^ (27 / 100 : ℝ) := by
          rw [show (27 / 100 : ℝ) = 1 / 4 + 1 / 100 + 1 / 100 by norm_num,
            Real.rpow_add' hab0 (by norm_num), Real.rpow_add' hab0 (by norm_num)]
          ring
      _ ≤ 101 * Dv * ((a * b : ℕ) : ℝ) ^ (1 / 3 : ℝ) :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hab1 (by norm_num))
            (by positivity)
  calc ‖((((Real.log (t / (2 * Real.pi)) / 2 + Real.eulerMascheroniConstant - ℓ / 2) *
          Sieve.twistForm₀ N a b + Sieve.twistForm₁ N a b / 2 : ℝ) : ℂ) + ratioErr N a b t)‖
      ≤ |(Real.log (t / (2 * Real.pi)) / 2 + Real.eulerMascheroniConstant - ℓ / 2) *
          Sieve.twistForm₀ N a b + Sieve.twistForm₁ N a b / 2| + ‖ratioErr N a b t‖ := by
        refine (norm_add_le _ _).trans ?_
        rw [Complex.norm_real, Real.norm_eq_abs]
    _ ≤ C₁ * ((1 + ℓ) * Sieve.twistSize a b) +
          CH * (((a * b : ℕ) : ℝ) ^ (1 / 4 : ℝ) * (((a * b).divisors.card : ℝ) * (1 + ℓ))) :=
        add_le_add hmain' hE'
    _ ≤ C₁ * (101 * Dv ^ 5 * ((a * b : ℕ) : ℝ) ^ (1 / 3 : ℝ)) +
          CH * (101 * Dv * ((a * b : ℕ) : ℝ) ^ (1 / 3 : ℝ)) := by gcongr
    _ = (C₁ * (101 * Dv ^ 5) + CH * (101 * Dv)) * ((a * b : ℕ) : ℝ) ^ (1 / 3 : ℝ) := by ring

end

end RHTower.VerticalAP
