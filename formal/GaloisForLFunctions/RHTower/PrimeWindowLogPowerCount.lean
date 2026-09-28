import GaloisForLFunctions.RHTower.WindowBudget
import GaloisForLFunctions.RHTower.Sieve.ChebyshevThetaBigO

/-!
# Prime counts in windows of length `R/(log R)^B`

The de la Vallée Poussin error `θ(t) - t = O(t e^{-c√log t})` beats every power of the logarithm:
`|θ(t) - t| ≤ C_A t/(log t)^A`.  Every prime `p ∈ (a, b]` has `log a < log p ≤ log b`, so

`#{p ∈ (a,b]} · log a ≤ θ(b) - θ(a) ≤ #{p ∈ (a,b]} · log b`.

Hence, uniformly for windows `(u, v] ⊆ [R, 2R]` of length at least `R/(log R)^B`,

* `#{p ∈ (u, v]} ≤ (1 + ε)(v - u)/log R`,
* `#{p ∈ (u/q, v/q]} ≥ (1 - ε)(v - u)/(q log R)` for `2 ≤ q ≤ 5`,

for every fixed `ε > 0` and all large `R`.
-/

open Finset Filter Topology

noncomputable section

namespace RHTower.PrimeCells

/-- `e^{-c√v} ≤ (2A)!/(c^{2A} v^A)` for `v ≥ 1`, from `x^n/n! ≤ e^x`. -/
theorem exp_neg_mul_sqrt_le {c v : ℝ} (hc : 0 < c) (hv : 1 ≤ v) (A : ℕ) :
    Real.exp (-c * Real.sqrt v) ≤ (2 * A).factorial / c ^ (2 * A) / v ^ A := by
  have hsv : 0 < Real.sqrt v := Real.sqrt_pos.mpr (by linarith)
  have h := Real.pow_div_factorial_le_exp (c * Real.sqrt v) (by positivity) (2 * A)
  have hsq : Real.sqrt v ^ (2 * A) = v ^ A := by
    rw [pow_mul, Real.sq_sqrt (by linarith)]
  have hf : (0 : ℝ) < (2 * A).factorial := by exact_mod_cast Nat.factorial_pos _
  have hv0 : 0 < v ^ A := by positivity
  rw [neg_mul, Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by positivity)]
  calc ((2 * A).factorial / c ^ (2 * A) / v ^ A)⁻¹
      = (c * Real.sqrt v) ^ (2 * A) / (2 * A).factorial := by
        rw [mul_pow, hsq]; field_simp
    _ ≤ Real.exp (c * Real.sqrt v) := h

/-- **The prime number theorem with a log-power error.**  `|θ(t) - t| ≤ C t/(log t)^A` for all
large `t`. -/
theorem exists_abs_theta_sub_le (A : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∃ T : ℝ, 3 ≤ T ∧ ∀ t : ℝ, T ≤ t →
      |Chebyshev.theta t - t| ≤ C * t / Real.log t ^ A := by
  obtain ⟨c, hc0, hO⟩ := Sieve.chebyshevTheta_sub_id_isBigO
  obtain ⟨K, hK⟩ := Asymptotics.isBigO_iff.mp hO
  obtain ⟨T₀, hT₀⟩ := eventually_atTop.mp hK
  set D : ℝ := (2 * A).factorial / c ^ (2 * A) with hD
  have hD0 : 0 < D := by
    have : (0 : ℝ) < (2 * A).factorial := by exact_mod_cast Nat.factorial_pos _
    positivity
  refine ⟨(|K| + 1) * D, by positivity, max T₀ 3, le_max_right _ _, fun t ht => ?_⟩
  have ht3 : 3 ≤ t := (le_max_right _ _).trans ht
  have hlog1 : 1 ≤ Real.log t := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) (by linarith [Real.exp_one_lt_d9])
  have h := hT₀ t ((le_max_left _ _).trans ht)
  simp only [Pi.sub_apply, id, Real.norm_eq_abs] at h
  have hE0 : 0 ≤ t * Real.exp (-c * Real.sqrt (Real.log t)) := by positivity
  rw [abs_of_nonneg hE0] at h
  have he := exp_neg_mul_sqrt_le hc0 hlog1 A
  have hlogA : 0 < Real.log t ^ A := by positivity
  have hK1 : K ≤ |K| + 1 := by have := le_abs_self K; linarith
  calc |Chebyshev.theta t - t| ≤ K * (t * Real.exp (-c * Real.sqrt (Real.log t))) := h
    _ ≤ (|K| + 1) * (t * Real.exp (-c * Real.sqrt (Real.log t))) :=
        mul_le_mul_of_nonneg_right hK1 hE0
    _ ≤ (|K| + 1) * (t * (D / Real.log t ^ A)) := by
        gcongr
    _ = (|K| + 1) * D * t / Real.log t ^ A := by ring

/-- Every window prime exceeds `a`, so `#(a,b] · log a ≤ θ(b) - θ(a)`. -/
theorem card_windowPrimes_mul_log_le {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    ((windowPrimes a b).card : ℝ) * Real.log a ≤ Chebyshev.theta b - Chebyshev.theta a := by
  rw [← sum_log_windowPrimes hab]
  have h := Finset.card_nsmul_le_sum (windowPrimes a b) (fun p => Real.log (p : ℝ))
    (Real.log a) (fun p hp => by
      obtain ⟨-, hlt, -⟩ := (mem_windowPrimes (by linarith) (by linarith)).mp hp
      exact Real.log_le_log (by linarith) hlt.le)
  rwa [nsmul_eq_mul] at h

/-- Every window prime is at most `b`, so `θ(b) - θ(a) ≤ #(a,b] · log b`. -/
theorem theta_sub_le_card_mul_log {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    Chebyshev.theta b - Chebyshev.theta a ≤ ((windowPrimes a b).card : ℝ) * Real.log b := by
  rw [← sum_log_windowPrimes hab]
  have h := Finset.sum_le_card_nsmul (windowPrimes a b) (fun p => Real.log (p : ℝ))
    (Real.log b) (fun p hp => by
      obtain ⟨hpr, -, hle⟩ := (mem_windowPrimes ha (by linarith)).mp hp
      exact Real.log_le_log (by exact_mod_cast hpr.pos) hle)
  rwa [nsmul_eq_mul] at h

/-- The θ-increment of a window beyond `T` is `b - a` up to `2Cb/(log a)^A`. -/
theorem abs_theta_increment_le {C T : ℝ} {A : ℕ} (hC : 0 ≤ C) (hT : 3 ≤ T)
    (hθ : ∀ t : ℝ, T ≤ t → |Chebyshev.theta t - t| ≤ C * t / Real.log t ^ A)
    {a b : ℝ} (ha : T ≤ a) (hab : a ≤ b) :
    |Chebyshev.theta b - Chebyshev.theta a - (b - a)| ≤ 2 * C * b / Real.log a ^ A := by
  have ha1 : 1 < a := by linarith
  have hloga : 0 < Real.log a := Real.log_pos ha1
  have hlogab : Real.log a ≤ Real.log b := Real.log_le_log (by linarith) hab
  have hA : 0 < Real.log a ^ A := by positivity
  have hAb : Real.log a ^ A ≤ Real.log b ^ A := by gcongr
  have h1 := hθ b (ha.trans hab)
  have h2 := hθ a ha
  have e1 : C * b / Real.log b ^ A ≤ C * b / Real.log a ^ A := by
    have : 0 ≤ C * b := by have : 0 ≤ b := by linarith
                           positivity
    exact div_le_div_of_nonneg_left this hA hAb
  have e2 : C * a / Real.log a ^ A ≤ C * b / Real.log a ^ A := by gcongr
  have habs : |Chebyshev.theta b - Chebyshev.theta a - (b - a)| ≤
      |Chebyshev.theta b - b| + |Chebyshev.theta a - a| := by
    have := abs_sub (Chebyshev.theta b - b) (Chebyshev.theta a - a)
    calc _ = |(Chebyshev.theta b - b) - (Chebyshev.theta a - a)| := by ring_nf
      _ ≤ _ := this
  calc _ ≤ |Chebyshev.theta b - b| + |Chebyshev.theta a - a| := habs
    _ ≤ C * b / Real.log a ^ A + C * b / Real.log a ^ A := by linarith
    _ = 2 * C * b / Real.log a ^ A := by ring

/-- For `A ≥ B + 1` and `log R ≥ 1`: `R/(log R)^A ≤ (R/(log R)^B)/log R`. -/
theorem rpow_logPow_le {R B : ℝ} {A : ℕ} (hR : 0 ≤ R) (hL : 1 ≤ Real.log R)
    (hAB : B + 1 ≤ A) :
    R / Real.log R ^ A ≤ R / Real.log R ^ B / Real.log R := by
  have hL0 : 0 < Real.log R := by linarith
  rw [div_div, ← Real.rpow_natCast, ← Real.rpow_add_one hL0.ne']
  exact div_le_div_of_nonneg_left hR (by positivity)
    (Real.rpow_le_rpow_of_exponent_le hL (by exact_mod_cast hAB))

/-- **Window prime counts from above.**  Uniformly for `(u, v] ⊆ [R, 2R]` of length at least
`R/(log R)^B`: `#{p ∈ (u, v]} ≤ (1 + ε)(v - u)/log R`. -/
theorem exists_card_windowPrimes_le (B : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ R₀ : ℝ, 3 ≤ R₀ ∧ ∀ R : ℝ, R₀ ≤ R → ∀ u v : ℝ, R ≤ u → u ≤ v → v ≤ 2 * R →
      R / Real.log R ^ B ≤ v - u →
      ((windowPrimes u v).card : ℝ) ≤ (1 + ε) * (v - u) / Real.log R := by
  set A : ℕ := ⌈B⌉₊ + 1 with hA
  have hAB : B + 1 ≤ A := by
    have := Nat.le_ceil B
    rw [hA]; push_cast; linarith
  obtain ⟨C, hC, T, hT, hθ⟩ := exists_abs_theta_sub_le A
  have hev : ∀ᶠ R : ℝ in atTop, T ≤ R ∧ 1 ≤ Real.log R ∧ 4 * C / ε ≤ Real.log R :=
    (eventually_ge_atTop T).and
      ((Real.tendsto_log_atTop.eventually_ge_atTop 1).and
        (Real.tendsto_log_atTop.eventually_ge_atTop _))
  obtain ⟨X, hX⟩ := eventually_atTop.mp hev
  refine ⟨max X 3, le_max_right _ _, fun R hR u v hRu huv hv hgap => ?_⟩
  obtain ⟨hTR, hL1, hLC⟩ := hX R ((le_max_left _ _).trans hR)
  have hR0 : 0 < R := by linarith [le_max_right X 3]
  have hL0 : 0 < Real.log R := by linarith
  have hlogu : Real.log R ≤ Real.log u := Real.log_le_log hR0 hRu
  have hcard := card_windowPrimes_mul_log_le (show 1 ≤ u by linarith [le_max_right X 3]) huv
  have hinc := abs_theta_increment_le hC.le hT hθ (hTR.trans hRu) huv
  have hLA : Real.log R ^ A ≤ Real.log u ^ A := by gcongr
  have hLA0 : 0 < Real.log R ^ A := by positivity
  -- the error is at most `ε (v - u)`
  have herr : 2 * C * v / Real.log u ^ A ≤ ε * (v - u) := by
    have h1 : 2 * C * v / Real.log u ^ A ≤ 4 * C * (R / Real.log R ^ A) := by
      calc 2 * C * v / Real.log u ^ A ≤ 2 * C * v / Real.log R ^ A := by
            have : 0 ≤ 2 * C * v := by have : 0 ≤ v := by linarith
                                       positivity
            exact div_le_div_of_nonneg_left this hLA0 hLA
        _ ≤ 2 * C * (2 * R) / Real.log R ^ A := by gcongr
        _ = 4 * C * (R / Real.log R ^ A) := by ring
    have h2 : R / Real.log R ^ A ≤ R / Real.log R ^ B / Real.log R :=
      rpow_logPow_le hR0.le hL1 hAB
    have h3 : 4 * C * (R / Real.log R ^ B / Real.log R) ≤ ε * (R / Real.log R ^ B) := by
      rw [div_le_iff₀ hε] at hLC
      have hq : 0 ≤ R / Real.log R ^ B := by positivity
      rw [mul_div_assoc']
      rw [div_le_iff₀ hL0]
      nlinarith
    have h4 : ε * (R / Real.log R ^ B) ≤ ε * (v - u) := by gcongr
    have : 0 ≤ 4 * C := by positivity
    nlinarith [mul_le_mul_of_nonneg_left h2 this]
  have hθle : Chebyshev.theta v - Chebyshev.theta u ≤ (1 + ε) * (v - u) := by
    have := (abs_le.mp hinc).2
    linarith
  have hmain : ((windowPrimes u v).card : ℝ) * Real.log R ≤ (1 + ε) * (v - u) := by
    have : ((windowPrimes u v).card : ℝ) * Real.log R ≤
        ((windowPrimes u v).card : ℝ) * Real.log u := by gcongr
    linarith
  rw [le_div_iff₀ hL0]
  linarith

/-- **Window prime counts from below, at a divided scale.**  Uniformly for `(u, v] ⊆ [R, 2R]` of
length at least `R/(log R)^B` and `2 ≤ q ≤ 5`: `#{p ∈ (u/q, v/q]} ≥ (1 - ε)(v - u)/(q log R)`. -/
theorem exists_card_windowPrimes_div_ge (B : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ R₀ : ℝ, 3 ≤ R₀ ∧ ∀ R : ℝ, R₀ ≤ R → ∀ q : ℝ, 2 ≤ q → q ≤ 5 →
      ∀ u v : ℝ, R ≤ u → u ≤ v → v ≤ 2 * R → R / Real.log R ^ B ≤ v - u →
      (1 - ε) * (v - u) / (q * Real.log R) ≤ ((windowPrimes (u / q) (v / q)).card : ℝ) := by
  set A : ℕ := ⌈B⌉₊ + 1 with hA
  have hAB : B + 1 ≤ A := by
    have := Nat.le_ceil B
    rw [hA]; push_cast; linarith
  obtain ⟨C, hC, T, hT, hθ⟩ := exists_abs_theta_sub_le A
  have hev : ∀ᶠ R : ℝ in atTop, 5 * T ≤ R ∧ 1 ≤ Real.log R ∧ 2 * Real.log 5 ≤ Real.log R ∧
      4 * C * 2 ^ A / ε ≤ Real.log R :=
    (eventually_ge_atTop _).and ((Real.tendsto_log_atTop.eventually_ge_atTop 1).and
      ((Real.tendsto_log_atTop.eventually_ge_atTop _).and
        (Real.tendsto_log_atTop.eventually_ge_atTop _)))
  obtain ⟨X, hX⟩ := eventually_atTop.mp hev
  refine ⟨max X 3, le_max_right _ _, fun R hR q hq2 hq5 u v hRu huv hv hgap => ?_⟩
  obtain ⟨hTR, hL1, hL5, hLC⟩ := hX R ((le_max_left _ _).trans hR)
  have hR0 : 0 < R := by linarith [le_max_right X 3]
  have hL0 : 0 < Real.log R := by linarith
  have hq0 : 0 < q := by linarith
  have hab : u / q ≤ v / q := by gcongr
  have haT : T ≤ u / q := by
    rw [le_div_iff₀ hq0]
    nlinarith
  have hinc := abs_theta_increment_le hC.le hT hθ haT hab
  -- `log (u/q) ≥ log R / 2`
  have hloga : Real.log R / 2 ≤ Real.log (u / q) := by
    have h1 : R / 5 ≤ u / q := by
      rw [div_le_div_iff₀ (by norm_num) hq0]; nlinarith
    have h2 : Real.log (R / 5) ≤ Real.log (u / q) := Real.log_le_log (by positivity) h1
    rw [Real.log_div hR0.ne' (by norm_num)] at h2
    linarith
  -- `log (v/q) ≤ log R`
  have hlogb : Real.log (v / q) ≤ Real.log R := by
    apply Real.log_le_log (by have : 0 < v := by linarith
                              positivity)
    rw [div_le_iff₀ hq0]; nlinarith
  have hLA0 : 0 < (Real.log R / 2) ^ A := by positivity
  have hLA : (Real.log R / 2) ^ A ≤ Real.log (u / q) ^ A := by gcongr
  have herr : 2 * C * (v / q) / Real.log (u / q) ^ A ≤ ε * ((v - u) / q) := by
    have h1 : 2 * C * (v / q) / Real.log (u / q) ^ A ≤
        1 / q * (4 * C * 2 ^ A * (R / Real.log R ^ A)) := by
      calc 2 * C * (v / q) / Real.log (u / q) ^ A ≤ 2 * C * (v / q) / (Real.log R / 2) ^ A := by
            have : 0 ≤ 2 * C * (v / q) := by
              have : 0 ≤ v := by linarith
              positivity
            exact div_le_div_of_nonneg_left this hLA0 hLA
        _ ≤ 2 * C * (2 * R / q) / (Real.log R / 2) ^ A := by gcongr
        _ = 1 / q * (4 * C * 2 ^ A * (R / Real.log R ^ A)) := by
            rw [div_pow]; field_simp; ring
    have h2 : R / Real.log R ^ A ≤ R / Real.log R ^ B / Real.log R :=
      rpow_logPow_le hR0.le hL1 hAB
    have h3 : 4 * C * 2 ^ A * (R / Real.log R ^ B / Real.log R) ≤ ε * (R / Real.log R ^ B) := by
      rw [div_le_iff₀ hε] at hLC
      have hq : 0 ≤ R / Real.log R ^ B := by positivity
      rw [mul_div_assoc']
      rw [div_le_iff₀ hL0]
      nlinarith
    have h4 : ε * (R / Real.log R ^ B) ≤ ε * (v - u) := by gcongr
    have h5 : 4 * C * 2 ^ A * (R / Real.log R ^ A) ≤ ε * (v - u) := by
      have : 0 ≤ 4 * C * 2 ^ A := by positivity
      nlinarith [mul_le_mul_of_nonneg_left h2 this]
    calc 2 * C * (v / q) / Real.log (u / q) ^ A ≤ 1 / q * (4 * C * 2 ^ A * (R / Real.log R ^ A)) := h1
      _ ≤ 1 / q * (ε * (v - u)) := by gcongr
      _ = ε * ((v - u) / q) := by ring
  have hθge : (1 - ε) * ((v - u) / q) ≤ Chebyshev.theta (v / q) - Chebyshev.theta (u / q) := by
    have := (abs_le.mp hinc).1
    have e : v / q - u / q = (v - u) / q := by ring
    rw [e] at this
    linarith
  have hu0 : 0 ≤ u := by linarith
  have hcard := theta_sub_le_card_mul_log (show 0 ≤ u / q by positivity) hab
  have hc0 : (0 : ℝ) ≤ (windowPrimes (u / q) (v / q)).card := Nat.cast_nonneg _
  have hmain : (1 - ε) * ((v - u) / q) ≤ ((windowPrimes (u / q) (v / q)).card : ℝ) * Real.log R :=
    hθge.trans (hcard.trans (mul_le_mul_of_nonneg_left hlogb hc0))
  rw [div_le_iff₀ (by positivity)]
  calc (1 - ε) * (v - u) = (1 - ε) * ((v - u) / q) * q := by field_simp
    _ ≤ ((windowPrimes (u / q) (v / q)).card : ℝ) * Real.log R * q := by gcongr
    _ = _ := by ring

end RHTower.PrimeCells
