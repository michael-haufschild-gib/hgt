import GaloisForLFunctions.RHTower.ZetaFrobeniusSurplusSplit

/-!
# Height Averaging Localizes the Trans-Threshold Prime Pairs to the Coalescent Band

The rank–trace seam of the explicit-formula Gram matrix is linear in `tr G̃²` once the inertia
parameter is fixed, so it may be averaged over the window height `T` against a weight `ω` before
the prime side is evaluated. At fixed `L` (fixed profile `Φ` and prime cutoff `X`) the prime–prime
part of the averaged Frobenius norm is the sum over pairs of the averaged kernels
`∫ ω(T) A^±(T; log n, log m) dT`. These decay in the frequency `θ = log n ∓ log m`:

1. **Oscillatory decay** (`abs_intervalIntegral_mul_sin_le`): `k` integrations by parts give
   `|∫ ω(T) sin(κT + c) dT| ≤ ‖ω^{(k)}‖₁ / |κ|^k`.
2. **Averaged pair kernel** (`abs_avg_Agen_le`): at every offset `x` the inner integral of `A^±` is
   `(sin(2θT + c₁) − sin(θT + c₂))/θ` (`Jgen_eq_of_ne`); splitting the offsets at `|x| = a`,
   `|∫ ω A^±| ≤ 2‖ω^{(k)}‖₁ (∫Φ²)/|θ|^{k+1} + b ‖ω‖₁ (∫Φ²x²)/a²` for `ω` supported in `[a, b]`.
3. **Sum frequencies and far pairs** (`abs_avg_ppSumFreq_le`, `abs_avg_ppOffDiag_sub_close_le`):
   the averaged sum frequencies, and the averaged off-diagonal pairs with `|log(n/m)| > θ₀`, are
   at most `(Σ_{n≤X} a_n)²` times the kernel bound at `θ = 1`, resp. `θ = θ₀`.

For `ω` of width `V = εT` the `k`-th derivative costs `V^{-k}`. At bandwidth `λ`, with
`(Σ a_n)² ≤ 9X`, the far pairs `|log(n/m)| > T^{-1+η}` and all sum frequencies cost
`O(XL·T^{1-η(k+1)}) + O(X/T)`, which is `o((aL)²Tℓ₁)` once `η(k+1) > λ` and `λ < 2`. The sharp
window charges each of them `O(X log X)`. After height averaging, only the coalescent band carries
trans-threshold mass.
-/

open MeasureTheory Real Set Finset Filter intervalIntegral
open scoped BigOperators ArithmeticFunction
open Zeta23 Zeta23.PrimeSide RHTower

noncomputable section

namespace GaloisForLFunctions.TransThresholdPairCorrelation

/-! ## 1. Oscillatory decay of a smooth height weight -/

section Decay

variable {a b : ℝ}

/-- A function vanishing off `[a, b]` has derivative vanishing off `[a, b]`. -/
theorem deriv_eq_zero_of_not_mem_Icc {ω : ℝ → ℝ} (hz : ∀ T ∉ Icc a b, ω T = 0) {T : ℝ}
    (hT : T ∉ Icc a b) : deriv ω T = 0 := by
  have hev : ω =ᶠ[nhds T] fun _ => (0 : ℝ) := by
    filter_upwards [isClosed_Icc.isOpen_compl.mem_nhds hT] with s hs using hz s hs
  rw [hev.deriv_eq, deriv_const]

/-- **`k`-fold integration by parts.** For a `C^k` weight `ω` vanishing off `[a, b]` and `κ ≠ 0`,
`|∫ ω(T) sin(κT + c) dT| ≤ ‖ω^{(k)}‖₁ / |κ|^k`, integrals over `[a − 1, b + 1] ⊇ supp ω`. -/
theorem abs_intervalIntegral_mul_sin_le (hab : a ≤ b) (k : ℕ) :
    ∀ {ω : ℝ → ℝ}, ContDiff ℝ k ω → (∀ T ∉ Icc a b, ω T = 0) → ∀ {κ : ℝ}, κ ≠ 0 → ∀ c : ℝ,
      |∫ T in (a - 1)..(b + 1), ω T * Real.sin (κ * T + c)|
        ≤ (∫ T in (a - 1)..(b + 1), |iteratedDeriv k ω T|) / |κ| ^ k := by
  have hle : a - 1 ≤ b + 1 := by linarith
  induction k with
  | zero =>
    intro ω hω _ κ _ c
    simp only [iteratedDeriv_zero, pow_zero, div_one]
    refine (abs_integral_le_integral_abs hle).trans
      (integral_mono_on hle ?_ ?_ fun T _ => ?_)
    · exact ((hω.continuous.mul (by fun_prop)).abs).intervalIntegrable _ _
    · exact hω.continuous.abs.intervalIntegrable _ _
    · rw [abs_mul]
      exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_sin_le_one _)
  | succ k ih =>
    intro ω hω hz κ hκ c
    obtain ⟨hdiff, -, hω'⟩ := contDiff_succ_iff_deriv.mp (by exact_mod_cast hω :
      ContDiff ℝ ((k : WithTop ℕ∞) + 1) ω)
    have hz' : ∀ T ∉ Icc a b, deriv ω T = 0 := fun T hT => deriv_eq_zero_of_not_mem_Icc hz hT
    have hv : ∀ x ∈ uIcc (a - 1) (b + 1),
        HasDerivAt (fun T => -Real.cos (κ * T + c) / κ) (Real.sin (κ * x + c)) x := by
      intro x _
      have h1 : HasDerivAt (fun T => κ * T + c) κ x := by
        simpa using ((hasDerivAt_id x).const_mul κ).add_const c
      have h2 : HasDerivAt (fun T => -Real.cos (κ * T + c) / κ)
          (-(-Real.sin (κ * x + c) * κ) / κ) x :=
        (h1.cos.neg).div_const κ
      rwa [neg_mul, neg_neg, mul_div_cancel_right₀ _ hκ] at h2
    have hibp := integral_mul_deriv_eq_deriv_mul (fun x _ => (hdiff x).hasDerivAt) hv
      (hω'.continuous.intervalIntegrable _ _)
      ((by fun_prop : Continuous fun T => Real.sin (κ * T + c)).intervalIntegrable _ _)
    have ha1 : ω (a - 1) = 0 := hz _ fun h => by linarith [h.1]
    have hb1 : ω (b + 1) = 0 := hz _ fun h => by linarith [h.2]
    have hcos : ∀ T, deriv ω T * (-Real.cos (κ * T + c) / κ)
        = -(κ⁻¹ * (deriv ω T * Real.sin (κ * T + (c + π / 2)))) := by
      intro T
      rw [show κ * T + (c + π / 2) = (κ * T + c) + π / 2 by ring, Real.sin_add_pi_div_two]
      ring
    simp only [ha1, hb1, zero_mul, sub_zero, zero_sub, hcos, intervalIntegral.integral_neg,
      neg_neg, intervalIntegral.integral_const_mul] at hibp
    rw [hibp, abs_mul, abs_inv, iteratedDeriv_succ', pow_succ]
    have := ih hω' hz' hκ (c + π / 2)
    have hκ0 : 0 < |κ| := abs_pos.mpr hκ
    calc |κ|⁻¹ * |∫ T in (a - 1)..(b + 1), deriv ω T * Real.sin (κ * T + (c + π / 2))|
        ≤ |κ|⁻¹ * ((∫ T in (a - 1)..(b + 1), |iteratedDeriv k (deriv ω) T|) / |κ| ^ k) :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = _ := by field_simp

end Decay

/-! ## 2. The averaged pair kernels `A^±` -/

section Kernel

variable {Φ : ℝ → ℝ}

/-- The inner integral of `A^±` at offset `x`: `∫ cos(θτ' + xy) dτ'` over `[T,2T] ∩ ([T,2T] − x)`. -/
def Jgen (T θ y x : ℝ) : ℝ := Jker θ (x * y) (max (T - x) T) (min (2 * T - x) (2 * T))

/-- `A^±(y, y')` written with its frequency `θ = y ∓ y'`. -/
def Agen (Φ : ℝ → ℝ) (T θ y : ℝ) : ℝ := ∫ x in Icc (-T) T, Φ x ^ 2 * Jgen T θ y x

theorem Aminus_eq_Agen (T y y' : ℝ) : Aminus Φ T y y' = Agen Φ T (y - y') y := rfl

theorem Aplus_eq_Agen (T y y' : ℝ) : Aplus Φ T y y' = Agen Φ T (y + y') y := rfl

/-- For `θ ≠ 0` the inner integral is a difference of two phases in the height `T`. -/
theorem Jgen_eq_of_ne {θ : ℝ} (hθ : θ ≠ 0) (T y x : ℝ) :
    Jgen T θ y x = (Real.sin (2 * θ * T + (x * y - θ * max x 0))
      - Real.sin (θ * T + (x * y - θ * min x 0))) / θ := by
  unfold Jgen
  rw [Jker_of_ne hθ]
  have h1 : min (2 * T - x) (2 * T) = 2 * T - max x 0 := by rw [← min_sub_sub_left]; simp
  have h2 : max (T - x) T = T - min x 0 := by rw [← max_sub_sub_left]; simp
  have e1 : θ * (2 * T - max x 0) + x * y = 2 * θ * T + (x * y - θ * max x 0) := by ring
  have e2 : θ * (T - min x 0) + x * y = θ * T + (x * y - θ * min x 0) := by ring
  rw [h1, h2, e1, e2]

theorem continuous_Jgen_uncurry (θ y : ℝ) : Continuous fun p : ℝ × ℝ => Jgen p.1 θ y p.2 := by
  unfold Jgen Jker
  by_cases hθ : θ = 0
  · simp only [hθ, if_true]; fun_prop
  · simp only [hθ, if_false]; fun_prop

theorem continuous_Jgen_swap (θ y : ℝ) : Continuous fun p : ℝ × ℝ => Jgen p.2 θ y p.1 := by
  unfold Jgen Jker
  by_cases hθ : θ = 0
  · simp only [hθ, if_true]; fun_prop
  · simp only [hθ, if_false]; fun_prop

/-- `|J(T; θ, y, x)| ≤ T` on `|x| ≤ T`: the inner window has length `T − |x|`. -/
theorem abs_Jgen_le {T : ℝ} (hT : 0 ≤ T) {x : ℝ} (hx : |x| ≤ T) (θ y : ℝ) :
    |Jgen T θ y x| ≤ T := by
  unfold Jgen
  rw [← intervalIntegral_cos_linear_eq_Jker]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := max (T - x) T)
    (b := min (2 * T - x) (2 * T)) (C := 1) (f := fun t => Real.cos (θ * t + x * y))
    (fun t _ => by simpa using Real.abs_cos_le_one (θ * t + x * y))
  rw [Real.norm_eq_abs, one_mul, abs_of_nonneg (sub_nonneg.mpr (Ix_le hT hx)), Ix_length] at h
  linarith [abs_nonneg x]

/-- `A^±` as an interval integral (for `T ≥ 0`). -/
theorem Agen_eq_intervalIntegral {T : ℝ} (hT : 0 ≤ T) (θ y : ℝ) :
    Agen Φ T θ y = ∫ x in (-T)..T, Φ x ^ 2 * Jgen T θ y x := by
  unfold Agen
  rw [intervalIntegral.integral_of_le (by linarith), integral_Icc_eq_integral_Ioc]

theorem continuous_intervalAgen (hΦ : Continuous Φ) (θ y : ℝ) :
    Continuous fun T => ∫ x in (-T)..T, Φ x ^ 2 * Jgen T θ y x := by
  have hf : Continuous (Function.uncurry fun T x => Φ x ^ 2 * Jgen T θ y x) :=
    ((hΦ.comp continuous_snd).pow 2).mul (continuous_Jgen_uncurry θ y)
  have hfT : ∀ T : ℝ, Continuous fun x => Φ x ^ 2 * Jgen T θ y x := fun T =>
    hf.comp (Continuous.prodMk_right T)
  have h : (fun T => ∫ x in (-T)..T, Φ x ^ 2 * Jgen T θ y x)
      = fun T => (∫ x in (0 : ℝ)..T, Φ x ^ 2 * Jgen T θ y x)
          - ∫ x in (0 : ℝ)..(-T), Φ x ^ 2 * Jgen T θ y x := by
    funext T
    rw [intervalIntegral.integral_interval_sub_left ((hfT T).intervalIntegrable _ _)
      ((hfT T).intervalIntegrable _ _)]
  rw [h]
  exact (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous hf continuous_id).sub
    (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous hf continuous_neg)

variable {ω : ℝ → ℝ} {a b : ℝ} {k : ℕ}

/-- `A^±` as the continuous interval integral `∫_{−T}^{T}` (equal to `Agen` for `T ≥ 0`). -/
def intAgen (Φ : ℝ → ℝ) (T θ y : ℝ) : ℝ := ∫ x in (-T)..T, Φ x ^ 2 * Jgen T θ y x

/-- The core offsets `|x| ≤ a` of `A^±`. -/
def coreAgen (Φ : ℝ → ℝ) (a T θ y : ℝ) : ℝ := ∫ x in (-a)..a, Φ x ^ 2 * Jgen T θ y x

theorem continuous_Phi_Jgen_uncurry (hΦ : Continuous Φ) (θ y : ℝ) :
    Continuous (Function.uncurry fun T x => Φ x ^ 2 * Jgen T θ y x) :=
  ((hΦ.comp continuous_snd).pow 2).mul (continuous_Jgen_uncurry θ y)

theorem continuous_coreAgen (hΦ : Continuous Φ) (a θ y : ℝ) :
    Continuous fun T => coreAgen Φ a T θ y :=
  intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (continuous_Phi_Jgen_uncurry hΦ θ y) (-a) a

theorem continuous_intAgen' (hΦ : Continuous Φ) (θ y : ℝ) :
    Continuous fun T => intAgen Φ T θ y :=
  continuous_intervalAgen hΦ θ y

/-- On the averaging interval `[a − 1, b + 1] ⊆ [0, ∞)` the two forms of `A^±` agree. -/
theorem Agen_eq_intAgen_of_mem (ha : 1 ≤ a) (hab : a ≤ b) {T : ℝ}
    (hT : T ∈ uIoc (a - 1) (b + 1)) (θ y : ℝ) : Agen Φ T θ y = intAgen Φ T θ y := by
  rw [uIoc_of_le (by linarith)] at hT
  exact Agen_eq_intervalIntegral (by linarith [hT.1]) θ y

theorem avg_Agen_eq (ha : 1 ≤ a) (hab : a ≤ b) (θ y : ℝ) :
    ∫ T in (a - 1)..(b + 1), ω T * Agen Φ T θ y
      = ∫ T in (a - 1)..(b + 1), ω T * intAgen Φ T θ y :=
  intervalIntegral.integral_congr_ae (Eventually.of_forall fun T hT => by
    rw [Agen_eq_intAgen_of_mem ha hab hT])

theorem intervalIntegrable_mul_Agen (hΦ : Continuous Φ) (hω : Continuous ω) (ha : 1 ≤ a)
    (hab : a ≤ b) (θ y : ℝ) :
    IntervalIntegrable (fun T => ω T * Agen Φ T θ y) volume (a - 1) (b + 1) := by
  have hc : Continuous fun T => ω T * intAgen Φ T θ y := hω.mul (continuous_intAgen' hΦ θ y)
  refine (hc.intervalIntegrable _ _).congr fun T hT => ?_
  show ω T * intAgen Φ T θ y = ω T * Agen Φ T θ y
  rw [Agen_eq_intAgen_of_mem ha hab hT]

/-- The averaged inner kernel at a fixed offset: `|∫ ω(T) J(T; θ, y, x) dT| ≤ 2‖ω^{(k)}‖₁/|θ|^{k+1}`. -/
theorem abs_avg_Jgen_le (hω : ContDiff ℝ k ω) (hz : ∀ T ∉ Icc a b, ω T = 0) (hab : a ≤ b)
    {θ : ℝ} (hθ : θ ≠ 0) (y x : ℝ) :
    |∫ T in (a - 1)..(b + 1), ω T * Jgen T θ y x|
      ≤ 2 * (∫ T in (a - 1)..(b + 1), |iteratedDeriv k ω T|) / |θ| ^ (k + 1) := by
  have hθ0 : 0 < |θ| := abs_pos.mpr hθ
  have h2θ : (2 * θ) ≠ 0 := mul_ne_zero two_ne_zero hθ
  have hs₁ := abs_intervalIntegral_mul_sin_le hab k hω hz h2θ (x * y - θ * max x 0)
  have hs₂ := abs_intervalIntegral_mul_sin_le hab k hω hz hθ (x * y - θ * min x 0)
  have hI0 : 0 ≤ ∫ T in (a - 1)..(b + 1), |iteratedDeriv k ω T| :=
    intervalIntegral.integral_nonneg (by linarith) fun _ _ => abs_nonneg _
  have hc : Continuous ω := hω.continuous
  have hi1 : IntervalIntegrable (fun T => ω T * Real.sin (2 * θ * T + (x * y - θ * max x 0)))
      volume (a - 1) (b + 1) := (hc.mul (by fun_prop)).intervalIntegrable _ _
  have hi2 : IntervalIntegrable (fun T => ω T * Real.sin (θ * T + (x * y - θ * min x 0)))
      volume (a - 1) (b + 1) := (hc.mul (by fun_prop)).intervalIntegrable _ _
  have hsplit : ∫ T in (a - 1)..(b + 1), ω T * Jgen T θ y x
      = θ⁻¹ * ((∫ T in (a - 1)..(b + 1), ω T * Real.sin (2 * θ * T + (x * y - θ * max x 0)))
          - ∫ T in (a - 1)..(b + 1), ω T * Real.sin (θ * T + (x * y - θ * min x 0))) := by
    rw [← intervalIntegral.integral_sub hi1 hi2, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun T _ => ?_
    simp only [Jgen_eq_of_ne hθ]
    ring
  rw [hsplit, abs_mul, abs_inv]
  have h2 : |θ| ^ k ≤ |2 * θ| ^ k := by
    rw [abs_mul, abs_two]
    exact pow_le_pow_left₀ (abs_nonneg _) (by linarith) k
  have hb₁ : (∫ T in (a - 1)..(b + 1), |iteratedDeriv k ω T|) / |2 * θ| ^ k
      ≤ (∫ T in (a - 1)..(b + 1), |iteratedDeriv k ω T|) / |θ| ^ k :=
    div_le_div_of_nonneg_left hI0 (by positivity) h2
  calc |θ|⁻¹ * |(∫ T in (a - 1)..(b + 1), ω T * Real.sin (2 * θ * T + (x * y - θ * max x 0)))
        - ∫ T in (a - 1)..(b + 1), ω T * Real.sin (θ * T + (x * y - θ * min x 0))|
      ≤ |θ|⁻¹ * ((∫ T in (a - 1)..(b + 1), |iteratedDeriv k ω T|) / |θ| ^ k
          + (∫ T in (a - 1)..(b + 1), |iteratedDeriv k ω T|) / |θ| ^ k) := by
        refine mul_le_mul_of_nonneg_left ((abs_sub _ _).trans ?_) (by positivity)
        exact add_le_add (hs₁.trans hb₁) hs₂
    _ = 2 * (∫ T in (a - 1)..(b + 1), |iteratedDeriv k ω T|) / |θ| ^ (k + 1) := by
        rw [pow_succ]; field_simp; ring

/-- Splitting `[−T, T]` at `±a`. -/
theorem intAgen_sub_coreAgen (hΦ : Continuous Φ) (a T θ y : ℝ) :
    intAgen Φ T θ y - coreAgen Φ a T θ y
      = (∫ x in (-T)..(-a), Φ x ^ 2 * Jgen T θ y x) + ∫ x in a..T, Φ x ^ 2 * Jgen T θ y x := by
  have hfT : Continuous fun x => Φ x ^ 2 * Jgen T θ y x :=
    (continuous_Phi_Jgen_uncurry hΦ θ y).comp (Continuous.prodMk_right T)
  have h1 := intervalIntegral.integral_add_adjacent_intervals (μ := volume) (a := -T) (b := -a)
    (c := T) (hfT.intervalIntegrable (-T) (-a)) (hfT.intervalIntegrable (-a) T)
  have h2 := intervalIntegral.integral_add_adjacent_intervals (μ := volume) (a := -a) (b := a)
    (c := T) (hfT.intervalIntegrable (-a) a) (hfT.intervalIntegrable a T)
  unfold intAgen coreAgen
  linarith

/-- `|Φ²J| ≤ (b/a²) Φ²x²` on `a ≤ |x| ≤ T ≤ b`. -/
theorem abs_Phi_Jgen_le_of_le {T : ℝ} (hT0 : 0 ≤ T) (hTb : T ≤ b) (ha : 0 < a) {x : ℝ}
    (hax : a ≤ |x|) (hxT : |x| ≤ T) (θ y : ℝ) :
    |Φ x ^ 2 * Jgen T θ y x| ≤ b / a ^ 2 * (Φ x ^ 2 * x ^ 2) := by
  rw [abs_mul, abs_of_nonneg (sq_nonneg _)]
  have hJ := abs_Jgen_le hT0 hxT θ y
  have hx2 : a ^ 2 ≤ x ^ 2 := by rw [← sq_abs x]; exact pow_le_pow_left₀ ha.le hax 2
  have hΦ0 : 0 ≤ Φ x ^ 2 := sq_nonneg _
  have ha2 : 0 < a ^ 2 := by positivity
  have hb0 : 0 ≤ b := hT0.trans hTb
  calc Φ x ^ 2 * |Jgen T θ y x| ≤ Φ x ^ 2 * b := mul_le_mul_of_nonneg_left (hJ.trans hTb) hΦ0
    _ = b / a ^ 2 * (Φ x ^ 2 * a ^ 2) := by field_simp
    _ ≤ b / a ^ 2 * (Φ x ^ 2 * x ^ 2) := by gcongr

theorem abs_integral_Phi_Jgen_right_le (hΦ : Continuous Φ)
    (hΦsq : Integrable fun x => Φ x ^ 2 * x ^ 2) (ha : 0 < a) {T : ℝ} (hT : T ∈ Icc a b)
    (θ y : ℝ) :
    |∫ x in a..T, Φ x ^ 2 * Jgen T θ y x| ≤ b / a ^ 2 * ∫ x in Ioi a, Φ x ^ 2 * x ^ 2 := by
  have hfT : Continuous fun x => Φ x ^ 2 * Jgen T θ y x :=
    (continuous_Phi_Jgen_uncurry hΦ θ y).comp (Continuous.prodMk_right T)
  have haT : a ≤ T := hT.1
  have hb0 : 0 ≤ b := by linarith [hT.1, hT.2]
  calc |∫ x in a..T, Φ x ^ 2 * Jgen T θ y x|
      ≤ ∫ x in a..T, |Φ x ^ 2 * Jgen T θ y x| := abs_integral_le_integral_abs haT
    _ = ∫ x in Ioc a T, |Φ x ^ 2 * Jgen T θ y x| := intervalIntegral.integral_of_le haT
    _ ≤ ∫ x in Ioc a T, b / a ^ 2 * (Φ x ^ 2 * x ^ 2) := by
        refine setIntegral_mono_on ((hfT.abs.integrableOn_Icc).mono_set Ioc_subset_Icc_self)
          (hΦsq.integrableOn.const_mul _) measurableSet_Ioc fun x hx => ?_
        have hx0 : 0 < x := by linarith [hx.1]
        exact abs_Phi_Jgen_le_of_le (by linarith) hT.2 ha (by rw [abs_of_pos hx0]; exact hx.1.le)
          (by rw [abs_of_pos hx0]; exact hx.2) θ y
    _ = b / a ^ 2 * ∫ x in Ioc a T, Φ x ^ 2 * x ^ 2 := integral_const_mul _ _
    _ ≤ b / a ^ 2 * ∫ x in Ioi a, Φ x ^ 2 * x ^ 2 := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact setIntegral_mono_set hΦsq.integrableOn
          (Eventually.of_forall fun x => by simp only [Pi.zero_apply]; positivity)
          Ioc_subset_Ioi_self.eventuallyLE

theorem abs_integral_Phi_Jgen_left_le (hΦ : Continuous Φ)
    (hΦsq : Integrable fun x => Φ x ^ 2 * x ^ 2) (ha : 0 < a) {T : ℝ} (hT : T ∈ Icc a b)
    (θ y : ℝ) :
    |∫ x in (-T)..(-a), Φ x ^ 2 * Jgen T θ y x| ≤ b / a ^ 2 * ∫ x in Iic (-a), Φ x ^ 2 * x ^ 2 := by
  have hfT : Continuous fun x => Φ x ^ 2 * Jgen T θ y x :=
    (continuous_Phi_Jgen_uncurry hΦ θ y).comp (Continuous.prodMk_right T)
  have haT : -T ≤ -a := by linarith [hT.1]
  have hb0 : 0 ≤ b := by linarith [hT.1, hT.2]
  calc |∫ x in (-T)..(-a), Φ x ^ 2 * Jgen T θ y x|
      ≤ ∫ x in (-T)..(-a), |Φ x ^ 2 * Jgen T θ y x| := abs_integral_le_integral_abs haT
    _ = ∫ x in Ioc (-T) (-a), |Φ x ^ 2 * Jgen T θ y x| := intervalIntegral.integral_of_le haT
    _ ≤ ∫ x in Ioc (-T) (-a), b / a ^ 2 * (Φ x ^ 2 * x ^ 2) := by
        refine setIntegral_mono_on ((hfT.abs.integrableOn_Icc).mono_set Ioc_subset_Icc_self)
          (hΦsq.integrableOn.const_mul _) measurableSet_Ioc fun x hx => ?_
        have hx0 : x < 0 := by linarith [hx.2]
        exact abs_Phi_Jgen_le_of_le (by linarith [hT.1]) hT.2 ha
          (by rw [abs_of_neg hx0]; linarith [hx.2]) (by rw [abs_of_neg hx0]; linarith [hx.1]) θ y
    _ = b / a ^ 2 * ∫ x in Ioc (-T) (-a), Φ x ^ 2 * x ^ 2 := integral_const_mul _ _
    _ ≤ b / a ^ 2 * ∫ x in Iic (-a), Φ x ^ 2 * x ^ 2 := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact setIntegral_mono_set hΦsq.integrableOn
          (Eventually.of_forall fun x => by simp only [Pi.zero_apply]; positivity)
          Ioc_subset_Iic_self.eventuallyLE

/-- On `T ∈ [a, b]` the offsets `|x| > a` contribute at most `b (∫Φ²x²)/a²` to `A^±(T)`. -/
theorem abs_intAgen_sub_coreAgen_le (hΦ : Continuous Φ)
    (hΦsq : Integrable fun x => Φ x ^ 2 * x ^ 2) (ha : 0 < a) {T : ℝ} (hT : T ∈ Icc a b)
    (θ y : ℝ) :
    |intAgen Φ T θ y - coreAgen Φ a T θ y| ≤ b * (∫ x, Φ x ^ 2 * x ^ 2) / a ^ 2 := by
  have hb0 : 0 ≤ b := by linarith [hT.1, hT.2]
  have hunion : (∫ x in Iic (-a), Φ x ^ 2 * x ^ 2) + ∫ x in Ioi a, Φ x ^ 2 * x ^ 2
      ≤ ∫ x, Φ x ^ 2 * x ^ 2 := by
    have hdisj : Disjoint (Iic (-a)) (Ioi a) := Set.disjoint_left.mpr fun x h1 h2 => by
      simp only [Set.mem_Iic] at h1; simp only [Set.mem_Ioi] at h2; linarith
    rw [← setIntegral_union hdisj measurableSet_Ioi hΦsq.integrableOn hΦsq.integrableOn]
    exact setIntegral_le_integral hΦsq (Eventually.of_forall fun x => by
      simp only [Pi.zero_apply]; positivity)
  rw [intAgen_sub_coreAgen hΦ]
  calc |(∫ x in (-T)..(-a), Φ x ^ 2 * Jgen T θ y x) + ∫ x in a..T, Φ x ^ 2 * Jgen T θ y x|
      ≤ b / a ^ 2 * (∫ x in Iic (-a), Φ x ^ 2 * x ^ 2)
          + b / a ^ 2 * ∫ x in Ioi a, Φ x ^ 2 * x ^ 2 :=
        (abs_add_le _ _).trans (add_le_add (abs_integral_Phi_Jgen_left_le hΦ hΦsq ha hT θ y)
          (abs_integral_Phi_Jgen_right_le hΦ hΦsq ha hT θ y))
    _ ≤ b / a ^ 2 * ∫ x, Φ x ^ 2 * x ^ 2 := by
        rw [← mul_add]; exact mul_le_mul_of_nonneg_left hunion (by positivity)
    _ = b * (∫ x, Φ x ^ 2 * x ^ 2) / a ^ 2 := by ring

/-- Fubini on the core box: the height average passes inside the offset integral. -/
theorem avg_coreAgen_eq (hΦ : Continuous Φ) (hω : Continuous ω) (θ y : ℝ) :
    ∫ T in (a - 1)..(b + 1), ω T * coreAgen Φ a T θ y
      = ∫ x in (-a)..a, Φ x ^ 2 * ∫ T in (a - 1)..(b + 1), ω T * Jgen T θ y x := by
  have hF : Continuous (Function.uncurry fun T x => ω T * (Φ x ^ 2 * Jgen T θ y x)) :=
    (hω.comp continuous_fst).mul (continuous_Phi_Jgen_uncurry hΦ θ y)
  have hint : IntegrableOn (Function.uncurry fun T x => ω T * (Φ x ^ 2 * Jgen T θ y x))
      (uIoc (a - 1) (b + 1) ×ˢ uIoc (-a) a) :=
    (hF.continuousOn.integrableOn_compact (isCompact_uIcc.prod isCompact_uIcc)).mono_set
      (Set.prod_mono uIoc_subset_uIcc uIoc_subset_uIcc)
  have h1 : ∫ T in (a - 1)..(b + 1), ω T * coreAgen Φ a T θ y
      = ∫ T in (a - 1)..(b + 1), ∫ x in (-a)..a, ω T * (Φ x ^ 2 * Jgen T θ y x) :=
    intervalIntegral.integral_congr fun T _ => by
      show ω T * coreAgen Φ a T θ y = _
      rw [coreAgen, ← intervalIntegral.integral_const_mul]
  rw [h1, intervalIntegral_intervalIntegral_swap hint]
  refine intervalIntegral.integral_congr fun x _ => ?_
  show (∫ T in (a - 1)..(b + 1), ω T * (Φ x ^ 2 * Jgen T θ y x))
    = Φ x ^ 2 * ∫ T in (a - 1)..(b + 1), ω T * Jgen T θ y x
  rw [← intervalIntegral.integral_const_mul]
  exact intervalIntegral.integral_congr fun T _ => by ring

/-- **Averaged pair kernel.** For a `C^k` weight `ω` vanishing off `[a, b]`, `1 ≤ a ≤ b`, and a
frequency `θ ≠ 0`:
`|∫ ω(T) A^±(T) dT| ≤ 2‖ω^{(k)}‖₁ (∫Φ²)/|θ|^{k+1} + b ‖ω‖₁ (∫Φ²x²)/a²`. -/
theorem abs_avg_Agen_le (hΦ : Continuous Φ) (hΦ2 : Integrable fun x => Φ x ^ 2)
    (hΦsq : Integrable fun x => Φ x ^ 2 * x ^ 2) (hω : ContDiff ℝ k ω)
    (hz : ∀ T ∉ Icc a b, ω T = 0) (ha : 1 ≤ a) (hab : a ≤ b) {θ : ℝ} (hθ : θ ≠ 0) (y : ℝ) :
    |∫ T in (a - 1)..(b + 1), ω T * Agen Φ T θ y|
      ≤ 2 * (∫ T in (a - 1)..(b + 1), |iteratedDeriv k ω T|) / |θ| ^ (k + 1) * (∫ x, Φ x ^ 2)
        + b * (∫ T in (a - 1)..(b + 1), |ω T|) * (∫ x, Φ x ^ 2 * x ^ 2) / a ^ 2 := by
  have hc : Continuous ω := hω.continuous
  have hle : a - 1 ≤ b + 1 := by linarith
  have hB := continuous_intAgen' hΦ θ y
  have hM := continuous_coreAgen hΦ a θ y
  rw [avg_Agen_eq ha hab]
  have hsplit : ∫ T in (a - 1)..(b + 1), ω T * intAgen Φ T θ y
      = (∫ T in (a - 1)..(b + 1), ω T * coreAgen Φ a T θ y)
        + ∫ T in (a - 1)..(b + 1), ω T * (intAgen Φ T θ y - coreAgen Φ a T θ y) := by
    rw [← intervalIntegral.integral_add (f := fun T => ω T * coreAgen Φ a T θ y)
      (g := fun T => ω T * (intAgen Φ T θ y - coreAgen Φ a T θ y))
      ((hc.mul hM).intervalIntegrable _ _) ((hc.mul (hB.sub hM)).intervalIntegrable _ _)]
    exact intervalIntegral.integral_congr fun T _ => by ring
  rw [hsplit]
  set K : ℝ := 2 * (∫ T in (a - 1)..(b + 1), |iteratedDeriv k ω T|) / |θ| ^ (k + 1) with hKdef
  have hK0 : 0 ≤ K := by
    have : 0 ≤ ∫ T in (a - 1)..(b + 1), |iteratedDeriv k ω T| :=
      intervalIntegral.integral_nonneg hle fun _ _ => abs_nonneg _
    rw [hKdef]; positivity
  -- the core offsets `|x| ≤ a`: Fubini, then oscillatory decay at each offset
  have hcore : |∫ T in (a - 1)..(b + 1), ω T * coreAgen Φ a T θ y| ≤ K * ∫ x, Φ x ^ 2 := by
    rw [avg_coreAgen_eq hΦ hc]
    have hinner : Continuous fun x => Φ x ^ 2 * ∫ T in (a - 1)..(b + 1), ω T * Jgen T θ y x := by
      have hF' : Continuous fun p : ℝ × ℝ => ω p.2 * Jgen p.2 θ y p.1 :=
        (hc.comp continuous_snd).mul (continuous_Jgen_swap θ y)
      exact (hΦ.pow 2).mul
        (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (μ := volume)
          (f := fun x T => ω T * Jgen T θ y x) hF' (a - 1) (b + 1))
    have haa : -a ≤ a := by linarith
    calc |∫ x in (-a)..a, Φ x ^ 2 * ∫ T in (a - 1)..(b + 1), ω T * Jgen T θ y x|
        ≤ ∫ x in (-a)..a, Φ x ^ 2 * K := by
          refine (abs_integral_le_integral_abs haa).trans
            (integral_mono_on haa (hinner.abs.intervalIntegrable _ _)
              (((hΦ.pow 2).mul continuous_const).intervalIntegrable _ _) fun x _ => ?_)
          rw [abs_mul, abs_of_nonneg (sq_nonneg _)]
          exact mul_le_mul_of_nonneg_left (abs_avg_Jgen_le hω hz hab hθ y x) (sq_nonneg _)
      _ = K * ∫ x in (-a)..a, Φ x ^ 2 := by rw [intervalIntegral.integral_mul_const]; ring
      _ ≤ K * ∫ x, Φ x ^ 2 := by
          refine mul_le_mul_of_nonneg_left ?_ hK0
          rw [intervalIntegral.integral_of_le haa]
          exact setIntegral_le_integral hΦ2 (Eventually.of_forall fun x => by
            simp only [Pi.zero_apply]; positivity)
  -- the far offsets `|x| > a`
  have htail : |∫ T in (a - 1)..(b + 1), ω T * (intAgen Φ T θ y - coreAgen Φ a T θ y)|
      ≤ b * (∫ T in (a - 1)..(b + 1), |ω T|) * (∫ x, Φ x ^ 2 * x ^ 2) / a ^ 2 := by
    have hpt : ∀ T, |ω T * (intAgen Φ T θ y - coreAgen Φ a T θ y)|
        ≤ |ω T| * (b * (∫ x, Φ x ^ 2 * x ^ 2) / a ^ 2) := by
      intro T
      rw [abs_mul]
      by_cases hT : T ∈ Icc a b
      · exact mul_le_mul_of_nonneg_left
          (abs_intAgen_sub_coreAgen_le hΦ hΦsq (by linarith) hT θ y) (abs_nonneg _)
      · rw [hz T hT, abs_zero, zero_mul, zero_mul]
    calc |∫ T in (a - 1)..(b + 1), ω T * (intAgen Φ T θ y - coreAgen Φ a T θ y)|
        ≤ ∫ T in (a - 1)..(b + 1), |ω T| * (b * (∫ x, Φ x ^ 2 * x ^ 2) / a ^ 2) :=
          (abs_integral_le_integral_abs hle).trans
            (integral_mono_on hle ((hc.mul (hB.sub hM)).abs.intervalIntegrable _ _)
              ((hc.abs.mul continuous_const).intervalIntegrable _ _) fun T _ => hpt T)
      _ = b * (∫ T in (a - 1)..(b + 1), |ω T|) * (∫ x, Φ x ^ 2 * x ^ 2) / a ^ 2 := by
          rw [intervalIntegral.integral_mul_const]; ring
  exact (abs_add_le _ _).trans (add_le_add hcore htail)

end Kernel

/-! ## 3. Sum frequencies and far pairs after height averaging -/

section Pairs

variable {Φ : ℝ → ℝ} {ω : ℝ → ℝ} {a b : ℝ} {k : ℕ}

/-- The kernel bound `2‖ω^{(k)}‖₁(∫Φ²)/θ^{k+1} + b‖ω‖₁(∫Φ²x²)/a²` at frequency scale `θ`. -/
def avgKernelBound (Φ ω : ℝ → ℝ) (a b : ℝ) (k : ℕ) (θ : ℝ) : ℝ :=
  2 * (∫ T in (a - 1)..(b + 1), |iteratedDeriv k ω T|) / θ ^ (k + 1) * (∫ x, Φ x ^ 2)
    + b * (∫ T in (a - 1)..(b + 1), |ω T|) * (∫ x, Φ x ^ 2 * x ^ 2) / a ^ 2

theorem avgKernelBound_nonneg (ha : 1 ≤ a) (hab : a ≤ b) {θ : ℝ} (hθ : 0 < θ) :
    0 ≤ avgKernelBound Φ ω a b k θ := by
  unfold avgKernelBound
  have hI : 0 ≤ ∫ T in (a - 1)..(b + 1), |iteratedDeriv k ω T| :=
    intervalIntegral.integral_nonneg (by linarith) fun _ _ => abs_nonneg _
  have hJ : 0 ≤ ∫ T in (a - 1)..(b + 1), |ω T| :=
    intervalIntegral.integral_nonneg (by linarith) fun _ _ => abs_nonneg _
  have hΦ0 : 0 ≤ ∫ x, Φ x ^ 2 := integral_nonneg fun _ => sq_nonneg _
  have hΦ1 : 0 ≤ ∫ x, Φ x ^ 2 * x ^ 2 := integral_nonneg fun _ => by positivity
  have hb0 : 0 ≤ b := by linarith
  positivity

/-- The kernel bound is antitone in the frequency scale. -/
theorem avgKernelBound_anti (hab : a ≤ b) {θ₁ θ₂ : ℝ} (h1 : 0 < θ₁) (h12 : θ₁ ≤ θ₂) :
    avgKernelBound Φ ω a b k θ₂ ≤ avgKernelBound Φ ω a b k θ₁ := by
  unfold avgKernelBound
  have hI : 0 ≤ ∫ T in (a - 1)..(b + 1), |iteratedDeriv k ω T| :=
    intervalIntegral.integral_nonneg (by linarith) fun _ _ => abs_nonneg _
  have hΦ0 : 0 ≤ ∫ x, Φ x ^ 2 := integral_nonneg fun _ => sq_nonneg _
  gcongr

theorem abs_avg_Agen_le_bound (hΦ : Continuous Φ) (hΦ2 : Integrable fun x => Φ x ^ 2)
    (hΦsq : Integrable fun x => Φ x ^ 2 * x ^ 2) (hω : ContDiff ℝ k ω)
    (hz : ∀ T ∉ Icc a b, ω T = 0) (ha : 1 ≤ a) (hab : a ≤ b) {θ₀ θ : ℝ} (hθ₀ : 0 < θ₀)
    (hθ : θ₀ ≤ |θ|) (y : ℝ) :
    |∫ T in (a - 1)..(b + 1), ω T * Agen Φ T θ y| ≤ avgKernelBound Φ ω a b k θ₀ := by
  have hθ0 : θ ≠ 0 := fun h => by rw [h, abs_zero] at hθ; linarith
  exact (abs_avg_Agen_le hΦ hΦ2 hΦsq hω hz ha hab hθ0 y).trans (avgKernelBound_anti hab hθ₀ hθ)

theorem intervalIntegrable_finsetSum' {s : Finset ℕ} {f : ℕ → ℝ → ℝ} {α β : ℝ}
    (h : ∀ i ∈ s, IntervalIntegrable (f i) volume α β) :
    IntervalIntegrable (fun T => ∑ i ∈ s, f i T) volume α β :=
  (IntervalIntegrable.sum s h).congr fun T _ => by simp only [Finset.sum_apply]

/-- **The height-averaged off-diagonal pairs** as a sum of averaged kernels. -/
theorem avg_ppOffDiag_eq (hΦ : Continuous Φ) (hω : Continuous ω) (ha : 1 ≤ a) (hab : a ≤ b)
    (X : ℝ) :
    ∫ T in (a - 1)..(b + 1), ω T * ppOffDiag Φ T X
      = ∑ n ∈ primeRange X, ∑ m ∈ primeRange X,
          if n = m then 0 else acoef n * acoef m
            * ∫ T in (a - 1)..(b + 1), ω T * Aminus Φ T (Real.log n) (Real.log m) := by
  have hint : ∀ n m : ℕ, IntervalIntegrable
      (fun T => ω T * (if n = m then (0 : ℝ) else
        acoef n * acoef m * Aminus Φ T (Real.log n) (Real.log m))) volume (a - 1) (b + 1) := by
    intro n m
    by_cases h : n = m
    · simp only [h, if_true, mul_zero]; exact intervalIntegrable_const
    · simp only [h, if_false]
      refine ((intervalIntegrable_mul_Agen hΦ hω ha hab (Real.log n - Real.log m)
        (Real.log n)).const_mul (acoef n * acoef m)).congr fun T _ => ?_
      show acoef n * acoef m * (ω T * Agen Φ T (Real.log n - Real.log m) (Real.log n))
        = ω T * (acoef n * acoef m * Aminus Φ T (Real.log n) (Real.log m))
      rw [Aminus_eq_Agen]; ring
  unfold ppOffDiag
  simp_rw [Finset.mul_sum]
  rw [intervalIntegral.integral_finsetSum fun n _ =>
    intervalIntegrable_finsetSum' fun m _ => hint n m]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [intervalIntegral.integral_finsetSum fun m _ => hint n m]
  refine Finset.sum_congr rfl fun m _ => ?_
  by_cases h : n = m
  · simp [h]
  · simp only [h, if_false]
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_congr fun T _ => by ring

/-- **The height-averaged sum frequencies** as a sum of averaged kernels. -/
theorem avg_ppSumFreq_eq (hΦ : Continuous Φ) (hω : Continuous ω) (ha : 1 ≤ a) (hab : a ≤ b)
    (X : ℝ) :
    ∫ T in (a - 1)..(b + 1), ω T * ppSumFreq Φ T X
      = ∑ n ∈ primeRange X, ∑ m ∈ primeRange X, acoef n * acoef m
          * ∫ T in (a - 1)..(b + 1), ω T * Aplus Φ T (Real.log n) (Real.log m) := by
  have hint : ∀ n m : ℕ, IntervalIntegrable
      (fun T => ω T * (acoef n * acoef m * Aplus Φ T (Real.log n) (Real.log m)))
      volume (a - 1) (b + 1) := by
    intro n m
    refine ((intervalIntegrable_mul_Agen hΦ hω ha hab (Real.log n + Real.log m)
      (Real.log n)).const_mul (acoef n * acoef m)).congr fun T _ => ?_
    show acoef n * acoef m * (ω T * Agen Φ T (Real.log n + Real.log m) (Real.log n))
      = ω T * (acoef n * acoef m * Aplus Φ T (Real.log n) (Real.log m))
    rw [Aplus_eq_Agen]; ring
  unfold ppSumFreq
  simp_rw [Finset.mul_sum]
  rw [intervalIntegral.integral_finsetSum fun n _ =>
    intervalIntegrable_finsetSum' fun m _ => hint n m]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [intervalIntegral.integral_finsetSum fun m _ => hint n m]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [← intervalIntegral.integral_const_mul]
  exact intervalIntegral.integral_congr fun T _ => by ring

theorem sum_sum_acoef_mul (X : ℝ) :
    ∑ n ∈ primeRange X, ∑ m ∈ primeRange X, acoef n * acoef m
      = (∑ n ∈ primeRange X, acoef n) ^ 2 := by
  rw [sq, Finset.sum_mul_sum]

/-- **Sum frequencies after height averaging.** `|∫ ω 𝒪₂| ≤ (Σ_{n≤X} a_n)² · avgKernelBound(1)`:
every sum frequency `log n + log m ≥ 2 log 2 > 1` is far from `0`. -/
theorem abs_avg_ppSumFreq_le (hΦ : Continuous Φ) (hΦ2 : Integrable fun x => Φ x ^ 2)
    (hΦsq : Integrable fun x => Φ x ^ 2 * x ^ 2) (hω : ContDiff ℝ k ω)
    (hz : ∀ T ∉ Icc a b, ω T = 0) (ha : 1 ≤ a) (hab : a ≤ b) (X : ℝ) :
    |∫ T in (a - 1)..(b + 1), ω T * ppSumFreq Φ T X|
      ≤ (∑ n ∈ primeRange X, acoef n) ^ 2 * avgKernelBound Φ ω a b k 1 := by
  rw [avg_ppSumFreq_eq hΦ hω.continuous ha hab, ← sum_sum_acoef_mul, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun n hn => ?_)
  rw [Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun m hm => ?_)
  have hB0 : 0 ≤ acoef n * acoef m := mul_nonneg (acoef_nonneg n) (acoef_nonneg m)
  rw [abs_mul, abs_of_nonneg hB0]
  rcases acoef_eq_zero_or_two_le hn with hn0 | hn2
  · simp [hn0]
  rcases acoef_eq_zero_or_two_le hm with hm0 | hm2
  · simp [hm0]
  refine mul_le_mul_of_nonneg_left ?_ hB0
  simp only [Aplus_eq_Agen]
  refine abs_avg_Agen_le_bound hΦ hΦ2 hΦsq hω hz ha hab one_pos ?_ _
  have hl2 : (1 : ℝ) / 2 ≤ Real.log 2 := by have := Real.log_two_gt_d9; linarith
  have hn' : Real.log 2 ≤ Real.log n := Real.log_le_log (by norm_num) (by exact_mod_cast hn2)
  have hm' : Real.log 2 ≤ Real.log m := Real.log_le_log (by norm_num) (by exact_mod_cast hm2)
  rw [abs_of_pos (by linarith)]
  linarith

/-- The averaged close-pair sum: off-diagonal pairs with `|log n − log m| ≤ θ₀`. -/
def avgClosePairs (Φ ω : ℝ → ℝ) (a b X θ₀ : ℝ) : ℝ :=
  ∑ n ∈ primeRange X, ∑ m ∈ primeRange X,
    if n = m ∨ θ₀ < |Real.log n - Real.log m| then 0 else acoef n * acoef m
      * ∫ T in (a - 1)..(b + 1), ω T * Aminus Φ T (Real.log n) (Real.log m)

/-- **Far pairs after height averaging.** The averaged off-diagonal sum differs from the averaged
close-pair sum `|log(n/m)| ≤ θ₀` by at most `(Σ_{n≤X} a_n)² · avgKernelBound(θ₀)`. -/
theorem abs_avg_ppOffDiag_sub_close_le (hΦ : Continuous Φ) (hΦ2 : Integrable fun x => Φ x ^ 2)
    (hΦsq : Integrable fun x => Φ x ^ 2 * x ^ 2) (hω : ContDiff ℝ k ω)
    (hz : ∀ T ∉ Icc a b, ω T = 0) (ha : 1 ≤ a) (hab : a ≤ b) (X : ℝ) {θ₀ : ℝ} (hθ₀ : 0 < θ₀) :
    |(∫ T in (a - 1)..(b + 1), ω T * ppOffDiag Φ T X) - avgClosePairs Φ ω a b X θ₀|
      ≤ (∑ n ∈ primeRange X, acoef n) ^ 2 * avgKernelBound Φ ω a b k θ₀ := by
  rw [avg_ppOffDiag_eq hΦ hω.continuous ha hab, avgClosePairs, ← Finset.sum_sub_distrib,
    ← sum_sum_acoef_mul, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun n _ => ?_)
  rw [← Finset.sum_sub_distrib, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun m _ => ?_)
  have hB0 : 0 ≤ acoef n * acoef m := mul_nonneg (acoef_nonneg n) (acoef_nonneg m)
  have hK0 : 0 ≤ avgKernelBound Φ ω a b k θ₀ := avgKernelBound_nonneg ha hab hθ₀
  by_cases hnm : n = m
  · subst hnm; simp only [if_true, true_or, sub_zero, abs_zero]; exact mul_nonneg hB0 hK0
  by_cases hfar : θ₀ < |Real.log n - Real.log m|
  · simp only [hnm, if_false, hfar, or_true, if_true, sub_zero]
    rw [abs_mul, abs_of_nonneg hB0]
    refine mul_le_mul_of_nonneg_left ?_ hB0
    simp only [Aminus_eq_Agen]
    exact abs_avg_Agen_le_bound hΦ hΦ2 hΦsq hω hz ha hab hθ₀ hfar.le _
  · simp only [hnm, hfar, if_false, or_self, sub_self, abs_zero]; exact mul_nonneg hB0 hK0

end Pairs

end GaloisForLFunctions.TransThresholdPairCorrelation
