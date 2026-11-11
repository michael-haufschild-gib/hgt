import GaloisForLFunctions.ShortIntervalPrimesInProgressions.TheExplicitFormulaForACharacter
import GaloisForLFunctions.RHTower.ChebyshevShortWindowLowerBound

/-!
# Character sums in short windows

Let `χ` be a primitive nonprincipal character. Write `ψ(X, χ) = Σ_{n ≤ X} χ(n)Λ(n)` and
`F(X) = X S(X, χ) − ψ(X, χ) = Σ_{n ≤ X} χ(n)Λ(n)(X/n − 1)`.

* **Squeeze.** On a window `[a, b]` with `w = 1/a − 1/b`, the average `(F(b)/b − F(a)/a)/w` differs
  from `ψ(a, χ)` by at most `ψ(b) − ψ(a)`: the twist only shrinks the nonnegative weights
  `1/n − 1/b ≤ w` (`norm_psiChi_sub_window_le`).
* **Zero side.** By the explicit formula the average is `Σ_ρ T(ρ; a, b) − β + O(log a) + O(D/(a²w))`
  with the corpus window terms `T` (`window_eq_zeroSum`).
* **Short windows** (`norm_psiChi_window_le`). For `2 ≤ x`, `0 < h'`, `2h' ≤ h ≤ x`,
  `|ψ(x+h, χ) − ψ(x, χ)| ≤ (ψ(x+h') − ψ(x)) + 2(ψ(x+h) − ψ(x+h−h')) + 2h Σ_ρ x^{β−1} min(1, 8x²/(hh'|ρ||1−ρ|)) + C(1 + log x) + C/h'`.
-/

open Complex Filter Topology Finset
open GaloisForLFunctions.EntireZeroDivisor
open ArithmeticFunction (vonMangoldt)

namespace GaloisForLFunctions.ShortIntervalPrimesInProgressions

noncomputable section

variable {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}

/-- `ψ(X, χ) = Σ_{n ≤ X} χ(n)Λ(n)`. -/
def psiChi (χ : DirichletCharacter ℂ N) (X : ℝ) : ℂ := ∑ n ∈ Icc 1 ⌊X⌋₊, twistedVM χ n

/-- `S(X, χ) = Σ_{n ≤ X} χ(n)Λ(n)/n`. -/
def sChi (χ : DirichletCharacter ℂ N) (X : ℝ) : ℂ := ∑ n ∈ Icc 1 ⌊X⌋₊, twistedVM χ n / n

omit [NeZero N] in
theorem perronSum_eq (X : ℝ) :
    ∑ n ∈ Icc 1 ⌊X⌋₊, twistedVM χ n * ((X : ℂ) / n - 1) = X * sChi χ X - psiChi χ X := by
  rw [sChi, psiChi, mul_sum, ← sum_sub_distrib]
  exact sum_congr rfl fun n _ => by ring

omit [NeZero N] in
theorem Icc_split {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    Icc 1 ⌊b⌋₊ = Icc 1 ⌊a⌋₊ ∪ Ioc ⌊a⌋₊ ⌊b⌋₊ := by
  have hfl : ⌊a⌋₊ ≤ ⌊b⌋₊ := Nat.floor_le_floor hab
  ext n
  simp only [mem_Icc, mem_union, mem_Ioc]
  omega

omit [NeZero N] in
theorem Icc_disjoint (a b : ℝ) : Disjoint (Icc 1 ⌊a⌋₊) (Ioc ⌊a⌋₊ ⌊b⌋₊) := by
  rw [disjoint_left]
  intro n h1 h2
  simp only [mem_Icc, mem_Ioc] at h1 h2
  omega

omit [NeZero N] in
/-- The window statistic: `F(b)/b − F(a)/a = ψ(a,χ)w + Σ_{a<n≤b} χ(n)Λ(n)(1/n − 1/b)`. -/
theorem window_split {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    sChi χ b - psiChi χ b / b - (sChi χ a - psiChi χ a / a) =
      psiChi χ a * ((1 / a - 1 / b : ℝ) : ℂ) +
        ∑ n ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, twistedVM χ n * (1 / (n : ℂ) - 1 / b) := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  rw [sChi, sChi, psiChi, psiChi, Icc_split ha.le hab, sum_union (Icc_disjoint a b),
    sum_union (Icc_disjoint a b)]
  have hb0 : (b : ℂ) ≠ 0 := by exact_mod_cast hb.ne'
  have ha0 : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  have hR : ∑ n ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, twistedVM χ n * (1 / (n : ℂ) - 1 / b) =
      ∑ n ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, twistedVM χ n / n - (∑ n ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, twistedVM χ n) / b := by
    rw [sum_div, ← sum_sub_distrib]
    exact sum_congr rfl fun n _ => by ring
  rw [hR]
  push_cast
  field_simp
  ring

theorem psi_mono_window {a b : ℝ} (hab : a ≤ b) (ha : 0 ≤ a) :
    ∑ n ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, vonMangoldt n = Chebyshev.psi b - Chebyshev.psi a := by
  rw [Chebyshev.psi_eq_sum_Icc, Chebyshev.psi_eq_sum_Icc]
  have hfl : ⌊a⌋₊ ≤ ⌊b⌋₊ := Nat.floor_le_floor hab
  have hsplit : Icc 0 ⌊b⌋₊ = Icc 0 ⌊a⌋₊ ∪ Ioc ⌊a⌋₊ ⌊b⌋₊ := by
    ext n; simp only [mem_Icc, mem_union, mem_Ioc]; omega
  have hdisj : Disjoint (Icc 0 ⌊a⌋₊) (Ioc ⌊a⌋₊ ⌊b⌋₊) := by
    rw [disjoint_left]; intro n h1 h2; simp only [mem_Icc, mem_Ioc] at h1 h2; omega
  rw [hsplit, sum_union hdisj]
  ring

omit [NeZero N] in
/-- **The squeeze.** `|ψ(a, χ) − (F(b)/b − F(a)/a)/w| ≤ ψ(b) − ψ(a)` on a window `[a, b]`. -/
theorem norm_psiChi_sub_window_le {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    ‖(sChi χ b - psiChi χ b / b - (sChi χ a - psiChi χ a / a)) / ((1 / a - 1 / b : ℝ) : ℂ) -
        psiChi χ a‖ ≤ Chebyshev.psi b - Chebyshev.psi a := by
  have hb : 0 < b := lt_trans ha hab
  have hw : 0 < 1 / a - 1 / b := by rw [sub_pos]; exact one_div_lt_one_div_of_lt ha hab
  have hw0 : ((1 / a - 1 / b : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hw.ne'
  rw [window_split ha hab.le, add_div, mul_div_cancel_right₀ _ hw0, add_sub_cancel_left,
    norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hw, div_le_iff₀ hw,
    ← psi_mono_window hab.le ha.le, sum_mul]
  refine (norm_sum_le _ _).trans (sum_le_sum fun n hn => ?_)
  simp only [mem_Ioc] at hn
  have hn0 : (0 : ℝ) < n := by
    have : a < n := (Nat.floor_lt ha.le).mp (Nat.lt_of_lt_of_le (by omega) le_rfl) |>.trans_le le_rfl
    linarith
  have han : a < n := Nat.lt_of_floor_lt hn.1
  have hnb : (n : ℝ) ≤ b := (Nat.cast_le.mpr hn.2).trans (Nat.floor_le hb.le)
  rw [norm_mul]
  have hweight : ‖(1 / (n : ℂ) - 1 / b)‖ ≤ 1 / a - 1 / b := by
    rw [show (1 / (n : ℂ) - 1 / b) = ((1 / (n : ℝ) - 1 / b : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by
        rw [sub_nonneg]; exact one_div_le_one_div_of_le hn0 hnb)]
    gcongr
  exact mul_le_mul (norm_twistedVM_le n) hweight (norm_nonneg _)
    ArithmeticFunction.vonMangoldt_nonneg

/-! ### The zero side -/

/-- A generic zero `ρ` of the critical strip: the corpus window bound. -/
theorem norm_window_diff_le_zeroShortWeight' {x h h' : ℝ} (hx : 2 ≤ x) (hh' : 0 < h')
    (hh'h : 2 * h' ≤ h) (hhx : h ≤ x) {ρ : ℂ} (hρ0 : 0 < ρ.re) (hρ1 : ρ.re < 1) :
    ‖RHTower.lagWindowZeroTerm ρ (x + h - h') (x + h) - RHTower.lagWindowZeroTerm ρ x (x + h')‖
      ≤ 2 * h * RHTower.zeroShortWeight x (8 * x ^ 2 / (h * h')) ρ := by
  have hx0 : 0 < x := by linarith
  have hh : 0 < h := by linarith
  have hρne : ρ ≠ 0 := fun h0 => by rw [h0, zero_re] at hρ0; exact lt_irrefl 0 hρ0
  have hρ1ne : 1 - ρ ≠ 0 := by
    intro h1; have := congrArg Complex.re h1; rw [sub_re, one_re, zero_re] at this; linarith
  set β := ρ.re with hβ
  set M := ‖ρ‖ * ‖1 - ρ‖ with hM
  have hM0 : 0 < M := mul_pos (norm_pos_iff.mpr hρne) (norm_pos_iff.mpr hρ1ne)
  have hshort := RHTower.norm_lagWindowZeroTerm_sub_le (a₁ := x + h - h') (b₁ := x + h)
    (a₂ := x) (b₂ := x + h') (H := h) hx0 (by linarith) (by linarith) le_rfl le_rfl
    (by linarith) (by linarith) hρ0 hρ1
  have hlong : ∀ a b : ℝ, x ≤ a → b - a = h' → b ≤ 2 * x →
      ‖RHTower.lagWindowZeroTerm ρ a b‖ ≤ 8 * x ^ (β - 1) * x ^ 2 / (h' * M) := by
    intro a b hxa hba hb2
    have ha0 : 0 < a := by linarith
    have hab : a < b := by linarith
    have hb0 : 0 < b := by linarith
    have hpa : a ^ (β - 1) ≤ x ^ (β - 1) := Real.rpow_le_rpow_of_nonpos hx0 hxa (by linarith)
    have hpb : b ^ (β - 1) ≤ x ^ (β - 1) :=
      Real.rpow_le_rpow_of_nonpos hx0 (by linarith) (by linarith)
    have hweq : 1 / a - 1 / b = h' / (a * b) := by rw [← hba]; field_simp
    refine le_trans (RHTower.norm_lagWindowZeroTerm_le ha0 hab _) ?_
    rw [← hβ, ← hM, hweq]
    have hab4 : a * b ≤ 4 * x ^ 2 := by nlinarith
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hsum : a ^ (β - 1) + b ^ (β - 1) ≤ 2 * x ^ (β - 1) := by linarith
    have hxb : 0 ≤ x ^ (β - 1) := Real.rpow_nonneg hx0.le _
    have e3 : 1 ≤ 4 * x ^ 2 / (a * b) := by rw [le_div_iff₀ (by positivity)]; linarith
    calc (a ^ (β - 1) + b ^ (β - 1)) * (h' * M) ≤ 2 * x ^ (β - 1) * (h' * M) :=
          mul_le_mul_of_nonneg_right hsum (by positivity)
      _ = 2 * x ^ (β - 1) * (h' * M) * 1 := by ring
      _ ≤ 2 * x ^ (β - 1) * (h' * M) * (4 * x ^ 2 / (a * b)) :=
          mul_le_mul_of_nonneg_left e3 (by positivity)
      _ = 8 * x ^ (β - 1) * x ^ 2 * (M * (h' / (a * b))) := by field_simp; ring
  have h1 := hlong (x + h - h') (x + h) (by linarith) (by ring) (by linarith)
  have h2 := hlong x (x + h') le_rfl (by ring) (by linarith)
  have hlong2 : ‖RHTower.lagWindowZeroTerm ρ (x + h - h') (x + h) -
      RHTower.lagWindowZeroTerm ρ x (x + h')‖ ≤ 16 * x ^ (β - 1) * x ^ 2 / (h' * M) := by
    refine le_trans (norm_sub_le _ _) ?_
    have : 16 * x ^ (β - 1) * x ^ 2 / (h' * M)
        = 8 * x ^ (β - 1) * x ^ 2 / (h' * M) + 8 * x ^ (β - 1) * x ^ 2 / (h' * M) := by ring
    linarith
  rw [RHTower.zeroShortWeight, ← hβ, ← hM, ← mul_assoc, mul_min_of_nonneg _ _ (by positivity),
    mul_one]
  refine le_min hshort (le_of_le_of_eq hlong2 ?_)
  field_simp
  ring

omit [NeZero N] in
/-- Twisted window masses are dominated by the untwisted ones. -/
theorem norm_psiChi_sub_le {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    ‖psiChi χ b - psiChi χ a‖ ≤ Chebyshev.psi b - Chebyshev.psi a := by
  rw [psiChi, psiChi, Icc_split ha hab, sum_union (Icc_disjoint a b), add_sub_cancel_left,
    ← psi_mono_window hab ha]
  exact (norm_sum_le _ _).trans (sum_le_sum fun n _ => norm_twistedVM_le n)

theorem summable_inv_norm_mul (hχ : χ ≠ 1) (hprim : χ.IsPrimitive) :
    Summable (fun q : LZero χ => 1 / (‖q.point‖ * ‖1 - q.point‖)) := by
  have hev := RHTower.eventually_norm_ge_of_summable_inv_sq (zeroCopyPoint_ne_zero' hχ)
    (summable_inv_sq hχ) (S := 4) (by norm_num)
  refine Summable.of_norm_bounded_eventually
    (g := fun q => (8 / 3) * (1 / ‖zeroCopyPoint (shiftedL χ) q‖ ^ (2 : ℕ)))
    ((summable_inv_sq hχ).mul_left _) ?_
  filter_upwards [hev] with q hq
  set w := zeroCopyPoint (shiftedL χ) q
  have hpt : q.point = w + 2 := rfl
  have hw0 : 0 < ‖w‖ := by linarith
  have hρ : ‖w‖ / 2 ≤ ‖q.point‖ := by
    rw [hpt]
    have := norm_sub_norm_le w (-(2 : ℂ))
    rw [sub_neg_eq_add, norm_neg] at this
    norm_num at this
    linarith
  have hρ1 : 3 * ‖w‖ / 4 ≤ ‖1 - q.point‖ := by
    rw [hpt, show 1 - (w + 2) = -(w - (-1)) by ring, norm_neg]
    have := norm_sub_norm_le w (-1 : ℂ)
    rw [norm_neg, norm_one] at this
    linarith
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc 1 / (‖q.point‖ * ‖1 - q.point‖) ≤ 1 / ((‖w‖ / 2) * (3 * ‖w‖ / 4)) := by gcongr
    _ = (8 / 3) * (1 / ‖w‖ ^ (2 : ℕ)) := by field_simp; ring

theorem summable_zeroShortWeight (hχ : χ ≠ 1) (hprim : χ.IsPrimitive) {x Y : ℝ} (hx : 1 ≤ x)
    (hY : 0 ≤ Y) : Summable (fun q : LZero χ => RHTower.zeroShortWeight x Y q.point) := by
  refine Summable.of_nonneg_of_le (fun q => RHTower.zeroShortWeight_nonneg (by linarith) hY _)
    (fun q => ?_) ((summable_inv_norm_mul hχ hprim).mul_left Y)
  rw [RHTower.zeroShortWeight]
  have hle : x ^ (q.point.re - 1) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hx (by linarith [(zero_re_mem hχ hprim q).2])
  have hm0 : 0 ≤ min 1 (Y / (‖q.point‖ * ‖1 - q.point‖)) := le_min zero_le_one (by positivity)
  calc x ^ (q.point.re - 1) * min 1 (Y / (‖q.point‖ * ‖1 - q.point‖))
      ≤ 1 * min 1 (Y / (‖q.point‖ * ‖1 - q.point‖)) := mul_le_mul_of_nonneg_right hle hm0
    _ ≤ Y * (1 / (‖q.point‖ * ‖1 - q.point‖)) := by rw [one_mul, mul_one_div]; exact min_le_right _ _

/-- The window statistic `F(X)/X = S(X,χ) − ψ(X,χ)/X`. -/
def windowStat (χ : DirichletCharacter ℂ N) (X : ℝ) : ℂ := sChi χ X - psiChi χ X / X

/-- **The zero side of a window.** For `1 < a < b ≤ 2a` the window average equals
`Σ_ρ T(ρ; a, b) − β` up to `|γ'|(1 + log a) + 4D/(b − a)`. -/
theorem norm_window_sub_zeroSum_le (hχ : χ ≠ 1) (hprim : χ.IsPrimitive) :
    ∃ β γ' : ℂ, ∃ D : ℝ, 0 ≤ D ∧ ∀ a b : ℝ, 1 < a → a < b → b ≤ 2 * a →
      Summable (fun q : LZero χ => RHTower.lagWindowZeroTerm q.point a b) ∧
      ‖(windowStat χ b - windowStat χ a) / ((1 / a - 1 / b : ℝ) : ℂ) -
          (∑' q : LZero χ, RHTower.lagWindowZeroTerm q.point a b - β)‖ ≤
        ‖γ'‖ * (1 + Real.log a) + 4 * D / (b - a) := by
  obtain ⟨α, β, γ', D, hD, hEF⟩ := explicitFormula hχ hprim
  refine ⟨β, γ', D, hD, fun a b ha hab hb2 => ?_⟩
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := by linarith
  have hb1 : 1 < b := by linarith
  have hw : 0 < 1 / a - 1 / b := by rw [sub_pos]; exact one_div_lt_one_div_of_lt ha0 hab
  have hwc : ((1 / a - 1 / b : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hw.ne'
  -- the remainder of the explicit formula
  set Z : ℝ → ℂ := fun X => ∑' q : LZero χ, (X : ℂ) ^ q.point / (q.point * (q.point - 1))
  set Θ : ℝ → ℂ := fun X => X * sChi χ X - psiChi χ X + Z X - (α * X + β + γ' * Complex.log X)
  have hΘ : ∀ X : ℝ, 1 < X → ‖Θ X‖ ≤ D / X := by
    intro X hX
    have := hEF X hX
    rwa [perronSum_eq] at this
  have hstat : ∀ X : ℝ, 0 < X → windowStat χ X =
      -(Z X / X) + α + β / X + γ' * Complex.log X / X + Θ X / X := by
    intro X hX
    have hX0 : (X : ℂ) ≠ 0 := by exact_mod_cast hX.ne'
    simp only [windowStat, Θ]
    field_simp
    ring
  -- the zero sums
  have hZ : ∀ X : ℝ, 0 < X → Z X / X =
      ∑' q : LZero χ, (X : ℂ) ^ (q.point - 1) / (q.point * (q.point - 1)) := by
    intro X hX
    have hX0 : (X : ℂ) ≠ 0 := by exact_mod_cast hX.ne'
    simp only [Z]
    rw [← tsum_div_const]
    refine tsum_congr fun q => ?_
    rw [Complex.cpow_sub _ _ hX0, Complex.cpow_one]
    field_simp
  have hsa := summable_cpow_div hχ hprim ha
  have hsb := summable_cpow_div hχ hprim hb1
  have hsa' : Summable fun q : LZero χ => (a : ℂ) ^ (q.point - 1) / (q.point * (q.point - 1)) :=
    (hsa.div_const (a : ℂ)).congr fun q => by
      rw [Complex.cpow_sub _ _ (by exact_mod_cast ha0.ne'), Complex.cpow_one]; field_simp
  have hsb' : Summable fun q : LZero χ => (b : ℂ) ^ (q.point - 1) / (q.point * (q.point - 1)) :=
    (hsb.div_const (b : ℂ)).congr fun q => by
      rw [Complex.cpow_sub _ _ (by exact_mod_cast hb0.ne'), Complex.cpow_one]; field_simp
  have hT : ∀ q : LZero χ, RHTower.lagWindowZeroTerm q.point a b =
      -((b : ℂ) ^ (q.point - 1) / (q.point * (q.point - 1)) -
        (a : ℂ) ^ (q.point - 1) / (q.point * (q.point - 1))) / ((1 / a - 1 / b : ℝ) : ℂ) := by
    intro q
    have h0 := point_ne_zero hχ hprim q
    have h1 : q.point - 1 ≠ 0 := sub_ne_zero.mpr (point_ne_one hχ hprim q)
    have h1' : 1 - q.point ≠ 0 := fun h => h1 (by linear_combination -h)
    rw [RHTower.lagWindowZeroTerm]
    field_simp
    ring
  have hsumT : Summable fun q : LZero χ => RHTower.lagWindowZeroTerm q.point a b :=
    ((hsb'.sub hsa').neg.div_const _).congr fun q => (hT q).symm
  refine ⟨hsumT, ?_⟩
  have htsumT : ∑' q : LZero χ, RHTower.lagWindowZeroTerm q.point a b =
      -(Z b / b - Z a / a) / ((1 / a - 1 / b : ℝ) : ℂ) := by
    rw [tsum_congr hT, tsum_div_const, tsum_neg, hsb'.tsum_sub hsa', hZ b hb0, hZ a ha0]
  rw [hstat b hb0, hstat a ha0, htsumT]
  -- what remains: the β, log and Θ terms
  have hβw : β / b - β / a = -β * ((1 / a - 1 / b : ℝ) : ℂ) := by push_cast; ring
  have hrest : (-(Z b / b) + α + β / b + γ' * Complex.log b / b + Θ b / b -
        (-(Z a / a) + α + β / a + γ' * Complex.log a / a + Θ a / a)) /
        ((1 / a - 1 / b : ℝ) : ℂ) -
      (-(Z b / b - Z a / a) / ((1 / a - 1 / b : ℝ) : ℂ) - β) =
      γ' * ((Complex.log b / b - Complex.log a / a) / ((1 / a - 1 / b : ℝ) : ℂ)) +
        (Θ b / b - Θ a / a) / ((1 / a - 1 / b : ℝ) : ℂ) := by
    have hw' : ((1 / a - 1 / b : ℝ) : ℂ) = 1 / (a : ℂ) - 1 / (b : ℂ) := by push_cast; ring
    have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast ha0.ne'
    have hb' : (b : ℂ) ≠ 0 := by exact_mod_cast hb0.ne'
    have hba : (b : ℂ) - a ≠ 0 := by
      rw [sub_ne_zero]; exact_mod_cast hab.ne'
    rw [hw']
    field_simp
    ring
  rw [hrest]
  -- the logarithmic term
  have hlog : ‖(Complex.log b / b - Complex.log a / a) / ((1 / a - 1 / b : ℝ) : ℂ)‖ ≤
      1 + Real.log a := by
    rw [show Complex.log b / b - Complex.log a / a =
        ((Real.log b / b - Real.log a / a : ℝ) : ℂ) by
      push_cast; rw [Complex.ofReal_log hb0.le, Complex.ofReal_log ha0.le],
      ← Complex.ofReal_div, Complex.norm_real, Real.norm_eq_abs, abs_div, abs_of_pos hw,
      div_le_iff₀ hw]
    have hla : 0 ≤ Real.log a := Real.log_nonneg ha.le
    have hsplit : Real.log b / b - Real.log a / a =
        Real.log (b / a) / b - Real.log a * (1 / a - 1 / b) := by
      rw [Real.log_div hb0.ne' ha0.ne']; field_simp; ring
    have hlba : 0 ≤ Real.log (b / a) := Real.log_nonneg (by rw [le_div_iff₀ ha0]; linarith)
    have hlb : Real.log (b / a) / b ≤ 1 / a - 1 / b := by
      have := Real.log_le_sub_one_of_pos (show 0 < b / a by positivity)
      rw [div_le_iff₀ hb0]
      calc Real.log (b / a) ≤ b / a - 1 := this
        _ = (1 / a - 1 / b) * b := by field_simp
    rw [hsplit]
    calc |Real.log (b / a) / b - Real.log a * (1 / a - 1 / b)|
        ≤ |Real.log (b / a) / b| + |Real.log a * (1 / a - 1 / b)| := abs_sub _ _
      _ = Real.log (b / a) / b + Real.log a * (1 / a - 1 / b) := by
          rw [abs_of_nonneg (by positivity), abs_of_nonneg (mul_nonneg hla hw.le)]
      _ ≤ (1 / a - 1 / b) + Real.log a * (1 / a - 1 / b) := by linarith
      _ = (1 + Real.log a) * (1 / a - 1 / b) := by ring
  -- the remainder term
  have hrem : ‖(Θ b / b - Θ a / a) / ((1 / a - 1 / b : ℝ) : ℂ)‖ ≤ 4 * D / (b - a) := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hw, div_le_iff₀ hw]
    have h1 : ‖Θ b / b‖ ≤ D / a ^ 2 := by
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hb0]
      calc ‖Θ b‖ / b ≤ (D / b) / b := div_le_div_of_nonneg_right (hΘ b hb1) hb0.le
        _ = D / (b * b) := by rw [div_div]
        _ ≤ D / a ^ 2 := div_le_div_of_nonneg_left hD (by positivity) (by nlinarith)
    have h2 : ‖Θ a / a‖ ≤ D / a ^ 2 := by
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha0]
      calc ‖Θ a‖ / a ≤ (D / a) / a := div_le_div_of_nonneg_right (hΘ a ha) ha0.le
        _ = D / a ^ 2 := by rw [div_div, sq]
    have hba : 0 < b - a := by linarith
    have hgoal : 4 * D / (b - a) * (1 / a - 1 / b) = 4 * D / (a * b) := by
      field_simp
    rw [hgoal]
    calc ‖Θ b / b - Θ a / a‖ ≤ ‖Θ b / b‖ + ‖Θ a / a‖ := norm_sub_le _ _
      _ ≤ 2 * D / a ^ 2 := by linarith
      _ ≤ 4 * D / (a * b) := by
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith
  calc ‖γ' * ((Complex.log b / b - Complex.log a / a) / ((1 / a - 1 / b : ℝ) : ℂ)) +
        (Θ b / b - Θ a / a) / ((1 / a - 1 / b : ℝ) : ℂ)‖
      ≤ ‖γ'‖ * ‖(Complex.log b / b - Complex.log a / a) / ((1 / a - 1 / b : ℝ) : ℂ)‖ +
        ‖(Θ b / b - Θ a / a) / ((1 / a - 1 / b : ℝ) : ℂ)‖ := by
          rw [← norm_mul]; exact norm_add_le _ _
    _ ≤ ‖γ'‖ * (1 + Real.log a) + 4 * D / (b - a) := by gcongr

end

end GaloisForLFunctions.ShortIntervalPrimesInProgressions
