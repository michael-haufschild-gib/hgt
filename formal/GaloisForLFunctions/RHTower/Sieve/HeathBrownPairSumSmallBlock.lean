import GaloisForLFunctions.RHTower.Sieve.HeathBrownPairSumRestrictedRange

/-!
# Heath-Brown's pair-sum theorem for short blocks

For a short block the pair sum is bounded by reflecting it onto a *long* block, where the
unconditional theorem of `HeathBrownPairSumRestrictedRange` applies.  The reflection is
Heath-Brown's own Corollary 2.1 in the dilation form `hbAmp_sq_le_rpow`: squaring a polynomial
supported in `(M, 2M]` produces divisor-bounded coefficients on `(M², 4M²]`, and the dilation
comparison carries that block into `(N, 8N]` for any `N ≥ M²`.  So

`𝒜_{1/2}((M,2M])² ≤ 2 (C_δ(8N)^δ)⁵ |W|² 𝒜_{1/2}((N,8N])`

and with `N = ⌈(2T)^{2/3}⌉` the right-hand factor is the long-block bound
`112 N |W| c(T) + K(T) · 2 (C_δ(8N)^δ)⁵ |W|²`.  Since `N ≍ T^{2/3}`, this gives

`𝒜_{1/2}((M,2M]) ⪅ T^{1/3}|W|^{3/2} + |W|²`.

The elementary inequality `T^{2/3} w³ ≤ w^{13/4}T^{1/2} + w^{5/2}T` for `w, T ≥ 1`
(`rpow_two_thirds_mul_cube_le`, by the case split at `w = T^{2/3}`, which is exactly the case
split of Guth–Maynard's Lemma 11.9) converts this into Heath-Brown's shape

`Σ_{t₁,t₂∈W} |Σ_{M<n≤2M} a_n n^{i(t₁−t₂)}|² ≤ C(T,δ) (|W|²M + |W|M² + |W|^{5/4}T^{1/2}M)`,

valid whenever `M² ≤ (2T)^{2/3}`, in particular for all `M ≤ T^{1/4}`: the range in which
Guth–Maynard's Lemmas 11.5 and 11.6 are applied inside Lemma 11.9 (`M = N/d`, `d ≥ N²/T`,
`N ≥ T^{3/4}`).
-/

set_option autoImplicit false

namespace RHTower.Sieve

open Finset

noncomputable section

/-- The reflection factor `c(T)` of the long-block bound. -/
def hbReflFactor (T : ℝ) : ℝ :=
  1 + 12 * hbReflConst ^ 2 * (1 + Real.logb 2 T) * ((1 + (1 + Real.logb 2 T)) ^ 2 + 1)

/-- The dual-block factor `K(T)` of the long-block bound. -/
def hbDualFactor (T : ℝ) : ℝ :=
  (1200000 * (1 + Real.logb 2 T) ^ 2) ^ 2 * (9 * (1 + Real.logb 2 T)) ^ 2

/-- The auxiliary long block `⌈(2T)^{2/3}⌉` onto which a short block is reflected. -/
def hbLongBlock (T : ℝ) : ℕ := ⌈(2 * T) ^ ((2 : ℝ) / 3)⌉₊

/-- The explicit constant of the short-block bound: polylogarithmic in `T` times
`(8⌈(2T)^{2/3}⌉)^{10δ}`. -/
def hbSmallConst (T δ : ℝ) : ℝ :=
  3584 * ((divisorBoundConst δ * ((8 * hbLongBlock T : ℕ) : ℝ) ^ δ) ^ 10 + 1) *
    (hbReflFactor T + hbDualFactor T + 1)

/-! ### The two factors -/

theorem one_le_hbReflFactor {T : ℝ} (hT : 1 ≤ T) : 1 ≤ hbReflFactor T := by
  have h : 0 ≤ Real.logb 2 T := Real.logb_nonneg (by norm_num) hT
  have h1 : (0 : ℝ) ≤ 12 * hbReflConst ^ 2 := by positivity
  have h2 : (0 : ℝ) ≤ 1 + Real.logb 2 T := by linarith
  have h3 : (0 : ℝ) ≤ (1 + (1 + Real.logb 2 T)) ^ 2 + 1 := by positivity
  have := mul_nonneg (mul_nonneg h1 h2) h3
  rw [hbReflFactor]
  linarith

theorem hbDualFactor_nonneg (T : ℝ) : 0 ≤ hbDualFactor T := by
  rw [hbDualFactor]
  positivity

theorem one_le_hbSmallConst {T δ : ℝ} (hT : 1 ≤ T) (_hδ : 0 < δ) : 1 ≤ hbSmallConst T δ := by
  have hc := one_le_hbReflFactor hT
  have hK := hbDualFactor_nonneg T
  have hC : 0 ≤ (divisorBoundConst δ * ((8 * hbLongBlock T : ℕ) : ℝ) ^ δ) ^ 10 := by positivity
  rw [hbSmallConst]
  nlinarith

/-! ### The auxiliary long block -/

theorem one_le_hbLongBlock {T : ℝ} (hT : 1 ≤ T) : 1 ≤ hbLongBlock T := by
  rw [hbLongBlock, Nat.one_le_ceil_iff]
  exact Real.rpow_pos_of_pos (by linarith) _

theorem le_hbLongBlock (T : ℝ) : (2 * T) ^ ((2 : ℝ) / 3) ≤ (hbLongBlock T : ℝ) :=
  Nat.le_ceil _

/-- `⌈(2T)^{2/3}⌉² > 2T`: the long block is admissible for the restricted-range theorem. -/
theorem two_mul_lt_hbLongBlock_sq {T : ℝ} (hT : 1 ≤ T) : 2 * T < (hbLongBlock T : ℝ) ^ 2 := by
  have h2T : (1 : ℝ) < 2 * T := by linarith
  have h0 : (0 : ℝ) ≤ 2 * T := by linarith
  have hy : (0 : ℝ) ≤ (2 * T) ^ ((2 : ℝ) / 3) := Real.rpow_nonneg h0 _
  have hsq : ((2 * T) ^ ((2 : ℝ) / 3)) ^ 2 = (2 * T) ^ ((4 : ℝ) / 3) := by
    rw [← Real.rpow_natCast ((2 * T) ^ ((2 : ℝ) / 3)) 2, ← Real.rpow_mul h0]
    norm_num
  have h43 : 2 * T < (2 * T) ^ ((4 : ℝ) / 3) := by
    have h := Real.rpow_lt_rpow_of_exponent_lt h2T (by norm_num : (1 : ℝ) < (4 : ℝ) / 3)
    rwa [Real.rpow_one] at h
  calc 2 * T < (2 * T) ^ ((4 : ℝ) / 3) := h43
    _ = ((2 * T) ^ ((2 : ℝ) / 3)) ^ 2 := hsq.symm
    _ ≤ (hbLongBlock T : ℝ) ^ 2 := by gcongr; exact le_hbLongBlock T

/-- `9⌈(2T)^{2/3}⌉³ ≥ 4T²`: the second admissibility condition. -/
theorem four_mul_sq_le_hbLongBlock_cube {T : ℝ} (hT : 1 ≤ T) :
    4 * T ^ 2 ≤ 9 * (hbLongBlock T : ℝ) ^ 3 := by
  have h0 : (0 : ℝ) ≤ 2 * T := by linarith
  have hy : (0 : ℝ) ≤ (2 * T) ^ ((2 : ℝ) / 3) := Real.rpow_nonneg h0 _
  have hcube : ((2 * T) ^ ((2 : ℝ) / 3)) ^ 3 = 4 * T ^ 2 := by
    rw [← Real.rpow_natCast ((2 * T) ^ ((2 : ℝ) / 3)) 3, ← Real.rpow_mul h0,
      show ((2 : ℝ) / 3 * (3 : ℕ)) = 2 by norm_num,
      show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    ring
  have hstep : 4 * T ^ 2 ≤ (hbLongBlock T : ℝ) ^ 3 := by
    rw [← hcube]
    gcongr
    exact le_hbLongBlock T
  have hpos : (0 : ℝ) ≤ (hbLongBlock T : ℝ) ^ 3 := by positivity
  linarith

/-- `⌈(2T)^{2/3}⌉ ≤ 4T^{2/3}`. -/
theorem hbLongBlock_le_rpow {T : ℝ} (hT : 1 ≤ T) :
    (hbLongBlock T : ℝ) ≤ 4 * T ^ ((2 : ℝ) / 3) := by
  have h0 : (0 : ℝ) ≤ 2 * T := by linarith
  have hT0 : (0 : ℝ) ≤ T := by linarith
  have h1 : (1 : ℝ) ≤ (2 * T) ^ ((2 : ℝ) / 3) :=
    Real.one_le_rpow (by linarith) (by norm_num)
  have hceil : (hbLongBlock T : ℝ) < (2 * T) ^ ((2 : ℝ) / 3) + 1 := by
    rw [hbLongBlock]
    exact Nat.ceil_lt_add_one (by linarith)
  have hsplit : (2 * T) ^ ((2 : ℝ) / 3) = (2 : ℝ) ^ ((2 : ℝ) / 3) * T ^ ((2 : ℝ) / 3) :=
    Real.mul_rpow (by norm_num) hT0
  have h2 : (2 : ℝ) ^ ((2 : ℝ) / 3) ≤ 2 := by
    have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
      (by norm_num : (2 : ℝ) / 3 ≤ 1)
    rwa [Real.rpow_one] at h
  have hTr : (1 : ℝ) ≤ T ^ ((2 : ℝ) / 3) := Real.one_le_rpow hT (by norm_num)
  rw [hsplit] at hceil h1
  nlinarith

/-- `C⁵ ≤ C^{10} + 1` for `C ≥ 0`. -/
private theorem pow_five_le_pow_ten_add_one {C : ℝ} (hC : 0 ≤ C) : C ^ 5 ≤ C ^ 10 + 1 := by
  rcases le_total C 1 with h | h
  · have h1 : C ^ 5 ≤ 1 := pow_le_one₀ hC h
    have h2 : (0 : ℝ) ≤ C ^ 10 := by positivity
    linarith
  · have h1 : C ^ 5 ≤ C ^ 10 := pow_le_pow_right₀ h (by norm_num)
    linarith

/-- The three comparisons the explicit constant has to satisfy. -/
theorem one_le_hbSmallConst_div_two {T δ : ℝ} (hT : 1 ≤ T) (_hδ : 0 < δ) :
    1 ≤ hbSmallConst T δ / 2 := by
  have hA : (0 : ℝ) ≤ (divisorBoundConst δ * ((8 * hbLongBlock T : ℕ) : ℝ) ^ δ) ^ 10 := by
    positivity
  have hc := one_le_hbReflFactor (T := T) hT
  have hK := hbDualFactor_nonneg T
  have h2 : (2 : ℝ) ≤
      ((divisorBoundConst δ * ((8 * hbLongBlock T : ℕ) : ℝ) ^ δ) ^ 10 + 1) *
        (hbReflFactor T + hbDualFactor T + 1) := by nlinarith
  rw [hbSmallConst]
  linarith

theorem hbSmallConst_refl_le {T δ : ℝ} (hT : 1 ≤ T) (hδ : 0 < δ) :
    896 * (divisorBoundConst δ * ((8 * hbLongBlock T : ℕ) : ℝ) ^ δ) ^ 5 * hbReflFactor T ≤
      hbSmallConst T δ / 2 := by
  have hC0 : (0 : ℝ) ≤ divisorBoundConst δ * ((8 * hbLongBlock T : ℕ) : ℝ) ^ δ :=
    mul_nonneg (divisorBoundConst_pos hδ).le (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have h5 := pow_five_le_pow_ten_add_one hC0
  have hc := one_le_hbReflFactor (T := T) hT
  have hK := hbDualFactor_nonneg T
  have hA : (0 : ℝ) ≤ (divisorBoundConst δ * ((8 * hbLongBlock T : ℕ) : ℝ) ^ δ) ^ 10 := by
    positivity
  have hprod : (divisorBoundConst δ * ((8 * hbLongBlock T : ℕ) : ℝ) ^ δ) ^ 5 * hbReflFactor T ≤
      ((divisorBoundConst δ * ((8 * hbLongBlock T : ℕ) : ℝ) ^ δ) ^ 10 + 1) *
        (hbReflFactor T + hbDualFactor T + 1) :=
    mul_le_mul h5 (by linarith) (by linarith) (by linarith)
  have hpos : (0 : ℝ) ≤
      ((divisorBoundConst δ * ((8 * hbLongBlock T : ℕ) : ℝ) ^ δ) ^ 10 + 1) *
        (hbReflFactor T + hbDualFactor T + 1) := by nlinarith
  rw [hbSmallConst]
  linarith

theorem hbSmallConst_dual_le {T δ : ℝ} (hT : 1 ≤ T) (_hδ : 0 < δ) :
    4 * (divisorBoundConst δ * ((8 * hbLongBlock T : ℕ) : ℝ) ^ δ) ^ 10 * hbDualFactor T ≤
      hbSmallConst T δ / 2 := by
  have hc := one_le_hbReflFactor (T := T) hT
  have hK := hbDualFactor_nonneg T
  have hA : (0 : ℝ) ≤ (divisorBoundConst δ * ((8 * hbLongBlock T : ℕ) : ℝ) ^ δ) ^ 10 := by
    positivity
  have hprod : (divisorBoundConst δ * ((8 * hbLongBlock T : ℕ) : ℝ) ^ δ) ^ 10 * hbDualFactor T ≤
      ((divisorBoundConst δ * ((8 * hbLongBlock T : ℕ) : ℝ) ^ δ) ^ 10 + 1) *
        (hbReflFactor T + hbDualFactor T + 1) :=
    mul_le_mul (by linarith) (by linarith) hK (by linarith)
  have hpos : (0 : ℝ) ≤
      ((divisorBoundConst δ * ((8 * hbLongBlock T : ℕ) : ℝ) ^ δ) ^ 10 + 1) *
        (hbReflFactor T + hbDualFactor T + 1) := by nlinarith
  rw [hbSmallConst]
  linarith

/-! ### The exponent inequality behind Guth–Maynard's case split -/

/-- **The case split at `w = t^{2/3}`.**  For `w, t ≥ 1`,
`t^{2/3} w³ ≤ w^{13/4} t^{1/2} + w^{5/2} t`: if `w ≥ t^{2/3}` the first term wins, if
`w ≤ t^{2/3}` the second does.  This is the inequality that turns the long-block bound into
Heath-Brown's shape, and it is the same dichotomy as in Guth–Maynard's Lemma 11.9. -/
theorem rpow_two_thirds_mul_cube_le {w t : ℝ} (hw : 1 ≤ w) (ht : 1 ≤ t) :
    t ^ ((2 : ℝ) / 3) * w ^ 3 ≤ w ^ ((13 : ℝ) / 4) * t ^ ((1 : ℝ) / 2) + w ^ ((5 : ℝ) / 2) * t := by
  have hw0 : (0 : ℝ) < w := by linarith
  have ht0 : (0 : ℝ) < t := by linarith
  have hw3 : w ^ (3 : ℝ) = w ^ (3 : ℕ) := by
    rw [show ((3 : ℝ)) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rcases le_total (t ^ ((2 : ℝ) / 3)) w with h | h
  · -- `w ≥ t^{2/3}`: raise to the power `1/4`
    have h4 : t ^ ((1 : ℝ) / 6) ≤ w ^ ((1 : ℝ) / 4) := by
      have hr := Real.rpow_le_rpow (Real.rpow_nonneg ht0.le _) h (by norm_num : (0 : ℝ) ≤ 1 / 4)
      rwa [← Real.rpow_mul ht0.le, show ((2 : ℝ) / 3 * (1 / 4)) = 1 / 6 by norm_num] at hr
    have e1 : t ^ ((2 : ℝ) / 3) = t ^ ((1 : ℝ) / 2) * t ^ ((1 : ℝ) / 6) := by
      rw [← Real.rpow_add ht0]; norm_num
    have e2 : w ^ ((13 : ℝ) / 4) = w ^ (3 : ℕ) * w ^ ((1 : ℝ) / 4) := by
      rw [← hw3, ← Real.rpow_add hw0]; norm_num
    have hprod : (0 : ℝ) ≤ t ^ ((1 : ℝ) / 2) * w ^ (3 : ℕ) :=
      mul_nonneg (Real.rpow_nonneg ht0.le _) (by positivity)
    have hmain : t ^ ((2 : ℝ) / 3) * w ^ 3 ≤ w ^ ((13 : ℝ) / 4) * t ^ ((1 : ℝ) / 2) := by
      calc t ^ ((2 : ℝ) / 3) * w ^ 3
          = t ^ ((1 : ℝ) / 2) * w ^ (3 : ℕ) * t ^ ((1 : ℝ) / 6) := by rw [e1]; ring
        _ ≤ t ^ ((1 : ℝ) / 2) * w ^ (3 : ℕ) * w ^ ((1 : ℝ) / 4) :=
            mul_le_mul_of_nonneg_left h4 hprod
        _ = w ^ ((13 : ℝ) / 4) * t ^ ((1 : ℝ) / 2) := by rw [e2]; ring
    have hrest : (0 : ℝ) ≤ w ^ ((5 : ℝ) / 2) * t :=
      mul_nonneg (Real.rpow_nonneg hw0.le _) ht0.le
    linarith
  · -- `w ≤ t^{2/3}`: raise to the power `1/2`
    have h2 : w ^ ((1 : ℝ) / 2) ≤ t ^ ((1 : ℝ) / 3) := by
      have hr := Real.rpow_le_rpow hw0.le h (by norm_num : (0 : ℝ) ≤ 1 / 2)
      rwa [← Real.rpow_mul ht0.le, show ((2 : ℝ) / 3 * (1 / 2)) = 1 / 3 by norm_num] at hr
    have e1 : w ^ (3 : ℕ) = w ^ ((5 : ℝ) / 2) * w ^ ((1 : ℝ) / 2) := by
      rw [← hw3, ← Real.rpow_add hw0]; norm_num
    have hprod : (0 : ℝ) ≤ t ^ ((2 : ℝ) / 3) * w ^ ((5 : ℝ) / 2) :=
      mul_nonneg (Real.rpow_nonneg ht0.le _) (Real.rpow_nonneg hw0.le _)
    have hmain : t ^ ((2 : ℝ) / 3) * w ^ 3 ≤ w ^ ((5 : ℝ) / 2) * t := by
      calc t ^ ((2 : ℝ) / 3) * w ^ 3
          = t ^ ((2 : ℝ) / 3) * w ^ ((5 : ℝ) / 2) * w ^ ((1 : ℝ) / 2) := by rw [e1]; ring
        _ ≤ t ^ ((2 : ℝ) / 3) * w ^ ((5 : ℝ) / 2) * t ^ ((1 : ℝ) / 3) :=
            mul_le_mul_of_nonneg_left h2 hprod
        _ = w ^ ((5 : ℝ) / 2) * (t ^ ((2 : ℝ) / 3) * t ^ ((1 : ℝ) / 3)) := by ring
        _ = w ^ ((5 : ℝ) / 2) * t := by
            rw [← Real.rpow_add ht0, show ((2 : ℝ) / 3 + 1 / 3) = 1 by norm_num, Real.rpow_one]
    have hrest : (0 : ℝ) ≤ w ^ ((13 : ℝ) / 4) * t ^ ((1 : ℝ) / 2) :=
      mul_nonneg (Real.rpow_nonneg hw0.le _) (Real.rpow_nonneg ht0.le _)
    linarith

/-- The scalar inequality behind the short-block bound: the long-block length `n ≤ 4t^{2/3}`
enters only through `t^{2/3}w³`, which the case split bounds by the two Heath-Brown monomials. -/
private theorem smallBlock_arith {w t c K C n X : ℝ} (hw : 1 ≤ w) (ht : 1 ≤ t) (hC : 0 ≤ C)
    (hc : 1 ≤ c) (_hK : 0 ≤ K) (_hn0 : 0 ≤ n) (hn : n ≤ 4 * t ^ ((2 : ℝ) / 3)) (hX1 : 1 ≤ X)
    (hXa : 896 * C ^ 5 * c ≤ X) (hXb : 4 * C ^ 10 * K ≤ X) :
    2 * C ^ 5 * w ^ 2 * (112 * n * w * c + K * (2 * C ^ 5 * w ^ 2)) ≤
      (X * (w ^ 2 + w ^ ((5 : ℝ) / 4) * t ^ ((1 : ℝ) / 2))) ^ 2 := by
  have hw0 : (0 : ℝ) < w := by linarith
  have ht0 : (0 : ℝ) < t := by linarith
  have hc0 : (0 : ℝ) ≤ c := by linarith
  have hC5 : (0 : ℝ) ≤ C ^ 5 := by positivity
  have hC10 : (0 : ℝ) ≤ C ^ 10 := by positivity
  have hw2 : (0 : ℝ) ≤ w ^ 2 := by positivity
  have hw3 : (0 : ℝ) ≤ w ^ 3 := by positivity
  have hw4 : (0 : ℝ) ≤ w ^ 4 := by positivity
  obtain ⟨u, hudef⟩ : ∃ u : ℝ, u = w ^ ((5 : ℝ) / 4) * t ^ ((1 : ℝ) / 2) := ⟨_, rfl⟩
  have hu0 : (0 : ℝ) ≤ u := by
    rw [hudef]; exact mul_nonneg (Real.rpow_nonneg hw0.le _) (Real.rpow_nonneg ht0.le _)
  have hwu : (0 : ℝ) ≤ w ^ 2 * u := mul_nonneg hw2 hu0
  have hu2 : (0 : ℝ) ≤ u ^ 2 := sq_nonneg u
  -- the two monomials of the expanded square
  have e1 : w ^ 2 * u = w ^ ((13 : ℝ) / 4) * t ^ ((1 : ℝ) / 2) := by
    rw [hudef, show (w ^ 2 : ℝ) = w ^ (2 : ℝ) by
        rw [show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast],
      ← mul_assoc, ← Real.rpow_add hw0]
    norm_num
  have e2 : u ^ 2 = w ^ ((5 : ℝ) / 2) * t := by
    rw [hudef, mul_pow, ← Real.rpow_natCast (w ^ ((5 : ℝ) / 4)) 2, ← Real.rpow_mul hw0.le,
      ← Real.rpow_natCast (t ^ ((1 : ℝ) / 2)) 2, ← Real.rpow_mul ht0.le]
    norm_num
  have harith : t ^ ((2 : ℝ) / 3) * w ^ 3 ≤ w ^ 2 * u + u ^ 2 := by
    rw [e1, e2]; exact rpow_two_thirds_mul_cube_le hw ht
  -- the left-hand side
  have hfac : (0 : ℝ) ≤ 224 * (C ^ 5 * (c * w ^ 3)) :=
    mul_nonneg (by norm_num) (mul_nonneg hC5 (mul_nonneg hc0 hw3))
  have hfac2 : (0 : ℝ) ≤ 896 * C ^ 5 * c := mul_nonneg (mul_nonneg (by norm_num) hC5) hc0
  have h1 : 2 * C ^ 5 * w ^ 2 * (112 * n * w * c) ≤
      896 * C ^ 5 * c * (w ^ 2 * u) + 896 * C ^ 5 * c * u ^ 2 := by
    calc 2 * C ^ 5 * w ^ 2 * (112 * n * w * c) = 224 * (C ^ 5 * (c * w ^ 3)) * n := by ring
      _ ≤ 224 * (C ^ 5 * (c * w ^ 3)) * (4 * t ^ ((2 : ℝ) / 3)) :=
          mul_le_mul_of_nonneg_left hn hfac
      _ = 896 * C ^ 5 * c * (t ^ ((2 : ℝ) / 3) * w ^ 3) := by ring
      _ ≤ 896 * C ^ 5 * c * (w ^ 2 * u + u ^ 2) := mul_le_mul_of_nonneg_left harith hfac2
      _ = 896 * C ^ 5 * c * (w ^ 2 * u) + 896 * C ^ 5 * c * u ^ 2 := by ring
  have h3 : 2 * C ^ 5 * w ^ 2 * (K * (2 * C ^ 5 * w ^ 2)) = 4 * C ^ 10 * K * w ^ 4 := by ring
  -- the right-hand side dominates both monomials
  have hX2 : X ≤ X ^ 2 := by nlinarith
  have hXa2 : 896 * C ^ 5 * c ≤ X ^ 2 := hXa.trans hX2
  have hXb2 : 4 * C ^ 10 * K ≤ X ^ 2 := hXb.trans hX2
  have k1 : 896 * C ^ 5 * c * (w ^ 2 * u) ≤ X ^ 2 * (w ^ 2 * u) :=
    mul_le_mul_of_nonneg_right hXa2 hwu
  have k2 : 896 * C ^ 5 * c * u ^ 2 ≤ X ^ 2 * u ^ 2 :=
    mul_le_mul_of_nonneg_right hXa2 hu2
  have k3 : 4 * C ^ 10 * K * w ^ 4 ≤ X ^ 2 * w ^ 4 :=
    mul_le_mul_of_nonneg_right hXb2 hw4
  have k4 : (0 : ℝ) ≤ X ^ 2 * (w ^ 2 * u) := mul_nonneg (sq_nonneg X) hwu
  have hexp : (X * (w ^ 2 + u)) ^ 2 =
      X ^ 2 * w ^ 4 + 2 * (X ^ 2 * (w ^ 2 * u)) + X ^ 2 * u ^ 2 := by ring
  have hgoal : 2 * C ^ 5 * w ^ 2 * (112 * n * w * c + K * (2 * C ^ 5 * w ^ 2)) =
      2 * C ^ 5 * w ^ 2 * (112 * n * w * c) + 4 * C ^ 10 * K * w ^ 4 := by
    rw [← h3]; ring
  rw [← hudef, hgoal, hexp]
  linarith

/-! ### The long-block bound at height `T` -/

/-- **The long-block bound in terms of the height.**  Mirror of `hbPairSum_Ioc_le_of_twoThirds`
for the amplitude `𝒜_{1/2}((N, 8N])` itself. -/
theorem hbAmp_half_Ioc_eight_le_of_diam {W : Finset ℝ} (hW : GuthMaynard.IsSeparated 1 W)
    {T : ℝ} (hT : 1 ≤ T) (hdiam : ∀ t ∈ W, ∀ t' ∈ W, |t - t'| ≤ T) {N : ℕ} (hN : 1 ≤ N)
    (hN2 : 2 * T < (N : ℝ) ^ 2) (hN3 : 4 * T ^ 2 ≤ 9 * (N : ℝ) ^ 3) {δ : ℝ} (hδ : 0 < δ) :
    hbAmp W (1 / 2) (Finset.Ioc N (8 * N)) ≤
      112 * N * W.card * hbReflFactor T +
        hbDualFactor T *
          (2 * (divisorBoundConst δ * ((8 * N : ℕ) : ℝ) ^ δ) ^ 5 * (W.card : ℝ) ^ 2) := by
  obtain ⟨k, hk1, hk2⟩ := GaloisForLFunctions.Nevanlinna.exists_dyadic_band hT
  have hpow : (2 : ℝ) ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ]; ring
  have hJN : (2 : ℝ) ^ (k + 1) < (N : ℝ) ^ 2 := by rw [hpow]; linarith
  have hJN3 : (4 : ℝ) ^ (k + 1) ≤ 9 * (N : ℝ) ^ 3 := by
    have h4 : (4 : ℝ) ^ (k + 1) = ((2 : ℝ) ^ (k + 1)) ^ 2 := by
      rw [← pow_mul, mul_comm, pow_mul]; norm_num
    have hk0 : (0 : ℝ) ≤ 2 ^ k := by positivity
    rw [h4, hpow]
    nlinarith
  have hdiam' : ∀ t ∈ W, ∀ t' ∈ W, |t - t'| ≤ (2 : ℝ) ^ (k + 1) := fun t ht t' ht' =>
    (hdiam t ht t' ht').trans hk2.le
  have hmain := hbAmp_half_Ioc_eight_le_restricted hW (J := k + 1) (by omega) hN hdiam' hJN hJN3 hδ
  have hkL : ((k + 1 : ℕ) : ℝ) ≤ 1 + Real.logb 2 T := by
    have hlog : (k : ℝ) ≤ Real.logb 2 T := by
      have h := Real.logb_le_logb_of_le (b := 2) (by norm_num) (by positivity) hk1
      rwa [Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one] at h
    push_cast
    linarith
  have hk0 : (0 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hL0 : 0 ≤ 1 + Real.logb 2 T := hk0.trans hkL
  have hC0 : 0 ≤ divisorBoundConst δ := (divisorBoundConst_pos hδ).le
  refine hmain.trans ?_
  rw [hbReflFactor, hbDualFactor]
  gcongr

/-! ### The short-block theorem -/

/-- **Heath-Brown's theorem for short blocks** (Guth–Maynard, Theorem 1.6, in the range where
the short block reflects into the proven long range).  For `W` `1`-separated of diameter at most
`T ≥ 1`, every `M ≥ 1` with `M² ≤ (2T)^{2/3}`, every `δ > 0` and `|a_n| ≤ 1`:

`Σ_{t₁,t₂∈W} |Σ_{M<n≤2M} a_n n^{i(t₁−t₂)}|² ≤ C(T,δ) (|W|²M + |W|M² + |W|^{5/4}T^{1/2}M)`.

In particular this covers every `M ≤ T^{1/4}`, the range used by Guth–Maynard's Lemma 11.9. -/
theorem hbPairSum_Ioc_le_smallBlock {W : Finset ℝ} (hW : GuthMaynard.IsSeparated 1 W)
    {T : ℝ} (hT : 1 ≤ T) (hdiam : ∀ t ∈ W, ∀ t' ∈ W, |t - t'| ≤ T) {M : ℕ} (hM : 1 ≤ M)
    (hMT : (M : ℝ) ^ 2 ≤ (2 * T) ^ ((2 : ℝ) / 3)) {δ : ℝ} (hδ : 0 < δ)
    {a : ℕ → ℂ} (ha : ∀ n ∈ Finset.Ioc M (2 * M), ‖a n‖ ≤ 1) :
    hbPairSum W (Finset.Ioc M (2 * M)) a ≤ hbSmallConst T δ *
      ((W.card : ℝ) ^ 2 * M + (W.card : ℝ) * (M : ℝ) ^ 2
        + (W.card : ℝ) ^ ((5 : ℝ) / 4) * T ^ ((1 : ℝ) / 2) * M) := by
  classical
  have hCsmall : 0 ≤ hbSmallConst T δ := le_trans zero_le_one (one_le_hbSmallConst hT hδ)
  have hT0 : (0 : ℝ) ≤ T := by linarith
  rcases Nat.eq_zero_or_pos W.card with hw0 | hwpos
  · -- an empty point set
    have hWe : W = ∅ := Finset.card_eq_zero.mp hw0
    have hzero : hbPairSum W (Finset.Ioc M (2 * M)) a = 0 := by
      rw [hbPairSum, hWe]; simp
    rw [hzero]
    exact mul_nonneg hCsmall (by positivity)
  · have hw1 : (1 : ℝ) ≤ (W.card : ℝ) := by exact_mod_cast hwpos
    obtain ⟨N, hNdef⟩ : ∃ N : ℕ, N = hbLongBlock T := ⟨_, rfl⟩
    have hN1 : 1 ≤ N := hNdef ▸ one_le_hbLongBlock hT
    have hMN : M ^ 2 ≤ N := by
      have h1 : ((M : ℝ)) ^ 2 ≤ (N : ℝ) := hMT.trans (hNdef ▸ le_hbLongBlock T)
      have h2 : ((M ^ 2 : ℕ) : ℝ) ≤ (N : ℝ) := by push_cast; exact h1
      exact_mod_cast h2
    have hN2 : 2 * T < (N : ℝ) ^ 2 := hNdef ▸ two_mul_lt_hbLongBlock_sq hT
    have hN3 : 4 * T ^ 2 ≤ 9 * (N : ℝ) ^ 3 := hNdef ▸ four_mul_sq_le_hbLongBlock_cube hT
    have hNle : (N : ℝ) ≤ 4 * T ^ ((2 : ℝ) / 3) := hNdef ▸ hbLongBlock_le_rpow hT
    -- Corollary 2.1 onto the long block, then the long-block bound
    have hstep1 := hbAmp_sq_le_rpow W hδ (by omega : 0 < M) hMN
      (subset_rfl (a := Finset.Ioc M (2 * M)))
    have hstep2 := hbAmp_half_Ioc_eight_le_of_diam hW hT hdiam hN1 hN2 hN3 hδ
    have hC₁0 : 0 ≤ divisorBoundConst δ * ((8 * N : ℕ) : ℝ) ^ δ :=
      mul_nonneg (divisorBoundConst_pos hδ).le (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    have hP0 : (0 : ℝ) ≤ 2 * (divisorBoundConst δ * ((8 * N : ℕ) : ℝ) ^ δ) ^ 5 *
        (W.card : ℝ) ^ 2 := by positivity
    have hsq := hstep1.trans (mul_le_mul_of_nonneg_left hstep2 hP0)
    -- solve the quadratic
    have hG : hbAmp W (1 / 2) (Finset.Ioc M (2 * M)) ≤
        (hbSmallConst T δ / 2) *
          ((W.card : ℝ) ^ 2 + (W.card : ℝ) ^ ((5 : ℝ) / 4) * T ^ ((1 : ℝ) / 2)) := by
      have hA0 : 0 ≤ hbAmp W (1 / 2) (Finset.Ioc M (2 * M)) := hbAmp_nonneg W _ _
      have hG0 : (0 : ℝ) ≤ (hbSmallConst T δ / 2) *
          ((W.card : ℝ) ^ 2 + (W.card : ℝ) ^ ((5 : ℝ) / 4) * T ^ ((1 : ℝ) / 2)) := by
        have : (0 : ℝ) ≤ (W.card : ℝ) ^ ((5 : ℝ) / 4) * T ^ ((1 : ℝ) / 2) := by positivity
        have h2 : (0 : ℝ) ≤ hbSmallConst T δ / 2 := by linarith
        nlinarith [sq_nonneg ((W.card : ℝ))]
      refine (pow_le_pow_iff_left₀ hA0 hG0 (two_ne_zero)).mp (hsq.trans ?_)
      -- the scalar inequality
      have hc1 := one_le_hbReflFactor hT
      have hK0 := hbDualFactor_nonneg T
      have hX1 : (1 : ℝ) ≤ hbSmallConst T δ / 2 := one_le_hbSmallConst_div_two hT hδ
      have hXa : 896 * (divisorBoundConst δ * ((8 * N : ℕ) : ℝ) ^ δ) ^ 5 * hbReflFactor T ≤
          hbSmallConst T δ / 2 := by
        have h := hbSmallConst_refl_le (T := T) (δ := δ) hT hδ
        rw [← hNdef] at h
        exact h
      have hXb : 4 * (divisorBoundConst δ * ((8 * N : ℕ) : ℝ) ^ δ) ^ 10 * hbDualFactor T ≤
          hbSmallConst T δ / 2 := by
        have h := hbSmallConst_dual_le (T := T) (δ := δ) hT hδ
        rw [← hNdef] at h
        exact h
      exact smallBlock_arith hw1 hT hC₁0 hc1 hK0 (Nat.cast_nonneg N) hNle hX1 hXa hXb
    calc hbPairSum W (Finset.Ioc M (2 * M)) a
        ≤ 2 * M * hbAmp W (1 / 2) (Finset.Ioc M (2 * M)) :=
          hbPairSum_le_two_mul_hbAmp_half W ha
      _ ≤ 2 * M * ((hbSmallConst T δ / 2) *
            ((W.card : ℝ) ^ 2 + (W.card : ℝ) ^ ((5 : ℝ) / 4) * T ^ ((1 : ℝ) / 2))) := by
          have : (0 : ℝ) ≤ 2 * M := by positivity
          exact mul_le_mul_of_nonneg_left hG this
      _ = hbSmallConst T δ * ((W.card : ℝ) ^ 2 * M
            + (W.card : ℝ) ^ ((5 : ℝ) / 4) * T ^ ((1 : ℝ) / 2) * M) := by ring
      _ ≤ hbSmallConst T δ * ((W.card : ℝ) ^ 2 * M + (W.card : ℝ) * (M : ℝ) ^ 2
            + (W.card : ℝ) ^ ((5 : ℝ) / 4) * T ^ ((1 : ℝ) / 2) * M) := by
          have hmid : (0 : ℝ) ≤ (W.card : ℝ) * (M : ℝ) ^ 2 := by positivity
          nlinarith

/-- **The hypothesis in the form used by Guth–Maynard's Lemma 11.9.**  `M ≤ T^{1/4}` implies
`M² ≤ (2T)^{2/3}`; in Lemma 11.9 the blocks have length `M = N/d ≤ T/N ≤ T^{1/4}`. -/
theorem sq_le_rpow_two_thirds_of_le_rpow_quarter {T : ℝ} (hT : 1 ≤ T) {M : ℕ}
    (hM : (M : ℝ) ≤ T ^ ((1 : ℝ) / 4)) : (M : ℝ) ^ 2 ≤ (2 * T) ^ ((2 : ℝ) / 3) := by
  have hT0 : (0 : ℝ) ≤ T := by linarith
  have h1 : (M : ℝ) ^ 2 ≤ (T ^ ((1 : ℝ) / 4)) ^ 2 :=
    pow_le_pow_left₀ (Nat.cast_nonneg _) hM 2
  have h2 : (T ^ ((1 : ℝ) / 4)) ^ 2 = T ^ ((1 : ℝ) / 2) := by
    rw [← Real.rpow_natCast (T ^ ((1 : ℝ) / 4)) 2, ← Real.rpow_mul hT0]
    norm_num
  have h3 : T ^ ((1 : ℝ) / 2) ≤ T ^ ((2 : ℝ) / 3) :=
    Real.rpow_le_rpow_of_exponent_le hT (by norm_num)
  have h4 : T ^ ((2 : ℝ) / 3) ≤ (2 * T) ^ ((2 : ℝ) / 3) :=
    Real.rpow_le_rpow hT0 (by linarith) (by norm_num)
  linarith [h1, h2 ▸ h1]

/-- **Heath-Brown's theorem for `M ≤ T^{1/4}`.**  The form in which Guth–Maynard's Lemma 11.9
applies Lemmas 11.5 and 11.6. -/
theorem hbPairSum_Ioc_le_of_le_rpow_quarter {W : Finset ℝ} (hW : GuthMaynard.IsSeparated 1 W)
    {T : ℝ} (hT : 1 ≤ T) (hdiam : ∀ t ∈ W, ∀ t' ∈ W, |t - t'| ≤ T) {M : ℕ} (hM : 1 ≤ M)
    (hMT : (M : ℝ) ≤ T ^ ((1 : ℝ) / 4)) {δ : ℝ} (hδ : 0 < δ)
    {a : ℕ → ℂ} (ha : ∀ n ∈ Finset.Ioc M (2 * M), ‖a n‖ ≤ 1) :
    hbPairSum W (Finset.Ioc M (2 * M)) a ≤ hbSmallConst T δ *
      ((W.card : ℝ) ^ 2 * M + (W.card : ℝ) * (M : ℝ) ^ 2
        + (W.card : ℝ) ^ ((5 : ℝ) / 4) * T ^ ((1 : ℝ) / 2) * M) :=
  hbPairSum_Ioc_le_smallBlock hW hT hdiam hM (sq_le_rpow_two_thirds_of_le_rpow_quarter hT hMT) hδ ha

/-! ### The interface with the Section 11 phase convention -/

/-- The phase of `hbPoly` in the `lagSum` convention `n^{iu} = exp(i u log n)`. -/
theorem hbPhase_eq_exp_I_mul (n : ℕ) (u : ℝ) :
    hbPhase n u = Complex.exp (Complex.I * (u : ℂ) * (Real.log n : ℂ)) := by
  rw [hbPhase]
  congr 1
  push_cast
  ring

/-- **The pair sum in the Section 11 convention.** -/
theorem hbPairSum_eq_sum_exp (W : Finset ℝ) (S : Finset ℕ) (a : ℕ → ℂ) :
    hbPairSum W S a = ∑ t₁ ∈ W, ∑ t₂ ∈ W,
      ‖∑ n ∈ S, a n * Complex.exp (Complex.I * ((t₁ : ℂ) - (t₂ : ℂ)) * (Real.log n : ℂ))‖ ^ 2 := by
  refine Finset.sum_congr rfl fun t₁ _ => Finset.sum_congr rfl fun t₂ _ => ?_
  rw [hbPoly]
  congr 2
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [hbPhase_eq_exp_I_mul]
  push_cast
  ring_nf

/-- **Heath-Brown's theorem for short blocks, in the Section 11 phase convention.**  This is the
`N ≤ (2T)^{1/3}` case of the datum `HeathBrownPairSumBound`, with an explicit constant. -/
theorem sum_sum_norm_sq_exp_le_smallBlock {W : Finset ℝ} (hW : GuthMaynard.IsSeparated 1 W)
    {T : ℝ} (hT : 1 ≤ T) (hdiam : ∀ t ∈ W, ∀ t' ∈ W, |t - t'| ≤ T) {M : ℕ} (hM : 1 ≤ M)
    (hMT : (M : ℝ) ^ 2 ≤ (2 * T) ^ ((2 : ℝ) / 3)) {δ : ℝ} (hδ : 0 < δ)
    {a : ℕ → ℂ} (ha : ∀ n ∈ Finset.Ioc M (2 * M), ‖a n‖ ≤ 1) :
    ∑ t₁ ∈ W, ∑ t₂ ∈ W, ‖∑ n ∈ Finset.Ioc M (2 * M),
        a n * Complex.exp (Complex.I * ((t₁ : ℂ) - (t₂ : ℂ)) * (Real.log n : ℂ))‖ ^ 2 ≤
      hbSmallConst T δ * ((W.card : ℝ) ^ 2 * M + (W.card : ℝ) * (M : ℝ) ^ 2
        + (W.card : ℝ) ^ ((5 : ℝ) / 4) * T ^ ((1 : ℝ) / 2) * M) := by
  rw [← hbPairSum_eq_sum_exp]
  exact hbPairSum_Ioc_le_smallBlock hW hT hdiam hM hMT hδ ha

end

end RHTower.Sieve
