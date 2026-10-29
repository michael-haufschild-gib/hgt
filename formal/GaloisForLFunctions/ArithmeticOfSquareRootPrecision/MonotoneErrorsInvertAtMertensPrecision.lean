import GaloisForLFunctions.ArithmeticOfSquareRootPrecision.WherePrecisionIsLost
import GaloisForLFunctions.RHTower.MobiusMertensLittlewood
import GaloisForLFunctions.RHTower.MertensSquareRootOmega

/-!
# Monotone errors invert at Mertens precision

The inversion operator `I_x(E) = Σ_{k ≤ x} μ(k) E(x/k)` computes the count from the Chebyshev
identity, and it is unbounded on every size class of errors (`not_inversion_bounded`): the
amplifying errors are maximally oscillating. This module is the positive survivor of that no-go.

* **Abel summation** (`sum_moebius_mul_eq`):
  `Σ_{k ≤ N} μ(k) f(k) = M(N) f(N + 1) + Σ_{k ≤ N} M(k) (f(k) − f(k + 1))`, `M` the Mertens function.
* **The monotone inversion law** (`abs_inversionOp_le_of_monotoneOn`): if `E` is monotone on
  `(0, ∞)` and `|E| ≤ B` on `(0, x]`, and `|M(k)| ≤ K` for `k ≤ x`, then `|I_x(E)| ≤ 3 B K`.
* **Sharpness** (`inversionOp_const`, `not_monotone_inversion_lt_half`): constant errors invert to
  the Mertens function itself, which is `Ω±(√x)`; no exponent below `½` is possible.
* **The inversion face of RH** (`riemannHypothesis_iff_monotone_inversion`): RH holds iff for every
  `δ > 0` monotone errors bounded by `1` are inverted to `O(x^{½ + δ})`.

So inversion with arithmetic input has exactly the precision of the Mertens function: square-root
precision on monotone errors is RH, and no precision on oscillating ones.
-/

noncomputable section

open Real Finset Filter
open ArithmeticFunction (moebius)

namespace GaloisForLFunctions.ArithmeticOfSquareRootPrecision

/-- The **Mertens function** `M(N) = Σ_{k ≤ N} μ(k)`. -/
def mertens (N : ℕ) : ℝ := ∑ k ∈ Ioc 0 N, (moebius k : ℝ)

theorem mertens_succ (N : ℕ) : mertens (N + 1) = mertens N + moebius (N + 1) := by
  unfold mertens; rw [sum_Ioc_succ_top (Nat.zero_le N)]

theorem mertens_eq_mobiusMertensPartialSum (N : ℕ) :
    ((mertens N : ℝ) : ℂ) = RHTower.mobiusMertensPartialSum N := by
  unfold mertens RHTower.mobiusMertensPartialSum RHTower.mobiusComplexCoefficient
  rw [range_eq_Ico, sum_eq_sum_Ico_succ_bot (Nat.succ_pos N)]
  simp only [ArithmeticFunction.map_zero, Int.cast_zero, zero_add]
  rfl

theorem mertens_eq_mertensFunctionReal (x : ℝ) :
    mertens ⌊x⌋₊ = RHTower.mertensFunctionReal x := by
  unfold mertens RHTower.mertensFunctionReal
  push_cast
  rfl

/-- **Abel summation against `μ`.** -/
theorem sum_moebius_mul_eq (f : ℕ → ℝ) (N : ℕ) :
    ∑ k ∈ Ioc 0 N, (moebius k : ℝ) * f k =
      mertens N * f (N + 1) + ∑ k ∈ Ioc 0 N, mertens k * (f k - f (k + 1)) := by
  induction N with
  | zero => simp [mertens]
  | succ N ih =>
    rw [sum_Ioc_succ_top (Nat.zero_le N), ih, sum_Ioc_succ_top (Nat.zero_le N), mertens_succ]
    ring

/-- The variation telescopes: `Σ_{k ≤ N} (f k − f (k + 1)) = f 1 − f (N + 1)`. -/
theorem sum_Ioc_sub_succ (f : ℕ → ℝ) (N : ℕ) :
    ∑ k ∈ Ioc 0 N, (f k - f (k + 1)) = f 1 - f (N + 1) := by
  induction N with
  | zero => simp
  | succ N ih => rw [sum_Ioc_succ_top (Nat.zero_le N), ih]; ring

/-- **Abel bound**: for `f` antitone on `[1, N + 1]` with `|f| ≤ B` there, and `|M(k)| ≤ K` for
`k ≤ N`, the twisted sum is at most `3 B K`. -/
theorem abs_sum_moebius_mul_le_of_antitone {f : ℕ → ℝ} {N : ℕ} {B K : ℝ}
    (hanti : ∀ k, 1 ≤ k → k ≤ N → f (k + 1) ≤ f k) (hB : ∀ k, 1 ≤ k → k ≤ N + 1 → |f k| ≤ B)
    (hK : ∀ k, k ≤ N → |mertens k| ≤ K) :
    |∑ k ∈ Ioc 0 N, (moebius k : ℝ) * f k| ≤ 3 * B * K := by
  have hK0 : 0 ≤ K := (abs_nonneg _).trans (hK 0 (Nat.zero_le _))
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB (N + 1) (by omega) le_rfl)
  rw [sum_moebius_mul_eq]
  have htel := sum_Ioc_sub_succ f N
  have hvar : |∑ k ∈ Ioc 0 N, mertens k * (f k - f (k + 1))| ≤ K * (f 1 - f (N + 1)) := by
    calc |∑ k ∈ Ioc 0 N, mertens k * (f k - f (k + 1))|
        ≤ ∑ k ∈ Ioc 0 N, |mertens k * (f k - f (k + 1))| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ k ∈ Ioc 0 N, K * (f k - f (k + 1)) := sum_le_sum fun k hk => by
          obtain ⟨h1, h2⟩ := mem_Ioc.mp hk
          rw [abs_mul, abs_of_nonneg (sub_nonneg.mpr (hanti k h1 h2))]
          exact mul_le_mul_of_nonneg_right (hK k h2) (sub_nonneg.mpr (hanti k h1 h2))
      _ = K * (f 1 - f (N + 1)) := by rw [← mul_sum, htel]
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp [mertens]; positivity
  have h1 := abs_le.mp (hB 1 le_rfl (by omega))
  have hN1 := abs_le.mp (hB (N + 1) (by omega) le_rfl)
  have hMN := hK N le_rfl
  calc |mertens N * f (N + 1) + ∑ k ∈ Ioc 0 N, mertens k * (f k - f (k + 1))|
      ≤ |mertens N * f (N + 1)| + |∑ k ∈ Ioc 0 N, mertens k * (f k - f (k + 1))| := abs_add_le _ _
    _ ≤ K * B + K * (f 1 - f (N + 1)) := by
        rw [abs_mul]
        exact add_le_add (mul_le_mul hMN (hB (N + 1) (by omega) le_rfl) (abs_nonneg _) hK0) hvar
    _ ≤ 3 * B * K := by nlinarith

/-- **The monotone inversion law.** If `E` is monotone on `(0, ∞)`, `|E| ≤ B` on `(0, x]`, and
`|M(k)| ≤ K` for `k ≤ x`, then `|I_x(E)| ≤ 3 B K`. -/
theorem abs_inversionOp_le_of_monotoneOn {E : ℝ → ℝ} (hE : MonotoneOn E (Set.Ioi 0)) {x B K : ℝ}
    (hx : 0 < x) (hB : ∀ y, 0 < y → y ≤ x → |E y| ≤ B)
    (hK : ∀ k : ℕ, k ≤ ⌊x⌋₊ → |mertens k| ≤ K) : |inversionOp E x| ≤ 3 * B * K := by
  unfold inversionOp
  refine abs_sum_moebius_mul_le_of_antitone (f := fun k => E (x / k)) (fun k h1 _ => ?_)
    (fun k h1 _ => ?_) hK
  · have hk : (0 : ℝ) < k := by exact_mod_cast h1
    exact hE (by simp only [Set.mem_Ioi]; positivity) (by simp only [Set.mem_Ioi]; positivity)
      (div_le_div_of_nonneg_left hx.le hk (by push_cast; linarith))
  · have hk : (1 : ℝ) ≤ k := by exact_mod_cast h1
    exact hB _ (by positivity) (div_le_self hx.le hk)

/-- **Constant errors invert to the Mertens function.** -/
theorem inversionOp_const (x : ℝ) : inversionOp (fun _ => 1) x = mertens ⌊x⌋₊ := by
  simp [inversionOp, mertens]

/-- **Sharpness**: no exponent below `½` bounds the inversion of monotone errors, since constant
errors invert to `M(x) = Ω±(√x)`. -/
theorem not_monotone_inversion_lt_half {θ : ℝ} (hθ : θ < 1 / 2) :
    ¬ ∃ C : ℝ, ∀ x : ℝ, 1 ≤ x → ∀ E : ℝ → ℝ, MonotoneOn E (Set.Ioi 0) →
      (∀ y, 0 < y → y ≤ x → |E y| ≤ 1) → |inversionOp E x| ≤ C * x ^ θ := by
  rintro ⟨C, hC⟩
  obtain ⟨c, hc, hfreq, -⟩ := RHTower.mertens_omega_pm_sqrt
  have hsmall := ((rpow_isLittleO_rpow (r := θ) (s := 1 / 2) hθ).const_mul_left C).def
    (c := c / 2) (by positivity)
  obtain ⟨x, ⟨h1, hx1⟩, h2⟩ := ((hsmall.and (eventually_ge_atTop (1 : ℝ))).and_frequently hfreq).exists
  have hx0 : 0 < x := by linarith
  have hb := hC x hx1 (fun _ => 1) (fun _ _ _ _ _ => le_rfl) (fun _ _ _ => by norm_num)
  rw [inversionOp_const, mertens_eq_mertensFunctionReal] at hb
  rw [Real.norm_eq_abs, Real.norm_of_nonneg (Real.rpow_nonneg hx0.le _), ← Real.sqrt_eq_rpow] at h1
  have hs : 0 < √x := Real.sqrt_pos.mpr hx0
  have hcs := mul_pos hc hs
  linarith [le_abs_self (RHTower.mertensFunctionReal x), le_abs_self (C * x ^ θ)]

/-- **The inversion face of RH.** RH holds iff for every `δ > 0` there is `C` with
`|I_x(E)| ≤ C x^{½ + δ}` for all `x ≥ 1` and all monotone `E` with `|E| ≤ 1` on `(0, x]`. -/
theorem riemannHypothesis_iff_monotone_inversion :
    RiemannHypothesis ↔ ∀ δ : ℝ, 0 < δ → ∃ C : ℝ, ∀ x : ℝ, 1 ≤ x → ∀ E : ℝ → ℝ,
      MonotoneOn E (Set.Ioi 0) → (∀ y, 0 < y → y ≤ x → |E y| ≤ 1) →
        |inversionOp E x| ≤ C * x ^ (1 / 2 + δ) := by
  constructor
  · intro hRH δ hδ
    obtain ⟨C, hC0, hC⟩ := RHTower.riemannHypothesis_implies_mobiusMertensAllStrictHalfPowerBound
      hRH δ hδ
    refine ⟨3 * (C * 2 ^ (1 / 2 + δ)), fun x hx E hE hB => ?_⟩
    have hx0 : 0 < x := by linarith
    have hK : ∀ k : ℕ, k ≤ ⌊x⌋₊ → |mertens k| ≤ C * 2 ^ (1 / 2 + δ) * x ^ (1 / 2 + δ) := by
      intro k hk
      have h := hC k
      rw [← mertens_eq_mobiusMertensPartialSum, Complex.norm_real, Real.norm_eq_abs] at h
      have hkx : (k : ℝ) + 1 ≤ 2 * x := by
        have := (Nat.cast_le.mpr hk).trans (Nat.floor_le hx0.le); linarith
      calc |mertens k| ≤ C * ((k : ℝ) + 1) ^ (1 / 2 + δ) := h
        _ ≤ C * (2 * x) ^ (1 / 2 + δ) :=
            mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) hkx (by linarith)) hC0
        _ = C * 2 ^ (1 / 2 + δ) * x ^ (1 / 2 + δ) := by
            rw [Real.mul_rpow (by norm_num) hx0.le]; ring
    have := abs_inversionOp_le_of_monotoneOn hE hx0 hB hK
    linarith
  · intro h
    refine RHTower.mobiusMertensAllStrictHalfPowerBound_implies_riemannHypothesis fun δ hδ => ?_
    obtain ⟨C, hC⟩ := h δ hδ
    refine ⟨max C 0, le_max_right _ _, fun N => ?_⟩
    rw [← mertens_eq_mobiusMertensPartialSum, Complex.norm_real, Real.norm_eq_abs]
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · simp only [mertens, Finset.Ioc_self, sum_empty, abs_zero]; positivity
    have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have hb := hC N hN1 (fun _ => 1) (fun _ _ _ _ _ => le_rfl) (fun _ _ _ => by norm_num)
    rw [inversionOp_const, Nat.floor_natCast] at hb
    calc |mertens N| ≤ C * (N : ℝ) ^ (1 / 2 + δ) := hb
      _ ≤ max C 0 * (N : ℝ) ^ (1 / 2 + δ) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
      _ ≤ max C 0 * ((N : ℝ) + 1) ^ (1 / 2 + δ) :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) (by linarith)
            (by linarith)) (le_max_right _ _)

end GaloisForLFunctions.ArithmeticOfSquareRootPrecision
