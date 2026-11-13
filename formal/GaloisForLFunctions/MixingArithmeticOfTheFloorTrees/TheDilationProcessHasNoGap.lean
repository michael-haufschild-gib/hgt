import GaloisForLFunctions.HTGeometry.DirichletSimultaneousApproximation
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# The dilation process has no gap

At infinite block size the floor tree of `k` is the dilation `x ↦ x/k` on `(1, Q]`. The
**dilation process** moves from `x` to `kx` at the rate `Λ(k)` and from `y` to `y/k` at the rate
`Λ(k)/k`; it is reversible for `dx`. In the coordinate `u = log x` its Dirichlet form is

  `E(f) = Σ_{2 ≤ k ≤ Q} Λ(k) ∫_0^{log(Q/k)} (f(u) − f(u + log k))² e^u du`

(`dilationForm`) with the variance `Var(f)` for `e^u du` on `[0, log Q]` (`dilationVar`).

  **For every `Q` the dilation process on `(1, Q]` has no spectral gap**
  (`dilationForm_le_of_no_gap`): for every `ε > 0` and every frequency bound `T` there is `t ≥ T`
  with `E(cos(t ·)) ≤ ε Var(cos(t ·))`.

Mechanism: the rotations `t ↦ t log k`, `k ≤ Q`, return together close to `2πℤ` (Dirichlet's
simultaneous approximation), and at a return the wave `cos(t log x)` is moved by no floor map. Its
variance stays a quarter of the mass, since `∫ cos(su) e^u du = O(e^L/|s|)`. The returns are the
frequencies at which the Dirichlet polynomial `Σ_{k ≤ Q} Λ(k) k^{it}` is close to its maximum
`ψ(Q)`: there the floor trees do not mix at all, and the gap of the Doob chain of a long window
must come from its jets. Below ratio `9/2` the same failure is exact at finite block size: the
trees split into components (`TheFloorTreesAloneDoNotConnectAWindowOfRatioBelowNineHalves`).
-/

open Finset Real MeasureTheory intervalIntegral
open scoped ArithmeticFunction.vonMangoldt

noncomputable section

namespace GaloisForLFunctions.MixingArithmeticOfTheFloorTrees

/-- **The Dirichlet form of the dilation process on `(1, Q]`**, in the coordinate `u = log x`: the
pairs `(x, kx)` with `1 < x`, `kx ≤ Q`, with the weight `Λ(k)`. -/
def dilationForm (Q : ℕ) (f : ℝ → ℝ) : ℝ :=
  ∑ k ∈ Icc 2 Q, Λ k * ∫ u in (0 : ℝ)..Real.log ((Q : ℝ) / k),
    (f u - f (u + Real.log k)) ^ 2 * Real.exp u

/-- The variance for the stationary measure `e^u du` on `[0, log Q]`, of total mass `Q − 1`. -/
def dilationVar (Q : ℕ) (f : ℝ → ℝ) : ℝ :=
  (∫ u in (0 : ℝ)..Real.log Q, f u ^ 2 * Real.exp u) -
    (∫ u in (0 : ℝ)..Real.log Q, f u * Real.exp u) ^ 2 / ((Q : ℝ) - 1)

/-! ### Waves against the exponential weight -/

theorem abs_cos_sub_cos_le (a b : ℝ) : |Real.cos a - Real.cos b| ≤ |a - b| := by
  rw [Real.cos_sub_cos, abs_mul, abs_mul, abs_neg, abs_two]
  have h1 := Real.abs_sin_le_one ((a + b) / 2)
  have h2 := Real.abs_sin_le_abs (x := (a - b) / 2)
  rw [abs_div, abs_two] at h2
  have h3 : 0 ≤ |Real.sin ((a - b) / 2)| := abs_nonneg _
  nlinarith [abs_nonneg (Real.sin ((a + b) / 2))]

/-- `∫_0^L cos(su) e^u du = (e^L (cos sL + s sin sL) − 1)/(1 + s²)`. -/
theorem integral_cos_mul_exp (s L : ℝ) :
    ∫ u in (0 : ℝ)..L, Real.cos (s * u) * Real.exp u =
      (Real.exp L * (Real.cos (s * L) + s * Real.sin (s * L)) - 1) / (1 + s ^ 2) := by
  have hs : 1 + s ^ 2 ≠ 0 := by positivity
  have hF : ∀ u, HasDerivAt
      (fun u => Real.exp u * (Real.cos (s * u) + s * Real.sin (s * u)) / (1 + s ^ 2))
      (Real.cos (s * u) * Real.exp u) u := by
    intro u
    have hl : HasDerivAt (fun u : ℝ => s * u) s u := by
      simpa using (hasDerivAt_id' u).const_mul s
    have h1 : HasDerivAt (fun u => Real.cos (s * u)) (-Real.sin (s * u) * s) u := hl.cos
    have h2 : HasDerivAt (fun u => Real.sin (s * u)) (Real.cos (s * u) * s) u := hl.sin
    have h3 := ((Real.hasDerivAt_exp u).mul (h1.add (h2.const_mul s))).div_const (1 + s ^ 2)
    exact h3.congr_deriv (by simp only [Pi.add_apply, Pi.mul_apply]; rw [div_eq_iff hs]; ring)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hF u)
    ((by fun_prop : Continuous fun u => Real.cos (s * u) * Real.exp u).intervalIntegrable _ _)]
  simp only [mul_zero, Real.cos_zero, Real.sin_zero, Real.exp_zero, one_mul, add_zero]
  field_simp

/-- A wave of frequency `|s| ≥ 1` integrates against `e^u` on `[0, L]` to at most `4 e^L/|s|`. -/
theorem abs_integral_cos_mul_exp_le {s L : ℝ} (hs : 1 ≤ |s|) (hL : 0 ≤ L) :
    |∫ u in (0 : ℝ)..L, Real.cos (s * u) * Real.exp u| ≤ 4 * Real.exp L / |s| := by
  rw [integral_cos_mul_exp]
  have heL : 1 ≤ Real.exp L := Real.one_le_exp hL
  have hs0 : 0 < |s| := by linarith
  have hden : 0 < 1 + s ^ 2 := by positivity
  have hnum : |Real.exp L * (Real.cos (s * L) + s * Real.sin (s * L)) - 1| ≤
      2 * Real.exp L * (1 + |s|) := by
    have hc := Real.abs_cos_le_one (s * L)
    have hsn := Real.abs_sin_le_one (s * L)
    have h1 : |Real.cos (s * L) + s * Real.sin (s * L)| ≤ 1 + |s| := by
      calc |Real.cos (s * L) + s * Real.sin (s * L)|
          ≤ |Real.cos (s * L)| + |s * Real.sin (s * L)| := abs_add_le _ _
        _ ≤ 1 + |s| := by
            rw [abs_mul]
            nlinarith [abs_nonneg s, abs_nonneg (Real.sin (s * L))]
    calc |Real.exp L * (Real.cos (s * L) + s * Real.sin (s * L)) - 1|
        ≤ |Real.exp L * (Real.cos (s * L) + s * Real.sin (s * L))| + |(1 : ℝ)| := abs_sub _ _
      _ = Real.exp L * |Real.cos (s * L) + s * Real.sin (s * L)| + 1 := by
          rw [abs_mul, abs_of_pos (Real.exp_pos L), abs_one]
      _ ≤ Real.exp L * (1 + |s|) + Real.exp L * (1 + |s|) := by
          have := mul_le_mul_of_nonneg_left h1 (Real.exp_pos L).le
          nlinarith [abs_nonneg s]
      _ = 2 * Real.exp L * (1 + |s|) := by ring
  rw [abs_div, abs_of_pos hden, div_le_div_iff₀ hden hs0]
  have hsq : s ^ 2 = |s| ^ 2 := (sq_abs s).symm
  have h2 : 2 * Real.exp L * (1 + |s|) * |s| ≤ 4 * Real.exp L * (1 + s ^ 2) := by
    rw [hsq]
    nlinarith [mul_nonneg (Real.exp_pos L).le (sq_nonneg (|s| - 1)), Real.exp_pos L]
  nlinarith [mul_le_mul_of_nonneg_right hnum hs0.le]

/-! ### The variance of a wave -/

/-- **A wave of high frequency keeps a quarter of the mass as variance.** -/
theorem dilationVar_cos_ge {Q : ℕ} (hQ : 2 ≤ Q) {t : ℝ} (ht : 64 * (Q : ℝ) ≤ t) :
    ((Q : ℝ) - 1) / 4 ≤ dilationVar Q (fun u => Real.cos (t * u)) := by
  have hQ1 : (1 : ℝ) ≤ (Q : ℝ) - 1 := by
    have : (2 : ℝ) ≤ Q := by exact_mod_cast hQ
    linarith
  have hQ0 : (0 : ℝ) < Q := by linarith
  have hL : 0 ≤ Real.log Q := Real.log_nonneg (by linarith)
  have heL : Real.exp (Real.log Q) = Q := Real.exp_log hQ0
  have ht1 : 1 ≤ t := by nlinarith
  have ht0 : 0 < t := by linarith
  -- the mass and the oscillating parts
  have hmass : ∫ u in (0 : ℝ)..Real.log Q, Real.exp u = (Q : ℝ) - 1 := by
    rw [integral_exp, heL, Real.exp_zero]
  have hsq : ∫ u in (0 : ℝ)..Real.log Q, Real.cos (t * u) ^ 2 * Real.exp u =
      ((Q : ℝ) - 1) / 2 + (∫ u in (0 : ℝ)..Real.log Q, Real.cos ((2 * t) * u) * Real.exp u) / 2 := by
    have e : (fun u => Real.cos (t * u) ^ 2 * Real.exp u) =
        fun u => Real.exp u / 2 + Real.cos ((2 * t) * u) * Real.exp u / 2 := by
      funext u
      rw [Real.cos_sq, show 2 * (t * u) = 2 * t * u by ring]
      ring
    rw [e, intervalIntegral.integral_add, intervalIntegral.integral_div,
      intervalIntegral.integral_div, hmass]
    · exact (Real.continuous_exp.div_const 2).intervalIntegrable _ _
    · exact ((by fun_prop : Continuous fun u => Real.cos ((2 * t) * u) * Real.exp u).div_const
        2).intervalIntegrable _ _
  have hb2 := abs_integral_cos_mul_exp_le (s := 2 * t) (by rw [abs_of_pos (by linarith)]; linarith)
    hL
  have hb1 := abs_integral_cos_mul_exp_le (s := t) (by rw [abs_of_pos ht0]; exact ht1) hL
  rw [heL, abs_of_pos (by linarith : (0 : ℝ) < 2 * t)] at hb2
  rw [heL, abs_of_pos ht0] at hb1
  -- `4Q/t ≤ 1/16`
  have hsmall : 4 * (Q : ℝ) / t ≤ 1 / 16 := by
    rw [div_le_div_iff₀ ht0 (by norm_num)]
    linarith
  have hsmall2 : 4 * (Q : ℝ) / (2 * t) ≤ 1 / 16 := by
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]
    linarith
  show ((Q : ℝ) - 1) / 4 ≤ (∫ u in (0 : ℝ)..Real.log Q, Real.cos (t * u) ^ 2 * Real.exp u) -
    (∫ u in (0 : ℝ)..Real.log Q, Real.cos (t * u) * Real.exp u) ^ 2 / ((Q : ℝ) - 1)
  rw [hsq]
  obtain ⟨I1, hI1⟩ : ∃ I, I = ∫ u in (0 : ℝ)..Real.log Q, Real.cos (t * u) * Real.exp u := ⟨_, rfl⟩
  obtain ⟨I2, hI2⟩ : ∃ I, I = ∫ u in (0 : ℝ)..Real.log Q, Real.cos ((2 * t) * u) * Real.exp u :=
    ⟨_, rfl⟩
  rw [← hI1] at hb1 ⊢
  rw [← hI2] at hb2 ⊢
  have h1 : |I1| ≤ 1 / 16 := hb1.trans hsmall
  have h2 : |I2| ≤ 1 / 16 := hb2.trans hsmall2
  have h3 : I1 ^ 2 ≤ 1 / 256 := by
    have := sq_abs I1
    nlinarith [abs_nonneg I1]
  have h4 : I1 ^ 2 / ((Q : ℝ) - 1) ≤ 1 / 256 := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  have h5 := neg_abs_le I2
  linarith

/-! ### The theorem -/

/-- At a common return of the rotations by `log k`, no floor map moves the wave. -/
theorem dilationForm_cos_le {Q : ℕ} {t η : ℝ}
    (hret : ∀ k ∈ Icc 2 Q, ∃ m : ℤ, |t * Real.log k - m * (2 * π)| ≤ η) :
    dilationForm Q (fun u => Real.cos (t * u)) ≤ η ^ 2 * Q * ∑ k ∈ Icc 2 Q, Λ k := by
  show ∑ k ∈ Icc 2 Q, Λ k * ∫ u in (0 : ℝ)..Real.log ((Q : ℝ) / k),
      (Real.cos (t * u) - Real.cos (t * (u + Real.log k))) ^ 2 * Real.exp u ≤ _
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun k hk => ?_
  obtain ⟨m, hm⟩ := hret k hk
  have hk2 : 2 ≤ k := (Finset.mem_Icc.mp hk).1
  have hkQ : k ≤ Q := (Finset.mem_Icc.mp hk).2
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hkQ' : (k : ℝ) ≤ Q := by exact_mod_cast hkQ
  have hQk : 0 ≤ Real.log ((Q : ℝ) / k) := Real.log_nonneg ((one_le_div hk0).mpr hkQ')
  have hpt : ∀ u, (Real.cos (t * u) - Real.cos (t * (u + Real.log k))) ^ 2 * Real.exp u ≤
      η ^ 2 * Real.exp u := fun u => by
    have e : Real.cos (t * (u + Real.log k)) =
        Real.cos (t * u + (t * Real.log k - m * (2 * π))) := by
      rw [show t * u + (t * Real.log k - m * (2 * π)) = t * (u + Real.log k) - m * (2 * π) by
        ring, Real.cos_sub_int_mul_two_pi]
    rw [e]
    have h := abs_cos_sub_cos_le (t * u) (t * u + (t * Real.log k - m * (2 * π)))
    rw [show t * u - (t * u + (t * Real.log k - m * (2 * π))) =
      -(t * Real.log k - m * (2 * π)) by ring, abs_neg] at h
    have h2 : (Real.cos (t * u) - Real.cos (t * u + (t * Real.log k - m * (2 * π)))) ^ 2 ≤
        η ^ 2 := by
      have := sq_abs (Real.cos (t * u) - Real.cos (t * u + (t * Real.log k - m * (2 * π))))
      nlinarith [abs_nonneg (Real.cos (t * u) - Real.cos (t * u + (t * Real.log k - m * (2 * π)))),
        abs_nonneg (t * Real.log k - m * (2 * π))]
    exact mul_le_mul_of_nonneg_right h2 (Real.exp_pos u).le
  have hint : ∫ u in (0 : ℝ)..Real.log ((Q : ℝ) / k),
      (Real.cos (t * u) - Real.cos (t * (u + Real.log k))) ^ 2 * Real.exp u ≤
      η ^ 2 * ((Q : ℝ) / k - 1) := by
    calc _ ≤ ∫ u in (0 : ℝ)..Real.log ((Q : ℝ) / k), η ^ 2 * Real.exp u :=
          integral_mono_on hQk
            ((by fun_prop : Continuous fun u =>
              (Real.cos (t * u) - Real.cos (t * (u + Real.log k))) ^ 2 *
                Real.exp u).intervalIntegrable _ _)
            ((by fun_prop : Continuous fun u => η ^ 2 * Real.exp u).intervalIntegrable _ _)
            fun u _ => hpt u
      _ = η ^ 2 * ((Q : ℝ) / k - 1) := by
          rw [intervalIntegral.integral_const_mul, integral_exp,
            Real.exp_log (div_pos (by linarith) hk0),
            Real.exp_zero]
  have hQk1 : (Q : ℝ) / k - 1 ≤ Q := by
    have : (Q : ℝ) / k ≤ Q := div_le_self (by linarith) (by exact_mod_cast (show 1 ≤ k by omega))
    linarith
  have hΛ : 0 ≤ Λ k := ArithmeticFunction.vonMangoldt_nonneg
  have h1 := mul_le_mul_of_nonneg_left hint hΛ
  have h2 : Λ k * (η ^ 2 * ((Q : ℝ) / k - 1)) ≤ η ^ 2 * Q * Λ k := by
    have := mul_le_mul_of_nonneg_left hQk1 (mul_nonneg hΛ (sq_nonneg η))
    nlinarith
  linarith

/-- **The dilation process on `(1, Q]` has no spectral gap**, at arbitrarily high frequencies: for
every `ε > 0` and `T` there is `t ≥ T` with `E(cos(t ·)) ≤ ε Var(cos(t ·))` and
`Var(cos(t ·)) > 0`. -/
theorem dilationForm_le_of_no_gap {Q : ℕ} (hQ : 2 ≤ Q) {ε : ℝ} (hε : 0 < ε) (T : ℝ) :
    ∃ t : ℝ, T ≤ t ∧ 0 < dilationVar Q (fun u => Real.cos (t * u)) ∧
      dilationForm Q (fun u => Real.cos (t * u)) ≤
        ε * dilationVar Q (fun u => Real.cos (t * u)) := by
  have hQ2 : (2 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hQ1 : (1 : ℝ) ≤ (Q : ℝ) - 1 := by linarith
  have hQ0 : (0 : ℝ) < Q := by linarith
  obtain ⟨S, hS⟩ : ∃ S, S = ∑ k ∈ Icc 2 Q, Λ k := ⟨_, rfl⟩
  have hS0 : 0 ≤ S := by
    rw [hS]; exact Finset.sum_nonneg fun _ _ => ArithmeticFunction.vonMangoldt_nonneg
  have hpi : 0 < 2 * π := by positivity
  -- the precision of the common return
  obtain ⟨X, hX⟩ : ∃ X : ℝ, X = 4 * Q * (S + 1) / ε := ⟨_, rfl⟩
  have hX0 : 0 < X := by
    rw [hX]; exact div_pos (mul_pos (mul_pos (by norm_num) hQ0) (by linarith)) hε
  have hsq0 : 0 < Real.sqrt X := Real.sqrt_pos.mpr hX0
  obtain ⟨N, hN⟩ := exists_nat_gt (2 * π * Real.sqrt X)
  have hN0 : (0 : ℝ) < N := (mul_pos hpi hsq0).trans hN
  have hN1 : 1 ≤ N := (by exact_mod_cast hN0 : 0 < N)
  -- a frequency scale above `T` and `64 Q`
  obtain ⟨T₀, hT₀⟩ : ∃ T₀ : ℝ, T₀ = max T (64 * Q) + 1 := ⟨_, rfl⟩
  have hT₀0 : 0 < T₀ := by
    rw [hT₀]
    have := le_max_right T (64 * (Q : ℝ))
    linarith
  obtain ⟨n, hn1, -, hn⟩ := HTGeometry.exists_dirichlet_simultaneous
    (ι := Icc 2 Q) (fun k => T₀ * Real.log (k : ℕ) / (2 * π)) N hN1
  have hT₀n : T₀ ≤ n * T₀ := le_mul_of_one_le_left hT₀0.le (by exact_mod_cast hn1)
  have h64 : 64 * (Q : ℝ) ≤ n * T₀ := by
    have := le_max_right T (64 * (Q : ℝ))
    linarith
  have hV := dilationVar_cos_ge hQ h64
  refine ⟨n * T₀, ?_, by linarith, ?_⟩
  · have := le_max_left T (64 * (Q : ℝ))
    linarith
  -- at the return no floor map moves the wave
  have hret : ∀ k ∈ Icc 2 Q, ∃ m : ℤ, |n * T₀ * Real.log k - m * (2 * π)| ≤ 2 * π / N := by
    intro k hk
    obtain ⟨m, hm⟩ := hn ⟨k, hk⟩
    refine ⟨m, ?_⟩
    have e : n * T₀ * Real.log k - m * (2 * π) =
        2 * π * ((n : ℝ) * (T₀ * Real.log (k : ℕ) / (2 * π)) - m) := by
      have h := div_mul_cancel₀ (T₀ * Real.log (k : ℕ)) hpi.ne'
      linear_combination (-(n : ℝ)) * h
    rw [e, abs_mul, abs_of_pos hpi]
    have := mul_le_mul_of_nonneg_left hm.le hpi.le
    calc 2 * π * |(n : ℝ) * (T₀ * Real.log (k : ℕ) / (2 * π)) - m| ≤ 2 * π * (1 / N) := this
      _ = 2 * π / N := by ring
  have hE := dilationForm_cos_le hret
  rw [← hS] at hE
  -- `(2π/N)² Q S ≤ ε (Q − 1)/4`
  have hηN : 2 * π / N ≤ 1 / Real.sqrt X := by
    rw [div_le_div_iff₀ hN0 hsq0]
    linarith
  have hη2 : (2 * π / N) ^ 2 ≤ ε / (4 * Q * (S + 1)) := by
    have h1 : (2 * π / N) ^ 2 ≤ (1 / Real.sqrt X) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hηN 2
    have h2 : (1 / Real.sqrt X) ^ 2 = ε / (4 * Q * (S + 1)) := by
      rw [div_pow, one_pow, Real.sq_sqrt hX0.le, hX, one_div_div]
    exact h1.trans (le_of_eq h2)
  have hfin : (2 * π / N) ^ 2 * Q * S ≤ ε * (((Q : ℝ) - 1) / 4) := by
    have h1 := mul_le_mul_of_nonneg_right hη2 (mul_nonneg hQ0.le hS0)
    have h2 : ε / (4 * Q * (S + 1)) * (Q * S) ≤ ε / 4 := by
      rw [div_mul_eq_mul_div, div_le_div_iff₀ (mul_pos (mul_pos (by norm_num) hQ0)
        (by linarith)) (by norm_num)]
      nlinarith [mul_pos hε hQ0]
    nlinarith
  calc dilationForm Q (fun u => Real.cos (n * T₀ * u)) ≤ (2 * π / N) ^ 2 * Q * S := hE
    _ ≤ ε * (((Q : ℝ) - 1) / 4) := hfin
    _ ≤ ε * dilationVar Q (fun u => Real.cos (n * T₀ * u)) :=
        mul_le_mul_of_nonneg_left hV hε.le

end GaloisForLFunctions.MixingArithmeticOfTheFloorTrees
