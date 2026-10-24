import GaloisForLFunctions.BezoutValuationIncidence.TheBalancedStatisticForcesAZeroFreeStrip

/-!
# The balanced statistic is the quasi-Riemann hypothesis

The dual-norm statistic of the Möbius windows has a power saving on a neighbourhood of the diagonal
`Q^{1-ε} ≤ d ≤ Q^{1+ε}` if and only if `ζ` has a zero-free strip, `Θ < 1`
(`balancedStatisticPowerSaving_iff`).

* `⇐`: Littlewood's `M(N) ≪ N^{Θ+ε}` bounds the long-window partial sums of the window, and the
  archimedean law (`abs_kernelStatisticAll_le_archimedean`) turns that into
  `|Λ_d(μ𝟙_{(Q,2Q]})| ≪ (d²/Q) Q^{-(1-Θ)/8}` on the band `|log d - log Q| ≤ ((1-Θ)/8) log Q`.
* `⇒`: `zetaZeroAbscissa_lt_one_of_balancedStatisticPowerSaving`.

Below the diagonal the power saving is unconditional at every modulus
(`abs_kernelStatisticAll_moebius_and_centredPrime_le_rpow`). So the cross-scale form of the Möbius
row has a power saving at every exponent `θ < 2`, and at `θ = 2` a power saving on any neighbourhood
is exactly a zero-free strip: the first rung of the balanced statistic is quasi-RH, with no weaker
intermediate statement.
-/

open Finset Filter Topology ArithmeticFunction RHTower
open scoped BigOperators ArithmeticFunction.Moebius

namespace GaloisForLFunctions.BezoutValuationIncidence

noncomputable section
set_option autoImplicit false

/-- `Σ_{1 ≤ e ≤ M} μ(e) = M(M)`. -/
theorem sum_Icc_moebiusReal_eq_mertensM (M : ℕ) :
    ∑ e ∈ Icc 1 M, moebiusReal e = RHTower.Sieve.mertensM M := by
  induction M with
  | zero => simp [RHTower.Sieve.mertensM]
  | succ M ih =>
    rw [sum_Icc_succ_top (by omega), ih, RHTower.Sieve.mertensM, RHTower.Sieve.mertensM,
      Finset.sum_range_succ _ (M + 1)]
    rfl

/-- Under `|M(N)| ≤ C₀ (N + 1)^γ`, the partial sums of the Möbius window are at most
`2 C₀ (2Q + 1)^γ`. -/
theorem abs_sum_range_moebiusWindowRow_le {C₀ γ : ℝ} (hγ : 0 ≤ γ)
    (hM : ∀ N : ℕ, |RHTower.Sieve.mertensM N| ≤ C₀ * ((N : ℝ) + 1) ^ γ) (Q : ℕ) :
    ∀ x ≤ Q, |∑ i ∈ range x, moebiusWindowRow Q (Q + 1 + i)| ≤ 2 * C₀ * (2 * (Q : ℝ) + 1) ^ γ := by
  intro x hx
  rw [sum_range_moebiusWindowRow Q x hx, sum_Icc_moebiusReal_eq_mertensM,
    sum_Icc_moebiusReal_eq_mertensM]
  have hC₀ : 0 ≤ C₀ := by
    have := (abs_nonneg _).trans (hM 0)
    simp only [Nat.cast_zero, zero_add, Real.one_rpow, mul_one] at this
    exact this
  have hxR : (x : ℝ) ≤ Q := by exact_mod_cast hx
  have h1 : |RHTower.Sieve.mertensM (Q + x)| ≤ C₀ * (2 * (Q : ℝ) + 1) ^ γ :=
    (hM _).trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity)
      (by push_cast; linarith) hγ) hC₀)
  have h2 : |RHTower.Sieve.mertensM Q| ≤ C₀ * (2 * (Q : ℝ) + 1) ^ γ :=
    (hM _).trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity)
      (by linarith [(Nat.cast_nonneg Q : (0 : ℝ) ≤ Q)]) hγ) hC₀)
  calc |RHTower.Sieve.mertensM (Q + x) - RHTower.Sieve.mertensM Q|
      ≤ |RHTower.Sieve.mertensM (Q + x)| + |RHTower.Sieve.mertensM Q| := abs_sub _ _
    _ ≤ 2 * C₀ * (2 * (Q : ℝ) + 1) ^ γ := by linarith

/-- The first layer of the archimedean law on the band: with `A ≤ 6C₀ q^γ`, `γ = 1 - 7ε₀`,
`W ≤ D(1 + log D)` and `q^{1-ε₀} ≤ D ≤ q^{1+ε₀}`, it is at most
`(π²/6 + 6(1 + 2/ε₀)²) C₀ D² q^{-1-ε₀}`. -/
theorem band_first_layer_le {q D A W C₀ γ ε₀ : ℝ} (hq1 : 1 ≤ q) (hD1 : 1 ≤ D)
    (hlo : q ^ (1 - ε₀) ≤ D) (hhi : D ≤ q ^ (1 + ε₀)) (hε₀ : 0 < ε₀) (hε₀1 : ε₀ ≤ 1 / 16)
    (hγ : γ = 1 - 7 * ε₀) (hC₀ : 0 ≤ C₀) (hA0 : 0 ≤ A) (hAle : A ≤ 6 * C₀ * q ^ γ)
    (hW0 : 0 ≤ W) (hW : W ≤ D * (1 + Real.log D)) :
    A / (q + 1) ^ 2 * (Real.pi ^ 2 * (D ^ 2 - 1) / 36 + q * W * (1 + Real.log q) / 2) ≤
      (Real.pi ^ 2 / 6 * C₀ + 6 * C₀ * (1 + 2 / ε₀) ^ 2) * (D ^ 2 * q ^ (-1 - ε₀)) := by
  have hq0 : 0 < q := by linarith
  have hD0 : 0 < D := by linarith
  have hlogq0 : 0 ≤ Real.log q := Real.log_nonneg hq1
  have hlogD : 1 + Real.log D ≤ 2 * (1 + Real.log q) := by
    have h := Real.log_le_log hD0 hhi
    rw [Real.log_rpow hq0] at h
    nlinarith
  have hlogq : (1 + Real.log q) ^ 2 ≤ (1 + 2 / ε₀) ^ 2 * q ^ ε₀ := by
    have h := one_add_log_le_rpow hq1 (by positivity : 0 < ε₀ / 2)
    rw [show 1 / (ε₀ / 2) = 2 / ε₀ by field_simp] at h
    calc (1 + Real.log q) ^ 2 ≤ ((1 + 2 / ε₀) * q ^ (ε₀ / 2)) ^ 2 :=
          pow_le_pow_left₀ (by linarith) h 2
      _ = (1 + 2 / ε₀) ^ 2 * q ^ ε₀ := by
          rw [mul_pow, ← Real.rpow_natCast (q ^ (ε₀ / 2)) 2, ← Real.rpow_mul hq0.le]
          congr 2; push_cast; ring
  have hinv : A / (q + 1) ^ 2 ≤ 6 * C₀ * q ^ (γ - 2) := by
    rw [Real.rpow_sub hq0, Real.rpow_two]
    calc A / (q + 1) ^ 2 ≤ A / q ^ 2 :=
          div_le_div_of_nonneg_left hA0 (by positivity) (pow_le_pow_left₀ hq0.le (by linarith) 2)
      _ ≤ 6 * C₀ * q ^ γ / q ^ 2 := div_le_div_of_nonneg_right hAle (by positivity)
      _ = 6 * C₀ * (q ^ γ / q ^ 2) := by ring
  have hX : Real.pi ^ 2 * (D ^ 2 - 1) / 36 + q * W * (1 + Real.log q) / 2 ≤
      Real.pi ^ 2 * D ^ 2 / 36 + q * D * (1 + Real.log q) ^ 2 := by
    have h1 : Real.pi ^ 2 * (D ^ 2 - 1) / 36 ≤ Real.pi ^ 2 * D ^ 2 / 36 := by
      have := sq_nonneg Real.pi; nlinarith
    have h2 : W * (1 + Real.log q) ≤ D * (2 * (1 + Real.log q)) * (1 + Real.log q) :=
      mul_le_mul_of_nonneg_right (hW.trans (mul_le_mul_of_nonneg_left hlogD hD0.le)) (by linarith)
    have h3 := mul_le_mul_of_nonneg_left h2 hq0.le
    have e : q * (D * (2 * (1 + Real.log q)) * (1 + Real.log q)) / 2 = q * D * (1 + Real.log q) ^ 2 := by
      ring
    have e' : q * W * (1 + Real.log q) / 2 = q * (W * (1 + Real.log q)) / 2 := by ring
    rw [e']
    linarith [div_le_div_of_nonneg_right h3 (by norm_num : (0 : ℝ) ≤ 2)]
  have hX0 : 0 ≤ Real.pi ^ 2 * (D ^ 2 - 1) / 36 + q * W * (1 + Real.log q) / 2 := by
    have : 0 ≤ D ^ 2 - 1 := by nlinarith
    positivity
  have hL := mul_le_mul hinv hX hX0 (by positivity)
  refine hL.trans ?_
  have b1 : q ^ (γ - 2) ≤ q ^ (-1 - ε₀) :=
    Real.rpow_le_rpow_of_exponent_le hq1 (by rw [hγ]; linarith)
  have b2 : D * (1 + Real.log q) ^ 2 * q ^ (γ - 1) ≤ (1 + 2 / ε₀) ^ 2 * (D ^ 2 * q ^ (-1 - ε₀)) := by
    calc D * (1 + Real.log q) ^ 2 * q ^ (γ - 1) ≤ D * ((1 + 2 / ε₀) ^ 2 * q ^ ε₀) * q ^ (γ - 1) := by
          gcongr
      _ = (1 + 2 / ε₀) ^ 2 * (D * q ^ (γ - 1 + ε₀)) := by
          rw [Real.rpow_add hq0]; ring
      _ ≤ (1 + 2 / ε₀) ^ 2 * (D * q ^ ((1 - ε₀) + (-1 - ε₀))) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ hD0.le) (by positivity)
          exact Real.rpow_le_rpow_of_exponent_le hq1 (by rw [hγ]; linarith)
      _ = (1 + 2 / ε₀) ^ 2 * (D * (q ^ (1 - ε₀) * q ^ (-1 - ε₀))) := by rw [Real.rpow_add hq0]
      _ ≤ (1 + 2 / ε₀) ^ 2 * (D * (D * q ^ (-1 - ε₀))) := by gcongr
      _ = (1 + 2 / ε₀) ^ 2 * (D ^ 2 * q ^ (-1 - ε₀)) := by ring
  have e1 : 6 * C₀ * q ^ (γ - 2) * (Real.pi ^ 2 * D ^ 2 / 36 + q * D * (1 + Real.log q) ^ 2) =
      Real.pi ^ 2 / 6 * C₀ * D ^ 2 * q ^ (γ - 2) +
        6 * C₀ * (D * (1 + Real.log q) ^ 2 * q ^ (γ - 1)) := by
    rw [show (γ - 1 : ℝ) = (γ - 2) + 1 by ring, Real.rpow_add hq0, Real.rpow_one]; ring
  rw [e1]
  have c1 : 0 ≤ Real.pi ^ 2 / 6 * C₀ * D ^ 2 := by positivity
  have t1 := mul_le_mul_of_nonneg_left b1 c1
  have t2 := mul_le_mul_of_nonneg_left b2 (by positivity : (0 : ℝ) ≤ 6 * C₀)
  have e2 : (Real.pi ^ 2 / 6 * C₀ + 6 * C₀ * (1 + 2 / ε₀) ^ 2) * (D ^ 2 * q ^ (-1 - ε₀)) =
      Real.pi ^ 2 / 6 * C₀ * D ^ 2 * q ^ (-1 - ε₀) +
        6 * C₀ * ((1 + 2 / ε₀) ^ 2 * (D ^ 2 * q ^ (-1 - ε₀))) := by ring
  rw [e2]
  linarith

/-- The second layer: at most `(π²/4) C₀ D² q^{-1-ε₀}`. -/
theorem band_second_layer_le {q D A C₀ γ ε₀ : ℝ} (hq1 : 1 ≤ q) (hD1 : 1 ≤ D)
    (hhi : D ≤ q ^ (1 + ε₀)) (hε₀ : 0 < ε₀) (hγ : γ = 1 - 7 * ε₀) (hC₀ : 0 ≤ C₀) (hA0 : 0 ≤ A)
    (hAle : A ≤ 6 * C₀ * q ^ γ) :
    A / (q + 1) ^ 3 * (Real.pi ^ 2 * (D ^ 2 - 1) * (D + 2 * q) / 72) ≤
      Real.pi ^ 2 / 4 * C₀ * (D ^ 2 * q ^ (-1 - ε₀)) := by
  have hq0 : 0 < q := by linarith
  have hinv : A / (q + 1) ^ 3 ≤ 6 * C₀ * q ^ (γ - 3) := by
    rw [Real.rpow_sub hq0, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    calc A / (q + 1) ^ 3 ≤ A / q ^ 3 :=
          div_le_div_of_nonneg_left hA0 (by positivity) (pow_le_pow_left₀ hq0.le (by linarith) 3)
      _ ≤ 6 * C₀ * q ^ γ / q ^ 3 := div_le_div_of_nonneg_right hAle (by positivity)
      _ = 6 * C₀ * (q ^ γ / q ^ 3) := by ring
  have hq1e : q ≤ q ^ (1 + ε₀) := by
    calc q = q ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ q ^ (1 + ε₀) := Real.rpow_le_rpow_of_exponent_le hq1 (by linarith)
  have h0 : 0 ≤ D ^ 2 - 1 := by nlinarith
  have hX : Real.pi ^ 2 * (D ^ 2 - 1) * (D + 2 * q) / 72 ≤ Real.pi ^ 2 * D ^ 2 * (3 * q ^ (1 + ε₀)) / 72 := by
    have hpi := sq_nonneg Real.pi
    have h1 : D + 2 * q ≤ 3 * q ^ (1 + ε₀) := by linarith
    have : Real.pi ^ 2 * (D ^ 2 - 1) * (D + 2 * q) ≤ Real.pi ^ 2 * D ^ 2 * (3 * q ^ (1 + ε₀)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left (by linarith) hpi) h1 (by positivity) (by positivity)
    linarith
  have hX0 : 0 ≤ Real.pi ^ 2 * (D ^ 2 - 1) * (D + 2 * q) / 72 := by positivity
  refine (mul_le_mul hinv hX hX0 (by positivity)).trans ?_
  have e : 6 * C₀ * q ^ (γ - 3) * (Real.pi ^ 2 * D ^ 2 * (3 * q ^ (1 + ε₀)) / 72) =
      Real.pi ^ 2 / 4 * C₀ * D ^ 2 * q ^ (γ + ε₀ - 2) := by
    rw [show q ^ (γ + ε₀ - 2) = q ^ (γ - 3) * q ^ (1 + ε₀) by
      rw [← Real.rpow_add hq0]; congr 1; ring]
    ring
  rw [e, mul_assoc (Real.pi ^ 2 / 4 * C₀)]
  refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ (by positivity)) (by positivity)
  exact Real.rpow_le_rpow_of_exponent_le hq1 (by rw [hγ]; linarith)

/-- The harmonic tail: at most `D² q^{-1-ε₀}/12`. -/
theorem band_third_layer_le {q D T ε₀ : ℝ} (hq1 : 1 ≤ q) (hD1 : 1 ≤ D) (hε₀1 : ε₀ ≤ 1)
    (hT0 : 0 ≤ T) (hT : T ≤ 1 / q) :
    (D ^ 2 - 1) / (12 * q) * T ≤ 1 / 12 * (D ^ 2 * q ^ (-1 - ε₀)) := by
  have hq0 : 0 < q := by linarith
  have h1 : (D ^ 2 - 1) / (12 * q) * T ≤ D ^ 2 / (12 * q) * (1 / q) :=
    mul_le_mul (div_le_div_of_nonneg_right (by linarith) (by positivity)) hT hT0 (by positivity)
  refine h1.trans ?_
  have e : D ^ 2 / (12 * q) * (1 / q) = 1 / 12 * (D ^ 2 * q ^ (-2 : ℝ)) := by
    rw [Real.rpow_neg hq0.le, Real.rpow_two]; field_simp
  rw [e]
  refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ (by positivity)) (by norm_num)
  exact Real.rpow_le_rpow_of_exponent_le hq1 (by linarith)

/-- **A zero-free strip gives the balanced power saving.** -/
theorem balancedStatisticPowerSaving_of_lt_one (hΘ : zetaZeroAbscissa < 1) :
    BalancedStatisticPowerSaving := by
  set Θ := zetaZeroAbscissa
  have hΘ0 : (1 / 2 : ℝ) ≤ Θ := half_le_zetaZeroAbscissa
  set ε₀ : ℝ := (1 - Θ) / 8 with hε₀
  have hε₀0 : 0 < ε₀ := by rw [hε₀]; linarith
  have hε₀1 : ε₀ ≤ 1 / 16 := by rw [hε₀]; linarith
  obtain ⟨C₀, hC₀, hL⟩ := mobiusMertens_subpower_zetaZeroAbscissa ε₀ hε₀0
  set γ := Θ + ε₀ with hγdef
  have hγ : γ = 1 - 7 * ε₀ := by rw [hγdef, hε₀]; ring
  have hγ0 : 0 ≤ γ := by rw [hγ]; linarith
  have hγ1 : γ ≤ 1 := by rw [hγ]; linarith
  have hM : ∀ N : ℕ, |RHTower.Sieve.mertensM N| ≤ C₀ * ((N : ℝ) + 1) ^ γ := fun N => by
    rw [← norm_mobiusMertensPartialSum_eq]; exact hL N
  refine ⟨ε₀, ε₀, Real.pi ^ 2 / 6 * C₀ + 6 * C₀ * (1 + 2 / ε₀) ^ 2 +
    Real.pi ^ 2 / 4 * C₀ + 1 / 12, hε₀0, hε₀0, fun Q d hQ hlo hhi => ?_⟩
  have hq2 : (2 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hq1 : (1 : ℝ) ≤ Q := by linarith
  have hq0 : (0 : ℝ) < Q := by linarith
  have hD1 : (1 : ℝ) ≤ d := le_trans (Real.one_le_rpow hq1 (by linarith)) hlo
  have hd0 : 0 < d := by exact_mod_cast (show (0 : ℝ) < d by linarith)
  have hA := abs_sum_range_moebiusWindowRow_le hγ0 hM Q
  have hsupp : ∀ n, moebiusWindowRow Q n ≠ 0 → Q < n ∧ n ≤ 2 * Q :=
    fun n h => moebiusWindowRow_ne_zero_imp h
  have hlaw := abs_kernelStatisticAll_le_archimedean hd0 le_rfl hsupp hA (by omega : 1 ≤ Q)
  refine hlaw.trans ?_
  have hAle : 2 * C₀ * (2 * (Q : ℝ) + 1) ^ γ ≤ 6 * C₀ * (Q : ℝ) ^ γ := by
    have h1 : (2 * (Q : ℝ) + 1) ^ γ ≤ (3 * (Q : ℝ)) ^ γ :=
      Real.rpow_le_rpow (by positivity) (by linarith) hγ0
    have h2 : (3 * (Q : ℝ)) ^ γ ≤ 3 * (Q : ℝ) ^ γ := by
      rw [Real.mul_rpow (by norm_num) hq0.le]
      refine mul_le_mul_of_nonneg_right ?_ (by positivity)
      calc (3 : ℝ) ^ γ ≤ (3 : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hγ1
        _ = 3 := Real.rpow_one 3
    nlinarith
  have hT : ∑ n ∈ Icc 1 (2 * Q), |moebiusWindowRow Q n| / (n : ℝ) ^ 2 ≤ 1 / (Q : ℝ) := by
    have h := sum_Icc_abs_moebiusWindowRow_div_pow_le (N := 2 * Q) (by omega : 1 ≤ Q) 2
    rwa [show ((Q : ℝ)) / (Q : ℝ) ^ 2 = 1 / (Q : ℝ) by field_simp] at h
  have hT0 : 0 ≤ ∑ n ∈ Icc 1 (2 * Q), |moebiusWindowRow Q n| / (n : ℝ) ^ 2 :=
    sum_nonneg fun _ _ => by positivity
  have h1 := band_first_layer_le hq1 hD1 hlo hhi hε₀0 hε₀1 hγ hC₀ (by positivity) hAle
    (rootHarmonicSum_nonneg d) (rootHarmonicSum_le d)
  have h2 := band_second_layer_le hq1 hD1 hhi hε₀0 hγ hC₀ (by positivity) hAle
  have h3 := band_third_layer_le (ε₀ := ε₀) hq1 hD1 (by linarith) hT0 hT
  have hP : ((d : ℝ) ^ 2 / Q) * (Q : ℝ) ^ (-ε₀) = (d : ℝ) ^ 2 * (Q : ℝ) ^ (-1 - ε₀) := by
    rw [show (-1 - ε₀ : ℝ) = -1 + -ε₀ by ring, Real.rpow_add hq0, Real.rpow_neg_one]; ring
  rw [mul_assoc (Real.pi ^ 2 / 6 * C₀ + 6 * C₀ * (1 + 2 / ε₀) ^ 2 + Real.pi ^ 2 / 4 * C₀ + 1 / 12), hP]
  have e : (Real.pi ^ 2 / 6 * C₀ + 6 * C₀ * (1 + 2 / ε₀) ^ 2 + Real.pi ^ 2 / 4 * C₀ + 1 / 12) *
      ((d : ℝ) ^ 2 * (Q : ℝ) ^ (-1 - ε₀)) =
      (Real.pi ^ 2 / 6 * C₀ + 6 * C₀ * (1 + 2 / ε₀) ^ 2) * ((d : ℝ) ^ 2 * (Q : ℝ) ^ (-1 - ε₀)) +
        Real.pi ^ 2 / 4 * C₀ * ((d : ℝ) ^ 2 * (Q : ℝ) ^ (-1 - ε₀)) +
        1 / 12 * ((d : ℝ) ^ 2 * (Q : ℝ) ^ (-1 - ε₀)) := by ring
  rw [e]
  linarith

/-- **The balanced statistic is the quasi-Riemann hypothesis.** A power saving for the statistic of
the Möbius windows on some neighbourhood of the diagonal holds if and only if `Θ < 1`. -/
theorem balancedStatisticPowerSaving_iff : BalancedStatisticPowerSaving ↔ zetaZeroAbscissa < 1 :=
  ⟨zetaZeroAbscissa_lt_one_of_balancedStatisticPowerSaving, balancedStatisticPowerSaving_of_lt_one⟩

end

end GaloisForLFunctions.BezoutValuationIncidence
