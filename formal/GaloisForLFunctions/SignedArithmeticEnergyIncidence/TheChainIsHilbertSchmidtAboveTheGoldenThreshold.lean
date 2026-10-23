import GaloisForLFunctions.SignedArithmeticEnergyIncidence.ShortIntervalSumsOfTheDampedDivisorCoefficients

/-!
# The chain is Hilbert–Schmidt above the golden threshold

`TheChainIsHilbertSchmidtAboveInverseRootTwo` bounds the source jump of the centred chain by
`min(J, 2C(N/K)^{1−η})` and so needs `η² > ½`.  The divisor structure of `c_η`
(`ShortIntervalSumsOfTheDampedDivisorCoefficients`, with `D = max(J, √a)`) sharpens the jump below
the square root (`abs_jump_le_belowSqrt`, `K² ≤ N`):

`|P(a) − P(a')| ≤ C (J^{1−η} + a^{(1−η)/2})`.

The first term is square summable against the kernel for every `η > ½`.  The second is
interpolated with the trivial bound `J`: `min(J, a^{(1−η)/2}) ≤ J^λ a^{(1−η)(1−λ)/2}`.  On
`K = N^κ`, `κ ∈ [0, ½]`, its exponent is linear in `κ`, and it is summable at both ends iff
`(2−3η)/(1−η) < λ < η/(1+η)`; these are compatible exactly when `η² + η > 1`
(`goldenExp_bounds`), i.e. `η > (√5−1)/2`.  Sums below the square root are reduced to products of
zeta values by moving `K^{2t} ≤ N^t` from the columns to the rows (`sum_belowSqrt_rpow_le`).

So the centred chain is bounded in `ℓ²` on finitely supported sequences above the golden threshold
(`centeredOperator_l2_le_of_goldenThreshold`).
-/

open Finset RHTower ArithmeticFunction
open scoped ZeroAtInfty
open GaloisForLFunctions.BezoutValuationIncidence GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy

namespace GaloisForLFunctions.SignedArithmeticEnergyIncidence

noncomputable section
set_option autoImplicit false

/-! ### The source jump below the square root -/

/-- Below the square root and for `K ≥ 2`, the jump interval is at most half of `⌊N/K⌋`. -/
theorem two_mul_floorJump_le {N K : ℕ} (hK : 2 ≤ K) (hA : K * K ≤ N) :
    2 * (N / K - N / (K + 1)) ≤ N / K := by
  have hq1 : 1 ≤ N / (K + 1) :=
    (Nat.le_div_iff_mul_le (by omega)).2 (by nlinarith [Nat.mul_le_mul_right K hK])
  have hlt : N < N / (K + 1) * (K + 1) + (K + 1) := Nat.lt_div_mul_add (by omega)
  have hle : N / K < 2 * (N / (K + 1)) + 1 := by
    rw [Nat.div_lt_iff_lt_mul (by omega)]
    have := Nat.mul_le_mul_left (N / (K + 1)) hK
    nlinarith
  generalize N / K = a at hle ⊢
  generalize N / (K + 1) = q at hle ⊢
  omega

/-- The constant of the source jump below the square root. -/
def jumpConstant (η : ℝ) : ℝ := 2 * shortIntervalConstant η + 4 * (1 + 1 / (1 - η) + 1 / η)

theorem one_le_jumpConstant {η : ℝ} (h0 : 0 < η) (h1 : η < 1) : 1 ≤ jumpConstant η := by
  unfold jumpConstant shortIntervalConstant
  have : 0 < 1 - η := by linarith
  have : 0 ≤ 1 / (1 - η) := by positivity
  have : 0 ≤ 1 / η := by positivity
  have : 0 ≤ 5 / η := by positivity
  linarith

theorem jump_combine {C C₁ X Y : ℝ} (hC₁ : 0 ≤ C₁) (hX : 0 ≤ X) (hY : 0 ≤ Y) :
    C * (2 * (X + Y)) ≤ (2 * C + 4 * C₁) * (X + Y) := by
  nlinarith [mul_nonneg hC₁ (add_nonneg hX hY)]

/-- `K = 1`: the sign-blind bound, since then `J ≥ a/2`. -/
theorem abs_jump_le_of_one {η : ℝ} (h0 : 0 < η) (h1 : η < 1) (N : ℕ) :
    |pmPowerDampedCenteredDivisorPrefix η (N / 1) -
        pmPowerDampedCenteredDivisorPrefix η (N / (1 + 1))| ≤
      4 * (1 + 1 / (1 - η) + 1 / η) * ((((N / 1 - N / (1 + 1) : ℕ) : ℝ)) ^ (1 - η)) := by
  rw [Nat.div_one, show (1 + 1 : ℕ) = 2 from rfl]
  have hC₁ : 0 < 1 + 1 / (1 - η) + 1 / η := by
    have : 0 < 1 - η := by linarith
    positivity
  have hle : N / 2 ≤ N := Nat.div_le_self N 2
  have hJeq : (((N - N / 2 : ℕ) : ℝ)) = (N : ℝ) - ((N / 2 : ℕ) : ℝ) := Nat.cast_sub hle
  have hhalf : ((N / 2 : ℕ) : ℝ) * 2 ≤ N := by exact_mod_cast Nat.div_mul_le_self N 2
  have hJa : (N : ℝ) / 2 ≤ (((N - N / 2 : ℕ) : ℝ)) := by rw [hJeq]; linarith
  have hPa := abs_centeredPrefix_le_rpow h0 h1 N
  have hPa' := abs_centeredPrefix_le_rpow h0 h1 (N / 2)
  have ha'a : ((N / 2 : ℕ) : ℝ) ^ (1 - η) ≤ (N : ℝ) ^ (1 - η) :=
    Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hle) (by linarith)
  -- `N^{1−η} ≤ 2 J^{1−η}`
  have hhalfpow : (N : ℝ) ^ (1 - η) ≤ 2 * (((N - N / 2 : ℕ) : ℝ)) ^ (1 - η) := by
    have h2 : ((N : ℝ) / 2) ^ (1 - η) * 2 ^ (1 - η) = (N : ℝ) ^ (1 - η) := by
      rw [← Real.mul_rpow (by positivity) (by norm_num)]; congr 1; ring
    have h3 : (2 : ℝ) ^ (1 - η) ≤ 2 := by
      calc (2 : ℝ) ^ (1 - η) ≤ 2 ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
        _ = 2 := Real.rpow_one 2
    have h4 : ((N : ℝ) / 2) ^ (1 - η) ≤ (((N - N / 2 : ℕ) : ℝ)) ^ (1 - η) :=
      Real.rpow_le_rpow (by positivity) hJa (by linarith)
    rw [← h2]
    nlinarith [mul_le_mul h4 h3 (by positivity) (Real.rpow_nonneg (Nat.cast_nonneg _) _)]
  calc _ ≤ |pmPowerDampedCenteredDivisorPrefix η N| +
        |pmPowerDampedCenteredDivisorPrefix η (N / 2)| := abs_sub _ _
    _ ≤ 2 * (1 + 1 / (1 - η) + 1 / η) * (N : ℝ) ^ (1 - η) := by
        nlinarith [mul_le_mul_of_nonneg_left ha'a hC₁.le]
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hhalfpow (by positivity : (0 : ℝ) ≤ 2 *
          (1 + 1 / (1 - η) + 1 / η))]

/-- `K ≥ 2`: the short-interval bound with `D = max(J, √a)`. -/
theorem abs_jump_le_of_two_le {η : ℝ} (h0 : 0 < η) (h1 : η < 1) {N K : ℕ} (hK : 2 ≤ K)
    (hA : K * K ≤ N) :
    |pmPowerDampedCenteredDivisorPrefix η (N / K) -
        pmPowerDampedCenteredDivisorPrefix η (N / (K + 1))| ≤
      shortIntervalConstant η * (2 * ((((N / K - N / (K + 1) : ℕ) : ℝ)) ^ (1 - η) +
        ((N / K : ℕ) : ℝ) ^ ((1 - η) / 2))) := by
  have h2 := two_mul_floorJump_le hK hA
  have ha1 : 1 ≤ N / K := (Nat.le_div_iff_mul_le (by omega)).2 (by nlinarith)
  have haa' : N / (K + 1) ≤ N / K := Nat.div_le_div_left (by omega) (by omega)
  set a := N / K with hadef
  set a' := N / (K + 1) with ha'def
  set J : ℝ := ((a - a' : ℕ) : ℝ) with hJdef
  have hJ0 : 0 ≤ J := Nat.cast_nonneg _
  have hJeq : J = (a : ℝ) - a' := Nat.cast_sub haa'
  have ha1' : (1 : ℝ) ≤ a := by exact_mod_cast ha1
  have ha0 : (0 : ℝ) ≤ a := by linarith
  set s := Real.sqrt a with hsdef
  have hs1 : 1 ≤ s := by rw [hsdef, Real.one_le_sqrt]; exact ha1'
  have hss : s * s = a := Real.mul_self_sqrt ha0
  have hs0 : 0 < s := by linarith
  have hsa : s ≤ a := by nlinarith
  have hJa : J ≤ a := by
    rw [hJeq]
    have : (0 : ℝ) ≤ a' := Nat.cast_nonneg _
    linarith
  have hD1 : 1 ≤ max J s := le_max_of_le_right hs1
  have hJD : (a : ℝ) - a' ≤ max J s := by rw [← hJeq]; exact le_max_left _ _
  have hDa : max J s ≤ a := max_le hJa hsa
  have hshort := abs_centeredPrefix_sub_le_short h0 h1 haa' h2 hD1 hJD hDa
  -- the three pieces of the short-interval bound
  have e1 : (max J s) ^ (1 - η) ≤ J ^ (1 - η) + s ^ (1 - η) := by
    rcases le_total J s with h | h
    · rw [max_eq_right h]; linarith [Real.rpow_nonneg hJ0 (1 - η)]
    · rw [max_eq_left h]; linarith [Real.rpow_nonneg hs0.le (1 - η)]
  have e2 : ((a : ℝ) - a') * (max J s) ^ (-η) ≤ J ^ (1 - η) := by
    rw [← hJeq]
    rcases hJ0.eq_or_lt with h | h
    · rw [← h, zero_mul]; exact Real.rpow_nonneg le_rfl _
    · calc J * (max J s) ^ (-η) ≤ J * J ^ (-η) :=
            mul_le_mul_of_nonneg_left
              (Real.rpow_le_rpow_of_nonpos h (le_max_left _ _) (by linarith)) hJ0
        _ = J ^ (1 - η) := mul_rpow_neg_eq h
  have e3 : (a : ℝ) * (max J s) ^ (-(1 + η)) ≤ s ^ (1 - η) := by
    calc (a : ℝ) * (max J s) ^ (-(1 + η)) ≤ a * s ^ (-(1 + η)) :=
          mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow_of_nonpos hs0 (le_max_right _ _) (by linarith)) ha0
      _ = s * (s * s ^ (-(1 + η))) := by rw [← hss]; ring
      _ = s ^ (1 - η) := by
          rw [mul_rpow_neg_eq hs0, show 1 - (1 + η) = -η by ring, mul_rpow_neg_eq hs0]
  have hsq : s ^ (1 - η) = (a : ℝ) ^ ((1 - η) / 2) := by
    rw [hsdef, Real.sqrt_eq_rpow, ← Real.rpow_mul ha0]; congr 1; ring
  have hC : 0 ≤ shortIntervalConstant η := by
    unfold shortIntervalConstant
    have : 0 < 1 - η := by linarith
    positivity
  rw [← hsq]
  calc _ ≤ shortIntervalConstant η * ((max J s) ^ (1 - η) + ((a : ℝ) - a') * (max J s) ^ (-η) +
        a * (max J s) ^ (-(1 + η))) := hshort
    _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) hC

/-- **The source jump below the square root**: for `1 ≤ K` and `K² ≤ N`, with `a = ⌊N/K⌋` and
`J = a − ⌊N/(K+1)⌋`, `|P(a) − P(a')| ≤ C (J^{1−η} + a^{(1−η)/2})`. -/
theorem abs_jump_le_belowSqrt {η : ℝ} (h0 : 0 < η) (h1 : η < 1) {N K : ℕ} (hK : 1 ≤ K)
    (hA : K * K ≤ N) :
    |pmPowerDampedCenteredDivisorPrefix η (N / K) -
        pmPowerDampedCenteredDivisorPrefix η (N / (K + 1))| ≤
      jumpConstant η * ((((N / K - N / (K + 1) : ℕ) : ℝ)) ^ (1 - η) +
        ((N / K : ℕ) : ℝ) ^ ((1 - η) / 2)) := by
  have hC₁ : 0 < 1 + 1 / (1 - η) + 1 / η := by
    have : 0 < 1 - η := by linarith
    positivity
  have hX : 0 ≤ (((N / K - N / (K + 1) : ℕ) : ℝ)) ^ (1 - η) :=
    Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hY : 0 ≤ ((N / K : ℕ) : ℝ) ^ ((1 - η) / 2) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  rcases (show K = 1 ∨ 2 ≤ K by omega) with rfl | hK2
  · refine (abs_jump_le_of_one h0 h1 N).trans ?_
    have hCs : 0 ≤ shortIntervalConstant η := by
      unfold shortIntervalConstant
      have : 0 < 1 - η := by linarith
      positivity
    unfold jumpConstant
    nlinarith [mul_nonneg hCs (add_nonneg hX hY), mul_nonneg hC₁.le hY]
  · exact (abs_jump_le_of_two_le h0 h1 hK2 hA).trans (jump_combine hC₁.le hX hY)

/-! ### The squared majorant below the square root -/

theorem sq_rpow_eq_of_nonneg {x a : ℝ} (hx : 0 ≤ x) : (x ^ a) ^ 2 = x ^ (2 * a) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]; push_cast; ring_nf

/-- `K^{2−2η} N^{−2} (N/K²)^{2(1−η)} = N^{−2η} K^{2η−2}`. -/
theorem lengthTerm_rpow_eq {N K η : ℝ} (hN : 0 < N) (hK : 0 < K) :
    K ^ (2 - 2 * η) * N ^ (-2 : ℝ) * (N / K ^ 2) ^ (2 * (1 - η)) =
      N ^ (-2 * η) * K ^ (2 * η - 2) := by
  obtain ⟨u, rfl⟩ : ∃ u, N = Real.exp u := ⟨Real.log N, (Real.exp_log hN).symm⟩
  obtain ⟨v, rfl⟩ : ∃ v, K = Real.exp v := ⟨Real.log K, (Real.exp_log hK).symm⟩
  rw [← Real.exp_nat_mul]
  simp only [← Real.exp_mul, ← Real.exp_sub, ← Real.exp_add]
  congr 1
  push_cast
  ring

/-- `K^{2−2η} N^{−2} (N/K²)^{2λ} (N/K)^{(1−η)(1−λ)} = N^{α} K^{β}`. -/
theorem interpTerm_rpow_eq {N K η l : ℝ} (hN : 0 < N) (hK : 0 < K) :
    K ^ (2 - 2 * η) * N ^ (-2 : ℝ) * ((N / K ^ 2) ^ (2 * l) * (N / K) ^ ((1 - η) * (1 - l))) =
      N ^ (-2 + 2 * l + (1 - η) * (1 - l)) * K ^ (2 - 2 * η - 4 * l - (1 - η) * (1 - l)) := by
  obtain ⟨u, rfl⟩ : ∃ u, N = Real.exp u := ⟨Real.log N, (Real.exp_log hN).symm⟩
  obtain ⟨v, rfl⟩ : ∃ v, K = Real.exp v := ⟨Real.log K, (Real.exp_log hK).symm⟩
  rw [← Real.exp_nat_mul]
  simp only [← Real.exp_mul, ← Real.exp_sub, ← Real.exp_add]
  congr 1
  push_cast
  ring

/-- `2^p ≤ 4` for `p ≤ 2`. -/
theorem two_rpow_le_four {p : ℝ} (hp : p ≤ 2) : (2 : ℝ) ^ p ≤ 4 := by
  calc (2 : ℝ) ^ p ≤ 2 ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hp
    _ = 4 := by norm_num [Real.rpow_two]

/-- `c² (q P) ≤ 4 c² P` for `q ≤ 4`, `P ≥ 0`. -/
theorem sq_mul_le_four {c q P : ℝ} (hq : q ≤ 4) (hP : 0 ≤ P) : c ^ 2 * (q * P) ≤ 4 * c ^ 2 * P := by
  nlinarith [mul_le_mul_of_nonneg_right hq (mul_nonneg (sq_nonneg c) hP)]

/-- `(K^{1−η}/N)² = K^{2−2η} N^{−2}`. -/
theorem sq_kernelFactor_eq {N K η : ℝ} (hN : 0 < N) (hK : 0 < K) :
    (K ^ (1 - η) / N) ^ 2 = K ^ (2 - 2 * η) * N ^ (-2 : ℝ) := by
  rw [div_eq_mul_one_div]; simp only [mul_pow]
  rw [sq_rpow_eq hK, sq_inv_eq_rpow hN]; ring_nf

theorem mul_add_le_three {u Δ m A B E : ℝ} (hu : 0 ≤ u) (hΔ : Δ ≤ A + B) (hm : m ≤ E) :
    u * (Δ + m) ≤ u * A + u * B + u * E := by
  calc u * (Δ + m) ≤ u * (A + B + E) := mul_le_mul_of_nonneg_left (by linarith) hu
    _ = _ := by ring

/-- **The jump splits** into a power of the length and an interpolation: if `Δ ≤ J` and
`Δ ≤ C(J^{1−η} + y)` with `C ≥ 1`, then `Δ ≤ C J^{1−η} + C J^λ y^{1−λ}`. -/
theorem jump_split_le {Δ J y C η l : ℝ} (hJ0 : 0 ≤ J) (hy0 : 0 ≤ y) (hC : 1 ≤ C) (hl0 : 0 ≤ l)
    (hl1 : l ≤ 1) (hΔJ : Δ ≤ J) (hΔC : Δ ≤ C * (J ^ (1 - η) + y)) :
    Δ ≤ C * J ^ (1 - η) + C * (J ^ l * y ^ (1 - l)) := by
  have hJp : 0 ≤ J ^ (1 - η) := Real.rpow_nonneg hJ0 _
  have hJl : 0 ≤ J ^ l * y ^ (1 - l) :=
    mul_nonneg (Real.rpow_nonneg hJ0 _) (Real.rpow_nonneg hy0 _)
  have hC0 : (0 : ℝ) ≤ C := by linarith
  have hm := min_le_rpow_mul_rpow hJ0 hy0 hl0 hl1
  rcases le_total J y with h | h
  · rw [min_eq_left h] at hm
    linarith [mul_nonneg (sub_nonneg.2 hC) hJl, mul_nonneg hC0 hJp]
  · rw [min_eq_right h] at hm
    linarith [mul_le_mul_of_nonneg_left hm hC0]

/-- The length term of the jump against the kernel: with `J ≤ 2N/K²`,
`((K^{1−η}/N) C J^{1−η})² ≤ 4C² N^{−2η} K^{2η−2}`. -/
theorem lengthTerm_sq_le {N K J C η : ℝ} (hN : 0 < N) (hK : 0 < K) (hJ0 : 0 ≤ J)
    (hJA : J ≤ 2 * (N / K ^ 2)) (h0 : 0 < η) (h1 : η < 1) :
    (K ^ (1 - η) / N * (C * J ^ (1 - η))) ^ 2 ≤
      4 * C ^ 2 * (N ^ (-2 * η) * K ^ (2 * η - 2)) := by
  have e : (K ^ (1 - η) / N * (C * J ^ (1 - η))) ^ 2 =
      C ^ 2 * ((K ^ (1 - η) / N) ^ 2 * J ^ (2 * (1 - η))) := by
    rw [← sq_rpow_eq_of_nonneg hJ0]; ring
  have hJ2 : J ^ (2 * (1 - η)) ≤ (2 * (N / K ^ 2)) ^ (2 * (1 - η)) :=
    Real.rpow_le_rpow hJ0 hJA (by linarith)
  have e2 : (K ^ (1 - η) / N) ^ 2 * (2 * (N / K ^ 2)) ^ (2 * (1 - η)) =
      2 ^ (2 * (1 - η)) * (N ^ (-2 * η) * K ^ (2 * η - 2)) := by
    rw [Real.mul_rpow (by norm_num) (by positivity), sq_kernelFactor_eq hN hK,
      ← lengthTerm_rpow_eq hN hK]
    ring
  rw [e]
  calc C ^ 2 * ((K ^ (1 - η) / N) ^ 2 * J ^ (2 * (1 - η)))
      ≤ C ^ 2 * ((K ^ (1 - η) / N) ^ 2 * (2 * (N / K ^ 2)) ^ (2 * (1 - η))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hJ2 (sq_nonneg _)) (sq_nonneg C)
    _ = C ^ 2 * (2 ^ (2 * (1 - η)) * (N ^ (-2 * η) * K ^ (2 * η - 2))) := by rw [e2]
    _ ≤ _ := sq_mul_le_four (two_rpow_le_four (by linarith)) (by positivity)

/-- The interpolated term of the jump against the kernel: with `J ≤ 2N/K²` and `a ≤ N/K`,
`((K^{1−η}/N) C J^λ (a^{(1−η)/2})^{1−λ})² ≤ 4C² N^α K^β`. -/
theorem interpTerm_sq_le {N K J a C η l : ℝ} (hN : 0 < N) (hK : 0 < K) (hJ0 : 0 ≤ J)
    (hJA : J ≤ 2 * (N / K ^ 2)) (ha0 : 0 ≤ a) (haN : a ≤ N / K) (hl0 : 0 ≤ l) (hl1 : l ≤ 1)
    (h1 : η < 1) :
    (K ^ (1 - η) / N * (C * (J ^ l * (a ^ ((1 - η) / 2)) ^ (1 - l)))) ^ 2 ≤
      4 * C ^ 2 * (N ^ (-2 + 2 * l + (1 - η) * (1 - l)) *
        K ^ (2 - 2 * η - 4 * l - (1 - η) * (1 - l))) := by
  have hy2 : ((a ^ ((1 - η) / 2)) ^ (1 - l)) ^ 2 = a ^ ((1 - η) * (1 - l)) := by
    rw [sq_rpow_eq_of_nonneg (Real.rpow_nonneg ha0 _), ← Real.rpow_mul ha0]; congr 1; ring
  have e : (K ^ (1 - η) / N * (C * (J ^ l * (a ^ ((1 - η) / 2)) ^ (1 - l)))) ^ 2 =
      C ^ 2 * ((K ^ (1 - η) / N) ^ 2 * (J ^ (2 * l) * a ^ ((1 - η) * (1 - l)))) := by
    rw [← hy2, ← sq_rpow_eq_of_nonneg hJ0]; ring
  have hJ2l : J ^ (2 * l) ≤ (2 * (N / K ^ 2)) ^ (2 * l) := Real.rpow_le_rpow hJ0 hJA (by linarith)
  have ha2 : a ^ ((1 - η) * (1 - l)) ≤ (N / K) ^ ((1 - η) * (1 - l)) :=
    Real.rpow_le_rpow ha0 haN (mul_nonneg (by linarith) (by linarith))
  have hprod : J ^ (2 * l) * a ^ ((1 - η) * (1 - l)) ≤
      (2 * (N / K ^ 2)) ^ (2 * l) * (N / K) ^ ((1 - η) * (1 - l)) :=
    mul_le_mul hJ2l ha2 (Real.rpow_nonneg ha0 _) (Real.rpow_nonneg (by positivity) _)
  have e2 : (K ^ (1 - η) / N) ^ 2 * ((2 * (N / K ^ 2)) ^ (2 * l) * (N / K) ^ ((1 - η) * (1 - l))) =
      2 ^ (2 * l) * (N ^ (-2 + 2 * l + (1 - η) * (1 - l)) *
        K ^ (2 - 2 * η - 4 * l - (1 - η) * (1 - l))) := by
    rw [Real.mul_rpow (by norm_num) (by positivity), sq_kernelFactor_eq hN hK,
      ← interpTerm_rpow_eq hN hK]
    ring
  rw [e]
  calc C ^ 2 * ((K ^ (1 - η) / N) ^ 2 * (J ^ (2 * l) * a ^ ((1 - η) * (1 - l))))
      ≤ C ^ 2 * ((K ^ (1 - η) / N) ^ 2 *
          ((2 * (N / K ^ 2)) ^ (2 * l) * (N / K) ^ ((1 - η) * (1 - l)))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hprod (sq_nonneg _)) (sq_nonneg C)
    _ = C ^ 2 * (2 ^ (2 * l) * (N ^ (-2 + 2 * l + (1 - η) * (1 - l)) *
          K ^ (2 - 2 * η - 4 * l - (1 - η) * (1 - l)))) := by rw [e2]
    _ ≤ _ := sq_mul_le_four (two_rpow_le_four (by linarith)) (by positivity)

/-- Region `K² ≤ N`: the sharpened source jump, squared against the kernel. -/
theorem regionA_golden_sq_le {N K J a Δ C ρ η l : ℝ} (hN : 0 < N) (hK : 0 < K) (hJ0 : 0 ≤ J)
    (hJA : J ≤ 2 * (N / K ^ 2)) (ha0 : 0 ≤ a) (haN : a ≤ N / K) (hC : 1 ≤ C) (hρ0 : 0 < ρ)
    (hl0 : 0 ≤ l) (hl1 : l ≤ 1) (h0 : 0 < η) (h1 : η < 1) (hΔ0 : 0 ≤ Δ) (hΔJ : Δ ≤ J)
    (hΔC : Δ ≤ C * (J ^ (1 - η) + a ^ ((1 - η) / 2))) :
    (K ^ (1 - η) / N * (Δ + ρ * min 2 (J + N / K ^ 2))) ^ 2 ≤
      3 * (4 * C ^ 2 * (N ^ (-2 * η) * K ^ (2 * η - 2)) +
        4 * C ^ 2 * (N ^ (-2 + 2 * l + (1 - η) * (1 - l)) *
          K ^ (2 - 2 * η - 4 * l - (1 - η) * (1 - l))) +
        4 * ρ ^ 2 * (K ^ (2 - 2 * η) * N ^ (-2 : ℝ))) := by
  have hΔ := jump_split_le hJ0 (Real.rpow_nonneg ha0 _) hC hl0 hl1 hΔJ hΔC
  have hu0 : 0 ≤ K ^ (1 - η) / N := by positivity
  have hmin : ρ * min 2 (J + N / K ^ 2) ≤ ρ * 2 :=
    mul_le_mul_of_nonneg_left (min_le_left _ _) hρ0.le
  have hmin0 : 0 ≤ ρ * min 2 (J + N / K ^ 2) :=
    mul_nonneg hρ0.le (le_min (by norm_num) (by positivity))
  have hb := mul_add_le_three hu0 hΔ hmin
  have hb0 : 0 ≤ K ^ (1 - η) / N * (Δ + ρ * min 2 (J + N / K ^ 2)) :=
    mul_nonneg hu0 (add_nonneg hΔ0 hmin0)
  have hsq := (pow_le_pow_left₀ hb0 hb 2).trans (add3_sq_le_three _ _ _)
  have hE2 : (K ^ (1 - η) / N * (ρ * 2)) ^ 2 = 4 * ρ ^ 2 * (K ^ (2 - 2 * η) * N ^ (-2 : ℝ)) := by
    rw [mul_pow, sq_kernelFactor_eq hN hK]; ring
  exact hsq.trans (mul_le_mul_of_nonneg_left (add_le_add (add_le_add
    (lengthTerm_sq_le hN hK hJ0 hJA h0 h1) (interpTerm_sq_le hN hK hJ0 hJA ha0 haN hl0 hl1 h1))
    hE2.le) (by norm_num))

/-! ### The golden interpolation exponent -/

/-- The interpolation exponent: the midpoint of `(max(0, (2−3η)/(1−η)), η/(1+η))`. -/
def goldenExp (η : ℝ) : ℝ := (max 0 ((2 - 3 * η) / (1 - η)) + η / (1 + η)) / 2

/-- **The golden window**: for `η² + η > 1` the interpolation exponent lies in `[0, 1]`, and the
interpolated term `N^α K^β` is square summable at both ends of `K ≤ √N`. -/
theorem goldenExp_bounds {η : ℝ} (h0 : 0 < η) (h1 : η < 1) (hg : 1 < η ^ 2 + η) :
    0 ≤ goldenExp η ∧ goldenExp η ≤ 1 ∧
      -2 + 2 * goldenExp η + (1 - η) * (1 - goldenExp η) < -1 ∧
      -2 + 2 * goldenExp η + (1 - η) * (1 - goldenExp η) +
        (2 - 2 * η - 4 * goldenExp η - (1 - η) * (1 - goldenExp η) + 1) / 2 < -1 := by
  set L := (2 - 3 * η) / (1 - η) with hL
  set U := η / (1 + η) with hU
  have h1η : 0 < 1 - η := by linarith
  have hU0 : 0 < U := by positivity
  have hU1 : U < 1 := by rw [hU, div_lt_one (by linarith)]; linarith
  have hLU : L < U := by
    rw [hL, hU, div_lt_div_iff₀ h1η (by linarith)]
    nlinarith
  have hm : max 0 L < U := max_lt hU0 hLU
  have hl : goldenExp η = (max 0 L + U) / 2 := rfl
  have hlU : goldenExp η < U := by rw [hl]; linarith
  have hLl : L < goldenExp η := by rw [hl]; linarith [le_max_right 0 L]
  have hl0 : 0 ≤ goldenExp η := by rw [hl]; linarith [le_max_left 0 L]
  -- `λ(1+η) < η` and `2 − 3η < λ(1−η)`
  have hA : goldenExp η * (1 + η) < η := by rwa [hU, lt_div_iff₀ (by linarith)] at hlU
  have hB : 2 - 3 * η < goldenExp η * (1 - η) := by rwa [hL, div_lt_iff₀ h1η] at hLl
  refine ⟨hl0, by linarith, by nlinarith, by nlinarith⟩

/-! ### Sums below the square root -/

/-- The exponent shift that moves `K^{2t} ≤ N^t` from the columns to the rows. -/
def belowSqrtShift (α β : ℝ) : ℝ := (max 0 ((β + 1) / 2) + (-1 - α)) / 2

/-- The constant of a sum below the square root. -/
def belowSqrtConstant (α β : ℝ) : ℝ :=
  realZetaSeries (-(α + belowSqrtShift α β)) * realZetaSeries (2 * belowSqrtShift α β - β)

/-- **Sums below the square root**: for `α < −1` and `α + (β+1)/2 < −1`,
`Σ_{K² ≤ N} N^α K^β ≤ belowSqrtConstant α β`. -/
theorem sum_belowSqrt_rpow_le {α β : ℝ} (hα : α < -1) (hαβ : α + (β + 1) / 2 < -1) (T M : ℕ) :
    ∑ n ∈ range T, ∑ k ∈ range M, (if (k + 1) * (k + 1) ≤ n + 1 then
      ((n + 1 : ℕ) : ℝ) ^ α * ((k + 1 : ℕ) : ℝ) ^ β else 0) ≤ belowSqrtConstant α β := by
  have hm := le_max_left 0 ((β + 1) / 2)
  have hm' := le_max_right 0 ((β + 1) / 2)
  have hmax : max 0 ((β + 1) / 2) < -1 - α := max_lt (by linarith) (by linarith)
  have ht0 : 0 ≤ belowSqrtShift α β := by unfold belowSqrtShift; linarith
  have hs : 1 < -(α + belowSqrtShift α β) := by unfold belowSqrtShift; linarith
  have hu : 1 < 2 * belowSqrtShift α β - β := by unfold belowSqrtShift; linarith
  refine le_trans (sum_le_sum fun n _ => sum_le_sum fun k _ => ?_) (sum_sum_rpow_le hs hu T M)
  have hK : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
  have hN : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  split_ifs with hA
  · set t := belowSqrtShift α β
    have hKN : ((k + 1 : ℕ) : ℝ) ^ (2 * t) ≤ ((n + 1 : ℕ) : ℝ) ^ t := by
      rw [Real.rpow_mul hK.le, Real.rpow_two]
      refine Real.rpow_le_rpow (sq_nonneg _) ?_ ht0
      rw [sq]; exact_mod_cast hA
    have e1 : ((k + 1 : ℕ) : ℝ) ^ β =
        ((k + 1 : ℕ) : ℝ) ^ (2 * t) * ((k + 1 : ℕ) : ℝ) ^ (-(2 * t - β)) := by
      rw [← Real.rpow_add hK]; congr 1; ring
    have e2 : ((n + 1 : ℕ) : ℝ) ^ (-(-(α + t))) =
        ((n + 1 : ℕ) : ℝ) ^ α * ((n + 1 : ℕ) : ℝ) ^ t := by
      rw [neg_neg, Real.rpow_add hN]
    rw [e1, e2]
    have := mul_le_mul_of_nonneg_left hKN (by positivity :
      (0 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) ^ α * ((k + 1 : ℕ) : ℝ) ^ (-(2 * t - β)))
    nlinarith
  · positivity

/-! ### The golden majorant -/

/-- The region-wise squared majorant of the kernel at the golden threshold. -/
def goldenMajorant (η : ℝ) (n k : ℕ) : ℝ :=
  3 * ((η * (1 + 1 / (1 - η) + 1 / η)) ^ 2 * (((n + 1 : ℕ) : ℝ) ^ (-2 * η) *
        ((k + 1 : ℕ) : ℝ) ^ (-2 : ℝ)) +
      (η * (pmPowerDampedDivisorDensity η).re) ^ 2 * (((k + 1 : ℕ) : ℝ) ^ (-2 * η) *
        ((n + 1 : ℕ) : ℝ) ^ (-2 : ℝ))) +
  3 * (if (k + 1) * (k + 1) ≤ n + 1 then
      3 * (4 * jumpConstant η ^ 2 *
          (((n + 1 : ℕ) : ℝ) ^ (-2 * η) * ((k + 1 : ℕ) : ℝ) ^ (2 * η - 2)) +
        4 * jumpConstant η ^ 2 *
          (((n + 1 : ℕ) : ℝ) ^ (-2 + 2 * goldenExp η + (1 - η) * (1 - goldenExp η)) *
            ((k + 1 : ℕ) : ℝ) ^ (2 - 2 * η - 4 * goldenExp η - (1 - η) * (1 - goldenExp η))) +
        4 * (pmPowerDampedDivisorDensity η).re ^ 2 *
          (((k + 1 : ℕ) : ℝ) ^ (2 - 2 * η) * ((n + 1 : ℕ) : ℝ) ^ (-2 : ℝ)))
    else
      2 * (1 + (pmPowerDampedDivisorDensity η).re) ^ 2 *
          (((k + 1 : ℕ) : ℝ) ^ (2 - 2 * η) * ((n + 1 : ℕ) : ℝ) ^ (-2 : ℝ) *
            ((((n + 1) / (k + 1) - (n + 1) / (k + 1 + 1) : ℕ) : ℝ))) +
        2 * (pmPowerDampedDivisorDensity η).re ^ 2 * ((k + 1 : ℕ) : ℝ) ^ (-2 - 2 * η))

/-- **The kernel is dominated by the golden majorant** for `η² + η > 1` and `η < 1`. -/
theorem sq_centeredRow_le_goldenMajorant {η : ℝ} (h0 : 0 < η) (h1 : η < 1)
    (hg : 1 < η ^ 2 + η) (n k : ℕ) :
    arithmeticDampingCenteredRow η n k ^ 2 ≤ goldenMajorant η n k := by
  have hK : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
  have hN : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  have hρ0 := RHTower.pmPowerDampedDivisorDensity_re_pos h0
  have hJ0 : (0 : ℝ) ≤ ((((n + 1) / (k + 1) - (n + 1) / (k + 1 + 1) : ℕ) : ℝ)) :=
    Nat.cast_nonneg _
  have e1 : (η * (1 + 1 / (1 - η) + 1 / η) * ((n + 1 : ℕ) : ℝ) ^ (-η) / ((k + 1 : ℕ) : ℝ)) ^ 2 =
      (η * (1 + 1 / (1 - η) + 1 / η)) ^ 2 * (((n + 1 : ℕ) : ℝ) ^ (-2 * η) *
        ((k + 1 : ℕ) : ℝ) ^ (-2 : ℝ)) := by
    rw [div_eq_mul_one_div, mul_pow, mul_pow, sq_rpow_eq hN, sq_inv_eq_rpow hK]; ring_nf
  have e2 : (η * (pmPowerDampedDivisorDensity η).re * ((k + 1 : ℕ) : ℝ) ^ (-η) /
      ((n + 1 : ℕ) : ℝ)) ^ 2 = (η * (pmPowerDampedDivisorDensity η).re) ^ 2 *
        (((k + 1 : ℕ) : ℝ) ^ (-2 * η) * ((n + 1 : ℕ) : ℝ) ^ (-2 : ℝ)) := by
    rw [div_eq_mul_one_div, mul_pow, mul_pow, sq_rpow_eq hK, sq_inv_eq_rpow hN]; ring_nf
  unfold goldenMajorant
  split_ifs with hA
  · obtain ⟨hl0, hl1, -, -⟩ := goldenExp_bounds h0 h1 hg
    have hmaj := abs_centeredRow_le_jump h0 h1 n k
    rw [div_mul_eq_mul_div, mul_rpow_neg_eq hK] at hmaj
    have hsq := (pow_le_pow_left₀ (abs_nonneg _) hmaj 2).trans (add3_sq_le_three _ _ _)
    rw [sq_abs, e1, e2] at hsq
    have haa' : (n + 1) / (k + 1 + 1) ≤ (n + 1) / (k + 1) :=
      Nat.div_le_div_left (by omega) (by omega)
    have hR := regionA_golden_sq_le hN hK hJ0 (floorJump_le_of_sq_le hA) (Nat.cast_nonneg _)
      (natDiv_le_div (n + 1) (k + 1)) (one_le_jumpConstant h0 h1) hρ0 hl0 hl1 h0 h1
      (abs_nonneg _) (abs_centeredPrefix_sub_le h0 haa')
      (abs_jump_le_belowSqrt h0 h1 (N := n + 1) (K := k + 1) (by omega) hA)
    linarith
  · have hmaj := abs_centeredRow_le_majorant h0 h1 n k
    rw [div_mul_eq_mul_div, mul_rpow_neg_eq hK] at hmaj
    have hsq := (pow_le_pow_left₀ (abs_nonneg _) hmaj 2).trans (add3_sq_le_three _ _ _)
    rw [sq_abs, e1, e2] at hsq
    have hJB : ((((n + 1) / (k + 1) - (n + 1) / (k + 1 + 1) : ℕ) : ℝ)) ≤ 1 := by
      have := div_sub_div_succ_le_one (N := n + 1) (K := k + 1) (by push Not at hA; omega)
      exact_mod_cast this
    have hC₁ : 0 ≤ 1 + 1 / (1 - η) + 1 / η := by
      have : 0 < 1 - η := by linarith
      positivity
    have hR := regionB_sq_le (η := η) (C₁ := 1 + 1 / (1 - η) + 1 / η) hN hK hJ0 hJB hC₁ hρ0
    linarith

/-! ### Summing the golden majorant -/

/-- The Hilbert–Schmidt constant of the chain at the golden threshold. -/
def goldenHSConstant (η : ℝ) : ℝ :=
  3 * ((η * (1 + 1 / (1 - η) + 1 / η)) ^ 2 * (realZetaSeries (2 * η) * realZetaSeries 2) +
      (η * (pmPowerDampedDivisorDensity η).re) ^ 2 * (realZetaSeries 2 * realZetaSeries (2 * η))) +
  3 * (12 * jumpConstant η ^ 2 * belowSqrtConstant (-(2 * η)) (2 * η - 2) +
      12 * jumpConstant η ^ 2 *
        belowSqrtConstant (-2 + 2 * goldenExp η + (1 - η) * (1 - goldenExp η))
          (2 - 2 * η - 4 * goldenExp η - (1 - η) * (1 - goldenExp η)) +
      12 * (pmPowerDampedDivisorDensity η).re ^ 2 * realZetaSeries ((1 + 2 * η) / 2) +
      2 * (1 + (pmPowerDampedDivisorDensity η).re) ^ 2 * ((1 + 1 / (2 * η - 1)) *
        realZetaSeries ((1 + 2 * η) / 2)) +
      2 * (pmPowerDampedDivisorDensity η).re ^ 2 * realZetaSeries (2 * η))

theorem sum_sum_linear7 (T M : ℕ) (a b c d e f g : ℝ) (F1 F2 F3 F4 F5 F6 F7 : ℕ → ℕ → ℝ) :
    ∑ n ∈ range T, ∑ k ∈ range M, (3 * (a * F1 n k + b * F2 n k) +
      3 * (c * F3 n k + d * F4 n k + e * F5 n k + f * F6 n k + g * F7 n k)) =
    3 * (a * ∑ n ∈ range T, ∑ k ∈ range M, F1 n k + b * ∑ n ∈ range T, ∑ k ∈ range M, F2 n k) +
    3 * (c * ∑ n ∈ range T, ∑ k ∈ range M, F3 n k + d * ∑ n ∈ range T, ∑ k ∈ range M, F4 n k +
      e * ∑ n ∈ range T, ∑ k ∈ range M, F5 n k + f * ∑ n ∈ range T, ∑ k ∈ range M, F6 n k +
      g * ∑ n ∈ range T, ∑ k ∈ range M, F7 n k) := by
  simp only [sum_add_distrib, mul_sum, mul_add]

/-- **The golden majorant is summable**: every partial double sum is at most
`goldenHSConstant η`. -/
theorem sum_goldenMajorant_le {η : ℝ} (h0 : 0 < η) (h1 : η < 1) (hg : 1 < η ^ 2 + η)
    (T M : ℕ) : ∑ n ∈ range T, ∑ k ∈ range M, goldenMajorant η n k ≤ goldenHSConstant η := by
  have hh : 1 / 2 < η := by nlinarith
  obtain ⟨-, -, hα, hαβ⟩ := goldenExp_bounds h0 h1 hg
  have hite : ∀ n k, goldenMajorant η n k =
      3 * ((η * (1 + 1 / (1 - η) + 1 / η)) ^ 2 *
          (((n + 1 : ℕ) : ℝ) ^ (-(2 * η)) * ((k + 1 : ℕ) : ℝ) ^ (-(2 : ℝ))) +
        (η * (pmPowerDampedDivisorDensity η).re) ^ 2 *
          (((n + 1 : ℕ) : ℝ) ^ (-(2 : ℝ)) * ((k + 1 : ℕ) : ℝ) ^ (-(2 * η)))) +
      3 * (12 * jumpConstant η ^ 2 * (if (k + 1) * (k + 1) ≤ n + 1 then
            ((n + 1 : ℕ) : ℝ) ^ (-(2 * η)) * ((k + 1 : ℕ) : ℝ) ^ (2 * η - 2) else 0) +
        12 * jumpConstant η ^ 2 * (if (k + 1) * (k + 1) ≤ n + 1 then
            ((n + 1 : ℕ) : ℝ) ^ (-2 + 2 * goldenExp η + (1 - η) * (1 - goldenExp η)) *
              ((k + 1 : ℕ) : ℝ) ^ (2 - 2 * η - 4 * goldenExp η - (1 - η) * (1 - goldenExp η))
            else 0) +
        12 * (pmPowerDampedDivisorDensity η).re ^ 2 * (((n + 1 : ℕ) : ℝ) ^ (-(2 : ℝ)) *
          (if (k + 1) * (k + 1) ≤ n + 1 then ((k + 1 : ℕ) : ℝ) ^ (2 - 2 * η) else 0)) +
        2 * (1 + (pmPowerDampedDivisorDensity η).re) ^ 2 * (((n + 1 : ℕ) : ℝ) ^ (-(2 : ℝ)) *
          (if (k + 1) * (k + 1) ≤ n + 1 then 0 else ((k + 1 : ℕ) : ℝ) ^ (2 - 2 * η) *
            ((((n + 1) / (k + 1) - (n + 1) / (k + 1 + 1) : ℕ) : ℝ)))) +
        2 * (pmPowerDampedDivisorDensity η).re ^ 2 * (if (k + 1) * (k + 1) ≤ n + 1 then 0 else
          ((k + 1 : ℕ) : ℝ) ^ (-2 - 2 * η))) := by
    intro n k
    unfold goldenMajorant
    rw [show (-2 : ℝ) * η = -(2 * η) by ring]
    split_ifs <;> ring
  refine (le_of_eq (sum_congr rfl fun n _ => sum_congr rfl fun k _ => hite n k)).trans ?_
  refine (le_of_eq (sum_sum_linear7 T M ((η * (1 + 1 / (1 - η) + 1 / η)) ^ 2)
    ((η * (pmPowerDampedDivisorDensity η).re) ^ 2) (12 * jumpConstant η ^ 2)
    (12 * jumpConstant η ^ 2) (12 * (pmPowerDampedDivisorDensity η).re ^ 2)
    (2 * (1 + (pmPowerDampedDivisorDensity η).re) ^ 2)
    (2 * (pmPowerDampedDivisorDensity η).re ^ 2)
    (fun n k => ((n + 1 : ℕ) : ℝ) ^ (-(2 * η)) * ((k + 1 : ℕ) : ℝ) ^ (-(2 : ℝ)))
    (fun n k => ((n + 1 : ℕ) : ℝ) ^ (-(2 : ℝ)) * ((k + 1 : ℕ) : ℝ) ^ (-(2 * η)))
    (fun n k => if (k + 1) * (k + 1) ≤ n + 1 then
      ((n + 1 : ℕ) : ℝ) ^ (-(2 * η)) * ((k + 1 : ℕ) : ℝ) ^ (2 * η - 2) else 0)
    (fun n k => if (k + 1) * (k + 1) ≤ n + 1 then
      ((n + 1 : ℕ) : ℝ) ^ (-2 + 2 * goldenExp η + (1 - η) * (1 - goldenExp η)) *
        ((k + 1 : ℕ) : ℝ) ^ (2 - 2 * η - 4 * goldenExp η - (1 - η) * (1 - goldenExp η)) else 0)
    (fun n k => ((n + 1 : ℕ) : ℝ) ^ (-(2 : ℝ)) *
      (if (k + 1) * (k + 1) ≤ n + 1 then ((k + 1 : ℕ) : ℝ) ^ (2 - 2 * η) else 0))
    (fun n k => ((n + 1 : ℕ) : ℝ) ^ (-(2 : ℝ)) *
      (if (k + 1) * (k + 1) ≤ n + 1 then 0 else ((k + 1 : ℕ) : ℝ) ^ (2 - 2 * η) *
        ((((n + 1) / (k + 1) - (n + 1) / (k + 1 + 1) : ℕ) : ℝ))))
    (fun n k => if (k + 1) * (k + 1) ≤ n + 1 then 0 else
      ((k + 1 : ℕ) : ℝ) ^ (-2 - 2 * η)))).trans ?_
  -- the seven families
  have hA1 := sum_sum_rpow_le (s := 2 * η) (t := 2) (by linarith) one_lt_two T M
  have hA2 := sum_sum_rpow_le (s := 2) (t := 2 * η) one_lt_two (by linarith) T M
  have hA3 := sum_belowSqrt_rpow_le (α := -(2 * η)) (β := 2 * η - 2) (by linarith)
    (by linarith) T M
  have hA4 := sum_belowSqrt_rpow_le hα hαβ T M
  have hB := sum_sum_belowSqrt_le h1 hh T M
  have hC := sum_sum_aboveSqrt_le h1 hh T M
  have hD := sum_above_sqrt_tail_le hh T M
  unfold goldenHSConstant
  exact add_le_add
    (mul_le_mul_of_nonneg_left (add_le_add
      (mul_le_mul_of_nonneg_left hA1 (sq_nonneg _))
      (mul_le_mul_of_nonneg_left hA2 (sq_nonneg _))) (by norm_num))
    (mul_le_mul_of_nonneg_left (add_le_add (add_le_add (add_le_add (add_le_add
      (mul_le_mul_of_nonneg_left hA3 (by positivity))
      (mul_le_mul_of_nonneg_left hA4 (by positivity)))
      (mul_le_mul_of_nonneg_left hB (by positivity)))
      (mul_le_mul_of_nonneg_left hC (by positivity)))
      (mul_le_mul_of_nonneg_left hD (by positivity))) (by norm_num))

/-- **The chain is bounded in `ℓ²` above the golden threshold**: for `η² + η > 1`, `η < 1`,
finitely supported `b` and every horizon, `Σ_{n<T} (C_η b)(n)² ≤ M_η Σ_k b_k²`. -/
theorem centeredOperator_l2_le_of_goldenThreshold {η : ℝ} (h0 : 0 < η) (h1 : η < 1)
    (hg : 1 < η ^ 2 + η) (b : C₀(ℕ, ℝ)) {N : ℕ} (hb : ∀ k, N ≤ k → b k = 0) (T : ℕ) :
    ∑ n ∈ range T, arithmeticDampingCenteredOperator h0 b n ^ 2 ≤
      goldenHSConstant η * ∑ k ∈ range N, b k ^ 2 := by
  have happ : ∀ n, arithmeticDampingCenteredOperator h0 b n =
      ∑ k ∈ range N, arithmeticDampingCenteredRow η n k * b k := by
    intro n
    rw [arithmeticDampingCenteredOperator_apply]
    exact tsum_eq_sum fun k hk => by rw [hb k (by simpa using hk), mul_zero]
  have hrow : ∀ n, arithmeticDampingCenteredOperator h0 b n ^ 2 ≤
      (∑ k ∈ range N, arithmeticDampingCenteredRow η n k ^ 2) * ∑ k ∈ range N, b k ^ 2 := by
    intro n; rw [happ]; exact sum_mul_sq_le_sq_mul_sq _ _ _
  have hb0 : 0 ≤ ∑ k ∈ range N, b k ^ 2 := sum_nonneg fun k _ => sq_nonneg _
  have hHS : ∑ n ∈ range T, ∑ k ∈ range N, arithmeticDampingCenteredRow η n k ^ 2 ≤
      goldenHSConstant η :=
    (sum_le_sum fun n _ => sum_le_sum fun k _ =>
      sq_centeredRow_le_goldenMajorant h0 h1 hg n k).trans (sum_goldenMajorant_le h0 h1 hg T N)
  calc ∑ n ∈ range T, arithmeticDampingCenteredOperator h0 b n ^ 2
      ≤ ∑ n ∈ range T, (∑ k ∈ range N, arithmeticDampingCenteredRow η n k ^ 2) *
          ∑ k ∈ range N, b k ^ 2 := sum_le_sum fun n _ => hrow n
    _ = (∑ n ∈ range T, ∑ k ∈ range N, arithmeticDampingCenteredRow η n k ^ 2) *
          ∑ k ∈ range N, b k ^ 2 := by rw [← sum_mul]
    _ ≤ goldenHSConstant η * ∑ k ∈ range N, b k ^ 2 := mul_le_mul_of_nonneg_right hHS hb0

end

end GaloisForLFunctions.SignedArithmeticEnergyIncidence
