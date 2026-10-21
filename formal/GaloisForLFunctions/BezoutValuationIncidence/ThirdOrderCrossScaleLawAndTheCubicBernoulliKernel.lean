import GaloisForLFunctions.BezoutValuationIncidence.ResidueDiscrepancyIsTheExactCrossScaleLoss

/-!
# The third-order cross-scale law and the cubic Bernoulli kernel

The residue potential `Φ_d(M) = (d²/2) B₂(ρ/d) - 1/12` (`ρ = M mod d`) has zero sums over periods, so it
has a periodic primitive. Centred to have zero period sums, it is the **cubic potential**

`Ψ_d(M) = (4ρ³ - 6(d - 1)ρ² + 2d(d - 3)ρ + d² - 1)/24 = (d³/6) B₃(ρ/d) + Φ_d(M)/2`,

with `Ψ_d(M + 1) - Ψ_d(M) = Φ_d(M + 1)`, `|Ψ_d| ≤ d³/6` and interval sums at most `d⁴/6`. One more
summation by parts against the first difference `Δw(M) = 2/(M(M+1)(M+2))` of the pronic weight gives,
for `1 ≤ A`,

`Σ_{M ≥ A} r_d(M) w(M) = -Φ_d(A)/A² - (2Ψ_d(A) - Φ_d(A))/A³ + O(d⁴/A⁴)`.

With the **cubic Bernoulli kernel**

`𝔅₃(d, n) = Σ_{j ≥ 1} (2Ψ_d(jn) - Φ_d(jn))/j³ = (d³/3) Σ_{j ≥ 1} B₃({jn/d})/j³`,

which, like `𝔅`, depends on `n` only through `n mod d`, every pair of rows satisfies

`|B(c, c') + m(c) R(c') + β(c) H(c') - Σ_{n, d} c'(n) (c(d)/d) (𝔅(d, n)/n² + 𝔅₃(d, n)/n³)|
  ≤ 6 (Σ_d |c(d)| d³)(Σ_n |c'(n)|/n⁴)`.

The error of the second-order law, `¾ Σ|c| d² Σ|c'|/n³`, is the cubic kernel term. It is replaced by
one smaller by the factor `d/n`. Up to `O(d³/n⁴)` the cross-scale form is a function of the residue
classes of the large moduli modulo the small ones, now at the two weights `n⁻²` and `n⁻³`.
-/

open Finset Filter Topology RHTower GaloisForLFunctions.BiScaleUncertainty
open scoped BigOperators

namespace GaloisForLFunctions.BezoutValuationIncidence

noncomputable section
set_option autoImplicit false

/-! ## §1. The cubic potential -/

/-- The cubic potential `Ψ_d(M) = (4ρ³ - 6(d-1)ρ² + 2d(d-3)ρ + d² - 1)/24`, `ρ = M mod d`. -/
def cubicPotential (d M : ℕ) : ℝ :=
  (4 * ((M % d : ℕ) : ℝ) ^ 3 - 6 * ((d : ℝ) - 1) * ((M % d : ℕ) : ℝ) ^ 2 +
    2 * (d : ℝ) * ((d : ℝ) - 3) * ((M % d : ℕ) : ℝ) + (d : ℝ) ^ 2 - 1) / 24

/-- The cubic potential is a primitive of the residue potential: `Ψ_d(M+1) - Ψ_d(M) = Φ_d(M+1)`. -/
theorem cubicPotential_succ_sub {d : ℕ} (hd : 0 < d) (M : ℕ) :
    cubicPotential d (M + 1) - cubicPotential d M = residuePotential d (M + 1) := by
  have hlt := Nat.mod_lt M hd
  unfold cubicPotential residuePotential
  rcases Nat.lt_or_ge (M % d + 1) d with h | h
  · have hm : (M + 1) % d = M % d + 1 := by
      rw [Nat.add_mod, Nat.mod_eq_of_lt (show 1 < d by omega), Nat.mod_eq_of_lt h]
    rw [hm]
    push_cast
    ring
  · have hr : M % d + 1 = d := by omega
    have hm : (M + 1) % d = 0 := by
      have h' : M + 1 = d * (M / d + 1) := by
        have := Nat.div_add_mod M d
        rw [mul_add, mul_one]; omega
      rw [h', Nat.mul_mod_right]
    have hrR : ((M % d : ℕ) : ℝ) = (d : ℝ) - 1 := by
      have := congrArg (Nat.cast : ℕ → ℝ) hr
      push_cast at this; linarith
    rw [hm, hrR]
    push_cast
    ring

theorem cubicPotential_add_period (d M : ℕ) : cubicPotential d (M + d) = cubicPotential d M := by
  simp [cubicPotential, Nat.add_mod_right]

/-- `2Ψ_d(M) - Φ_d(M) = (d³/3) B₃(ρ/d)` with `B₃(x) = x³ - (3/2)x² + x/2`. -/
theorem two_mul_cubicPotential_sub_eq {d : ℕ} (hd : 0 < d) (M : ℕ) :
    2 * cubicPotential d M - residuePotential d M =
      (d : ℝ) ^ 3 / 3 * ((((M % d : ℕ) : ℝ) / d) ^ 3 - 3 / 2 * (((M % d : ℕ) : ℝ) / d) ^ 2 +
        (((M % d : ℕ) : ℝ) / d) / 2) := by
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  unfold cubicPotential residuePotential
  field_simp
  ring

theorem sum_range_cast_cube_eq (n : ℕ) :
    ∑ i ∈ range n, (i : ℝ) ^ 3 = ((n : ℝ) * ((n : ℝ) - 1) / 2) ^ 2 := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

theorem sum_Ico_cubicPotential_period {d : ℕ} (hd : 0 < d) (N : ℕ) :
    ∑ M ∈ Ico N (N + d), cubicPotential d M = 0 := by
  induction N with
  | zero =>
    rw [zero_add, ← Finset.range_eq_Ico]
    rw [sum_congr rfl fun M hM => by rw [cubicPotential, Nat.mod_eq_of_lt (mem_range.mp hM)]]
    rw [← sum_div]
    simp only [sum_add_distrib, sum_sub_distrib, ← mul_sum, sum_const, card_range, nsmul_eq_mul]
    rw [sum_range_cast_eq, sum_range_cast_sq_eq, sum_range_cast_cube_eq]
    ring
  | succ N ih =>
    rw [show N + 1 + d = N + d + 1 by ring, sum_Ico_succ_top (by omega),
      ← sum_Ico_consecutive _ (Nat.le_succ N) (by omega : N + 1 ≤ N + d)] at *
    have hN : ∑ M ∈ Ico N (N + 1), cubicPotential d M = cubicPotential d N := by simp
    have hper := cubicPotential_add_period d N
    linarith

theorem abs_cubicPotential_le {d : ℕ} (hd : 0 < d) (M : ℕ) :
    |cubicPotential d M| ≤ (d : ℝ) ^ 3 / 6 := by
  have hlt := Nat.mod_lt M hd
  set ρ : ℝ := ((M % d : ℕ) : ℝ)
  have hr0 : 0 ≤ ρ := Nat.cast_nonneg _
  have hrd : ρ ≤ d := by simp only [ρ]; exact_mod_cast hlt.le
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have e : cubicPotential d M =
      (2 * (ρ * (2 * ρ - d) * (ρ - d)) + (6 * ρ ^ 2 - 6 * d * ρ + (d : ℝ) ^ 2 - 1)) / 24 := by
    simp only [cubicPotential, ρ]; ring
  have hP : |ρ * (2 * ρ - d) * (ρ - d)| ≤ (d : ℝ) ^ 3 := by
    rw [abs_mul, abs_mul, abs_of_nonneg hr0]
    have h1 : |2 * ρ - d| ≤ d := abs_le.mpr ⟨by linarith, by linarith⟩
    have h2 : |ρ - d| ≤ d := abs_le.mpr ⟨by linarith, by linarith⟩
    calc ρ * |2 * ρ - d| * |ρ - d| ≤ d * d * d := by gcongr
      _ = (d : ℝ) ^ 3 := by ring
  have hQ : |6 * ρ ^ 2 - 6 * d * ρ + (d : ℝ) ^ 2 - 1| ≤ (d : ℝ) ^ 2 + 1 :=
    abs_le.mpr ⟨by nlinarith [sq_nonneg (2 * ρ - d), sq_nonneg (d : ℝ)],
      by nlinarith [mul_nonneg hr0 (sub_nonneg.mpr hrd)]⟩
  rw [e, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 24)]
  have := abs_add_le (2 * (ρ * (2 * ρ - d) * (ρ - d))) (6 * ρ ^ 2 - 6 * d * ρ + (d : ℝ) ^ 2 - 1)
  rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at this
  rw [div_le_div_iff₀ (by norm_num) (by norm_num)]
  have h3 : (d : ℝ) ^ 2 ≤ (d : ℝ) ^ 3 := by
    nlinarith [mul_le_mul_of_nonneg_left hd1 (by positivity : (0 : ℝ) ≤ (d : ℝ) ^ 2)]
  have h4 : (1 : ℝ) ≤ (d : ℝ) ^ 3 := one_le_pow₀ hd1
  linarith

/-- Interval sums of the cubic potential are at most `d⁴/6`. -/
theorem abs_sum_Ico_cubicPotential_le {d : ℕ} (hd : 0 < d) (N K : ℕ) :
    |∑ M ∈ Ico N (N + K), cubicPotential d M| ≤ (d : ℝ) ^ 4 / 6 := by
  induction K using Nat.strong_induction_on generalizing N with
  | _ K ih =>
    by_cases hK : K < d
    · calc |∑ M ∈ Ico N (N + K), cubicPotential d M|
          ≤ ∑ M ∈ Ico N (N + K), |cubicPotential d M| := abs_sum_le_sum_abs _ _
        _ ≤ ∑ _M ∈ Ico N (N + K), (d : ℝ) ^ 3 / 6 :=
          sum_le_sum fun M _ => abs_cubicPotential_le hd M
        _ = K * ((d : ℝ) ^ 3 / 6) := by rw [sum_const, Nat.card_Ico]; simp
        _ ≤ (d : ℝ) ^ 4 / 6 := by
          have : (K : ℝ) ≤ d := by exact_mod_cast hK.le
          have : (0 : ℝ) ≤ (d : ℝ) ^ 3 := by positivity
          nlinarith
    · replace hK := not_lt.mp hK
      rw [show N + K = (N + d) + (K - d) by omega,
        ← sum_Ico_consecutive _ (by omega : N ≤ N + d) (by omega : N + d ≤ N + d + (K - d)),
        sum_Ico_cubicPotential_period hd N, zero_add]
      exact ih (K - d) (by omega) (N + d)

/-! ## §2. The third summation by parts -/

/-- Summation by parts: `Σ_{A ≤ M ≤ A+k} (X(M+1) - X(M)) u(M)
= X(A+k+1) u(A+k) - X(A) u(A) + Σ_{A ≤ M < A+k} X(M+1)(u(M) - u(M+1))`. -/
theorem sum_Ico_sub_mul_eq (X u : ℕ → ℝ) (A k : ℕ) :
    ∑ M ∈ Ico A (A + k + 1), (X (M + 1) - X M) * u M =
      X (A + k + 1) * u (A + k) - X A * u A + ∑ M ∈ Ico A (A + k), X (M + 1) * (u M - u (M + 1)) := by
  induction k with
  | zero =>
    simp only [add_zero, Ico_self, sum_empty]
    rw [sum_Ico_succ_top le_rfl, Ico_self, sum_empty, zero_add]
    ring
  | succ k ih =>
    rw [show A + (k + 1) + 1 = A + k + 1 + 1 by ring, sum_Ico_succ_top (by omega), ih,
      show A + (k + 1) = A + k + 1 by ring, sum_Ico_succ_top (by omega : A ≤ A + k)]
    ring

theorem pw_second_diff {M : ℕ} (hM : 1 ≤ M) :
    (pw M - pw (M + 1)) - (pw (M + 1) - pw (M + 1 + 1)) =
      6 / ((M : ℝ) * ((M : ℝ) + 1) * ((M : ℝ) + 2) * ((M : ℝ) + 3)) := by
  rw [pw_sub_pw_succ hM, pw_sub_pw_succ (by omega)]
  have : (0 : ℝ) < M := by exact_mod_cast hM
  push_cast
  field_simp
  ring

theorem pw_sub_pw_succ_le_two_mul {M : ℕ} (hM : 1 ≤ M) : pw M - pw (M + 1) ≤ 2 * pw (M + 1) := by
  rw [pw_sub_pw_succ hM, pw]
  have : (1 : ℝ) ≤ M := by exact_mod_cast hM
  push_cast
  rw [mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_pos (by linarith : (0 : ℝ) < (M : ℝ) + 1) (by linarith : (0 : ℝ) < (M : ℝ) + 2)]

/-- **The third-order step.** For `1 ≤ A`,
`|Σ_{A ≤ M < H} r_d(M) w(M) + 1[A < H](Φ_d(A)/A² + (2Ψ_d(A) - Φ_d(A))/A³)|
  ≤ 1[A < H](d²/8 + d³/3) w(H-1) + 3d⁴/A⁴`. -/
theorem abs_sum_Ico_centeredResidue_mul_pw_add_third_le {d A : ℕ} (hd : 0 < d) (hA : 1 ≤ A)
    (H : ℕ) :
    |∑ M ∈ Ico A H, centeredResidue d M * pw M +
        (if A < H then residuePotential d A / (A : ℝ) ^ 2 +
          (2 * cubicPotential d A - residuePotential d A) / (A : ℝ) ^ 3 else 0)| ≤
      (if A < H then ((d : ℝ) ^ 2 / 8 + (d : ℝ) ^ 3 / 3) * pw (H - 1) else 0) +
        3 * (d : ℝ) ^ 4 / (A : ℝ) ^ 4 := by
  have hAR : (1 : ℝ) ≤ A := by exact_mod_cast hA
  have hA0 : (0 : ℝ) < A := by linarith
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  -- the two expansion errors
  have hpw : |1 / (A : ℝ) ^ 2 - 1 / (A : ℝ) ^ 3 - pw A| ≤ 1 / (A : ℝ) ^ 4 := by
    unfold pw
    rw [show 1 / (A : ℝ) ^ 2 - 1 / (A : ℝ) ^ 3 - 1 / ((A : ℝ) * ((A : ℝ) + 1)) =
        -(1 / ((A : ℝ) ^ 3 * ((A : ℝ) + 1))) by field_simp; ring, abs_neg,
      abs_of_nonneg (by positivity)]
    exact one_div_le_one_div_of_le (by positivity) (by nlinarith [pow_pos hA0 3])
  have hΔ : |2 / (A : ℝ) ^ 3 - (pw A - pw (A + 1))| ≤ 6 / (A : ℝ) ^ 4 := by
    rw [pw_sub_pw_succ hA]
    rw [show 2 / (A : ℝ) ^ 3 - 2 / ((A : ℝ) * ((A : ℝ) + 1) * ((A : ℝ) + 2)) =
        2 * (3 * (A : ℝ) + 2) / ((A : ℝ) ^ 3 * ((A : ℝ) + 1) * ((A : ℝ) + 2)) by field_simp; ring,
      abs_of_nonneg (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [pow_pos hA0 3, pow_pos hA0 4, pow_pos hA0 5]
  have hΦA := abs_residuePotential_le hd A
  have hΨA := abs_cubicPotential_le hd A
  have hexp : |residuePotential d A * (1 / (A : ℝ) ^ 2 - 1 / (A : ℝ) ^ 3 - pw A) +
      cubicPotential d A * (2 / (A : ℝ) ^ 3 - (pw A - pw (A + 1)))| ≤
      ((d : ℝ) ^ 2 / 8 + (d : ℝ) ^ 3) / (A : ℝ) ^ 4 := by
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul]
    calc |residuePotential d A| * |1 / (A : ℝ) ^ 2 - 1 / (A : ℝ) ^ 3 - pw A| +
          |cubicPotential d A| * |2 / (A : ℝ) ^ 3 - (pw A - pw (A + 1))|
        ≤ (d : ℝ) ^ 2 / 8 * (1 / (A : ℝ) ^ 4) + (d : ℝ) ^ 3 / 6 * (6 / (A : ℝ) ^ 4) := by
          gcongr
      _ = _ := by ring
  have hfin : ((d : ℝ) ^ 2 / 8 + (d : ℝ) ^ 3) / (A : ℝ) ^ 4 + (d : ℝ) ^ 4 / (A : ℝ) ^ 4 ≤
      3 * (d : ℝ) ^ 4 / (A : ℝ) ^ 4 := by
    rw [← add_div, div_le_div_iff_of_pos_right (by positivity)]
    nlinarith [pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hd1 2,
      pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hd1 3,
      mul_le_mul_of_nonneg_left hd1 (by positivity : (0 : ℝ) ≤ (d : ℝ) ^ 2),
      mul_le_mul_of_nonneg_left hd1 (by positivity : (0 : ℝ) ≤ (d : ℝ) ^ 3)]
  have hΔ0 := pw_sub_pw_succ_nonneg hA
  split_ifs with hAH
  · obtain ⟨k, rfl⟩ : ∃ k, H = A + k + 1 := ⟨H - A - 1, by omega⟩
    rw [sum_Ico_centeredResidue_mul_pw_eq hd A k, show A + k + 1 - 1 = A + k by omega]
    rcases Nat.eq_zero_or_pos k with hk | hk
    · -- `H = A + 1`
      subst hk
      simp only [add_zero, Ico_self, sum_empty]
      have hb1 : |residuePotential d (A + 1)| * pw A ≤ (d : ℝ) ^ 2 / 8 * pw A :=
        mul_le_mul_of_nonneg_right (abs_residuePotential_le hd _) (pw_nonneg _)
      have hb2 : |cubicPotential d A| * (pw A - pw (A + 1)) ≤ (d : ℝ) ^ 3 / 3 * pw A := by
        have h2 : pw A - pw (A + 1) ≤ 2 * pw A := by
          have := pw_nonneg (A + 1); linarith
        calc |cubicPotential d A| * (pw A - pw (A + 1)) ≤ (d : ℝ) ^ 3 / 6 * (2 * pw A) :=
              mul_le_mul hΨA h2 hΔ0 (by positivity)
          _ = (d : ℝ) ^ 3 / 3 * pw A := by ring
      have hsplit : residuePotential d (A + 1) * pw A - residuePotential d A * pw A +
          (residuePotential d A / (A : ℝ) ^ 2 +
            (2 * cubicPotential d A - residuePotential d A) / (A : ℝ) ^ 3) =
          residuePotential d (A + 1) * pw A + cubicPotential d A * (pw A - pw (A + 1)) +
            (residuePotential d A * (1 / (A : ℝ) ^ 2 - 1 / (A : ℝ) ^ 3 - pw A) +
              cubicPotential d A * (2 / (A : ℝ) ^ 3 - (pw A - pw (A + 1)))) := by ring
      rw [hsplit]
      calc |residuePotential d (A + 1) * pw A + cubicPotential d A * (pw A - pw (A + 1)) +
            (residuePotential d A * (1 / (A : ℝ) ^ 2 - 1 / (A : ℝ) ^ 3 - pw A) +
              cubicPotential d A * (2 / (A : ℝ) ^ 3 - (pw A - pw (A + 1))))|
          ≤ |residuePotential d (A + 1)| * pw A + |cubicPotential d A| * (pw A - pw (A + 1)) +
              ((d : ℝ) ^ 2 / 8 + (d : ℝ) ^ 3) / (A : ℝ) ^ 4 := by
            refine (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans ?_) hexp)
            rw [abs_mul, abs_mul, abs_of_nonneg (pw_nonneg _), abs_of_nonneg hΔ0]
        _ ≤ ((d : ℝ) ^ 2 / 8 + (d : ℝ) ^ 3 / 3) * pw A +
              (((d : ℝ) ^ 2 / 8 + (d : ℝ) ^ 3) / (A : ℝ) ^ 4 + (d : ℝ) ^ 4 / (A : ℝ) ^ 4) := by
            have : (0 : ℝ) ≤ (d : ℝ) ^ 4 / (A : ℝ) ^ 4 := by positivity
            nlinarith
        _ ≤ ((d : ℝ) ^ 2 / 8 + (d : ℝ) ^ 3 / 3) * pw A + 3 * (d : ℝ) ^ 4 / (A : ℝ) ^ 4 := by
            linarith
    · -- `H ≥ A + 2`
      obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      set u : ℕ → ℝ := fun M => pw M - pw (M + 1)
      have hparts : ∑ M ∈ Ico A (A + (k' + 1)), residuePotential d (M + 1) * (pw M - pw (M + 1)) =
          cubicPotential d (A + k' + 1) * u (A + k') - cubicPotential d A * u A +
            ∑ M ∈ Ico A (A + k'), cubicPotential d (M + 1) * (u M - u (M + 1)) := by
        rw [← sum_Ico_sub_mul_eq (cubicPotential d) u A k', show A + (k' + 1) = A + k' + 1 by ring]
        exact sum_congr rfl fun M _ => by rw [cubicPotential_succ_sub hd M]
      rw [hparts]
      set I := ∑ M ∈ Ico A (A + k'), cubicPotential d (M + 1) * (u M - u (M + 1))
      -- the interior Abel bound
      have hI : |I| ≤ (d : ℝ) ^ 4 / (A : ℝ) ^ 4 := by
        set g : ℕ → ℝ := fun i => u (A + i) - u (A + i + 1)
        set x : ℕ → ℝ := fun i => cubicPotential d (A + i + 1)
        have hg : ∀ i, g i = 6 / (((A + i : ℕ) : ℝ) * (((A + i : ℕ) : ℝ) + 1) *
            (((A + i : ℕ) : ℝ) + 2) * (((A + i : ℕ) : ℝ) + 3)) := fun i => by
          simp only [g, u]
          rw [← pw_second_diff (by omega : 1 ≤ A + i)]
        have hg0 : ∀ i, 0 ≤ g i := fun i => by rw [hg]; positivity
        have hanti : Antitone g := by
          refine antitone_nat_of_succ_le fun i => ?_
          rw [hg, hg]
          refine div_le_div_of_nonneg_left (by norm_num) (by positivity) ?_
          push_cast
          have h1 : (1 : ℝ) ≤ (A : ℝ) + i := by
            have : (1 : ℝ) ≤ ((A + i : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ A + i)
            push_cast at this; exact this
          have hm : ∀ a b : ℝ, 0 ≤ a → a ≤ b → ∀ c : ℝ, 0 ≤ c →
              a * c ≤ b * c := fun a b ha hab c hc => mul_le_mul_of_nonneg_right hab hc
          gcongr <;> linarith
        have hx : ∀ N L, |∑ i ∈ Ico N (N + L), x i| ≤ (d : ℝ) ^ 4 / 6 := by
          intro N L
          have h := abs_sum_Ico_cubicPotential_le hd (A + N + 1) L
          rw [sum_Ico_eq_sum_range] at h ⊢
          simp only [x, show N + L - N = L by omega,
            show A + N + 1 + L - (A + N + 1) = L by omega] at h ⊢
          convert h using 3 with i
          ring_nf
        have habel := abs_sum_Ico_mul_antitone_le (by positivity) hg0 hanti hx 0 k'
        have hre : I = ∑ i ∈ Ico 0 k', g i * x i := by
          simp only [I]
          rw [sum_Ico_eq_sum_range, sum_Ico_eq_sum_range]
          simp only [g, x, u, show A + k' - A = k' by omega, Nat.sub_zero, zero_add]
          exact sum_congr rfl fun i _ => by ring
        rw [hre]
        refine habel.trans ?_
        have hg00 : g 0 ≤ 6 / (A : ℝ) ^ 4 := by
          rw [hg]
          simp only [add_zero]
          refine div_le_div_of_nonneg_left (by norm_num) (by positivity) ?_
          nlinarith [pow_pos hA0 2, pow_pos hA0 3, pow_pos hA0 4]
        calc (d : ℝ) ^ 4 / 6 * g 0 ≤ (d : ℝ) ^ 4 / 6 * (6 / (A : ℝ) ^ 4) :=
              mul_le_mul_of_nonneg_left hg00 (by positivity)
          _ = (d : ℝ) ^ 4 / (A : ℝ) ^ 4 := by ring
      have hb1 : |residuePotential d (A + (k' + 1) + 1)| * pw (A + (k' + 1)) ≤
          (d : ℝ) ^ 2 / 8 * pw (A + (k' + 1)) :=
        mul_le_mul_of_nonneg_right (abs_residuePotential_le hd _) (pw_nonneg _)
      have hb2 : |cubicPotential d (A + k' + 1)| * u (A + k') ≤
          (d : ℝ) ^ 3 / 3 * pw (A + (k' + 1)) := by
        have hu0 : 0 ≤ u (A + k') := pw_sub_pw_succ_nonneg (by omega)
        have hu : u (A + k') ≤ 2 * pw (A + (k' + 1)) := by
          simp only [u]
          rw [show A + (k' + 1) = A + k' + 1 by ring]
          exact pw_sub_pw_succ_le_two_mul (by omega)
        calc |cubicPotential d (A + k' + 1)| * u (A + k') ≤ (d : ℝ) ^ 3 / 6 * (2 * pw (A + (k' + 1))) :=
              mul_le_mul (abs_cubicPotential_le hd _) hu hu0 (by positivity)
          _ = (d : ℝ) ^ 3 / 3 * pw (A + (k' + 1)) := by ring
      have hsplit : residuePotential d (A + (k' + 1) + 1) * pw (A + (k' + 1)) -
          residuePotential d A * pw A +
          (cubicPotential d (A + k' + 1) * u (A + k') - cubicPotential d A * u A + I) +
          (residuePotential d A / (A : ℝ) ^ 2 +
            (2 * cubicPotential d A - residuePotential d A) / (A : ℝ) ^ 3) =
          residuePotential d (A + (k' + 1) + 1) * pw (A + (k' + 1)) +
            cubicPotential d (A + k' + 1) * u (A + k') + I +
            (residuePotential d A * (1 / (A : ℝ) ^ 2 - 1 / (A : ℝ) ^ 3 - pw A) +
              cubicPotential d A * (2 / (A : ℝ) ^ 3 - (pw A - pw (A + 1)))) := by
        simp only [u]; ring
      rw [hsplit]
      calc |residuePotential d (A + (k' + 1) + 1) * pw (A + (k' + 1)) +
            cubicPotential d (A + k' + 1) * u (A + k') + I +
            (residuePotential d A * (1 / (A : ℝ) ^ 2 - 1 / (A : ℝ) ^ 3 - pw A) +
              cubicPotential d A * (2 / (A : ℝ) ^ 3 - (pw A - pw (A + 1))))|
          ≤ |residuePotential d (A + (k' + 1) + 1)| * pw (A + (k' + 1)) +
              |cubicPotential d (A + k' + 1)| * u (A + k') + |I| +
              ((d : ℝ) ^ 2 / 8 + (d : ℝ) ^ 3) / (A : ℝ) ^ 4 := by
            have hu0 : 0 ≤ u (A + k') := pw_sub_pw_succ_nonneg (by omega)
            refine (abs_add_le _ _).trans (add_le_add ?_ hexp)
            refine (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans ?_) le_rfl)
            rw [abs_mul, abs_mul, abs_of_nonneg (pw_nonneg _), abs_of_nonneg hu0]
        _ ≤ ((d : ℝ) ^ 2 / 8 + (d : ℝ) ^ 3 / 3) * pw (A + (k' + 1)) +
              (((d : ℝ) ^ 2 / 8 + (d : ℝ) ^ 3) / (A : ℝ) ^ 4 + (d : ℝ) ^ 4 / (A : ℝ) ^ 4) := by
            nlinarith
        _ ≤ ((d : ℝ) ^ 2 / 8 + (d : ℝ) ^ 3 / 3) * pw (A + (k' + 1)) +
              3 * (d : ℝ) ^ 4 / (A : ℝ) ^ 4 := by linarith
  · rw [Ico_eq_empty_of_le (not_lt.mp hAH), sum_empty, zero_add, abs_zero, zero_add]
    positivity

/-! ## §3. The cubic kernel -/

theorem abs_two_mul_cubicPotential_sub_le {d : ℕ} (hd : 0 < d) (M : ℕ) :
    |2 * cubicPotential d M - residuePotential d M| ≤ (d : ℝ) ^ 3 / 2 := by
  have h1 := abs_cubicPotential_le hd M
  have h2 := abs_residuePotential_le hd M
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have h3 : (d : ℝ) ^ 2 ≤ (d : ℝ) ^ 3 := by
    nlinarith [mul_le_mul_of_nonneg_left hd1 (by positivity : (0 : ℝ) ≤ (d : ℝ) ^ 2)]
  calc |2 * cubicPotential d M - residuePotential d M|
      ≤ |2 * cubicPotential d M| + |residuePotential d M| := abs_sub _ _
    _ = 2 * |cubicPotential d M| + |residuePotential d M| := by
        rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    _ ≤ 2 * ((d : ℝ) ^ 3 / 6) + (d : ℝ) ^ 2 / 8 := by gcongr
    _ ≤ (d : ℝ) ^ 3 / 2 := by have : (0 : ℝ) ≤ (d : ℝ) ^ 3 := by positivity
                              linarith

theorem summable_cubicPotential_div_cube {d : ℕ} (hd : 0 < d) (n : ℕ) :
    Summable fun j : ℕ =>
      (2 * cubicPotential d ((j + 1) * n) - residuePotential d ((j + 1) * n)) / ((j : ℝ) + 1) ^ 3 := by
  have hs : Summable fun j : ℕ => (d : ℝ) ^ 3 / 2 * (1 / ((j + 1 : ℕ) : ℝ) ^ 3) :=
    ((summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr (by norm_num))).mul_left _
  refine Summable.of_norm_bounded hs fun j => ?_
  rw [Real.norm_eq_abs, abs_div, abs_of_pos (by positivity : (0 : ℝ) < ((j : ℝ) + 1) ^ 3)]
  push_cast
  rw [div_eq_mul_one_div]
  exact mul_le_mul_of_nonneg_right (abs_two_mul_cubicPotential_sub_le hd _) (by positivity)

/-- The **cubic Bernoulli kernel** `𝔅₃(d, n) = Σ_{j ≥ 1} (2Ψ_d(jn) - Φ_d(jn))/j³`. -/
def cubicKernel (d n : ℕ) : ℝ :=
  ∑' j : ℕ, (2 * cubicPotential d ((j + 1) * n) - residuePotential d ((j + 1) * n)) /
    ((j : ℝ) + 1) ^ 3

theorem hasSum_cubicKernel {d : ℕ} (hd : 0 < d) (n : ℕ) :
    HasSum (fun j : ℕ =>
      (2 * cubicPotential d ((j + 1) * n) - residuePotential d ((j + 1) * n)) / ((j : ℝ) + 1) ^ 3)
      (cubicKernel d n) :=
  (summable_cubicPotential_div_cube hd n).hasSum

theorem cubicKernel_mod (d n : ℕ) : cubicKernel d n = cubicKernel d (n % d) := by
  simp only [cubicKernel, cubicPotential, residuePotential, Nat.mul_mod, Nat.mod_mod]

theorem abs_cubicKernel_le {d : ℕ} (hd : 0 < d) (n : ℕ) : |cubicKernel d n| ≤ (d : ℝ) ^ 3 := by
  have hz : HasSum (fun j : ℕ => 1 / ((j : ℝ) + 1) ^ 2) (Real.pi ^ 2 / 6) := by
    have := (hasSum_nat_add_iff' 1).mpr hasSum_zeta_two
    simpa using this
  have hle : |cubicKernel d n| ≤ (d : ℝ) ^ 3 / 2 * (Real.pi ^ 2 / 6) := by
    rw [← Real.norm_eq_abs]
    refine (norm_tsum_le_tsum_norm (summable_cubicPotential_div_cube hd n).norm).trans ?_
    rw [← (hz.mul_left ((d : ℝ) ^ 3 / 2)).tsum_eq]
    refine Summable.tsum_le_tsum (fun j => ?_) (summable_cubicPotential_div_cube hd n).norm
      (hz.mul_left _).summable
    have hj : (1 : ℝ) ≤ (j : ℝ) + 1 := by have := (Nat.cast_nonneg j : (0 : ℝ) ≤ j); linarith
    rw [Real.norm_eq_abs, abs_div, abs_of_pos (by positivity : (0 : ℝ) < ((j : ℝ) + 1) ^ 3)]
    calc |2 * cubicPotential d ((j + 1) * n) - residuePotential d ((j + 1) * n)| / ((j : ℝ) + 1) ^ 3
        ≤ (d : ℝ) ^ 3 / 2 / ((j : ℝ) + 1) ^ 3 :=
          div_le_div_of_nonneg_right (abs_two_mul_cubicPotential_sub_le hd _) (by positivity)
      _ ≤ (d : ℝ) ^ 3 / 2 / ((j : ℝ) + 1) ^ 2 :=
          div_le_div_of_nonneg_left (by positivity) (by positivity)
            (pow_le_pow_right₀ hj (by norm_num))
      _ = (d : ℝ) ^ 3 / 2 * (1 / ((j : ℝ) + 1) ^ 2) := by ring
  have hpi : Real.pi ^ 2 / 6 ≤ 2 := by nlinarith [Real.pi_lt_d2, Real.pi_pos]
  calc |cubicKernel d n| ≤ (d : ℝ) ^ 3 / 2 * (Real.pi ^ 2 / 6) := hle
    _ ≤ (d : ℝ) ^ 3 / 2 * 2 := by gcongr
    _ = (d : ℝ) ^ 3 := by ring

/-! ## §4. The third-order law -/

/-- Truncated sums `Σ_{1 ≤ j ≤ H, jn < H} f(j)` converge to `Σ_{j ≥ 1} f(j)`. -/
theorem tendsto_sum_Icc_ite_of_hasSum {n : ℕ} (hn : 1 ≤ n) {f : ℕ → ℝ} {s : ℝ}
    (hf : HasSum (fun i => f (i + 1)) s) :
    Tendsto (fun H : ℕ => ∑ j ∈ Icc 1 H, (if j * n < H then f j else 0)) atTop (𝓝 s) := by
  have hpart : ∀ K, ∑ j ∈ Icc 1 K, f j = ∑ i ∈ range K, f (i + 1) := by
    intro K
    induction K with
    | zero => simp
    | succ K ih => rw [sum_Icc_succ_top (by omega), ih, Finset.sum_range_succ]
  have heq : ∀ H, ∑ j ∈ Icc 1 H, (if j * n < H then f j else 0) =
      ∑ i ∈ range ((H - 1) / n), f (i + 1) := by
    intro H
    rw [← hpart, ← sum_filter]
    congr 1
    ext j
    simp only [mem_filter, mem_Icc]
    have hn0 : 0 < n := by omega
    constructor
    · rintro ⟨⟨hj1, _⟩, hjn⟩
      have h1 : j * n ≤ H - 1 := by omega
      exact ⟨hj1, (Nat.le_div_iff_mul_le hn0).mpr h1⟩
    · rintro ⟨hj1, hj⟩
      have h1 : j * n ≤ H - 1 := (Nat.le_div_iff_mul_le hn0).mp hj
      have h2 : j ≤ j * n := Nat.le_mul_of_pos_right j hn0
      have h3 : 1 ≤ H := by
        rcases Nat.eq_zero_or_pos H with h | h
        · subst h; simp at h1; omega
        · exact h
      exact ⟨⟨hj1, by omega⟩, by omega⟩
  have hdiv : Tendsto (fun H : ℕ => (H - 1) / n) atTop atTop := by
    refine tendsto_atTop_atTop.mpr fun b => ⟨b * n + 1, fun H hH => ?_⟩
    exact (Nat.le_div_iff_mul_le (by omega)).mpr (by omega)
  simp_rw [heq]
  exact hf.tendsto_sum_nat.comp hdiv

theorem tendsto_sum_Icc_cubicPotential_div_cube {d n : ℕ} (hd : 0 < d) (hn : 1 ≤ n) :
    Tendsto (fun H : ℕ => ∑ j ∈ Icc 1 H,
      (if j * n < H then (2 * cubicPotential d (j * n) - residuePotential d (j * n)) /
        ((j * n : ℕ) : ℝ) ^ 3 else 0)) atTop (𝓝 (cubicKernel d n / (n : ℝ) ^ 3)) := by
  refine tendsto_sum_Icc_ite_of_hasSum hn ?_
  refine ((hasSum_cubicKernel hd n).div_const ((n : ℝ) ^ 3)).congr_fun fun i => ?_
  push_cast
  rw [mul_pow, div_div]

/-- The `j`-sum of third-order remainders of one large modulus `n` against one small modulus `d`. -/
theorem abs_sum_Icc_step_add_third_le {d n : ℕ} (hd : 0 < d) (hn : 1 ≤ n) (H : ℕ) :
    |∑ j ∈ Icc 1 H, (∑ M ∈ Ico (j * n) H, centeredResidue d M * pw M +
        (if j * n < H then residuePotential d (j * n) / ((j * n : ℕ) : ℝ) ^ 2 +
          (2 * cubicPotential d (j * n) - residuePotential d (j * n)) / ((j * n : ℕ) : ℝ) ^ 3
        else 0))| ≤
      ((d : ℝ) ^ 2 / 8 + (d : ℝ) ^ 3 / 3) * ((H : ℝ) * pw (H - 1)) +
        6 * (d : ℝ) ^ 4 / (n : ℝ) ^ 4 := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hterm := fun j (hj : j ∈ Icc 1 H) =>
    abs_sum_Ico_centeredResidue_mul_pw_add_third_le hd
      (Nat.one_le_iff_ne_zero.mpr (by have := (mem_Icc.mp hj).1; positivity) : 1 ≤ j * n) H
  have hquart : ∑ j ∈ Icc 1 H, 3 * (d : ℝ) ^ 4 / ((j * n : ℕ) : ℝ) ^ 4 ≤
      6 * (d : ℝ) ^ 4 / (n : ℝ) ^ 4 := by
    rw [show ∑ j ∈ Icc 1 H, 3 * (d : ℝ) ^ 4 / ((j * n : ℕ) : ℝ) ^ 4 =
      3 * (d : ℝ) ^ 4 * ∑ j ∈ Icc 1 H, 1 / ((j * n : ℕ) : ℝ) ^ 4 by
        rw [mul_sum]; exact sum_congr rfl fun j _ => by ring]
    have hs : ∑ j ∈ Icc 1 H, 1 / ((j * n : ℕ) : ℝ) ^ 4 ≤ 2 / (n : ℝ) ^ 4 := by
      calc ∑ j ∈ Icc 1 H, 1 / ((j * n : ℕ) : ℝ) ^ 4
          ≤ ∑ j ∈ Icc 1 H, 1 / (n : ℝ) ^ 4 * (1 / (j : ℝ) ^ 2) := by
            refine sum_le_sum fun j hj => ?_
            have hjR : (1 : ℝ) ≤ j := by exact_mod_cast (mem_Icc.mp hj).1
            push_cast
            rw [div_mul_div_comm, one_mul]
            refine one_div_le_one_div_of_le (by positivity) ?_
            rw [mul_pow]
            have h2 : (j : ℝ) ^ 2 ≤ (j : ℝ) ^ 4 := pow_le_pow_right₀ hjR (by norm_num)
            nlinarith [mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ (n : ℝ) ^ 4)]
        _ = 1 / (n : ℝ) ^ 4 * ∑ j ∈ Icc 1 H, 1 / (j : ℝ) ^ 2 := by rw [mul_sum]
        _ ≤ 1 / (n : ℝ) ^ 4 * 2 := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            rcases Nat.eq_zero_or_pos H with h0 | hH
            · subst h0; simp
            · have := sum_Icc_one_div_sq_le hH
              have : 0 ≤ 1 / (H : ℝ) := by positivity
              linarith
        _ = 2 / (n : ℝ) ^ 4 := by ring
    calc 3 * (d : ℝ) ^ 4 * ∑ j ∈ Icc 1 H, 1 / ((j * n : ℕ) : ℝ) ^ 4
        ≤ 3 * (d : ℝ) ^ 4 * (2 / (n : ℝ) ^ 4) := mul_le_mul_of_nonneg_left hs (by positivity)
      _ = 6 * (d : ℝ) ^ 4 / (n : ℝ) ^ 4 := by ring
  have hite : ∑ j ∈ Icc 1 H,
      (if j * n < H then ((d : ℝ) ^ 2 / 8 + (d : ℝ) ^ 3 / 3) * pw (H - 1) else 0) ≤
      ((d : ℝ) ^ 2 / 8 + (d : ℝ) ^ 3 / 3) * ((H : ℝ) * pw (H - 1)) := by
    calc ∑ j ∈ Icc 1 H,
          (if j * n < H then ((d : ℝ) ^ 2 / 8 + (d : ℝ) ^ 3 / 3) * pw (H - 1) else 0)
        ≤ ∑ _j ∈ Icc 1 H, ((d : ℝ) ^ 2 / 8 + (d : ℝ) ^ 3 / 3) * pw (H - 1) :=
          sum_le_sum fun j _ => by
            split_ifs
            · exact le_rfl
            · have := pw_nonneg (H - 1); positivity
      _ = _ := by rw [sum_const, Nat.card_Icc]; simp; ring
  calc |∑ j ∈ Icc 1 H, (∑ M ∈ Ico (j * n) H, centeredResidue d M * pw M +
        (if j * n < H then residuePotential d (j * n) / ((j * n : ℕ) : ℝ) ^ 2 +
          (2 * cubicPotential d (j * n) - residuePotential d (j * n)) / ((j * n : ℕ) : ℝ) ^ 3
        else 0))|
      ≤ ∑ j ∈ Icc 1 H,
          ((if j * n < H then ((d : ℝ) ^ 2 / 8 + (d : ℝ) ^ 3 / 3) * pw (H - 1) else 0) +
            3 * (d : ℝ) ^ 4 / ((j * n : ℕ) : ℝ) ^ 4) :=
        (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun j hj => hterm j hj)
    _ = ∑ j ∈ Icc 1 H,
          (if j * n < H then ((d : ℝ) ^ 2 / 8 + (d : ℝ) ^ 3 / 3) * pw (H - 1) else 0) +
          ∑ j ∈ Icc 1 H, 3 * (d : ℝ) ^ 4 / ((j * n : ℕ) : ℝ) ^ 4 := sum_add_distrib
    _ ≤ _ := add_le_add hite hquart

/-- **The third-order cross-scale law.** For all rows `c, c'`,
`|B(c, c') + m(c) R(c') + β(c) H(c') - Σ_{n, d} c'(n) (c(d)/d) (𝔅(d, n)/n² + 𝔅₃(d, n)/n³)|
  ≤ 6 (Σ_d |c(d)| d³)(Σ_n |c'(n)|/n⁴)`. -/
theorem abs_rowBilinear_add_mean_add_beta_sub_third_order_le (N : ℕ) (c c' : ℕ → ℝ) :
    |rowBilinear N c c' + rowMean N c * vonMangoldtReadout N c' +
        rowBeta N c * finiteHarmonicSum N c' -
        ∑ n ∈ Icc 1 N, ∑ d ∈ Icc 1 N, c' n * (c d / d) *
          (bernoulliKernel d n / (n : ℝ) ^ 2 + cubicKernel d n / (n : ℝ) ^ 3)| ≤
      6 * (∑ d ∈ Icc 1 N, |c d| * (d : ℝ) ^ 3) * ∑ n ∈ Icc 1 N, |c' n| / (n : ℝ) ^ 4 := by
  classical
  set ite' : ℕ → ℕ → ℕ → ℕ → ℝ := fun d n H j =>
    if j * n < H then residuePotential d (j * n) / ((j * n : ℕ) : ℝ) ^ 2 +
      (2 * cubicPotential d (j * n) - residuePotential d (j * n)) / ((j * n : ℕ) : ℝ) ^ 3 else 0
  set step : ℕ → ℝ := fun H => ∑ n ∈ Icc 1 N, c' n *
    ∑ M ∈ range H, rowFluct N c M * ((M / n : ℕ) : ℝ) / (pronicSeq M : ℝ)
  set main : ℕ → ℝ := fun H => ∑ n ∈ Icc 1 N, ∑ d ∈ Icc 1 N, c' n * (c d / d) *
    ∑ j ∈ Icc 1 H, ite' d n H j
  set δ : ℕ → ℝ := fun H => (∑ n ∈ Icc 1 N, ∑ d ∈ Icc 1 N, |c' n| * (|c d| / d) *
    ((d : ℝ) ^ 2 / 8 + (d : ℝ) ^ 3 / 3)) * ((H : ℝ) * pw (H - 1))
  set C : ℝ := ∑ n ∈ Icc 1 N, ∑ d ∈ Icc 1 N, |c' n| * (|c d| / d) *
    (6 * (d : ℝ) ^ 4 / (n : ℝ) ^ 4)
  have hrow : ∀ n H, ∑ j ∈ Icc 1 H, ∑ M ∈ Ico (j * n) H, rowFluct N c M * pw M =
      -∑ d ∈ Icc 1 N, c d / d * ∑ j ∈ Icc 1 H, ∑ M ∈ Ico (j * n) H, centeredResidue d M * pw M := by
    intro n H
    simp only [rowFluct, neg_mul, sum_mul, sum_neg_distrib, mul_sum]
    congr 1
    calc ∑ j ∈ Icc 1 H, ∑ M ∈ Ico (j * n) H, ∑ d ∈ Icc 1 N, c d / d * centeredResidue d M * pw M
        = ∑ j ∈ Icc 1 H, ∑ d ∈ Icc 1 N, ∑ M ∈ Ico (j * n) H, c d / d * centeredResidue d M * pw M :=
          sum_congr rfl fun j _ => sum_comm
      _ = ∑ d ∈ Icc 1 N, ∑ j ∈ Icc 1 H, ∑ M ∈ Ico (j * n) H, c d / d * centeredResidue d M * pw M :=
          sum_comm
      _ = _ := sum_congr rfl fun d _ => sum_congr rfl fun j _ => sum_congr rfl fun M _ => by ring
  have hdiff : ∀ H, step H - main H = -∑ n ∈ Icc 1 N, ∑ d ∈ Icc 1 N, c' n * (c d / d) *
      ∑ j ∈ Icc 1 H, (∑ M ∈ Ico (j * n) H, centeredResidue d M * pw M + ite' d n H j) := by
    intro H
    simp only [step, main, ← sum_sub_distrib, ← sum_neg_distrib]
    refine sum_congr rfl fun n hn => ?_
    rw [sum_range_mul_div_div_pronic_eq (mem_Icc.mp hn).1, hrow, mul_neg, mul_sum, ← sum_neg_distrib,
      ← sum_sub_distrib]
    refine sum_congr rfl fun d _ => ?_
    rw [sum_add_distrib]
    ring
  have hbound : ∀ H, |step H - main H| ≤ C + δ H := by
    intro H
    rw [hdiff, abs_neg]
    calc |∑ n ∈ Icc 1 N, ∑ d ∈ Icc 1 N, c' n * (c d / d) *
          ∑ j ∈ Icc 1 H, (∑ M ∈ Ico (j * n) H, centeredResidue d M * pw M + ite' d n H j)|
        ≤ ∑ n ∈ Icc 1 N, ∑ d ∈ Icc 1 N, |c' n| * (|c d| / d) *
            (((d : ℝ) ^ 2 / 8 + (d : ℝ) ^ 3 / 3) * ((H : ℝ) * pw (H - 1)) +
              6 * (d : ℝ) ^ 4 / (n : ℝ) ^ 4) := by
          refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun n hn => ?_)
          refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun d hd => ?_)
          have hd0 : 0 < d := (mem_Icc.mp hd).1
          have hdR : (0 : ℝ) < d := by exact_mod_cast hd0
          rw [abs_mul, abs_mul, abs_div, abs_of_pos hdR]
          exact mul_le_mul_of_nonneg_left (abs_sum_Icc_step_add_third_le hd0 (mem_Icc.mp hn).1 H)
            (by positivity)
      _ = C + δ H := by
          have e1 : δ H = ∑ n ∈ Icc 1 N, ∑ d ∈ Icc 1 N, |c' n| * (|c d| / d) *
              ((d : ℝ) ^ 2 / 8 + (d : ℝ) ^ 3 / 3) * ((H : ℝ) * pw (H - 1)) := by
            simp only [δ, sum_mul]
          rw [e1, ← sum_add_distrib]
          refine sum_congr rfl fun n _ => ?_
          rw [← sum_add_distrib]
          exact sum_congr rfl fun d _ => by ring
  have hstep_lim := tendsto_rowStepSum N c c'
  have hmain_lim : Tendsto main atTop (𝓝 (∑ n ∈ Icc 1 N, ∑ d ∈ Icc 1 N,
      c' n * (c d / d) * (bernoulliKernel d n / (n : ℝ) ^ 2 + cubicKernel d n / (n : ℝ) ^ 3))) := by
    simp only [main]
    refine tendsto_finsetSum _ fun n hn => tendsto_finsetSum _ fun d hd => ?_
    have hsplit : ∀ H, ∑ j ∈ Icc 1 H, ite' d n H j =
        ∑ j ∈ Icc 1 H, (if j * n < H then residuePotential d (j * n) / ((j * n : ℕ) : ℝ) ^ 2
          else 0) +
        ∑ j ∈ Icc 1 H, (if j * n < H then (2 * cubicPotential d (j * n) -
          residuePotential d (j * n)) / ((j * n : ℕ) : ℝ) ^ 3 else 0) := by
      intro H
      rw [← sum_add_distrib]
      exact sum_congr rfl fun j _ => by simp only [ite']; split_ifs <;> simp
    simp_rw [hsplit]
    exact ((tendsto_sum_Icc_residuePotential_div_sq (mem_Icc.mp hd).1 (mem_Icc.mp hn).1).add
      (tendsto_sum_Icc_cubicPotential_div_cube (mem_Icc.mp hd).1 (mem_Icc.mp hn).1)).const_mul _
  have hδ : Tendsto δ atTop (𝓝 0) := by
    have := tendsto_mul_pw_pred.const_mul
      (∑ n ∈ Icc 1 N, ∑ d ∈ Icc 1 N, |c' n| * (|c d| / d) * ((d : ℝ) ^ 2 / 8 + (d : ℝ) ^ 3 / 3))
    rw [mul_zero] at this
    exact this
  have hle : |rowBilinear N c c' + rowMean N c * vonMangoldtReadout N c' +
        rowBeta N c * finiteHarmonicSum N c' -
        ∑ n ∈ Icc 1 N, ∑ d ∈ Icc 1 N, c' n * (c d / d) *
          (bernoulliKernel d n / (n : ℝ) ^ 2 + cubicKernel d n / (n : ℝ) ^ 3)| ≤ C := by
    have := le_of_tendsto_of_tendsto (hstep_lim.sub hmain_lim).abs (tendsto_const_nhds.add hδ)
      (Eventually.of_forall hbound)
    simpa using this
  refine hle.trans (le_of_eq ?_)
  have hprod : 6 * (∑ d ∈ Icc 1 N, |c d| * (d : ℝ) ^ 3) * ∑ n ∈ Icc 1 N, |c' n| / (n : ℝ) ^ 4 =
      ∑ n ∈ Icc 1 N, ∑ d ∈ Icc 1 N, 6 * (|c d| * (d : ℝ) ^ 3) * (|c' n| / (n : ℝ) ^ 4) := by
    rw [mul_assoc, sum_mul_sum, sum_comm, mul_sum]
    refine sum_congr rfl fun n _ => ?_
    rw [mul_sum]
    exact sum_congr rfl fun d _ => by ring
  rw [hprod]
  refine sum_congr rfl fun n hn => sum_congr rfl fun d hd => ?_
  have hdR : (0 : ℝ) < d := by exact_mod_cast (mem_Icc.mp hd).1
  have hnR : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
  field_simp

end

end GaloisForLFunctions.BezoutValuationIncidence
