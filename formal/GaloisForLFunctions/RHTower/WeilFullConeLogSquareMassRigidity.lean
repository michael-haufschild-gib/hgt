import GaloisForLFunctions.RHTower.WeilFullConeSquareRootScaleRigidity

/-!
# Log-weighted square-summable rigidity of the full Weil cone

**Theorem** (`eq_vonMangoldt_of_weilPositiveFull_of_log_square_summable`, unconditional). Let `lam`
be full-cone Weil-positive with `Σ_n (lam(n) − Λ(n))² / (1 + log n)^K < ∞` for some `K`. Then
`lam = Λ`. Hence RH holds iff such a `lam` exists
(`riemannHypothesis_iff_exists_weilPositiveFull_log_square_summable`).

The hypothesis is equivalent to a polylogarithmic square mass
`Σ_{n ≤ N} (lam(n) − Λ(n))² ≪ (log N)^{K'}`. It allows deviations of bounded size at arbitrary
positions of a polylogarithmically sparse set, with no separation between their logarithms, and
it contains the square-root-scale class `|lam − Λ| ≤ C (1 + log n)^B / √n`.

**Proof.** The zero-free-window method, with the mean-value errors controlled in `ℓ²`:
- `κ(n, m) ≤ 3 + N(n, m)`, where `N(n, m) = (n + m)/|n − m|` for `n ≠ m` within a factor `2`
  (`intLogKernel_le_three_add_near`), and `Σ_n N(n, m) ≤ 5 m (1 + log m)`
  (`tsum_nearLogKernel_le`);
- the symmetric Schur bound `Σ_m |c_m| Σ_n |c_n| N(n, m) ≤ Σ_m c_m² · 5 m (1 + log m)`
  (`tsum_abs_mul_tsum_nearLogKernel_le`);
- for `c_n = v(n) B(η log n)`: `c_n² · 5n(1 + log n) ≤ 5 K_p² (lam(n) − Λ(n))²/(1 + log n)^K`
  with `K_p = O(η^{−J})`, `J = K + 2` (`normDeficit_mul_sq_mul_le`), and `Σ |c_n| = O(η^{−J})` by
  the AM-GM majorant (`abs_normDeficit_mul_inv_pow_le`).

All errors are `O(η^{−2J})`, negligible at height `T = η^{−(2J+1)}`.

**Reach.** With polynomially decaying bump transforms the tail
`Σ_{n > e^{1/η}} (lam(n) − Λ(n))² B(η log n)²` is polynomial in `1/η` exactly for polylogarithmic
square mass, which is therefore the natural limit of the method on dense supports.
-/

open Complex MeasureTheory Filter Topology Set
open scoped Real ComplexConjugate Convolution FourierTransform
open Zeta23

namespace RHTower

noncomputable section

/-! ## The near-diagonal integer kernel -/

/-- `N(n, m) = (n + m)/|n − m|` when `n ≠ m` and `n, m` are within a factor `2`, else `0`. -/
def nearLogKernel (n m : ℕ) : ℝ :=
  if n ≠ m ∧ n ≤ 2 * m ∧ m ≤ 2 * n then ((n : ℝ) + m) / |(n : ℝ) - m| else 0

theorem nearLogKernel_nonneg (n m : ℕ) : 0 ≤ nearLogKernel n m := by
  unfold nearLogKernel; split_ifs <;> positivity

theorem nearLogKernel_symm (n m : ℕ) : nearLogKernel n m = nearLogKernel m n := by
  unfold nearLogKernel
  by_cases h : n ≠ m ∧ n ≤ 2 * m ∧ m ≤ 2 * n
  · rw [if_pos h, if_pos ⟨Ne.symm h.1, h.2.2, h.2.1⟩, add_comm, abs_sub_comm]
  · rw [if_neg h, if_neg (fun h' => h ⟨Ne.symm h'.1, h'.2.2, h'.2.1⟩)]

theorem nearLogKernel_eq_zero_of_lt {n m : ℕ} (h : 2 * m < n) : nearLogKernel n m = 0 := by
  unfold nearLogKernel; rw [if_neg (by omega)]

/-- `κ(n, m) ≤ 3 + N(n, m)` for `m ≥ 2`. -/
theorem intLogKernel_le_three_add_near {m : ℕ} (hm : 2 ≤ m) (n : ℕ) :
    intLogKernel n m ≤ 3 + nearLogKernel n m := by
  have hN := nearLogKernel_nonneg n m
  unfold intLogKernel
  by_cases hnm : n = m
  · rw [if_pos hnm]; linarith
  rw [if_neg hnm]
  have hlog2 : (0.69 : ℝ) < Real.log 2 := by have := Real.log_two_gt_d9; linarith
  have hm1 : (1 : ℝ) < m := by exact_mod_cast (by omega : 1 < m)
  by_cases hnear : n ≤ 2 * m ∧ m ≤ 2 * n
  · have hn1 : 1 ≤ n := by omega
    have hn1' : (1 : ℝ) ≤ n := by exact_mod_cast hn1
    unfold nearLogKernel
    rw [if_pos ⟨hnm, hnear⟩]
    rcases lt_or_gt_of_ne hnm with hlt | hgt
    · have hl := inv_log_sub_log_le (m := n) (n := m) hn1 hlt
      have hmn : (n : ℝ) < m := by exact_mod_cast hlt
      rw [abs_sub_comm, abs_of_pos (sub_pos.mpr (Real.log_lt_log (by linarith) hmn)),
        abs_sub_comm, abs_of_pos (sub_pos.mpr hmn)]
      have : (m : ℝ) / ((m : ℝ) - n) ≤ ((n : ℝ) + m) / ((m : ℝ) - n) :=
        div_le_div_of_nonneg_right (by linarith) (by linarith)
      linarith
    · have hl := inv_log_sub_log_le (m := m) (n := n) (by omega) hgt
      have hmn : (m : ℝ) < n := by exact_mod_cast hgt
      rw [abs_of_pos (sub_pos.mpr (Real.log_lt_log (by linarith) hmn)),
        abs_of_pos (sub_pos.mpr hmn)]
      have : (n : ℝ) / ((n : ℝ) - m) ≤ ((n : ℝ) + m) / ((n : ℝ) - m) :=
        div_le_div_of_nonneg_right (by linarith) (by linarith)
      linarith
  · have hfar : Real.log 2 ≤ |Real.log n - Real.log m| := by
      rcases Nat.eq_zero_or_pos n with rfl | hn0
      · simp only [Nat.cast_zero, Real.log_zero, zero_sub, abs_neg]
        rw [abs_of_nonneg (Real.log_nonneg hm1.le)]
        exact Real.log_le_log (by norm_num) (by exact_mod_cast hm)
      have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn0
      by_cases h1 : n ≤ 2 * m
      · have h2 : 2 * n < m := by omega
        have h2' : 2 * (n : ℝ) ≤ m := by exact_mod_cast h2.le
        have hle : Real.log n ≤ Real.log m := Real.log_le_log (by linarith) (by linarith)
        rw [abs_sub_comm, abs_of_nonneg (by linarith)]
        have : Real.log (2 * n) ≤ Real.log m := Real.log_le_log (by positivity) h2'
        rw [Real.log_mul (by norm_num) (by linarith)] at this
        linarith
      · have h2 : 2 * m < n := by omega
        have h2' : 2 * (m : ℝ) ≤ n := by exact_mod_cast h2.le
        have hle : Real.log m ≤ Real.log n := Real.log_le_log (by linarith) (by linarith)
        rw [abs_of_nonneg (by linarith)]
        have : Real.log (2 * m) ≤ Real.log n := Real.log_le_log (by positivity) h2'
        rw [Real.log_mul (by norm_num) (by linarith)] at this
        linarith
    have hpos : 0 < |Real.log n - Real.log m| := by linarith
    have hinv : |Real.log n - Real.log m|⁻¹ ≤ 2 := by
      rw [inv_le_comm₀ hpos (by norm_num)]; linarith
    linarith

theorem summable_nearLogKernel (m : ℕ) : Summable fun n => nearLogKernel n m :=
  summable_of_ne_finset_zero (s := Finset.range (2 * m + 1)) fun n hn => by
    rw [Finset.mem_range] at hn; exact nearLogKernel_eq_zero_of_lt (by omega)

/-- `Σ_n N(n, m) ≤ 5 m (1 + log m)`. -/
theorem tsum_nearLogKernel_le (m : ℕ) :
    ∑' n, nearLogKernel n m ≤ 5 * m * (1 + Real.log m) := by
  rw [tsum_eq_sum (s := Finset.range (2 * m + 1)) fun n hn => by
    rw [Finset.mem_range] at hn; exact nearLogKernel_eq_zero_of_lt (by omega)]
  rw [← Finset.sum_range_add_sum_Ico _ (show m ≤ 2 * m + 1 by omega),
    Finset.sum_Ico_eq_sum_range, show 2 * m + 1 - m = m + 1 by omega, Finset.sum_range_succ']
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hlog : 0 ≤ Real.log m := Real.log_natCast_nonneg m
  -- lower part
  have h1 : ∑ n ∈ Finset.range m, nearLogKernel n m ≤ 2 * m * (1 + Real.log m) := by
    have hpt : ∀ n ∈ Finset.range m, nearLogKernel n m ≤ 2 * m * ((m : ℝ) - n)⁻¹ := by
      intro n hn
      rw [Finset.mem_range] at hn
      have hmn : (n : ℝ) < m := by exact_mod_cast hn
      unfold nearLogKernel
      split_ifs with h
      · rw [abs_sub_comm, abs_of_pos (sub_pos.mpr hmn), div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_right (by linarith) (inv_nonneg.mpr (by linarith))
      · exact mul_nonneg (by positivity) (inv_nonneg.mpr (by linarith))
    calc ∑ n ∈ Finset.range m, nearLogKernel n m ≤ ∑ n ∈ Finset.range m, 2 * m * ((m : ℝ) - n)⁻¹ :=
          Finset.sum_le_sum hpt
      _ = 2 * m * ∑ n ∈ Finset.range m, ((m : ℝ) - n)⁻¹ := by rw [Finset.mul_sum]
      _ ≤ 2 * m * (1 + Real.log m) :=
          mul_le_mul_of_nonneg_left (sum_range_inv_sub_le m) (by positivity)
  -- upper part
  have h2 : ∑ k ∈ Finset.range m, nearLogKernel (m + (k + 1)) m ≤ 3 * m * (1 + Real.log m) := by
    have hpt : ∀ k ∈ Finset.range m, nearLogKernel (m + (k + 1)) m ≤
        3 * m * (((k + 1 : ℕ) : ℝ))⁻¹ := by
      intro k hk
      rw [Finset.mem_range] at hk
      unfold nearLogKernel
      split_ifs with h
      · push_cast
        rw [show (m : ℝ) + (k + 1) - m = k + 1 by ring, abs_of_pos (by positivity), div_eq_mul_inv]
        have hk' : (k : ℝ) + 1 ≤ m := by exact_mod_cast hk
        exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      · positivity
    calc ∑ k ∈ Finset.range m, nearLogKernel (m + (k + 1)) m
        ≤ ∑ k ∈ Finset.range m, 3 * m * (((k + 1 : ℕ) : ℝ))⁻¹ := Finset.sum_le_sum hpt
      _ = 3 * m * ((harmonic m : ℚ) : ℝ) := by
          rw [← Finset.mul_sum]; congr 1; unfold harmonic; push_cast; rfl
      _ ≤ 3 * m * (1 + Real.log m) :=
          mul_le_mul_of_nonneg_left (harmonic_le_one_add_log m) (by positivity)
  have h0 : nearLogKernel (m + 0) m = 0 := by
    unfold nearLogKernel; rw [if_neg (by omega)]
  rw [h0, add_zero]
  linarith

/-! ## The symmetric Schur bound -/

/-- `Σ_m |c_m| Σ_n |c_n| N(n, m) ≤ Σ_m c_m² W(m)` whenever `Σ_n N(n, m) ≤ W(m)`. -/
theorem tsum_abs_mul_tsum_nearLogKernel_le {c W : ℕ → ℝ}
    (hW : ∀ m, ∑' n, nearLogKernel n m ≤ W m) (hcW : Summable fun m => c m ^ 2 * W m) :
    Summable (fun m => |c m| * ∑' n, |c n| * nearLogKernel n m) ∧
      ∑' m, |c m| * ∑' n, |c n| * nearLogKernel n m ≤ ∑' m, c m ^ 2 * W m := by
  have hN0 := nearLogKernel_nonneg
  have hrow : ∀ m, Summable fun n => |c n| * nearLogKernel n m := fun m =>
    summable_of_ne_finset_zero (s := Finset.range (2 * m + 1)) fun n hn => by
      rw [Finset.mem_range] at hn; rw [nearLogKernel_eq_zero_of_lt (by omega), mul_zero]
  have hrow2 : ∀ m, Summable fun n => c n ^ 2 * nearLogKernel n m := fun m =>
    summable_of_ne_finset_zero (s := Finset.range (2 * m + 1)) fun n hn => by
      rw [Finset.mem_range] at hn; rw [nearLogKernel_eq_zero_of_lt (by omega), mul_zero]
  have hcol2 : ∀ n, Summable fun m => c n ^ 2 * nearLogKernel n m := fun n =>
    summable_of_ne_finset_zero (s := Finset.range (2 * n + 1)) fun m hm => by
      rw [Finset.mem_range] at hm
      rw [nearLogKernel_symm, nearLogKernel_eq_zero_of_lt (by omega), mul_zero]
  -- the pointwise AM-GM
  have hpt : ∀ m n, |c m| * (|c n| * nearLogKernel n m) ≤
      (c m ^ 2 * nearLogKernel n m + c n ^ 2 * nearLogKernel n m) / 2 := by
    intro m n
    have h := two_mul_le_add_sq |c m| |c n|
    rw [sq_abs, sq_abs] at h
    have := mul_le_mul_of_nonneg_right h (hN0 n m)
    nlinarith
  -- row sums of the two halves
  have hA : ∀ m, ∑' n, c m ^ 2 * nearLogKernel n m ≤ c m ^ 2 * W m := fun m => by
    rw [tsum_mul_left]; exact mul_le_mul_of_nonneg_left (hW m) (sq_nonneg _)
  have hsumA : Summable fun m => ∑' n, c m ^ 2 * nearLogKernel n m :=
    hcW.of_nonneg_of_le (fun m => tsum_nonneg fun n => mul_nonneg (sq_nonneg _) (hN0 n m)) hA
  -- the second half, summed over `m` first
  set g : ℕ → ℕ → ℝ := fun n m => c n ^ 2 * nearLogKernel n m with hg
  have hg0 : ∀ n m, 0 ≤ g n m := fun n m => mul_nonneg (sq_nonneg _) (hN0 n m)
  have hB : ∀ n, ∑' m, g n m ≤ c n ^ 2 * W n := fun n => by
    simp only [hg]
    rw [tsum_mul_left]
    refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
    calc ∑' m, nearLogKernel n m = ∑' m, nearLogKernel m n := tsum_congr fun m => nearLogKernel_symm n m
      _ ≤ W n := hW n
  have hgprod : Summable (Function.uncurry g) := by
    have h := (summable_prod_of_nonneg (f := fun p : ℕ × ℕ => g p.1 p.2)
      (fun p => hg0 p.1 p.2)).mpr ⟨hcol2, hcW.of_nonneg_of_le
        (fun n => tsum_nonneg fun m => hg0 n m) hB⟩
    exact h
  have hswap : ∑' m, ∑' n, g n m = ∑' n, ∑' m, g n m :=
    hgprod.tsum_comm' hcol2 hrow2
  have hsumB : Summable fun m => ∑' n, g n m := by
    have h := (summable_prod_of_nonneg (f := fun p : ℕ × ℕ => g p.2 p.1)
      (fun p => hg0 p.2 p.1)).mp (hgprod.prod_symm)
    exact h.2
  -- combine
  have hrowA : ∀ m, Summable fun n => c m ^ 2 * nearLogKernel n m := fun m =>
    (summable_nearLogKernel m).mul_left _
  have hbd : ∀ m, |c m| * ∑' n, |c n| * nearLogKernel n m ≤
      (∑' n, c m ^ 2 * nearLogKernel n m + ∑' n, g n m) / 2 := by
    intro m
    rw [← tsum_mul_left]
    have hs := ((hrowA m).add (hrow2 m)).div_const 2
    calc ∑' n, |c m| * (|c n| * nearLogKernel n m)
        ≤ ∑' n, (c m ^ 2 * nearLogKernel n m + c n ^ 2 * nearLogKernel n m) / 2 :=
          ((hrow m).mul_left _).tsum_le_tsum (fun n => hpt m n) hs
      _ = (∑' n, c m ^ 2 * nearLogKernel n m + ∑' n, g n m) / 2 := by
          rw [tsum_div_const, (hrowA m).tsum_add (hrow2 m)]
  have hsumAB : Summable fun m => (∑' n, c m ^ 2 * nearLogKernel n m + ∑' n, g n m) / 2 :=
    (hsumA.add hsumB).div_const 2
  have hL0 : ∀ m, 0 ≤ |c m| * ∑' n, |c n| * nearLogKernel n m := fun m =>
    mul_nonneg (abs_nonneg _) (tsum_nonneg fun n => mul_nonneg (abs_nonneg _) (hN0 n m))
  have hsL := hsumAB.of_nonneg_of_le hL0 hbd
  refine ⟨hsL, (hsL.tsum_le_tsum hbd hsumAB).trans ?_⟩
  rw [tsum_div_const, hsumA.tsum_add hsumB, hswap]
  have h1 : ∑' m, ∑' n, c m ^ 2 * nearLogKernel n m ≤ ∑' m, c m ^ 2 * W m :=
    hsumA.tsum_le_tsum hA hcW
  have hsB' : Summable fun n => ∑' m, g n m :=
    hcW.of_nonneg_of_le (fun n => tsum_nonneg fun m => hg0 n m) hB
  have h2 : ∑' n, ∑' m, g n m ≤ ∑' n, c n ^ 2 * W n := hsB'.tsum_le_tsum hB hcW
  linarith

/-! ## Log-weighted square-summable rigidity -/

/-- The AM-GM step `|d|/(√n L^{K+2}) ≤ (d²/L^K + 1/(n L^{K+4}))/2` with `L = 1 + log n`. -/
theorem abs_div_sqrt_mul_pow_le {X s L : ℝ} (hs : 0 < s) (hL : 1 ≤ L) (K : ℕ) :
    X / s * ((L ^ (K + 2))⁻¹) ≤ (X ^ 2 * (L ^ K)⁻¹ + ((s ^ 2) * L ^ (K + 4))⁻¹) / 2 := by
  have hP : 0 < L ^ K := by positivity
  have e1 : L ^ (K + 2) = L ^ K * L ^ 2 := pow_add L K 2
  have e2 : L ^ (K + 4) = L ^ K * L ^ 4 := pow_add L K 4
  rw [e1, e2]
  have hL2 : 0 < L ^ 2 := by positivity
  set y := X * s * L ^ 2 with hy
  have key : 2 * y ≤ y ^ 2 + 1 := by nlinarith [sq_nonneg (y - 1)]
  have lhs : X / s * ((L ^ K * L ^ 2)⁻¹) = y / (s ^ 2 * L ^ K * L ^ 4) := by
    rw [hy]; field_simp
  have rhs : (X ^ 2 * (L ^ K)⁻¹ + ((s ^ 2) * (L ^ K * L ^ 4))⁻¹) / 2 =
      (y ^ 2 + 1) / (2 * (s ^ 2 * L ^ K * L ^ 4)) := by
    rw [hy]; field_simp
  rw [lhs, rhs, div_le_div_iff₀ (by positivity) (by positivity)]
  have hq : 0 < s ^ 2 * L ^ K * L ^ 4 := by positivity
  nlinarith

/-- `v(n)² ≤ K! e · (lam(n) − Λ(n))² / (1 + log n)^K` for `v = normDeficit lam`. -/
theorem normDeficit_sq_le (lam : ℕ → ℝ) (K n : ℕ) :
    normDeficit lam n ^ 2 ≤ K.factorial * Real.exp 1 *
      ((lam n - ArithmeticFunction.vonMangoldt n) ^ 2 * ((1 + Real.log n) ^ K)⁻¹) := by
  have hl := Real.log_natCast_nonneg n
  by_cases hn : 2 ≤ n
  · simp only [normDeficit, if_pos hn]
    have hn' : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hP : 0 < (1 + Real.log n) ^ K := by positivity
    have h1 := one_add_log_pow_le_mul K (by omega : 1 ≤ n)
    rw [div_pow, Real.sq_sqrt hn'.le, show (ArithmeticFunction.vonMangoldt n - lam n) ^ 2 =
      (lam n - ArithmeticFunction.vonMangoldt n) ^ 2 by ring, div_le_iff₀ hn']
    have e : K.factorial * Real.exp 1 * ((lam n - ArithmeticFunction.vonMangoldt n) ^ 2 *
        ((1 + Real.log n) ^ K)⁻¹) * n = (lam n - ArithmeticFunction.vonMangoldt n) ^ 2 *
        (K.factorial * Real.exp 1 * n / (1 + Real.log n) ^ K) := by
      field_simp
    rw [e]
    refine le_mul_of_one_le_right (sq_nonneg _) ?_
    rw [one_le_div hP]; linarith
  · simp only [normDeficit, if_neg hn, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
    positivity

/-- The AM-GM majorant: `|v(n)| / (1 + log n)^{K+2} ≤ (dq(n) + F_{K+4}(n))/2`. -/
theorem abs_normDeficit_mul_inv_pow_le (lam : ℕ → ℝ) (K n : ℕ) :
    |normDeficit lam n| * ((1 + Real.log n) ^ (K + 2))⁻¹ ≤
      ((lam n - ArithmeticFunction.vonMangoldt n) ^ 2 * ((1 + Real.log n) ^ K)⁻¹ +
        invLogWeight (K + 4) n) / 2 := by
  have hl := Real.log_natCast_nonneg n
  by_cases hn : 2 ≤ n
  · simp only [normDeficit, if_pos hn, invLogWeight]
    have hn' : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hs : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn'
    rw [abs_div, abs_of_pos hs, abs_sub_comm]
    have h := abs_div_sqrt_mul_pow_le (X := |lam n - ArithmeticFunction.vonMangoldt n|) hs
      (L := 1 + Real.log n) (by linarith) K
    rw [sq_abs, Real.sq_sqrt hn'.le] at h
    exact h
  · simp only [normDeficit, if_neg hn, abs_zero, zero_mul]
    have := invLogWeight_nonneg (K + 4) n
    positivity

/-- The weighted square bound `c(n)² · 5n(1 + log n) ≤ 5 K_p² dq(n)` for `c = v · b` with
`|b| ≤ K_p (1 + log n)^{−J}`, `K + 1 ≤ 2J`. -/
theorem normDeficit_mul_sq_mul_le (lam : ℕ → ℝ) {K J : ℕ} (hJ : K + 1 ≤ 2 * J) {Kp b : ℝ}
    (n : ℕ) (hb : |b| ≤ Kp * ((1 + Real.log n) ^ J)⁻¹) :
    (normDeficit lam n * b) ^ 2 * (5 * n * (1 + Real.log n)) ≤
      5 * Kp ^ 2 * ((lam n - ArithmeticFunction.vonMangoldt n) ^ 2 * ((1 + Real.log n) ^ K)⁻¹) := by
  have hl := Real.log_natCast_nonneg n
  have hKp : 0 ≤ Kp := by
    have h0 := (abs_nonneg b).trans hb
    have hp : 0 < ((1 + Real.log n) ^ J)⁻¹ := by positivity
    exact nonneg_of_mul_nonneg_left h0 hp
  by_cases hn : 2 ≤ n
  · have hn' : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hvn : normDeficit lam n ^ 2 * n = (lam n - ArithmeticFunction.vonMangoldt n) ^ 2 := by
      simp only [normDeficit, if_pos hn]
      rw [div_pow, Real.sq_sqrt hn'.le]; field_simp; ring
    have hB2 : b ^ 2 ≤ (Kp * ((1 + Real.log n) ^ J)⁻¹) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hb 2
    have hL1 : 1 ≤ 1 + Real.log n := by linarith
    have hpowle : (1 + Real.log n) * (1 + Real.log n) ^ K ≤ ((1 + Real.log n) ^ J) ^ 2 := by
      rw [← pow_succ', ← pow_mul]; exact pow_le_pow_right₀ hL1 (by omega)
    have hq : (1 + Real.log n) / ((1 + Real.log n) ^ J) ^ 2 ≤ ((1 + Real.log n) ^ K)⁻¹ := by
      rw [div_le_iff₀ (by positivity), inv_mul_eq_div, le_div_iff₀ (by positivity)]
      linarith
    have hv0 : 0 ≤ normDeficit lam n ^ 2 * n := by positivity
    calc (normDeficit lam n * b) ^ 2 * (5 * n * (1 + Real.log n))
        = 5 * (normDeficit lam n ^ 2 * n) * b ^ 2 * (1 + Real.log n) := by ring
      _ ≤ 5 * (normDeficit lam n ^ 2 * n) * (Kp * ((1 + Real.log n) ^ J)⁻¹) ^ 2 *
          (1 + Real.log n) := by gcongr
      _ = 5 * Kp ^ 2 * (lam n - ArithmeticFunction.vonMangoldt n) ^ 2 *
          ((1 + Real.log n) / ((1 + Real.log n) ^ J) ^ 2) := by
          rw [hvn]; field_simp
      _ ≤ 5 * Kp ^ 2 * (lam n - ArithmeticFunction.vonMangoldt n) ^ 2 *
          ((1 + Real.log n) ^ K)⁻¹ := mul_le_mul_of_nonneg_left hq (by positivity)
      _ = _ := by ring
  · simp only [normDeficit, if_neg hn, zero_mul, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow]
    positivity

/-- **Mean values with the near-diagonal kernel.** For `c` supported on `n ≥ 2`, absolutely
summable, bounded by `M`, and with `Σ c(n)² · 5n(1 + log n) < ∞`, the coefficient extraction
and the mean square on `[T, 2T]` have errors `3Σ|c| + 5M m(1 + log m)` and
`3(Σ|c|)² + Σ c(n)² 5n(1 + log n)`. -/
theorem windowCosSeries_meanValue_bounds_near {c : ℕ → ℝ} (hc2 : ∀ n, c n ≠ 0 → 2 ≤ n)
    (hc : Summable fun n => |c n|) {M : ℝ} (hM : ∀ n, |c n| ≤ M)
    (hcW : Summable fun n => c n ^ 2 * (5 * n * (1 + Real.log n))) (T : ℝ) :
    (∀ m, c m ≠ 0 → |(∫ t in T..2 * T, windowCosSeries c t * Real.cos (2 * π * t * Real.log m)) -
        T / 2 * c m| ≤ 3 * (∑' n, |c n|) + M * (5 * m * (1 + Real.log m))) ∧
      |(∫ t in T..2 * T, windowCosSeries c t ^ 2) - T / 2 * ∑' n, c n ^ 2| ≤
        3 * (∑' n, |c n|) ^ 2 + ∑' n, c n ^ 2 * (5 * n * (1 + Real.log n)) := by
  set A1 := ∑' n, |c n| with hA1def
  have hA10 : 0 ≤ A1 := tsum_nonneg fun _ => abs_nonneg _
  set W : ℕ → ℝ := fun n => 5 * n * (1 + Real.log n) with hWdef
  have hWle : ∀ k, ∑' n, nearLogKernel n k ≤ W k := fun k => tsum_nearLogKernel_le k
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  have hnear : ∀ k, Summable fun n => |c n| * nearLogKernel n k := fun k =>
    summable_of_ne_finset_zero (s := Finset.range (2 * k + 1)) fun n hn => by
      rw [Finset.mem_range] at hn; rw [nearLogKernel_eq_zero_of_lt (by omega), mul_zero]
  have hnearb : ∀ k, ∑' n, |c n| * nearLogKernel n k ≤ M * W k := by
    intro k
    have hpt : ∀ n, |c n| * nearLogKernel n k ≤ M * nearLogKernel n k := fun n =>
      mul_le_mul_of_nonneg_right (hM n) (nearLogKernel_nonneg n k)
    calc ∑' n, |c n| * nearLogKernel n k ≤ ∑' n, M * nearLogKernel n k :=
          (hnear k).tsum_le_tsum hpt ((summable_nearLogKernel k).mul_left _)
      _ = M * ∑' n, nearLogKernel n k := tsum_mul_left
      _ ≤ M * W k := mul_le_mul_of_nonneg_left (hWle k) hM0
  have hker0 : ∀ n k, 0 ≤ intLogKernel n k := fun n k => by
    unfold intLogKernel; split_ifs <;> positivity
  have hRk : ∀ k, 2 ≤ k → Summable (fun n => |c n| * intLogKernel n k) ∧
      ∑' n, |c n| * intLogKernel n k ≤ 3 * A1 + ∑' n, |c n| * nearLogKernel n k := by
    intro k hk
    have hpt : ∀ n, |c n| * intLogKernel n k ≤ 3 * |c n| + |c n| * nearLogKernel n k := fun n => by
      have := mul_le_mul_of_nonneg_left (intLogKernel_le_three_add_near hk n) (abs_nonneg (c n))
      linarith
    have hs2 := (hc.mul_left 3).add (hnear k)
    have hs := hs2.of_nonneg_of_le (fun n => mul_nonneg (abs_nonneg _) (hker0 n k)) hpt
    refine ⟨hs, (hs.tsum_le_tsum hpt hs2).trans (le_of_eq ?_)⟩
    rw [(hc.mul_left 3).tsum_add (hnear k), tsum_mul_left]
  set R : ℕ → ℝ := fun k => ∑' n, |c n| * intLogKernel n k with hRdef
  have hext : ∀ k, c k ≠ 0 → ∀ a b : ℝ,
      |(∫ t in a..b, windowCosSeries c t * Real.cos (2 * π * t * Real.log k)) -
        (b - a) / 2 * c k| ≤ R k := by
    intro k hk a b
    have hk2 : 2 ≤ k := hc2 k hk
    exact abs_integral_windowCosSeries_mul_cos_sub_le_of_bound hc a b
      (fun n => abs_meanKernel_le_intLogKernel (c := c) hc2 hk2 a b n) (hRk k hk2).1
  obtain ⟨hSch, hSchb⟩ := tsum_abs_mul_tsum_nearLogKernel_le (c := c) hWle hcW
  have hRpt : ∀ k, |c k| * R k ≤ 3 * A1 * |c k| + |c k| * ∑' n, |c n| * nearLogKernel n k := by
    intro k
    by_cases hk : c k = 0
    · rw [hk, abs_zero, zero_mul, mul_zero, zero_mul, add_zero]
    have := mul_le_mul_of_nonneg_left (hRk k (hc2 k hk)).2 (abs_nonneg (c k))
    simp only [hRdef]
    linarith
  have hRs2 := (hc.mul_left (3 * A1)).add hSch
  have hRs : Summable fun k => |c k| * R k :=
    hRs2.of_nonneg_of_le (fun k => mul_nonneg (abs_nonneg _)
      (tsum_nonneg fun n => mul_nonneg (abs_nonneg _) (hker0 n k))) hRpt
  have hQQ : ∑' k, |c k| * R k ≤ 3 * A1 ^ 2 + ∑' n, c n ^ 2 * W n := by
    have h1 : ∑' k, |c k| * R k ≤ ∑' k, (3 * A1 * |c k| +
        |c k| * ∑' n, |c n| * nearLogKernel n k) := hRs.tsum_le_tsum hRpt hRs2
    rw [(hc.mul_left (3 * A1)).tsum_add hSch, tsum_mul_left, ← hA1def] at h1
    have e : 3 * A1 * A1 = 3 * A1 ^ 2 := by ring
    linarith
  refine ⟨fun m hm => ?_, ?_⟩
  · have h := hext m hm T (2 * T)
    rw [show 2 * T - T = T by ring] at h
    refine h.trans ?_
    have hm2 := hc2 m hm
    exact (hRk m hm2).2.trans (by linarith [hnearb m])
  · have h := abs_integral_windowCosSeries_sq_sub_le_of_bound hc T (2 * T)
      (fun k hk => hext k hk T (2 * T)) hRs
    rw [show 2 * T - T = T by ring] at h
    exact h.trans hQQ

/-- The size bookkeeping of the log-weighted rigidity argument (pure real arithmetic). -/
theorem log_square_sizes_le {A1 Kp Ha KJ Tη Av Wm Cd Sw : ℝ} (hA10 : 0 ≤ A1) (hA1 : A1 ≤ Kp * Ha)
    (hKpT : Kp ≤ KJ * Tη) (hKp2 : Kp ^ 2 = KJ ^ 2 * Tη) (hHa0 : 0 ≤ Ha) (hAv : 0 ≤ Av)
    (hWm : 0 ≤ Wm) (hSw : Sw ≤ 5 * Kp ^ 2 * Cd) :
    A1 ≤ KJ * Ha * Tη ∧ 3 * A1 ^ 2 + Sw ≤ KJ ^ 2 * (3 * Ha ^ 2 + 5 * Cd) * Tη ∧
      3 * A1 + Kp * Av * Wm ≤ KJ * (3 * Ha + Av * Wm) * Tη := by
  have hA1sq : A1 ^ 2 ≤ (Kp * Ha) ^ 2 := pow_le_pow_left₀ hA10 hA1 2
  have e1 : (Kp * Ha) ^ 2 = KJ ^ 2 * Tη * Ha ^ 2 := by rw [mul_pow, hKp2]
  have hAW : 0 ≤ Av * Wm := mul_nonneg hAv hWm
  refine ⟨?_, ?_, ?_⟩
  · have := mul_le_mul_of_nonneg_right hKpT hHa0
    nlinarith
  · have e2 : KJ ^ 2 * (3 * Ha ^ 2 + 5 * Cd) * Tη = 3 * (KJ ^ 2 * Tη * Ha ^ 2) + 5 * (KJ ^ 2 * Tη) * Cd :=
      by ring
    rw [e2, ← hKp2]; nlinarith
  · have h1 := mul_le_mul_of_nonneg_right hKpT (show 0 ≤ 3 * Ha + Av * Wm by positivity)
    nlinarith

/-- **Log-weighted square-summable rigidity.** A full-cone Weil-positive system with
`Σ_n (lam(n) − Λ(n))² / (1 + log n)^K < ∞` is `Λ`. -/
theorem eq_vonMangoldt_of_weilPositiveFull_of_log_square_summable {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) {K : ℕ}
    (hdev : Summable fun n : ℕ => (lam n - ArithmeticFunction.vonMangoldt n) ^ 2 *
      ((1 + Real.log n) ^ K)⁻¹) :
    ∀ m, 2 ≤ m → lam m = ArithmeticFunction.vonMangoldt m := by
  set v := normDeficit lam with hvdef
  have hv2 : ∀ n, v n ≠ 0 → 2 ≤ n := by
    intro n hn; by_contra h; exact hn (by simp only [hvdef, normDeficit, if_neg h])
  set dq : ℕ → ℝ := fun n => (lam n - ArithmeticFunction.vonMangoldt n) ^ 2 *
    ((1 + Real.log n) ^ K)⁻¹ with hdq
  have hdq0 : ∀ n, 0 ≤ dq n := fun n => by
    have := Real.log_natCast_nonneg n; simp only [hdq]; positivity
  set Cd := ∑' n, dq n with hCd
  have hCd0 : 0 ≤ Cd := tsum_nonneg hdq0
  have hdqC : ∀ n, dq n ≤ Cd := fun n => hdev.le_tsum n fun j _ => hdq0 j
  set Kf : ℝ := K.factorial * Real.exp 1 with hKf
  have hKf0 : 0 ≤ Kf := by positivity
  have hv2b : ∀ n, v n ^ 2 ≤ Kf * dq n := fun n => normDeficit_sq_le lam K n
  set Av := 1 + Kf * Cd with hAv
  have hAv0 : 0 ≤ Av := by positivity
  have hA : ∀ n, |v n| ≤ Av := by
    intro n
    have h1 : v n ^ 2 ≤ Kf * Cd := (hv2b n).trans (mul_le_mul_of_nonneg_left (hdqC n) hKf0)
    have h2 : |v n| ≤ 1 + v n ^ 2 := by
      rw [← sq_abs]; nlinarith [sq_nonneg (|v n| - 1), abs_nonneg (v n)]
    rw [hAv]; linarith
  have hsq : Summable fun n => v n ^ 2 :=
    (hdev.mul_left Kf).of_nonneg_of_le (fun n => sq_nonneg _) hv2b
  set V := ∑' n, v n ^ 2 with hV
  have hV0 : 0 ≤ V := tsum_nonneg fun _ => sq_nonneg _
  set J := K + 2 with hJ
  have hF4 := summable_invLogWeight (D := K + 4) (by omega)
  set S4 := ∑' n, invLogWeight (K + 4) n with hS4
  have hS40 : 0 ≤ S4 := tsum_nonneg fun n => invLogWeight_nonneg _ n
  have hvw : ∀ n, |v n| * ((1 + Real.log n) ^ J)⁻¹ ≤ (dq n + invLogWeight (K + 4) n) / 2 :=
    fun n => abs_normDeficit_mul_inv_pow_le lam K n
  have hZs : Summable fun n => |v n| * ((1 + Real.log n) ^ J)⁻¹ :=
    ((hdev.add hF4).div_const 2).of_nonneg_of_le (fun n => by
      have := Real.log_natCast_nonneg n; positivity) hvw
  have hZ : Summable fun n : ℕ => |v n| * ((1 + |Real.log n|) ^ J)⁻¹ :=
    hZs.congr fun n => by rw [abs_of_nonneg (Real.log_natCast_nonneg n)]
  set Ha := (Cd + S4) / 2 with hHa
  have hHa0 : 0 ≤ Ha := by positivity
  have hZsum : ∑' n, |v n| * ((1 + Real.log n) ^ J)⁻¹ ≤ Ha := by
    calc ∑' n, |v n| * ((1 + Real.log n) ^ J)⁻¹ ≤ ∑' n, (dq n + invLogWeight (K + 4) n) / 2 :=
          hZs.tsum_le_tsum hvw ((hdev.add hF4).div_const 2)
      _ = Ha := by rw [tsum_div_const, hdev.tsum_add hF4]
  -- constants
  have hB0 := bumpCos_zero_pos
  set B0 := bumpCos 0 with hB0def
  obtain ⟨KJ, hKJ0, hKJ⟩ := exists_abs_bumpCos_le J
  set cf : ℝ → ℕ → ℝ := fun η n => v n * bumpCos (η * Real.log n) with hcf
  have hbump : ∀ η, 0 < η → η ≤ 1 → ∀ n : ℕ,
      |bumpCos (η * Real.log n)| ≤ KJ * (η ^ J)⁻¹ * ((1 + Real.log n) ^ J)⁻¹ := by
    intro η hη0 hη1 n
    have hl := Real.log_natCast_nonneg n
    have h2 := hKJ (η * Real.log n)
    rw [abs_of_nonneg (by positivity : 0 ≤ η * Real.log n)] at h2
    have h3 := pow_mul_one_add_pow_le hη0 hη1 hl J
    have h5 : ((1 + η * Real.log n) ^ J)⁻¹ ≤ (η ^ J)⁻¹ * ((1 + Real.log n) ^ J)⁻¹ := by
      rw [← mul_inv]; exact inv_anti₀ (by positivity) h3
    calc |bumpCos (η * Real.log n)| ≤ KJ * ((1 + η * Real.log n) ^ J)⁻¹ := h2
      _ ≤ KJ * ((η ^ J)⁻¹ * ((1 + Real.log n) ^ J)⁻¹) := mul_le_mul_of_nonneg_left h5 hKJ0
      _ = _ := by ring
  have hcfw : ∀ η, 0 < η → η ≤ 1 → ∀ n,
      |cf η n| ≤ KJ * (η ^ J)⁻¹ * (|v n| * ((1 + Real.log n) ^ J)⁻¹) := by
    intro η hη0 hη1 n
    simp only [hcf]; rw [abs_mul]
    calc |v n| * |bumpCos (η * Real.log n)| ≤
          |v n| * (KJ * (η ^ J)⁻¹ * ((1 + Real.log n) ^ J)⁻¹) :=
          mul_le_mul_of_nonneg_left (hbump η hη0 hη1 n) (abs_nonneg _)
      _ = _ := by ring
  have hcfA : ∀ η, 0 < η → η ≤ 1 → ∀ n, |cf η n| ≤ KJ * (η ^ J)⁻¹ * Av := by
    intro η hη0 hη1 n
    refine (hcfw η hη0 hη1 n).trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
    have hl := Real.log_natCast_nonneg n
    have : ((1 + Real.log n) ^ J)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by linarith))
    calc |v n| * ((1 + Real.log n) ^ J)⁻¹ ≤ |v n| * 1 :=
          mul_le_mul_of_nonneg_left this (abs_nonneg _)
      _ ≤ Av := by rw [mul_one]; exact hA n
  have hcs : ∀ η, ∑' n, cf η n ^ 2 ≤ B0 ^ 2 * V := by
    intro η
    have hpt : ∀ n, cf η n ^ 2 ≤ B0 ^ 2 * v n ^ 2 := by
      intro n
      simp only [hcf]
      rw [mul_pow, mul_comm]
      refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
      rw [← sq_abs, ← sq_abs B0]
      exact pow_le_pow_left₀ (abs_nonneg _) ((abs_bumpCos_le _).trans (le_abs_self _)) 2
    calc ∑' n, cf η n ^ 2 ≤ ∑' n, B0 ^ 2 * v n ^ 2 :=
          ((hsq.mul_left _).of_nonneg_of_le (fun _ => sq_nonneg _) hpt).tsum_le_tsum hpt
            (hsq.mul_left _)
      _ = B0 ^ 2 * V := tsum_mul_left
  have hU0 : ∀ a, 0 ≤ unitZeroBound a := fun a =>
    le_trans (Nat.cast_nonneg _) (realZeroSet_unit a).2
  have hmain : ∀ m, v m = 0 := by
    intro m
    by_contra hm
    have hm2 := hv2 m hm
    have key : ∀ ε > 0, |v m| * (B0 / 2) ≤ ε := by
      intro ε hε
      set l := 4 * (B0 ^ 2 * V + 1) / ε with hl
      have hl0 : 0 < l := by positivity
      set CX := 8 * (1 + π ^ 2) with hCX
      set a0 := |xiLineTwoLogDerivConstant| + Real.log 50 with ha0
      set p : ℕ := 2 * J + 1 with hp
      have hlm : 0 ≤ Real.log m := Real.log_natCast_nonneg m
      set Wm := 5 * (m : ℝ) * (1 + Real.log m) with hWm
      have hWm0 : 0 ≤ Wm := by positivity
      set H := 2 * (KJ * Ha) / (π * Real.log 2) + 2 * (KJ ^ 2 * (3 * Ha ^ 2 + 5 * Cd)) / l +
        2 * (KJ * (3 * Ha + Av * Wm)) with hH
      have hH0 : 0 ≤ H := by
        have : 0 < Real.log 2 := Real.log_pos (by norm_num)
        positivity
      have hev1 : ∀ᶠ η in 𝓝[>] (0 : ℝ), 0 < η ∧ η ≤ 1 := by
        filter_upwards [Ioc_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with η hη
        exact ⟨hη.1, hη.2⟩
      have hev2 : ∀ᶠ η in 𝓝[>] (0 : ℝ), B0 / 2 < bumpCos (η * Real.log m) := by
        have ht : Tendsto (fun η : ℝ => bumpCos (η * Real.log m)) (𝓝 0) (𝓝 B0) := by
          have hc : Continuous fun η : ℝ => bumpCos (η * Real.log m) :=
            continuous_bumpCos.comp (continuous_id.mul continuous_const)
          have := hc.tendsto 0
          simpa [hB0def] using this
        exact nhdsWithin_le_nhds (ht.eventually_const_lt (by linarith))
      have hev3 : ∀ᶠ η in 𝓝[>] (0 : ℝ),
          16 * l * (CX * (a0 * η - (p : ℝ) * (η * Real.log η))) ≤ ε / 4 := by
        have ht : Tendsto (fun η : ℝ => 16 * l * (CX * (a0 * η - (p : ℝ) * (η * Real.log η))))
            (𝓝 0) (𝓝 0) := by
          have h1 : Tendsto (fun η : ℝ => η * Real.log η) (𝓝 0) (𝓝 0) := by
            have := Real.continuous_mul_log.tendsto 0; simpa using this
          have := (((tendsto_id.const_mul a0).sub (h1.const_mul (p : ℝ))).const_mul CX).const_mul
            (16 * l)
          simpa using this
        exact nhdsWithin_le_nhds (ht.eventually_le_const (by positivity))
      have hev4 : ∀ᶠ η in 𝓝[>] (0 : ℝ), η * H ≤ ε / 2 := by
        have ht : Tendsto (fun η : ℝ => η * H) (𝓝 0) (𝓝 0) := by
          have := (tendsto_id (x := 𝓝 (0 : ℝ))).mul_const H; simpa using this
        exact nhdsWithin_le_nhds (ht.eventually_le_const (by positivity))
      obtain ⟨η, hηall⟩ := (((hev1.and hev2).and hev3).and hev4).exists
      obtain ⟨⟨⟨⟨hη0, hη1⟩, hη2⟩, hη3⟩, hη4⟩ := hηall
      set y := η⁻¹ with hy
      have hy1 : 1 ≤ y := (one_le_inv₀ hη0).mpr hη1
      set T := y ^ p with hT
      have hT1 : 1 ≤ T := one_le_pow₀ hy1
      set Kp := KJ * (η ^ J)⁻¹ with hKp
      have hKp0 : 0 ≤ Kp := by positivity
      have hcs1 : Summable fun n => |cf η n| :=
        (hZs.mul_left Kp).of_nonneg_of_le (fun _ => abs_nonneg _) (hcfw η hη0 hη1)
      have hA1 : ∑' n, |cf η n| ≤ Kp * Ha := by
        calc ∑' n, |cf η n| ≤ ∑' n, Kp * (|v n| * ((1 + Real.log n) ^ J)⁻¹) :=
              hcs1.tsum_le_tsum (hcfw η hη0 hη1) (hZs.mul_left Kp)
          _ = Kp * ∑' n, |v n| * ((1 + Real.log n) ^ J)⁻¹ := tsum_mul_left
          _ ≤ Kp * Ha := mul_le_mul_of_nonneg_left hZsum hKp0
      have hcWpt : ∀ n, cf η n ^ 2 * (5 * n * (1 + Real.log n)) ≤ 5 * Kp ^ 2 * dq n := fun n =>
        normDeficit_mul_sq_mul_le lam (K := K) (J := J) (by omega) n (hbump η hη0 hη1 n)
      have hcWs : Summable fun n => cf η n ^ 2 * (5 * n * (1 + Real.log n)) :=
        (hdev.mul_left (5 * Kp ^ 2)).of_nonneg_of_le (fun n => by
          have := Real.log_natCast_nonneg n; positivity) hcWpt
      have hcWb : ∑' n, cf η n ^ 2 * (5 * n * (1 + Real.log n)) ≤ 5 * Kp ^ 2 * Cd := by
        rw [hCd, ← tsum_mul_left]; exact hcWs.tsum_le_tsum hcWpt (hdev.mul_left _)
      have hc2' : ∀ n, cf η n ≠ 0 → 2 ≤ n := fun n hn => hv2 n (left_ne_zero_of_mul hn)
      obtain ⟨hextb, hsqb⟩ := windowCosSeries_meanValue_bounds_near hc2' hcs1 (hcfA η hη0 hη1)
        hcWs T
      have hbm : 0 < bumpCos (η * Real.log m) := by linarith
      have hcm : cf η m ≠ 0 := by simp only [hcf]; exact mul_ne_zero hm hbm.ne'
      have hext' := hextb m hcm
      have hpos : ∀ t, T ≤ t → t ≤ 2 * T → (∀ ξ, |ξ - t| < η → phiFourierReal ξ ≠ 0) →
          0 ≤ windowCosSeries (cf η) t := by
        intro t _ _ hfree
        have := localized_deviation_nonneg hW hA hZ hη0 (ξ₀ := t) hfree
        simpa [windowCosSeries, hcf] using this
      have hass := half_mul_abs_le_of_zeroFree_of_bounds hc2' hcs1 hT1 hl0 hη0 hη1 hpos hext' hsqb
      -- sizes
      have hyJ : (η ^ J)⁻¹ = y ^ J := by rw [hy, inv_pow]
      have hTη : T * η = y ^ (2 * J) := by
        rw [hT, hp, pow_succ, mul_assoc, hy, inv_mul_cancel₀ hη0.ne', mul_one]
      have hyJ2 : y ^ J ≤ y ^ (2 * J) := pow_le_pow_right₀ hy1 (by omega)
      have hKpT : Kp ≤ KJ * (T * η) := by
        rw [hKp, hyJ, hTη]; exact mul_le_mul_of_nonneg_left hyJ2 hKJ0
      have hKp2 : Kp ^ 2 = KJ ^ 2 * (T * η) := by
        rw [hKp, hyJ, hTη, mul_pow, ← pow_mul, mul_comm J 2]
      obtain ⟨A1, hA1def⟩ : ∃ A1, A1 = ∑' n, |cf η n| := ⟨_, rfl⟩
      have hA10 : 0 ≤ A1 := hA1def ▸ tsum_nonneg fun _ => abs_nonneg _
      obtain ⟨hA1', hQQ', hRm'⟩ := log_square_sizes_le (Tη := T * η) (Cd := Cd) (Av := Av)
        (Wm := Wm) (Sw := ∑' n, cf η n ^ 2 * (5 * n * (1 + Real.log n))) hA10 (hA1def ▸ hA1)
        hKpT hKp2 hHa0 hAv0 hWm0 hcWb
      rw [hA1def] at hA1' hQQ' hRm'
      have hS2' := hcs η
      -- the zero count
      have hceil : (⌈T⌉₊ : ℝ) < T + 1 := Nat.ceil_lt_add_one (by linarith)
      have hN1 : (((⌈T⌉₊ + 1 : ℕ) : ℝ) + 1) ≤ 4 * T := by push_cast; linarith
      have hU1 : unitZeroBound (|T - 1| + (((⌈T⌉₊ + 1 : ℕ) : ℝ) + 1)) ≤ unitZeroBound (5 * T) := by
        refine unitZeroBound_le_of_le (by linarith) ?_
        rw [abs_of_nonneg (by rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ T - 1)]; positivity)]
        rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ T - 1)]
        push_cast; linarith
      have hU5 := unitZeroBound_five_mul_le hT1
      have hlogT : Real.log T = -((p : ℝ) * Real.log η) := by
        rw [hT, Real.log_pow, hy, Real.log_inv]; ring
      have hZc : (((⌈T⌉₊ + 1 : ℕ) : ℝ) + 1) * unitZeroBound (|T - 1| + (((⌈T⌉₊ + 1 : ℕ) : ℝ) + 1))
          ≤ 4 * T * (CX * (a0 * 1 - (p : ℝ) * Real.log η)) := by
        have hUpos := hU0 (|T - 1| + (((⌈T⌉₊ + 1 : ℕ) : ℝ) + 1))
        calc (((⌈T⌉₊ + 1 : ℕ) : ℝ) + 1) * unitZeroBound (|T - 1| + (((⌈T⌉₊ + 1 : ℕ) : ℝ) + 1))
            ≤ 4 * T * unitZeroBound (5 * T) :=
              mul_le_mul hN1 hU1 hUpos (by linarith)
          _ ≤ 4 * T * (CX * (a0 + Real.log T)) := mul_le_mul_of_nonneg_left hU5 (by linarith)
          _ = 4 * T * (CX * (a0 * 1 - (p : ℝ) * Real.log η)) := by rw [hlogT]; ring
      have hB2V : B0 ^ 2 * V / l ≤ ε / 4 := by
        rw [hl]; exact div_four_mul_add_one_div_le (by positivity) hε
      have hcfm : |cf η m| ≤ ε :=
        le_of_assembly_bounds_general (x := |cf η m|) (T := T) (η := η) (ε := ε) (l := l)
          (Ka := KJ * Ha) (Kq := KJ ^ 2 * (3 * Ha ^ 2 + 5 * Cd)) (Kr := KJ * (3 * Ha + Av * Wm))
          (QQ := 3 * (∑' n, |cf η n|) ^ 2 + ∑' n, cf η n ^ 2 * (5 * n * (1 + Real.log n)))
          (Rm := 3 * (∑' n, |cf η n|) + Kp * Av * Wm) (A1 := ∑' n, |cf η n|)
          (S2 := ∑' n, cf η n ^ 2)
          (Zc := (((⌈T⌉₊ + 1 : ℕ) : ℝ) + 1) * unitZeroBound (|T - 1| + (((⌈T⌉₊ + 1 : ℕ) : ℝ) + 1)))
          (B2V := B0 ^ 2 * V) (CX := CX) (a0 := a0) (P := (p : ℝ)) (L2 := π * Real.log 2)
          hT1 hl0 hη0 (by positivity) hass hA1' hQQ' hRm' hS2' hB2V hZc hη3 hη4
      calc |v m| * (B0 / 2) ≤ |v m| * |bumpCos (η * Real.log m)| :=
            mul_le_mul_of_nonneg_left (by rw [abs_of_pos hbm]; linarith) (abs_nonneg _)
        _ = |cf η m| := by simp only [hcf, abs_mul]
        _ ≤ ε := hcfm
    have h0 : |v m| * (B0 / 2) ≤ 0 := le_of_forall_pos_le_add fun ε hε => by
      have := key ε hε; linarith
    have : |v m| * (B0 / 2) = 0 := le_antisymm h0 (by positivity)
    rcases mul_eq_zero.mp this with h | h
    · exact hm (abs_eq_zero.mp h)
    · linarith
  intro m hm2
  have hv := hmain m
  simp only [hvdef, normDeficit, if_pos hm2] at hv
  have hsq0 : Real.sqrt m ≠ 0 := (Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < m))).ne'
  rw [div_eq_zero_iff, sub_eq_zero] at hv
  rcases hv with hv | hv
  · exact hv.symm
  · exact absurd hv hsq0

/-- **RH as a log-weighted square-summable deformation problem.** -/
theorem riemannHypothesis_iff_exists_weilPositiveFull_log_square_summable :
    RiemannHypothesis ↔ ∃ lam : ℕ → ℝ, WeilPositiveFull lam ∧ ∃ K : ℕ,
      Summable fun n : ℕ => (lam n - ArithmeticFunction.vonMangoldt n) ^ 2 *
        ((1 + Real.log n) ^ K)⁻¹ := by
  constructor
  · intro hRH
    refine ⟨_, riemannHypothesis_iff_weilPositiveFull_vonMangoldt.mp hRH, 0, ?_⟩
    simp
  · rintro ⟨lam, hW, K, hdev⟩
    have h := eq_vonMangoldt_of_weilPositiveFull_of_log_square_summable hW hdev
    refine riemannHypothesis_iff_weilPositiveFull_vonMangoldt.mpr fun f hf hfc => ?_
    rw [weilFullFunctional_congr (lam' := lam) (fun n hn => (h n hn).symm)]
    exact hW f hf hfc

end

end RHTower

