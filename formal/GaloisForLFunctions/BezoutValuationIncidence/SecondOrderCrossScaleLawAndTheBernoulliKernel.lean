import GaloisForLFunctions.BezoutValuationIncidence.LargeSieveDispersionInSelbergCoordinates

/-!
# The second-order cross-scale law and the Bernoulli kernel

The centered residue `r_d(M) = (M mod d) - (d-1)/2` has the mean-zero second primitive

`Φ_d(M) = (d² - 1)/12 - ρ(d - ρ)/2 = (d²/2) B₂(ρ/d) - 1/12`,  `ρ = M mod d`,

with `Φ_d(M+1) - Φ_d(M) = r_d(M)`, `|Φ_d| ≤ d²/8` and interval sums at most `d³/8`. Summation by
parts against the pronic weight `w(M) = 1/(M(M+1))`, done twice, gives for `1 ≤ A < H`

`Σ_{A ≤ M < H} r_d(M) w(M) = Φ_d(H) w(H-1) - Φ_d(A) w(A) + O(d³ (w(A) - w(A+1)))`.

Inserted into the step decomposition `⌊M/n⌋ = Σ_j 1[jn ≤ M]` of the exact rank-two law, this
identifies the cross-scale remainder at second order. With the **Bernoulli kernel**

`𝔅(d, n) = Σ_{j ≥ 1} Φ_d(jn)/j²`,

which depends on `n` only through `n mod d`, every pair of rows `c, c'` satisfies

`|B(c, c') + m(c) R(c') + β(c) H(c') - Σ_{n, d} c'(n) c(d) 𝔅(d, n)/(d n²)|
  ≤ ¾ (Σ_d |c(d)| d²) (Σ_n |c'(n)|/n³)`.

For two primes `p < q` this reads `𝒢^{ec}(p, q) = -pq (m R + β H) + 𝔅(p, q)/q + O(p³/q²)`: the
fine cross-scale structure of the pronic Gram is a function of `q mod p` of size `p²/q`, and the
error is smaller by the factor `p/q`. Since `Φ_d = (d²/2) B₂ - 1/12`,
`𝔅(d, n) = (d²/2) Σ_j B₂({jn/d})/j² - π²/72`; the constant splits off one more rank-one term
`-(π²/72) (Σ_d c(d)/d)(Σ_n c'(n)/n²)`, and the Fourier series `B₂({x}) = π⁻² Σ_k cos(2πkx)/k²` makes
`Σ_j B₂({jx})/j²` the Estermann cosine series `π⁻² Σ_h d(h) cos(2πhx)/h²` at `x = n/d`.
-/

open Finset Filter Topology RHTower GaloisForLFunctions.BiScaleUncertainty
open scoped BigOperators

namespace GaloisForLFunctions.BezoutValuationIncidence

noncomputable section
set_option autoImplicit false

/-! ## §1. The residue potential -/

/-- The mean-zero second primitive `Φ_d(M) = (d² - 1)/12 - ρ(d - ρ)/2`, `ρ = M mod d`, of the
centered residue. -/
def residuePotential (d M : ℕ) : ℝ :=
  ((d : ℝ) ^ 2 - 1) / 12 - ((M % d : ℕ) : ℝ) * ((d : ℝ) - ((M % d : ℕ) : ℝ)) / 2

/-- `Φ_d(M) = (d²/2) B₂(ρ/d) - 1/12` with `B₂(x) = x² - x + 1/6`. -/
theorem residuePotential_eq_bernoulli {d : ℕ} (hd : 0 < d) (M : ℕ) :
    residuePotential d M = (d : ℝ) ^ 2 / 2 *
      ((((M % d : ℕ) : ℝ) / d) ^ 2 - ((M % d : ℕ) : ℝ) / d + 1 / 6) - 1 / 12 := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  unfold residuePotential
  field_simp
  ring

/-- The potential is a second primitive: `Φ_d(M + 1) - Φ_d(M) = r_d(M)`. -/
theorem residuePotential_succ_sub {d : ℕ} (hd : 0 < d) (M : ℕ) :
    residuePotential d (M + 1) - residuePotential d M = centeredResidue d M := by
  have hlt := Nat.mod_lt M hd
  unfold residuePotential centeredResidue
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

theorem residuePotential_add_period (d M : ℕ) :
    residuePotential d (M + d) = residuePotential d M := by
  simp [residuePotential, Nat.add_mod_right]

theorem abs_residuePotential_le {d : ℕ} (hd : 0 < d) (M : ℕ) :
    |residuePotential d M| ≤ (d : ℝ) ^ 2 / 8 := by
  have hlt := Nat.mod_lt M hd
  have hr0 : (0 : ℝ) ≤ ((M % d : ℕ) : ℝ) := Nat.cast_nonneg _
  have hrd : ((M % d : ℕ) : ℝ) ≤ d := by exact_mod_cast hlt.le
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  unfold residuePotential
  rw [abs_le]
  constructor
  · nlinarith [sq_nonneg ((d : ℝ) - 2 * ((M % d : ℕ) : ℝ))]
  · nlinarith [mul_nonneg hr0 (sub_nonneg.mpr hrd)]

theorem sum_range_cast_eq (n : ℕ) : ∑ i ∈ range n, (i : ℝ) = (n : ℝ) * ((n : ℝ) - 1) / 2 := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

theorem sum_range_cast_sq_eq (n : ℕ) :
    ∑ i ∈ range n, (i : ℝ) ^ 2 = ((n : ℝ) - 1) * n * (2 * n - 1) / 6 := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

theorem sum_Ico_residuePotential_period {d : ℕ} (hd : 0 < d) (N : ℕ) :
    ∑ M ∈ Ico N (N + d), residuePotential d M = 0 := by
  induction N with
  | zero =>
    rw [zero_add, ← Finset.range_eq_Ico]
    rw [sum_congr rfl fun M hM => by rw [residuePotential, Nat.mod_eq_of_lt (mem_range.mp hM)]]
    rw [sum_sub_distrib, sum_const, card_range, nsmul_eq_mul, ← sum_div]
    simp_rw [show ∀ i : ℕ, (i : ℝ) * ((d : ℝ) - i) = (d : ℝ) * i - (i : ℝ) ^ 2 from
      fun i => by ring]
    rw [sum_sub_distrib, ← mul_sum, sum_range_cast_eq, sum_range_cast_sq_eq]
    ring
  | succ N ih =>
    rw [show N + 1 + d = N + d + 1 by ring, sum_Ico_succ_top (by omega),
      ← sum_Ico_consecutive _ (Nat.le_succ N) (by omega : N + 1 ≤ N + d)] at *
    have hN : ∑ M ∈ Ico N (N + 1), residuePotential d M = residuePotential d N := by simp
    have hper := residuePotential_add_period d N
    linarith

/-- Interval sums of the potential are at most `d³/8`. -/
theorem abs_sum_Ico_residuePotential_le {d : ℕ} (hd : 0 < d) (N K : ℕ) :
    |∑ M ∈ Ico N (N + K), residuePotential d M| ≤ (d : ℝ) ^ 3 / 8 := by
  induction K using Nat.strong_induction_on generalizing N with
  | _ K ih =>
    by_cases hK : K < d
    · calc |∑ M ∈ Ico N (N + K), residuePotential d M|
          ≤ ∑ M ∈ Ico N (N + K), |residuePotential d M| := abs_sum_le_sum_abs _ _
        _ ≤ ∑ _M ∈ Ico N (N + K), (d : ℝ) ^ 2 / 8 :=
          sum_le_sum fun M _ => abs_residuePotential_le hd M
        _ = K * ((d : ℝ) ^ 2 / 8) := by rw [sum_const, Nat.card_Ico]; simp
        _ ≤ (d : ℝ) ^ 3 / 8 := by
          have : (K : ℝ) ≤ d := by exact_mod_cast hK.le
          have : (0 : ℝ) ≤ (d : ℝ) ^ 2 := sq_nonneg _
          nlinarith
    · replace hK := not_lt.mp hK
      rw [show N + K = (N + d) + (K - d) by omega,
        ← sum_Ico_consecutive _ (by omega : N ≤ N + d) (by omega : N + d ≤ N + d + (K - d)),
        sum_Ico_residuePotential_period hd N, zero_add]
      exact ih (K - d) (by omega) (N + d)

/-! ## §2. Second summation by parts against the pronic weight -/

/-- Exact summation by parts: `Σ_{A ≤ M ≤ A+k} r_d(M) w(M) = Φ_d(A+k+1) w(A+k) - Φ_d(A) w(A)
+ Σ_{A ≤ M < A+k} Φ_d(M+1) (w(M) - w(M+1))`. -/
theorem sum_Ico_centeredResidue_mul_pw_eq {d : ℕ} (hd : 0 < d) (A k : ℕ) :
    ∑ M ∈ Ico A (A + k + 1), centeredResidue d M * pw M =
      residuePotential d (A + k + 1) * pw (A + k) - residuePotential d A * pw A +
        ∑ M ∈ Ico A (A + k), residuePotential d (M + 1) * (pw M - pw (M + 1)) := by
  induction k with
  | zero =>
    simp only [add_zero, Ico_self, sum_empty]
    rw [show A + 1 = A + 1 from rfl, sum_Ico_succ_top le_rfl, Ico_self, sum_empty, zero_add,
      ← residuePotential_succ_sub hd A]
    ring
  | succ k ih =>
    rw [show A + (k + 1) + 1 = A + k + 1 + 1 by ring, sum_Ico_succ_top (by omega), ih,
      show A + (k + 1) = A + k + 1 by ring, sum_Ico_succ_top (by omega : A ≤ A + k),
      ← residuePotential_succ_sub hd (A + k + 1)]
    ring

theorem pw_sub_pw_succ_nonneg {M : ℕ} (hM : 1 ≤ M) : 0 ≤ pw M - pw (M + 1) := by
  rw [pw_sub_pw_succ hM]; positivity

/-- The second Abel step: `|Σ_{A ≤ M < A+k} Φ_d(M+1) (w(M) - w(M+1))| ≤ (d³/8) (w(A) - w(A+1))`. -/
theorem abs_sum_Ico_residuePotential_mul_pw_sub_le {d A : ℕ} (hd : 0 < d) (hA : 1 ≤ A) (k : ℕ) :
    |∑ M ∈ Ico A (A + k), residuePotential d (M + 1) * (pw M - pw (M + 1))| ≤
      (d : ℝ) ^ 3 / 8 * (pw A - pw (A + 1)) := by
  set g : ℕ → ℝ := fun i => pw (A + i) - pw (A + i + 1)
  set x : ℕ → ℝ := fun i => residuePotential d (A + i + 1)
  have hg0 : ∀ i, 0 ≤ g i := fun i => pw_sub_pw_succ_nonneg (by omega)
  have hanti : Antitone g := by
    refine antitone_nat_of_succ_le fun i => ?_
    simp only [g]
    rw [pw_sub_pw_succ (by omega), pw_sub_pw_succ (by omega)]
    have h1 : (1 : ℝ) ≤ ((A + i : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ A + i)
    push_cast at h1 ⊢
    refine div_le_div_of_nonneg_left (by norm_num) (by positivity) ?_
    nlinarith [mul_pos (by linarith : (0 : ℝ) < (A : ℝ) + i) (by linarith : (0 : ℝ) < (A : ℝ) + i + 1)]
  have hx : ∀ N L, |∑ i ∈ Ico N (N + L), x i| ≤ (d : ℝ) ^ 3 / 8 := by
    intro N L
    have h := abs_sum_Ico_residuePotential_le hd (A + N + 1) L
    rw [sum_Ico_eq_sum_range] at h ⊢
    simp only [x, show N + L - N = L by omega, show A + N + 1 + L - (A + N + 1) = L by omega] at h ⊢
    convert h using 3 with i
    ring_nf
  have habel := abs_sum_Ico_mul_antitone_le (by positivity) hg0 hanti hx 0 k
  have hre : ∑ M ∈ Ico A (A + k), residuePotential d (M + 1) * (pw M - pw (M + 1)) =
      ∑ i ∈ Ico 0 k, g i * x i := by
    rw [sum_Ico_eq_sum_range, sum_Ico_eq_sum_range]
    simp only [g, x, show A + k - A = k by omega, Nat.sub_zero, zero_add]
    exact sum_congr rfl fun i _ => by ring
  rw [hre]
  simpa [g] using habel

/-- One step of the cross-scale remainder at second order: for `1 ≤ A`,
`|Σ_{A ≤ M < H} r_d(M) w(M) + 1[A < H] Φ_d(A)/A²|
  ≤ 1[A < H] (d²/8) w(H-1) + (d³/8)(w(A) - w(A+1)) + (d²/8)/A³`. -/
theorem abs_sum_Ico_centeredResidue_mul_pw_add_le {d A : ℕ} (hd : 0 < d) (hA : 1 ≤ A) (H : ℕ) :
    |∑ M ∈ Ico A H, centeredResidue d M * pw M +
        (if A < H then residuePotential d A / (A : ℝ) ^ 2 else 0)| ≤
      (if A < H then (d : ℝ) ^ 2 / 8 * pw (H - 1) else 0) +
        (d : ℝ) ^ 3 / 8 * (pw A - pw (A + 1)) + (d : ℝ) ^ 2 / 8 / (A : ℝ) ^ 3 := by
  have hAR : (1 : ℝ) ≤ A := by exact_mod_cast hA
  have hΔ := pw_sub_pw_succ_nonneg hA
  split_ifs with hAH
  · obtain ⟨k, rfl⟩ : ∃ k, H = A + k + 1 := ⟨H - A - 1, by omega⟩
    rw [sum_Ico_centeredResidue_mul_pw_eq hd A k, show A + k + 1 - 1 = A + k by omega]
    have hpw : |pw A - 1 / (A : ℝ) ^ 2| ≤ 1 / (A : ℝ) ^ 3 := by
      unfold pw
      rw [show 1 / ((A : ℝ) * ((A : ℝ) + 1)) - 1 / (A : ℝ) ^ 2 =
          -(1 / ((A : ℝ) ^ 2 * ((A : ℝ) + 1))) by field_simp; ring, abs_neg,
        abs_of_nonneg (by positivity)]
      exact one_div_le_one_div_of_le (by positivity) (by nlinarith)
    have h1 := abs_residuePotential_le hd (A + k + 1)
    have h2 := abs_residuePotential_le hd A
    have h3 := abs_sum_Ico_residuePotential_mul_pw_sub_le hd hA k
    set R := ∑ M ∈ Ico A (A + k), residuePotential d (M + 1) * (pw M - pw (M + 1))
    have hsplit : residuePotential d (A + k + 1) * pw (A + k) - residuePotential d A * pw A + R +
        residuePotential d A / (A : ℝ) ^ 2 = residuePotential d (A + k + 1) * pw (A + k) -
          residuePotential d A * (pw A - 1 / (A : ℝ) ^ 2) + R := by ring
    rw [hsplit]
    calc |residuePotential d (A + k + 1) * pw (A + k) -
          residuePotential d A * (pw A - 1 / (A : ℝ) ^ 2) + R|
        ≤ |residuePotential d (A + k + 1)| * pw (A + k) +
            |residuePotential d A| * |pw A - 1 / (A : ℝ) ^ 2| + |R| := by
          refine (abs_add_le _ _).trans (add_le_add ((abs_sub _ _).trans ?_) le_rfl)
          rw [abs_mul, abs_mul, abs_of_nonneg (pw_nonneg _)]
      _ ≤ (d : ℝ) ^ 2 / 8 * pw (A + k) + (d : ℝ) ^ 2 / 8 * (1 / (A : ℝ) ^ 3) +
            (d : ℝ) ^ 3 / 8 * (pw A - pw (A + 1)) := by
          gcongr
          exact (pw_nonneg _)
      _ = _ := by ring
  · rw [Ico_eq_empty_of_le (not_lt.mp hAH), sum_empty, zero_add, abs_zero, zero_add]
    positivity

/-! ## §3. The Bernoulli kernel -/

theorem summable_residuePotential_div_sq {d : ℕ} (hd : 0 < d) (n : ℕ) :
    Summable fun j : ℕ => residuePotential d ((j + 1) * n) / ((j : ℝ) + 1) ^ 2 := by
  have hs : Summable fun j : ℕ => (d : ℝ) ^ 2 / 8 * (1 / ((j + 1 : ℕ) : ℝ) ^ 2) :=
    ((summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr one_lt_two)).mul_left _
  refine Summable.of_norm_bounded hs fun j => ?_
  rw [Real.norm_eq_abs, abs_div, abs_of_pos (by positivity : (0 : ℝ) < ((j : ℝ) + 1) ^ 2)]
  push_cast
  rw [div_eq_mul_one_div]
  exact mul_le_mul_of_nonneg_right (abs_residuePotential_le hd _) (by positivity)

/-- The **Bernoulli kernel** `𝔅(d, n) = Σ_{j ≥ 1} Φ_d(jn)/j²`. -/
def bernoulliKernel (d n : ℕ) : ℝ :=
  ∑' j : ℕ, residuePotential d ((j + 1) * n) / ((j : ℝ) + 1) ^ 2

theorem hasSum_bernoulliKernel {d : ℕ} (hd : 0 < d) (n : ℕ) :
    HasSum (fun j : ℕ => residuePotential d ((j + 1) * n) / ((j : ℝ) + 1) ^ 2)
      (bernoulliKernel d n) :=
  (summable_residuePotential_div_sq hd n).hasSum

/-- The kernel depends on the large modulus only through its residue: `𝔅(d, n) = 𝔅(d, n mod d)`. -/
theorem bernoulliKernel_mod (d n : ℕ) : bernoulliKernel d n = bernoulliKernel d (n % d) := by
  unfold bernoulliKernel residuePotential
  simp only [Nat.mul_mod_mod]

theorem abs_bernoulliKernel_le {d : ℕ} (hd : 0 < d) (n : ℕ) :
    |bernoulliKernel d n| ≤ (d : ℝ) ^ 2 / 8 * (Real.pi ^ 2 / 6) := by
  have hz : HasSum (fun j : ℕ => 1 / ((j : ℝ) + 1) ^ 2) (Real.pi ^ 2 / 6) := by
    have := (hasSum_nat_add_iff' 1).mpr hasSum_zeta_two
    simpa using this
  rw [← Real.norm_eq_abs]
  refine (norm_tsum_le_tsum_norm ?_).trans ?_
  · exact (summable_residuePotential_div_sq hd n).norm
  rw [← (hz.mul_left ((d : ℝ) ^ 2 / 8)).tsum_eq]
  refine Summable.tsum_le_tsum (fun j => ?_) (summable_residuePotential_div_sq hd n).norm
    (hz.mul_left _).summable
  rw [Real.norm_eq_abs, abs_div, abs_of_pos (by positivity : (0 : ℝ) < ((j : ℝ) + 1) ^ 2),
    div_eq_mul_one_div]
  exact mul_le_mul_of_nonneg_right (abs_residuePotential_le hd _) (by positivity)

/-- The truncated sums `Σ_{1 ≤ j ≤ H, jn < H} Φ_d(jn)/(jn)²` converge to `𝔅(d, n)/n²`. -/
theorem tendsto_sum_Icc_residuePotential_div_sq {d n : ℕ} (hd : 0 < d) (hn : 1 ≤ n) :
    Tendsto (fun H : ℕ => ∑ j ∈ Icc 1 H,
      (if j * n < H then residuePotential d (j * n) / ((j * n : ℕ) : ℝ) ^ 2 else 0)) atTop
      (𝓝 (bernoulliKernel d n / (n : ℝ) ^ 2)) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  set f : ℕ → ℝ := fun j => residuePotential d (j * n) / ((j * n : ℕ) : ℝ) ^ 2
  have hf : HasSum (fun i => f (i + 1)) (bernoulliKernel d n / (n : ℝ) ^ 2) := by
    refine ((hasSum_bernoulliKernel hd n).div_const ((n : ℝ) ^ 2)).congr_fun fun i => ?_
    simp only [f]
    push_cast
    rw [mul_pow, div_div]
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
  simp only [f] at heq hf
  simp_rw [heq]
  exact hf.tendsto_sum_nat.comp hdiv

/-! ## §4. The second-order law -/

theorem tendsto_mul_pw_pred : Tendsto (fun H : ℕ => (H : ℝ) * pw (H - 1)) atTop (𝓝 0) := by
  refine squeeze_zero' (Eventually.of_forall fun H => by have := pw_nonneg (H - 1); positivity)
    (eventually_atTop.mpr ⟨2, fun H hH => ?_⟩) (tendsto_const_div_atTop_nhds_zero_nat 2)
  have hH1 : ((H - 1 : ℕ) : ℝ) = (H : ℝ) - 1 := by rw [Nat.cast_sub (by omega)]; push_cast; ring
  have hHR : (2 : ℝ) ≤ H := by exact_mod_cast hH
  rw [pw, hH1, show (H : ℝ) - 1 + 1 = H by ring, mul_one_div,
    div_le_div_iff₀ (by nlinarith) (by linarith)]
  nlinarith

/-- The per-pair estimate: the `j`-sum of second-order remainders of one large modulus `n` against
one small modulus `d`. -/
theorem abs_sum_Icc_step_add_le {d n : ℕ} (hd : 0 < d) (hn : 1 ≤ n) (H : ℕ) :
    |∑ j ∈ Icc 1 H, (∑ M ∈ Ico (j * n) H, centeredResidue d M * pw M +
        (if j * n < H then residuePotential d (j * n) / ((j * n : ℕ) : ℝ) ^ 2 else 0))| ≤
      (d : ℝ) ^ 2 / 8 * ((H : ℝ) * pw (H - 1)) +
        ((d : ℝ) ^ 3 / 2 + (d : ℝ) ^ 2 / 4) / (n : ℝ) ^ 3 := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hterm := fun j (hj : j ∈ Icc 1 H) =>
    abs_sum_Ico_centeredResidue_mul_pw_add_le hd
      (Nat.one_le_iff_ne_zero.mpr (by have := (mem_Icc.mp hj).1; positivity) : 1 ≤ j * n) H
  have hcube : ∑ j ∈ Icc 1 H, (d : ℝ) ^ 2 / 8 / ((j * n : ℕ) : ℝ) ^ 3 ≤
      (d : ℝ) ^ 2 / 8 * (2 / (n : ℝ) ^ 3) := by
    rw [show ∑ j ∈ Icc 1 H, (d : ℝ) ^ 2 / 8 / ((j * n : ℕ) : ℝ) ^ 3 =
      (d : ℝ) ^ 2 / 8 * ∑ j ∈ Icc 1 H, 1 / ((j * n : ℕ) : ℝ) ^ 3 by
        rw [mul_sum]; exact sum_congr rfl fun j _ => by ring]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    calc ∑ j ∈ Icc 1 H, 1 / ((j * n : ℕ) : ℝ) ^ 3
        ≤ ∑ j ∈ Icc 1 H, 1 / (n : ℝ) ^ 3 * (1 / (j : ℝ) ^ 2) := by
          refine sum_le_sum fun j hj => ?_
          have hjR : (1 : ℝ) ≤ j := by exact_mod_cast (mem_Icc.mp hj).1
          push_cast
          rw [div_mul_div_comm, one_mul]
          refine one_div_le_one_div_of_le (by positivity) ?_
          rw [mul_pow]
          have : (j : ℝ) ^ 2 * 1 ≤ (j : ℝ) ^ 2 * j := mul_le_mul_of_nonneg_left hjR (by positivity)
          nlinarith [mul_le_mul_of_nonneg_left this (by positivity : (0 : ℝ) ≤ (n : ℝ) ^ 3)]
      _ = 1 / (n : ℝ) ^ 3 * ∑ j ∈ Icc 1 H, 1 / (j : ℝ) ^ 2 := by rw [mul_sum]
      _ ≤ 1 / (n : ℝ) ^ 3 * 2 := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          rcases Nat.eq_zero_or_pos H with h0 | hH
          · subst h0; simp
          · have := sum_Icc_one_div_sq_le hH
            have : 0 ≤ 1 / (H : ℝ) := by positivity
            linarith
      _ = 2 / (n : ℝ) ^ 3 := by ring
  have hite : ∑ j ∈ Icc 1 H, (if j * n < H then (d : ℝ) ^ 2 / 8 * pw (H - 1) else 0) ≤
      (d : ℝ) ^ 2 / 8 * ((H : ℝ) * pw (H - 1)) := by
    calc ∑ j ∈ Icc 1 H, (if j * n < H then (d : ℝ) ^ 2 / 8 * pw (H - 1) else 0)
        ≤ ∑ _j ∈ Icc 1 H, (d : ℝ) ^ 2 / 8 * pw (H - 1) := sum_le_sum fun j _ => by
          split_ifs
          · exact le_rfl
          · have := pw_nonneg (H - 1); positivity
      _ = _ := by rw [sum_const, Nat.card_Icc]; simp; ring
  have hsteps := sum_Icc_pw_sub_pw_succ_mul_le (H := H) hn
  calc |∑ j ∈ Icc 1 H, (∑ M ∈ Ico (j * n) H, centeredResidue d M * pw M +
        (if j * n < H then residuePotential d (j * n) / ((j * n : ℕ) : ℝ) ^ 2 else 0))|
      ≤ ∑ j ∈ Icc 1 H, ((if j * n < H then (d : ℝ) ^ 2 / 8 * pw (H - 1) else 0) +
          (d : ℝ) ^ 3 / 8 * (pw (j * n) - pw (j * n + 1)) +
          (d : ℝ) ^ 2 / 8 / ((j * n : ℕ) : ℝ) ^ 3) :=
        (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun j hj => hterm j hj)
    _ = ∑ j ∈ Icc 1 H, (if j * n < H then (d : ℝ) ^ 2 / 8 * pw (H - 1) else 0) +
          (d : ℝ) ^ 3 / 8 * ∑ j ∈ Icc 1 H, (pw (j * n) - pw (j * n + 1)) +
          ∑ j ∈ Icc 1 H, (d : ℝ) ^ 2 / 8 / ((j * n : ℕ) : ℝ) ^ 3 := by
        rw [sum_add_distrib, sum_add_distrib, mul_sum]
    _ ≤ (d : ℝ) ^ 2 / 8 * ((H : ℝ) * pw (H - 1)) + (d : ℝ) ^ 3 / 8 * (4 / (n : ℝ) ^ 3) +
          (d : ℝ) ^ 2 / 8 * (2 / (n : ℝ) ^ 3) := by
        gcongr
    _ = _ := by ring

/-- **The second-order cross-scale law.** For all rows `c, c'`,
`|B(c, c') + m(c) R(c') + β(c) H(c') - Σ_{n, d} c'(n) c(d) 𝔅(d, n)/(d n²)|
  ≤ ¾ (Σ_d |c(d)| d²)(Σ_n |c'(n)|/n³)`. -/
theorem abs_rowBilinear_add_mean_add_beta_sub_bernoulli_le (N : ℕ) (c c' : ℕ → ℝ) :
    |rowBilinear N c c' + rowMean N c * vonMangoldtReadout N c' +
        rowBeta N c * finiteHarmonicSum N c' -
        ∑ n ∈ Icc 1 N, ∑ d ∈ Icc 1 N, c' n * (c d / d) * (bernoulliKernel d n / (n : ℝ) ^ 2)| ≤
      3 / 4 * (∑ d ∈ Icc 1 N, |c d| * (d : ℝ) ^ 2) * ∑ n ∈ Icc 1 N, |c' n| / (n : ℝ) ^ 3 := by
  classical
  set ite' : ℕ → ℕ → ℕ → ℕ → ℝ := fun d n H j =>
    if j * n < H then residuePotential d (j * n) / ((j * n : ℕ) : ℝ) ^ 2 else 0
  set step : ℕ → ℝ := fun H => ∑ n ∈ Icc 1 N, c' n *
    ∑ M ∈ range H, rowFluct N c M * ((M / n : ℕ) : ℝ) / (pronicSeq M : ℝ)
  set main : ℕ → ℝ := fun H => ∑ n ∈ Icc 1 N, ∑ d ∈ Icc 1 N, c' n * (c d / d) *
    ∑ j ∈ Icc 1 H, ite' d n H j
  set δ : ℕ → ℝ := fun H => (∑ n ∈ Icc 1 N, ∑ d ∈ Icc 1 N, |c' n| * (|c d| / d) *
    ((d : ℝ) ^ 2 / 8)) * ((H : ℝ) * pw (H - 1))
  set C : ℝ := ∑ n ∈ Icc 1 N, ∑ d ∈ Icc 1 N, |c' n| * (|c d| / d) *
    (((d : ℝ) ^ 3 / 2 + (d : ℝ) ^ 2 / 4) / (n : ℝ) ^ 3)
  -- the step sums in residue form
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
            ((d : ℝ) ^ 2 / 8 * ((H : ℝ) * pw (H - 1)) +
              ((d : ℝ) ^ 3 / 2 + (d : ℝ) ^ 2 / 4) / (n : ℝ) ^ 3) := by
          refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun n hn => ?_)
          refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun d hd => ?_)
          have hd0 : 0 < d := (mem_Icc.mp hd).1
          have hdR : (0 : ℝ) < d := by exact_mod_cast hd0
          rw [abs_mul, abs_mul, abs_div, abs_of_pos hdR]
          exact mul_le_mul_of_nonneg_left (abs_sum_Icc_step_add_le hd0 (mem_Icc.mp hn).1 H)
            (by positivity)
      _ = C + δ H := by
          simp only [C, δ, mul_add, sum_add_distrib, sum_mul]
          rw [add_comm]
          congr 1
          exact sum_congr rfl fun n _ => sum_congr rfl fun d _ => by ring
  have hstep_lim := tendsto_rowStepSum N c c'
  have hmain_lim : Tendsto main atTop (𝓝 (∑ n ∈ Icc 1 N, ∑ d ∈ Icc 1 N,
      c' n * (c d / d) * (bernoulliKernel d n / (n : ℝ) ^ 2))) := by
    simp only [main, ite']
    refine tendsto_finsetSum _ fun n hn => tendsto_finsetSum _ fun d hd => ?_
    exact (tendsto_sum_Icc_residuePotential_div_sq (mem_Icc.mp hd).1 (mem_Icc.mp hn).1).const_mul _
  have hδ : Tendsto δ atTop (𝓝 0) := by
    have := tendsto_mul_pw_pred.const_mul
      (∑ n ∈ Icc 1 N, ∑ d ∈ Icc 1 N, |c' n| * (|c d| / d) * ((d : ℝ) ^ 2 / 8))
    rw [mul_zero] at this
    exact this
  have hle : |rowBilinear N c c' + rowMean N c * vonMangoldtReadout N c' +
        rowBeta N c * finiteHarmonicSum N c' -
        ∑ n ∈ Icc 1 N, ∑ d ∈ Icc 1 N, c' n * (c d / d) * (bernoulliKernel d n / (n : ℝ) ^ 2)| ≤
      C := by
    have := le_of_tendsto_of_tendsto (hstep_lim.sub hmain_lim).abs (tendsto_const_nhds.add hδ)
      (Eventually.of_forall hbound)
    simpa using this
  refine hle.trans ?_
  calc C = ∑ n ∈ Icc 1 N, ∑ d ∈ Icc 1 N, |c' n| / (n : ℝ) ^ 3 *
        (|c d| * ((d : ℝ) ^ 2 / 2 + (d : ℝ) / 4)) :=
        sum_congr rfl fun n hn => sum_congr rfl fun d hd => by
          have hdR : (0 : ℝ) < d := by exact_mod_cast (mem_Icc.mp hd).1
          have hnR : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
          field_simp
    _ ≤ ∑ n ∈ Icc 1 N, ∑ d ∈ Icc 1 N, |c' n| / (n : ℝ) ^ 3 * (3 / 4 * (|c d| * (d : ℝ) ^ 2)) :=
        sum_le_sum fun n _ => sum_le_sum fun d hd => by
          have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast (mem_Icc.mp hd).1
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          have := abs_nonneg (c d)
          nlinarith [mul_nonneg this (by nlinarith : (0 : ℝ) ≤ (d : ℝ) ^ 2 - d)]
    _ = _ := by
        rw [mul_assoc, sum_mul_sum, sum_comm, mul_sum]
        refine sum_congr rfl fun d _ => ?_
        rw [mul_sum]
        exact sum_congr rfl fun n _ => by ring

/-! ## §5. Two primes -/

/-- **The second-order law for two primes.** With `D_p = (p-1)/2 - log p` and
`β_p = β(δ_p) = Σ_{M ≥ 1} F_{δ_p}(M)/(M+1)`,
`|𝒢^{ec}(p, q) - D_p log q + p β_p - 𝔅(p, q)/q| ≤ ¾ p³/q²`. The kernel term `𝔅(p, q mod p)/q` is a
function of the residue of `q` of size at most `(π²/48) p²/q`. -/
theorem abs_pmRamanujanEnergyCenteredGram_sub_second_order_le {N p q : ℕ} (hp : p.Prime)
    (hq : q.Prime) (hpN : p ≤ N) (hqN : q ≤ N) :
    |pmRamanujanEnergyCenteredGram p q - (((p : ℝ) - 1) / 2 - Real.log p) * Real.log q +
        p * rowBeta N (unitRow p) - bernoulliKernel p q / q| ≤
      3 / 4 * (p : ℝ) ^ 3 / (q : ℝ) ^ 2 := by
  have hpI : p ∈ Icc 1 N := mem_Icc.mpr ⟨hp.one_lt.le, hpN⟩
  have hqI : q ∈ Icc 1 N := mem_Icc.mpr ⟨hq.one_lt.le, hqN⟩
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq.pos
  have h := abs_rowBilinear_add_mean_add_beta_sub_bernoulli_le N (unitRow p) (unitRow q)
  have hK : ∑ n ∈ Icc 1 N, ∑ d ∈ Icc 1 N, unitRow q n * (unitRow p d / d) *
      (bernoulliKernel d n / (n : ℝ) ^ 2) = bernoulliKernel p q / (p * (q : ℝ) ^ 2) := by
    rw [sum_eq_single q (fun n _ hn => by simp [unitRow, hn]) (fun h => absurd hqI h),
      sum_eq_single p (fun d _ hd => by simp [unitRow, hd]) (fun h => absurd hpI h)]
    simp only [unitRow, if_true]
    field_simp
  have hL : ∑ d ∈ Icc 1 N, |unitRow p d| * (d : ℝ) ^ 2 = (p : ℝ) ^ 2 := by
    rw [sum_eq_single p (fun d _ hd => by simp [unitRow, hd]) (fun h => absurd hpI h)]
    simp [unitRow]
  have hR : ∑ n ∈ Icc 1 N, |unitRow q n| / (n : ℝ) ^ 3 = 1 / (q : ℝ) ^ 3 := by
    rw [sum_eq_single q (fun n _ hn => by simp [unitRow, hn]) (fun h => absurd hqI h)]
    simp [unitRow]
  rw [hK, hL, hR, rowMean_unitRow hpI, vonMangoldtReadout_unitRow hqI,
    finiteHarmonicSum_unitRow hqI] at h
  have hG := mul_rowBilinear_unitRow_prime hp hq hpN hqN
  have hpq : (0 : ℝ) < p * q := mul_pos hpR hqR
  have hmul := mul_le_mul_of_nonneg_left h hpq.le
  rw [← abs_of_pos hpq, ← abs_mul, abs_of_pos hpq] at hmul
  have hid : (p : ℝ) * q * (rowBilinear N (unitRow p) (unitRow q) +
        (Real.log p / p - ((p : ℝ) - 1) / (2 * p)) * (Real.log q / q) +
        rowBeta N (unitRow p) * (1 / q) - bernoulliKernel p q / (p * (q : ℝ) ^ 2)) =
      pmRamanujanEnergyCenteredGram p q - (((p : ℝ) - 1) / 2 - Real.log p) * Real.log q +
        p * rowBeta N (unitRow p) - bernoulliKernel p q / q := by
    rw [← hG]
    field_simp
    ring
  rw [hid] at hmul
  refine hmul.trans (le_of_eq ?_)
  field_simp

end

end GaloisForLFunctions.BezoutValuationIncidence
