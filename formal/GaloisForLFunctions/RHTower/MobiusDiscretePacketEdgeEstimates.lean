import GaloisForLFunctions.RHTower.MobiusDiscretePacketHorizon
import GaloisForLFunctions.RHTower.MobiusCubicSourceMertensEnergy
import GaloisForLFunctions.HTGeometry.ShiftLatticeThetaSeries

/-!
# Edge estimates for the cubic Möbius packets

Tools for the two source edges of the packets `c_k = Σ_n μ(n) g_k(n)`,
`g_k(x) = x² (x+1)^{-(5+δ)} ((x-1)/(x+1))^k`, uniform in `0 ≤ δ ≤ 1`:

* summation by parts on `(a, b]` against `M(n) = Σ_{m ≤ n} μ(m)`, with the bound `2 B g(b)` for a
  nondecreasing nonnegative weight when `|M| ≤ B` on `[a, b]`;
* the kernel is nondecreasing in `n` while `2n ≤ k` (its logarithmic increment is at least
  `(2k - 4n)/(n(n+1))`), and `|g_k(x+1) - g_k(x)| ≤ 8 x^{-4-δ}` for `x ≥ k`;
* the low-edge absolute sum telescopes: with `F(y) = y^{-1-δ} e^{-2k/y}/(2k)` one has
  `m^{-3-δ} e^{-2k/m} ≤ 2(F(m+1) - F(m))` for `2 ≤ m`, `6m ≤ k`, hence
  `Σ_{n ≤ M} (n+1)^{-3-δ} e^{-2k/(n+1)} ≤ (M+2)^{-1-δ} e^{-2k/(M+2)}/k`;
* geometric tails `Σ_{k ≥ K} k^p x^k ≤ K^p x^K / (1 - x e^{p/K})`;
* `Σ_k (log k)^p E(k)² / k < ∞` for the Mertens saving `E(x) = exp(-(log x)^{1/3}/108)`,
  by Cauchy condensation.
-/

open Finset Filter Topology
open scoped ArithmeticFunction.Moebius

noncomputable section

namespace RHTower.DiscretePacket

open CubicGamma

/-! ### Summation by parts against the Mertens function -/

theorem sum_range_succ_moebius (n : ℕ) :
    ∑ j ∈ range (n + 1), ((μ j : ℤ) : ℝ) = abelMertens n := by
  rw [abelMertens_eq_mertensM]
  rfl

theorem abelMertens_zero : abelMertens 0 = 0 := by
  simp [abelMertens, prefixSum]

/-- Summation by parts on `(a, b]`. -/
theorem sum_Ioc_moebius_mul_eq (g : ℕ → ℝ) {a b : ℕ} (hab : a < b) :
    ∑ n ∈ Ioc a b, ((μ n : ℤ) : ℝ) * g n =
      g b * abelMertens b - g (a + 1) * abelMertens a -
        ∑ n ∈ Ioc a (b - 1), (g (n + 1) - g n) * abelMertens n := by
  have h := Finset.sum_Ioc_by_parts g (fun n => ((μ n : ℤ) : ℝ)) hab
  simp only [smul_eq_mul, sum_range_succ_moebius] at h
  rw [show ∑ n ∈ Ioc a b, ((μ n : ℤ) : ℝ) * g n = ∑ n ∈ Ioc a b, g n * ((μ n : ℤ) : ℝ) from
    sum_congr rfl fun n _ => mul_comm _ _, h]

theorem sum_Ioc_telescope (g : ℕ → ℝ) {a c : ℕ} (hac : a ≤ c) :
    ∑ n ∈ Ioc a c, (g (n + 1) - g n) = g (c + 1) - g (a + 1) := by
  induction c, hac using Nat.le_induction with
  | base => simp
  | succ c hc ih =>
    rw [Finset.sum_Ioc_succ_top (by omega), ih]
    ring

/-- **Abel bound for a nondecreasing weight.**  If `|M(n)| ≤ B` on `[a, b]` and `g ≥ 0` is
nondecreasing on `[a+1, b]`, then `|Σ_{a<n≤b} μ(n) g(n)| ≤ 2 B g(b)`. -/
theorem abs_sum_Ioc_moebius_mul_le_of_monotone (g : ℕ → ℝ) {a b : ℕ} (hab : a < b) {B : ℝ}
    (hM : ∀ n, a ≤ n → n ≤ b → |abelMertens n| ≤ B)
    (hg0 : 0 ≤ g (a + 1)) (hmono : ∀ n, a + 1 ≤ n → n < b → g n ≤ g (n + 1)) :
    |∑ n ∈ Ioc a b, ((μ n : ℤ) : ℝ) * g n| ≤ 2 * B * g b := by
  have hchain : ∀ c, a + 1 ≤ c → c ≤ b → g (a + 1) ≤ g c := by
    intro c hc hcb
    induction c, hc using Nat.le_induction with
    | base => exact le_rfl
    | succ c hc ih => exact (ih (by omega)).trans (hmono c hc (by omega))
  have hgb := hchain b (by omega) le_rfl
  rw [sum_Ioc_moebius_mul_eq g hab]
  have hvar : |∑ n ∈ Ioc a (b - 1), (g (n + 1) - g n) * abelMertens n| ≤
      B * (g b - g (a + 1)) := by
    calc _ ≤ ∑ n ∈ Ioc a (b - 1), |(g (n + 1) - g n) * abelMertens n| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ n ∈ Ioc a (b - 1), (g (n + 1) - g n) * B := by
        apply sum_le_sum
        intro n hn
        have hn' := mem_Ioc.mp hn
        have hd : 0 ≤ g (n + 1) - g n := by linarith [hmono n (by omega) (by omega)]
        rw [abs_mul, abs_of_nonneg hd]
        exact mul_le_mul_of_nonneg_left (hM n (by omega) (by omega)) hd
      _ = B * (g b - g (a + 1)) := by
        rw [← Finset.sum_mul, sum_Ioc_telescope g (show a ≤ b - 1 by omega),
          Nat.sub_add_cancel (by omega : 1 ≤ b)]
        ring
  have h1 : |g b * abelMertens b| ≤ g b * B := by
    rw [abs_mul, abs_of_nonneg (hg0.trans hgb)]
    exact mul_le_mul_of_nonneg_left (hM b hab.le le_rfl) (hg0.trans hgb)
  have h2 : |g (a + 1) * abelMertens a| ≤ g (a + 1) * B := by
    rw [abs_mul, abs_of_nonneg hg0]
    exact mul_le_mul_of_nonneg_left (hM a le_rfl hab.le) hg0
  have e1 := abs_le.mp h1
  have e2 := abs_le.mp h2
  have e3 := abs_le.mp hvar
  rw [abs_le]
  constructor <;> linarith

/-- **Abel bound by total variation.** -/
theorem abs_sum_Ioc_moebius_mul_le (g : ℕ → ℝ) {a b : ℕ} (hab : a < b) :
    |∑ n ∈ Ioc a b, ((μ n : ℤ) : ℝ) * g n| ≤
      |g b| * |abelMertens b| + |g (a + 1)| * |abelMertens a| +
        ∑ n ∈ Ioc a (b - 1), |g (n + 1) - g n| * |abelMertens n| := by
  rw [sum_Ioc_moebius_mul_eq g hab]
  have hvar : |∑ n ∈ Ioc a (b - 1), (g (n + 1) - g n) * abelMertens n| ≤
      ∑ n ∈ Ioc a (b - 1), |g (n + 1) - g n| * |abelMertens n| := by
    refine (abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
    simp_rw [abs_mul]
  calc _ ≤ |g b * abelMertens b - g (a + 1) * abelMertens a| +
        |∑ n ∈ Ioc a (b - 1), (g (n + 1) - g n) * abelMertens n| := abs_sub _ _
    _ ≤ |g b * abelMertens b| + |g (a + 1) * abelMertens a| +
        |∑ n ∈ Ioc a (b - 1), (g (n + 1) - g n) * abelMertens n| := by
        gcongr
        exact abs_sub _ _
    _ ≤ _ := by
        rw [abs_mul, abs_mul]
        linarith

/-! ### Mertens bounds on windows -/

/-- `|M(n)| ≤ C n E(n)` for every `n`. -/
theorem exists_abs_abelMertens_le_all :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, |abelMertens n| ≤ C * n * mertensSaving n := by
  obtain ⟨C, hC, h⟩ := exists_abs_abelMertens_le
  refine ⟨C, hC, fun n => ?_⟩
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [abelMertens_zero]
  · exact h n hn

/-- On a window `L/4 ≤ n ≤ L`, `|M(n)| ≤ C L E(L)`. -/
theorem exists_abs_abelMertens_window :
    ∃ C : ℝ, 0 < C ∧ ∀ n L : ℕ, 1 ≤ n → n ≤ L → L ≤ 4 * n →
      |abelMertens n| ≤ C * L * mertensSaving L := by
  obtain ⟨C, hC, h⟩ := exists_abs_abelMertens_le_all
  obtain ⟨K, hK, hslow⟩ := mertensSaving_slow (η := 1) one_pos
  refine ⟨4 * C * K, by positivity, fun n L hn hnL hL => ?_⟩
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnL' : (n : ℝ) ≤ L := by exact_mod_cast hnL
  have hL' : (L : ℝ) ≤ 4 * n := by exact_mod_cast hL
  have hE := hslow n L hn1 hnL'
  rw [Real.rpow_one] at hE
  have hratio : (L : ℝ) / n ≤ 4 := by
    rw [div_le_iff₀ (by linarith)]
    linarith
  have hEL := mertensSaving_pos (L : ℝ)
  have hEn0 := mertensSaving_pos (n : ℝ)
  have hEn : mertensSaving n ≤ 4 * K * mertensSaving L := by
    calc mertensSaving n ≤ K * mertensSaving L * ((L : ℝ) / n) := hE
      _ ≤ K * mertensSaving L * 4 := by gcongr
      _ = _ := by ring
  calc |abelMertens n| ≤ C * n * mertensSaving n := h n
    _ ≤ C * L * (4 * K * mertensSaving L) := by
        gcongr
    _ = _ := by ring

/-! ### Monotonicity of the kernel below `k/2` -/

theorem packetKernel_eq_exp {δ : ℝ} (k : ℕ) {x : ℝ} (hx : 1 < x) :
    packetKernel δ k x = Real.exp (2 * Real.log x - (5 + δ) * Real.log (x + 1) +
      k * Real.log ((x - 1) / (x + 1))) := by
  have hx0 : 0 < x := by linarith
  have hq : 0 < (x - 1) / (x + 1) := div_pos (by linarith) (by linarith)
  have h1 : Real.exp (2 * Real.log x) = x ^ 2 := by
    rw [show 2 * Real.log x = Real.log (x ^ 2) by rw [Real.log_pow]; push_cast; ring,
      Real.exp_log (by positivity)]
  have h2 : Real.exp ((5 + δ) * Real.log (x + 1)) = (x + 1) ^ (5 + δ) := by
    rw [Real.rpow_def_of_pos (by linarith), mul_comm]
  have h3 : Real.exp (k * Real.log ((x - 1) / (x + 1))) = ((x - 1) / (x + 1)) ^ k := by
    rw [show (k : ℝ) * Real.log ((x - 1) / (x + 1)) = Real.log (((x - 1) / (x + 1)) ^ k) by
      rw [Real.log_pow], Real.exp_log (pow_pos hq k)]
  unfold packetKernel
  rw [Real.exp_add, Real.exp_sub, h1, h2, h3, Real.rpow_neg (by linarith)]
  ring

/-- The kernel is nondecreasing from `x` to `x+1` whenever `2 ≤ x` and `2x ≤ k`. -/
theorem packetKernel_le_succ {δ : ℝ} (hδ1 : δ ≤ 1) {k : ℕ} {x : ℝ} (hx : 2 ≤ x)
    (hk : 2 * x ≤ k) : packetKernel δ k x ≤ packetKernel δ k (x + 1) := by
  have hx0 : 0 < x := by linarith
  rw [packetKernel_eq_exp k (by linarith), packetKernel_eq_exp k (by linarith)]
  apply Real.exp_le_exp.mpr
  -- the three logarithmic increments
  have hA : 1 / (x + 1) ≤ Real.log (x + 1) - Real.log x := by
    rw [← Real.log_div (by linarith) (by linarith)]
    have h := Real.one_sub_inv_le_log_of_pos (show 0 < (x + 1) / x by positivity)
    have he : 1 - ((x + 1) / x)⁻¹ = 1 / (x + 1) := by field_simp; ring
    linarith
  have hB : Real.log (x + 1 + 1) - Real.log (x + 1) ≤ 1 / (x + 1) := by
    rw [← Real.log_div (by linarith) (by linarith)]
    have h := Real.log_le_sub_one_of_pos (show 0 < (x + 1 + 1) / (x + 1) by positivity)
    have he : (x + 1 + 1) / (x + 1) - 1 = 1 / (x + 1) := by field_simp; ring
    linarith
  have hB0 : 0 ≤ Real.log (x + 1 + 1) - Real.log (x + 1) := by
    have := Real.log_le_log (by linarith : (0 : ℝ) < x + 1) (by linarith : x + 1 ≤ x + 1 + 1)
    linarith
  have hC : 2 / (x * (x + 1)) ≤
      Real.log ((x + 1 - 1) / (x + 1 + 1)) - Real.log ((x - 1) / (x + 1)) := by
    have hq1 : 0 < (x - 1) / (x + 1) := div_pos (by linarith) (by linarith)
    have hq2 : 0 < (x + 1 - 1) / (x + 1 + 1) := div_pos (by linarith) (by linarith)
    rw [← Real.log_div hq2.ne' hq1.ne']
    have h := Real.one_sub_inv_le_log_of_pos (div_pos hq2 hq1)
    have he : 1 - ((x + 1 - 1) / (x + 1 + 1) / ((x - 1) / (x + 1)))⁻¹ = 2 / (x * (x + 1)) := by
      have : x - 1 ≠ 0 := by linarith
      have : x ≠ 0 := hx0.ne'
      have : x + 1 ≠ 0 := by linarith
      have : x + 1 + 1 ≠ 0 := by linarith
      rw [show x + 1 - 1 = x by ring]
      field_simp
      ring
    linarith
  have hk0 : (0 : ℝ) ≤ k := by positivity
  have hkC : 4 * (1 / (x + 1)) ≤ (k : ℝ) * (2 / (x * (x + 1))) := by
    rw [show 4 * (1 / (x + 1)) = 2 * x * (2 / (x * (x + 1))) by field_simp; ring]
    exact mul_le_mul_of_nonneg_right hk (by positivity)
  have h5 : (5 + δ) * (Real.log (x + 1 + 1) - Real.log (x + 1)) ≤ 6 * (1 / (x + 1)) :=
    mul_le_mul (by linarith) hB hB0 (by norm_num)
  have hkC' : (k : ℝ) * (2 / (x * (x + 1))) ≤ (k : ℝ) *
      (Real.log ((x + 1 - 1) / (x + 1 + 1)) - Real.log ((x - 1) / (x + 1))) :=
    mul_le_mul_of_nonneg_left hC hk0
  linarith

theorem packetKernel_nat_le_succ {δ : ℝ} (hδ1 : δ ≤ 1) {k n : ℕ} (hn : 2 ≤ n) (hk : 2 * n ≤ k) :
    packetKernel δ k n ≤ packetKernel δ k (n + 1 : ℕ) := by
  push_cast
  exact packetKernel_le_succ hδ1 (by exact_mod_cast hn) (by exact_mod_cast hk)

/-! ### The kernel increment beyond `k` -/

/-- `a^{-s} - b^{-s} ≤ s (b - a) a^{-s-1}` for `0 < a ≤ b`, `s ≥ 0`. -/
theorem rpow_neg_sub_rpow_neg_le {a b s : ℝ} (ha : 0 < a) (hab : a ≤ b) (hs : 0 ≤ s) :
    a ^ (-s) - b ^ (-s) ≤ s * (b - a) * a ^ (-(s + 1)) := by
  have hb : 0 < b := ha.trans_le hab
  have hlog : 1 - b / a ≤ Real.log (a / b) := by
    have h := Real.one_sub_inv_le_log_of_pos (div_pos ha hb)
    rwa [inv_div] at h
  have hexp : 1 + s * Real.log (a / b) ≤ (a / b) ^ s := by
    rw [Real.rpow_def_of_pos (div_pos ha hb)]
    linarith [Real.add_one_le_exp (Real.log (a / b) * s), mul_comm s (Real.log (a / b))]
  have hbs : b ^ (-s) = a ^ (-s) * (a / b) ^ s := by
    rw [Real.div_rpow ha.le hb.le, Real.rpow_neg ha.le, Real.rpow_neg hb.le]
    have : a ^ s ≠ 0 := (Real.rpow_pos_of_pos ha s).ne'
    field_simp
  have has : a ^ (-(s + 1)) = a ^ (-s) / a := by
    rw [show -(s + 1) = -s - 1 by ring, Real.rpow_sub_one ha.ne']
  rw [hbs, has]
  have hpos : 0 < a ^ (-s) := Real.rpow_pos_of_pos ha _
  have key : 1 - (a / b) ^ s ≤ s * (b - a) / a := by
    have : s * (b - a) / a = s * (b / a - 1) := by field_simp
    rw [this]
    nlinarith
  calc a ^ (-s) - a ^ (-s) * (a / b) ^ s = a ^ (-s) * (1 - (a / b) ^ s) := by ring
    _ ≤ a ^ (-s) * (s * (b - a) / a) := mul_le_mul_of_nonneg_left key hpos.le
    _ = _ := by ring

/-- `s (b - a) b^{-s-1} ≤ a^{-s} - b^{-s}` for `0 < a ≤ b`, `s ≥ 0`. -/
theorem le_rpow_neg_sub_rpow_neg {a b s : ℝ} (ha : 0 < a) (hab : a ≤ b) (hs : 0 ≤ s) :
    s * (b - a) * b ^ (-(s + 1)) ≤ a ^ (-s) - b ^ (-s) := by
  have hb : 0 < b := ha.trans_le hab
  have hlog : 1 - a / b ≤ Real.log (b / a) := by
    have h := Real.one_sub_inv_le_log_of_pos (div_pos hb ha)
    rwa [inv_div] at h
  have hexp : 1 + s * Real.log (b / a) ≤ (b / a) ^ s := by
    rw [Real.rpow_def_of_pos (div_pos hb ha)]
    linarith [Real.add_one_le_exp (Real.log (b / a) * s), mul_comm s (Real.log (b / a))]
  have has : a ^ (-s) = b ^ (-s) * (b / a) ^ s := by
    rw [Real.div_rpow hb.le ha.le, Real.rpow_neg ha.le, Real.rpow_neg hb.le]
    have : b ^ s ≠ 0 := (Real.rpow_pos_of_pos hb s).ne'
    field_simp
  have hbs : b ^ (-(s + 1)) = b ^ (-s) / b := by
    rw [show -(s + 1) = -s - 1 by ring, Real.rpow_sub_one hb.ne']
  rw [has, hbs]
  have hpos : 0 < b ^ (-s) := Real.rpow_pos_of_pos hb _
  have key : s * (b - a) / b ≤ (b / a) ^ s - 1 := by
    have : s * (b - a) / b = s * (1 - a / b) := by field_simp
    rw [this]
    nlinarith
  calc s * (b - a) * (b ^ (-s) / b) = b ^ (-s) * (s * (b - a) / b) := by ring
    _ ≤ b ^ (-s) * ((b / a) ^ s - 1) := mul_le_mul_of_nonneg_left key hpos.le
    _ = _ := by ring

/-- `z^k - y^k ≤ k (z - y)` for `0 ≤ y ≤ z ≤ 1`. -/
theorem pow_sub_pow_le_mul {y z : ℝ} (hy : 0 ≤ y) (hyz : y ≤ z) (hz : z ≤ 1) (k : ℕ) :
    z ^ k - y ^ k ≤ k * (z - y) := by
  rw [← geom_sum₂_mul]
  apply mul_le_mul_of_nonneg_right _ (by linarith)
  calc ∑ i ∈ range k, z ^ i * y ^ (k - 1 - i) ≤ ∑ _i ∈ range k, (1 : ℝ) := by
        apply sum_le_sum
        intro i _
        have h1 : z ^ i ≤ 1 := pow_le_one₀ (hy.trans hyz) hz
        have h2 : y ^ (k - 1 - i) ≤ 1 := pow_le_one₀ hy (hyz.trans hz)
        calc z ^ i * y ^ (k - 1 - i) ≤ 1 * 1 :=
              mul_le_mul h1 h2 (pow_nonneg hy _) zero_le_one
          _ = 1 := one_mul 1
    _ = k := by simp

theorem rpow_neg_le_of_le {x y s : ℝ} (hx : 0 < x) (hxy : x ≤ y) (hs : 0 ≤ s) :
    y ^ (-s) ≤ x ^ (-s) :=
  Real.rpow_le_rpow_of_nonpos hx hxy (by linarith)

/-- `|g_k(x+1) - g_k(x)| ≤ 8 x^{-4-δ}` for `x ≥ 1`, `k ≤ x`, `0 ≤ δ ≤ 1`. -/
theorem abs_packetKernel_succ_sub_le {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) {k : ℕ} {x : ℝ}
    (hx : 1 ≤ x) (hk : (k : ℝ) ≤ x) :
    |packetKernel δ k (x + 1) - packetKernel δ k x| ≤ 8 * x ^ (-(4 + δ)) := by
  have hx0 : 0 < x := by linarith
  set s : ℝ := 5 + δ with hs
  set Q : ℝ → ℝ := fun y => (y - 1) / (y + 1) with hQ
  set h : ℝ → ℝ := fun y => y ^ 2 * (y + 1) ^ (-s) with hh
  have hg : ∀ y, packetKernel δ k y = h y * Q y ^ k := fun y => rfl
  have hQ0 : 0 ≤ Q x := node_nonneg' hx
  have hQ1 : Q (x + 1) ≤ 1 := by
    simp only [hQ]
    rw [div_le_one (by linarith)]
    linarith
  have hQmono : Q x ≤ Q (x + 1) := by
    simp only [hQ]
    rw [div_le_div_iff₀ (by linarith) (by linarith)]
    nlinarith
  have hQdiff : Q (x + 1) - Q x = 2 / ((x + 1) * (x + 2)) := by
    simp only [hQ]
    field_simp
    ring
  -- powers of `x` and `x+1`
  have hx1 : 0 < x + 1 := by linarith
  have hsplit (y : ℝ) (hy : 0 < y) (a : ℝ) (n : ℕ) : y ^ (-(a + n)) = y ^ (-a) / y ^ n := by
    rw [show -(a + n) = -a + -((n : ℕ) : ℝ) by ring, Real.rpow_add hy, Real.rpow_neg hy.le
      ((n : ℕ) : ℝ), Real.rpow_natCast, div_eq_mul_inv]
  have h4 : (x + 1) ^ (-(4 + δ)) ≤ x ^ (-(4 + δ)) := rpow_neg_le_of_le hx0 (by linarith) (by linarith)
  -- the second factor
  have hhx : h x ≤ x ^ (-(3 + δ)) := by
    simp only [hh, hs]
    have e : (x + 1) ^ (-(5 + δ)) = (x + 1) ^ (-(3 + δ)) / (x + 1) ^ 2 := by
      rw [show (5 : ℝ) + δ = (3 + δ) + ((2 : ℕ) : ℝ) by push_cast; ring, hsplit _ hx1]
    rw [e]
    have h3 : (x + 1) ^ (-(3 + δ)) ≤ x ^ (-(3 + δ)) :=
      rpow_neg_le_of_le hx0 (by linarith) (by linarith)
    have hp : 0 ≤ (x + 1) ^ (-(3 + δ)) := (Real.rpow_pos_of_pos hx1 _).le
    calc x ^ 2 * ((x + 1) ^ (-(3 + δ)) / (x + 1) ^ 2)
        = (x + 1) ^ (-(3 + δ)) * (x ^ 2 / (x + 1) ^ 2) := by ring
      _ ≤ (x + 1) ^ (-(3 + δ)) * 1 := by
          gcongr
          rw [div_le_one (by positivity)]
          nlinarith
      _ ≤ _ := by rw [mul_one]; exact h3
  have hh0 : 0 ≤ h x := by simp only [hh]; positivity
  have hsecond : 0 ≤ h x * (Q (x + 1) ^ k - Q x ^ k) ∧
      h x * (Q (x + 1) ^ k - Q x ^ k) ≤ 2 * x ^ (-(4 + δ)) := by
    have hd0 : 0 ≤ Q (x + 1) ^ k - Q x ^ k := by
      linarith [pow_le_pow_left₀ hQ0 hQmono k]
    refine ⟨mul_nonneg hh0 hd0, ?_⟩
    have hd := pow_sub_pow_le_mul hQ0 hQmono hQ1 k
    rw [hQdiff] at hd
    have hkx : (k : ℝ) * (2 / ((x + 1) * (x + 2))) ≤ 2 / x := by
      rw [mul_div_assoc', div_le_div_iff₀ (by positivity) hx0]
      nlinarith
    have hx4 : x ^ (-(3 + δ)) * (2 / x) = 2 * x ^ (-(4 + δ)) := by
      rw [show (4 : ℝ) + δ = (3 + δ) + ((1 : ℕ) : ℝ) by push_cast; ring, hsplit _ hx0]
      ring
    calc h x * (Q (x + 1) ^ k - Q x ^ k) ≤ x ^ (-(3 + δ)) * (k * (2 / ((x + 1) * (x + 2)))) :=
          mul_le_mul hhx hd hd0 (Real.rpow_pos_of_pos hx0 _).le
      _ ≤ x ^ (-(3 + δ)) * (2 / x) :=
          mul_le_mul_of_nonneg_left hkx (Real.rpow_pos_of_pos hx0 _).le
      _ = _ := hx4
  -- the first factor
  have hfirst : |h (x + 1) - h x| ≤ 6 * x ^ (-(4 + δ)) := by
    rw [abs_le]
    constructor
    · -- lower bound
      have hdiff := rpow_neg_sub_rpow_neg_le hx1 (show x + 1 ≤ x + 1 + 1 by linarith)
        (show 0 ≤ s by rw [hs]; linarith)
      have hs6 : s + 1 = (4 + δ) + ((2 : ℕ) : ℝ) := by rw [hs]; push_cast; ring
      have hlow : h x - h (x + 1) ≤ x ^ 2 * ((x + 1) ^ (-s) - (x + 1 + 1) ^ (-s)) := by
        simp only [hh]
        have : x ^ 2 * (x + 1 + 1) ^ (-s) ≤ (x + 1) ^ 2 * (x + 1 + 1) ^ (-s) := by
          gcongr
          linarith
        nlinarith
      have hpow : x ^ 2 * (x + 1) ^ (-(s + 1)) ≤ x ^ (-(4 + δ)) := by
        rw [hs6, hsplit _ hx1]
        calc x ^ 2 * ((x + 1) ^ (-(4 + δ)) / (x + 1) ^ 2)
            = (x + 1) ^ (-(4 + δ)) * (x ^ 2 / (x + 1) ^ 2) := by ring
          _ ≤ (x + 1) ^ (-(4 + δ)) * 1 := by
              gcongr
              rw [div_le_one (by positivity)]
              nlinarith
          _ ≤ _ := by rw [mul_one]; exact h4
      have hs6' : s ≤ 6 := by rw [hs]; linarith
      have hstep : x ^ 2 * ((x + 1) ^ (-s) - (x + 1 + 1) ^ (-s)) ≤ 6 * x ^ (-(4 + δ)) := by
        have hxp : 0 ≤ x ^ 2 := by positivity
        have hr : 0 ≤ (x + 1) ^ (-(s + 1)) := (Real.rpow_pos_of_pos hx1 _).le
        calc x ^ 2 * ((x + 1) ^ (-s) - (x + 1 + 1) ^ (-s))
            ≤ x ^ 2 * (s * (x + 1 + 1 - (x + 1)) * (x + 1) ^ (-(s + 1))) :=
              mul_le_mul_of_nonneg_left hdiff hxp
          _ = s * (x ^ 2 * (x + 1) ^ (-(s + 1))) := by ring
          _ ≤ 6 * (x ^ 2 * (x + 1) ^ (-(s + 1))) := by gcongr
          _ ≤ 6 * x ^ (-(4 + δ)) := by gcongr
      linarith
    · -- upper bound
      have hup : h (x + 1) - h x ≤ (2 * x + 1) * (x + 1) ^ (-s) := by
        simp only [hh]
        have : (x + 1 + 1) ^ (-s) ≤ (x + 1) ^ (-s) :=
          rpow_neg_le_of_le hx1 (by linarith) (by rw [hs]; linarith)
        have hp : 0 ≤ (x + 1) ^ 2 := by positivity
        nlinarith [mul_le_mul_of_nonneg_left this hp]
      have hs5 : s = (4 + δ) + ((1 : ℕ) : ℝ) := by rw [hs]; push_cast; ring
      have hbound : (2 * x + 1) * (x + 1) ^ (-s) ≤ 2 * x ^ (-(4 + δ)) := by
        rw [hs5, hsplit _ hx1]
        have hp : 0 ≤ (x + 1) ^ (-(4 + δ)) := (Real.rpow_pos_of_pos hx1 _).le
        calc (2 * x + 1) * ((x + 1) ^ (-(4 + δ)) / (x + 1) ^ 1)
            = (x + 1) ^ (-(4 + δ)) * ((2 * x + 1) / (x + 1)) := by ring
          _ ≤ (x + 1) ^ (-(4 + δ)) * 2 := by
              gcongr
              rw [div_le_iff₀ hx1]
              linarith
          _ ≤ x ^ (-(4 + δ)) * 2 := by gcongr
          _ = _ := by ring
      have hp : 0 ≤ x ^ (-(4 + δ)) := (Real.rpow_pos_of_pos hx0 _).le
      linarith
  have hQk : Q (x + 1) ^ k ≤ 1 := pow_le_one₀ (hQ0.trans hQmono) hQ1
  have hQk0 : 0 ≤ Q (x + 1) ^ k := pow_nonneg (hQ0.trans hQmono) k
  rw [hg, hg]
  have hdec : h (x + 1) * Q (x + 1) ^ k - h x * Q x ^ k =
      (h (x + 1) - h x) * Q (x + 1) ^ k + h x * (Q (x + 1) ^ k - Q x ^ k) := by ring
  rw [hdec]
  have hA : |(h (x + 1) - h x) * Q (x + 1) ^ k| ≤ 6 * x ^ (-(4 + δ)) := by
    rw [abs_mul, abs_of_nonneg hQk0]
    calc |h (x + 1) - h x| * Q (x + 1) ^ k ≤ |h (x + 1) - h x| * 1 :=
          mul_le_mul_of_nonneg_left hQk (abs_nonneg _)
      _ ≤ _ := by rw [mul_one]; exact hfirst
  calc _ ≤ |(h (x + 1) - h x) * Q (x + 1) ^ k| + |h x * (Q (x + 1) ^ k - Q x ^ k)| :=
        abs_add_le _ _
    _ ≤ 6 * x ^ (-(4 + δ)) + 2 * x ^ (-(4 + δ)) := by
        rw [abs_of_nonneg hsecond.1]
        linarith [hsecond.2]
    _ = _ := by ring

/-- `Σ_{U < n ≤ M} n^{-(s+1)} ≤ U^{-s}/s` for `U ≥ 1`, `s > 0`. -/
theorem sum_Ioc_rpow_neg_le {s : ℝ} (hs : 0 < s) {U : ℕ} (hU : 1 ≤ U) (M : ℕ) :
    ∑ n ∈ Ioc U M, (n : ℝ) ^ (-(s + 1)) ≤ (U : ℝ) ^ (-s) / s := by
  have hterm : ∀ n ∈ Ioc U M, (n : ℝ) ^ (-(s + 1)) ≤
      (((n - 1 : ℕ) : ℝ) ^ (-s) - (n : ℝ) ^ (-s)) / s := by
    intro n hn
    have hn' := mem_Ioc.mp hn
    have h1 : (1 : ℝ) ≤ ((n - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ n - 1)
    have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega)]; simp
    have h := le_rpow_neg_sub_rpow_neg (s := s) (show (0 : ℝ) < ((n - 1 : ℕ) : ℝ) by linarith)
      (show ((n - 1 : ℕ) : ℝ) ≤ n by rw [hcast]; linarith) hs.le
    rw [le_div_iff₀ hs]
    rw [hcast] at h ⊢
    nlinarith
  have htel : ∀ M, U ≤ M → ∑ n ∈ Ioc U M, (((n - 1 : ℕ) : ℝ) ^ (-s) - (n : ℝ) ^ (-s)) =
      (U : ℝ) ^ (-s) - (M : ℝ) ^ (-s) := by
    intro M hM
    induction M, hM using Nat.le_induction with
    | base => simp
    | succ M hM ih =>
      rw [Finset.sum_Ioc_succ_top hM, ih]
      simp
  rcases le_or_gt M U with hMU | hMU
  · rw [Finset.Ioc_eq_empty (by omega), Finset.sum_empty]
    have : 0 ≤ (U : ℝ) ^ (-s) := Real.rpow_nonneg (by positivity) _
    positivity
  · calc ∑ n ∈ Ioc U M, (n : ℝ) ^ (-(s + 1))
        ≤ ∑ n ∈ Ioc U M, (((n - 1 : ℕ) : ℝ) ^ (-s) - (n : ℝ) ^ (-s)) / s := sum_le_sum hterm
      _ = ((U : ℝ) ^ (-s) - (M : ℝ) ^ (-s)) / s := by rw [← Finset.sum_div, htel M hMU.le]
      _ ≤ (U : ℝ) ^ (-s) / s := by
          gcongr
          have : 0 ≤ (M : ℝ) ^ (-s) := Real.rpow_nonneg (by positivity) _
          linarith

/-! ### The low-edge absolute sum -/

/-- The primitive `F(y) = y^{-1-δ} e^{-2k/y} / (2k)`. -/
def lowPrimitive (δ k y : ℝ) : ℝ := y ^ (-(1 + δ)) * Real.exp (-(2 * k / y)) / (2 * k)

theorem lowPrimitive_nonneg (δ : ℝ) {k y : ℝ} (hk : 0 < k) (hy : 0 < y) :
    0 ≤ lowPrimitive δ k y := by
  unfold lowPrimitive
  have := Real.rpow_pos_of_pos hy (-(1 + δ))
  positivity

/-- `m^{-3-δ} e^{-2k/m} ≤ 2 (F(m+1) - F(m))` for `2 ≤ m`, `6m ≤ k`, `0 ≤ δ ≤ 1`. -/
theorem rpow_exp_le_lowPrimitive_sub {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) {k m : ℝ}
    (hm : 2 ≤ m) (hmk : 6 * m ≤ k) :
    m ^ (-(3 + δ)) * Real.exp (-(2 * k / m)) ≤
      2 * (lowPrimitive δ k (m + 1) - lowPrimitive δ k m) := by
  have hm0 : 0 < m := by linarith
  have hm1 : 0 < m + 1 := by linarith
  have hk : 0 < k := by linarith
  set s : ℝ := 1 + δ with hs
  set E : ℝ := Real.exp (-(2 * k / m)) with hE
  set u : ℝ := 2 * k / (m * (m + 1)) with hu
  have hE0 : 0 < E := Real.exp_pos _
  have hexpu : Real.exp (-(2 * k / (m + 1))) = E * Real.exp u := by
    rw [hE, ← Real.exp_add]
    congr 1
    rw [hu]
    field_simp
    ring
  -- `(m+1)^{-s} ≥ m^{-s} e^{-s/m}`
  have hratio : (m + 1) / m ≤ Real.exp (1 / m) := by
    have h := Real.add_one_le_exp (1 / m)
    have : (m + 1) / m = 1 / m + 1 := by field_simp; ring
    linarith
  have hpow : m ^ (-s) * Real.exp (-(s / m)) ≤ (m + 1) ^ (-s) := by
    have hsplit : (m + 1) ^ (-s) = m ^ (-s) * ((m + 1) / m) ^ (-s) := by
      rw [← Real.mul_rpow hm0.le (by positivity)]
      congr 1
      field_simp
    rw [hsplit]
    apply mul_le_mul_of_nonneg_left _ (Real.rpow_pos_of_pos hm0 _).le
    have : ((m + 1) / m) ^ (-s) ≥ Real.exp (1 / m) ^ (-s) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) hratio (by rw [hs]; linarith)
    rw [← Real.exp_mul] at this
    calc Real.exp (-(s / m)) = Real.exp (1 / m * -s) := by congr 1; ring
      _ ≤ _ := this
  -- key inequality `u - s/m ≥ k/m²`
  have hkey : k / m ^ 2 ≤ u - s / m := by
    have hs2 : s ≤ 2 := by rw [hs]; linarith
    have e : u - s / m - k / m ^ 2 = (k * (m - 1) - s * m * (m + 1)) / (m ^ 2 * (m + 1)) := by
      rw [hu]
      field_simp
      ring
    have hnum : 0 ≤ k * (m - 1) - s * m * (m + 1) := by nlinarith
    have : 0 ≤ (k * (m - 1) - s * m * (m + 1)) / (m ^ 2 * (m + 1)) :=
      div_nonneg hnum (by positivity)
    linarith
  -- assemble
  have hdiff : 2 * k * (lowPrimitive δ k (m + 1) - lowPrimitive δ k m) =
      (m + 1) ^ (-s) * (E * Real.exp u) - m ^ (-s) * E := by
    unfold lowPrimitive
    rw [hexpu]
    field_simp
    rw [← hs, ← hE]
    ring
  have hlow : m ^ (-s) * E * (u - s / m) ≤
      (m + 1) ^ (-s) * (E * Real.exp u) - m ^ (-s) * E := by
    have h1 : m ^ (-s) * Real.exp (-(s / m)) * (E * Real.exp u) ≤
        (m + 1) ^ (-s) * (E * Real.exp u) :=
      mul_le_mul_of_nonneg_right hpow (by positivity)
    have h2 : Real.exp (-(s / m)) * Real.exp u = Real.exp (u - s / m) := by
      rw [← Real.exp_add]; ring_nf
    have h3 : u - s / m + 1 ≤ Real.exp (u - s / m) := Real.add_one_le_exp _
    have hms : 0 < m ^ (-s) := Real.rpow_pos_of_pos hm0 _
    have h4 : m ^ (-s) * E * (u - s / m) ≤ m ^ (-s) * E * (Real.exp (u - s / m) - 1) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    calc m ^ (-s) * E * (u - s / m) ≤ m ^ (-s) * E * (Real.exp (u - s / m) - 1) := h4
      _ = m ^ (-s) * Real.exp (-(s / m)) * (E * Real.exp u) - m ^ (-s) * E := by
          rw [← h2]; ring
      _ ≤ _ := by linarith
  have hm3 : m ^ (-(3 + δ)) = m ^ (-s) / m ^ 2 := by
    rw [show (3 : ℝ) + δ = s + ((2 : ℕ) : ℝ) by rw [hs]; push_cast; ring,
      show -(s + ((2 : ℕ) : ℝ)) = -s + -((2 : ℕ) : ℝ) by ring, Real.rpow_add hm0,
      Real.rpow_neg hm0.le ((2 : ℕ) : ℝ), Real.rpow_natCast, div_eq_mul_inv]
  have hms : 0 < m ^ (-s) := Real.rpow_pos_of_pos hm0 _
  have hfinal : k * (m ^ (-(3 + δ)) * E) ≤
      k * (2 * (lowPrimitive δ k (m + 1) - lowPrimitive δ k m)) := by
    have e1 : k * (m ^ (-(3 + δ)) * E) = m ^ (-s) * E * (k / m ^ 2) := by
      rw [hm3]; field_simp
    have e2 : k * (2 * (lowPrimitive δ k (m + 1) - lowPrimitive δ k m)) =
        (m + 1) ^ (-s) * (E * Real.exp u) - m ^ (-s) * E := by
      rw [← hdiff]; ring
    rw [e1, e2]
    calc m ^ (-s) * E * (k / m ^ 2) ≤ m ^ (-s) * E * (u - s / m) :=
          mul_le_mul_of_nonneg_left hkey (by positivity)
      _ ≤ _ := hlow
  exact le_of_mul_le_mul_left hfinal hk

/-- `Σ_{1 ≤ n ≤ M} (n+1)^{-3-δ} e^{-2k/(n+1)} ≤ (M+2)^{-1-δ} e^{-2k/(M+2)} / k` when
`6(M+1) ≤ k`. -/
theorem sum_rpow_exp_low_le {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) {k : ℝ} (hk : 0 < k) (M : ℕ)
    (hM : 6 * ((M : ℝ) + 1) ≤ k) :
    ∑ n ∈ Ioc 0 M, ((n : ℝ) + 1) ^ (-(3 + δ)) * Real.exp (-(2 * k / ((n : ℝ) + 1))) ≤
      ((M : ℝ) + 2) ^ (-(1 + δ)) * Real.exp (-(2 * k / ((M : ℝ) + 2))) / k := by
  set G : ℕ → ℝ := fun n => lowPrimitive δ k ((n : ℝ) + 1) with hG
  have hterm : ∀ n ∈ Ioc 0 M, ((n : ℝ) + 1) ^ (-(3 + δ)) *
      Real.exp (-(2 * k / ((n : ℝ) + 1))) ≤ 2 * (G (n + 1) - G n) := by
    intro n hn
    have hn' := mem_Ioc.mp hn
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn'.1
    have hnM : (n : ℝ) ≤ M := by exact_mod_cast hn'.2
    have h := rpow_exp_le_lowPrimitive_sub hδ0 hδ1 (m := (n : ℝ) + 1) (by linarith)
      (by linarith)
    simp only [hG]
    push_cast
    exact h
  calc _ ≤ ∑ n ∈ Ioc 0 M, 2 * (G (n + 1) - G n) := sum_le_sum hterm
    _ = 2 * (G (M + 1) - G 1) := by
        rw [← Finset.mul_sum, sum_Ioc_telescope G (Nat.zero_le M)]
    _ ≤ 2 * G (M + 1) := by
        have : 0 ≤ G 1 := lowPrimitive_nonneg δ hk (by positivity)
        linarith
    _ = _ := by
        simp only [hG, lowPrimitive]
        push_cast
        rw [show (M : ℝ) + 1 + 1 = (M : ℝ) + 2 by ring]
        field_simp

/-- **Low-edge packet bound.**  For `c ≤ M` and `6(M+1) ≤ k`,
`|Σ_{1 ≤ n ≤ c} μ(n) g_k(n)| ≤ (M+2)^{-1-δ} e^{-2k/(M+2)} / k`. -/
theorem abs_sum_low_packetKernel_le {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) {k : ℕ} (hk : 1 ≤ k)
    {c M : ℕ} (hc : c ≤ M) (hM : 6 * ((M : ℝ) + 1) ≤ k) :
    |∑ n ∈ Ioc 0 c, ((μ n : ℤ) : ℝ) * packetKernel δ k n| ≤
      ((M : ℝ) + 2) ^ (-(1 + δ)) * Real.exp (-(2 * k / ((M : ℝ) + 2))) / k := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hterm : ∀ n ∈ Ioc 0 c, |((μ n : ℤ) : ℝ) * packetKernel δ k n| ≤
      ((n : ℝ) + 1) ^ (-(3 + δ)) * Real.exp (-(2 * k / ((n : ℝ) + 1))) := by
    intro n hn
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (mem_Ioc.mp hn).1
    rw [abs_mul, abs_of_nonneg (packetKernel_nonneg k hn1)]
    calc |((μ n : ℤ) : ℝ)| * packetKernel δ k n ≤ 1 * packetKernel δ k n :=
          mul_le_mul_of_nonneg_right (abs_moebius_le_one' n) (packetKernel_nonneg k hn1)
      _ ≤ _ := by rw [one_mul]; exact packetKernel_le k hn1
  have hsub : Ioc 0 c ⊆ Ioc 0 M := Finset.Ioc_subset_Ioc_right hc
  calc _ ≤ ∑ n ∈ Ioc 0 c, |((μ n : ℤ) : ℝ) * packetKernel δ k n| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ n ∈ Ioc 0 c, ((n : ℝ) + 1) ^ (-(3 + δ)) * Real.exp (-(2 * k / ((n : ℝ) + 1))) :=
        sum_le_sum hterm
    _ ≤ ∑ n ∈ Ioc 0 M, ((n : ℝ) + 1) ^ (-(3 + δ)) * Real.exp (-(2 * k / ((n : ℝ) + 1))) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hsub
        intro n _ _
        have := Real.rpow_pos_of_pos (show (0 : ℝ) < (n : ℝ) + 1 by positivity) (-(3 + δ))
        positivity
    _ ≤ _ := sum_rpow_exp_low_le hδ0 hδ1 hk0 M hM

/-! ### Geometric tails -/

/-- `Σ_{j ≥ 0} (j+K)^p x^{j+K} ≤ K^p x^K / (1 - x e^{p/K})` when `x e^{p/K} < 1`. -/
theorem rpow_mul_pow_tail {p x : ℝ} (hp : 0 ≤ p) (hx : 0 < x) {K : ℕ} (hK : 1 ≤ K)
    (hρ : x * Real.exp (p / K) < 1) :
    Summable (fun j : ℕ => ((j + K : ℕ) : ℝ) ^ p * x ^ (j + K)) ∧
      ∑' j : ℕ, ((j + K : ℕ) : ℝ) ^ p * x ^ (j + K) ≤
        (K : ℝ) ^ p * x ^ K / (1 - x * Real.exp (p / K)) := by
  have hK0 : (0 : ℝ) < K := by exact_mod_cast hK
  set ρ : ℝ := x * Real.exp (p / K) with hρdef
  have hρ0 : 0 ≤ ρ := by positivity
  have hterm : ∀ j : ℕ, ((j + K : ℕ) : ℝ) ^ p * x ^ (j + K) ≤ (K : ℝ) ^ p * x ^ K * ρ ^ j := by
    intro j
    have hjK : ((j + K : ℕ) : ℝ) = (K : ℝ) * (1 + j / K) := by
      push_cast; field_simp; ring
    have h1 : (1 + (j : ℝ) / K) ^ p ≤ Real.exp (p / K) ^ j := by
      calc (1 + (j : ℝ) / K) ^ p ≤ Real.exp ((j : ℝ) / K) ^ p :=
            Real.rpow_le_rpow (by positivity) (by linarith [Real.add_one_le_exp ((j : ℝ) / K)]) hp
        _ = Real.exp (p / K) ^ j := by
            rw [← Real.exp_mul, ← Real.exp_nat_mul]
            ring_nf
    rw [hjK, Real.mul_rpow hK0.le (by positivity), pow_add, hρdef, mul_pow]
    have hxj : 0 ≤ x ^ j := pow_nonneg hx.le j
    have hKp : 0 ≤ (K : ℝ) ^ p := Real.rpow_nonneg hK0.le p
    calc (K : ℝ) ^ p * (1 + (j : ℝ) / K) ^ p * (x ^ j * x ^ K)
        ≤ (K : ℝ) ^ p * Real.exp (p / K) ^ j * (x ^ j * x ^ K) := by gcongr
      _ = _ := by ring
  have hgeo : Summable (fun j : ℕ => (K : ℝ) ^ p * x ^ K * ρ ^ j) :=
    (summable_geometric_of_lt_one hρ0 hρ).mul_left _
  have hsum : Summable (fun j : ℕ => ((j + K : ℕ) : ℝ) ^ p * x ^ (j + K)) :=
    Summable.of_nonneg_of_le (fun j => by positivity) hterm hgeo
  refine ⟨hsum, ?_⟩
  calc ∑' j : ℕ, ((j + K : ℕ) : ℝ) ^ p * x ^ (j + K)
      ≤ ∑' j : ℕ, (K : ℝ) ^ p * x ^ K * ρ ^ j := hsum.tsum_le_tsum hterm hgeo
    _ = (K : ℝ) ^ p * x ^ K * (1 - ρ)⁻¹ := by
        rw [tsum_mul_left, tsum_geometric_of_lt_one hρ0 hρ]
    _ = _ := by rw [div_eq_mul_inv]

/-! ### Summability at the Mertens saving -/

/-- `u^p e^{-c u^{1/3}} ≤ C e^{-(c/2) u^{1/3}}` for `u ≥ 0`. -/
theorem pow_mul_exp_neg_cbrt_le (p : ℕ) {c : ℝ} (hc : 0 < c) :
    ∃ C : ℝ, 0 < C ∧ ∀ u : ℝ, 0 ≤ u →
      u ^ p * Real.exp (-(c * u ^ ((1 : ℝ) / 3))) ≤
        C * Real.exp (-(c / 2 * u ^ ((1 : ℝ) / 3))) := by
  refine ⟨(2 / c) ^ (3 * p) * ((3 * p).factorial : ℝ) + 1, by positivity, fun u hu => ?_⟩
  set v : ℝ := u ^ ((1 : ℝ) / 3) with hv
  have hv0 : 0 ≤ v := Real.rpow_nonneg hu _
  have huv : u = v ^ 3 := by
    rw [hv, ← Real.rpow_natCast, ← Real.rpow_mul hu]
    norm_num
  have hfac := Real.pow_div_factorial_le_exp (c / 2 * v) (by positivity) (3 * p)
  have hbound : v ^ (3 * p) ≤ (2 / c) ^ (3 * p) * ((3 * p).factorial : ℝ) *
      Real.exp (c / 2 * v) := by
    have hf : (0 : ℝ) < ((3 * p).factorial : ℝ) := by positivity
    rw [div_le_iff₀ hf] at hfac
    have e : v ^ (3 * p) = (2 / c) ^ (3 * p) * (c / 2 * v) ^ (3 * p) := by
      rw [← mul_pow]
      congr 1
      field_simp
    rw [e]
    have : 0 ≤ (2 / c) ^ (3 * p) := by positivity
    calc (2 / c) ^ (3 * p) * (c / 2 * v) ^ (3 * p)
        ≤ (2 / c) ^ (3 * p) * (Real.exp (c / 2 * v) * ((3 * p).factorial : ℝ)) :=
          mul_le_mul_of_nonneg_left hfac this
      _ = _ := by ring
  rw [huv, ← pow_mul]
  have hsplit : Real.exp (-(c * v)) = (Real.exp (c / 2 * v))⁻¹ * Real.exp (-(c / 2 * v)) := by
    rw [← Real.exp_neg, ← Real.exp_add]
    ring_nf
  rw [hsplit]
  have he : 0 < Real.exp (c / 2 * v) := Real.exp_pos _
  have he2 : 0 < Real.exp (-(c / 2 * v)) := Real.exp_pos _
  calc v ^ (3 * p) * ((Real.exp (c / 2 * v))⁻¹ * Real.exp (-(c / 2 * v)))
      = v ^ (3 * p) / Real.exp (c / 2 * v) * Real.exp (-(c / 2 * v)) := by ring
    _ ≤ ((2 / c) ^ (3 * p) * ((3 * p).factorial : ℝ)) * Real.exp (-(c / 2 * v)) := by
        gcongr
        rw [div_le_iff₀ he]
        exact hbound
    _ ≤ _ := by
        gcongr
        linarith

/-- `Σ_m e^{-c (log m)^{1/3}} / m < ∞` for `c > 0`, by Cauchy condensation. -/
theorem summable_exp_neg_cbrt_log_div {c : ℝ} (hc : 0 < c) :
    Summable (fun m : ℕ => Real.exp (-(c * Real.log m ^ ((1 : ℝ) / 3))) / m) := by
  set f : ℕ → ℝ := fun m => Real.exp (-(c * Real.log m ^ ((1 : ℝ) / 3))) / m with hf
  have hnonneg : ∀ m, 0 ≤ f m := fun m => by simp only [hf]; positivity
  have hmono : ∀ ⦃m n : ℕ⦄, 0 < m → m ≤ n → f n ≤ f m := by
    intro m n hm hmn
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
    have hmn' : (m : ℝ) ≤ n := by exact_mod_cast hmn
    have hlog : Real.log m ≤ Real.log n := Real.log_le_log (by linarith) hmn'
    have hlog0 : 0 ≤ Real.log m := Real.log_nonneg hm1
    have hr : Real.log m ^ ((1 : ℝ) / 3) ≤ Real.log n ^ ((1 : ℝ) / 3) :=
      Real.rpow_le_rpow hlog0 hlog (by norm_num)
    have hexp : Real.exp (-(c * Real.log n ^ ((1 : ℝ) / 3))) ≤
        Real.exp (-(c * Real.log m ^ ((1 : ℝ) / 3))) :=
      Real.exp_le_exp.mpr (by nlinarith)
    simp only [hf]
    exact div_le_div₀ (Real.exp_pos _).le hexp (by linarith) hmn'
  rw [← summable_condensed_iff_of_nonneg hnonneg hmono]
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have ha : (0 : ℝ) < c * Real.log 2 ^ ((1 : ℝ) / 3) := by positivity
  have hbase := GaloisForLFunctions.HTGeometry.summable_rpow_mul_exp_neg_rpow (A := 0) ha
    (show (0 : ℝ) < 1 / 3 by norm_num)
  refine hbase.congr fun k => ?_
  have h2k : (((2 : ℕ) ^ k : ℕ) : ℝ) = (2 : ℝ) ^ k := by push_cast; ring
  simp only [hf, Real.rpow_zero, one_mul]
  rw [h2k, Real.log_pow, Real.mul_rpow (Nat.cast_nonneg k) hlog2.le]
  have hpow : (2 : ℝ) ^ k ≠ 0 := by positivity
  field_simp

/-- `Σ_m (log m)^p e^{-c (log m)^{1/3}} / m < ∞` for `c > 0`. -/
theorem summable_log_pow_mul_exp_neg_cbrt_log_div (p : ℕ) {c : ℝ} (hc : 0 < c) :
    Summable (fun m : ℕ => Real.log m ^ p * Real.exp (-(c * Real.log m ^ ((1 : ℝ) / 3))) / m) := by
  obtain ⟨C, hC, hbound⟩ := pow_mul_exp_neg_cbrt_le p hc
  refine Summable.of_nonneg_of_le (fun m => ?_) (fun m => ?_)
    ((summable_exp_neg_cbrt_log_div (half_pos hc)).mul_left C)
  · rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp
    · have : 0 ≤ Real.log m := Real.log_nonneg (by exact_mod_cast hm)
      positivity
  · rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp
    · have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
      have hl : 0 ≤ Real.log m := Real.log_nonneg hm1
      have h := hbound (Real.log m) hl
      have hm0 : (0 : ℝ) < m := by linarith
      rw [mul_div_assoc']
      exact div_le_div_of_nonneg_right (by linarith) hm0.le

/-- `Σ_k (log k)^p E(k)² / k < ∞`. -/
theorem summable_log_pow_mul_mertensSaving_sq_div (p : ℕ) :
    Summable (fun k : ℕ => Real.log k ^ p * mertensSaving k ^ 2 / k) := by
  refine (summable_log_pow_mul_exp_neg_cbrt_log_div p (c := 1 / 54) (by norm_num)).congr
    fun k => ?_
  simp only [mertensSaving, deningerMertensSaving]
  rw [← Real.exp_nat_mul]
  congr 3
  push_cast
  ring

/-- The Mertens saving is sub-polynomial at order `1/6`: `k^{-1/3} ≤ C E(k)²`. -/
theorem exists_rpow_neg_third_le_mertensSaving_sq :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 1 ≤ x → x ^ (-(1 / 3 : ℝ)) ≤ C * mertensSaving x ^ 2 := by
  obtain ⟨K, hK, hge⟩ := mertensSaving_ge (η := 1 / 6) (by norm_num)
  refine ⟨K ^ 2, by positivity, fun x hx => ?_⟩
  have h := hge x hx
  have hx0 : 0 < x := by linarith
  have hp : 0 ≤ K⁻¹ * x ^ (-(1 / 6 : ℝ)) := by
    have := Real.rpow_pos_of_pos hx0 (-(1 / 6 : ℝ))
    positivity
  have hsq : (K⁻¹ * x ^ (-(1 / 6 : ℝ))) ^ 2 ≤ mertensSaving x ^ 2 :=
    pow_le_pow_left₀ hp h 2
  have e0 : (x ^ (-(1 / 6 : ℝ))) ^ 2 = x ^ (-(1 / 3 : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
    norm_num
  have e : (K⁻¹ * x ^ (-(1 / 6 : ℝ))) ^ 2 = (K ^ 2)⁻¹ * x ^ (-(1 / 3 : ℝ)) := by
    rw [mul_pow, inv_pow, e0]
  rw [e] at hsq
  have hK2 : 0 < K ^ 2 := by positivity
  calc x ^ (-(1 / 3 : ℝ)) = K ^ 2 * ((K ^ 2)⁻¹ * x ^ (-(1 / 3 : ℝ))) := by field_simp
    _ ≤ K ^ 2 * mertensSaving x ^ 2 := by gcongr

/-- `E(x) (log x)^p → 0`. -/
theorem tendsto_mertensSaving_mul_log_pow (p : ℕ) :
    Tendsto (fun x => mertensSaving x * Real.log x ^ p) atTop (𝓝 0) := by
  have hg : Tendsto (fun u : ℝ => 108 ^ (3 * p) * ((u / 108) ^ (3 * p) * Real.exp (-(u / 108))))
      atTop (𝓝 0) := by
    have h := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero (3 * p)).comp
      (tendsto_id.atTop_div_const (by norm_num : (0 : ℝ) < 108))
    have := h.const_mul (108 ^ (3 * p))
    rw [mul_zero] at this
    exact this
  have hu : Tendsto (fun x : ℝ => Real.log x ^ ((1 : ℝ) / 3)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp Real.tendsto_log_atTop
  refine (hg.comp hu).congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  have hl : 0 ≤ Real.log x := Real.log_nonneg hx.le
  simp only [Function.comp_apply, mertensSaving, deningerMertensSaving]
  have hc : (Real.log x ^ ((1 : ℝ) / 3)) ^ (3 * p) = Real.log x ^ p := by
    rw [← Real.rpow_natCast (Real.log x ^ ((1 : ℝ) / 3)) (3 * p), ← Real.rpow_mul hl,
      ← Real.rpow_natCast]
    congr 1
    push_cast
    ring
  rw [div_pow, hc]
  field_simp

end RHTower.DiscretePacket
