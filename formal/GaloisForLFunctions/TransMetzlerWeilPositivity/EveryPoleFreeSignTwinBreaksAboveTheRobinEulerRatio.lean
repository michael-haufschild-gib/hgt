import GaloisForLFunctions.TransMetzlerWeilPositivity.LiouvilleTwinSelectivity
import GaloisForLFunctions.ArithmeticCountingPositivity.CofinitePrimeFlipsHaveZeroGap

/-!
# Every pole-free sign twin breaks above the Robin–Euler ratio

Let `ω` be completely multiplicative with values `±1` on the positive integers and with bounded
harmonic sums, `|Σ_{n ≤ M} ω(n)/n| ≤ B` (its Dirichlet series has no pole at `s = 1`). The
projection of `ωb`, `b_n = n^{−1/2}`, onto the pole hyperplane `Σ x_n/√n = 0` is
`x = (ω − s)b`, `s = S/H`; the twin's prime form at `x` is `ζ`'s at `b − sωb`, which reaches
`log M − γ − ε` per unit mass, the corrections being `O(B²)` (`exists_bounded_hyperplane_signTwin_witness`).
Below the spacing the gauge is a congruence, so the twin's complete form on this sub-horizon
witness is its Markov form, and above the Robin–Euler ratio the leading coefficient is negative
(`eventually_signTwin_weilQuadTw_neg_of_gt_robinEuler`). The Liouville twin is the case `B = 2`;
every cofinite flip `λ · ω_F` (all primes outside a finite set `F` flipped) is pole-free with
`B = 2/c_F` (`eventually_cofiniteFlip_weilQuadTw_neg_of_gt_robinEuler`).
-/

noncomputable section

open MeasureTheory Filter Topology Finset RHTower
open scoped Real

namespace GaloisForLFunctions.TransMetzlerWeilPositivity

open SpacingScaleHarmonicAnalysis CriticalArithmeticCorrelationTheory
  RenormalizedArithmeticPotentialTheory SelectiveMultiscaleArithmeticPositivity
  ArithmeticLorentzianGeometry ArithmeticElectrostatics

section SignTwin

variable {ω : ArithmeticFunction ℝ}

theorem abs_signTwin (hsign : ∀ n, 0 < n → ω n = 1 ∨ ω n = -1) {n : ℕ} (hn : 0 < n) :
    |ω n| = 1 := by
  rcases hsign n hn with h | h <;> simp [h]

theorem signTwin_mul_self (hsign : ∀ n, 0 < n → ω n = 1 ∨ ω n = -1) {n : ℕ} (hn : 0 < n) :
    ω n * ω n = 1 := by
  rcases hsign n hn with h | h <;> simp [h]

variable (hω : ∀ a b, ω (a * b) = ω a * ω b) (hsign : ∀ n, 0 < n → ω n = 1 ∨ ω n = -1)
  {Bω : ℝ} (hB : ∀ M : ℕ, |∑ n ∈ Icc 1 M, ω n / n| ≤ Bω)

include hsign hB in
/-- Projected pole witness of a pole-free sign twin on `Icc 1 M`: on the pole hyperplane, with
`n x_n² ≤ 4` and `log M − 2 ≤ Σ x_n²`, attaining `log M − γ − ε` in the twin's prime form. -/
theorem exists_bounded_hyperplane_signTwin_witness {ε : ℝ} (hε : 0 < ε) :
    ∃ M₀ : ℕ, 1 ≤ M₀ ∧ ∀ M, M₀ ≤ M →
      ∃ x : ℕ → ℝ,
        (∀ n, n ∉ Icc 1 M → x n = 0) ∧
        ∑ n ∈ Icc 1 M, x n / Real.sqrt n = 0 ∧
        (∀ n ∈ Icc 1 M, (n : ℝ) * x n ^ 2 ≤ 4) ∧
        Real.log M - 2 ≤ ∑ n ∈ Icc 1 M, x n ^ 2 ∧
        0 < ∑ n ∈ Icc 1 M, x n ^ 2 ∧
        (Real.log M - Real.eulerMascheroniConstant - ε) * ∑ n ∈ Icc 1 M, x n ^ 2 ≤
          atomicWeilForm M (fun n => ω n * x n) := by
  let γ := Real.eulerMascheroniConstant
  obtain ⟨M₁, hM₁⟩ := eventually_atomicWeilForm_truncPole_ge (show 0 < ε / 2 by positivity)
  set C₀ := Real.log 4 + 4
  set Bm := Real.log 4 + 4 + Real.log 2 + γ
  have hC₀ : 0 ≤ C₀ := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ 4 by norm_num)
    positivity
  have hγ : 0 < γ := by linarith [Real.one_half_lt_eulerMascheroniConstant]
  have hBm : 0 ≤ Bm := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ 2 by norm_num)
    positivity
  set K := Bω ^ 2 + Bω ^ 2 * C₀ + 2 * Bω ^ 2 + 2 * Bω ^ 2 * γ + 2 * Bω * Bm
  obtain ⟨M₂, hM₂⟩ := Filter.eventually_atTop.mp
    ((Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop
      (max (γ + ε) (max (2 * K / ε) (max 3 (Bω + Bω ^ 2)))))
  refine ⟨max 1 (max M₁ M₂), le_max_left _ _, fun M hM => ?_⟩
  have hM1_ge : 1 ≤ M := (le_max_left _ _).trans hM
  have hMM₁ : M₁ ≤ M := (le_max_left _ _).trans ((le_max_right _ _).trans hM)
  have hMM₂ : M₂ ≤ M := (le_max_right _ _).trans ((le_max_right _ _).trans hM)
  have hlog_ge := hM₂ M hMM₂
  simp only [Function.comp] at hlog_ge
  have hLγ : γ + ε ≤ Real.log M := (le_max_left _ _).trans hlog_ge
  have hLK : 2 * K / ε ≤ Real.log M := ((le_max_left _ _).trans (le_max_right _ _)).trans hlog_ge
  have hL3 : 3 ≤ Real.log M :=
    ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans hlog_ge
  have hLB : Bω + Bω ^ 2 ≤ Real.log M :=
    ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans hlog_ge
  set b := truncPole M
  set H := ∑ n ∈ Icc 1 M, (1 : ℝ) / n
  set S := ∑ n ∈ Icc 1 M, ω n / n
  set L := Real.log M
  have hb_zero : ∀ n, n ∉ Icc 1 M → b n = 0 := fun n hn => by
    simp only [mem_Icc, not_and_or, not_le] at hn
    rcases hn with hn0 | hnM
    · have : n = 0 := by omega
      subst this; simp [b, truncPole, poleVector]
    · simp [b, truncPole, if_neg (not_le.mpr hnM)]
  have hb2 : ∀ n ∈ Icc 1 M, b n ^ 2 = 1 / n := fun n hn => by
    simp only [b, truncPole, if_pos (mem_Icc.mp hn).2, poleVector_sq]
  have hbsq : ∑ n ∈ Icc 1 M, b n ^ 2 = H := sum_congr rfl hb2
  have hbs : ∀ n ∈ Icc 1 M, b n / Real.sqrt n = 1 / n := fun n hn => by
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
    simp only [b, truncPole, if_pos (mem_Icc.mp hn).2, poleVector]
    rw [div_div, Real.mul_self_sqrt hn0.le]
  have hHL : L ≤ H := by
    have h := log_add_one_le_harmonic M
    rw [RHTower.harmonic_eq_sum_Icc] at h
    push_cast at h
    have : L ≤ Real.log ((M : ℝ) + 1) := Real.log_le_log (by exact_mod_cast hM1_ge) (by linarith)
    linarith
  have hH3 : 3 ≤ H := hL3.trans hHL
  have hH0 : 0 < H := by linarith only [hH3]
  have hS : |S| ≤ Bω := hB M
  have hBω : 0 ≤ Bω := (abs_nonneg S).trans hS
  have hBH : Bω ≤ H := by nlinarith only [hLB, hHL, sq_nonneg Bω]
  have hB2H : Bω ^ 2 ≤ H := by nlinarith only [hLB, hHL, hBω]
  have hS2 : S ^ 2 ≤ Bω ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg S) hS 2
  set s := S / H
  have hs : |s| ≤ Bω / H := by
    rw [abs_div, abs_of_pos hH0]
    exact div_le_div_of_nonneg_right hS hH0.le
  have hs_le_one : |s| ≤ 1 := by
    refine hs.trans ?_
    rw [div_le_one hH0]
    exact hBH
  set x : ℕ → ℝ := fun n => (ω n - s) * b n
  have hx_supp : ∀ n, n ∉ Icc 1 M → x n = 0 := fun n hn => by
    simp only [x, hb_zero n hn, mul_zero]
  have horth : ∑ n ∈ Icc 1 M, x n / Real.sqrt n = 0 := by
    have hpt : ∀ n ∈ Icc 1 M, x n / Real.sqrt n = ω n / n - s * (1 / n) :=
      fun n hn => by
        rw [show x n / Real.sqrt n = (ω n - s) * (b n / Real.sqrt n) by
          simp only [x]; ring, hbs n hn]
        ring
    rw [sum_congr rfl hpt, sum_sub_distrib, ← mul_sum]
    show S - s * H = 0
    rw [div_mul_cancel₀ S hH0.ne', sub_self]
  have hnx_le : ∀ n ∈ Icc 1 M, (n : ℝ) * x n ^ 2 ≤ 4 := fun n hn => by
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
    have habs : |ω n - s| ≤ 2 := by
      calc |ω n - s| ≤ |ω n| + |s| := abs_sub _ _
        _ ≤ 1 + 1 := by rw [abs_signTwin hsign (mem_Icc.mp hn).1]; linarith only [hs_le_one]
        _ = 2 := by norm_num
    have hsq4 : (ω n - s) ^ 2 ≤ 4 := by
      have h := pow_le_pow_left₀ (abs_nonneg _) habs 2
      rw [sq_abs] at h
      linarith only [h]
    dsimp only [x]
    rw [mul_pow, hb2 n hn]
    have hcancel : (n : ℝ) * ((ω n - s) ^ 2 * (1 / (n : ℝ))) =
        (ω n - s) ^ 2 := by field_simp [hn0.ne']
    linarith only [hcancel, hsq4]
  have hxsq : ∑ n ∈ Icc 1 M, x n ^ 2 = H - S ^ 2 / H := by
    have hpt : ∀ n ∈ Icc 1 M, x n ^ 2 = 1 / n - 2 * s * (ω n / n) + s ^ 2 * (1 / n) :=
      fun n hn => by
        have hl := signTwin_mul_self hsign (mem_Icc.mp hn).1
        dsimp only [x]
        rw [mul_pow, hb2 n hn]
        have : (ω n - s) ^ 2 = 1 - 2 * s * ω n + s ^ 2 := by
          linear_combination hl
        rw [this]
        ring
    rw [sum_congr rfl hpt, sum_add_distrib, sum_sub_distrib, ← mul_sum, ← mul_sum]
    dsimp only [s]
    field_simp [hH0.ne']
    ring
  have hS2H_le : S ^ 2 / H ≤ 2 := by
    rw [div_le_iff₀ hH0]
    linarith only [hS2, hB2H, hH3]
  have hx_ge_log : L - 2 ≤ ∑ n ∈ Icc 1 M, x n ^ 2 := by
    rw [hxsq]
    linarith only [hHL, hS2H_le]
  have hxpos : 0 < ∑ n ∈ Icc 1 M, x n ^ 2 := by
    linarith only [hx_ge_log, hL3]
  refine ⟨x, hx_supp, horth, hnx_le, hx_ge_log, hxpos, ?_⟩
  set u : ℕ → ℝ := fun n => -s * (ω n * b n)
  have hlx : (fun n => ω n * x n) = fun n => b n + u n := by
    funext n
    dsimp only [x, u]
    by_cases hn : n ∈ Icc 1 M
    · have hl := signTwin_mul_self hsign (mem_Icc.mp hn).1
      linear_combination b n * hl
    · rw [hb_zero n hn]; ring
  rw [hlx, atomicWeilForm_truncPole_add M u]
  have hPb : (L - γ - ε / 2) * H ≤ atomicWeilForm M b := by
    have := hM₁ M hMM₁
    rwa [hbsq] at this
  have hlb2 : ∑ n ∈ Icc 1 M, (ω n * b n) ^ 2 = H := by
    rw [← hbsq]
    exact sum_congr rfl fun n hn => by
      rw [mul_pow, show ω n ^ 2 = 1 by rw [sq, signTwin_mul_self hsign (mem_Icc.mp hn).1], one_mul]
  have hPu : -(s ^ 2 * ((L + C₀) * H)) ≤ atomicWeilForm M u := by
    have hu : u = fun n => (-s) * (ω n * b n) := rfl
    rw [hu, atomicWeilForm_smul, neg_sq]
    have hbot := fixedPoint_bottom_ge (κ := -1) (by norm_num) M (fun n => ω n * b n)
    rw [hlb2] at hbot
    have e : ((-1 : ℝ) - 1 / -1) = 0 := by norm_num
    rw [e, zero_mul, zero_add] at hbot
    have h1 : -((L + C₀) * H) ≤ atomicWeilForm M (fun n => ω n * b n) := by
      dsimp only [L, C₀] at hbot ⊢; linarith
    have h2 := mul_le_mul_of_nonneg_left h1 (sq_nonneg s)
    linarith only [h2]
  have hcross : |∑ n ∈ Icc 1 M,
        (RenormalizedArithmeticPotentialTheory.mertensSum (M / n) + Real.log n) * b n * u n| ≤
      |s| * ((L + γ) * Bω + Bm * H) := by
    have e : ∀ n ∈ Icc 1 M,
        (RenormalizedArithmeticPotentialTheory.mertensSum (M / n) + Real.log n) * b n * u n =
        -s * ((L - γ) * (ω n / n) +
          (RenormalizedArithmeticPotentialTheory.mertensSum (M / n) + Real.log n - (L - γ)) *
            (ω n * (1 / n))) := by
      intro n hn
      dsimp only [u]
      have hbb : b n * b n = 1 / n := by rw [← sq, hb2 n hn]
      have hr : (RenormalizedArithmeticPotentialTheory.mertensSum (M / n) + Real.log n) *
          b n * (-s * (ω n * b n)) =
          -s * ((RenormalizedArithmeticPotentialTheory.mertensSum (M / n) + Real.log n) *
            ω n * (b n * b n)) := by ring
      rw [hr, hbb]
      ring
    rw [sum_congr rfl e, ← mul_sum, abs_mul, abs_neg]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg s)
    rw [sum_add_distrib, ← mul_sum]
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [abs_mul]
      have : |L - γ| ≤ L + γ := by rw [abs_le]; constructor <;> linarith
      exact mul_le_mul this hS (abs_nonneg _) (by linarith)
    · refine (abs_sum_le_sum_abs _ _).trans ?_
      rw [show Bm * H = ∑ n ∈ Icc 1 M, Bm * (1 / (n : ℝ)) by rw [← mul_sum]]
      refine sum_le_sum fun n hn => ?_
      have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
      rw [abs_mul, abs_mul, abs_signTwin hsign (mem_Icc.mp hn).1, one_mul,
        abs_of_pos (by positivity : (0 : ℝ) < 1 / n)]
      exact mul_le_mul_of_nonneg_right (abs_row_sub_le hn) (by positivity)
  have hs2 : s ^ 2 ≤ Bω ^ 2 / H ^ 2 := by
    rw [div_pow]
    exact div_le_div_of_nonneg_right hS2 (by positivity)
  have hLH : L / H ≤ 1 := by rw [div_le_one hH0]; exact hHL
  have hT1 : s ^ 2 * ((L + C₀) * H) ≤ Bω ^ 2 + Bω ^ 2 * C₀ := by
    calc s ^ 2 * ((L + C₀) * H) ≤ Bω ^ 2 / H ^ 2 * ((L + C₀) * H) :=
          mul_le_mul_of_nonneg_right hs2 (by positivity)
      _ = Bω ^ 2 * (L / H) + Bω ^ 2 * C₀ / H := by field_simp [hH0.ne']
      _ ≤ Bω ^ 2 + Bω ^ 2 * C₀ := by
          have h1 : Bω ^ 2 * (L / H) ≤ Bω ^ 2 := mul_le_of_le_one_right (sq_nonneg _) hLH
          have h2 : Bω ^ 2 * C₀ / H ≤ Bω ^ 2 * C₀ := div_le_self (by positivity) (by linarith)
          linarith
  have hT2 : 2 * (|s| * ((L + γ) * Bω + Bm * H)) ≤
      2 * Bω ^ 2 + 2 * Bω ^ 2 * γ + 2 * Bω * Bm := by
    calc 2 * (|s| * ((L + γ) * Bω + Bm * H)) ≤ 2 * (Bω / H * ((L + γ) * Bω + Bm * H)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hs (by positivity)) (by norm_num)
      _ = 2 * Bω ^ 2 * (L / H) + 2 * Bω ^ 2 * γ / H + 2 * Bω * Bm := by
          field_simp [hH0.ne']
      _ ≤ 2 * Bω ^ 2 + 2 * Bω ^ 2 * γ + 2 * Bω * Bm := by
          have h1 : 2 * Bω ^ 2 * (L / H) ≤ 2 * Bω ^ 2 :=
            mul_le_of_le_one_right (by positivity) hLH
          have h2 : 2 * Bω ^ 2 * γ / H ≤ 2 * Bω ^ 2 * γ := div_le_self (by positivity) (by linarith)
          linarith
  have hεH : K ≤ ε / 2 * H := by
    have : 2 * K / ε ≤ H := hLK.trans hHL
    rw [div_le_iff₀ hε] at this
    linarith
  have hxH : ∑ n ∈ Icc 1 M, x n ^ 2 ≤ H := by
    rw [hxsq]
    have : 0 ≤ S ^ 2 / H := div_nonneg (sq_nonneg _) hH0.le
    linarith
  have hcoef : 0 ≤ L - γ - ε := by linarith
  have hcr := (abs_le.mp hcross).1
  calc (L - γ - ε) * ∑ n ∈ Icc 1 M, x n ^ 2 ≤ (L - γ - ε) * H :=
        mul_le_mul_of_nonneg_left hxH hcoef
    _ ≤ atomicWeilForm M b + atomicWeilForm M u +
        2 * ∑ n ∈ Icc 1 M,
          (RenormalizedArithmeticPotentialTheory.mertensSum (M / n) + Real.log n) * b n * u n := by
        linarith

/-! ### The sub-horizon bound and the breakdown -/

private theorem integral_levyMixed_atom_self (g : ℝ → ℝ) (n : ℕ) :
    (∫ y in Set.Ioi 0, levyMixed (atom g n) (atom g n) y) = levyEnergy g := by
  unfold levyEnergy levyMixed atom
  refine setIntegral_congr_fun measurableSet_Ioi fun y _ => ?_
  congr 1
  rw [← integral_sub_right_eq_self (fun u => (g u - g (u + y)) ^ 2) (Real.log n)]
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  dsimp only
  rw [sq, show u - Real.log n + y = u + y - Real.log n by ring]

private theorem atomicTest_eq_of_le {M N : ℕ} (hMN : M ≤ N) {x : ℕ → ℝ}
    (hx : ∀ n, n ∉ Icc 1 M → x n = 0) (g : ℝ → ℝ) :
    atomicTest N x g = atomicTest M x g := by
  funext u
  rw [atomicTest_eq_sum_atom, atomicTest_eq_sum_atom]
  refine (sum_subset (Icc_subset_Icc_right hMN) ?_).symm
  intro n _ hnM
  rw [hx n hnM, zero_mul]

include hω hsign in
/-- Pointwise upper bound on a sign twin's complete Weil form on a sub-horizon harmonic
hyperplane witness with `n x_n² ≤ 4`. -/
theorem signTwin_weilQuadTw_subhorizon_le {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hφ0 : 0 < ∫ u, φ u ^ 2) {K_lip : ℝ}
    (hLip : ∀ u v, |φ u - φ v| ≤ K_lip * |u - v|)
    {M N : ℕ} (hM1 : 1 ≤ M) (hMN : M ≤ N) {w c₀ : ℝ}
    (hw0 : 0 < w) (hw1 : w ≤ 1) (hc0 : 0 ≤ c₀) (hc1 : c₀ < 1)
    (hw_c0 : w ≤ c₀ / (M : ℝ)) (hw_sp : w < atomSpacing M)
    {x : ℕ → ℝ} (hx_supp : ∀ n, n ∉ Icc 1 M → x n = 0)
    (horth : ∑ n ∈ Icc 1 M, x n / Real.sqrt n = 0)
    (hnx : ∀ n ∈ Icc 1 M, (n : ℝ) * x n ^ 2 ≤ 4)
    {ε : ℝ} (hprime : (Real.log M - Real.eulerMascheroniConstant - ε) *
        (∑ n ∈ Icc 1 M, x n ^ 2) ≤ atomicWeilForm M (fun n => ω n * x n)) :
    weilQuadTw (fun n => ω n * ArithmeticFunction.vonMangoldt n)
        (atomicTest N x (atomDilate φ w)) ≤
      (∫ u, atomDilate φ w u ^ 2) *
        ((Real.log (1 / (2 * Real.pi * (w * M))) +
            bumpRobin φ 1 / (∫ u, φ u ^ 2) + ε + Real.exp (1 / 2) / 2 * w) *
          (∑ n ∈ Icc 1 M, x n ^ 2) +
          17 * ((∫ u, φ u) ^ 2 / ∫ u, φ u ^ 2) * (w * M) +
          56 * (38 * (∫ u, |φ u|) ^ 2 / ((∫ u, φ u ^ 2) * (1 - c₀) ^ 2)) * (w * M) ^ 2) := by
  set g := atomDilate φ w
  obtain ⟨hgc2, hgsupp, hgc⟩ := atomDilate_facts hφ hφsupp hw0
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM1
  have hG : 0 < ∫ u, g u ^ 2 := by
    rw [integral_atomDilate_sq hw0]; exact mul_pos hw0 hφ0
  rw [atomicTest_eq_of_le hMN hx_supp g]
  have hf := contDiff_atomicTest hgc2 M x
  have hfc := hasCompactSupport_atomicTest hgsupp M x
  rw [weilQuadTw_eq_twinMarkov_add_pole ω hf hfc,
    integral_atomicTest_mul_exp_neg_half hgc2.continuous hgsupp M x]
  simp only [horth, zero_mul, mul_zero, add_zero]
  rw [archForm_eq_levyEnergy hf hfc,
    integral_atomicTest_sq hgc2 hgc hgsupp hw_sp x,
    (twistedPrimeSum_atomicTest hω hsign hgc2 hgc hgsupp hw_sp x).2,
    twistedAtomicWeilForm_eq hω hsign M x]
  -- Self-energy and off-diagonal decomposition of `levyEnergy`
  have hlevy_eq : levyEnergy (atomicTest M x g) =
      (∑ n ∈ Icc 1 M, x n ^ 2) * levyEnergy g -
        (∫ u, g u ^ 2) *
          (((∫ u, g u) ^ 2 / ∫ u, g u ^ 2) *
              (∑ n ∈ Icc 1 M, ∑ j ∈ Icc 1 M, x n * x j * archimedeanCenterKernel n j) +
            ∑ n ∈ Icc 1 M, ∑ j ∈ Icc 1 M, x n * x j * atomCrossErrorKernel g n j) := by
    rw [levyEnergy_atomicTest_eq_sum hgc2 hgsupp M x]
    have hdiag_split :
        (∑ n ∈ Icc 1 M, ∑ j ∈ Icc 1 M,
            x n * x j * ∫ y in Set.Ioi 0, levyMixed (atom g n) (atom g j) y) =
          (∑ n ∈ Icc 1 M, x n ^ 2) * levyEnergy g +
            ∑ n ∈ Icc 1 M, ∑ j ∈ Icc 1 M,
              if n = j then 0
              else x n * x j * (-atomCrossTerm g |Real.log j - Real.log n|) := by
      rw [sum_mul, ← sum_add_distrib]
      refine sum_congr rfl fun n hn => ?_
      rw [sum_eq_diag_add hn, integral_levyMixed_atom_self]
      congr 1
      · ring
      · refine sum_congr rfl fun j hj => ?_
        split_ifs with hnj
        · rfl
        · have hgap := atomSpacing_le_abs_logGap hn hj hnj
          simp only [SpacingScaleHarmonicAnalysis.logGap] at hgap
          rw [integral_levyMixed_atom_of_lt_abs_log hgsupp
            (mem_Icc.mp hn).1 (mem_Icc.mp hj).1 hw0.le (hw_sp.trans_le hgap)]
    rw [hdiag_split]
    have hoff_eq :
        (∑ n ∈ Icc 1 M, ∑ j ∈ Icc 1 M,
            if n = j then 0 else x n * x j * (-atomCrossTerm g |Real.log j - Real.log n|)) =
          -(∫ u, g u ^ 2) *
            (((∫ u, g u) ^ 2 / ∫ u, g u ^ 2) *
                (∑ n ∈ Icc 1 M, ∑ j ∈ Icc 1 M, x n * x j * archimedeanCenterKernel n j) +
              ∑ n ∈ Icc 1 M, ∑ j ∈ Icc 1 M, x n * x j * atomCrossErrorKernel g n j) := by
      rw [mul_add, ← mul_assoc, mul_sum, mul_sum, ← sum_add_distrib]
      refine sum_congr rfl fun n _ => ?_
      rw [mul_sum, mul_sum, ← sum_add_distrib]
      refine sum_congr rfl fun j _ => ?_
      by_cases hnj : n = j
      · subst hnj
        simp [archimedeanCenterKernel_self, atomCrossErrorKernel_self]
      · rw [if_neg hnj, atomCrossErrorKernel, if_neg hnj]
        field_simp [hG.ne']
        ring
    rw [hoff_eq]
    ring
  rw [hlevy_eq]
  -- Bound the four pieces
  have hself := abs_levyEnergy_atomDilate_sub_le hφ hφsupp hφ0 hw0 hw1 hLip
  have hself_up : levyEnergy g ≤
      (Real.log (1 / w) + profileRobin φ + Real.exp (1 / 2) / 2 * w) * ∫ u, g u ^ 2 := by
    have := (abs_le.mp hself).2
    dsimp only [g]
    linarith
  have hX_nn : 0 ≤ ∑ n ∈ Icc 1 M, x n ^ 2 := sum_nonneg fun n _ => sq_nonneg _
  have hdiag_up : 2 * gammaHardyPhaseRate 0 * ((∑ n ∈ Icc 1 M, x n ^ 2) * ∫ u, g u ^ 2) +
        (∑ n ∈ Icc 1 M, x n ^ 2) * levyEnergy g -
        (∫ u, g u ^ 2) * atomicWeilForm M (fun n => ω n * x n) ≤
      (∫ u, g u ^ 2) *
        ((Real.log (1 / (2 * Real.pi * (w * M))) + bumpRobin φ 1 / (∫ u, φ u ^ 2) + ε +
            Real.exp (1 / 2) / 2 * w) * ∑ n ∈ Icc 1 M, x n ^ 2) := by
    have h1 := mul_le_mul_of_nonneg_left hself_up hX_nn
    have h2 := mul_le_mul_of_nonneg_left hprime hG.le
    have hfp := finitePart_profileRobin_eq φ
    have hlog_eq : Real.log (1 / (2 * Real.pi * (w * M))) =
        Real.log (1 / w) - Real.log M - Real.log (2 * Real.pi) := by
      rw [one_div, Real.log_inv, Real.log_mul (by positivity) (by positivity),
        Real.log_mul hw0.ne' hM0.ne', one_div, Real.log_inv]
      ring
    calc 2 * gammaHardyPhaseRate 0 * ((∑ n ∈ Icc 1 M, x n ^ 2) * ∫ u, g u ^ 2) +
            (∑ n ∈ Icc 1 M, x n ^ 2) * levyEnergy g -
            (∫ u, g u ^ 2) * atomicWeilForm M (fun n => ω n * x n)
        ≤ 2 * gammaHardyPhaseRate 0 * ((∑ n ∈ Icc 1 M, x n ^ 2) * ∫ u, g u ^ 2) +
            (∑ n ∈ Icc 1 M, x n ^ 2) *
              ((Real.log (1 / w) + profileRobin φ + Real.exp (1 / 2) / 2 * w) * ∫ u, g u ^ 2) -
            (∫ u, g u ^ 2) *
              ((Real.log M - Real.eulerMascheroniConstant - ε) * ∑ n ∈ Icc 1 M, x n ^ 2) := by
          linarith only [h1, h2]
      _ = (∫ u, g u ^ 2) *
            (((2 * gammaHardyPhaseRate 0 + profileRobin φ + Real.eulerMascheroniConstant) +
                Real.log (1 / w) - Real.log M + ε + Real.exp (1 / 2) / 2 * w) *
              ∑ n ∈ Icc 1 M, x n ^ 2) := by ring
      _ = (∫ u, g u ^ 2) *
            ((Real.log (1 / (2 * Real.pi * (w * M))) + bumpRobin φ 1 / (∫ u, φ u ^ 2) + ε +
                Real.exp (1 / 2) / 2 * w) * ∑ n ∈ Icc 1 M, x n ^ 2) := by
          rw [hfp, hlog_eq]
          ring
  -- Center kernel bound
  have hcenter_ge := sum_archimedeanCenterKernel_ge M x
  have hsum_nx : ∑ n ∈ Icc 1 M, (n : ℝ) * x n ^ 2 ≤ 4 * M := by
    calc ∑ n ∈ Icc 1 M, (n : ℝ) * x n ^ 2 ≤ ∑ _n ∈ Icc 1 M, (4 : ℝ) := sum_le_sum hnx
      _ = 4 * M := by rw [sum_const, Nat.card_Icc, Nat.add_sub_cancel_right, nsmul_eq_mul]; ring
  have hint_g_eq : ∫ u, g u = w * ∫ u, φ u := by
    have h := MeasureTheory.Measure.integral_comp_div φ w
    simpa only [g, atomDilate, smul_eq_mul, abs_of_pos hw0] using h
  have hratio_g : (∫ u, g u) ^ 2 / (∫ u, g u ^ 2) = w * ((∫ u, φ u) ^ 2 / ∫ u, φ u ^ 2) := by
    rw [hint_g_eq, integral_atomDilate_sq hw0]
    field_simp [hw0.ne', hφ0.ne']
  have hcenter_up : -(((∫ u, g u) ^ 2 / ∫ u, g u ^ 2) *
        ∑ n ∈ Icc 1 M, ∑ j ∈ Icc 1 M, x n * x j * archimedeanCenterKernel n j) ≤
      17 * ((∫ u, φ u) ^ 2 / ∫ u, φ u ^ 2) * (w * M) := by
    have hq_nn : 0 ≤ (∫ u, g u) ^ 2 / ∫ u, g u ^ 2 := div_nonneg (sq_nonneg _) hG.le
    have h1 : -(∑ n ∈ Icc 1 M, ∑ j ∈ Icc 1 M, x n * x j * archimedeanCenterKernel n j) ≤
        17 * (M : ℝ) := by linarith only [hcenter_ge, hsum_nx]
    calc -(((∫ u, g u) ^ 2 / ∫ u, g u ^ 2) *
            ∑ n ∈ Icc 1 M, ∑ j ∈ Icc 1 M, x n * x j * archimedeanCenterKernel n j)
        = ((∫ u, g u) ^ 2 / ∫ u, g u ^ 2) *
            (-(∑ n ∈ Icc 1 M, ∑ j ∈ Icc 1 M, x n * x j * archimedeanCenterKernel n j)) := by ring
      _ ≤ ((∫ u, g u) ^ 2 / ∫ u, g u ^ 2) * (17 * (M : ℝ)) :=
          mul_le_mul_of_nonneg_left h1 hq_nn
      _ = 17 * ((∫ u, φ u) ^ 2 / ∫ u, φ u ^ 2) * (w * M) := by rw [hratio_g]; ring
  -- Cross-error bound
  set K₀ : ℝ := 38 * (∫ u, |φ u|) ^ 2 / ((∫ u, φ u ^ 2) * (1 - c₀) ^ 2)
  have hK0_nn : 0 ≤ K₀ := by
    dsimp only [K₀]; positivity
  have herr_up : -(∑ n ∈ Icc 1 M, ∑ j ∈ Icc 1 M, x n * x j * atomCrossErrorKernel g n j) ≤
      56 * K₀ * (w * M) ^ 2 := by
    have habs : |∑ n ∈ Icc 1 M, ∑ j ∈ Icc 1 M, x n * x j * atomCrossErrorKernel g n j| ≤
        K₀ * w ^ 2 *
          ∑ n ∈ Icc 1 M, ∑ j ∈ Icc 1 M,
            if n = j then 0 else |x n| * |x j| * (max (n : ℝ) j) ^ 2 / |(n : ℝ) - j| ^ 2 := by
      refine (abs_sum_le_sum_abs _ _).trans ?_
      rw [mul_sum]
      refine sum_le_sum fun n hn => ?_
      refine (abs_sum_le_sum_abs _ _).trans ?_
      rw [mul_sum]
      refine sum_le_sum fun j hj => ?_
      by_cases hnj : n = j
      · subst hnj; simp [atomCrossErrorKernel_self]
      · rw [if_neg hnj, abs_mul, abs_mul]
        have hk := abs_atomCrossErrorKernel_atomDilate_le hφ hφsupp hφ0 hw0 hc0 hc1 hw_c0 hn hj
        calc |x n| * |x j| * |atomCrossErrorKernel g n j|
            ≤ |x n| * |x j| * (K₀ * w ^ 2 * (max (n : ℝ) j) ^ 2 / |(n : ℝ) - j| ^ 2) :=
              mul_le_mul_of_nonneg_left hk (mul_nonneg (abs_nonneg _) (abs_nonneg _))
          _ = K₀ * w ^ 2 * (|x n| * |x j| * (max (n : ℝ) j) ^ 2 / |(n : ℝ) - j| ^ 2) := by ring
    have hsum56 := sum_cross_error_bounded_pole_le hnx
    have htot : |∑ n ∈ Icc 1 M, ∑ j ∈ Icc 1 M, x n * x j * atomCrossErrorKernel g n j| ≤
        56 * K₀ * (w * M) ^ 2 := by
      calc |∑ n ∈ Icc 1 M, ∑ j ∈ Icc 1 M, x n * x j * atomCrossErrorKernel g n j|
          ≤ K₀ * w ^ 2 *
              ∑ n ∈ Icc 1 M, ∑ j ∈ Icc 1 M,
                if n = j then 0 else |x n| * |x j| * (max (n : ℝ) j) ^ 2 / |(n : ℝ) - j| ^ 2 :=
            habs
        _ ≤ K₀ * w ^ 2 * (56 * (M : ℝ) ^ 2) :=
            mul_le_mul_of_nonneg_left hsum56 (by positivity)
        _ = 56 * K₀ * (w * M) ^ 2 := by ring
    have hneg := neg_abs_le (∑ n ∈ Icc 1 M, ∑ j ∈ Icc 1 M, x n * x j * atomCrossErrorKernel g n j)
    linarith only [htot, hneg]
  have hcomb := mul_le_mul_of_nonneg_left (add_le_add hcenter_up herr_up) hG.le
  linarith only [hdiag_up, hcomb]

include hω hsign hB in
/-- **Breakdown of every pole-free sign twin above the Robin–Euler ratio**: for a completely
multiplicative sign `ω` with bounded harmonic sums, every `C²` profile `φ` on `[0, 1]` with
`robinEulerThreshold φ < 1` and every fixed `c > robinEulerThreshold φ`, eventually in `N` the
twin's complete Weil form is strictly negative on some atomic test of width `w_N` whenever
`w_N N → c`. -/
theorem eventually_signTwin_weilQuadTw_neg_of_gt_robinEuler {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hφ0 : 0 < ∫ u, φ u ^ 2) (hRE1 : robinEulerThreshold φ < 1)
    {c : ℝ} (hc : robinEulerThreshold φ < c)
    {w : ℕ → ℝ} (hw_pos : ∀ᶠ N in atTop, 0 < w N)
    (hw_lim : Tendsto (fun N : ℕ => w N * (N : ℝ)) atTop (𝓝 c)) :
    ∀ᶠ N : ℕ in atTop, ∃ x : ℕ → ℝ,
      weilQuadTw (fun n => ω n * ArithmeticFunction.vonMangoldt n)
        (atomicTest N x (atomDilate φ (w N))) < 0 := by
  have hφc : HasCompactSupport φ := HasCompactSupport.intro isCompact_Icc fun u hu => hφsupp u hu
  obtain ⟨K_lip, hC_lip⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hφc hφ (by norm_num)
  have hLip : ∀ u v, |φ u - φ v| ≤ (K_lip : ℝ) * |u - v| := fun u v => by
    simpa [Real.dist_eq] using hC_lip.dist_le_mul u v
  have hRE_pos : 0 < robinEulerThreshold φ := robinEulerThreshold_pos φ
  have hc_pos : 0 < c := hRE_pos.trans hc
  -- Sub-horizon target overlap ratio `c' ∈ (robinEulerThreshold φ, 1)` with `c' ≤ c`
  set c' : ℝ := min c ((robinEulerThreshold φ + 1) / 2)
  have hc'_gt : robinEulerThreshold φ < c' := lt_min hc (by linarith only [hRE1])
  have hc'_lt1 : c' < 1 := (min_le_right _ _).trans_lt (by linarith only [hRE1])
  have hc'_pos : 0 < c' := hRE_pos.trans hc'_gt
  have hc'_le_c : c' ≤ c := min_le_left _ _
  set θ : ℝ := c' / c
  have hθ_pos : 0 < θ := div_pos hc'_pos hc_pos
  have hθ_le1 : θ ≤ 1 := (div_le_one hc_pos).mpr hc'_le_c
  set c₀ : ℝ := (c' + 1) / 2
  have hc₀_gt : c' < c₀ := by dsimp only [c₀]; linarith only [hc'_lt1]
  have hc₀_lt1 : c₀ < 1 := by dsimp only [c₀]; linarith only [hc'_lt1]
  have hc₀_nn : 0 ≤ c₀ := by linarith only [hc'_pos, hc₀_gt]
  -- Logarithmic margin `μ = log (c' / c_RE(φ)) > 0`
  set μ : ℝ := Real.log (c' / robinEulerThreshold φ)
  have hμ_pos : 0 < μ := Real.log_pos ((one_lt_div hRE_pos).mpr hc'_gt)
  obtain ⟨M₀, hM₀1, hwit⟩ := exists_bounded_hyperplane_signTwin_witness hsign hB (ε := μ / 4) (by positivity)
  -- Sub-horizon window `M N = ⌊θ * N⌋₊`
  set M : ℕ → ℕ := fun N => ⌊θ * (N : ℝ)⌋₊
  have hM_tendsto : Tendsto M atTop atTop := by
    refine tendsto_atTop.mpr fun B => ?_
    filter_upwards [eventually_ge_atTop (⌈((B : ℝ) + 1) / θ⌉₊)] with N hN
    have h1 : ((B : ℝ) + 1) / θ ≤ N := (Nat.le_ceil _).trans (by exact_mod_cast hN)
    have h2 : (B : ℝ) ≤ θ * (N : ℝ) := by
      have := (div_le_iff₀ hθ_pos).mp h1
      linarith only [this]
    exact Nat.le_floor h2
  have hMN_ratio : Tendsto (fun N : ℕ => (M N : ℝ) / (N : ℝ)) atTop (𝓝 θ) := by
    have h1 : Tendsto (fun N : ℕ => (1 : ℝ) / (N : ℝ)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
    have hlow : Tendsto (fun N : ℕ => θ - 1 / (N : ℝ)) atTop (𝓝 θ) := by
      simpa using tendsto_const_nhds.sub h1
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
    · filter_upwards [eventually_ge_atTop 1] with N hN
      have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
      have hfl : θ * (N : ℝ) - 1 ≤ (M N : ℝ) := (Nat.sub_one_lt_floor _).le
      rw [le_div_iff₀ hN0, sub_mul, div_mul_cancel₀ _ hN0.ne']
      exact hfl
    · filter_upwards [eventually_ge_atTop 1] with N hN
      have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
      rw [div_le_iff₀ hN0]
      exact Nat.floor_le (by positivity)
  have hwM_lim : Tendsto (fun N : ℕ => w N * (M N : ℝ)) atTop (𝓝 c') := by
    have hprod := hw_lim.mul hMN_ratio
    have hcθ : c * θ = c' := mul_div_cancel₀ c' hc_pos.ne'
    rw [hcθ] at hprod
    refine hprod.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
    field_simp [hN0]
  have hw_zero : Tendsto w atTop (𝓝 0) := by
    have hinv : Tendsto (fun N : ℕ => (1 : ℝ) / (N : ℝ)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
    have hp := hw_lim.mul hinv
    rw [mul_zero] at hp
    refine hp.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
    field_simp [hN0]
  -- Continuity of the leading coefficient as `w N * M N → c'` and `w N → 0`
  have hcoef_lim : Tendsto (fun N : ℕ =>
      Real.log (1 / (2 * Real.pi * (w N * (M N : ℝ)))) +
        bumpRobin φ 1 / (∫ u, φ u ^ 2) + μ / 4 + Real.exp (1 / 2) / 2 * w N)
      atTop (𝓝 (-(3 * μ / 4))) := by
    have hdenom : Tendsto (fun N : ℕ => 2 * Real.pi * (w N * (M N : ℝ))) atTop
        (𝓝 (2 * Real.pi * c')) := hwM_lim.const_mul (2 * Real.pi)
    have hinv_d : Tendsto (fun N : ℕ => 1 / (2 * Real.pi * (w N * (M N : ℝ)))) atTop
        (𝓝 (1 / (2 * Real.pi * c'))) :=
      tendsto_const_nhds.div hdenom (by positivity)
    have hlog_t := (Real.continuousAt_log (by positivity)).tendsto.comp hinv_d
    have htot := ((hlog_t.add_const (bumpRobin φ 1 / ∫ u, φ u ^ 2)).add_const (μ / 4)).add
      (hw_zero.const_mul (Real.exp (1 / 2) / 2))
    have hval : Real.log (1 / (2 * Real.pi * c')) + bumpRobin φ 1 / (∫ u, φ u ^ 2) +
        μ / 4 + Real.exp (1 / 2) / 2 * 0 = -(3 * μ / 4) := by
      have hRE_eq : Real.log (robinEulerThreshold φ) =
          bumpRobin φ 1 / (∫ u, φ u ^ 2) - Real.log (2 * Real.pi) := by
        unfold robinEulerThreshold
        rw [Real.log_div (Real.exp_pos _).ne' (by positivity), Real.log_exp]
      have hlog1 : Real.log (1 / (2 * Real.pi * c')) =
          -Real.log (2 * Real.pi) - Real.log c' := by
        rw [one_div, Real.log_inv, Real.log_mul (by positivity) hc'_pos.ne']
        ring
      have hμ_eq : μ = Real.log c' - Real.log (robinEulerThreshold φ) :=
        Real.log_div hc'_pos.ne' hRE_pos.ne'
      linarith only [hRE_eq, hlog1, hμ_eq]
    rwa [hval] at htot
  -- Uniform bound `C_err` on the `O(1)` archimedean center + cross-error terms
  set K₀ : ℝ := 38 * (∫ u, |φ u|) ^ 2 / ((∫ u, φ u ^ 2) * (1 - c₀) ^ 2)
  set C_err : ℝ := 17 * ((∫ u, φ u) ^ 2 / ∫ u, φ u ^ 2) * 1 + 56 * K₀ * 1 ^ 2
  have hlogM_atTop : Tendsto (fun N : ℕ => Real.log (M N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp hM_tendsto)
  filter_upwards [hw_pos,
    hw_zero.eventually (gt_mem_nhds zero_lt_one),
    hM_tendsto.eventually_ge_atTop M₀,
    (tendsto_natCast_atTop_atTop.comp hM_tendsto).eventually_gt_atTop (c₀ / (1 - c₀)),
    hwM_lim.eventually (gt_mem_nhds hc₀_gt),
    hcoef_lim.eventually (gt_mem_nhds (show -(3 * μ / 4) < -(μ / 2) by linarith only [hμ_pos])),
    hlogM_atTop.eventually_gt_atTop (2 + 2 * (C_err + 1) / μ)]
    with N hw0 hw1 hMM₀ hM_sp hwM_c₀ hcoef_neg hlogM_big
  simp only [Function.comp] at hM_sp hlogM_big
  have hM1 : 1 ≤ M N := hM₀1.trans hMM₀
  have hM0 : (0 : ℝ) < M N := by exact_mod_cast hM1
  have hMN : M N ≤ N := by
    have hle : θ * (N : ℝ) ≤ (N : ℝ) := by
      have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
      nlinarith only [hθ_le1, hN0]
    exact Nat.floor_le_of_le hle
  have hw_c0 : w N ≤ c₀ / (M N : ℝ) := (le_div_iff₀ hM0).mpr hwM_c₀.le
  have hw_sp : w N < atomSpacing (M N) := by
    have hsp := (atomSpacing_bounds hM1).1
    have hlt : c₀ / (M N : ℝ) < 1 / ((M N : ℝ) + 1) := by
      rw [div_lt_div_iff₀ hM0 (by positivity)]
      have hsub_pos : 0 < 1 - c₀ := sub_pos.mpr hc₀_lt1
      have h1 := (div_lt_iff₀ hsub_pos).mp hM_sp
      nlinarith only [h1]
    exact (hw_c0.trans_lt hlt).trans_le hsp
  obtain ⟨x, hx_supp, horth, hnx, hx_log, hx_pos, hprime⟩ := hwit (M N) hMM₀
  refine ⟨x, ?_⟩
  have hup := signTwin_weilQuadTw_subhorizon_le hω hsign hφ hφsupp hφ0 hLip hM1 hMN hw0 hw1.le hc₀_nn
    hc₀_lt1 hw_c0 hw_sp hx_supp horth hnx hprime
  have hG_pos : 0 < ∫ u, atomDilate φ (w N) u ^ 2 := by
    rw [integral_atomDilate_sq hw0]; exact mul_pos hw0 hφ0
  have hwM_le1 : w N * (M N : ℝ) ≤ 1 := hwM_c₀.le.trans hc₀_lt1.le
  have hwM_nn : 0 ≤ w N * (M N : ℝ) := by positivity
  have hK0_nn : 0 ≤ K₀ := by dsimp only [K₀]; positivity
  have herr_le : 17 * ((∫ u, φ u) ^ 2 / ∫ u, φ u ^ 2) * (w N * (M N : ℝ)) +
      56 * K₀ * (w N * (M N : ℝ)) ^ 2 ≤ C_err := by
    dsimp only [C_err]
    have hq_nn : 0 ≤ (∫ u, φ u) ^ 2 / ∫ u, φ u ^ 2 := div_nonneg (sq_nonneg _) hφ0.le
    have hsq1 : (w N * (M N : ℝ)) ^ 2 ≤ 1 ^ 2 := pow_le_pow_left₀ hwM_nn hwM_le1 2
    nlinarith only [hwM_le1, hq_nn, hK0_nn, hsq1]
  have hlead_le : (Real.log (1 / (2 * Real.pi * (w N * (M N : ℝ)))) +
        bumpRobin φ 1 / (∫ u, φ u ^ 2) + μ / 4 + Real.exp (1 / 2) / 2 * w N) *
      (∑ n ∈ Icc 1 (M N), x n ^ 2) ≤ -(μ / 2) * (Real.log (M N : ℝ) - 2) := by
    have h1 := mul_le_mul_of_nonneg_right hcoef_neg.le hx_pos.le
    have h2 : -(μ / 2) * (∑ n ∈ Icc 1 (M N), x n ^ 2) ≤ -(μ / 2) * (Real.log (M N : ℝ) - 2) := by
      nlinarith only [hμ_pos, hx_log]
    linarith only [h1, h2]
  have hbracket_neg :
      (Real.log (1 / (2 * Real.pi * (w N * (M N : ℝ)))) +
          bumpRobin φ 1 / (∫ u, φ u ^ 2) + μ / 4 + Real.exp (1 / 2) / 2 * w N) *
        (∑ n ∈ Icc 1 (M N), x n ^ 2) +
        17 * ((∫ u, φ u) ^ 2 / ∫ u, φ u ^ 2) * (w N * (M N : ℝ)) +
        56 * K₀ * (w N * (M N : ℝ)) ^ 2 < 0 := by
    have hbig : C_err + 1 < (μ / 2) * (Real.log (M N : ℝ) - 2) := by
      have h := (div_lt_iff₀ hμ_pos).mp (show 2 * (C_err + 1) / μ < Real.log (M N : ℝ) - 2 by
        linarith only [hlogM_big])
      linarith only [h]
    linarith only [hlead_le, herr_le, hbig]
  have hprod_neg := mul_neg_of_pos_of_neg hG_pos hbracket_neg
  exact hup.trans_lt hprod_neg

end SignTwin

/-! ### Sign gauges and cofinite flips -/

section Gauge

open ArithmeticCountingPositivity

variable {ε : ℕ → ℝ}

/-- A sign gauge as an arithmetic function (vanishing at `0`). -/
def signGaugeTwin (ε : ℕ → ℝ) : ArithmeticFunction ℝ := ⟨fun n => if n = 0 then 0 else ε n, rfl⟩

theorem signGaugeTwin_apply {n : ℕ} (hn : n ≠ 0) : signGaugeTwin ε n = ε n := if_neg hn

theorem signGaugeTwin_mul (hε : IsSignGauge ε) (a b : ℕ) :
    signGaugeTwin ε (a * b) = signGaugeTwin ε a * signGaugeTwin ε b := by
  rcases eq_or_ne a 0 with rfl | ha
  · simp [signGaugeTwin]
  rcases eq_or_ne b 0 with rfl | hb
  · simp [signGaugeTwin]
  rw [signGaugeTwin_apply (mul_ne_zero ha hb), signGaugeTwin_apply ha, signGaugeTwin_apply hb,
    hε.mul ha hb]

theorem signGaugeTwin_sign (hε : IsSignGauge ε) (n : ℕ) (hn : 0 < n) :
    signGaugeTwin ε n = 1 ∨ signGaugeTwin ε n = -1 := by
  rw [signGaugeTwin_apply hn.ne']
  exact mul_self_eq_one_iff.mp (hε.mul_self hn.ne')

theorem weilQuadTw_signGaugeTwin (ε : ℕ → ℝ) (f : ℝ → ℝ) :
    weilQuadTw (fun n => signGaugeTwin ε n * ArithmeticFunction.vonMangoldt n) f =
      weilQuadTw (fun n => ε n * ArithmeticFunction.vonMangoldt n) f := by
  congr 1
  funext n
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · rw [signGaugeTwin_apply hn]

/-- **Every pole-free sign gauge breaks above the Robin–Euler ratio.** -/
theorem eventually_signGauge_weilQuadTw_neg_of_gt_robinEuler (hε : IsSignGauge ε) {B : ℝ}
    (hB : ∀ M : ℕ, |gaugeHarmonicSum ε M| ≤ B) {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hφ0 : 0 < ∫ u, φ u ^ 2) (hRE1 : robinEulerThreshold φ < 1)
    {c : ℝ} (hc : robinEulerThreshold φ < c)
    {w : ℕ → ℝ} (hw_pos : ∀ᶠ N in atTop, 0 < w N)
    (hw_lim : Tendsto (fun N : ℕ => w N * (N : ℝ)) atTop (𝓝 c)) :
    ∀ᶠ N : ℕ in atTop, ∃ x : ℕ → ℝ,
      weilQuadTw (fun n => ε n * ArithmeticFunction.vonMangoldt n)
        (atomicTest N x (atomDilate φ (w N))) < 0 := by
  have hBt : ∀ M : ℕ, |∑ n ∈ Icc 1 M, signGaugeTwin ε n / n| ≤ B := fun M => by
    have : ∑ n ∈ Icc 1 M, signGaugeTwin ε n / n = gaugeHarmonicSum ε M :=
      sum_congr rfl fun n hn => by
        rw [signGaugeTwin_apply (by have := (mem_Icc.mp hn).1; omega)]
    rw [this]; exact hB M
  have h := eventually_signTwin_weilQuadTw_neg_of_gt_robinEuler (signGaugeTwin_mul hε)
    (signGaugeTwin_sign hε) hBt hφ hφsupp hφ0 hRE1 hc hw_pos hw_lim
  simpa only [weilQuadTw_signGaugeTwin] using h

/-- **Every cofinite flip breaks above the Robin–Euler ratio**: flipping every prime outside a
finite set `F` (the Liouville twin is `F = ∅`) leaves a pole-free gauge, whose complete form is
eventually negative at every fixed overlap above the Robin–Euler ratio of the profile. -/
theorem eventually_cofiniteFlip_weilQuadTw_neg_of_gt_robinEuler {F : Finset ℕ}
    (hF : ∀ p ∈ F, p.Prime) {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hφ0 : 0 < ∫ u, φ u ^ 2) (hRE1 : robinEulerThreshold φ < 1)
    {c : ℝ} (hc : robinEulerThreshold φ < c)
    {w : ℕ → ℝ} (hw_pos : ∀ᶠ N in atTop, 0 < w N)
    (hw_lim : Tendsto (fun N : ℕ => w N * (N : ℝ)) atTop (𝓝 c)) :
    ∀ᶠ N : ℕ in atTop, ∃ x : ℕ → ℝ,
      weilQuadTw (fun n => cofiniteFlip F n * ArithmeticFunction.vonMangoldt n)
        (atomicTest N x (atomDilate φ (w N))) < 0 :=
  eventually_signGauge_weilQuadTw_neg_of_gt_robinEuler (cofiniteFlip_isSignGauge F)
    (cofiniteFlip_harmonicSum_abs_le hF) hφ hφsupp hφ0 hRE1 hc hw_pos hw_lim

end Gauge

end GaloisForLFunctions.TransMetzlerWeilPositivity
