import GaloisForLFunctions.RHTower.WeilWorkPBAPCriticalDatum
import GaloisForLFunctions.RHTower.WeilPrimitiveSetMeanSquare

/-!
# Actual convergence of coefficients of a modified Weil datum

The primitive-set and dyadic arguments are applied to the sharp bound derived
from actual smooth tests. Absolute convergence on every `Re s > 1` is a
conclusion, never an extra premise of the critical-coefficient argument.
-/

open Complex Finset Filter Topology
open scoped Real ComplexConjugate
noncomputable section
namespace RHTower.WeilWorkPBAP
open WeilMeanSquare

/-- The star-vector argument at one finite level, with its exact scalar ceiling. -/
theorem primitive_square_bound {lam : ℕ → ℝ} {N : ℕ} {L : ℝ} (hN : 1 ≤ N)
    (hBound : ∀ c : ℕ → ℂ, (∀ m, N < m → c m = 0) →
      2 * ∑ n ∈ Finset.Icc 2 N, lam n / Real.sqrt n *
        (∑ m ∈ Finset.Icc 1 N, c (n * m) * conj (c m)).re ≤
          L * ∑ m ∈ Finset.Icc 1 N, ‖c m‖ ^ 2) :
    0 ≤ L ∧ ∀ S : Finset ℕ, S ⊆ Finset.Icc 2 N → IsPrimitiveSet S →
      ∑ n ∈ S, lam n ^ 2 / n ≤ L ^ 2 := by
  -- the resonator `c = δ₁ + t Σ_S lam(n) n^{-1/2} δ_n`
  have key : ∀ S : Finset ℕ, S ⊆ Finset.Icc 2 N → IsPrimitiveSet S → ∀ t : ℝ,
      2 * t * ∑ n ∈ S, lam n ^ 2 / n ≤
        (L) * (1 + t ^ 2 * ∑ n ∈ S, lam n ^ 2 / n) := by
    intro S hS hprim t
    set c : ℕ → ℂ := fun m => if m = 1 then 1 else if m ∈ S then
      ((t * lam m / Real.sqrt m : ℝ) : ℂ) else 0 with hc
    have hcN : ∀ m, N < m → c m = 0 := by
      intro m hm
      have h1 : m ≠ 1 := by omega
      have h2 : m ∉ S := fun h => by have := (Finset.mem_Icc.mp (hS h)).2; omega
      simp [hc, h1, h2]
    have h := hBound c hcN
    have hinner : ∀ n ∈ Finset.Icc 2 N,
        (∑ m ∈ Finset.Icc 1 N, c (n * m) * conj (c m)).re =
          if n ∈ S then t * lam n / Real.sqrt n else 0 := by
      intro n hn
      obtain ⟨hn2, hnN⟩ := Finset.mem_Icc.mp hn
      rw [← Finset.add_sum_erase _ _ (Finset.mem_Icc.mpr ⟨le_rfl, hN⟩)]
      have hrest : ∑ m ∈ (Finset.Icc 1 N).erase 1, c (n * m) * conj (c m) = 0 := by
        refine Finset.sum_eq_zero fun m hm => ?_
        obtain ⟨hm1, hmI⟩ := Finset.mem_erase.mp hm
        by_cases hmS : m ∈ S
        · have hnm1 : n * m ≠ 1 := by
            have := (Finset.mem_Icc.mp hmI).1; nlinarith
          have hnmS : n * m ∉ S := fun h' => hprim _ h' m hmS n hn2 rfl
          simp [hc, hnm1, hnmS]
        · simp [hc, hm1, hmS]
      rw [hrest, add_zero, mul_one]
      have hn1 : n ≠ 1 := by omega
      by_cases hnS : n ∈ S
      · simp [hc, hn1, hnS]
      · simp [hc, hn1, hnS]
    have hmass : ∑ m ∈ Finset.Icc 1 N, ‖c m‖ ^ 2 = 1 + t ^ 2 * ∑ n ∈ S, lam n ^ 2 / n := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_Icc.mpr ⟨le_rfl, hN⟩)]
      have hS' : S ⊆ (Finset.Icc 1 N).erase 1 := fun n hn => by
        have := Finset.mem_Icc.mp (hS hn)
        exact Finset.mem_erase.mpr ⟨by omega, Finset.mem_Icc.mpr ⟨by omega, this.2⟩⟩
      rw [← Finset.sum_subset hS' (fun m hm hmS => by
        have hm1 := (Finset.mem_erase.mp hm).1
        simp [hc, hm1, hmS]), Finset.mul_sum]
      · congr 1
        · simp [hc]
        · refine Finset.sum_congr rfl fun n hn => ?_
          have hn2 := (Finset.mem_Icc.mp (hS hn)).1
          have hn1 : n ≠ 1 := by omega
          have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
          simp only [hc, hn1, hn, if_false, if_true, Complex.norm_real, Real.norm_eq_abs, sq_abs,
            div_pow, mul_pow, Real.sq_sqrt hn0.le]
          ring
    have hlhs : ∑ n ∈ Finset.Icc 2 N, lam n / Real.sqrt n *
        (∑ m ∈ Finset.Icc 1 N, c (n * m) * conj (c m)).re = t * ∑ n ∈ S, lam n ^ 2 / n := by
      rw [Finset.sum_congr rfl fun n hn => by rw [hinner n hn], Finset.mul_sum]
      rw [← Finset.sum_subset hS (fun n _ hnS => by simp [hnS])]
      refine Finset.sum_congr rfl fun n hn => ?_
      have hn2 := (Finset.mem_Icc.mp (hS hn)).1
      have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
      have hsq : Real.sqrt n * Real.sqrt n = n := Real.mul_self_sqrt hn0.le
      rw [if_pos hn, show lam n / Real.sqrt n * (t * lam n / Real.sqrt n) =
        t * (lam n ^ 2 / (Real.sqrt n * Real.sqrt n)) by ring, hsq]
    rw [hlhs, hmass] at h
    linarith
  -- the constant is nonnegative: take `S = ∅`
  have hB : 0 ≤ L := by
    have := key ∅ (Finset.empty_subset _) (fun m hm => absurd hm (Finset.notMem_empty m)) 0
    simpa using this
  refine ⟨hB, fun S hS hprim => ?_⟩
  set Q := ∑ n ∈ S, lam n ^ 2 / n with hQ
  have hQ0 : 0 ≤ Q := Finset.sum_nonneg fun n _ => div_nonneg (sq_nonneg _) (Nat.cast_nonneg n)
  set B := L with hBdef
  rcases hQ0.lt_or_eq with hQpos | hQzero
  · have h := key S hS hprim (B / Q)
    rw [← hQ] at h
    have e : 2 * (B / Q) * Q = 2 * B := by field_simp
    have e2 : B * (1 + (B / Q) ^ 2 * Q) = B + B ^ 3 / Q := by field_simp
    rw [e, e2] at h
    have h3 : B ≤ B ^ 3 / Q := by linarith
    rcases hB.lt_or_eq with hBpos | hBzero
    · rw [le_div_iff₀ hQpos] at h3
      nlinarith
    · have h1 := key S hS hprim 1
      rw [← hQ, ← hBzero] at h1
      nlinarith
  · rw [← hQzero]; positivity

/-- Dyadic mean square for every actual modified completion. -/
theorem critical_dyadic_square_bound {a b C : ℝ} (ha : 0 ≤ a) {lam : ℕ → ℝ}
    (h : ∀ f : SmoothTest, testAtoms lam f.1 ≤ criticalDatum a b C f.1.1)
    (N : ℕ) (hN : 1 ≤ N) :
    0 ≤ a * Real.log (2 * N : ℕ) + (a * resonatorGammaConstant + C) ∧
    ∑ n ∈ Finset.Ioc N (2 * N), lam n ^ 2 ≤
      (2 * N : ℕ) * (a * Real.log (2 * N : ℕ) + (a * resonatorGammaConstant + C)) ^ 2 := by
  obtain ⟨hB, h⟩ := primitive_square_bound (by omega : 1 ≤ 2 * N)
    (fun c hc => critical_multiplicativeToeplitz_bound ha h (by omega) c hc)
  refine ⟨hB, ?_⟩
  have hsub : Finset.Ioc N (2 * N) ⊆ Finset.Icc 2 (2 * N) := fun n hn => by
    rw [Finset.mem_Ioc] at hn; rw [Finset.mem_Icc]; omega
  have hprim : IsPrimitiveSet (Finset.Ioc N (2 * N)) := by
    intro m hm m' hm' k hk heq
    rw [Finset.mem_Ioc] at hm hm'
    have : k * m' ≥ 2 * (N + 1) := Nat.mul_le_mul hk (by omega)
    omega
  have hQ := h _ hsub hprim
  have h2N : (0 : ℝ) < (2 * N : ℕ) := by exact_mod_cast (show 0 < 2 * N by omega)
  calc ∑ n ∈ Finset.Ioc N (2 * N), lam n ^ 2
      = (2 * N : ℕ) * ∑ n ∈ Finset.Ioc N (2 * N), lam n ^ 2 / (2 * N : ℕ) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun n _ => by field_simp
    _ ≤ (2 * N : ℕ) * ∑ n ∈ Finset.Ioc N (2 * N), lam n ^ 2 / n := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun n hn => ?_) h2N.le
        rw [Finset.mem_Ioc] at hn
        have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
        exact div_le_div_of_nonneg_left (sq_nonneg _) hn0 (by exact_mod_cast hn.2)
    _ ≤ (2 * N : ℕ) * (a * Real.log (2 * N : ℕ) + (a * resonatorGammaConstant + C)) ^ 2 := mul_le_mul_of_nonneg_left hQ h2N.le

/-- The actual Dirichlet coefficients converge absolutely for every exponent above one. -/
theorem summable_abs_div_rpow_critical {a b C : ℝ} (ha : 0 ≤ a) {lam : ℕ → ℝ}
    (h : ∀ f : SmoothTest, testAtoms lam f.1 ≤ criticalDatum a b C f.1.1)
    {σ : ℝ} (hσ : 1 < σ) : Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ := by
  let C₀ := a * resonatorGammaConstant + C
  have hC := critical_dyadic_square_bound ha h
  change ∀ N : ℕ, 1 ≤ N → 0 ≤ a * Real.log (2 * N : ℕ) + C₀ ∧
    ∑ n ∈ Finset.Ioc N (2 * N), lam n ^ 2 ≤
      (2 * N : ℕ) * (a * Real.log (2 * N : ℕ) + C₀) ^ 2 at hC
  set r : ℝ := (2 : ℝ) ^ (1 - σ) with hr
  have hr0 : 0 ≤ r := Real.rpow_nonneg (by norm_num) _
  have hr1 : r < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  set b : ℕ → ℝ := fun j => 3 / 2 * r ^ j * (a * ((j + 1) * Real.log 2) + |C₀| + 1) with hb
  have hbs : Summable b := by
    have h1 := (summable_pow_mul_geometric_of_norm_lt_one 1
      (show ‖r‖ < 1 by rw [Real.norm_eq_abs, abs_of_nonneg hr0]; exact hr1)).mul_left
      (3 / 2 * a * Real.log 2)
    have h2 := (summable_geometric_of_lt_one hr0 hr1).mul_left
      (3 / 2 * (a * Real.log 2 + |C₀| + 1))
    refine (h1.add h2).congr fun j => ?_
    simp only [hb, pow_one]; ring
  have hb0 : ∀ j, 0 ≤ b j := fun j => by
    simp only [hb]; have := Real.log_nonneg (show (1 : ℝ) ≤ 2 by norm_num); positivity
  set f : ℕ → ℝ := fun n => |lam n| / (n : ℝ) ^ σ with hf
  have hf0 : ∀ n, 0 ≤ f n := fun n => by simp only [hf]; positivity
  -- the block bound
  have hblock : ∀ j : ℕ, ∑ n ∈ Finset.Ioc (2 ^ j) (2 ^ (j + 1)), f n ≤ b j := by
    intro j
    set N : ℕ := 2 ^ j with hN
    have hN1 : 1 ≤ N := Nat.one_le_two_pow
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
    have h2N : 2 ^ (j + 1) = 2 * N := by rw [pow_succ, mul_comm]
    rw [h2N]
    obtain ⟨hL, hsq⟩ := hC N hN1
    have habs := sum_abs_Ioc_le_of_sum_sq hL hsq
    have hNσ : ∀ n ∈ Finset.Ioc N (2 * N), f n ≤ |lam n| / (N : ℝ) ^ σ := by
      intro n hn
      rw [Finset.mem_Ioc] at hn
      simp only [hf]
      refine div_le_div_of_nonneg_left (abs_nonneg _) (Real.rpow_pos_of_pos hN0 _)
        (Real.rpow_le_rpow hN0.le (by exact_mod_cast hn.1.le) (by linarith))
    calc ∑ n ∈ Finset.Ioc N (2 * N), f n
        ≤ ∑ n ∈ Finset.Ioc N (2 * N), |lam n| / (N : ℝ) ^ σ := Finset.sum_le_sum hNσ
      _ = (∑ n ∈ Finset.Ioc N (2 * N), |lam n|) / (N : ℝ) ^ σ := by rw [Finset.sum_div]
      _ ≤ 3 / 2 * N * (a * Real.log (2 * N : ℕ) + C₀ + 1) / (N : ℝ) ^ σ :=
          div_le_div_of_nonneg_right habs (Real.rpow_nonneg hN0.le _)
      _ ≤ b j := by
          have hNr : (N : ℝ) / (N : ℝ) ^ σ = r ^ j := by
            have e1 : (N : ℝ) = (2 : ℝ) ^ (j : ℝ) := by
              rw [hN, Nat.cast_pow, Nat.cast_ofNat, Real.rpow_natCast]
            have e2 : (N : ℝ) ^ σ = (2 : ℝ) ^ ((j : ℝ) * σ) := by
              rw [e1, ← Real.rpow_mul (by norm_num)]
            have e3 : r ^ j = (2 : ℝ) ^ ((1 - σ) * (j : ℝ)) := by
              rw [hr, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
            rw [e2, e3, e1, ← Real.rpow_sub (by norm_num)]
            congr 1; ring
          have hlog : Real.log (2 * N : ℕ) = (j + 1) * Real.log 2 := by
            rw [← h2N, Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]; push_cast; ring
          rw [hlog]
          have e : 3 / 2 * (N : ℝ) * (a * ((j + 1) * Real.log 2) + C₀ + 1) / (N : ℝ) ^ σ =
              3 / 2 * ((N : ℝ) / (N : ℝ) ^ σ) * (a * ((j + 1) * Real.log 2) + C₀ + 1) := by ring
          rw [e, hNr]
          simp only [hb]
          have hrj : 0 ≤ r ^ j := pow_nonneg hr0 j
          have hC : C₀ ≤ |C₀| := le_abs_self C₀
          nlinarith
  -- dyadic decomposition of `(1, 2^J]`
  have hdyad : ∀ J : ℕ, ∑ n ∈ Finset.Ioc 1 (2 ^ J), f n ≤ ∑ j ∈ Finset.range J, b j := by
    intro J
    induction J with
    | zero => simp
    | succ J ih =>
      rw [← Finset.sum_Ioc_consecutive f (Nat.one_le_two_pow) (Nat.pow_le_pow_right (by norm_num)
        (Nat.le_succ J)), Finset.sum_range_succ]
      exact add_le_add ih (hblock J)
  refine summable_of_sum_range_le (c := f 0 + f 1 + ∑' j, b j) hf0 fun T => ?_
  have hT : T ≤ 2 ^ T := (Nat.lt_two_pow_self).le
  calc ∑ n ∈ Finset.range T, f n ≤ ∑ n ∈ Finset.range (2 ^ T + 1), f n :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr (by omega))
          (fun n _ _ => hf0 n)
    _ = f 0 + f 1 + ∑ n ∈ Finset.Ioc 1 (2 ^ T), f n :=
        sum_range_succ_eq_Ioc f (2 ^ T) Nat.one_le_two_pow
    _ ≤ f 0 + f 1 + ∑' j, b j := by
        have := (hdyad T).trans (hbs.sum_le_tsum _ fun j _ => hb0 j)
        linarith

/-- Harmonic density, including every unimodular multiplicative twist. -/
theorem critical_twisted_density_bound {a b C : ℝ} (ha : 0 ≤ a) {lam : ℕ → ℝ}
    (h : ∀ f : SmoothTest, testAtoms lam f.1 ≤ criticalDatum a b C f.1.1)
    (N : ℕ) (hN : 1 ≤ N) (χ : ℕ → ℂ)
    (hmul : ∀ m n, χ (m * n) = χ m * χ n) (hnorm : ∀ m, ‖χ m‖ = 1) :
    2 * ∑ n ∈ Finset.Icc 2 N, ∑ m ∈ Finset.Icc 1 N,
        (if n * m ≤ N then lam n * (χ n).re / (n * m) else 0) ≤
      (a * Real.log N + (a * resonatorGammaConstant + C)) *
        ∑ m ∈ Finset.Icc 1 N, (1 : ℝ) / m := by
  set c : ℕ → ℂ := fun m => if m ≤ N then χ m * ((1 / Real.sqrt m : ℝ) : ℂ) else 0 with hcdef
  have hc : ∀ m, N < m → c m = 0 := fun m hm => by simp [hcdef, not_le.mpr hm]
  have h := critical_multiplicativeToeplitz_bound ha h hN c hc
  have hχconj : ∀ m, χ m * conj (χ m) = 1 := fun m => by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hnorm]; simp
  have hlhs : ∀ n ∈ Finset.Icc 2 N, lam n / Real.sqrt n *
      (∑ m ∈ Finset.Icc 1 N, c (n * m) * conj (c m)).re =
      ∑ m ∈ Finset.Icc 1 N, (if n * m ≤ N then lam n * (χ n).re / (n * m) else 0) := by
    intro n hn
    have hn1 : (0 : ℝ) < n := by
      have := (Finset.mem_Icc.mp hn).1; exact_mod_cast (show 0 < n by omega)
    rw [Complex.re_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m hm => ?_
    obtain ⟨hm1, hmN⟩ := Finset.mem_Icc.mp hm
    have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
    by_cases hnm : n * m ≤ N
    · rw [if_pos hnm]
      simp only [hcdef, if_pos hnm, if_pos hmN, map_mul, Complex.conj_ofReal, hmul]
      have hsq : Real.sqrt ((n * m : ℕ) : ℝ) = Real.sqrt n * Real.sqrt m := by
        push_cast; exact Real.sqrt_mul hn1.le _
      rw [hsq]
      have hsm : Real.sqrt m * Real.sqrt m = m := Real.mul_self_sqrt hm0.le
      have hr : (1 / (Real.sqrt n * Real.sqrt m)) * (1 / Real.sqrt m) = 1 / (Real.sqrt n * m) := by
        rw [div_mul_div_comm, one_mul, mul_assoc, hsm]
      have e : χ n * χ m * ((1 / (Real.sqrt n * Real.sqrt m) : ℝ) : ℂ) *
          (conj (χ m) * ((1 / Real.sqrt m : ℝ) : ℂ)) =
          χ n * (χ m * conj (χ m)) * ((1 / (Real.sqrt n * m) : ℝ) : ℂ) := by
        rw [← hr]; push_cast; ring
      rw [e, hχconj, mul_one, Complex.re_mul_ofReal]
      have hsn : Real.sqrt n * Real.sqrt n = n := Real.mul_self_sqrt hn1.le
      have hsn0 : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn1
      calc lam n / Real.sqrt n * ((χ n).re * (1 / (Real.sqrt n * m)))
          = lam n * (χ n).re / ((Real.sqrt n * Real.sqrt n) * m) := by field_simp
        _ = lam n * (χ n).re / (n * m) := by rw [hsn]
    · rw [if_neg hnm]
      simp [hcdef, if_neg hnm]
  have hrhs : ∑ m ∈ Finset.Icc 1 N, ‖c m‖ ^ 2 = ∑ m ∈ Finset.Icc 1 N, (1 : ℝ) / m := by
    refine Finset.sum_congr rfl fun m hm => ?_
    obtain ⟨hm1, hmN⟩ := Finset.mem_Icc.mp hm
    have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
    simp only [hcdef, if_pos hmN, norm_mul, hnorm, one_mul, Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_pos (by positivity), div_pow, one_pow, Real.sq_sqrt hm0.le]
  rw [Finset.sum_congr rfl hlhs, hrhs] at h
  exact h

/-- The untwisted signed harmonic density. -/
def harmonicDensity (lam : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 2 N, ∑ m ∈ Finset.Icc 1 N,
    if n * m ≤ N then lam n / (n * m) else 0

/-- Exact quadratic logarithmic ceiling for the actual signed coefficients. -/
theorem critical_harmonic_ceiling {a b C : ℝ} (ha : 0 ≤ a) {lam : ℕ → ℝ}
    (h : ∀ f : SmoothTest, testAtoms lam f.1 ≤ criticalDatum a b C f.1.1)
    (N : ℕ) (hN : 1 ≤ N) :
    2 * harmonicDensity lam N ≤
      a * (Real.log N) ^ 2 + (a + (a * resonatorGammaConstant + C)) * Real.log N +
        (a * resonatorGammaConstant + C) := by
  have hd := critical_twisted_density_bound ha h N hN (fun _ => 1)
    (fun _ _ => by simp) (fun _ => by simp)
  simp only [Complex.one_re, mul_one] at hd
  change 2 * harmonicDensity lam N ≤ _ at hd
  have hB := (primitive_square_bound hN
    (fun c hc => critical_multiplicativeToeplitz_bound ha h hN c hc)).1
  have hb := mul_le_mul_of_nonneg_left (sum_Icc_inv_le_one_add_log N) hB
  exact hd.trans (by nlinarith)

/-- A uniform sharp quadratic ceiling with an explicit constant remainder. -/
theorem critical_harmonic_eps_ceiling {a b C : ℝ} (ha : 0 ≤ a) {lam : ℕ → ℝ}
    (h : ∀ f : SmoothTest, testAtoms lam f.1 ≤ criticalDatum a b C f.1.1)
    (N : ℕ) (hN : 1 ≤ N) {ε : ℝ} (hε : 0 < ε) :
    harmonicDensity lam N ≤ (a / 2 + ε) * (Real.log N) ^ 2 +
      (a * resonatorGammaConstant + C) / 2 +
        (a + (a * resonatorGammaConstant + C)) ^ 2 / (16 * ε) := by
  have hd := critical_harmonic_ceiling ha h N hN
  have hd' := mul_le_mul_of_nonneg_left hd (show 0 ≤ 8 * ε by positivity)
  have hs := sq_nonneg (4 * ε * Real.log N - (a + (a * resonatorGammaConstant + C)))
  have he : (0 : ℝ) < 16 * ε := by positivity
  apply (mul_le_mul_iff_right₀ he).mp
  have heq : (16 * ε) * ((a / 2 + ε) * (Real.log N) ^ 2 +
      (a * resonatorGammaConstant + C) / 2 +
        (a + (a * resonatorGammaConstant + C)) ^ 2 / (16 * ε)) =
      (16 * ε) * ((a / 2 + ε) * (Real.log N) ^ 2 +
        (a * resonatorGammaConstant + C) / 2) +
        (a + (a * resonatorGammaConstant + C)) ^ 2 := by
    field_simp
  rw [heq]
  nlinarith only [hd', hs]

end RHTower.WeilWorkPBAP
