import GaloisForLFunctions.RHTower.CHMDFullJumpMoment
import GaloisForLFunctions.RHTower.ZetaSymbolArchimedeanHorizon

/-!
# Uniform endpoint control for all arithmetic jumps

Chebyshev's square-root prefix bound and logarithmic shells control the complete
prime row. This is the analytic input to arithmetic domain removal; no truncation
or assumption about the zeros is used.
-/

open MeasureTheory Set Filter Topology
noncomputable section
namespace RHTower.CHMDDoobGraph

theorem sum_primeAtom_le (s : Finset ℕ) {Y : ℝ} (hY : 0 ≤ Y)
    (hs : ∀ n ∈ s, (n : ℝ) ≤ Y) :
    ∑ n ∈ s, vonMangoldtAtom n ≤ 34 * Real.sqrt Y := by
  classical
  calc
    ∑ n ∈ s, vonMangoldtAtom n =
        ∑ n ∈ s.filter (fun n => 2 ≤ n),
          ArithmeticFunction.vonMangoldt n / Real.sqrt n := by
      simp only [Finset.sum_filter, vonMangoldtAtom]
    _ ≤ ∑ n ∈ Finset.Ioc 0 ⌊Y⌋₊,
          ArithmeticFunction.vonMangoldt n / Real.sqrt n := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro n hn
        obtain ⟨hn, hn2⟩ := Finset.mem_filter.mp hn
        exact Finset.mem_Ioc.mpr ⟨by omega, Nat.le_floor (hs n hn)⟩
      · intro n _ _
        exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _)
    _ ≤ 34 * Real.sqrt (⌊Y⌋₊ : ℝ) := RHTower.sum_vonMangoldt_div_sqrt_le _
    _ ≤ 34 * Real.sqrt Y :=
      mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (Nat.floor_le hY)) (by norm_num)

theorem prime_shell_bound {C : ℝ} (hC : 0 ≤ C)
    (hθ : ∀ x, riemannKernelReal x ≤ C * Real.exp (-(4 * |x|)))
    (x : ℝ) (k : ℕ) (s : Finset ℕ)
    (hs : ∀ n ∈ s, ⌊|x - Real.log n|⌋₊ = k) :
    ∑ n ∈ s, vonMangoldtAtom n * riemannKernelReal (x - Real.log n) ≤
      (34 * C * Real.exp (1 / 2) * Real.exp (x / 2)) *
        Real.exp (-(7 / 2 : ℝ)) ^ k := by
  have hprefix := sum_primeAtom_le s (Real.exp_pos (x + k + 1)).le (fun n hn => by
    by_cases hn0 : n = 0
    · subst n; simpa using (Real.exp_pos (x + k + 1)).le
    have hnf : |x - Real.log n| < (k : ℝ) + 1 := by
      simpa only [hs n hn] using Nat.lt_floor_add_one |x - Real.log n|
    have hl : Real.log n ≤ x + k + 1 := by
      have := neg_le_abs (x - Real.log n)
      linarith
    exact (Real.log_le_iff_le_exp (by exact_mod_cast Nat.pos_of_ne_zero hn0)).mp hl)
  have hθk (n : ℕ) (hn : n ∈ s) :
      riemannKernelReal (x - Real.log n) ≤ C * Real.exp (-4 * (k : ℝ)) := by
    have hnf : (k : ℝ) ≤ |x - Real.log n| := by
      simpa only [hs n hn] using Nat.floor_le (abs_nonneg (x - Real.log n))
    exact (hθ _).trans (mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (by linarith)) hC)
  calc
    _ ≤ ∑ n ∈ s, vonMangoldtAtom n * (C * Real.exp (-4 * (k : ℝ))) :=
      Finset.sum_le_sum fun n hn =>
        mul_le_mul_of_nonneg_left (hθk n hn) (vonMangoldtAtom_nonneg n)
    _ = (∑ n ∈ s, vonMangoldtAtom n) * (C * Real.exp (-4 * (k : ℝ))) :=
      (Finset.sum_mul ..).symm
    _ ≤ (34 * Real.sqrt (Real.exp (x + k + 1))) *
        (C * Real.exp (-4 * (k : ℝ))) :=
      mul_le_mul_of_nonneg_right hprefix (mul_nonneg hC (Real.exp_pos _).le)
    _ = _ := by
      have hsqrt : Real.sqrt (Real.exp (x + k + 1)) = Real.exp ((x + k + 1) / 2) := by
        calc
          _ = Real.sqrt (Real.exp ((x + k + 1) / 2) * Real.exp ((x + k + 1) / 2)) := by
            rw [← Real.exp_add]
            congr 2; ring
          _ = _ := Real.sqrt_mul_self (Real.exp_pos _).le
      rw [hsqrt, ← Real.exp_nat_mul]
      calc
        _ = 34 * C * (Real.exp ((x + k + 1) / 2) * Real.exp (-4 * (k : ℝ))) := by ring
        _ = 34 * C * Real.exp ((x + k + 1) / 2 + -4 * (k : ℝ)) := by rw [Real.exp_add]
        _ = 34 * C * Real.exp ((1 / 2 : ℝ) + x / 2 + k * -(7 / 2 : ℝ)) := by
          congr 2; ring
        _ = _ := by rw [Real.exp_add, Real.exp_add]; ring

theorem exists_prime_row_bound : ∃ K : ℝ, 0 ≤ K ∧ ∀ x : ℝ,
    Summable (fun n : ℕ => vonMangoldtAtom n * riemannKernelReal (x - Real.log n)) ∧
      (∑' n : ℕ, vonMangoldtAtom n * riemannKernelReal (x - Real.log n)) ≤
        K * Real.exp (x / 2) := by
  classical
  obtain ⟨C, hC, hθ⟩ := exists_riemannKernelReal_le
  let r : ℝ := Real.exp (-(7 / 2 : ℝ))
  have hr0 : 0 ≤ r := (Real.exp_pos _).le
  have hrs : Summable (fun k : ℕ => r ^ k) :=
    summable_geometric_of_norm_lt_one (by
      rw [Real.norm_eq_abs, abs_of_nonneg hr0]
      exact Real.exp_lt_one_iff.mpr (by norm_num))
  let A : ℝ := 34 * C * Real.exp (1 / 2)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  refine ⟨A * ∑' k : ℕ, r ^ k, mul_nonneg hA (tsum_nonneg fun k => pow_nonneg hr0 k), ?_⟩
  intro x
  have hnonneg (n : ℕ) : 0 ≤ vonMangoldtAtom n * riemannKernelReal (x - Real.log n) :=
    mul_nonneg (vonMangoldtAtom_nonneg n) (riemannKernelReal_pos _).le
  have hfinite (s : Finset ℕ) :
      ∑ n ∈ s, vonMangoldtAtom n * riemannKernelReal (x - Real.log n) ≤
        (A * ∑' k : ℕ, r ^ k) * Real.exp (x / 2) := by
    let shell : ℕ → ℕ := fun n => ⌊|x - Real.log n|⌋₊
    rw [← Finset.sum_fiberwise_of_maps_to
      (fun n hn => Finset.mem_image_of_mem shell hn)]
    calc
      _ ≤ ∑ k ∈ s.image shell, (A * Real.exp (x / 2)) * r ^ k := by
        apply Finset.sum_le_sum
        intro k _
        exact prime_shell_bound hC hθ x k _ (fun n hn => (Finset.mem_filter.mp hn).2)
      _ = (A * Real.exp (x / 2)) * ∑ k ∈ s.image shell, r ^ k :=
        (Finset.mul_sum ..).symm
      _ ≤ (A * Real.exp (x / 2)) * ∑' k : ℕ, r ^ k :=
        mul_le_mul_of_nonneg_left (hrs.sum_le_tsum _ fun k _ => pow_nonneg hr0 k)
          (mul_nonneg hA (Real.exp_pos _).le)
      _ = _ := by ring
  exact ⟨summable_of_sum_le hnonneg hfinite, Real.tsum_le_of_sum_le hnonneg hfinite⟩

def primeRowConstant : ℝ := exists_prime_row_bound.choose

theorem primeRowConstant_nonneg : 0 ≤ primeRowConstant :=
  exists_prime_row_bound.choose_spec.1

theorem summable_prime_row (x : ℝ) :
    Summable (fun n : ℕ => vonMangoldtAtom n * riemannKernelReal (x - Real.log n)) :=
  (exists_prime_row_bound.choose_spec.2 x).1

theorem prime_row_le (x : ℝ) :
    (∑' n : ℕ, vonMangoldtAtom n * riemannKernelReal (x - Real.log n)) ≤
      primeRowConstant * Real.exp (x / 2) :=
  (exists_prime_row_bound.choose_spec.2 x).2

theorem summable_prime_row_plus (x : ℝ) :
    Summable (fun n : ℕ => vonMangoldtAtom n * riemannKernelReal (x + Real.log n)) := by
  have h := summable_prime_row (-x)
  simpa only [show ∀ n : ℕ, -x - Real.log n = -(x + Real.log n) by intro n; ring,
    WeilExcess.riemannKernelReal_neg] using h

theorem prime_row_plus_le (x : ℝ) :
    (∑' n : ℕ, vonMangoldtAtom n * riemannKernelReal (x + Real.log n)) ≤
      primeRowConstant * Real.exp (-x / 2) := by
  have h := prime_row_le (-x)
  simpa only [show ∀ n : ℕ, -x - Real.log n = -(x + Real.log n) by intro n; ring,
    WeilExcess.riemannKernelReal_neg] using h

end RHTower.CHMDDoobGraph
