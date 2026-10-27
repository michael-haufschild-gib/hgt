import GaloisForLFunctions.ArithmeticIntersectionTheory.ThePrimeKernelIsASumOfTransverseTowers
import GaloisForLFunctions.RHTower.MertensSecondTheorem
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# The local forms do not sum

Weil's prime form is the sum of its local forms, `Σ x_m x_n P(m,n) = Σ_p Q_p(x)`, and each local form
is bounded uniformly in the cycle: `(1 − q) Q_p(x) ≤ 2q log p |x|²`, `q = p^{−1/2}`
(`ThePrimeKernelIsASumOfTransverseTowers`). The sum is not bounded.

* **The pole direction** (`primeForm_poleVector_ge`): on the orders `1, …, M²` the cycle
  `x_n = n^{−1/2}` — the coefficients of the partial sums of `ζ` at the centre, i.e. the direction of
  the pole — has prime form at least `H_M · Σ_{t ≤ M} Λ(t)/t` and mass `H_{M²}`.
* **Unboundedness** (`not_exists_primeForm_le`): no constant `C` satisfies
  `Σ x_m x_n P(m,n) ≤ C |x|²` for all cycles. By Mertens' theorem the ratio along the pole direction
  grows like `log M`.

So local positivity at every prime (`localForm_lower`) and local boundedness (`localForm_upper`) do
not survive the sum over primes: the identity is subtracted once per prime, and `Σ_p 2 log p/(√p − 1)`
diverges. In Weil's form the growth is paid by the archimedean place, whose self-energy of an atom of
width `ε` is `log(1/ε)`: this is where the global sign has to come from.
-/

noncomputable section

open Finset Filter Topology
open scoped ArithmeticFunction.vonMangoldt

namespace GaloisForLFunctions.ArithmeticIntersectionTheory

open ArithmeticEffectivityTheory

theorem weilPrimeKernel_nonneg (m n : ℕ) : 0 ≤ weilPrimeKernel m n := by
  unfold weilPrimeKernel
  split_ifs
  · exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _)
  · exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _)
  · exact le_rfl

theorem weilPrimeKernel_mul_right {m t : ℕ} (hm : 0 < m) (ht : 1 < t) :
    weilPrimeKernel m (m * t) = Λ t / Real.sqrt t := by
  have hne : m ≠ m * t := fun h => by
    have := Nat.eq_of_mul_eq_mul_left hm (h.symm.trans (mul_one m).symm); omega
  rw [weilPrimeKernel, if_pos ⟨dvd_mul_right m t, hne⟩, Nat.mul_div_cancel_left t hm]

/-- The **pole direction** `x_n = n^{−1/2}`. -/
def poleVector (n : ℕ) : ℝ := 1 / Real.sqrt n

theorem poleVector_nonneg (n : ℕ) : 0 ≤ poleVector n := by unfold poleVector; positivity

theorem sum_poleVector_sq (N : ℕ) : ∑ n ∈ Icc 1 N, poleVector n ^ 2 = harmonic N := by
  rw [harmonic_eq_sum_Icc]
  push_cast
  refine sum_congr rfl fun n _ => ?_
  rw [poleVector, div_pow, one_pow, Real.sq_sqrt (Nat.cast_nonneg n), one_div]

/-- **The prime form along the pole direction**: on `1, …, M²`,
`Σ x_m x_n P(m,n) ≥ H_M Σ_{t ≤ M} Λ(t)/t` for `x_n = n^{−1/2}`. -/
theorem primeForm_poleVector_ge (M : ℕ) :
    (harmonic M : ℝ) * ∑ t ∈ Icc 1 M, Λ t / (t : ℝ) ≤ primeForm (Icc 1 (M ^ 2)) poleVector := by
  set S := Icc 1 (M ^ 2)
  set f : ℕ × ℕ → ℝ := fun p => poleVector p.1 * poleVector p.2 * weilPrimeKernel p.1 p.2
  have hf : ∀ p, 0 ≤ f p := fun p =>
    mul_nonneg (mul_nonneg (poleVector_nonneg _) (poleVector_nonneg _)) (weilPrimeKernel_nonneg _ _)
  set g : ℕ × ℕ → ℕ × ℕ := fun q => (q.1, q.1 * q.2)
  have hg : Set.InjOn g ↑(Icc 1 M ×ˢ Icc 2 M) := by
    intro q hq q' hq' h
    simp only [coe_product, Set.mem_prod, mem_coe, mem_Icc] at hq hq'
    simp only [g, Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    rw [h1] at h2
    exact Prod.ext h1 (Nat.eq_of_mul_eq_mul_left (by omega) h2)
  have hsub : (Icc 1 M ×ˢ Icc 2 M).image g ⊆ S ×ˢ S := by
    intro p hp
    obtain ⟨q, hq, rfl⟩ := mem_image.mp hp
    simp only [mem_product, mem_Icc] at hq
    simp only [g, S, mem_product, mem_Icc]
    refine ⟨⟨hq.1.1, ?_⟩, ⟨by nlinarith, ?_⟩⟩
    · nlinarith
    · rw [sq]; exact Nat.mul_le_mul hq.1.2 hq.2.2
  have hterm : ∀ q ∈ Icc 1 M ×ˢ Icc 2 M, f (g q) = Λ q.2 / (q.2 : ℝ) * (1 / (q.1 : ℝ)) := by
    intro q hq
    simp only [mem_product, mem_Icc] at hq
    have hm : (0 : ℝ) < q.1 := by exact_mod_cast hq.1.1
    have ht : (0 : ℝ) < q.2 := by exact_mod_cast (show 0 < q.2 by omega)
    simp only [f, g, poleVector, weilPrimeKernel_mul_right (show 0 < q.1 by omega)
      (show 1 < q.2 by omega), Nat.cast_mul]
    rw [Real.sqrt_mul hm.le]
    have hsm := Real.sq_sqrt hm.le
    have hst := Real.sq_sqrt ht.le
    have h1 : 0 < Real.sqrt q.1 := Real.sqrt_pos.mpr hm
    have h2 : 0 < Real.sqrt q.2 := Real.sqrt_pos.mpr ht
    field_simp
    simp only [hsm, hst]
    ring
  calc (harmonic M : ℝ) * ∑ t ∈ Icc 1 M, Λ t / (t : ℝ)
      = ∑ q ∈ Icc 1 M ×ˢ Icc 2 M, Λ q.2 / (q.2 : ℝ) * (1 / (q.1 : ℝ)) := by
        rw [sum_product, harmonic_eq_sum_Icc]
        push_cast
        rw [sum_mul]
        refine sum_congr rfl fun m _ => ?_
        rw [mul_comm, sum_mul]
        rcases Nat.eq_zero_or_pos M with rfl | hM
        · simp
        rw [← insert_Icc_add_one_left_eq_Icc (by omega : 1 ≤ M), sum_insert (by simp)]
        simp only [ArithmeticFunction.vonMangoldt_apply_one, zero_div, zero_mul, zero_add, one_div]
        rfl
    _ = ∑ q ∈ Icc 1 M ×ˢ Icc 2 M, f (g q) := (sum_congr rfl hterm).symm
    _ = ∑ p ∈ (Icc 1 M ×ˢ Icc 2 M).image g, f p := (sum_image hg).symm
    _ ≤ ∑ p ∈ S ×ˢ S, f p := sum_le_sum_of_subset_of_nonneg hsub fun p _ _ => hf p
    _ = primeForm S poleVector := by rw [sum_product]; rfl

/-- **The local forms do not sum**: there is no constant `C` with `Σ x_m x_n P(m,n) ≤ C |x|²` for all
cycles on positive orders, although each local form obeys such a bound. -/
theorem not_exists_primeForm_le :
    ¬ ∃ C : ℝ, ∀ (S : Finset ℕ) (x : ℕ → ℝ), (∀ n ∈ S, n ≠ 0) →
      primeForm S x ≤ C * ∑ n ∈ S, x n ^ 2 := by
  rintro ⟨C, hC⟩
  set C' := max C 0
  set γ := Real.eulerMascheroniConstant
  -- Mertens: eventually `Σ_{t ≤ M} Λ(t)/t ≥ log M − γ − 1`
  have hmert : ∀ᶠ M : ℕ in atTop,
      Real.log M - γ - 1 ≤ ∑ t ∈ Icc 1 M, Λ t / (t : ℝ) := by
    have h := RHTower.tendsto_sum_vonMangoldt_div_sub_log
    filter_upwards [(h.eventually (Ioi_mem_nhds (show -γ - 1 < -γ by linarith)))] with M hM
    have hM' : -γ - 1 < (∑ n ∈ Icc 1 M, (ArithmeticFunction.vonMangoldt n : ℝ) / (n : ℝ)) -
        Real.log M := hM
    linarith
  have hlog : ∀ᶠ M : ℕ in atTop, max C' (γ + 2 + 2 * C') + 1 < Real.log M :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_gt_atTop _
  obtain ⟨M, hM1, hM2⟩ := (hmert.and hlog).exists
  have hC'0 : 0 ≤ C' := le_max_right _ _
  have hM0 : 0 < M := by
    rcases Nat.eq_zero_or_pos M with h | h
    · exfalso
      rw [h, Nat.cast_zero, Real.log_zero] at hM2
      linarith [le_max_left C' (γ + 2 + 2 * C')]
    · exact h
  set L := Real.log M
  have hL1 : C' < L := by linarith [le_max_left C' (γ + 2 + 2 * C')]
  have hL2 : γ + 2 + 2 * C' < L := by linarith [le_max_right C' (γ + 2 + 2 * C')]
  have hH : L ≤ (harmonic M : ℝ) := by
    calc L ≤ Real.log ((M + 1 : ℕ) : ℝ) :=
          Real.log_le_log (by exact_mod_cast hM0) (by push_cast; linarith)
      _ ≤ _ := log_add_one_le_harmonic M
  have hH2 : (harmonic (M ^ 2) : ℝ) ≤ 1 + 2 * L := by
    have := harmonic_le_one_add_log (M ^ 2)
    rwa [Nat.cast_pow, Real.log_pow, Nat.cast_ofNat] at this
  have hlow := primeForm_poleVector_ge M
  have hup := hC (Icc 1 (M ^ 2)) poleVector (fun n hn => by simp at hn; omega)
  rw [sum_poleVector_sq] at hup
  have hS : (0 : ℝ) ≤ harmonic (M ^ 2) := by
    rw [harmonic_eq_sum_Icc]; push_cast; exact sum_nonneg fun i _ => by positivity
  have hmass : C * (harmonic (M ^ 2) : ℝ) ≤ C' * (1 + 2 * L) :=
    (mul_le_mul_of_nonneg_right (le_max_left C 0) hS).trans
      (mul_le_mul_of_nonneg_left hH2 hC'0)
  have hsum : 0 ≤ L - γ - 1 := by linarith
  have key : L * (L - γ - 1) ≤ (harmonic M : ℝ) * ∑ t ∈ Icc 1 M, Λ t / (t : ℝ) :=
    mul_le_mul hH hM1 hsum (le_trans (by linarith) hH)
  nlinarith

end GaloisForLFunctions.ArithmeticIntersectionTheory
