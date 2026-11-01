import GaloisForLFunctions.HodgeTheoryWithoutVarieties.TheMoebiusGluingOfStars
import GaloisForLFunctions.ArithmeticCouplingTheory.TheCompleteFormOnTheCoherentSector

/-!
# The renormalized prime form is glued from its stars

The Möbius recursion of the prime form (`atomicWeilForm_moebius_recursion`) writes `P_N` as the
cone of the vertex `1` plus the Möbius-signed prime forms of the stars. Gluing the counterterms in
the same way produces the classical identity `Σ_{d ∣ n} μ(d) log d = −Λ(n)`: the counterterms
`log ⌊N/d⌋ − γ` of the stars, signed by `−μ(d)`, add up at a vertex `n ≥ 2` to
`log N − γ − Λ(n)`, up to the floor defects. The missing `Λ(n)` combines with the cone of the root
into a sum of squares. The result is an exact inductive identity
(`renormalizedPrimeForm_moebius_recursion`):

  `R_N(x) = Σ_{k ≤ N} Λ(k)(x_k − x₁ k^{−1/2})² − R(N) x₁² − F_N(x)
            + Σ_{2 ≤ d ≤ N} (−μ(d)) R_{⌊N/d⌋}(x(d·))`,

* the **root defect** `Σ Λ(k)(x_k − x₁/√k)²` is the pole defect of the edges leaving the vertex
  `1`, a local sum of squares (`rootDefect_nonneg`);
* `R(N) = ψ₁(N) − log N + γ` is the Mertens remainder at the root;
* `F_N(x) = Σ_n x_n² Σ_{d ∣ n, d ≥ 2} μ(d) δ_N(d)` collects the floor defects
  `δ_N(d) = log N − log d − log ⌊N/d⌋ ∈ [0, log 2]`;
* the last sum is the renormalized form of every star at its lower horizon, with Möbius signs.

At each level the renormalized form is a positive local piece at the root, an arithmetic remainder
and an alternating sum of lower levels. Unwinding the recursion over the nerve assembles the root
defects of all vertices into RAPT's pole defect. That is the ground-state identity, written as an
induction over stars.
-/

noncomputable section

open Finset ArithmeticFunction
open GaloisForLFunctions.ArithmeticCouplingTheory GaloisForLFunctions.ArithmeticElectrostatics
  GaloisForLFunctions.ArithmeticEffectivityTheory

namespace GaloisForLFunctions.HodgeTheoryWithoutVarieties

/-- The root defect: the pole defect of the dilation edges leaving the vertex `1`. -/
def rootDefect (N : ℕ) (x : ℕ → ℝ) : ℝ := ∑ k ∈ Icc 1 N, Λ k * (x k - x 1 / Real.sqrt k) ^ 2

theorem rootDefect_nonneg (N : ℕ) (x : ℕ → ℝ) : 0 ≤ rootDefect N x :=
  sum_nonneg fun _ _ => mul_nonneg vonMangoldt_nonneg (sq_nonneg _)

/-- The floor term `Σ_n x_n² Σ_{d ∣ n, d ≥ 2} μ(d) δ_N(d)`. -/
def starFloorTerm (N : ℕ) (x : ℕ → ℝ) : ℝ :=
  ∑ n ∈ Icc 1 N, x n ^ 2 * ∑ d ∈ n.divisors.erase 1, (μ d : ℝ) * floorDefect N d

/-- The cone of the root is Weil's kernel from `1`: `P(1, k) = Λ(k)/√k`. -/
theorem weilPrimeKernel_one_left (k : ℕ) : weilPrimeKernel 1 k = Λ k / Real.sqrt k := by
  rcases Nat.lt_or_ge k 2 with hk | hk
  · interval_cases k <;> simp [weilPrimeKernel]
  · simp [weilPrimeKernel, show (1 : ℕ) ≠ k by omega]

/-- The divisors `≥ 2` of `n ≤ N` are the multiples-in-reverse used by the stars. -/
theorem filter_Icc_two_dvd {N n : ℕ} (hn : n ∈ Icc 1 N) :
    (Icc 2 N).filter (· ∣ n) = n.divisors.erase 1 := by
  have hn0 : n ≠ 0 := by have := (mem_Icc.mp hn).1; omega
  ext d
  simp only [mem_filter, mem_Icc, mem_erase, Nat.mem_divisors]
  constructor
  · rintro ⟨⟨h2, -⟩, hd⟩; exact ⟨by omega, hd, hn0⟩
  · rintro ⟨h1, hd, -⟩
    have hd0 : d ≠ 0 := by rintro rfl; simp at hd; exact hn0 hd
    exact ⟨⟨by omega, (Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hd).trans (mem_Icc.mp hn).2⟩, hd⟩

/-- **The star counterterms glue to `log N − γ − Λ(n)`.** At a vertex `n ≤ N` the Möbius-signed
counterterms of the stars through `n` add up to `[n ≠ 1](log N − γ) − Λ(n) + Σ μ(d) δ_N(d)`. -/
theorem sum_star_counterterms {N n : ℕ} (hn : n ∈ Icc 1 N) :
    ∑ d ∈ n.divisors.erase 1,
        -(μ d : ℝ) * (Real.log (N / d : ℕ) - Real.eulerMascheroniConstant) =
      (if n = 1 then 0 else Real.log N - Real.eulerMascheroniConstant) - Λ n +
        ∑ d ∈ n.divisors.erase 1, (μ d : ℝ) * floorDefect N d := by
  have hn0 : n ≠ 0 := by have := (mem_Icc.mp hn).1; omega
  have hterm : ∀ d ∈ n.divisors.erase 1,
      -(μ d : ℝ) * (Real.log (N / d : ℕ) - Real.eulerMascheroniConstant) =
        -(μ d : ℝ) * (Real.log N - Real.eulerMascheroniConstant) + (μ d : ℝ) * Real.log d +
          (μ d : ℝ) * floorDefect N d := fun d _ => by
    rw [floorDefect]; ring
  rw [sum_congr rfl hterm, sum_add_distrib, sum_add_distrib, ← sum_mul]
  have h1 := sum_divisors_moebius n
  have h2 := sum_moebius_mul_log_eq (n := n)
  have hmem : (1 : ℕ) ∈ n.divisors := Nat.mem_divisors.mpr ⟨one_dvd n, hn0⟩
  rw [← sum_erase_add _ _ hmem] at h1 h2
  simp only [moebius_apply_one, Int.cast_one, Nat.cast_one, Real.log_one, mul_zero,
    add_zero] at h1 h2
  rw [sum_neg_distrib, h2]
  split_ifs with hn1
  · rw [show ∑ x ∈ n.divisors.erase 1, (μ x : ℝ) = 0 by rw [if_pos hn1] at h1; linarith]
    simp [hn1]
  · rw [show ∑ x ∈ n.divisors.erase 1, (μ x : ℝ) = -1 by rw [if_neg hn1] at h1; linarith]
    ring

/-- The diagonal of the star counterterms, regrouped by vertices. -/
theorem sum_star_diagonal (N : ℕ) (x : ℕ → ℝ) (c : ℕ → ℝ) :
    ∑ d ∈ Icc 2 N, c d * ∑ a ∈ Icc 1 (N / d), starPullback d x a ^ 2 =
      ∑ n ∈ Icc 1 N, x n ^ 2 * ∑ d ∈ n.divisors.erase 1, c d := by
  have hstar : ∀ d ∈ Icc 2 N, ∑ a ∈ Icc 1 (N / d), starPullback d x a ^ 2 =
      ∑ n ∈ Icc 1 N, if d ∣ n then x n ^ 2 else 0 := by
    intro d hd
    have hd0 : 0 < d := by have := (mem_Icc.mp hd).1; omega
    rw [sum_Icc_star hd0 N (fun n => if d ∣ n then x n ^ 2 else 0) fun n hn => if_neg hn]
    exact sum_congr rfl fun a _ => by simp [starPullback]
  have hL : ∑ d ∈ Icc 2 N, c d * ∑ a ∈ Icc 1 (N / d), starPullback d x a ^ 2 =
      ∑ d ∈ Icc 2 N, c d * ∑ n ∈ Icc 1 N, (if d ∣ n then x n ^ 2 else 0) :=
    sum_congr rfl fun d hd => by rw [hstar d hd]
  rw [hL]
  simp only [mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun n hn => ?_
  rw [← filter_Icc_two_dvd hn, sum_filter]
  exact sum_congr rfl fun d _ => by split_ifs <;> ring

/-- **The renormalized prime form is glued from its stars.** -/
theorem renormalizedPrimeForm_moebius_recursion {N : ℕ} (hN : 1 ≤ N) (x : ℕ → ℝ) :
    renormalizedPrimeForm N x =
      rootDefect N x - mertensRemainder N * x 1 ^ 2 - starFloorTerm N x +
        ∑ d ∈ Icc 2 N, -(μ d : ℝ) * renormalizedPrimeForm (N / d) (starPullback d x) := by
  -- Express each star's prime form through its renormalized form and regroup the diagonals.
  have hstars : ∑ d ∈ Icc 2 N, -(μ d : ℝ) * atomicWeilForm (N / d) (starPullback d x) =
      ∑ n ∈ Icc 1 N, x n ^ 2 * ∑ d ∈ n.divisors.erase 1,
          -(μ d : ℝ) * (Real.log (N / d : ℕ) - Real.eulerMascheroniConstant) -
        ∑ d ∈ Icc 2 N, -(μ d : ℝ) * renormalizedPrimeForm (N / d) (starPullback d x) := by
    have hdiag := sum_star_diagonal N x
      (fun d => -(μ d : ℝ) * (Real.log (N / d : ℕ) - Real.eulerMascheroniConstant))
    simp only at hdiag
    rw [← hdiag, ← sum_sub_distrib]
    refine sum_congr rfl fun d _ => ?_
    rw [renormalizedPrimeForm]
    ring
  have hroot : rootDefect N x = ∑ k ∈ Icc 1 N, Λ k * x k ^ 2 -
      2 * x 1 * ∑ k ∈ Icc 1 N, weilPrimeKernel 1 k * x k + mertensSum N * x 1 ^ 2 := by
    rw [rootDefect, mertensSum, mul_sum, sum_mul, ← sum_sub_distrib, ← sum_add_distrib]
    refine sum_congr rfl fun k hk => ?_
    have hk0 : (0 : ℝ) < k := by exact_mod_cast (mem_Icc.mp hk).1
    have hk' : Real.sqrt k ^ 2 = k := Real.sq_sqrt hk0.le
    rw [weilPrimeKernel_one_left, sub_sq, div_pow, hk']
    ring
  have hcoef : ∀ n ∈ Icc 1 N, x n ^ 2 * ∑ d ∈ n.divisors.erase 1,
        -(μ d : ℝ) * (Real.log (N / d : ℕ) - Real.eulerMascheroniConstant) =
      x n ^ 2 * (if n = 1 then 0 else Real.log N - Real.eulerMascheroniConstant) -
        Λ n * x n ^ 2 + x n ^ 2 * ∑ d ∈ n.divisors.erase 1, (μ d : ℝ) * floorDefect N d := by
    intro n hn
    rw [sum_star_counterterms hn]
    ring
  have hsplit : ∑ n ∈ Icc 1 N, x n ^ 2 *
        (if n = 1 then 0 else Real.log N - Real.eulerMascheroniConstant) =
      (Real.log N - Real.eulerMascheroniConstant) * ∑ n ∈ Icc 1 N, x n ^ 2 -
        (Real.log N - Real.eulerMascheroniConstant) * x 1 ^ 2 := by
    rw [mul_sum, ← sum_erase_add _ _ (mem_Icc.mpr ⟨le_rfl, hN⟩),
      ← sum_erase_add _ _ (mem_Icc.mpr ⟨le_rfl, hN⟩), if_pos rfl]
    rw [sum_congr rfl fun n hn => by rw [if_neg (ne_of_mem_erase hn)]]
    ring
  rw [renormalizedPrimeForm, atomicWeilForm_moebius_recursion, hstars, sum_congr rfl hcoef,
    sum_add_distrib, sum_sub_distrib, hsplit, hroot, starFloorTerm, mertensRemainder]
  ring

end GaloisForLFunctions.HodgeTheoryWithoutVarieties
