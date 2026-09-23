import GaloisForLFunctions.RHTower.PolynomialFockExactToeplitzAtomScale
import GaloisForLFunctions.RHTower.CriticalPrimeFockAtomicCellAverage

open Filter Topology

namespace RHTower

noncomputable section

/-- Literal adapted average of the exact atomic Toeplitz measure whose raw-evaluation quadratic
form equals normalized critical-prime sampling. -/
def criticalPrimeFockExactToeplitzCellAverage
    (m : ℝ) (hm : 4 ≤ m) (n : ℕ) : ℝ :=
  let x := criticalPrimeFockAdaptedCellCenter m n
  let r := criticalPrimeFockRadius m x
  ∑ k ∈ Finset.Ioc ⌊Real.exp (x - r)⌋₊ ⌊Real.exp (x + r)⌋₊,
    primeLogPowWeight 2 k *
      (polynomialFockExactToeplitzAtomScale m hm (Real.log k) / r ^ 2)

theorem criticalPrimeFockExactToeplitzCellAverage_nonneg
    (m : ℝ) (hm : 4 ≤ m) (n : ℕ) :
    0 ≤ criticalPrimeFockExactToeplitzCellAverage m hm n := by
  unfold criticalPrimeFockExactToeplitzCellAverage
  dsimp only
  exact Finset.sum_nonneg fun k _ => mul_nonneg
    (primeLogPowWeight_two_nonneg k)
    (div_nonneg (polynomialFockExactToeplitzAtomScale_pos hm _).le (sq_nonneg _))

/-- Fixed lower comparison constant between the exact diagonal-normalized Toeplitz atom and the
model `rho_m^(2 : ℕ)` atom. -/
def polynomialFockExactToeplitzLowerConstant (m : ℝ) : ℝ :=
  Real.pi * Real.exp (-2 * (polynomialFockLocalBregmanConstant m / m)) *
    polynomialFockInnerWindowFactor m ^ 2

theorem polynomialFockExactToeplitzLowerConstant_pos
    {m : ℝ} (hm : 4 ≤ m) :
    0 < polynomialFockExactToeplitzLowerConstant m := by
  unfold polynomialFockExactToeplitzLowerConstant
  exact mul_pos (mul_pos Real.pi_pos (Real.exp_pos _))
    (sq_pos_of_pos (polynomialFockInnerWindowFactor_pos hm))

theorem criticalPrimeFockExactToeplitzCellAverage_bounds
    {m : ℝ} (hm : 4 ≤ m) {n : ℕ}
    (hn : 2 ≤ criticalPrimeFockAdaptedCellCenter m n) :
    polynomialFockExactToeplitzLowerConstant m *
        criticalPrimeFockAtomicCellAverage m n ≤
      criticalPrimeFockExactToeplitzCellAverage m hm n ∧
    criticalPrimeFockExactToeplitzCellAverage m hm n ≤
      Real.pi * criticalPrimeFockAtomicCellAverage m n := by
  let x := criticalPrimeFockAdaptedCellCenter m n
  let r := criticalPrimeFockRadius m x
  let S := Finset.Ioc ⌊Real.exp (x - r)⌋₊ ⌊Real.exp (x + r)⌋₊
  have hx : 2 ≤ x := by simpa [x] using hn
  have hx0 : 0 < x := by linarith
  have hrpos : 0 < r := by dsimp [r]; exact criticalPrimeFockRadius_pos hx0
  have hrone : r ≤ 1 := by
    dsimp [r]
    exact criticalPrimeFockRadius_le_one (by linarith : 2 ≤ m) (by linarith)
  have hterm : ∀ k ∈ S,
      polynomialFockExactToeplitzLowerConstant m *
          (primeLogPowWeight 2 k *
            (criticalPrimeFockRadius m (Real.log k) / r) ^ 2) ≤
        primeLogPowWeight 2 k *
          (polynomialFockExactToeplitzAtomScale m hm (Real.log k) / r ^ 2) ∧
      primeLogPowWeight 2 k *
          (polynomialFockExactToeplitzAtomScale m hm (Real.log k) / r ^ 2) ≤
        Real.pi * (primeLogPowWeight 2 k *
          (criticalPrimeFockRadius m (Real.log k) / r) ^ 2) := by
    intro k hk
    have habs := abs_log_sub_le_of_mem_window (by simpa [S, r, x] using hk)
    have hklog : 1 ≤ Real.log k := by
      have := (abs_le.mp habs).1
      linarith
    have hlow := polynomialFockExactToeplitzAtomScale_lower hm hklog
    have hupp0 := polynomialFockExactToeplitzAtomScale_le (m := m) (x := Real.log k) hm
    have htangent := polynomialFockTangentRadius_le_criticalPrimeFockRadius
      (m := m) (x := Real.log k) (by linarith : 2 ≤ m) (by linarith : 0 < Real.log k)
    have htangentSq : polynomialFockTangentRadius m (Real.log k) ^ 2 ≤
        criticalPrimeFockRadius m (Real.log k) ^ 2 := by
      nlinarith [sq_le_sq₀ (polynomialFockTangentRadius_pos (by linarith : 0 < m)).le
        (criticalPrimeFockRadius_pos (by linarith : 0 < Real.log k)).le |>.2 htangent]
    have hupp : polynomialFockExactToeplitzAtomScale m hm (Real.log k) ≤
        Real.pi * criticalPrimeFockRadius m (Real.log k) ^ 2 :=
      hupp0.trans (mul_le_mul_of_nonneg_left htangentSq Real.pi_pos.le)
    have hw := primeLogPowWeight_two_nonneg k
    have hr2 : 0 < r ^ 2 := sq_pos_of_pos hrpos
    have hlowerDiv : polynomialFockExactToeplitzLowerConstant m *
          criticalPrimeFockRadius m (Real.log k) ^ 2 / r ^ 2 ≤
        polynomialFockExactToeplitzAtomScale m hm (Real.log k) / r ^ 2 := by
      apply div_le_div_of_nonneg_right
      · simpa [polynomialFockExactToeplitzLowerConstant, mul_assoc] using hlow
      · exact hr2.le
    have hupperDiv : polynomialFockExactToeplitzAtomScale m hm (Real.log k) / r ^ 2 ≤
        Real.pi * criticalPrimeFockRadius m (Real.log k) ^ 2 / r ^ 2 :=
      div_le_div_of_nonneg_right hupp hr2.le
    constructor
    · have := mul_le_mul_of_nonneg_left hlowerDiv hw
      calc
        polynomialFockExactToeplitzLowerConstant m *
            (primeLogPowWeight 2 k *
              (criticalPrimeFockRadius m (Real.log k) / r) ^ 2) =
            primeLogPowWeight 2 k *
              (polynomialFockExactToeplitzLowerConstant m *
                criticalPrimeFockRadius m (Real.log k) ^ 2 / r ^ 2) := by
          field_simp
        _ ≤ _ := this
    · have := mul_le_mul_of_nonneg_left hupperDiv hw
      calc
        primeLogPowWeight 2 k *
            (polynomialFockExactToeplitzAtomScale m hm (Real.log k) / r ^ 2) ≤
            primeLogPowWeight 2 k *
              (Real.pi * criticalPrimeFockRadius m (Real.log k) ^ 2 / r ^ 2) := this
        _ = Real.pi * (primeLogPowWeight 2 k *
              (criticalPrimeFockRadius m (Real.log k) / r) ^ 2) := by
          field_simp
  constructor
  · unfold criticalPrimeFockAtomicCellAverage
    unfold criticalPrimeFockExactToeplitzCellAverage
    dsimp only
    rw [Finset.mul_sum]
    simpa [x, r, S] using Finset.sum_le_sum fun k hk => (hterm k hk).1
  · unfold criticalPrimeFockAtomicCellAverage
    unfold criticalPrimeFockExactToeplitzCellAverage
    dsimp only
    rw [Finset.mul_sum]
    simpa [x, r, S] using Finset.sum_le_sum fun k hk => (hterm k hk).2

theorem exists_criticalPrimeFockExactToeplitzCellAverage_bounds
    {m : ℝ} (hm : 4 < m) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      polynomialFockExactToeplitzLowerConstant m *
          criticalPrimeFockAtomicCellAverage m n ≤
        criticalPrimeFockExactToeplitzCellAverage m (le_of_lt hm) n ∧
      criticalPrimeFockExactToeplitzCellAverage m (le_of_lt hm) n ≤
        Real.pi * criticalPrimeFockAtomicCellAverage m n := by
  obtain ⟨N, hN⟩ := eventually_atTop.1
    ((tendsto_criticalPrimeFockAdaptedCellCenter_atTop (by linarith : 0 < m)).eventually_ge_atTop 2)
  exact ⟨N, fun n hn => criticalPrimeFockExactToeplitzCellAverage_bounds
    (le_of_lt hm) (hN n hn)⟩

theorem summable_rpow_criticalPrimeFockExactToeplitzCellAverage_add_iff_atomic_add
    {m q : ℝ} (hm : 4 < m) (hq : 0 < q) {N : ℕ}
    (hN : ∀ n : ℕ, N ≤ n →
      polynomialFockExactToeplitzLowerConstant m *
          criticalPrimeFockAtomicCellAverage m n ≤
        criticalPrimeFockExactToeplitzCellAverage m (le_of_lt hm) n ∧
      criticalPrimeFockExactToeplitzCellAverage m (le_of_lt hm) n ≤
        Real.pi * criticalPrimeFockAtomicCellAverage m n) :
    Summable (fun n : ℕ =>
      criticalPrimeFockExactToeplitzCellAverage m (le_of_lt hm) (n + N) ^ q) ↔
    Summable (fun n : ℕ => criticalPrimeFockAtomicCellAverage m (n + N) ^ q) := by
  let c := polynomialFockExactToeplitzLowerConstant m
  have hc : 0 < c := polynomialFockExactToeplitzLowerConstant_pos (le_of_lt hm)
  have hlower : ∀ n : ℕ,
      c ^ q * criticalPrimeFockAtomicCellAverage m (n + N) ^ q ≤
        criticalPrimeFockExactToeplitzCellAverage m (le_of_lt hm) (n + N) ^ q := by
    intro n
    rw [← Real.mul_rpow hc.le (criticalPrimeFockAtomicCellAverage_nonneg m (n + N))]
    exact Real.rpow_le_rpow (mul_nonneg hc.le
      (criticalPrimeFockAtomicCellAverage_nonneg m (n + N)))
      (by simpa [c] using (hN (n + N) (Nat.le_add_left N n)).1) hq.le
  have hupper : ∀ n : ℕ,
      criticalPrimeFockExactToeplitzCellAverage m (le_of_lt hm) (n + N) ^ q ≤
        Real.pi ^ q * criticalPrimeFockAtomicCellAverage m (n + N) ^ q := by
    intro n
    rw [← Real.mul_rpow Real.pi_pos.le (criticalPrimeFockAtomicCellAverage_nonneg m (n + N))]
    exact Real.rpow_le_rpow
      (criticalPrimeFockExactToeplitzCellAverage_nonneg m (le_of_lt hm) (n + N))
      (hN (n + N) (Nat.le_add_left N n)).2 hq.le
  constructor
  · intro hExact
    have hscaled : Summable (fun n : ℕ =>
        c ^ q * criticalPrimeFockAtomicCellAverage m (n + N) ^ q) :=
      Summable.of_nonneg_of_le
        (fun n => mul_nonneg (Real.rpow_nonneg hc.le q)
          (Real.rpow_nonneg (criticalPrimeFockAtomicCellAverage_nonneg m (n + N)) q))
        hlower hExact
    exact (summable_mul_left_iff (Real.rpow_pos_of_pos hc q).ne').mp hscaled
  · intro hAtomic
    have hscaled : Summable (fun n : ℕ =>
        Real.pi ^ q * criticalPrimeFockAtomicCellAverage m (n + N) ^ q) :=
      hAtomic.mul_left (Real.pi ^ q)
    exact Summable.of_nonneg_of_le
      (fun n => Real.rpow_nonneg
        (criticalPrimeFockExactToeplitzCellAverage_nonneg m (le_of_lt hm) (n + N)) q)
      hupper hscaled

theorem summable_rpow_criticalPrimeFockExactToeplitzCellAverage_iff_atomic
    {m q : ℝ} (hm : 4 < m) (hq : 0 < q) :
    Summable (fun n : ℕ =>
      criticalPrimeFockExactToeplitzCellAverage m (le_of_lt hm) n ^ q) ↔
    Summable (fun n : ℕ => criticalPrimeFockAtomicCellAverage m n ^ q) := by
  obtain ⟨N, hN⟩ := exists_criticalPrimeFockExactToeplitzCellAverage_bounds hm
  have hshift :=
    summable_rpow_criticalPrimeFockExactToeplitzCellAverage_add_iff_atomic_add hm hq hN
  have hExactTail :
      Summable (fun n : ℕ =>
        criticalPrimeFockExactToeplitzCellAverage m (le_of_lt hm) (n + N) ^ q) ↔
      Summable (fun n : ℕ =>
        criticalPrimeFockExactToeplitzCellAverage m (le_of_lt hm) n ^ q) :=
    summable_nat_add_iff (f := fun n : ℕ =>
      criticalPrimeFockExactToeplitzCellAverage m (le_of_lt hm) n ^ q) N
  have hAtomicTail :
      Summable (fun n : ℕ => criticalPrimeFockAtomicCellAverage m (n + N) ^ q) ↔
      Summable (fun n : ℕ => criticalPrimeFockAtomicCellAverage m n ^ q) :=
    summable_nat_add_iff
      (f := fun n : ℕ => criticalPrimeFockAtomicCellAverage m n ^ q) N
  exact hExactTail.symm.trans (hshift.trans hAtomicTail)

theorem summable_rpow_criticalPrimeFockExactToeplitzCellAverage_iff
    {m q : ℝ} (hm : 4 < m) (hq : 0 < q) :
    Summable (fun n : ℕ =>
      criticalPrimeFockExactToeplitzCellAverage m (le_of_lt hm) n ^ q) ↔
      criticalPrimeFockSchattenThreshold m < q :=
  (summable_rpow_criticalPrimeFockExactToeplitzCellAverage_iff_atomic hm hq).trans
    (summable_rpow_criticalPrimeFockAtomicCellAverage_iff hm hq)

end

end RHTower
