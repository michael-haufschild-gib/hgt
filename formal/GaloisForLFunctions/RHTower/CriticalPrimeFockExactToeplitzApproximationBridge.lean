import GaloisForLFunctions.RHTower.CriticalPrimeFockExactToeplitzCellAverage
import GaloisForLFunctions.RHTower.SchattenApproximation

open Filter

namespace RHTower

noncomputable section

/-- Exact localization conclusion needed from doubling-Fock Toeplitz theory: approximation numbers
of the concrete positive Toeplitz operator are eventually comparable to its literal adapted
Toeplitz cell averages. -/
def HasCriticalPrimeFockExactToeplitzApproximationCellComparison
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (T : H →L[ℂ] H) (m : ℝ) (hm : 4 ≤ m) : Prop :=
  ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ᶠ n : ℕ in atTop,
    c * criticalPrimeFockExactToeplitzCellAverage m hm n ≤ approxNumber T n ∧
      approxNumber T n ≤ C * criticalPrimeFockExactToeplitzCellAverage m hm n

theorem summable_rpow_approxNumber_add_iff_exactToeplitzCellAverage_add
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {T : H →L[ℂ] H} {m q c C : ℝ} (hm : 4 ≤ m) (hq : 0 < q) (hc : 0 < c)
    (hC : 0 < C) {N : ℕ}
    (hN : ∀ n : ℕ, N ≤ n →
      c * criticalPrimeFockExactToeplitzCellAverage m hm n ≤ approxNumber T n ∧
        approxNumber T n ≤ C * criticalPrimeFockExactToeplitzCellAverage m hm n) :
    Summable (fun n : ℕ => approxNumber T (n + N) ^ q) ↔
      Summable (fun n : ℕ =>
        criticalPrimeFockExactToeplitzCellAverage m hm (n + N) ^ q) := by
  have hlower : ∀ n : ℕ,
      c ^ q * criticalPrimeFockExactToeplitzCellAverage m hm (n + N) ^ q ≤
        approxNumber T (n + N) ^ q := by
    intro n
    rw [← Real.mul_rpow hc.le
      (criticalPrimeFockExactToeplitzCellAverage_nonneg m hm (n + N))]
    exact Real.rpow_le_rpow (mul_nonneg hc.le
      (criticalPrimeFockExactToeplitzCellAverage_nonneg m hm (n + N)))
      (hN (n + N) (Nat.le_add_left N n)).1 hq.le
  have hupper : ∀ n : ℕ,
      approxNumber T (n + N) ^ q ≤
        C ^ q * criticalPrimeFockExactToeplitzCellAverage m hm (n + N) ^ q := by
    intro n
    rw [← Real.mul_rpow hC.le
      (criticalPrimeFockExactToeplitzCellAverage_nonneg m hm (n + N))]
    exact Real.rpow_le_rpow (approxNumber_nonneg T (n + N))
      (hN (n + N) (Nat.le_add_left N n)).2 hq.le
  constructor
  · intro hT
    have hscaled : Summable (fun n : ℕ =>
        c ^ q * criticalPrimeFockExactToeplitzCellAverage m hm (n + N) ^ q) :=
      Summable.of_nonneg_of_le
        (fun n => mul_nonneg (Real.rpow_nonneg hc.le q)
          (Real.rpow_nonneg
            (criticalPrimeFockExactToeplitzCellAverage_nonneg m hm (n + N)) q))
        hlower hT
    exact (summable_mul_left_iff (Real.rpow_pos_of_pos hc q).ne').mp hscaled
  · intro hA
    have hscaled : Summable (fun n : ℕ =>
        C ^ q * criticalPrimeFockExactToeplitzCellAverage m hm (n + N) ^ q) :=
      hA.mul_left (C ^ q)
    exact Summable.of_nonneg_of_le
      (fun n => Real.rpow_nonneg (approxNumber_nonneg T (n + N)) q)
      hupper hscaled

theorem HasCriticalPrimeFockExactToeplitzApproximationCellComparison.memSchattenClass_iff
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {T : H →L[ℂ] H} {m q : ℝ}
    (hm : 4 < m) (hq : 0 < q)
    (hT : HasCriticalPrimeFockExactToeplitzApproximationCellComparison T m (le_of_lt hm)) :
    MemSchattenClass q T ↔ criticalPrimeFockSchattenThreshold m < q := by
  obtain ⟨c, C, hc, hC, hev⟩ := hT
  obtain ⟨N, hN⟩ := eventually_atTop.1 hev
  have hshift :
      Summable (fun n : ℕ => approxNumber T (n + N) ^ q) ↔
        Summable (fun n : ℕ =>
          criticalPrimeFockExactToeplitzCellAverage m (le_of_lt hm) (n + N) ^ q) :=
    summable_rpow_approxNumber_add_iff_exactToeplitzCellAverage_add
      (le_of_lt hm) hq hc hC hN
  have happroxTail :
      Summable (fun n : ℕ => approxNumber T (n + N) ^ q) ↔
        Summable (fun n : ℕ => approxNumber T n ^ q) :=
    summable_nat_add_iff (f := fun n : ℕ => approxNumber T n ^ q) N
  have hcellTail :
      Summable (fun n : ℕ =>
        criticalPrimeFockExactToeplitzCellAverage m (le_of_lt hm) (n + N) ^ q) ↔
      Summable (fun n : ℕ =>
        criticalPrimeFockExactToeplitzCellAverage m (le_of_lt hm) n ^ q) :=
    summable_nat_add_iff
      (f := fun n : ℕ =>
        criticalPrimeFockExactToeplitzCellAverage m (le_of_lt hm) n ^ q) N
  change Summable (fun n : ℕ => approxNumber T n ^ q) ↔ _
  exact happroxTail.symm.trans
    (hshift.trans (hcellTail.trans
      (summable_rpow_criticalPrimeFockExactToeplitzCellAverage_iff hm hq)))

end

end RHTower
