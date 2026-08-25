import GaloisForLFunctions.HTGeometry.PositiveSummabilityComparison

open Filter

namespace HTGeometry

theorem summable_iff_of_eventually_nat_mul_le_of_le
    (f g : ℕ → ℝ) {c C : ℝ}
    (hf : ∀ n, 0 ≤ f n) (hg : ∀ n, 0 ≤ g n) (hc : 0 < c)
    (hcomp : ∀ᶠ n : ℕ in atTop, c * f n ≤ g n ∧ g n ≤ C * f n) :
    Summable g ↔ Summable f := by
  obtain ⟨N, hN⟩ := eventually_atTop.1 hcomp
  have htail : Summable (fun n => g (n + N)) ↔
      Summable (fun n => f (n + N)) := by
    constructor
    · intro hgTail
      have hcTail : Summable (fun n => c * f (n + N)) :=
        Summable.of_nonneg_of_le
          (fun n => mul_nonneg hc.le (hf (n + N)))
          (fun n => (hN (n + N) (Nat.le_add_left N n)).1)
          hgTail
      exact (summable_mul_left_iff hc.ne').mp hcTail
    · intro hfTail
      exact Summable.of_nonneg_of_le
        (fun n => hg (n + N))
        (fun n => (hN (n + N) (Nat.le_add_left N n)).2)
        (hfTail.mul_left C)
  exact (summable_nat_add_iff N).symm.trans
    (htail.trans (summable_nat_add_iff N))

end HTGeometry

