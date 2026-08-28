import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenPieceTypes

/-!
# Intrinsic cardinality bound for Type-II prime products

The selected Type-II product already lies below its root cutoff.  Since every selected scale is
at least `z₀ > 1`, its number of factors satisfies Proposition 2.2's logarithmic bound directly;
no bound on the surrounding Buchstab chain is needed.
-/

namespace RHTower.Sieve

open Finset

noncomputable section

/-- A finite product of factors in `[z₀,∞)` lying below `z` has at most
`floor (log z / log z₀)` factors. -/
theorem card_le_floor_log_div_log_of_one_lt_of_prod_le
    {ι : Type*} [DecidableEq ι] (I : Finset ι) (Q : ι → ℝ) {z₀ z : ℝ}
    (hz₀ : 1 < z₀) (hQ : ∀ i ∈ I, z₀ ≤ Q i)
    (hprod : ∏ i ∈ I, Q i ≤ z) :
    I.card ≤ Nat.floor (Real.log z / Real.log z₀) := by
  have hz₀pos : 0 < z₀ := lt_trans zero_lt_one hz₀
  have hQpos : ∀ i ∈ I, 0 < Q i := fun i hi => hz₀pos.trans_le (hQ i hi)
  have hprodPos : 0 < ∏ i ∈ I, Q i := Finset.prod_pos hQpos
  have hlogQ : ∀ i ∈ I, Real.log z₀ ≤ Real.log (Q i) := by
    intro i hi
    exact Real.log_le_log hz₀pos (hQ i hi)
  have hsum : (I.card : ℝ) * Real.log z₀ ≤
      ∑ i ∈ I, Real.log (Q i) := by
    simpa using Finset.sum_le_sum hlogQ
  have hlogProd : Real.log (∏ i ∈ I, Q i) ≤ Real.log z :=
    Real.log_le_log hprodPos hprod
  rw [Real.log_prod (fun i hi => ne_of_gt (hQpos i hi))] at hlogProd
  apply Nat.le_floor
  apply (le_div_iff₀ (Real.log_pos hz₀)).2
  exact hsum.trans hlogProd

end

end RHTower.Sieve
