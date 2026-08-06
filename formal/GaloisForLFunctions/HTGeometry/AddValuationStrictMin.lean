import GaloisForLFunctions.HTGeometry.EisensteinRootUniformizer

/-!
# The strict minimum principle for valuations of finite sums

A finite sum in which one term has strictly smaller valuation than every other has exactly that
valuation.  The corpus already had the inequality direction, that a uniform lower bound on the
summands bounds the sum; this is the matching exact statement, which is what turns a valuation
estimate into a valuation computation.
-/

namespace GaloisForLFunctions.HTGeometry

open IsDiscreteValuationRing

variable {B : Type*} [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]

theorem lt_add_one_of_ne_zero {x : B} (hx : x ≠ 0) : addVal B x < addVal B x + 1 := by
  have htop : addVal B x ≠ ⊤ := by
    rw [Ne, addVal_eq_top_iff]
    exact hx
  obtain ⟨n, hn⟩ : ∃ n : ℕ, addVal B x = (n : ℕ∞) := ⟨_, (ENat.coe_toNat htop).symm⟩
  rw [hn]
  have hcast : ((n : ℕ) : ℕ∞) < ((n + 1 : ℕ) : ℕ∞) := by exact_mod_cast Nat.lt_succ_self n
  simpa using hcast

/-- **The strict minimum principle.**  If one summand has valuation strictly below every other,
the sum has exactly that valuation. -/
theorem addVal_sum_eq_of_strict_min {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → B)
    {i₀ : ι}
    (hi₀ : i₀ ∈ s) (hne : f i₀ ≠ 0)
    (hmin : ∀ j ∈ s.erase i₀, addVal B (f i₀) + 1 ≤ addVal B (f j)) :
    addVal B (∑ i ∈ s, f i) = addVal B (f i₀) := by
  rw [← Finset.add_sum_erase s f hi₀]
  have htail : addVal B (f i₀) + 1 ≤ addVal B (∑ i ∈ s.erase i₀, f i) :=
    le_addVal_sum _ _ _ hmin
  have hlt : addVal B (f i₀) < addVal B (∑ i ∈ s.erase i₀, f i) :=
    lt_of_lt_of_le (lt_add_one_of_ne_zero hne) htail
  rw [AddValuation.map_add_of_distinct_val _ (ne_of_lt hlt)]
  exact min_eq_left (le_of_lt hlt)

/-- The valuation of a sum with a strictly smallest term is smaller than any bound exceeded by the
other terms. -/
theorem addVal_sum_lt_of_strict_min {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → B)
    {i₀ : ι}
    (hi₀ : i₀ ∈ s) (hne : f i₀ ≠ 0) {b : ℕ∞} (hb : addVal B (f i₀) < b)
    (hmin : ∀ j ∈ s.erase i₀, addVal B (f i₀) + 1 ≤ addVal B (f j)) :
    addVal B (∑ i ∈ s, f i) < b := by
  rw [addVal_sum_eq_of_strict_min s f hi₀ hne hmin]
  exact hb

end GaloisForLFunctions.HTGeometry
