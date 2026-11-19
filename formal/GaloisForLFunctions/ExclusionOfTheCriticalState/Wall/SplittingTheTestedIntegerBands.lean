import GaloisForLFunctions.ExclusionOfTheCriticalState.Wall.TheLowerIntegerPrefixAtTheMovingEdge

/-!
# Splitting tested integer bands

On any bounded time cut, one can split the infinite moving-edge row at a
finite integer endpoint by taking the limit of consecutive finite bands.
-/

noncomputable section
open MeasureTheory Filter Set Topology
namespace GaloisForLFunctions.ExclusionOfTheCriticalState

/-- The integral over consecutive indices equals the difference of tested prefixes. -/
theorem finite_band_integral_sub {Φ : ℝ → ℝ} (hc : Continuous Φ) (hi : Integrable Φ)
    {k L : ℕ} (h : k ≤ L) (U M T : ℝ) :
    (∫ t in Ioc U M, finiteCriticalComplementBand Φ k L t*fractionalPrimeTest (T-t)) =
      (∫ t in Ioc U M, finiteCriticalComplementRow Φ L t*fractionalPrimeTest (T-t))-
      (∫ t in Ioc U M, finiteCriticalComplementRow Φ k t*fractionalPrimeTest (T-t)) := by
  rw [← integral_sub (tested_prefix_split_at_moving_edge hc hi L T).1.integrableOn
    (tested_prefix_split_at_moving_edge hc hi k T).1.integrableOn]
  apply integral_congr_ae (Eventually.of_forall fun t => ?_)
  dsimp only [finiteCriticalComplementRow,finiteCriticalComplementBand]
  rw [← Finset.sum_Ioc_consecutive _ (Nat.zero_le k) h,add_mul,add_sub_cancel_left]

/-- The signed infinite tail is additive at every intermediate integer endpoint. -/
theorem upper_band_integral_split {Φ : ℝ → ℝ} (hc : Continuous Φ) (hi : Integrable Φ)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ v, |Φ v| ≤ C*Real.exp (2*v)) {k L : ℕ} (h : k ≤ L)
    (U M T : ℝ) :
    (∫ t in Ioc U M, criticalComplementBand Φ k t*fractionalPrimeTest (T-t)) =
      (∫ t in Ioc U M, finiteCriticalComplementBand Φ k L t*fractionalPrimeTest (T-t))+
      (∫ t in Ioc U M, criticalComplementBand Φ L t*fractionalPrimeTest (T-t)) := by
  let lim := fun j => ∫ t in Ioc U M, criticalComplementBand Φ j t*fractionalPrimeTest (T-t)
  let band := fun i j => ∫ t in Ioc U M, finiteCriticalComplementBand Φ i j t*fractionalPrimeTest (T-t)
  have hh (i : ℕ) : Tendsto (band i) atTop (𝓝 (lim i)) :=
    finiteCriticalComplementBand_on_bounded_cut hc hC hb i U M T
  have hg : Tendsto (fun _ : ℕ => band k L) atTop (𝓝 (lim k-lim L)) := by
    apply ((hh k).sub (hh L)).congr'
    filter_upwards [eventually_ge_atTop L] with n hn
    dsimp only [band]
    rw [finite_band_integral_sub hc hi (h.trans hn),finite_band_integral_sub hc hi hn,
      finite_band_integral_sub hc hi h]
    ring
  exact sub_eq_iff_eq_add.mp (tendsto_nhds_unique hg tendsto_const_nhds)

#print axioms upper_band_integral_split
end GaloisForLFunctions.ExclusionOfTheCriticalState
