import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ContinuityOfCoefficientEmbedding

/-! The maximal-ideal adic topology on the integral model is detected by
the norm of the p-adic coefficient embedding. -/

noncomputable section

open Filter IsLocalRing
open scoped Topology
open WindowedLandauTheory.BasicNotions WindowedLandauTheory.MainNotions.N
open GlobalTheory.TeichPlace GlobalTheory.LadicPlace

namespace WindowedLandauTheory.NormalizedTypes

/-- Continuity into the integral model can be checked after coefficient
extension. A unit has norm one, so the norm detects the uniformizer exponent. -/
theorem continuous_of_continuous_iotaOQ (D : D7) (i : D.nd.Loc)
    {Y : Type*} [TopologicalSpace Y] {f : Y → D.nd.O i}
    (hf : Continuous fun y => iotaOQ D.nd D.naut i (f y)) : Continuous f := by
  let p := D.nd.l i
  letI : Fact p.Prime := D.nd.lPrime i
  let j := iotaOQ D.nd D.naut i
  obtain ⟨_, hj⟩ := exists_eq_residue_of_integral_order p j (D.naut.iotaQ_alg i) (D.naut.kFbar i)
  have hb (y : D.nd.O i) : ‖j y‖ ≤ 1 := (mem_padicAlgClIntegers_iff _).mp (hj y).choose
  have hunit (b : (D.nd.O i)ˣ) : ‖j (b : D.nd.O i)‖ = 1 := by
    refine le_antisymm (hb b) ?_
    have e := mul_le_mul_of_nonneg_left (hb (↑b⁻¹ : D.nd.O i)) (norm_nonneg (j b))
    simpa only [mul_one, ← norm_mul, ← map_mul, Units.mul_inv, map_one, norm_one] using e
  obtain ⟨u, hu⟩ := IsDiscreteValuationRing.exists_irreducible (D.nd.O i)
  have hj₀ : Function.Injective j := (D.naut.iotaQ i).injective.comp
    (IsFractionRing.injective (D.nd.O i) (FractionRing (D.nd.O i)))
  have hu₀ : 0 < ‖j u‖ := norm_pos_iff.mpr (by
    intro h
    exact hu.ne_zero (hj₀ (h.trans (map_zero j).symm)))
  have hsmall (n : ℕ) {x : D.nd.O i} (hx : ‖j x‖ < ‖j u‖ ^ n) :
      x ∈ maximalIdeal (D.nd.O i) ^ n := by
    by_cases hx₀ : x = 0
    · exact hx₀ ▸ Ideal.zero_mem _
    obtain ⟨a, b, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx₀ hu
    rw [map_mul, map_pow, norm_mul, norm_pow, hunit, one_mul] at hx
    have hna : n ≤ a := by
      by_contra! h
      exact (not_lt_of_ge (pow_le_pow_of_le_one (norm_nonneg _) (hb u) h.le)) hx
    rw [hu.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    exact (pow_dvd_pow u hna).mul_left _
  rw [continuous_iff_continuousAt]
  intro y
  rw [ContinuousAt, ← tendsto_sub_nhds_zero_iff,
    (D.nd.O_adic i).hasBasis_nhds_zero.tendsto_right_iff]
  intro n _
  have hh : ContinuousAt (fun z => j (f z)) y := hf.continuousAt
  have he := Metric.tendsto_nhds.mp hh (‖j u‖ ^ n) (pow_pos hu₀ _)
  filter_upwards [he] with z hz
  apply hsmall n
  rw [map_sub]
  simpa only [dist_eq_norm] using hz

end WindowedLandauTheory.NormalizedTypes
