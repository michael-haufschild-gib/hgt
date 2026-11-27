import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NormalizedLocalResidue
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.CoefficientPadicPlace

/-! The coefficient embedding into the p-adic algebraic closure is
continuous for the maximal-ideal adic topology. -/

noncomputable section

open IsLocalRing
open WindowedLandauTheory.BasicNotions WindowedLandauTheory.MainNotions.N
open GlobalTheory.TeichPlace GlobalTheory.LadicPlace

namespace WindowedLandauTheory.NormalizedTypes

/-- Integral coefficient values have norm at most one. Powers of the
uniformizer then give a basis on which the embedding converges to zero. -/
theorem continuous_iotaOQ (D : D7) (i : D.nd.Loc) :
    Continuous (iotaOQ D.nd D.naut i) := by
  let p := D.nd.l i
  letI : Fact p.Prime := D.nd.lPrime i
  let j := iotaOQ D.nd D.naut i
  obtain ⟨_, hj⟩ := exists_eq_residue_of_integral_order p j (D.naut.iotaQ_alg i) (D.naut.kFbar i)
  have hb (y : D.nd.O i) : ‖j y‖ ≤ 1 := (mem_padicAlgClIntegers_iff _).mp (hj y).choose
  have hp₀ : (p : D.nd.O i) ≠ 0 := by
    intro h
    have he := congrArg j h
    rw [map_natCast, map_zero] at he
    exact (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero) he
  obtain ⟨u, hu⟩ := IsDiscreteValuationRing.exists_irreducible (D.nd.O i)
  obtain ⟨e, he⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible
    (s := Ideal.span {(p : D.nd.O i)}) (by rwa [Ne, Ideal.span_singleton_eq_bot]) hu
  have heq : maximalIdeal (D.nd.O i) ^ e = Ideal.span {(p : D.nd.O i)} := by
    rw [he, hu.maximalIdeal_eq, Ideal.span_singleton_pow]
  have hq : ‖(p : PadicAlgCl p)‖ < 1 := by
    have he := PadicAlgCl.norm_extends p (p : ℚ_[p])
    rw [map_natCast] at he
    rw [he]
    exact Padic.norm_p_lt_one
  refine continuous_of_continuousAt_zero j ?_
  rw [ContinuousAt, map_zero, Metric.nhds_basis_ball.tendsto_right_iff]
  intro ε hε
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hε hq
  have hopen := (isAdic_iff.mp (D.nd.O_adic i)).1 (e * k)
  filter_upwards [hopen.mem_nhds (Ideal.zero_mem _)] with x hx
  have hx' : x ∈ Ideal.span {(p : D.nd.O i) ^ k} := by
    rwa [pow_mul, heq, Ideal.span_singleton_pow] at hx
  obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp hx'
  rw [Metric.mem_ball, dist_zero_right, map_mul, map_pow, map_natCast, norm_mul, norm_pow]
  exact (mul_le_of_le_one_left (pow_nonneg (norm_nonneg _) _) (hb b)).trans_lt hk

end WindowedLandauTheory.NormalizedTypes
