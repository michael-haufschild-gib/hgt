import GaloisForLFunctions.RHTower.XiDiagonalFusedResponseSupportBlindness
import GaloisForLFunctions.RHTower.XiUnitDoubleEulerResponseNegativeType

/-!
# Unit-double Euler/physical trace-class universality

The physical prime endpoint and the negative-type unit-double Euler response appear on separate
theorem surfaces.  On every prime their non-trace-class terms cancel exactly, leaving the positive
summable coefficient two times log(p) over p squared.  The identity persists for arbitrary
prime-labelled vectors in every real module.
-/

open scoped BigOperators
open ArithmeticFunction

namespace RHTower

noncomputable section

/-- Positive trace-class remainder after joining physical and unit-double Euler prime sources. -/
def xiUnitDoubleEulerPhysicalTraceRemainder (p : Nat.Primes) : ℝ :=
  2 * Real.log (p : ℝ) / (p : ℝ) ^ 2

/-- Primewise cancellation of the physical endpoint against the unit-double Euler response. -/
theorem physicalPrimeEndpointWeight_add_unitDoubleEulerResponse_eq_traceRemainder
    (p : Nat.Primes) :
    physicalPrimeEndpointWeight p +
        xiUnitDoubleEulerResponseSpectralCoefficient p =
      xiUnitDoubleEulerPhysicalTraceRemainder p := by
  have hp0 : (p : ℝ) ≠ 0 := by
    exact_mod_cast p.prop.ne_zero
  rw [physicalPrimeEndpointWeight,
    xiUnitDoubleEulerResponseSpectralCoefficient,
    ArithmeticFunction.vonMangoldt_apply_prime p.prop,
    xiUnitDoubleEulerPhysicalTraceRemainder]
  field_simp [hp0]
  ring

/-- The joined remainder is strictly positive at every prime. -/
theorem xiUnitDoubleEulerPhysicalTraceRemainder_pos (p : Nat.Primes) :
    0 < xiUnitDoubleEulerPhysicalTraceRemainder p := by
  rw [xiUnitDoubleEulerPhysicalTraceRemainder]
  have hp : (1 : ℝ) < p := by exact_mod_cast p.prop.one_lt
  exact div_pos (mul_pos (by norm_num) (Real.log_pos hp)) (sq_pos_of_pos (by positivity))

/-- The joined positive remainder is trace class over all primes. -/
theorem summable_xiUnitDoubleEulerPhysicalTraceRemainder :
    Summable xiUnitDoubleEulerPhysicalTraceRemainder := by
  have hnat := summable_abs_log_natCast_pow_mul_rpow_neg 1 2 (by norm_num)
  have hnat' : Summable (fun n : ℕ => Real.log n / (n : ℝ) ^ 2) := by
    apply hnat.congr
    intro n
    rcases n with _ | n
    · simp
    have hn : 0 < ((n + 1 : ℕ) : ℝ) := by positivity
    have hlog : 0 ≤ Real.log ((n + 1 : ℕ) : ℝ) :=
      Real.log_nonneg (by norm_num)
    rw [abs_of_nonneg hlog, pow_one, Real.rpow_neg hn.le]
    rw [show ((n + 1 : ℕ) : ℝ) ^ (2 : ℝ) =
        ((n + 1 : ℕ) : ℝ) ^ (2 : ℕ) by
      exact Real.rpow_natCast _ 2]
    field_simp
  have hprime : Summable (fun p : Nat.Primes =>
      Real.log (p : ℝ) / (p : ℝ) ^ 2) :=
    hnat'.comp_injective Subtype.val_injective
  exact (hprime.mul_left 2).congr fun p => by
    rw [xiUnitDoubleEulerPhysicalTraceRemainder]
    ring

/-- Support-blind vector lift of the primewise cancellation. -/
theorem physicalEndpoint_add_unitDoubleEulerResponse_sum_eq_traceRemainder
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (P : Finset Nat.Primes) (v : Nat.Primes → E) :
    (∑ p ∈ P, physicalPrimeEndpointWeight p • v p) +
        (∑ p ∈ P, xiUnitDoubleEulerResponseSpectralCoefficient p • v p) =
      ∑ p ∈ P, xiUnitDoubleEulerPhysicalTraceRemainder p • v p := by
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p _hp
  rw [← add_smul,
    physicalPrimeEndpointWeight_add_unitDoubleEulerResponse_eq_traceRemainder]

/-- **Unit-double Euler/physical trace-class universality.**  Primewise cancellation is positive
and globally summable. -/
theorem xiUnitDoubleEulerPhysical_traceClassUniversality :
    (∀ p : Nat.Primes,
      physicalPrimeEndpointWeight p +
          xiUnitDoubleEulerResponseSpectralCoefficient p =
        xiUnitDoubleEulerPhysicalTraceRemainder p) ∧
      (∀ p : Nat.Primes, 0 < xiUnitDoubleEulerPhysicalTraceRemainder p) ∧
      Summable xiUnitDoubleEulerPhysicalTraceRemainder :=
  ⟨physicalPrimeEndpointWeight_add_unitDoubleEulerResponse_eq_traceRemainder,
    xiUnitDoubleEulerPhysicalTraceRemainder_pos,
    summable_xiUnitDoubleEulerPhysicalTraceRemainder⟩

end

end RHTower
