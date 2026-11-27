import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Arithmetic.Crossing.Family.Lattice.PrimeCalibration.Multiplicity.Resolution.Residual

/-! # Optimal inverse exponent for a stationary Gibbs measurement -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Lattice.PrimeCalibration.Multiplicity.Resolution

open Filter Real
open scoped Topology

private theorem positive_off_line (p q : Nat.Primes) {d : ℝ} (hd : d≠0) : 0<residual p q d :=
  lt_of_le_of_ne ((abs_nonneg _).trans (le_max_left _ _))
    (Ne.symm fun h => hd ((residual_zero p q d).mp h))

/-- Dividing the damping distance by the cube root of the measured
joint error has a finite strictly positive limit on both sides. -/
theorem inverse_limit (p q : Nat.Primes) :
    Tendsto (fun d : ℝ => |d|/(residual p q d)^(1/3 : ℝ))
      (𝓝[≠] 0) (𝓝 ((3*cubic p q)⁻¹ ^ (1/3 : ℝ))) := by
  have hc : 0<3*cubic p q := mul_pos (by norm_num) (cubic_pos p q)
  have lim := ((residual_limit p q).inv₀ hc.ne').rpow
    (tendsto_const_nhds (x := (1/3 : ℝ))) (Or.inl (inv_ne_zero hc.ne'))
  apply lim.congr'
  filter_upwards [show ∀ᶠ d : ℝ in 𝓝[≠] 0, d≠0 from self_mem_nhdsWithin] with d hd
  have cube : (|d|^3 : ℝ)^(1/3 : ℝ)=|d| := by
    rw [←rpow_natCast,←rpow_mul (abs_nonneg _)]
    norm_num
  simp only [inv_div,div_rpow (pow_nonneg (abs_nonneg _) 3)
    (positive_off_line p q hd).le,cube]

/-- For every exponent strictly above one third, the ratio of distance
to that power of the error is unbounded, even arbitrarily near the line. -/
theorem larger_exponent (p q : Nat.Primes) (a : ℝ) (ha : 1/3<a) :
    Tendsto (fun d : ℝ => |d|/(residual p q d)^a) (𝓝[≠] 0) atTop := by
  let R := residual p q
  have hc : 0<3*cubic p q := mul_pos (by norm_num) (cubic_pos p q)
  have cont : ContinuousWithinAt R ({0}ᶜ) 0 := (residual_continuous p q).continuousAt.continuousWithinAt
  have hzero : Tendsto R (𝓝[≠] 0) (𝓝 0) := by
    simpa only [(residual_zero p q 0).mpr rfl] using
      (show Tendsto R (𝓝[≠] 0) (𝓝 (residual p q 0)) from cont.tendsto)
  have punct : ∀ᶠ d : ℝ in 𝓝[≠] 0, d≠0 := self_mem_nhdsWithin
  have hp : Tendsto R (𝓝[≠] 0) (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨hzero,punct.mono fun _ hd => positive_off_line p q hd⟩
  have blow := (tendsto_rpow_neg_nhdsGT_zero (sub_neg.mpr ha)).comp hp
  apply (blow.atTop_mul_pos (rpow_pos_of_pos (inv_pos.mpr hc) _) (inverse_limit p q)).congr'
  filter_upwards [punct] with d hd
  have hr : 0<R d := positive_off_line p q hd
  change R d^(1/3-a)*(|d|/R d^(1/3 : ℝ))=|d|/R d^a
  rw [Real.rpow_sub hr]
  field_simp

#print axioms inverse_limit
#print axioms larger_exponent

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Lattice.PrimeCalibration.Multiplicity.Resolution
