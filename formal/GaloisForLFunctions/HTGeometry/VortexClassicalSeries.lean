import GaloisForLFunctions.HTGeometry.VortexWardOperator
import GaloisForLFunctions.HTGeometry.ModifiedBesselIOrder
import GaloisForLFunctions.HTGeometry.CentralBinomialSeries
import GaloisForLFunctions.HTGeometry.NegativeBinomialShell
import Mathlib.RingTheory.PowerSeries.Exp

/-!
# Vortex Ward equations across classical coefficient families

The recurrence-to-Ward-operator mechanism of arXiv:2609.09298, Section 2.9, applies
unchanged to the existing reciprocal-Gamma Bessel coefficients, central-binomial sequence,
negative-binomial shells, and exponential power series. In particular, reciprocal Gamma
preserves the Bessel equation at every complex order without a resonant correction.
-/

namespace GaloisForLFunctions.HTGeometry
noncomputable section
open PowerSeries

/-- Formal degree series of the corpus's reciprocal-Gamma Bessel coefficients. -/
def vortexBesselSeries (a : ℝ) (z : ℂ) : PowerSeries ℂ :=
  PowerSeries.mk (fun n => modifiedBesselIOrderCoreTerm a n z)

/-- Reciprocal Gamma, unlike totalized Pochhammer division, preserves the unregularized
Ward equation at every complex order. -/
theorem vortexBessel_ward (a : ℝ) (z : ℂ) :
    vortexWard (fun n => (n : ℂ) * (z + n)) (fun _ => (a : ℂ) ^ (2 : ℕ))
      (vortexBesselSeries a z) = 0 := by
  apply (vortexWard_zero_iff _ _ _).2
  refine ⟨by simp, fun n => ?_⟩
  simpa only [vortexBesselSeries, coeff_mk, Nat.cast_add, Nat.cast_one, mul_comm] using
    modifiedBesselIOrderCoreTerm_succ_mul a n z

/-- Formal Bessel equation in the squared radial coordinate. -/
theorem vortexBessel_differential_equation (a : ℝ) (z : ℂ) :
    X * derivative ℂ (derivative ℂ (vortexBesselSeries a z)) +
      C (z + 1) * derivative ℂ (vortexBesselSeries a z) -
        C ((a : ℂ) ^ (2 : ℕ)) * vortexBesselSeries a z = 0 := by
  ext n
  cases n with
  | zero =>
    have h := modifiedBesselIOrderCoreTerm_succ_mul a 0 z
    rw [map_sub, map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul]
    simp only [coeff_zero_X_mul, zero_add, coeff_derivative, vortexBesselSeries,
      coeff_mk, Nat.cast_zero, mul_one, map_zero]
    norm_num at h
    linear_combination h
  | succ n =>
    have h := modifiedBesselIOrderCoreTerm_succ_mul a (n + 1) z
    rw [map_sub, map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul]
    simp only [coeff_succ_X_mul, coeff_derivative, vortexBesselSeries, coeff_mk, map_zero]
    push_cast at h ⊢
    linear_combination h

/-- Central-binomial coefficients carry the same first-order Ward structure. -/
theorem vortexCentralBinomial_ward :
    vortexWard (fun n => (n : ℂ)) (fun n => 2 * (2 * (n : ℂ) + 1))
      (PowerSeries.mk (fun n => (Nat.centralBinom n : ℂ))) = 0 := by
  apply (vortexWard_zero_iff _ _ _).2
  refine ⟨by simp, fun n => ?_⟩
  simpa only [coeff_mk, Nat.cast_add, Nat.cast_one, Nat.cast_mul, Nat.cast_ofNat] using
    congrArg (fun k : ℕ => (k : ℂ)) (Nat.succ_mul_centralBinom_succ n)

/-- Every positive-order negative-binomial shell in the corpus satisfies a closed Ward equation. -/
theorem vortexNegativeBinomialShell_ward (a : ℂ) (m : ℕ) :
    vortexWard (fun n => (n : ℂ)) (fun n => -a * ((m : ℂ) + 1 + n))
      (shellSeries a (m + 1)) = 0 := by
  apply (vortexWard_zero_iff _ _ _).2
  refine ⟨by simp, fun n => ?_⟩
  have hchoose := congrArg (fun k : ℕ => (k : ℂ)) (Nat.choose_mul_succ_eq (m + n) m)
  have hsub : m + n + 1 - m = n + 1 := by omega
  rw [hsub] at hchoose
  push_cast at hchoose
  rw [coeff_shellSeries a (Nat.succ_pos m), coeff_shellSeries a (Nat.succ_pos m)]
  simp only [Nat.succ_sub_one, Nat.cast_add, Nat.cast_one, pow_succ]
  have hind : m + (n + 1) = m + n + 1 := by omega
  rw [hind]
  linear_combination -((-a) ^ n * (-a)) * hchoose

/-- Exponential power series realizes the factorial-normalized constant-step Ward equation. -/
theorem vortexExponential_ward (a : ℂ) :
    vortexWard (fun n => (n : ℂ)) (fun _ => a) (rescale a (PowerSeries.exp ℂ)) = 0 := by
  have h : vortexWard (fun n => (n : ℂ)) (fun _ => 1) (PowerSeries.exp ℂ) = 0 := by
    rw [vortexWard, vortexDiagonal_euler, PowerSeries.derivative_exp]
    have hd : vortexDiagonal (fun _ => 1) (PowerSeries.exp ℂ) = PowerSeries.exp ℂ := by
      ext n
      simp
    rw [hd, sub_self]
  simpa only [mul_one, h, map_zero] using
    vortexWard_rescale (fun n => (n : ℂ)) (fun _ => 1) a (PowerSeries.exp ℂ)

end
end GaloisForLFunctions.HTGeometry
