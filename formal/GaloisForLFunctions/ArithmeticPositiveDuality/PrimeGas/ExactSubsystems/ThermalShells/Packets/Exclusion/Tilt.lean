import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.ThermalShells.Packets.Occupation.Atoms

/-! # The one-draw law conditional on two coincident prime labels -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.ThermalShells.Packets.Exclusion

open Occupation Finset Real Filter Topology
open Set (Ioi)
open BinaryOrientation.LargestPrime.Bands

/-- Independent draws conditional on equality have exactly the Gibbs law at twice the inverse temperature. -/
theorem collision_tilt {S : Finset Nat.Primes} {P : Finset ℕ} (hp : P.Nonempty)
    (him : (modes S P).image serial = P) (b t : ℝ) (p : ↥S) :
    draw S P b t p^2 = (∑ r, draw S P b t r^2)*draw S P (2*b) t p := by
  rw [squared_draw him]
  by_cases hm : p ∈ modes S P
  · simp only [draw,if_pos hm,div_pow]
    have he : shifted b t (serial p)^2 = shifted (2*b) t (serial p) := by
      rw [shifted,shifted,sq,← exp_add]; congr 1; ring
    rw [he]
    field_simp [(mass_pos (shifted_pos b t) hp).ne',(mass_pos (shifted_pos (2*b) t) hp).ne']
  · simp only [draw,if_neg hm,zero_pow (Nat.succ_ne_zero 1),mul_zero]

def collision (c d D k b : ℝ) (h : Ioi (0:ℝ)) :=
  let t := c/h.val
  ∑ r, draw (added c d h) (both D k t) b t r^2

theorem collision_vanishes {c d D k : ℝ} (hc : 0 < c) (hcd : c < d) (hD : 0 < D) (hk : 0 < k) (b : ℝ) :
    Tendsto (collision c d D k b) criticalApproach (𝓝 0) := by
  have H := (squared_draw_limit hc hcd hD hk b).mul (scale_zero.comp (translation_limit hc))
  rw [mul_zero] at H
  apply H.congr
  intro h
  exact div_mul_cancel₀ _ (div_pos (sq_pos_of_pos (div_pos hc h.property)) (exp_pos _) : 0 < scale (c/h.val)).ne'

#print axioms collision_tilt
#print axioms collision_vanishes

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.ThermalShells.Packets.Exclusion
