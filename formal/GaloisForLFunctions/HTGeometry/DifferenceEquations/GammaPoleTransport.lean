import GaloisForLFunctions.HTGeometry.GammaFactorialAsymptoticConnection

/-!
# Conservative transport along the Gamma pole clock

Transport from pole index `r` through `N` links is `r!/(r+N)!`.
The cocycle identity gives the parallel-trajectory coboundary law, and
every positive integer stride retains the zero limit of the Gamma scale.
These specialize the trajectory laws in *New Directions in Irrationality*
to the reciprocal-Gamma pole connection.
-/

namespace GaloisForLFunctions.HTGeometry

open Finset Filter
open scoped Topology

/-- Transport through `N` Gamma pole-clock links starting at index `r`. -/
noncomputable def gammaPoleTransport (r N : ℕ) : ℝ :=
  (r.factorial : ℝ) / ((r + N).factorial : ℝ)

theorem gammaPoleTransport_pos (r N : ℕ) : 0 < gammaPoleTransport r N := by
  unfold gammaPoleTransport
  positivity

@[simp] theorem gammaPoleTransport_zero (r : ℕ) : gammaPoleTransport r 0 = 1 := by
  simp [gammaPoleTransport, Nat.factorial_ne_zero]

/-- The one-step transport is the source-defined Gamma connection link. -/
theorem gammaPoleTransport_one (r : ℕ) :
    gammaPoleTransport r 1 = gammaFactorialConnectionLink r := by
  unfold gammaPoleTransport gammaFactorialConnectionLink
  rw [Nat.factorial_succ]
  push_cast
  field_simp

/-- Concatenating pole intervals multiplies their transports. -/
theorem gammaPoleTransport_add (r M N : ℕ) :
    gammaPoleTransport r (M + N) = gammaPoleTransport r M * gammaPoleTransport (r + M) N := by
  unfold gammaPoleTransport
  rw [Nat.add_assoc]
  field_simp

/-- The factorial ratio is the literal product of the intervening connection links. -/
theorem gammaPoleTransport_eq_prod (r N : ℕ) :
    gammaPoleTransport r N = ∏ j ∈ range N, gammaFactorialConnectionLink (r + j) := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [gammaPoleTransport_add, gammaPoleTransport_one, ih, prod_range_succ]

/-- Integral shifts are coboundaries of the same Gamma pole connection. -/
theorem gammaPoleTransport_parallel (r k N : ℕ) :
    gammaPoleTransport r k * gammaPoleTransport (r + k) N =
      gammaPoleTransport r N * gammaPoleTransport (r + N) k := by
  rw [← gammaPoleTransport_add, ← gammaPoleTransport_add, Nat.add_comm k N]

/-- The parallel-trajectory law at the level of the individual links. -/
theorem gammaPoleLink_coboundary (r k : ℕ) :
    gammaPoleTransport r k * gammaFactorialConnectionLink (r + k) =
      gammaFactorialConnectionLink r * gammaPoleTransport (r + 1) k := by
  simpa only [gammaPoleTransport_one] using gammaPoleTransport_parallel r k 1

/-- Every positive integer stride has the same limiting pole scale. -/
theorem gammaPoleTransport_stride_tendsto_zero (r m : ℕ) :
    Tendsto (fun N => gammaPoleTransport r ((m + 1) * N)) atTop (𝓝 0) := by
  have hind : Tendsto (fun N : ℕ => r + (m + 1) * N) atTop atTop := by
    apply tendsto_atTop.mpr
    intro b
    refine eventually_atTop.mpr ⟨b, ?_⟩
    intro N hN
    rw [Nat.add_mul, Nat.one_mul]
    omega
  have h := (gammaFactorialConnectionTransport_tendsto_zero.comp hind).const_mul
    (r.factorial : ℝ)
  simpa only [gammaPoleTransport, gammaFactorialConnectionTransport, mul_zero, div_eq_mul_inv,
    one_mul] using h

#print axioms gammaPoleTransport_eq_prod
#print axioms gammaPoleTransport_parallel
#print axioms gammaPoleTransport_stride_tendsto_zero

end GaloisForLFunctions.HTGeometry
