import GaloisForLFunctions.RHTower.PrimeBurnolThetaModularHolonomy

/-!
# Literal Burnol--theta cubic trace cancellation

The actual source triple is `(sigma q, q, p)` with modular-fixed neutral reference `p`.
Its sigma-trace vanishes even when source-frame holonomy is nontrivial. More strongly,
every prime-depth scalar-mask trace of the literal density-weighted cubic vanishes.

The positive residue is an exact localization to reference motion and failures of modular
invariance or twisted cyclicity. These are algebraic identities and finite source statements;
no unbounded trace-domain passage, completed Xi admission, or RH conclusion is asserted.
-/


namespace GaloisForLFunctions.HTGeometry

section
variable {A G : Type*} [Ring A] [AddCommGroup G]

/-- Exact reference-drift and trace-defect decomposition for an arbitrary additive reporter. -/
theorem cubic_modular_trace_defect_localization
    (sigma : A →+* A) (tau : A →+ G) (q p : A) (hq : q * q = q) :
    tau (cubicProjectionAssociatorAlgebra (sigma q) q p) =
      tau ((sigma q - p) ^ 3 - (sigma q - sigma p) ^ 3) +
      (tau (sigma ((q - p) ^ 3)) - tau ((q - p) ^ 3)) -
      (tau (sigma q) - tau q) -
      (tau (q * sigma q * q) - tau (sigma q * q * sigma q)) := by
  have hr : sigma q * sigma q = sigma q := by rw [← map_mul, hq]
  have hid : (sigma q - q) ^ 3 =
      sigma q - q - sigma q * q * sigma q + q * sigma q * q := by
    noncomm_ring [hr, hq]
  simp only [cubicProjectionAssociatorAlgebra, hid, map_sub, map_add, map_pow]
  abel

/-- The density-weighted cubic modular displacement is one exact commutator. -/
theorem weighted_modular_projection_cube_commutator
    (c : Aˣ) (q : A) (hq : q * q = q) :
    (c : A) * (sourceModularAutomorphism c q - q) ^ 3 =
      modularCommutator q
        ((c : A) * (sourceModularAutomorphism c q - q) ^ 2) := by
  let r := sourceModularAutomorphism c q
  let d := r - q
  have hr : r * r = r := sourceModularAutomorphism_idempotent c q hq
  have hc : (c : A) * r = q * (c : A) := by
    simp [r, sourceModularAutomorphism, ← mul_assoc]
  have hcd : (c : A) * d = q * (c : A) - (c : A) * q := by
    dsimp only [d]
    rw [mul_sub, hc]
  have hqd : q * d ^ 2 = d ^ 2 * q := by
    have hqqr : q * (q * r) = q * r := by rw [← mul_assoc, hq]
    dsimp [d]
    noncomm_ring [hr, hq, hqqr]
  change (c : A) * d ^ 3 = modularCommutator q ((c : A) * d ^ 2)
  calc
    (c : A) * d ^ 3 = ((c : A) * d) * d ^ 2 := by noncomm_ring
    _ = (q * (c : A) - (c : A) * q) * d ^ 2 := by rw [hcd]
    _ = q * ((c : A) * d ^ 2) - (c : A) * (q * d ^ 2) := by noncomm_ring
    _ = modularCommutator q ((c : A) * d ^ 2) := by
      rw [hqd, modularCommutator]
      noncomm_ring

/-- Fixed-reference source cubic splits into two explicit commutators before scalarization. -/
theorem weighted_sourceFrameCubicDefect_commutators
    (c u : Aˣ) (p : A) (hp : p * p = p)
    (hfixed : sourceModularAutomorphism c p = p) :
    (c : A) * sourceFrameCubicDefect c u p =
      modularCommutator ((sourceFramedElement u p - p) ^ 3) (c : A) -
      modularCommutator (sourceFramedElement u p)
        ((c : A) *
          (sourceModularAutomorphism c (sourceFramedElement u p) -
            sourceFramedElement u p) ^ 2) := by
  let q := sourceFramedElement u p
  let r := sourceModularAutomorphism c q
  have hq : q * q = q := sourceFramedElement_idempotent u p hp
  have hlong : (c : A) * (r - p) ^ 3 = (q - p) ^ 3 * (c : A) := by
    have hmap : (r - p) ^ 3 = sourceModularAutomorphism c ((q - p) ^ 3) := by
      simp only [map_pow, map_sub, hfixed, r]
    rw [hmap]
    simp [sourceModularAutomorphism, ← mul_assoc]
  change (c : A) * cubicProjectionAssociatorAlgebra r q p = _
  rw [cubicProjectionAssociatorAlgebra, mul_sub, mul_sub, hlong]
  rw [weighted_modular_projection_cube_commutator c q hq]
  simp only [modularCommutator]
  dsimp only [q]
  abel

theorem sigmaTrace_modular_invariant
    {sigma : A →+* A} {tau : A →+ G} (h : IsSigmaTrace sigma tau) (x : A) :
    tau (sigma x) = tau x := by
  simpa only [one_mul, mul_one] using (h 1 x).symm

theorem sigmaTrace_projection_displacement_cube
    {sigma : A →+* A} {tau : A →+ G} (h : IsSigmaTrace sigma tau)
    (q : A) (hq : q * q = q) :
    tau ((sigma q - q) ^ 3) = 0 := by
  have hr : sigma q * sigma q = sigma q := by
    rw [← map_mul, hq]
  have hid : (sigma q - q) ^ 3 =
      sigma q - q - sigma q * q * sigma q + q * sigma q * q := by
    noncomm_ring [hr, hq]
  have hcyc : tau (q * sigma q * q) = tau (sigma q * q * sigma q) := by
    simpa only [mul_assoc] using h (q * sigma q) q
  rw [hid, map_add, map_sub, map_sub, sigmaTrace_modular_invariant h, hcyc]
  abel

/-- A compatible sigma-trace reads only the motion of the reference projection. -/
theorem sigmaTrace_cubic_associator_reference_drift
    {sigma : A →+* A} {tau : A →+ G} (h : IsSigmaTrace sigma tau)
    (q p : A) (hq : q * q = q) :
    tau (cubicProjectionAssociatorAlgebra (sigma q) q p) =
      tau ((sigma q - p) ^ 3 - (sigma q - sigma p) ^ 3) := by
  have hinv : tau ((sigma q - sigma p) ^ 3) = tau ((q - p) ^ 3) := by
    rw [← map_sub, ← map_pow]
    exact sigmaTrace_modular_invariant h _
  rw [cubicProjectionAssociatorAlgebra, map_sub, map_sub,
    sigmaTrace_projection_displacement_cube h q hq, sub_zero, map_sub, hinv]

theorem sigmaTrace_cubic_associator_fixed_reference
    {sigma : A →+* A} {tau : A →+ G} (h : IsSigmaTrace sigma tau)
    (q p : A) (hq : q * q = q) (hp : sigma p = p) :
    tau (cubicProjectionAssociatorAlgebra (sigma q) q p) = 0 := by
  rw [sigmaTrace_cubic_associator_reference_drift h q p hq, hp, sub_self, map_zero]

theorem sigmaTrace_sourceFrameCubicDefect_fixed_reference
    (c u : Aˣ) (p : A) (hp : p * p = p)
    (tau : A →+ G) (htau : IsSigmaTrace (sourceModularAutomorphism c) tau)
    (hfixed : sourceModularAutomorphism c p = p) :
    tau (sourceFrameCubicDefect c u p) = 0 := by
  exact sigmaTrace_cubic_associator_fixed_reference htau
    (sourceFramedElement u p) p (sourceFramedElement_idempotent u p hp) hfixed

end

section Matrix
variable {K n : Type*} [CommRing K] [Fintype n] [DecidableEq n]

theorem matrixTrace_cutoff_commutator
    (e x y : Matrix n n K) (hex : e * x = x * e) :
    Matrix.trace (e * modularCommutator x y) = 0 := by
  rw [modularCommutator, mul_sub, Matrix.trace_sub]
  have hleft : e * (x * y) = x * (e * y) := by
    rw [← mul_assoc, hex, mul_assoc]
  rw [hleft, Matrix.trace_mul_comm x (e * y), mul_assoc, sub_self]

/-- Cutoff-weighted cancellation does not require the cutoff reporter to be a sigma-trace. -/
theorem matrixTrace_cutoff_sourceFrameCubicDefect_eq_zero
    (c u : (Matrix n n K)ˣ) (p e : Matrix n n K)
    (hp : p * p = p) (hfixed : sourceModularAutomorphism c p = p)
    (hep : e * p = p * e)
    (heq : e * sourceFramedElement u p = sourceFramedElement u p * e) :
    Matrix.trace (e * (c : Matrix n n K) * sourceFrameCubicDefect c u p) = 0 := by
  have heb : Commute e (sourceFramedElement u p - p) := by
    change e * (sourceFramedElement u p - p) = (sourceFramedElement u p - p) * e
    rw [mul_sub, sub_mul, hep, heq]
  have hecube := heb.pow_right 3
  rw [mul_assoc, weighted_sourceFrameCubicDefect_commutators c u p hp hfixed,
    mul_sub, Matrix.trace_sub,
    matrixTrace_cutoff_commutator e _ _ hecube.eq,
    matrixTrace_cutoff_commutator e _ _ heq, sub_self]

end Matrix
end GaloisForLFunctions.HTGeometry

namespace RHTower
open GaloisForLFunctions.HTGeometry
noncomputable section

/-- Arbitrary complex prime-depth weights, acting identically on both theta coordinates. -/
def primeBurnolThetaPrimeDepthMask {N : ℕ} (w : Fin N → ℂ) :
    Matrix (PrimeBurnolThetaIndex N) (PrimeBurnolThetaIndex N) ℂ :=
  Matrix.diagonal (fun i => w i.1)

theorem primeBurnolThetaPrimeDepthMask_commutes_frame
    {N : ℕ} (pe : Fin N → Nat.Primes × ℕ) (a : ℝ) (w : Fin N → ℂ) :
    primeBurnolThetaPrimeDepthMask w * primeBurnolThetaFrameMatrix pe a =
      primeBurnolThetaFrameMatrix pe a * primeBurnolThetaPrimeDepthMask w := by
  ext i j
  simp only [primeBurnolThetaPrimeDepthMask, Matrix.diagonal_mul, Matrix.mul_diagonal]
  by_cases hij : i.1 = j.1
  · simp [primeBurnolThetaFrameMatrix, hij, mul_comm]
  · simp [primeBurnolThetaFrameMatrix, hij]

theorem primeBurnolThetaPrimeDepthMask_commutes_neutral
    {N : ℕ} (w : Fin N → ℂ) :
    primeBurnolThetaPrimeDepthMask w * primeBurnolThetaNeutralProjection N =
      primeBurnolThetaNeutralProjection N * primeBurnolThetaPrimeDepthMask w := by
  ext i j
  simp only [primeBurnolThetaPrimeDepthMask, Matrix.diagonal_mul, Matrix.mul_diagonal]
  by_cases hij : i.1 = j.1
  · simp [primeBurnolThetaNeutralProjection, hij, mul_comm]
  · simp [primeBurnolThetaNeutralProjection, hij]

theorem primeBurnolThetaPrimeDepthMask_commutes_framed
    {N : ℕ} (pe : Fin N → Nat.Primes × ℕ) (a : ℝ) (w : Fin N → ℂ) :
    primeBurnolThetaPrimeDepthMask w *
        sourceFramedElement (primeBurnolThetaFrameUnit pe a)
          (primeBurnolThetaNeutralProjection N) =
      sourceFramedElement (primeBurnolThetaFrameUnit pe a)
          (primeBurnolThetaNeutralProjection N) * primeBurnolThetaPrimeDepthMask w := by
  change primeBurnolThetaPrimeDepthMask w *
      (primeBurnolThetaFrameMatrix pe a * primeBurnolThetaNeutralProjection N *
        primeBurnolThetaFrameMatrix pe (-a)) = _
  rw [← mul_assoc, ← mul_assoc,
    primeBurnolThetaPrimeDepthMask_commutes_frame pe a w,
    mul_assoc _ (primeBurnolThetaPrimeDepthMask w),
    primeBurnolThetaPrimeDepthMask_commutes_neutral,
    ← mul_assoc, mul_assoc _ (primeBurnolThetaPrimeDepthMask w),
    primeBurnolThetaPrimeDepthMask_commutes_frame pe (-a) w]
  change _ = (primeBurnolThetaFrameMatrix pe a * primeBurnolThetaNeutralProjection N *
    primeBurnolThetaFrameMatrix pe (-a)) * primeBurnolThetaPrimeDepthMask w
  simp only [mul_assoc]

/-- Every literal prime-depth scalar-mask trace is zero, with all Burnol coefficients,
source depths, clock values, and theta grades unchanged. -/
theorem primeBurnolThetaPrimeDepthWeightedCubicTrace_eq_zero
    {N : ℕ} (pe : Fin N → Nat.Primes × ℕ) (hpe : Function.Injective pe)
    (kappa : Fin N → ℝ) (a : ℝ) (w : Fin N → ℂ) :
    Matrix.trace (primeBurnolThetaPrimeDepthMask w *
      (primeBurnolDoubledGramUnit pe hpe kappa :
        Matrix (PrimeBurnolThetaIndex N) (PrimeBurnolThetaIndex N) ℂ) *
      primeBurnolThetaCubicDefect pe hpe kappa a) = 0 := by
  exact matrixTrace_cutoff_sourceFrameCubicDefect_eq_zero
    (primeBurnolDoubledGramUnit pe hpe kappa) (primeBurnolThetaFrameUnit pe a)
    (primeBurnolThetaNeutralProjection N) (primeBurnolThetaPrimeDepthMask w)
    (primeBurnolThetaNeutralProjection_idempotent N)
    (primeBurnolDoubledModularAction_neutral pe hpe kappa)
    (primeBurnolThetaPrimeDepthMask_commutes_neutral w)
    (primeBurnolThetaPrimeDepthMask_commutes_framed pe a w)

theorem sigmaTrace_primeBurnolThetaCubicDefect_eq_zero
    {N : ℕ} (pe : Fin N → Nat.Primes × ℕ) (hpe : Function.Injective pe)
    (kappa : Fin N → ℝ) (a : ℝ)
    (tau : Matrix (PrimeBurnolThetaIndex N) (PrimeBurnolThetaIndex N) ℂ →+ ℂ)
    (htau : IsSigmaTrace
      (sourceModularAutomorphism (primeBurnolDoubledGramUnit pe hpe kappa)) tau) :
    tau (primeBurnolThetaCubicDefect pe hpe kappa a) = 0 := by
  exact sigmaTrace_sourceFrameCubicDefect_fixed_reference
    (primeBurnolDoubledGramUnit pe hpe kappa) (primeBurnolThetaFrameUnit pe a)
    (primeBurnolThetaNeutralProjection N) (primeBurnolThetaNeutralProjection_idempotent N)
    tau htau (primeBurnolDoubledModularAction_neutral pe hpe kappa)

/-- Nontrivial literal holonomy does not produce nonzero admitted cubic sigma-trace charge. -/
theorem sigmaTrace_primeBurnolThetaCubicAnomaly_eq_zero
    {N : ℕ} (pe : Fin N → Nat.Primes × ℕ) (hpe : Function.Injective pe)
    (kappa : Fin N → ℝ) (a : ℝ)
    (tau : Matrix (PrimeBurnolThetaIndex N) (PrimeBurnolThetaIndex N) ℂ →+ ℂ)
    (htau : IsSigmaTrace
      (sourceModularAutomorphism (primeBurnolDoubledGramUnit pe hpe kappa)) tau) :
    tau (primeBurnolThetaCubicAnomaly pe hpe kappa a) = 0 := by
  rw [← RHTower.IsSigmaTrace.map_primeBurnolThetaCubicDefect pe hpe kappa a tau htau]
  exact sigmaTrace_primeBurnolThetaCubicDefect_eq_zero pe hpe kappa a tau htau

end
end RHTower
