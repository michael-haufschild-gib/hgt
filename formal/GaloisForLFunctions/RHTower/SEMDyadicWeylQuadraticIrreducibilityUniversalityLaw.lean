import GaloisForLFunctions.RHTower.SEMDyadicWeylQuadraticIncidenceLaw
import GaloisForLFunctions.RHTower.WeylCommonEigenspaceNoGo

/-!
# SEM dyadic Weyl quadratic irreducibility

A nonsingular completed SEM boundary Weyl packet simultaneously lies on a square-divisible local
Xi incidence stratum and forbids every common character line.  The arithmetic selection rule and
representation-theoretic obstruction therefore hold on one and the same finite jet packet.
-/

open Complex Matrix Polynomial

noncomputable section

namespace RHTower

/-- Joint arithmetic and representation certificate carried by one nonsingular completed SEM
boundary Weyl packet. -/
structure SEMDyadicWeylQuadraticIrreducibilityUniversalCertificate
    (rho : ℂ) (r0 R : ℝ) (N n k : ℕ) (holonomy : ℂ) (m : ℕ) (hm : 1 ≤ m) : Prop where
  dimensionDivisibility : 2 ^ k ∣ n + 1
  dimensionLowerBound : 2 ^ k ≤ n + 1
  jetQuadraticDivisibility :
    ((2 : ℤ) ^ k) ^ (2 : ℕ) ∣
      integralJetQuadraticIndex m hm
        (completedSEMContourBoundaryZ rho r0 R N m)
  xiQuadraticDivisibility :
    ((2 : ℤ) ^ k) ^ (2 : ℕ) ∣ (((analyticOrderAt xi rho).toNat : ℤ) ^ (2 : ℕ))
  noCommonCharacterLine :
    ¬ ∃ (x : Fin (n + 1) → ℂ) (a b : ℂ),
      x ≠ 0 ∧ a ≠ 0 ∧ b ≠ 0 ∧
        truncatedJetClock n (Bottcher.dyadicRoot k) *ᵥ x = a • x ∧
        boundaryCompletedJetShift n holonomy *ᵥ x = b • x

/-- **SEM dyadic Weyl quadratic-irreducibility law.**  At positive depth and nonzero wrap, every
completed SEM boundary Weyl realization has dimension divisible by `2^k`, both its jet quadratic
index and local Xi-order square divisible by `(2^k)^(2 : ℕ)`, and no common nonzero character line for
its clock and shift generators. -/
theorem semDyadicWeyl_quadraticIrreducibilityUniversalCertificate
    {rho : ℂ} {r0 R : ℝ} {N n : ℕ} {zs : List ℂ} {u : ℂ → ℂ}
    (hsplit : SEMSplitData rho r0 R N zs u) (hlen : zs.length = n + 1)
    {k : ℕ} (hk : 0 < k) {holonomy : ℂ} (hholonomy : holonomy ≠ 0)
    {m : ℕ} (hm : 1 ≤ m)
    (hweyl :
      truncatedJetClock n (Bottcher.dyadicRoot k) *
            boundaryCompletedJetShift n holonomy =
          Bottcher.dyadicRoot k •
            (boundaryCompletedJetShift n holonomy *
              truncatedJetClock n (Bottcher.dyadicRoot k))) :
    SEMDyadicWeylQuadraticIrreducibilityUniversalCertificate
      rho r0 R N n k holonomy m hm := by
  have hdvd : 2 ^ k ∣ n + 1 := by
    rcases (dyadicBoundaryCompletedJetWeyl_iff_zero_or_dvd n k holonomy).mp hweyl with
      hzero | hdvd
    · exact False.elim (hholonomy hzero)
    · exact hdvd
  have hquad := boundaryCompletedJetWeyl_implies_zeroWrap_or_quadraticXiIncidence
    hsplit hlen k holonomy hm hweyl
  rcases hquad with hzero | hquad
  · exact False.elim (hholonomy hzero)
  · exact {
      dimensionDivisibility := hdvd
      dimensionLowerBound := Nat.le_of_dvd (by omega) hdvd
      jetQuadraticDivisibility := hquad.1
      xiQuadraticDivisibility := hquad.2
      noCommonCharacterLine :=
        no_dyadicWeyl_common_eigenvector hk
          (truncatedJetClock n (Bottcher.dyadicRoot k))
          (boundaryCompletedJetShift n holonomy) hweyl }

end RHTower

end
