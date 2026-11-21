import GaloisForLFunctions.HTGeometry.Quantum.LinearResponse.CommutatorGreenCovariance
import GaloisForLFunctions.HTGeometry.Quantum.LinearResponse.AbelSymmetricResolvent

/-!
# Parity-resolved measurements

A symmetry that fixes the probe and reverses the perturbation
exchanges its two readings. Symmetric observations lose the sign,
while antisymmetric observations retain it.
-/

open Matrix Set
open scoped Matrix

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {H T X : Matrix ι ι ℂ}

/-- The symmetric part of a reading under the chosen automorphism. -/
def matrixEvenPart (e : Matrix ι ι ℂ ≃⋆ₐ[ℂ] Matrix ι ι ℂ) (Y : Matrix ι ι ℂ) :
    Matrix ι ι ℂ := (2 : ℂ)⁻¹ • (Y + e Y)

/-- The antisymmetric part of a reading under the chosen automorphism. -/
def matrixOddPart (e : Matrix ι ι ℂ ≃⋆ₐ[ℂ] Matrix ι ι ℂ) (Y : Matrix ι ι ℂ) :
    Matrix ι ι ℂ := (2 : ℂ)⁻¹ • (Y - e Y)

private theorem map_abelResponse_add_odd (e : Matrix ι ι ℂ ≃⋆ₐ[ℂ] Matrix ι ι ℂ)
    (hH : H.IsHermitian) (hT : T.IsHermitian) (h0 : e H = H) (h1 : e T = -T)
    (hX : e X = X) (μ : ℝ) (ε : Ioi (0 : ℝ)) :
    e (hamiltonianDampedGapResponse (hH.add hT) μ ε X) =
      hamiltonianDampedGapResponse (hH.sub hT) μ ε X := by
  have he : e (H + T) = H - T := by rw [map_add, h0, h1, sub_eq_add_neg]
  have he' := map_hamiltonianDampedGapResponse_of_eq e (hH.add hT) (hH.sub hT) he μ ε X
  rwa [hX] at he'

private theorem map_abelResponse_sub_odd (e : Matrix ι ι ℂ ≃⋆ₐ[ℂ] Matrix ι ι ℂ)
    (hH : H.IsHermitian) (hT : T.IsHermitian) (h0 : e H = H) (h1 : e T = -T)
    (hX : e X = X) (μ : ℝ) (ε : Ioi (0 : ℝ)) :
    e (hamiltonianDampedGapResponse (hH.sub hT) μ ε X) =
      hamiltonianDampedGapResponse (hH.add hT) μ ε X := by
  have he : e (H - T) = H + T := by rw [map_sub, h0, h1, sub_neg_eq_add]
  have he' := map_hamiltonianDampedGapResponse_of_eq e (hH.sub hT) (hH.add hT) he μ ε X
  rwa [hX] at he'

/-- The two parity components realize the mean and half-difference of
opposite perturbation responses. -/
theorem abelParityReadout_eq_symmetric_antisymmetric
    (e : Matrix ι ι ℂ ≃⋆ₐ[ℂ] Matrix ι ι ℂ)
    (hH : H.IsHermitian) (hT : T.IsHermitian) (h0 : e H = H) (h1 : e T = -T)
    (hX : e X = X) (ε : Ioi (0 : ℝ)) :
    matrixEvenPart e (hamiltonianDampedGapResponse (hH.add hT) 0 ε X) =
        abelSymmetricResponse hH hT ε X ∧
      matrixOddPart e (hamiltonianDampedGapResponse (hH.add hT) 0 ε X) =
        abelAntisymmetricResponse hH hT ε X := by
  have he := map_abelResponse_add_odd e hH hT h0 h1 hX 0 ε
  constructor
  · simp only [matrixEvenPart, abelSymmetricResponse, he]
  · simp only [matrixOddPart, abelAntisymmetricResponse, he]

/-- Symmetric readings of invariant probes cannot distinguish the
sign of an antisymmetric Hamiltonian perturbation. -/
theorem abelEvenReadout_add_eq_sub
    (e : Matrix ι ι ℂ ≃⋆ₐ[ℂ] Matrix ι ι ℂ)
    (hH : H.IsHermitian) (hT : T.IsHermitian) (h0 : e H = H) (h1 : e T = -T)
    (hX : e X = X) (μ : ℝ) (ε : Ioi (0 : ℝ)) :
    matrixEvenPart e (hamiltonianDampedGapResponse (hH.add hT) μ ε X) =
      matrixEvenPart e (hamiltonianDampedGapResponse (hH.sub hT) μ ε X) := by
  rw [matrixEvenPart, matrixEvenPart, map_abelResponse_add_odd e hH hT h0 h1 hX μ ε,
    map_abelResponse_sub_odd e hH hT h0 h1 hX μ ε, add_comm]

/-- The complementary readings reverse sign with the perturbation. -/
theorem abelOddReadout_add_eq_neg_sub
    (e : Matrix ι ι ℂ ≃⋆ₐ[ℂ] Matrix ι ι ℂ)
    (hH : H.IsHermitian) (hT : T.IsHermitian) (h0 : e H = H) (h1 : e T = -T)
    (hX : e X = X) (μ : ℝ) (ε : Ioi (0 : ℝ)) :
    matrixOddPart e (hamiltonianDampedGapResponse (hH.add hT) μ ε X) =
      -matrixOddPart e (hamiltonianDampedGapResponse (hH.sub hT) μ ε X) := by
  rw [matrixOddPart, matrixOddPart, map_abelResponse_add_odd e hH hT h0 h1 hX μ ε,
    map_abelResponse_sub_odd e hH hT h0 h1 hX μ ε, ← smul_neg, neg_sub]

/-- A nonzero antisymmetric perturbation gives a genuine ambiguity
beyond the scalar energy shift. -/
theorem not_abelOddSign_scalarDifference (e : Matrix ι ι ℂ ≃⋆ₐ[ℂ] Matrix ι ι ℂ)
    (hodd : e T = -T) (hT : T ≠ 0) : ¬ ∃ c : ℂ, (H + T) - (H - T) = c • 1 := by
  rintro ⟨c, hc⟩
  rw [show (H + T) - (H - T) = (2 : ℂ) • T from by rw [two_smul]; abel] at hc
  have he := congrArg e hc
  rw [map_smul, map_smul, map_one, hodd] at he
  have hn : -T = T := by
    have hd : (2 : ℂ) • (-T - T) = 0 := by rw [smul_sub, he, hc, sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero.mp hd).resolve_left two_ne_zero)
  have hz : (2 : ℂ) • T = 0 := by
    calc
      _ = T + T := two_smul ℂ T
      _ = -T + T := congrArg (fun Z => Z + T) hn.symm
      _ = 0 := neg_add_cancel T
  exact hT ((smul_eq_zero.mp hz).resolve_left two_ne_zero)

#print axioms abelParityReadout_eq_symmetric_antisymmetric
#print axioms abelEvenReadout_add_eq_sub
#print axioms abelOddReadout_add_eq_neg_sub
#print axioms not_abelOddSign_scalarDifference

end

end GaloisForLFunctions.HTGeometry
