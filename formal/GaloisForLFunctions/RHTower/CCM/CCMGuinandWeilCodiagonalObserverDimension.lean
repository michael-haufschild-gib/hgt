/-
# Guinand--Weil codiagonal observer dimension

At Galerkin level `N`, the zero-to-positive codiagonal of a source-reflection imbalance observes
exactly `N` sine moments.  The square rigidity theorem therefore has a sharp dimension boundary.
For at most `N` distinct nondegenerate reflection orbits, vanishing of all `N` observed moments
forces every imbalance coefficient to vanish.  For more than `N` orbits, rank--nullity forces a
nonzero imbalance invisible to the entire codiagonal observer, for every placement of the horizons.

This is the finite-dimensional source of selection ambiguity in overcomplete prime packets and
continuous pole/archimedean measures.  It does not say that the whole event matrix vanishes: its
diagonal also observes the weighted cosine coordinates in Groskin's `2N+1` source quotient.  Thus
the result locates, rather than assumes away, the exact source information lost by the codiagonal.
-/
import GaloisForLFunctions.RHTower.CCM.CCMGuinandWeilReflectionOddRigidity
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

noncomputable section

open scoped BigOperators

namespace RHTower

open Matrix

/-- Rectangular sine-moment observer with `N` modes and `R` event orbits. -/
def ccmGuinandWeilRectangularSineMomentMatrix {N R : ℕ}
    (angle : Fin R → ℝ) : Matrix (Fin N) (Fin R) ℝ :=
  fun k i => Real.sin (((k : ℕ) + 1 : ℝ) * angle i)

/-- **Undercomplete codiagonal rigidity.**  If the number of nondegenerate event orbits does not
exceed the number of observed positive modes, every vanishing imbalance is zero. -/
theorem ccmGuinandWeilRectangularSineMoment_rigidity_of_le
    {N R : ℕ} (hRN : R ≤ N) (angle : Fin R → ℝ)
    (hcos : Function.Injective (fun i => Real.cos (angle i)))
    (hsin : ∀ i, Real.sin (angle i) ≠ 0)
    (imbalance : Fin R → ℝ)
    (hmoment : ∀ k : Fin N,
      ∑ i, imbalance i * Real.sin (((k : ℕ) + 1 : ℝ) * angle i) = 0) :
    imbalance = 0 := by
  apply ccmGuinandWeilSineMoment_rigidity angle hcos hsin
  intro k
  let kN : Fin N := ⟨k, lt_of_lt_of_le k.isLt hRN⟩
  simpa [kN] using hmoment kN

/-- **Overcomplete codiagonal kernel.**  More event orbits than positive modes always produce a
nonzero reflection imbalance invisible to every observed sine moment. -/
theorem ccmGuinandWeilRectangularSineMoment_exists_nonzero_kernel
    {N R : ℕ} (hNR : N < R) (angle : Fin R → ℝ) :
    ∃ imbalance : Fin R → ℝ, imbalance ≠ 0 ∧
      ∀ k : Fin N,
        ∑ i, imbalance i *
          Real.sin (((k : ℕ) + 1 : ℝ) * angle i) = 0 := by
  let T : (Fin R → ℝ) →ₗ[ℝ] (Fin N → ℝ) :=
    (ccmGuinandWeilRectangularSineMomentMatrix angle).mulVecLin
  have hdimension :
      Module.finrank ℝ (Fin N → ℝ) < Module.finrank ℝ (Fin R → ℝ) := by
    simpa using hNR
  have hker : LinearMap.ker T ≠ ⊥ :=
    T.ker_ne_bot_of_finrank_lt hdimension
  obtain ⟨imbalance, himbalance, hne⟩ :=
    Submodule.exists_mem_ne_zero_of_ne_bot hker
  refine ⟨imbalance, hne, fun k => ?_⟩
  have hzero : T imbalance = 0 := LinearMap.mem_ker.mp himbalance
  have hk := congr_fun hzero k
  simpa [T, ccmGuinandWeilRectangularSineMomentMatrix,
    Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, mul_comm] using hk

/-- Paired event packet with `R` reflection orbits carried by modes `0,...,N`. -/
def ccmGuinandWeilRectangularPairedEventPacketMatrix {N R : ℕ}
    (forward reflected horizon : Fin R → ℝ) :
    Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ :=
  ∑ r, (forward r •
      ccmGuinandWeilEventMatrix
        (fun j : Fin (N + 1) => (j : ℤ)) (horizon r) +
    reflected r •
      ccmGuinandWeilEventMatrix
        (fun j : Fin (N + 1) => (j : ℤ)) (1 - horizon r))

/-- Literal codiagonal edge law for the rectangular paired packet. -/
theorem ccmGuinandWeilRectangularPairedEventPacketMatrix_zero_edge
    {N R : ℕ} (forward reflected horizon : Fin R → ℝ) (k : Fin N) :
    ccmGuinandWeilRectangularPairedEventPacketMatrix
        forward reflected horizon (Fin.succ k) 0 =
      (∑ r, (forward r - reflected r) *
        Real.sin (((k : ℕ) + 1 : ℝ) * (2 * Real.pi * horizon r))) /
          (Real.pi * ((k : ℕ) + 1 : ℝ)) := by
  rw [ccmGuinandWeilRectangularPairedEventPacketMatrix, Matrix.sum_apply]
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  simp only [ccmGuinandWeilEventMatrix, ccmDividedDifferenceMatrix,
    Fin.succ_ne_zero, if_false]
  simp_rw [ccmGuinandWeilEventSource_one_sub]
  simp [ccmGuinandWeilEventSource]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro r _
  rw [show 2 * Real.pi * horizon r * (((k : ℕ) : ℝ) + 1) =
    (((k : ℕ) : ℝ) + 1) * (2 * Real.pi * horizon r) by ring]
  have hkpos : (0 : ℝ) < ((k : ℕ) : ℝ) + 1 := by positivity
  field_simp [Real.pi_ne_zero, ne_of_gt hkpos]
  ring

/-- More than `N` reflection orbits admit unequal forward/reflected weights whose entire
zero-to-positive codiagonal vanishes.  No horizon collision or endpoint is required. -/
theorem
    ccmGuinandWeilRectangularPairedEventPacketMatrix_exists_unbalanced_zero_codiagonal
    {N R : ℕ} (hNR : N < R) (horizon : Fin R → ℝ) :
    ∃ forward reflected : Fin R → ℝ, forward ≠ reflected ∧
      ∀ k : Fin N,
        ccmGuinandWeilRectangularPairedEventPacketMatrix
          forward reflected horizon (Fin.succ k) 0 = 0 := by
  obtain ⟨imbalance, hne, hmoment⟩ :=
    ccmGuinandWeilRectangularSineMoment_exists_nonzero_kernel hNR
      (fun i => 2 * Real.pi * horizon i)
  refine ⟨imbalance, 0, hne, fun k => ?_⟩
  rw [ccmGuinandWeilRectangularPairedEventPacketMatrix_zero_edge]
  rw [show (∑ r, (imbalance r - (0 : Fin R → ℝ) r) *
      Real.sin (((k : ℕ) + 1 : ℝ) * (2 * Real.pi * horizon r))) = 0 by
    simpa using hmoment k]
  simp

end RHTower
