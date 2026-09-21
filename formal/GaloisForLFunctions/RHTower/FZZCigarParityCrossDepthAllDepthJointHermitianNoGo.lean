import GaloisForLFunctions.RHTower.FZZCigarParityCrossDepthAllDepthJointExchange

/-!
# FZZ-P joint all-depth Hermitian source no-go

The physical FZZ screening tower is all-depth. This leaf upgrades the finite
Hermitian source obstruction to a single joint sum over two screening depths.
The joint domain is exchange-stable by the preceding exact index law. Hence a
Hermitian source kernel cannot create FZZ-P orientation at any depth.

Proof-chain role:
`all-depth source kernel -> joint source current -> oriented Ward term ->
FZZ-P`. This closes the all-depth exchange-stable Hermitian branch. A
surviving physical source must derive either an ordered/non-joint prescription
or a non-Hermitian current.
-/

open Complex
open scoped BigOperators ComplexConjugate

namespace GaloisForLFunctions.RHTower

noncomputable section

/-- Joint all-depth source accumulation of literal neutral cross-depth
covariance. Unlike an iterated ordered sum, its source domain is explicitly
exchange-stable. -/
def fzzRadialCouplingAllDepthJointComplexKernel
    (u : ℕ → ℝ) (K : ℕ → ℕ → ℂ) (v p : ℝ) : ℂ :=
  ∑' ij : ℕ × ℕ,
    K ij.1 ij.2 *
      fzzRadialCouplingCrossDepthCoherence (u ij.1) (u ij.2) v p

/-- Conjugation transports a joint source to exchanged screening depths. -/
theorem star_fzzRadialCouplingAllDepthJointComplexKernel
    (u : ℕ → ℝ) (K : ℕ → ℕ → ℂ) (v p : ℝ) :
    star (fzzRadialCouplingAllDepthJointComplexKernel u K v p) =
      ∑' ij : ℕ × ℕ,
        star (K ij.2 ij.1) *
          fzzRadialCouplingCrossDepthCoherence (u ij.1) (u ij.2) v p := by
  unfold fzzRadialCouplingAllDepthJointComplexKernel
  rw [tsum_star]
  calc
    (∑' ij : ℕ × ℕ, star (K ij.1 ij.2 *
        fzzRadialCouplingCrossDepthCoherence (u ij.1) (u ij.2) v p)) =
        ∑' ij : ℕ × ℕ, star (K ij.1 ij.2) *
          fzzRadialCouplingCrossDepthCoherence (u ij.2) (u ij.1) v p := by
            apply tsum_congr
            rintro ⟨i, j⟩
            change (starRingEnd ℂ) (K i j *
              fzzRadialCouplingCrossDepthCoherence (u i) (u j) v p) = _
            rw [map_mul]
            change star (K i j) *
              star (fzzRadialCouplingCrossDepthCoherence (u i) (u j) v p) =
                star (K i j) *
                  fzzRadialCouplingCrossDepthCoherence (u j) (u i) v p
            rw [star_fzzRadialCouplingCrossDepthCoherence]
    _ = ∑' ij : ℕ × ℕ, star (K ij.2 ij.1) *
          fzzRadialCouplingCrossDepthCoherence (u ij.1) (u ij.2) v p := by
            exact (tsum_fzzRadialCouplingNatDepthExchange (fun ij =>
              star (K ij.1 ij.2) *
                fzzRadialCouplingCrossDepthCoherence (u ij.2) (u ij.1) v p)).symm

/-- Every joint all-depth Hermitian source kernel is orientation-blind. -/
theorem fzzRadialCouplingAllDepthJointComplexKernel_im_eq_zero_of_depthHermitian
    (u : ℕ → ℝ) (K : ℕ → ℕ → ℂ) (v p : ℝ)
    (hK : ∀ i j, K i j = star (K j i)) :
    (fzzRadialCouplingAllDepthJointComplexKernel u K v p).im = 0 := by
  have hstar : star (fzzRadialCouplingAllDepthJointComplexKernel u K v p) =
      fzzRadialCouplingAllDepthJointComplexKernel u K v p := by
    rw [star_fzzRadialCouplingAllDepthJointComplexKernel]
    apply tsum_congr
    rintro ⟨i, j⟩
    rw [← hK i j]
  have him := congrArg Complex.im hstar
  change -(fzzRadialCouplingAllDepthJointComplexKernel u K v p).im =
    (fzzRadialCouplingAllDepthJointComplexKernel u K v p).im at him
  linarith

/-- **All-depth FZZ-P route kill.** No exchange-stable joint all-depth
Hermitian source yields a nonzero oriented Ward contribution. -/
theorem not_exists_fzzRadialCouplingAllDepthJointComplexKernel_im_ne_zero_of_depthHermitian :
    ¬ ∃ (u : ℕ → ℝ) (K : ℕ → ℕ → ℂ) (v p : ℝ),
      (∀ i j, K i j = star (K j i)) ∧
        (fzzRadialCouplingAllDepthJointComplexKernel u K v p).im ≠ 0 := by
  rintro ⟨u, K, v, p, hK, hnonzero⟩
  exact hnonzero
    (fzzRadialCouplingAllDepthJointComplexKernel_im_eq_zero_of_depthHermitian u K v p hK)

end

end GaloisForLFunctions.RHTower
