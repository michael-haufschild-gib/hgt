import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.WeakBonds.NearDiagonal.LinearCap.Carrier

/-! # All-time phase synthesis with free diagonal coefficients -/

open Finset Matrix Real
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.WeakBonds.NearDiagonal
open DiagonalSynthesis DiagonalSynthesis.CommutatorBounds
noncomputable section
variable {n : ℕ}

/-- Coordinatewise errors add in operator norm since each Pauli word
has norm one. -/
theorem shell_difference (u v : PathShell n) {r : ℝ} (hu : ∀ l, |u l-v l| ≤ r) :
    ‖pathHamiltonian u-pathHamiltonian v‖ ≤ (Fintype.card (PathLabel n):ℝ)*r :=
  coordinate_norm_bound u v hu

/-- Diagonal entries can vary at the spacing scale independently of
precision. Only transverse coefficients pay the extra factor ε. -/
theorem separated_box_synthesis :
    ∃ β ∈ Set.Ioc (0:ℝ) (1/20000), ∀ n : ℕ,
      let K := n+2
      let M : ℝ := Fintype.card (PathLabel n)
      let r := β/(M*3^K)
      ∃ w : PathShell n, (∀ l, IsDiagLabel l → 1 ≤ w l ∧ w l ≤ 2) ∧
        (∀ l, ¬IsDiagLabel l → w l=0) ∧
        ∀ ε ∈ Set.Ioc (0:ℝ) 1, ∀ u : PathShell n,
          (∀ l, IsDiagLabel l → |u l-w l| ≤ r) →
          (∀ l, ¬IsDiagLabel l → |u l| ≤ r*ε) →
          ∀ t : ℝ, HasProjectiveCircuitApproximation K ε (2^K*(2*K+1))
            (unitaryEvolution (pathHamiltonian u) t) := by
  obtain ⟨β,hβ,h⟩ := linear_separated_box
  refine ⟨β,hβ,?_⟩
  intro n K M r
  obtain ⟨w,hd,ho,hw⟩ := h n
  refine ⟨w,hd,ho,?_⟩
  intro ε hε u hdiag htrans t
  obtain ⟨z,hz,C,hC,hfit⟩ := hw ε hε u hdiag htrans t
  exact ⟨z,hz,C,hC.trans (Nat.mul_le_mul_left _ (by dsimp only [K]; omega)),hfit⟩

#print axioms separated_box_synthesis
end
end GaloisForLFunctions.HTGeometry.WeakBonds.NearDiagonal
