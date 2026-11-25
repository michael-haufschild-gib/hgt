import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrescribedTimes.WindowEvent
import GaloisForLFunctions.HTGeometry.PauliOperatorNormSandwich

/-! # Operator norm control by the physical Pauli coordinates -/

open Finset Real
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.PrescribedTimes
noncomputable section

/-- Each basis term is a norm-one Pauli word, so perturbing the
couplings costs at most their total absolute change. -/
theorem numberedGenerator_sub_le {n : ℕ} (x y : PrefixIndex n→ℝ) :
    ‖numberedGenerator n x-numberedGenerator n y‖ ≤ ∑ i, |x i-y i| := by
  rw [numberedGenerator,numberedGenerator,←sum_sub_distrib]
  apply (norm_sum_le ..).trans
  calc
    _ = ∑ l : PathLabel n, |x ((pathCoeffEquiv n).symm l)-y ((pathCoeffEquiv n).symm l)| := by
      apply sum_congr rfl
      intro l _
      rw [←sub_smul,←Complex.ofReal_sub,norm_smul,norm_finitePauliMatrix,mul_one,Complex.norm_real,Real.norm_eq_abs]
    _ = _ := Equiv.sum_comp (pathCoeffEquiv n).symm (fun i => |x i-y i|)

/-- A coordinate cube around any reference Hamiltonian is contained
in its operator-norm ball after multiplication by the number of couplings. -/
theorem numberedGenerator_box {n : ℕ} (x y : PrefixIndex n→ℝ) {δ : ℝ} (h : ∀ i, |x i-y i|≤δ) :
    ‖numberedGenerator n x-numberedGenerator n y‖ ≤ (Fintype.card (PrefixIndex n):ℝ)*δ := by
  apply (numberedGenerator_sub_le x y).trans
  simpa only [sum_const,card_univ,nsmul_eq_mul] using
    sum_le_sum (s:=Finset.univ) (fun i _ => h i)

#print axioms numberedGenerator_sub_le
end
end GaloisForLFunctions.HTGeometry.PrescribedTimes
