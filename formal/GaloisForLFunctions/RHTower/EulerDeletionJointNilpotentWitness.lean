import GaloisForLFunctions.RHTower.EulerDeletionJointProductOneFifth
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Tactic

/-!
# An explicit fifth-order word witness for joint Euler deletion

Six coordinates record the word `XXYYY`: `X` has entries `(0,1),(1,2)` and `Y`
has entries `(2,3),(3,4),(4,5)`, all equal to one. Direct symbolic multiplication
proves sixth powers vanish for every linear combination. The actual exponential is
therefore the displayed finite polynomial.

For the literal moduli-two-and-three six-factor source block, the exact value is
`1 - (z^5/60) • E₀₅`. The retained coordinate is nonzero, squares to zero, and is
absorbed on both sides by every block with arbitrary within-block weights. These
identities provide the fixed finite-dimensional witness for the one-fifth sharpness
argument. Infinite-product divergence still requires its summable-error proof.

No zero premise, commutation premise, numerical experiment, or external certificate
is used. This is a word-coordinate calculation and gives no RH implication.
-/

open Filter Topology
open scoped BigOperators Matrix.Norms.Operator
namespace RHTower.DeletionJointSharpness
noncomputable section
set_option maxRecDepth 4096

abbrev A := Matrix (Fin 6) (Fin 6) ℂ
local instance : TopologicalSpace A := (inferInstance : NormedRing A).toUniformSpace.toTopologicalSpace

def chain (a b : ℂ) : A :=
  !![0,a,0,0,0,0;
     0,0,a,0,0,0;
     0,0,0,b,0,0;
     0,0,0,0,b,0;
     0,0,0,0,0,b;
     0,0,0,0,0,0]

def chainSquare (a b : ℂ) : A :=
  !![0,0,a^2,0,0,0;
     0,0,0,a*b,0,0;
     0,0,0,0,b^2,0;
     0,0,0,0,0,b^2;
     0,0,0,0,0,0;
     0,0,0,0,0,0]

def chainCube (a b : ℂ) : A :=
  !![0,0,0,a^2*b,0,0;
     0,0,0,0,a*b^2,0;
     0,0,0,0,0,b^3;
     0,0,0,0,0,0;
     0,0,0,0,0,0;
     0,0,0,0,0,0]

def chainFourth (a b : ℂ) : A :=
  !![0,0,0,0,a^2*b^2,0;
     0,0,0,0,0,a*b^3;
     0,0,0,0,0,0;
     0,0,0,0,0,0;
     0,0,0,0,0,0;
     0,0,0,0,0,0]

def chainFifth (a b : ℂ) : A :=
  !![0,0,0,0,0,a^2*b^3;
     0,0,0,0,0,0;
     0,0,0,0,0,0;
     0,0,0,0,0,0;
     0,0,0,0,0,0;
     0,0,0,0,0,0]

private theorem chain_sq (a b : ℂ) : chain a b ^ 2 = chainSquare a b := by
  rw [pow_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [chain, chainSquare, Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

private theorem chain_cube (a b : ℂ) : chain a b ^ 3 = chainCube a b := by
  rw [pow_succ (chain a b) 2, chain_sq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [chain, chainSquare, chainCube, Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

private theorem chain_fourth (a b : ℂ) : chain a b ^ 4 = chainFourth a b := by
  rw [pow_succ (chain a b) 3, chain_cube]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [chain, chainCube, chainFourth, Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

private theorem chain_fifth (a b : ℂ) : chain a b ^ 5 = chainFifth a b := by
  rw [pow_succ (chain a b) 4, chain_fourth]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [chain, chainFourth, chainFifth, Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

theorem chain_sixth (a b : ℂ) : chain a b ^ 6 = 0 := by
  rw [pow_succ (chain a b) 5, chain_fifth]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [chain, chainFifth, Matrix.mul_apply, Fin.sum_univ_succ]


private theorem chain_exp_sum (a b : ℂ) :
    NormedSpace.exp (chain a b) = ∑ n ∈ Finset.range 6, (n.factorial : ℂ)⁻¹ • chain a b ^ n := by
  rw [NormedSpace.exp_eq_tsum (𝕂 := ℂ)]
  apply tsum_eq_sum
  intro n hn
  have hn' : 6 ≤ n := by simpa only [Finset.mem_range, not_lt] using hn
  rw [pow_eq_zero_of_le hn' (chain_sixth a b), smul_zero]

def chainExp (a b : ℂ) : A :=
  !![1,a,a^2/2,a^2*b/6,a^2*b^2/24,a^2*b^3/120;
     0,1,a,a*b/2,a*b^2/6,a*b^3/24;
     0,0,1,b,b^2/2,b^3/6;
     0,0,0,1,b,b^2/2;
     0,0,0,0,1,b;
     0,0,0,0,0,1]

theorem exp_chain (a b : ℂ) : NormedSpace.exp (chain a b) = chainExp a b := by
  rw [chain_exp_sum]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, pow_one,
    chain_sq, chain_cube, chain_fourth, chain_fifth]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [chain, chainSquare, chainCube, chainFourth, chainFifth, chainExp,
      Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply] <;> ring

def topWord : A := Matrix.single (⟨0, by omega⟩ : Fin 6) (⟨5, by omega⟩ : Fin 6) 1

set_option maxHeartbeats 4000000 in
theorem frozen_chain (z : ℂ) :
    chainExp z z * (chainExp (-z) z * (chainExp z (-2*z) *
      (chainExp (-z) z * (chainExp z z * chainExp (-z) (-2*z))))) =
      1 - (z^5/60) • topWord := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [chainExp, topWord, Matrix.mul_apply, Fin.sum_univ_succ,
      Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.single, Fin.ext_iff] <;> ring


def generatorX : A := chain 1 0
def generatorY : A := chain 0 1

private theorem smul_chain (z a b : ℂ) : z • chain a b = chain (z*a) (z*b) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [chain, Matrix.smul_apply]

private theorem add_chain (a b c d : ℂ) : chain a b + chain c d = chain (a+c) (b+d) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [chain, Matrix.add_apply]

theorem sourceVelocity_chain (n : ℕ) :
    DeletionJointExponential.sourceVelocity 2 3 n generatorX generatorY =
      chain (blockDeletionCoefficient 2 (n+1)) (blockDeletionCoefficient 3 (n+1)) := by
  simp [DeletionJointExponential.sourceVelocity, generatorX, generatorY, smul_chain, add_chain]

theorem variableBlock_chain (u : Fin 6 → ℂ) :
    DeletionJointProduct.variableBlock generatorX generatorY u =
      chainExp (u 0) (u 0) * (chainExp (-u 1) (u 1) * (chainExp (u 2) (-2*u 2) *
        (chainExp (-u 3) (u 3) * (chainExp (u 4) (u 4) * chainExp (-u 5) (-2*u 5))))) := by
  simp only [DeletionJointProduct.variableBlock, sourceVelocity_chain, smul_chain]
  norm_num [blockDeletionCoefficient, mul_comm]
  simp only [exp_chain]

theorem frozen_source_exact (z : ℂ) :
    DeletionJointExponential.twoThreeSourceBlock generatorX generatorY z =
      1 - (z^5/60) • topWord := by
  rw [← DeletionJointProduct.variableBlock_frozen, variableBlock_chain]
  exact frozen_chain z

theorem topWord_sq : topWord * topWord = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [topWord, Fin.ext_iff]

theorem topWord_entry : topWord 0 5 = 1 := by simp [topWord]

theorem chainExp_mul_topWord (a b : ℂ) : chainExp a b * topWord = topWord := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [chainExp, topWord, Fin.ext_iff]

theorem topWord_mul_chainExp (a b : ℂ) : topWord * chainExp a b = topWord := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [chainExp, topWord, Fin.ext_iff]

theorem variableBlock_absorbs_topWord (u : Fin 6 → ℂ) :
    DeletionJointProduct.variableBlock generatorX generatorY u * topWord = topWord ∧
    topWord * DeletionJointProduct.variableBlock generatorX generatorY u = topWord := by
  constructor
  · simp only [variableBlock_chain, mul_assoc, chainExp_mul_topWord]
  · simp only [variableBlock_chain, ← mul_assoc, topWord_mul_chainExp]

end
end RHTower.DeletionJointSharpness
