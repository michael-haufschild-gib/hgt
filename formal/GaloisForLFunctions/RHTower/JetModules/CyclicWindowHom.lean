import GaloisForLFunctions.RepresentationLifting.OperatorKernels.CyclicOperatorHom
import GaloisForLFunctions.RHTower.WindowJetWeylClassification

/-!
# Cyclic probes of a window of Jordan jets

A cyclic probe with relation (X-ν)ⁿ sees exactly the generalized ν-eigenspace
of depth n. For the actual window operator its Hom dimension is the sum
of min(n,mᵢ) over resonant blocks. Thus cyclic-module maps measure both
spectral resonance and jet length.
-/

noncomputable section
namespace GaloisForLFunctions.RHTower.WindowJetWeylClassification

open Polynomial
open RepresentationLifting.OperatorKernels

/-- Module maps from a cyclic spectral probe into the window jet operator. -/
abbrev CyclicWindowHom {ι : Type*} (m : ι → ℕ) (μ : ι → ℂ) (ν : ℂ) (n : ℕ) :=
  CyclicOperatorHom (blockJordan m μ) ((X - C ν) ^ n)

/-- The exact response of every cyclic probe, including empty blocks and depth zero. -/
theorem finrank_cyclicWindowHom {ι : Type*} [Fintype ι]
    (m : ι → ℕ) (μ : ι → ℂ) (ν : ℂ) (n : ℕ) :
    Module.finrank ℂ (CyclicWindowHom m μ ν n) =
      ∑ i, if μ i = ν then min n (m i) else 0 := by
  change Module.finrank ℂ (CyclicOperatorHom (blockJordan m μ) ((X - C ν) ^ n)) = _
  rw [finrank_cyclicOperatorHom]
  have heval : aeval (blockJordan m μ) ((X - C ν) ^ n) =
      (blockJordan m μ - ν • 1) ^ n := by
    simp [Algebra.algebraMap_eq_smul_one]
  rw [heval, finrank_ker_blockJordan_pencil_pow]

end GaloisForLFunctions.RHTower.WindowJetWeylClassification

#print axioms GaloisForLFunctions.RHTower.WindowJetWeylClassification.finrank_cyclicWindowHom

