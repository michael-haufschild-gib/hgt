/-
# Trace-orthonormal coordinates for Hermitian matrix submodules

Every finite-dimensional real submodule of Hermitian matrices has a basis orthonormal for the
Hilbert--Schmidt trace pairing.  This converts spectral energy into ordinary Euclidean coefficient
energy without changing the represented matrix submodule.

Main results:
* `traceOrthonormalSubmoduleGenerator` -- a trace-orthonormal basis of a Hermitian submodule.
* `traceOrthonormalSubmoduleGenerator_mem` -- every generator remains in the submodule.
* `traceOrthonormalSubmoduleGenerator_trace_mul` -- exact trace orthonormality.
* `exists_traceOrthonormalCoordinates` -- every submodule element has exact real coordinates.
-/
import GaloisForLFunctions.HTGeometry.PhysicalLeafSpanMembership
import GaloisForLFunctions.HTGeometry.IncidenceLeakageDimensionLoss
import Mathlib.Analysis.InnerProductSpace.PiL2

open scoped Matrix

namespace GaloisForLFunctions.HTGeometry

noncomputable section

universe u

variable {I : Type u} [Fintype I]

/-- The trace of a product of Hermitian matrices is the complexification of its real part. -/
theorem trace_mul_eq_ofReal_re {A B : Matrix I I ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    (A * B).trace = (((A * B).trace.re : ℝ) : ℂ) := by
  symm
  apply Complex.conj_eq_iff_re.mp
  change star ((A * B).trace) = (A * B).trace
  rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, hB.eq, hA.eq,
    Matrix.trace_mul_comm]

/-- Vanishing Hilbert--Schmidt energy forces a complex matrix to vanish. -/
theorem eq_zero_of_hilbertSchmidt_trace {A : Matrix I I ℂ}
    (h : (Aᴴ * A).trace = 0) : A = 0 := by
  rw [trace_conjTranspose_mul_self] at h
  have hreal : (∑ i, ∑ j, ‖A j i‖ ^ 2 : ℝ) = 0 := by exact_mod_cast h
  ext j i
  have h1 := (Finset.sum_eq_zero_iff_of_nonneg
    (fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg ‖A j i‖)).mp hreal i
    (Finset.mem_univ i)
  have h2 := (Finset.sum_eq_zero_iff_of_nonneg
    (fun j _ => sq_nonneg ‖A j i‖)).mp h1 j (Finset.mem_univ j)
  simpa using (sq_eq_zero_iff.mp h2)

/-- The real Hilbert--Schmidt trace pairing is a positive-definite inner product on every real
submodule consisting of Hermitian matrices. -/
@[implicit_reducible] noncomputable def hermitianSubmoduleTraceCore
    (L : Submodule ℝ (Matrix I I ℂ))
    (hL : L ≤ selfAdjoint.submodule ℝ (Matrix I I ℂ)) :
    InnerProductSpace.Core ℝ L where
  toInner := ⟨fun A B => (A.1 * B.1).trace.re⟩
  conj_inner_symm A B := by
    simp only [conj_trivial]
    rw [Matrix.trace_mul_comm]
  re_inner_nonneg A := by
    have hAH : A.1.IsHermitian :=
      Matrix.isHermitian_iff_isSelfAdjoint.mpr (hL A.2)
    simpa [hsSqRe, hAH.eq] using hsSqRe_nonneg A.1
  definite A hA := by
    apply Subtype.ext
    apply eq_zero_of_hilbertSchmidt_trace
    have hAH : A.1.IsHermitian :=
      Matrix.isHermitian_iff_isSelfAdjoint.mpr (hL A.2)
    have hreal : ((A.1ᴴ * A.1).trace).re = 0 := by
      simpa [hAH.eq] using hA
    rw [trace_conjTranspose_mul_self, Complex.ofReal_re] at hreal
    rw [trace_conjTranspose_mul_self]
    exact_mod_cast hreal
  add_left A B C := by
    change (((A.1 + B.1) * C.1).trace).re = _
    simp [Matrix.add_mul, Matrix.trace_add]
  smul_left A B r := by
    change (((r : ℂ) • A.1 * B.1).trace).re = _
    simp [Matrix.trace_smul]

/-- A canonical choice of Hilbert--Schmidt trace-orthonormal generators for a finite real
Hermitian matrix submodule. -/
noncomputable def traceOrthonormalSubmoduleGenerator
    (L : Submodule ℝ (Matrix I I ℂ))
    (hL : L ≤ selfAdjoint.submodule ℝ (Matrix I I ℂ)) :
    Fin (Module.finrank ℝ L) → Matrix I I ℂ := by
  letI : InnerProductSpace.Core ℝ L := hermitianSubmoduleTraceCore L hL
  letI : NormedAddCommGroup L :=
    @InnerProductSpace.Core.toNormedAddCommGroup ℝ L _ _ _
      (hermitianSubmoduleTraceCore L hL)
  letI : InnerProductSpace ℝ L := InnerProductSpace.ofCore _
  exact fun i => (stdOrthonormalBasis ℝ L i).1

/-- Every trace-orthonormal generator remains in the original submodule. -/
theorem traceOrthonormalSubmoduleGenerator_mem
    (L : Submodule ℝ (Matrix I I ℂ))
    (hL : L ≤ selfAdjoint.submodule ℝ (Matrix I I ℂ))
    (i : Fin (Module.finrank ℝ L)) :
    traceOrthonormalSubmoduleGenerator L hL i ∈ L := by
  letI : InnerProductSpace.Core ℝ L := hermitianSubmoduleTraceCore L hL
  letI : NormedAddCommGroup L :=
    @InnerProductSpace.Core.toNormedAddCommGroup ℝ L _ _ _
      (hermitianSubmoduleTraceCore L hL)
  letI : InnerProductSpace ℝ L := InnerProductSpace.ofCore _
  exact (stdOrthonormalBasis ℝ L i).2

/-- Trace-orthonormal generators are Hermitian. -/
theorem traceOrthonormalSubmoduleGenerator_isHermitian
    (L : Submodule ℝ (Matrix I I ℂ))
    (hL : L ≤ selfAdjoint.submodule ℝ (Matrix I I ℂ))
    (i : Fin (Module.finrank ℝ L)) :
    (traceOrthonormalSubmoduleGenerator L hL i).IsHermitian :=
  Matrix.isHermitian_iff_isSelfAdjoint.mpr
    (hL (traceOrthonormalSubmoduleGenerator_mem L hL i))

/-- Exact Hilbert--Schmidt trace orthonormality. -/
theorem traceOrthonormalSubmoduleGenerator_trace_mul
    (L : Submodule ℝ (Matrix I I ℂ))
    (hL : L ≤ selfAdjoint.submodule ℝ (Matrix I I ℂ))
    (a b : Fin (Module.finrank ℝ L)) :
    (traceOrthonormalSubmoduleGenerator L hL a *
        traceOrthonormalSubmoduleGenerator L hL b).trace =
      if a = b then (1 : ℂ) else 0 := by
  letI : InnerProductSpace.Core ℝ L := hermitianSubmoduleTraceCore L hL
  letI : NormedAddCommGroup L :=
    @InnerProductSpace.Core.toNormedAddCommGroup ℝ L _ _ _
      (hermitianSubmoduleTraceCore L hL)
  letI : InnerProductSpace ℝ L := InnerProductSpace.ofCore _
  have hinner := orthonormal_iff_ite.mp (stdOrthonormalBasis ℝ L).orthonormal a b
  change ((traceOrthonormalSubmoduleGenerator L hL a *
    traceOrthonormalSubmoduleGenerator L hL b).trace).re =
      if a = b then 1 else 0 at hinner
  rw [trace_mul_eq_ofReal_re
    (traceOrthonormalSubmoduleGenerator_isHermitian L hL a)
    (traceOrthonormalSubmoduleGenerator_isHermitian L hL b)]
  rw [hinner]
  split_ifs <;> norm_num

/-- Every member of a finite Hermitian submodule has exact real coordinates in its
trace-orthonormal generator family. -/
theorem exists_traceOrthonormalCoordinates
    (L : Submodule ℝ (Matrix I I ℂ))
    (hL : L ≤ selfAdjoint.submodule ℝ (Matrix I I ℂ))
    {H : Matrix I I ℂ} (hH : H ∈ L) :
    ∃ θ : Fin (Module.finrank ℝ L) → ℝ,
      ∑ i, θ i • traceOrthonormalSubmoduleGenerator L hL i = H := by
  letI : InnerProductSpace.Core ℝ L := hermitianSubmoduleTraceCore L hL
  letI : NormedAddCommGroup L :=
    @InnerProductSpace.Core.toNormedAddCommGroup ℝ L _ _ _
      (hermitianSubmoduleTraceCore L hL)
  letI : InnerProductSpace ℝ L := InnerProductSpace.ofCore _
  let x : L := ⟨H, hH⟩
  let θ : Fin (Module.finrank ℝ L) → ℝ :=
    fun i => (stdOrthonormalBasis ℝ L).repr x i
  refine ⟨θ, ?_⟩
  have hsum := (stdOrthonormalBasis ℝ L).sum_repr x
  have hsumValue := congrArg L.subtype hsum
  simpa only [map_sum, map_smul, Submodule.coe_subtype,
    traceOrthonormalSubmoduleGenerator, θ, x] using hsumValue

end

end GaloisForLFunctions.HTGeometry
