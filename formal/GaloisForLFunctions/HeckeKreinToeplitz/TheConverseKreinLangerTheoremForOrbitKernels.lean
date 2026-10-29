import GaloisForLFunctions.HeckeKreinToeplitz.TheWeilKernelIsKreinLangerOnTheFiniteStratum

/-!
# The converse Krein–Langer theorem for orbit kernels

Krein–Langer on `ℤ` says that a Hermitian kernel with finitely many negative squares is a
positive-definite kernel plus finitely many hyperbolic (and boundary) terms. For the kernels of the
theory the converse holds on the whole Hecke lattice:

**Finite index is Krein–Langer** (`isKreinLanger_orbitKernel_iff_negIndex_lt_top`). The Hecke orbit
kernel of a real test on a tempered zero configuration is Krein–Langer iff its negative index is
finite; then its spectral data are the on-line zeros (positive part) and one pair per seen right
zero. For `ζ` (`isKreinLanger_zetaKernel_iff_negIndex_lt_top`), finite index of the Weil kernel is
its Krein–Langer decomposition.

The index law and the decomposition do the work: the index counts the seen right zeros, and
finitely many seen right zeros give the decomposition explicitly. The general converse on `Γ`, for
kernels not presented by a zero configuration, remains open.
-/

open Zeta23
open GaloisForLFunctions.ArithmeticCastelnuovoSeveri (realTests)
open GaloisForLFunctions.SquareRootThreshold (TemperedConfig temperedConfig_zetaZeroConfig)

noncomputable section

namespace GaloisForLFunctions.HeckeKreinToeplitz

/-- **The converse Krein–Langer theorem for orbit kernels.** -/
theorem isKreinLanger_orbitKernel_iff_negIndex_lt_top {Z : ZeroConfig} (hZ : TemperedConfig Z)
    {f : ℝ → ℝ} (hf : f ∈ realTests) :
    IsKreinLanger (orbitKernel Z f) ↔ negIndex (orbitKernel Z f) < ⊤ := by
  rw [isKreinLanger_orbitKernel_iff hZ hf, negIndex_orbitKernel Z hZ hf, Set.encard_lt_top_iff]

/-- **For `ζ`, finite index of the Weil kernel is its Krein–Langer decomposition.** -/
theorem isKreinLanger_zetaKernel_iff_negIndex_lt_top :
    IsKreinLanger zetaKernel ↔ negIndex zetaKernel < ⊤ :=
  isKreinLanger_orbitKernel_iff_negIndex_lt_top temperedConfig_zetaZeroConfig
    cubicSpline_mem_realTests

end GaloisForLFunctions.HeckeKreinToeplitz
