import GaloisForLFunctions.RHTower.XiPoissonShellSplit
import GaloisForLFunctions.HTGeometry.AbstractSpectralFamily

/-!
# Admissible spectral families over the Xi divisor

The vertical-line criterion of `XiPoissonLineBoundRH` never uses the Poisson coordinate as such.  It
uses a family of points indexed by the Xi divisor with six properties: heights bounded away from
zero, displacements uniformly bounded, a summable weight, finite shells, stability under line
conjugation, and the identification of vanishing displacement with the critical line.

Those six properties are exactly the index-free interface `HTGeometry.AbstractSpectralFamily`, whose
involution field is instantiated here at line conjugation of divisor copies.  `SpectralFamily` is
therefore *literally* that structure at `ι = XiZeroCopy`, not a parallel copy of it: every abstract
law -- the exponential-type envelope, summability, analyticity of the trace, the bottom-shell
decomposition, Phragmén--Lindelöf decay, the graded criterion, the defect and energy criteria and
the vertical-line rigidity theorem -- applies to the Xi family verbatim, with no transport lemma in
between.

The Poisson family is the instance carried by the rest of the corpus.  The point of the abstraction
is a second instance -- the mass-shifted family `sqrt (alpha ^ 2 + a ^ 2)`, which is
prime-accessible where the Poisson family is not.
-/

open Complex
open scoped BigOperators

namespace RHTower

noncomputable section

/-- A family of spectral points admissible for the vertical-line argument: an abstract spectral
family indexed by the multiplicity copies of the Xi divisor. -/
abbrev SpectralFamily := HTGeometry.AbstractSpectralFamily XiZeroCopy

/-- The Poisson family is admissible, with line conjugation as its involution. -/
def xiPoissonFamily (h : 0 < xiPoissonBottomHeight) : SpectralFamily where
  pt := xiPoissonPoint
  inv := xiZeroCopyLineConjEquiv
  base := xiPoissonBottomHeight
  base_pos := h
  base_le := fun q => xiPoissonBottomCopy_min q
  abs_im_lt := abs_xiPoissonPoint_im_lt_half
  summable_weight := fun hσ => summable_xiPoissonWeight hσ
  shell_finite := finite_xiPoissonShell
  conj_stable := xiPoissonPoint_lineConj

end

end RHTower
