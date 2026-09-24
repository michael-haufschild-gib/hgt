# W1C bare Clifford eigenvalue occurrence

- **ID:** W1C-bare-spectrum
- **Stage:** 5-failed
- **Type:** FALSIFIED (bare eigenvalue/compact-resolvent subroute only)
- **Source:** `WeightOneCliffordSpectralClosure.lean`; W1C in the read-only current frontier map
- **Statement:** The unchanged closed weight-one Clifford operator could realize Xi zeros as its discrete eigenvalues or through a compact-resolvent Fredholm determinant.

## No-go closure

- **Exact killing theorem/mechanism:** The natural square is maximal Fourier multiplication by `a²-(2πξ)²`. Each energy fibre is Lebesgue-null, so the square has no nonzero eigenvectors. An eigenvector of the Dirac root would square to one of the square, so it has none either. The square's resolvent at `i` is not compact. All three results are unconditional for every real mass `a` in [WeightOneCliffordSpectralNoGo.lean](../../../../formal/GaloisForLFunctions/RHTower/WeightOneCliffordSpectralNoGo.lean).
- **Strongest positive survivor:** `weightOneSpectralSquareEnergy_fibre_eq_twoPoint` classifies each attained energy fibre exactly as the two reflected frequencies `{u,-u}`. The carrier is a continuum with no point spectrum, not a hidden discrete Xi spectrum.
- **New insight:** The existing W1C Clifford relation is a free kinematic identity. Arithmetic cannot enter its unchanged eigenvalue set; it must enter a genuinely new operator/domain or a source-derived scattering denominator before any Xi occurrence claim. This does not retire W1C scattering.
- **Status:** Complete paper proof: quadratic energy equality gives `ξ²=u²`, hence `ξ=±u`; finite fibres are null; the corpus's multiplication and compact-resolvent theorems finish the operator claims. Scratch `lake --old env lean /tmp/W1CSpectralNoGo.lean` and targeted `lake --old build GaloisForLFunctions.RHTower.WeightOneCliffordSpectralNoGo:olean` passed. Leaf wired into `RHTower.lean`; no umbrella/full build.
