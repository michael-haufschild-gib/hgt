# Arithmetic reflection of the full Mayer spectral family

- **Stage:** 5-failed
- **Wall:** Γ25
- **Failed claim:** On a nonempty open subset of `0<Re w<1`, the actual
  determinant satisfies `D(1−conj w,conj λ)=c(w)conj D(w,λ)` for every `λ`,
  with a scalar factor independent of `λ`.

Normalization at `λ=0` forces `c(w)=1`. The derivative there is the negative
first trace. Its reflected difference has residue `−1` at both endpoints,
so holomorphic uniqueness excludes reflection even on an open subregion.
The ordinary identity `D(1−w,λ)=c(w)D(w,λ)` fails as well.

**Positive survivor:** the exact decomposition
`T(1−w)−T(w)=H(w)−1/w−1/(w−1)`, with `H` holomorphic on `−1<Re w<2`.
The cleared defect `G=w(w−1)H+1−2w` is reflection-odd and has
`G(0)=1`, `G(1)=−1`; both trace-defect residues equal `−1`.
The [paper proof and Lean certificate](../3-formalized/mayer-arithmetic-reflection-trace-obstruction.md)
are complete, with standard axioms only.

Selected scattering-divisor reflection, closed Cauchy reflection and
physical signed descent are not retired by this result.
