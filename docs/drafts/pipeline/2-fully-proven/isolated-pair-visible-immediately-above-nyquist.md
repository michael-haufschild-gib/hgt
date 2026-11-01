# An isolated pair is visible immediately above Nyquist

- **ID:** isolated-pair-visible-immediately-above-nyquist
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Source:** `review-0111/obstacles-summary.md`, A3.
- **Statement:** For every `L>0`, `0<δ≤1/2`, height `γ`, and aperture
  `a>L/2`, the doubled on-line lattice with the single reflected pair
  `1/2±δ+iγ` has Hodge defect one at degree `a`.

## Proof

Set `w=a−L/2>0` and `D(z)=exp(−izL/2)−exp(izL/2)`.
At every on-line lattice frequency `2πk/L`, `D` vanishes. At
`z₋=γ−iδ` and `z₊=γ+iδ`, it is nonzero: equality of the two
exponentials would equate their norms `exp(±δL/2)`.

The proved fixed-support interpolation theorem
`exists_test_interpolating_Icc` gives a complex `C²` test `b` supported
in `[-w,w]`, with Fourier values `1/D(z₋)` and `−1/D(z₊)`.
Then `f(u)=b(u+L/2)−b(u−L/2)` is supported in `[-a,a]`.
Its transform vanishes on the entire on-line lattice and takes values
`1,−1` at the reflected pair. Every on-line Weil summand is zero;
the two off-line summands are each `−1`. Thus `W(f,f)=−2`.
The configuration has exactly one right zero, so its defect is exactly one.

Together with the exact sub-Nyquist law, this gives the global edge
`exp(min(x/δ,L))`, where `x>0` uniquely solves `sinh x−x=2δL`.

## Gates

- [x] Dependency-closed paper proof.
- [ ] Exact Lean theorem and transitive axiom audit.
