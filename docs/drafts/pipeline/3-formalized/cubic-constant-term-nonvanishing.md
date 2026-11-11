# Nonvanishing from the cubic constant term

- **ID:** cubic-constant-term-nonvanishing
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Parent:** [cubic theta residue](cubic-theta-residue-and-gauss-coefficients.md)
- **Statement:** The actual incoming residue at `s=4/3` is a nonzero quotient `L²` eigenvector of the Laplacian with eigenvalue `8/9`.

Let `V=9√3/2` be the covolume of the period lattice `3ℤ[ω]`, and let
`Z₀(t)=(1−3^(−t))ζ_K(t)` omit the ramified prime of `K=ℚ(ω)`.
Unfolding the zero Fourier coefficient gives
`v^s + v^(2−s) π c₀(s)/(s−1)`.
The finite residue-character sum defining `c₀` vanishes unless its
denominator is a cube: multiplication by each admissible residue class
forces triviality of the cubic symbol. Unramified reciprocity and the
ramified supplementary laws force every valuation to be divisible by three
and the unit class to be a cube. Conversely, cubes give the
number of admissible classes.

Write each cube denominator uniquely as
`±λ^(3(n+1)) g(I)^3`, where `n≥0`, `I` is unramified, and `g(I)` is its
primary generator. Its contribution is
`3^((3−3s)(n+1)) φ(I)N(I)^(2−3s)`.
The ramified geometric sum and ideal totient convolution then give
`c₀(s)=(2/V)(3^(3s−3)−1)⁻¹ Z₀(3s−3)/Z₀(3s−2)`.
Absolute convergence holds for `Re s>4/3`.

The Dedekind zeta residue gives
`r₀=Res₁ Z₀=(2/3)Res₁ ζ_K≠0`, while `Z₀(2)≠0` follows from its
absolutely convergent Möbius inverse. Thus
`Res_(4/3)c₀=r₀/(3VZ₀(2))≠0`.

Integrating the constant mode over heights `5≤v≤6`, with volume density
`v⁻³`, multiplies this residue by
`3πV·[5^(−4/3)−6^(−4/3)]/(4/3)`, which is nonzero.
The incoming height term is analytic there. This compact cusp average is
a bounded functional on the local `L²` family.

[Initial source matching](cubic-initial-resolvent-matching.md) identifies
the two averages for `Re s>4`, `Im s>0`. Analytic uniqueness extends the
identity to `Re s>4/3`, `Im s>0`. The isolated spectral pole permits passage
to the real boundary near `4/3`; uniqueness of the residue limit therefore
identifies the bounded functional of the actual residue with the nonzero
constant above. The actual vector cannot vanish.

Formalized in `TheCubicResidueIsNonzero.lean` as
`CubicEisenstein.cubicEisensteinResidue_ne_zero` and
`cubicEisensteinResidue_eigenvector`, for the actual family with cutoff heights
`2,3`. The endpoint `cubicEisensteinResidue_cusp_average` identifies its
nonzero detecting average. Period-lattice unfolding, cube support, ideal
totient series, the constant-term residue, and initial source matching are
kernel-checked. Direct endpoint audits use only `propext`, `Classical.choice`,
and `Quot.sound`; no analytic premise remains. Nonconstant Gauss-coefficient
identification and uniform descent remain open.

Adapted from OpenAI's cubic constant-term, cusp-average, and residual-vector
arguments; this is classical spectral input, not a new cancellation estimate.
