# Critical radial \(L^2\) quotient as arithmetic Hodge cohomology

- **ID:** `deninger-critical-radial-l2-hodge-quotient`
- **Stage:** 5-failed
- **Type:** NO-GO WITH POSITIVE SURVIVOR
- **Label:** `DAC_CRITICAL_RADIAL_L2_POISSON_QUOTIENT_NO_GO`
- **Parent:** `deninger-poisson-hodge-polarization`
- **Statement:** the local Hermitian radial-line metric is the correct
  critical measure, but completing Meyer's Poisson complex in that
  scalar \(L^2\) space makes the Poisson range dense and erases reduced
  middle cohomology.

## Candidate

The Hermitian radial-line theorem gives
\[
 L^2_{1/2}
 =
 L^2(\mathbb R_{>0},x\,d^\times x)
 =
 L^2(\mathbb R_{>0},dx).                                         \tag{1}
\]
The centered dilation flow is unitary on `(1)`, and the local
degree-one Hodge star is positive.  The tempting construction is
\[
 \overline{H_-}^{\,L^2_{1/2}}
 \Big/
 \overline{Z(H_\cap)}^{\,L^2_{1/2}}.                             \tag{2}
\]

## Density theorem

`[PROVED HERE] [DAC_CRITICAL_RADIAL_L2_POISSON_QUOTIENT_NO_GO]`

\[
 \overline{Z(H_\cap)}^{\,L^2(\mathbb R_{>0},dx)}
 =
 L^2(\mathbb R_{>0},dx).                                         \tag{3}
\]
Consequently the reduced Hilbert cohomology in `(2)` is zero.

### Proof

First \(H_\cap\) is dense in \(L^2(\mathbb R_{>0},dx)\).
Compactly supported smooth functions away from zero are dense.  After
even extension, the condition \(f(0)=0\) already holds.  The remaining
condition
\[
 \widehat f(0)=\int_{\mathbb R}f(x)\,dx=0
\]
can be imposed with arbitrarily small \(L^2\) error: subtract a smooth
even plateau of integral \(\int f\), supported on an interval of
length \(L\) far from the original support.  Its amplitude is
\(O(L^{-1})\), hence its \(L^2\) norm is \(O(L^{-1/2})\).

The critical Mellin transform is unitary, up to normalization,
\[
 \mathcal M_{1/2}:
 L^2(\mathbb R_{>0},dx)
 \longrightarrow L^2(\mathbb R,dt).                              \tag{4}
\]
On \(H_\cap\),
\[
 \mathcal M_{1/2}(Zf)(t)
 =
 \zeta\!\left(\frac12+it\right)
 \mathcal M_{1/2}f(t).                                           \tag{5}
\]
The meromorphic function \(\zeta\) is not identically zero, so its
zeros on the critical line form a measure-zero discrete set.

If \(g\) is orthogonal to the range in `(5)`, then
\[
 \int_{\mathbb R}
 \zeta\!\left(\frac12+it\right)
 \mathcal M_{1/2}f(t)\overline{g(t)}\,dt=0
 \qquad(f\in H_\cap).
\]
Density of the Mellin core implies
\[
 \overline{\zeta(1/2+it)}\,g(t)=0
\quad\text{a.e.}
\]
Since the multiplier is nonzero almost everywhere, \(g=0\).
Thus the orthogonal complement of \(Z(H_\cap)\) is zero, proving
`(3)`.

## Why local Hodge positivity does not descend

The local star commutes with the differential on the test core, but
Hilbert harmonic cohomology represents the quotient by the
**closure** of the differential range.  Equation `(3)` makes that
harmonic space zero.  Therefore:

- local Kähler positivity is genuine;
- the critical measure is forced and correct;
- scalar Hilbert completion before nuclear cohomology is wrong.

This is the exact distinction between a positive source metric and a
faithful positive metric on \(M_\zeta\).

## Strongest positive survivor

1. Form the strict nuclear quotient
   \(M_\zeta=H_-/Z(H_\cap)\) first.
2. Retain the Gelfand rigging
   \[
   H_{\mathrm{test}}\subset H_{\mathrm{Hilb}}
   \subset H_{\mathrm{test}}'
   \]
   without identifying nuclear cohomology with the reduced scalar
   Hilbert quotient.
3. A successful arithmetic leaf complex must contain additional
   source coefficient/transverse data whose closed reduced harmonic
   image maps faithfully into \(M_\zeta'\).  The scalar radial line
   alone cannot do this.
4. Cup-isometric faithfulness of that map is the RH-bearing theorem;
   it cannot be inferred from local star positivity.

## No-go closure

- **Killed representation:** scalar critical-\(L^2\) completion of
  the Poisson cokernel.
- **Killing mechanism:** Mellin multiplication by a nonzero-a.e.
  zeta multiplier has dense range.
- **Positive invariant:** exact forced critical measure and local
  weight-one Hodge star survive as one channel of a larger rigged
  coefficient.
- **Paper status:** dependency-closed proof above.
- **Lean status:** abstract dense-multiplier formalization pending a
  low-load window.

## References

- Ralf Meyer, *A spectral interpretation for the zeros of the Riemann
  zeta function*: https://arxiv.org/abs/math/0412277.
- `DAC_DENINGER_HERMITIAN_RADIAL_LINE_POISSON_HODGE`
- `DAC_MEYER_NUCLEAR_RADIAL_STRICTNESS`

## Log

- 2026-07-27 — Proved that the forced critical scalar Hilbert
  completion has zero reduced Poisson cohomology; retained the local
  Kähler line only as one channel of a future rigged leaf complex.
