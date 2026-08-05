# Route R pre-divisor rational Cartier cyclic-coinvariant functor

- **ID:** `route-r-pre-divisor-rational-cartier-coinvariant-functor`
- **Stage:** 3-formalized
- **Type:** THEOREM (paper + Lean)
- **Source:** `docs/drafts/pipeline/1-in-progress/route-r-rational-cartier-prime-dilation-landing.md`
- **Lean:** `formal/GaloisForLFunctions/RHTower/RouteRPreDivisorRationalCartierCoinvariantFunctor.lean`
- **Status:** `[SOURCE FUNCTOR CONSTRUCTED] [PHYSICAL NATURALITY OPEN] [NOT RH]`

## Exact theorem

Let `C1` be the genuine degree-one cyclic bar of the rational-adelic source, let `tau` be its
cyclic rotation, and put

\[
  C_{1,\mathrm{cyc}}=C_1/\operatorname{im}(\tau-1).
\]

For independent jet grade `k` and spectral parameter `w`, the pre-divisor Cartier coefficient

\[
 h_{k,w}(x)=\mathcal X^{(k)}(w)\,\varepsilon_0^{(1)}(x)
\]

annihilates `im(tau-1)` and therefore descends canonically to a linear functional

\[
 \bar h_{k,w}:C_{1,\mathrm{cyc}}\longrightarrow\mathbb C.
\]

The constant polynomial pair

\[
 A_{q,k,w,[x]}(z)=\bar h_{k,w}([x]),\qquad B_{q,k,w,[x]}(z)=1
\]

is a coefficient-faithful rational Cartier presentation with source dilation character one.  It
depends only on the genuine cyclic class, not on a chosen representative.

For the ordinary-prime atom `u_p`, its coinvariant class is nonzero.  Indeed,

\[
 \bar h_{0,0}([u_p])=\mathcal X(0)\ne0.
\]

At an Xi divisor point `rho`, specialization to the first nonzero jet gives

\[
 \bar h_{m_\rho,w_\rho}([u_p])=c_\rho\ne0.
\]

Thus cyclic quotienting retains the prime atom, divisor multiplicity, and leading Xi coefficient.

## Proof

Cyclicity of the zero-adele trace gives

\[
 \varepsilon_0^{(1)}(\tau x)=\varepsilon_0^{(1)}(x).
\]

Multiplication by the independent scalar `X^(k)(w)` preserves this equality, so
`h_(k,w)((tau-1)x)=0`.  The universal quotient map therefore defines `bar h_(k,w)`, and evaluation
on any representative recovers `h_(k,w)` exactly.  The constant numerator and unit denominator
then satisfy the cross-multiplied dilation law for gain one by direct polynomial algebra.

Trace one of `u_p` gives the two displayed evaluations.  Nonvanishing at `(k,w)=(0,0)` uses the
proved central value `X(0) != 0`; nonvanishing at a divisor uses the multiplicity-leading-jet
theorem.

For the physical centered character

\[
 g_{p,\rho}=p^{2\operatorname{Re}\rho-1},
\]

the descended source functor has exact naturality defect

\[
 \bar h([u_p])-g_{p,\rho}\bar h([u_p])=(1-g_{p,\rho})c_\rho.
\]

The established source comparison identifies this nondivisively with the negative canonical
readout of the cofinal central Bockstein class.  Passing to genuine cyclic coinvariants therefore
does not erase or rename the remaining Route R obstruction.

## Lean realization

Module proves:

- `ccmRationalAdelicDegreeOneCyclicCoinvariantClass_rotate`;
- `ccmRationalAdelicDegreeOneCyclicBoundary_le_ker_cartierCoefficient`;
- `ccmRationalAdelicPreDivisorCoinvariantCartierCoefficient_mk`;
- `ccmRationalAdelicPreDivisorCoinvariantCartierCoefficient_comp_class`;
- `ccmRationalAdelicPreDivisorCoinvariantRationalCartierPresentation_mk`;
- `ccmRationalAdelicOrdinaryPrimeCyclicCoinvariantClass_ne_zero`;
- `ccmRationalAdelicPreDivisorCoinvariantRationalCartierPresentation_primeAtom_ne_zero`;
- `ccmRationalAdelicPrimeXiCoinvariantCartierPhysicalDilationDefect_eq_neg_cofinalReadout`.

## Hostile audit

This closes genuine source functoriality: presentation is defined on cyclic coinvariants and the
prime class remains nonzero there.  It does not construct the physical-gain rational landing.
That landing would require the final defect above to vanish and is already equivalent to the
Route R Hodge-mate coefficient being zero.  No quotient by the physical paracyclic defect was
taken, because doing so would impose the RH-equivalent conclusion.

Finite theta-isogeny and two-orientation determinant-one refinements do not change this verdict:
the existing Route R hyperbolic classification realizes reciprocal nonneutral characters with
determinant one for every centered rate.  A successful next producer must be singular,
divisor-supported, and must identify the source unit character with the fixed same-fibre physical
character without quotienting away the retained class.

## Log

- 2026-08-05 — dependency-closed paper proof and Lean formalization completed; umbrella import
  added; direct module check passed.
