# Local full-Cauchy uniqueness for arithmetic Hodge charts

- **ID:** `deninger-local-full-cauchy-uniqueness`
- **Stage:** 2-fully-proven
- **Type:** SOURCE LOCAL ELLIPTIC THEOREM
- **Label:** `DAC_LOCAL_FULL_CAUCHY_UNIQUENESS`
- **Parent:** `deninger-arithmetic-calderon-global-chirality-kernel`
- **Statement:** on each Kummer half-cylinder, finite-prime extended
  cylinder, and real orientation-apex chart, a harmonic source packet
  with zero full Cauchy data on a noncharacteristic interface is zero.

## Full Cauchy data

Full Cauchy data mean the value and outward normal derivative of the
harmonic packet on a compact chart interface.  At a finite prime they
are retained together with the extended asymptotic residue channel;
at the real chart they are retained together with the apex endpoint.
An asymptotic residue or apex value alone is not full Cauchy data and
does not satisfy this theorem.

## Kummer half-cylinder

For a nonconstant Fourier character \(a\), write
\(m=|\ell(a)|>0\).  A harmonic coefficient satisfies
\[
  u_a''-m^2u_a=0.
\]
Hence
\[
  u_a(r)=c_a^+e^{mr}+c_a^-e^{-mr}.                            \tag{1}
\]
Finite homogeneous energy removes \(c_a^+\).  Vanishing Dirichlet
trace at \(r=0\) removes \(c_a^-\).  Equivalently, vanishing full
Cauchy data removes both coefficients without using the energy
condition.  The mean-zero relative domain has no constant packet.
Therefore the harmonic Kummer packet is zero.

## Finite-prime extended cylinder

On a finite cylindrical truncation
\([s_0,\infty)\times S^1\), decompose an extended harmonic form into
Fourier modes.  Every nonzero mode obeys a constant-coefficient
first-order Hodge--Dirac system, equivalently a second-order equation
of the form `(1)`.  Its value and normal value at \(s=s_0\) determine
both integration constants.  Zero full Cauchy data therefore kill
every nonzero mode.

The zero mode is
\[
  a\,d\theta+b\,ds.
\]
Its interface Cauchy value, and equivalently its extended leading
packet, is \((a,b)\); zero data kill it.  In particular the retained
\(d\log z=-ds+i\,d\theta\) residue line is not discarded: it is
detected and then killed only when its full Cauchy data are zero.

## Real orientation-apex chart

Lift to the oriented double cover.  The invariant and
orientation-anti-invariant summands satisfy the ordinary Euclidean
Hodge--Dirac equation componentwise.  Fourier expansion on a compact
circle around the apex again reduces to a first-order radial system.
Value and normal value on that circle determine every radial
coefficient.  Zero full Cauchy data kill both summands.  Descent is
faithful because the double-cover invariant/anti-invariant
decomposition is direct.

## Theorem

`[PROVED HERE] [DAC_LOCAL_FULL_CAUCHY_UNIQUENESS]`

For each of the three arithmetic local Hodge models, the map
\[
 \{\text{harmonic packets in the stated source domain}\}
 \longrightarrow
 \{\text{full interface Cauchy data}\}
\]
is injective.

The result is stable under finite Fourier packets, lattice
refinement, Galois maps, positive-rational power maps,
residue/corestriction, and real orientation descent because all these
maps intertwine the local Hodge--Dirac equations and their interface
traces.

## Global consequence

Together with
`DAC_RELATIVE_CAUCHY_UNIQUENESS_DESCENT`, this reduces global
relative Cauchy uniqueness to two exact descent checks:

1. zero global Cauchy data restrict to zero full Cauchy data on every
   chart;
2. chart restrictions jointly separate global harmonic classes in
   the strict Rost--Schmid totalization.

No additional local PDE theorem remains.

## Falsifiers

- Prime residue data alone do not determine a harmonic packet;
  nonzero decaying Fourier modes can have zero asymptotic leading
  term.  Full interface Cauchy data are load-bearing.
- Ordinary \(L^2\) at the prime cusp is not substituted for the
  extended domain.
- The Kummer constant packet is removed by the actual relative
  augmentation, not by an informal mean-zero convention.
- The real orientation double cover must descend both invariant and
  anti-invariant summands.
- This is local uniqueness, not the still-open strict global descent.

## Lean status

The nonconstant cylindrical Fourier-mode coefficient elimination is
formalized in
`GaloisForLFunctions.RHTower.DeningerArithmeticLocalCauchyUniqueness`
as `deningerSecondOrderMode_coefficients_eq_zero` and
`deningerFiniteEnergyMode_coefficients_eq_zero`.  Its required
direct-file check passes.

The exact logical descent is formalized as
`RHTower.deningerRelativeCauchyUnique_of_localRestrictions` in
`GaloisForLFunctions.RHTower.DeningerArithmeticPositiveCalderonKoszul`;
required direct-file check passes.  Formal derivation of the mode
normal form from the local Hodge--Dirac PDE and orientation-twisted
real descent remain to be added.

## References

- Karsten Fritzsch, Daniel Grieser, Elmar Schrohe, *The Calderón
  Projector for Fibred Cusp Operators*, arXiv:2006.04645.
- `DAC_KUMMER_RELATIVE_CALDERON_POISSON_DOMAIN`.
- `DAC_ARITHMETIC_EXTENDED_CUSP_HODGE_BOUNDARY`.
- `DAC_REAL_ORIENTATION_TWISTED_HODGE_APEX`.

## Log

- 2026-07-27 — Proved local full-Cauchy uniqueness on all three
  arithmetic Hodge chart types and isolated strict joint-separation
  descent as the only remaining global uniqueness input.
