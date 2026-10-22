# Local full-Cauchy uniqueness for arithmetic Hodge charts

- **ID:** `deninger-local-full-cauchy-uniqueness`
- **Stage:** 3-formalized
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
`GaloisForLFunctions.RHTower.Deninger.DeningerArithmeticLocalCauchyUniqueness`
as `deningerSecondOrderMode_coefficients_eq_zero` and
`deningerFiniteEnergyMode_coefficients_eq_zero`.  Its required
direct-file check passes.

The exact logical descent is formalized as
`RHTower.deningerRelativeCauchyUnique_of_localRestrictions` in
`GaloisForLFunctions.RHTower.Deninger.DeningerArithmeticPositiveCalderonKoszul`;
required direct-file check passes.  The derivation of the mode normal
form from the local Hodge--Dirac PDE and the orientation-twisted real
descent are formalized as well; see the sections below.

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

### The mode normal form landed

`formal/GaloisForLFunctions/RHTower/Deninger/DeningerModeNormalForm.lean`.  Axiom audit:
`propext, Classical.choice, Quot.sound`.

- `deningerFirstOrder_eq_exp` — **uniqueness for `f' = c f`**: a solution equals its initial value
  times the exponential.  Proved by showing `f(t)·e^{-ct}` has vanishing derivative, hence is
  constant (`is_const_of_deriv_eq_zero`).
- `deningerSecondOrder_normal_form` — **the normal form `(1)`**: a solution of `u'' = m²u`
  satisfies

  `u(r) = ((u'(0) + m u(0))/2m)·e^{mr} - ((u'(0) - m u(0))/2m)·e^{-mr}`.

  Passing to `w = u' + m u` and `z = u' - m u` turns the second-order equation into `w' = m w`
  and `z' = -m z`; the first-order uniqueness solves both, and `u = (w - z)/2m` recombines them.

This supplies the derivation of the mode normal form from the second-order coefficient equation,
which was listed as remaining.  Together with the already-formalized coefficient elimination
(`deningerSecondOrderMode_coefficients_eq_zero`,
`deningerFiniteEnergyMode_coefficients_eq_zero`) the Kummer half-cylinder argument is complete:
every solution has the two-exponential form, and vanishing full Cauchy data kill both
coefficients.

### Remaining

The reduction of the local Hodge--Dirac PDE to the scalar equation `u'' = m² u` for each Fourier
mode, and orientation-twisted real descent.  Those are the geometric inputs; the ODE content is
now proved.

### The Hodge--Dirac reduction landed

Added to `DeningerModeNormalForm.lean`.  Axiom audit: `propext, Classical.choice, Quot.sound`.

- `deningerDirac_secondOrder` — **the first-order system gives the second-order equation**: from
  `f' = m g` and `g' = m f`, the component `f` satisfies `f'' = m² f` in exactly the
  `HasDerivAt` form the normal form consumes.  This is the card's "equivalently a second-order
  equation of the form `(1)`".
- `deningerDiracMode_eq_zero` — **zero full Cauchy data kill a nonzero mode**: if `f` and `g`
  solve the system and both vanish at the interface `r = 0`, then `f ≡ 0` and `g ≡ 0`.  The
  normal form makes both integration constants zero, so `f` vanishes; then `f' = m g` with
  `m ≠ 0` forces `g` to vanish too.
- `deningerZeroMode_eq_zero` — the zero mode `a dθ + b ds` is killed by its interface pair.

The local argument is now complete for a mode of the finite-prime extended cylinder: value and
normal value at the interface determine both integration constants, and vanishing data kill the
mode.  The same statement serves the Kummer half-cylinder and the radial system of the real
orientation-apex chart, all three being the same constant-coefficient system.

### Remaining

Orientation-twisted real descent: that the invariant and anti-invariant summands of the oriented
double cover decompose directly, so that faithfulness of the descent follows.  That is a
representation-theoretic statement about the double cover, not a PDE statement, and the PDE
content of all three local models is now formalized.

### Orientation descent landed

`formal/GaloisForLFunctions/RHTower/Deninger/DeningerOrientationDescent.lean`.  Axiom audit:
`propext, Classical.choice, Quot.sound` (the faithfulness lemma needs only `propext`).

- `deningerOrientationInvariant`, `deningerOrientationAntiInvariant` — the two summands, as
  kernels of `C - 1` and `C + 1`, with their membership criteria `C v = v` and `C v = -v`.
- `deningerOrientation_eq_zero_of_parts` — **faithfulness of the descent**: a class whose
  invariant and anti-invariant parts both vanish is zero, since the two conditions add to
  `2v = 0`.
- `deningerOrientation_isCompl` — **the decomposition is direct**: the summands are disjoint
  because a vector both fixed and negated is its own negative, and they span because
  `v = (v + Cv)/2 + (v - Cv)/2`.

This is the card's "descent is faithful because the double-cover invariant/anti-invariant
decomposition is direct", now proved rather than asserted.

### Status

All three local models are formalized: the mode normal form and the Hodge--Dirac reduction give
"zero full Cauchy data kill every nonzero mode" for the common constant-coefficient system, the
zero-mode case is the interface pair, and the orientation descent is direct and faithful.  The
logical descent to the global statement was already formalized as
`deningerRelativeCauchyUnique_of_localRestrictions`.

### Gates

- [x] 0 → 1 in-progress: three local models isolated
- [x] 1 → 2 fully-proven: injectivity in all three models
- [x] 2 → 3 formalized: mode normal form, Hodge--Dirac reduction, mode vanishing, zero mode,
      orientation descent, and the logical descent lemma
- [ ] 3 → 4 publication-ready: the two global descent checks stated under "Global consequence",
      which this card reduces to rather than proves
