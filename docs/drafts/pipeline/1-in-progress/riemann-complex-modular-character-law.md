# Riemann complex modular-character law

- **ID:** `riemann-complex-modular-character-law`
- **Stage:** 1-in-progress
- **Type:** UNIVERSAL THEOREM / RH-FACING STRUCTURAL SEPARATION
- **Supersedes as headline:** `hedenmalm-weil-chiral-aperture`
- **Status:** paper proof in construction; exact Lean theorem surface in construction

## Universal object

For a spectral point \(\rho\), put
\[
  \chi_\rho(z)=\exp\!\left(z(\rho-\tfrac12)\right),
  \qquad z\in\mathbb C.
\]
This is a one-dimensional complex representation of the additive dilation plane.  Its centered
real weight is
\[
  a_\rho=\operatorname{Re}\rho-\tfrac12.
\]

The proposed law is not that several RH criteria happen to be equivalent.  It is that the
apparently different orientation, growth, monodromy, Krein, Ward, and escape observables are exact
functors of this one character:

1. **real dilation:** at \(z=\log r\), \(\chi_\rho(z)=r^{\rho-1/2}\), so
   \[
   \frac{\log|\chi_\rho(\log r)|}{\log r}=a_\rho;
   \]
2. **Hurwitz monodromy:** at \(z=-2\pi i\), the centered character is the negative of the
   Hurwitz monodromy character; on the open critical strip its principal phase recovers
   \(|a_\rho|\) without aliasing;
3. **reflection grading:** \(\rho\mapsto1-\bar\rho\) sends \(a_\rho\mapsto-a_\rho\) and dualizes
   the real-dilation character;
4. **Krein generator:** the signed transverse operator is the infinitesimal real-weight
   generator, and critical-line reflection anticommutes with it;
5. **aperture:** the spectral aperture is the supremum of the positive real weights;
6. **Hurwitz energy:** the canonical orientation energy is a reciprocal-square weighted
   Hilbert shadow of the imaginary-period character;
7. **Ward charge:** divisor transgression counts nontrivial reflection orbits but does not bound
   their real weights;
8. **source tomography:** forward/inverse compact-BV source dilations multiply actual Laurent
   residues by the two dual real-ray characters and recover \(a_\rho\) from their norm ratio.

## New separation theorem

Fix \(0<a<1/2\), and let
\[
  \rho_n=\tfrac12+a+i(n+1).
\]
The normalized functional-equation quartet gauge with orbit
\(\tfrac12\pm a\pm i(n+1)\) has the following simultaneous behavior:

- its completed-symmetry hypertranscendental carrier converges to \(\xi\) through every
  holomorphic jet on compact sets;
- its complete represented differential matroid is unchanged;
- its nonnegative Ward density converges uniformly to zero on every bounded height window;
- its total Ward mass remains exactly \(8\pi\);
- every reciprocal-square trace-class orientation atom tends to zero;
- nevertheless its complex modular character has real weight exactly \(a\) for every \(n\), and
  its imaginary-period principal phase and horizontal aperture remain exactly \(a\).

Hence compact-open analytic data, differential-algebraic data, local Ward density, total
topological charge, and trace-class energy do not control the horizontal aperture, even jointly,
on the natural completed-symmetry hypertranscendental gauge class.  The character weight is the
height-uniform coordinate missing from all those reporters.

This is a positive classification, not only a no-go: the compact-BV forward/inverse residue pair
is an explicit source operation that reconstructs the missing character weight exactly whenever
the source window is noncensoring.

## Paper question answered

**Question.** What common mathematical datum is being lost by squaring, positive scalarization,
trace-class energy, finite-height observation, compact-open limits, and differential-field
quotients, and what source operation retains it?

**Answer.** The lost datum is the real weight of the complex modular character
\(\chi_\rho\).  Reflection-even operations pair a character with its dual, compact/trace-class
operations are noncoercive at the height boundary, and rational differential gauges quotient out
finite divisor changes.  Forward/inverse source dilation retains the unsquared character and
recovers its real weight.

## Formal targets

1. Define the centered complex modular character and prove its additive character law.
2. Prove exact real-ray `cpow` realization, norm law, and logarithmic recovery.
3. Identify its \(-2\pi i\) value with the negative Hurwitz monodromy character.
4. Prove reflection duality.
5. Define the escaping quartet character and prove its weight is constant.
6. Prove the reciprocal-square character energy tends to zero.
7. Package these with existing compact-open all-jet convergence, Kolchin blindness, local Ward
   escape, exact \(8\pi\) mass, BV-residue phase reconstruction, and aperture identities.

## Hostile gates

1. If the main theorem is only the elementary exponential character identity, reject it.
2. If “all shadows” are analogies rather than displayed theorem-level maps, reject it.
3. If the escape theorem does not include a genuinely height-uniform surviving coordinate,
   reject it.
4. If source reconstruction assumes RH, simplicity, or a zero-selected topology, reject it.
5. If compact-open or trace-class noncoercivity was already stated in this simultaneous form in
   prior literature, narrow or retire novelty.
6. If the paper implies zero exclusion without a proved source inequality, reject it.
7. If the paper ends with an unproved conjecture as its claimed result, reject it.

## Log

- 2026-07-30 — Derived after the defect-norm analogy failed: Ward charge, endpoint trace,
  Hurwitz energy, and aperture are not norms on one fixed space.  Replaced that analogy by the
  complex modular character whose restrictions, generator, transgressions, and weighted
  representations produce the exact observables.
