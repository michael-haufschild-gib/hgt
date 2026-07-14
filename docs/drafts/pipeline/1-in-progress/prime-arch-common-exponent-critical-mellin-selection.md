# Prime--archimedean common-exponent critical-Mellin selection

- **ID:** prime-arch-common-exponent-critical-mellin-selection
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Status:** `[CONJECTURE; OPEN CORE]`
- **Source:** completed Euler--Gamma source, endpoint Bernstein moment germ, critical-Mellin defect
- **Statement:** The exact scale-sensitive completed prime--Gamma identity forces the endpoint Bernstein cumulative dissipation to have linear growth on a cofinal degree sequence, and hence forces its unique exact exponential exponent to equal one.

## Goal

Prove unconditionally, without reflection positivity, a self-adjoint realization, or an RH-equivalent
analytic-continuation hypothesis, that there are degrees `d(j) -> infinity` and a constant `C` such
that

\[
  \Pi_0+\sum_{m<d(j)}\mathfrak D_m\le C\,(d(j)+1).
\]

The existing dissipation identity then gives bounded endpoint Bernstein purity on that cofinal
sequence, selects the unique exact exponent `E_* = 1`, and proves RH.

## Gates

- [x] 0 → 1 in-progress: the target is well-posed and source-pure; the exact circularity exclusions are explicit.
- [ ] 1 → 2 fully-proven: derive a scale-sensitive prime--Gamma estimate that pays the cumulative dissipation budget.
- [ ] 2 → 3 formalized: formalize the unconditional source estimate and connect it to the existing master theorem.
- [ ] 3 → 4 publication-ready: promote the source-selection theorem to the paper's master theorem.

## Existing exact reductions

The current formal theorem surface already proves the following equivalent sufficient targets:

1. cofinal linear cumulative dissipation;
2. cofinal bounded endpoint Bernstein purity;
3. bounded endpoint Bernstein negative mass;
4. subexponential endpoint Bernstein total variation;
5. prime--polar negative Dirichlet abscissa at most one;
6. a uniformly bounded aggregate Bernstein discrepancy from positive finite Xi thermal systems.

It also proves that these targets select the unique common purity/dissipation exponent `E_* = 1`.

## Unconditional source progress

The completed divisor source now supplies two quantitative chambers without assuming RH.

1. The scaled Hausdorff rectangle `k <= 13`, `r <= 43` forces every endpoint Bernstein
   coefficient through degree `13` to be nonnegative.  Hence the canonical negative mass is
   exactly zero through defect degree `12`.
2. The narrow-sector estimate gives the positive Abel susceptibility
   \[
     \chi(t)=\sum_{n\ge0}\Pi_n t^n
   \]
   throughout the explicit interval
   \[
     0\le t<\frac{250000}{251001}.
   \]
   Moreover
   \[
     \mathrm{RH}\iff \chi(t)<\infty\quad\text{for every }0\le t<1.
   \]
   If RH is false, the source-attained lower exponential envelope produces a concrete
   `t in (0,1)` at which `chi(t)` diverges.
3. The susceptibility has a unique exact radius `R_A`, reciprocal to the unique common
   purity/dissipation exponent `E_*`:
   \[
     R_AE_*=1,
     \qquad
     \frac{250000}{251001}<R_A\le1.
   \]
   False RH forces `R_A=B^{-2}` for a maximal amplitude carried by an actual off-critical divisor
   atom; RH is exactly `R_A=1`.

Thus the missing estimate is no longer an unspecified global positivity assertion.  It is the
extension of one already-convergent positive source susceptibility across the collar
\[
  \frac{250000}{251001}\le t<1.
\]

## Candidate moves

### A. Exact critical-Mellin quadratic budget

`[CONJECTURE]` There is an exact finite-aperture identity expressing the cumulative Bernstein
dissipation as a positive quadratic transform of the signed critical-Mellin carrier

\[
  dR(h),\qquad R(h)=4\sinh(h/2)-\sum_{n\le e^h}\frac{\Lambda(n)}{\sqrt n},
\]

plus an explicitly controlled archimedean boundary term.  The required estimate must use the
actual Euler and Gamma weights; a scale-invariant sign or orientation statement cannot pay it.

### B. Positive thermal comparator with bounded aggregate error

`[CONJECTURE]` A cofinal choice of finite Xi thermal cutoffs `M(j)` can be made directly from the
completed source so that the aggregate Bernstein coefficient discrepancy at degree `d(j)` remains
uniformly bounded.  Positivity of the finite comparator is unconditional; only the global error
budget is open.

### C. Finite-order source distribution

`[CONJECTURE]` The completed Euler--Gamma source defines a compactly supported finite-order
distribution whose normalized moments are the endpoint moments.  Such a representation would
force only polynomial Bernstein growth and therefore `E_* = 1`.

## Attack and exclusions

- Reflection-positive Gram existence, a positive Hausdorff representing measure, and a global
  anti-Herglotz sign are excluded as inputs: the current tree already proves them equivalent to RH.
- Mere meromorphic continuation of the critical-Mellin transform transports the divisor but does
  not bound its negative mass.
- A scale-invariant source orientation cannot imply a fixed Loewner or dissipation budget without
  an independent scale-fixing identity.
- A finite-order compactly supported distribution representation must be derived from the source;
  if its existence is equivalent to exclusion of off-line poles, it is only another RH criterion.

## Proven carrier restriction

For every strictly increasing \(\phi\), \(C>0\), and \(y\ge0\),
\[
  \phi\!\left(\frac{4}{y+1}\right)\le\phi(C)
  \iff
  y\ge\frac{4-C}{C}.
\]
In particular, for every $k\ge1$, the full homogeneous charge family satisfies
$$
  \left(\frac{4}{y+1}\right)^k\le C^k
  \iff
  y\ge\frac{4-C}{C}.
$$
Thus every common strict order reparameterization of the charge observable and its budget has
exactly the same height content. The cubic thermal gate, the rational sector envelope, and their
higher-power variants belong to this saturated family.

Positively, the remaining source estimate is forced to use a nonhomogeneous carrier.  Candidate A
must therefore retain genuine scale information from $dR(h)$: a logarithmic weight, a mixed-height
quadratic correlation, or an exact source--divisor incidence term.  A power of the endpoint charge
ratio—or any monotone reparameterization of that ratio—cannot close the Abel collar.

## Open core

`[OPEN CORE]` Produce one noncircular prime--Gamma estimate extending Abel susceptibility
convergence from `t < 250000 / 251001` to every `t < 1`.  Equivalently, prove a uniform aggregate
Bernstein comparator error or a cofinal linear cumulative dissipation bound.  Any successful
estimate must exploit the exact completed source coupling; the sector envelope alone is sharp only
at the smaller radius.

## Log

- 2026-07-14 — created after the exact common-exponent/dissipation theorem reduced the Connes route to one source-side selection estimate.
- 2026-07-14 — proved the finite-to-cofinal Abel selection theorem: zero negative mass through degree 12, unconditional susceptibility on `t < 250000 / 251001`, and exact RH selection at the unit boundary.
- 2026-07-14 — proved and formalized the power-invariant saturation law for all homogeneous endpoint-charge gates; the open estimate is now restricted to a nonhomogeneous critical-Mellin carrier.
