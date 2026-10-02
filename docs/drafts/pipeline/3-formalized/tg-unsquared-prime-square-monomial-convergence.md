# TG C9.11m.1 — unsquared prime-square monomial convergence

- **Stage:** 3-formalized
- **Route:** TG, actual cofinal relative operator admission
- **Parent:** `tg-unsquared-relative-source-assembly.md`
- **Status:** exact vector convergence and degree-uniform tails proved;
  full relative operator assembly remains open.

## Exact new result

Let `f_n(x)=x^n 1_{[-a,a]}(x)` in the actual Sonin L² carrier. For every real
aperture a and every natural degree n, the original source family

`p ↦ c_(p,0) (D_(p²)+D_(p⁻²)) f_n`

is unconditionally summable over all finite prime sets. Here the corpus's
literal `soninLogPrimePowerCoefficient(p,0)` is proved equal to `1/(2p)`;
neither the coefficient nor the two dilation directions have been replaced.

The stronger result needed for the operator passage is also proved. For every
ε>0 there is a finite prime set S such that, for every finite T disjoint from S
and every n, the norm of the corresponding source sum is at most `ε ||f_n||`.
The same exclusion S works for all degrees.

## Dependency-closed proof

For 0<r≤s, projection onto `[-a/s,a/s]` sends `D_r f_n` to
`(sqrt(r)/sqrt(s)) (r/s)^n D_s f_n`. The projection fixes `D_s f_n`, so
self-adjointness gives their exact inner product. Its norm is at most
`sqrt(r)/sqrt(s) ||f_n||²`, uniformly in n. This proof uses actual supports;
no decorrelation premise or numerical integration occurs.

After multiplication by the original prime-square coefficients, the complete
same-direction Gram matrix is bounded by
`||f_n||²/(4 max(p,q)²)`. Inverting both scales reverses the overlap by the
unitary dilation composition law, giving the identical bound for the other
direction.

The majorant is summable over all prime pairs. Its triangular rows are
`π(p)/p²`; Chebyshev's eventual bound compares these to the corpus's summable
prime reciprocal-log series. The union of both triangles bounds the whole
matrix, including its diagonal and every off-diagonal entry.

For an arbitrary Hilbert-space vector family, absolute summability of its
complete Gram matrix implies unconditional vector summability. Expand the
squared norm of a finite tail into its full Gram sum. A finite exclusion for
the pair family induces one for the vectors by projecting onto the first
coordinate. Applying this argument with the same scalar majorant at every
degree gives the uniform tails above. Add the two convergent dilation legs.

## Lean and audit

- `SoninCutoffMonomialDilation`: actual cutoff monomial, proportional cutoff,
  exact overlap and degree-uniform overlap loss.
- `CoherentGramSummability`: finite Gram norm estimate and unconditional
  vector summability from the complete Gram matrix.
- `SoninPrimeSquareOverlapSummability`: actual prime-pair majorant summability.
- `SoninPrimeSquareCoherentMonomials`: original coefficient identity,
  inverse-dilation identity, actual symmetric source convergence and uniform tail.

All four final foreground `lake --old env lean <leaf>` audits pass. All
thirteen public declarations have only `propext`, `Classical.choice` and
`Quot.sound` in their axiom audits. All four leaves are wired into RHTower;
no umbrella or full build was run. No new heartbeat setting, hole or axiom.
Global lint reports twelve unrelated unwired modules and no error in these
leaves (`/tmp/tg-c911m-monomial-lint.log`).

## Remaining hard mathematical work

Transfer the uniform source tail through the **actual** time-band rank-one
expansion in trace norm, then through the verified correction right factors.
Add the unchanged deeper prime-power modes. This still does not admit the
linear prime principal source or the complete prime–Gamma class; their joint
continuation, Hardy cubic compatibility and strict sub-unit law remain open.
