# Universal one-probe real-descent law

## Status

- **Stage:** 3 — formalized
- **Type:** universal theorem with Riemann-hypothesis specialization
- **Public manuscript:** `docs/drafts/manuscripts/one-cauchy-probe-real-krylov-descent/main.tex`
- **Verification modules:**
  - `formal/GaloisForLFunctions/RHTower/UniversalCauchyRealKrylovDescentLaw.lean`
  - `formal/GaloisForLFunctions/RHTower/UniversalCauchyQuartetVarianceLaw.lean`

## Universal theorem

Let \((a_j)_{j\in J}\subset\mathbb C^\times\) be stable under complex conjugation and let
\(z\notin\mathbb R\) avoid the family. Define the diagonal Krylov coordinate

\[
  K_z(p)(j)=\frac{p(a_j^{-1})}{a_j-z},\qquad p\in\mathbb R[X],
\]

and the conjugate-adjoint Cauchy response

\[
  R_z(j)=\frac{\overline{a_j}^{-2}}{\overline{a_j}-z}.
\]

Then a single sequence \((p_n)\subset\mathbb R[X]\) satisfies

\[
  K_z(p_n)(j)\longrightarrow R_z(j)\quad\text{for every }j
\]

if and only if every \(a_j\) is real. The forward implication is a finite conjugation-seam
rigidity argument. The reverse implication is exact: \(p=X^2\) already gives the response.
No discreteness, summability, norm convergence, or Hilbert-space closure hypothesis is used.

## Quartet companion law

For a conjugation/negation-stable complex family, the signed Cauchy orientation statistic over
each quartet \(\{a,\bar a,-a,-\bar a\}\) equals

\[
  16\,\Re z\,\Im z\;
  \frac{(\Re a)^2(\Im a)^2}{|a-z|^2|a-\bar z|^2|a+z|^2|a+\bar z|^2}.
\]

Consequently the global orientation charge, whenever summable, is an exact nonnegative total
variance in the first quadrant and vanishes precisely on coordinate-axis quartets.

## RH specialization

For centered nontrivial zeta zeros \(a=-i(\rho-\tfrac12)\), reality of every spectral point is
equivalent to the Riemann hypothesis. At any fixed nonreal regular probe, in particular
\(z_0=(1+i)/4\), RH is therefore equivalent to pointwise real-polynomial recovery of the
conjugate-adjoint response from one Cauchy seed.

This is an unconditional equivalence, not a proof of RH. Its right-to-left endpoint is closed;
the new open core is source-side: produce the required common real-polynomial approximants from
prime/Gamma data without presupposing conjugation-seam invariance.

## Hostile route audit

The obvious coefficient-realification strategy does not close the route. If complex polynomials
recover a target, replacing each polynomial by its coefficientwise real part converges to the
seam projection

\[
  P_zv(a)=\frac12\left(v(a)+\frac{a-\bar z}{a-z}\overline{v(\bar a)}\right),
\]

not generally to \(v\). For the adjoint response, equality with this projection is itself
equivalent to reality of the spectral points. Thus naive realification is circular, and the exact
surviving problem is a zeta-specific conjugation-preserving source-selection theorem (or a source
packet with a provable opposite-sign contrast).

## Novelty audit

Targeted searches covered Li/Weil criteria, Bombieri--Lagarias, compact-normal Krylov solvability,
recent cyclicity approaches, and recent RH operator/preprint literature. No prior theorem matching
the topology-free, one-fixed-probe, pointwise real-descent equivalence was found. Priority remains
provisional pending expert review and a broader bibliographic audit.

## Verification audit

- `lake env lean GaloisForLFunctions/RHTower/UniversalCauchyQuartetVarianceLaw.lean` — pass
- `lake env lean GaloisForLFunctions/RHTower/UniversalCauchyRealKrylovDescentLaw.lean` — pass
- `lake build GaloisForLFunctions.RHTower.UniversalCauchyQuartetVarianceLaw` — pass
- `lake build GaloisForLFunctions.RHTower.UniversalCauchyRealKrylovDescentLaw` — pass
- Axiom footprint of seven principal theorems: only `propext`, `Classical.choice`, `Quot.sound`
- Both modules imported by `formal/GaloisForLFunctions/RHTower.lean`
- Global formal lint currently blocked by unrelated concurrent modules missing from their umbrellas;
  neither module on this card appears in the lint failure set.

## Next backward step

Attack the source theorem rather than add estimates: identify a prime/Gamma-generated packet whose
construction forces coefficientwise realness before zero-side evaluation. Any proposed source must
be tested against the exact seam projection above; if it merely realifies a complex approximant,
it cannot advance the route.
