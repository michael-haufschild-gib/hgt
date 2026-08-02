# Route E rough-semiprime Lambert return

- **ID:** `ROUTE-E-ROUGH-SEMIPRIME-LAMBERT-RETURN-001`
- **Stage:** 5-failed
- **Type:** SOURCE-MECHANISM NO-GO / POSITIVE SURVIVOR
- **Parent:** `../1-in-progress/route-e-squarefree-exponential-gibbs-parity.md`
- **Source:** `OPEN-SOURCE-001`
- **RH used:** no
- **Computation used:** no
- **Lean status:** exact finite divisor-fibre law formalized in
  `MobiusRoughLambertBoundary.lean`, including exact assignment of the positive fibre to the
  two-or-more-large remainder; analytic PNT asymptotic paper-proved

## Proposed mechanism

For

\[
B_z^{(0)}(x)=A_z(x)-\sum_{p>z}A_z(px),
\qquad
{\cal L}f(x)=\sum_{k\ge1}f(kx),
\]

ordinary divisor regrouping gives

\[
{\cal L}B_z^{(0)}(x)
=e^{-x}-C_z(x),
\]

\[
C_z(x)=
\sum_{\substack{P^-(n)>z\\\omega(n)\ge2}}
(\omega(n)-1)e^{-nx}\ge0.
\tag{1}
\]

At the canonical critical scale \(x_z=\lambda_z/z^2\),
\(\lambda_z+\frac12\log\lambda_z=\log z\), the positive defect is

\[
C_z(x_z)
\sim\frac{x_z^{-1/2}}{2(\log z)^3},
\tag{2}
\]

and is asymptotically carried by squarefree rough semiprimes.  The proposed source was to lift
this positive breadth-two current through a singular inverse-Lambert relation and use its
near-square-root capacity to orient \(B_z^{(0)}\).

## Killing identity

The proposal assigns the positive current to the wrong preimage.  The exact Route E sector
decomposition is

\[
\Phi=B_z^{(0)}+R_{\ge2,z},
\tag{3}
\]

where \(R_{\ge2,z}\) is the already-controlled two-or-more-large-prime remainder.  The classical
ordinary-lattice identity and `(1)` are

\[
{\cal L}\Phi=e^{-x},
\qquad
{\cal L}B_z^{(0)}=e^{-x}-C_z.
\tag{4}
\]

Subtracting `(4)` and using `(3)` gives, without an estimate,

\[
\boxed{{\cal L}R_{\ge2,z}=C_z.}
\tag{5}
\]

Therefore inverse-Lambert return of \(C_z\) reconstructs the admissible remainder
\(R_{\ge2,z}\), not the hard zero/one boundary.  Once this current is removed, the forward datum
is the vacuum \(e^{-x}\), whose physical Möbius inverse is exactly

\[
{\cal L}^{-1}e^{-x}=\Phi.
\]

A bound for that inverse is `OPEN-SOURCE-001`.  The semiprime current does not provide it.

## Strongest positive survivor

The route exposes an exact and quantitatively sharp scalarization law.

1. Small-prime divisor fibres cancel by Boolean inclusion--exclusion.
2. Rough prime-power fibres cancel exactly.
3. Every transverse rough support has coefficient \(1-\omega(n)<0\).
4. If \(xz^2\sim\log z\), breadth two dominates:

   \[
   C_z(x)
   \sim
   \frac{z^2e^{-xz^2}}
        {2(xz^2)^2(\log z)^2}.
   \]

5. At the sharp critical aperture this is `(2)`.
6. Identity `(5)` proves that ordinary Lambert scalarization places all this positive capacity
   in the already-admissible error sector and erases the hard vacuum preimage.

The survivor sharpens source architecture: a viable ordinary-integer mechanism must act before
Lambert scalarization or add an independent co-Poisson boundary condition selecting the vacuum
preimage.  Positivity of the rough-composite image cannot do so.

## Hostile audit

- No RH or zero-free estimate enters `(1)` or `(5)`.
- `(2)` uses only PNT with its classical remainder and endpoint Laplace asymptotics.
- The route is not retired because inversion is technically difficult; it is retired because its
  proposed positive source is exactly the image of the wrong, already-controlled sector.
- Generic inverse-Lambert stability on the remaining vacuum is the original reciprocal-zeta
  problem and is not counted as a replacement conjecture.
- Literature search located general semiprime counting and standard Laplace/PNT machinery, but
  not the moving lower-prime-cutoff asymptotic `(2)` or its Route E scalarization identity.
  Positive survivor remains `[CANDIDATE NEW SCIENTIFIC KNOWLEDGE; NOVELTY UNVERIFIED]`.

## Status

`RETIRED`.  Exact positive survivor retained.  `OPEN-SOURCE-001` remains open.
