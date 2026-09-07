# EDQ complete-period residue covariance

Stage: 3-formalized. [BRIDGE] derived theorem; paper proof and Lean proof complete.
Full chain: Euler deletion → exact complex zero balance → signed arithmetic separation → off-line exclusion → RH.

The missing source comparison concerns the complete signed modular Gram. This
bridge isolates what exact period averaging preserves, before using any weighted
chronological estimate. It does not replace the missing cofinal logarithmic ceiling.

## Dependency-closed paper derivation

For a positive modulus m define c_m(k)=(k mod m)-(m-1)/2. Over every common
positive period P of m and n,

    sum_(k<P) c_m(k)c_n(k) = P*(gcd(m,n)^2-1)/12.

Write m=g*a, n=g*b with g=gcd(m,n) and a,b coprime. At k=g*j+i, 0<=i<g,
the centered residues are g*c_a(j)+c_g(i) and g*c_b(j)+c_g(i).
Chinese remaindering makes the a- and b-residue coordinates independent over
ab indices. Each has zero sum, so their conditional product sum is ab*c_g(i)^2.
The elementary square moment is sum_(i<g)c_g(i)^2=g*(g^2-1)/12.
Repetition gives every common period, with no limiting interchange.

Consequently, for any real coefficients u_m on positive moduli dividing P, the
period mean of sum_m u_m*(k mod m)/m is
sum_m u_m*(m-1)/(2m), and its centered second moment is exactly

    (1/12)*sum_(m,n) u_m*u_n*(gcd(m,n)^2-1)/(m*n).

The literal Möbius primitive therefore has mean (M_N-H_N)/2 and the corresponding
complete signed gcd-square covariance. Both Möbius signs and all common factors
remain present. The full second moment is mean squared plus this covariance.

For each residue r modulo P let

    W_P(r)=sum_(j>=0) 1/((r+P*j)*(r+P*j+1)),

with the zero-index summand equal to zero. The actual squared modular carrier
norm is exactly sum_(r mod P) abs(A_N(r))^2*W_P(r). Genuine summability and
periodicity justify this reindexing of the complete infinite series. The weights
are retained individually, including every nonzero multiple in the zero residue.

## Boundary of the result

These are complete-period identities. The existing carrier norm uses the
nonconstant weight 1/(k(k+1)); its full energy cannot be replaced by a period
average without controlling the resulting weighted remainder. The period may
grow extremely rapidly with the channel cutoff. No logarithmic energy ceiling,
source-current annihilation, off-line zero, or RH conclusion is asserted.

## Corpus and scientific-method audit

The existing coprime-period factorization supplies the CRT step. The reflected
logarithmic Gram controls the increment covariance gcd(m,n)-1, but does not
identify the covariance of the residue primitives. The existing Gram-residue
decomposition handles individual diagonals with their exact progression weights.
The common-divisor Abel cross decomposition retains masks for a different source.
None of these supplies the claimed primitive pair moment directly.

This is a derived [BRIDGE] under docs/meta/scientific-method.md, not a new primary
conjecture. The displayed result is predicted by the paper proof, so no numerical
experiment is justified or planned. The original RH objective remains unchanged.

## Lean status

`EulerDeletionMobiusPeriodCovariance.lean`, namespace
`RHTower.DeletionPeriodCovariance`, contains five definitions and fourteen public
theorems. Both factorial-period specializations are unconditional at every channel
cutoff. The complete scratch passed without diagnostics; the final targeted leaf
build compiled only this module. All nineteen new public declarations have been
audited once and depend only on `propext`, `Classical.choice`, and `Quot.sound`.
The leaf is wired into `RHTower.lean`; no umbrella build or numerical experiment
was run. The search index and scoped source, umbrella, documentation-link, and whitespace
checks are complete. Repository lint found one unrelated concurrent unwired module,
`FiniteDirichletCriticalNonannihilation`; no new EDQ lint error was reported, and the
global gate is not claimed to pass. All owned Lean processes exited and temporary
proof/API/audit source files were removed. The [related averaging obstruction and
formal positive survivor](../5-failed/edq-period-average-growth-obstruction.md) retain
the actual progression weights identified here.
