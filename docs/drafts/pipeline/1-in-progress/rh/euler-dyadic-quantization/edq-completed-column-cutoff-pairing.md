# EDQ: signed cutoff after completed-column inversion

- **ID:** EDQ-COLUMN-CUTOFF-PAIRING
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Statement:** Control the finite subtraction in completed coprime kernel columns, retaining its signed boundary and every time window.
- **Status:** No stronger arithmetic bound obtained. Arguments below are on paper, not new Lean results. EDQ remains open.

## Proof target

Euler deletion → cofinal subpower control of the complete signed physical
source/current → exclusion of off-line zeros → RH.

EulerDeletionCompletedColumnMain controls the aggregate error after the
Euler main of each complete column. The finite numerator subtraction
remains uncontrolled at the required scale. This note tests first-crossing
cancellation and real stability against that subtraction. It does not
retire EDQ or close a no-go card.

## Exact cutoff coefficients

Use the corpus kernel

\[
 P_b(n)=\frac{(n\bmod b)^2}{2b}-\frac{n\bmod b}{2},\qquad
 K(a,b)=\sum_{j\ge1}\frac{P_b(aj)}{(aj)^2}.
\]

For positive integers \(A,m,b\), put

\[
 H_A(m,b)=\sum_{\substack{1\le a\le A\\(a,m)=1}}\mu(a)K(a,b),\qquad
 T_{A,m}(n)=\sum_{\substack{a\mid n\\a>A\\(a,m)=1}}\mu(a).
\]

With \(C(m,b)\) the complete coprime kernel column, exact regrouping gives

\[
 C(m,b)-H_A(m,b)
   =\sum_{n\ge1}\frac{P_b(n)}{n^2}T_{A,m}(n).                 \tag{1}
\]

Expand \(K\) and group \(aj=n\). The rearrangement is absolute:
\(|P_b|\le b/8\), and the sum of \(b/(8a^2j^2)\) is finite.
Thus (1) retains the entire infinite numerator/time tail.

**First prime pairing.** If \(p\mid n\) is prime and \(p\nmid m\), then

\[
 T_{A,m}(n)=-
 \sum_{\substack{d\mid n,\ p\nmid d,\ (d,m)=1\\A/p<d\le A}}\mu(d). \tag{2}
\]

Discard zero Möbius coefficients and pair \(d\) with \(pd\), where
\(p\nmid d\). Both divide \(n\), have the same coprimality admission,
and have opposite signs. Pairs wholly above or below \(A\) cancel or
contribute nothing. A crossing pair satisfies \(d\le A<pd\) and
contributes \(-\mu(d)\). Higher powers of \(p\) in \(n\) cause no
exception: divisors containing \(p^2\) have zero coefficient.

If every prime of \(n\) divides \(m\), the only admitted divisor is \(1\),
so \(T_{A,m}(n)=0\). This is the already identified prime-support cancellation.

**Second prime pairing.** For distinct admitted primes \(p<q\) dividing
\(n\), write \(W(d)=1_{A/p<d\le A}\). Equation (2) becomes

\[
 T_{A,m}(n)=-
 \sum_{\substack{e\mid n,\ (e,pq)=1,\ (e,m)=1}}
 \mu(e)\bigl(W(e)-W(qe)\bigr).
\]

The windows \((A/p,A]\) and \((A/(pq),A/q]\) are disjoint because
\(p<q\). This toggle does not itself cancel their signed masses.
Choosing the larger prime first cancels the overlap and returns the
same two remaining windows.

**First time window.** For \(A<n\le2A\),

\[
 T_{A,m}(n)=\mu(n)\,1_{(n,m)=1}.                            \tag{3}
\]

Every proper divisor of \(n\) is at most \(n/2\le A\). The sole possible
tail divisor is therefore \(n\). The first window of (1) is the original
signed Möbius sum against \(P_b(n)/n^2\). All windows \(n>2A\) remain;
(3) is not a lower bound for the full signed tail.

Taking absolute values does not give the target. The existing kernel
envelope gives a column cost at most
\((b/4)\sum_{a>A}a^{-2}\le b/(4A)\). In the physical triangle
\(A=\lfloor N/r\rfloor,\ b\le A\), summation with weight \(1/r\)
still has a linear ceiling. No signed improvement is proved here.

## Reflection and stability tests

A broad newest-first arXiv search for **reciprocity** found Weiqi Jiang's
8 September 2026 paper,
[Real stability of layer-refined antichain polynomials for three-chain products with a two-element factor](https://arxiv.org/html/2609.10609v1).
Its inspected proof uses an explicit first-crossing reflection and inverse
to count the off-diagonal term of a two-path determinant. Jacobi
interlacing then makes residues of a rational function positive.
These are mechanisms to test, not arithmetic theorems about EDQ.

The divisor toggle above preserves weight at fixed \(n\), but leaves its
cutoff boundary. For a fixed nonzero residue modulo \(b\), the numerator
\(P_b(n)\) is a fixed negative number. Equality of \(P_b(n)/n^2\) at
two positive integers in that residue class forces the integers to
coincide. Residue preservation alone therefore cannot pair distinct
boundary integers of opposite sign without a weight correction.

Generic stability of the product-cutoff subset polynomial fails directly.
Take the squarefree divisors of \(2\cdot3\cdot5\) through cutoff \(6\),
with variables \(x,y,z\) for the three primes. Their polynomial is

\[
 f(x,y,z)=1+x+y+z+xy=(1+x)(1+y)+z.
\]

At \(x=y=-2+i,\ z=2i\), all imaginary parts are positive and \(f=0\).
Thus this literal cutoff polynomial is not real stable. This is a
symbolic algebraic argument, not a numerical experiment. It rejects
generic product-cutoff stability; it does not exclude a different,
explicitly constructed stable EDQ object.

## Transport pivot

For integers \(b\ge1\), \(|P_b(t+1)-P_b(t)|\le1/2\), including
the wrap from residue \(b-1\) to \(0\). Together with \(|P_b(t)|\le b/8\),
this gives, for integers \(n,n'\ge L\ge b\),

\[
 \left|\frac{P_b(n)}{n^2}-\frac{P_b(n')}{(n')^2}\right|
       \le \frac{3|n-n'|}{4L^2}.                          \tag{4}
\]

For one step, split the changes of \(P_b\) and \(t^{-2}\), using
\(t^{-2}-(t+1)^{-2}\le2t^{-3}\). The bound is
\(1/(2t^2)+b/(4t^3)\le3/(4t^2)\); telescope to obtain (4).

An arithmetic transport could spend this displacement cost and retain
all unmatched mass. But no matching, fractional transport, or residual
mass bound has been proved for (1). The inspected corpus theorem
RHTower.exists_injective_dampedLaplaceTransport_of_hall, in
MobiusBoundaryOppositeSignTransport,
requires actual Hall inequalities and an edge envelope; it also uses a
different, exponential kernel. Another conditional transport receiver
would leave the arithmetic gap intact.

## Search audit and remaining target

Three deep searches used all retrieval views, no module cap, cached
index, at most two rounds, and a 120-second budget:

| Query | Result |
| --- | --- |
| method finite coprime column truncation signed remainder hyperbola reciprocity (OR) | Partial; generation 867859, coverage pending; no candidate/source-argument/idea/ingredient entries. |
| involution cancellation boundary (OR) | Partial; source inventory 56,798 complete, most compiler states pending; 20 source arguments, no candidate lemmas or proof ideas, one generic involution ingredient set. |
| transport | Partial; source inventory 56,804 complete, most compiler states pending; 20 candidate lemmas, 20 source arguments, two proof ideas, one ingredient set about transporting algebraic operations. |

The latter two report unavailable semantic retrieval. No service was
started. Candidate/source entries were source-only, applicability
unchecked. All returned lanes were inspected; none supplied the
arithmetic pairing. Source-text searches located the existing Möbius
transport and Gibbs-cardinality modules. The additional broad arXiv
search for coupling returned older material; its newest-first page
was unavailable.

A broader corpus hit was checked beyond its title:
CoupledFloorMobiusCriticalBoundaryCancellation proves strong \(L^2\)
convergence for \(e^{-(1+\omega)t}E_\omega(e^t)\), \(0<\omega<1/2\).
Its source bound is \(E_\omega(X)=O(X^{1-\omega})\), proved by absolute
values, and its incidence uses \(\mu(d)d^{-1-2\omega}\). The theorem
supplies no bounded comparison to the complete EDQ cutoff source.

The remaining target is a quantitative estimate of (1), jointly over
the physical \(r,b\) triangle, keeping the Euler main and finite
subtraction together. The first interval (3), later intervals, and
their mutual signed cancellation remain uncontrolled. No RH proof,
falsification, stronger source bound, new Lean theorem, or completed
no-go is claimed.

No computations, Lean builds, axiom re-audits, or frontier-map edits
were performed for this note.
