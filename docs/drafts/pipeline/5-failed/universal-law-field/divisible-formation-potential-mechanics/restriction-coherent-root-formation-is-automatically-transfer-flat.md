# Failed conjecture: restriction-coherent root formation is automatically transfer-flat

- **Status:** [FAILED] [EXACT COUNTERTHEOREM] [POSITIVE SURVIVOR EXTRACTED]
- **Parent:** ULF-DFPM-5

## Conjecture

A coherent tower of root holonomies should already be compatible with every canonical change of
root depth.  If true, ordinary root coherence would force divisor charge zero.

## Failure

For integer charge \(q\), the depth-
\(n\) holonomy is \(q_n=[q]_n\).  If \(n\mid m\), reduction satisfies

\[
 R_{m,n}(q_m)=q_n
\]

for every \(q\).  Thus the usual root tower is perfectly restriction-coherent even when the
divisor is nonzero.

The opposite-variance transfer sends

\[
 T_{n,m}([x]_n)=[(m/n)x]_m.
\]

For every \(q\ne0\) and every \(n>|q|\), the doubling defect is

\[
 q_{2n}-T_{n,2n}(q_n)=[-q]_{2n}\ne0.
\]

Restriction and transfer are not inverses, and one variance cannot manufacture the other.

## Positive survivor

The ambidextrous defect obeys the exact crossed composition law

\[
 \Delta_{n,\ell}
 =\Delta_{m,\ell}+T_{m,\ell}\Delta_{n,m}
 \qquad(n\mid m\mid\ell),
\]

its cofinal doubling family reconstructs the integer charge, and its global regular packet is a
compact perturbation of identity exactly at charge zero.  The useful missing source theorem is
therefore not “coherent roots”; it is simultaneous restriction--transfer horizontalness.

No Lean was written or built in this research pass.
