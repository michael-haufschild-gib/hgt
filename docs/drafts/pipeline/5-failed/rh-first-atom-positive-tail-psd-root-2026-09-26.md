# Exact first-atom PSD fails on every real tail

- **ID:** RH-FIRST-ATOM-POSITIVE-TAIL-PSD-ROOT-20260926
- **Stage:** 5-failed
- **Type:** [BRIDGE] obstruction test; RH unresolved
- **Owner:** root
- **Parent:** `../1-in-progress/rh-first-atom-tail-audit-root-2026-09-26.md`

## Frozen statement and outcome

Let f(x)=thetaCuspSourceTerm x 1 and
`K_f(x,y)=integral_(s>0) (x+y+2s) f(x+s) f(y+s)`.
For every real a, there exist n, real x_i>a, and real b_i such that
`sum_ij b_i*b_j*K_f(x_i,x_j)<0`.
Thus no real tail has PSD first-atom Gram matrices at every rank.

This statement passes Lean scratch. Named leaf and axiom audits pending.
No claim concerns the sign of the complete even theta kernel.

## Dependency-closed paper proof

1. Prior exact moment identity gives a negative incoming diagonal for K_f:
   `integral exp(2x) f²=[75/(44*pi)] integral f²` and
   `integral 2x f²<0`. Hence some K_f(x,x)<0.
2. The actual first atom is entire. On any closed substrip |Im z|<=delta<pi/4,
   the explicit Gaussian bound gives `|f(z)|<=C exp(-|Re z|)`.
   At positive Re z use `t³/6<=exp(t)` to absorb the polynomial prefactor;
   at negative Re z the Gaussian factor is at most one.
3. Define L2 sections `g±(z,s)=1_(s>0)(z+s±1) f(z+s)`.
   On each compact parameter ball they admit an L2 majorant
   `C exp(-|s|/2)`. For any L2 vector v, Cauchy–Schwarz makes
   `|v(s)| C exp(-|s|/2)` integrable. Dominated Cauchy differentiation
   proves every scalar Hilbert pairing holomorphic.
4. In the two-copy L2 space, J=diag(1,-1) is bounded Hermitian and
   `<g(y),Jg(x)>=2 K_f(x,y)` for real x,y. Compress J to the closed
   span of all strip sections, preserving these pairings.
5. Every real tail has an accumulation point inside the connected strip.
   Analytic uniqueness makes its section span dense in the same Hilbert
   space. Continuity of the quadratic form transports a strict negative
   vector to a finite combination of tail sections.
6. Since K_f is real, the complex packet energy is the sum of its real
   and imaginary coefficient energies. At least one is negative. Enumerate
   its finite support to obtain exactly the frozen finite real-node statement.

## Strongest positive survivor

For every strip source satisfying these analytic bounds, **all finite negative
dimensions are invariant under restriction to any real tail**. This applies
both to the exact first atom and the complete theta source, with exact kernel
identification in each case. The generic proof and both actual instantiations
are Lean-closed in scratch. This survivor is stronger than transporting one
negative diagonal: it preserves the entire finite negative-index profile.

Files:
- `formal/GaloisForLFunctions/RHTower/AnalyticDominatedL2Sections.lean`
- `formal/GaloisForLFunctions/RHTower/ThetaTailAnalyticLocality.lean`
- `formal/GaloisForLFunctions/RHTower/ThetaFirstAtomTailLocalityObstruction.lean`

## Whole route

The all-rank corrected logarithmic-Cauchy model remains positive. Its exact
first-atom realization nevertheless fails on every tail; therefore its
uncontrolled remainder is sign-decisive at suitable rank. Complete theta's
higher atoms cannot be discarded merely because they are small pointwise.

The complete-source realization also shows why choosing a farther analytic
tail cannot remove a genuine negative direction. Fixed finite configurations
can become positive under translation while other configurations retain the
same negative index. The missing full-source sign remains the actual target.

## Novelty and scope audit

Analytic uniqueness and abstract index locality already exist in the corpus.
New bridge: verify the literal theta/first-atom L2 hypotheses and exact kernel
identity, then combine with the exact first-atom center obstruction. No claim
of global mathematical priority. No numerical experiment or RH assumption.
