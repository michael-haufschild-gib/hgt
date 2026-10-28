# Spectral exhaustion by torsion-adjunction energies

- **ID:** full-prime-spectrum-adjunction-exhaustion
- **Stage:** 0-backlog
- **Type:** CONJECTURE
- **Source:** Ramanujan full-matrix quasimodes; harmonic rough-number tensorization; prime-defect Dirichlet form
- **Statement:** Every bounded energy window of `log(N) I-P_N` converges, with multiplicity, to the simple energies `gamma+log(m)+tameDifferent(m)`.
- **Count:** uncounted; novelty, full paper proof, and Lean remain

## Goal

The finite-packet quasimode project provides actual nearby eigenvalues for each
fixed conductor. It does not exclude additional bounded-energy branches. The
proposed theorem would identify the entire bounded-energy spectrum and its
eigenvectors, thereby determining every fixed ordered eigenvalue asymptotic.
The optimal pole gap would be a consequence, not a separately counted numerical
improvement. No full Weil positivity or RH implication is asserted.

## Gates

- [ ] Full corpus novelty and significance audit.
- [ ] Dependency-closed paper proof of compactness and spectral exhaustion.
- [ ] Exact Lean realization, direct source checks, transitive axioms, umbrella wiring.

## Existing input inspected

`ThePrimeFormHasASpectralGapBelowItsPole.lean` and its formalized card were read
in full. Its public result gives one uniform positive pole-complement gap.
`TheHarmonicMeasureTensorizesOverPrimes.lean` was inspected at definitions and
the complete final induction, lines 540--725. Inside that proof the local
`claim` bounds every rough interval, not merely its published Q=0 specialization:

`harmonicVar Q X f <= K*exp(Psi(Q,X))*glauberForm Q X f`.

For X>=2, `Psi(Q,X)=-A*S(Q)/log(X)<=0`, so one constant K bounds all rough
intervals. The small-X cases have zero variance. Exposing and auditing this
stronger interface remains necessary; the local claim is not an available
public Lean declaration. Reuse this argument rather than assume rough-fibre
tensorization. Its proof is baseline, not independently new mathematics.

Initial whole-corpus and RAPT-restricted searches returned the existing single
gap, finite-sieve spectrum, finite-class horizon limits, and unrelated Ramanujan
prefix/PM/CCM matrices. The current RAPT README's spectrum/module description
was checked through its new tensorization and gap entries. These first searches
did not exhibit bounded-window exhaustion of the literal prime matrix. This is
only an initial novelty audit, not an assertion of exhaustive novelty.

The initial HTGeometry machinery search returned generic compact-operator
spectral finiteness (`CompactOperatorDiscreteSpectrum`,
`CompactOperatorBoundedBelow`) and spectral approximation/Schur lemmas for
other operators. Their statements were inspected in the search results;
their sources have not yet been audited for use. No ready-made variable-horizon
arithmetic compactness certificate was identified by that search.

## Proposed compactness mechanism

Write `y(n)=sqrt(n)*x(n)` and let D_N be the literal pole-defect Dirichlet form.
The ground-state top-control inequality already used by the spectral-gap proof
gives, for each small eta and all sufficiently large N,

`<x,(log(N)I-P_N)x> >= (gamma-eta)||x||^2+(1-eta)D_N(x)`.

Thus bounded renormalized energy controls D_N. Two separate truncations should
make these bounded-energy vectors uniformly close to a finite Ramanujan span.

1. Fix P>1 and condition harmonic measure on the prime valuations below P.
   Each fibre is `n=d*k`, with fixed small-prime part d and P-rough k<=N/d.
   Uniform rough tensorization, together with the same disjoint ladder-edge
   bound but `log(q)>=log(P)`, should give

   `||x-E_(P,N)x||^2 <= K*D_N(x)/log(P)`.

   Here E is harmonic conditional expectation in pole gauge, transported back
   to ordinary Euclidean coordinates. The exact fibre identity and scaling
   must be proved; they are not assumptions of the target.

2. For each fixed small prime p, the elementary inequality
   `(a-b)^2 >= a^2/2-b^2`, summed over its downward prime-power edges, suggests

   `sum_n v_p(n)*|x(n)|^2 <= 2*D_p(x)/log(p)+2*||x||^2/(p-1)`.

   Every n has v_p(n) downward p-edges. The negative terms reindex as a
   geometric sum bounded by `||x||^2/(p-1)`. This bounds mass outside any fixed
   box of the small-prime valuations by O(1/L), uniformly in N. Conditional
   expectation contracts that same box-complement norm because the box is
   measurable in the conditioning variables.

   Existing exact interfaces were checked in
   `TheDeficitOfThePrimeFormIsADirichletEnergy.lean`: `sum_edges_eq_sum_divisors`
   reindexes all edges by their top; `log_mul_ladderDefect_le` bounds one
   prime's edge defect by D_N. The new quasimode support theorem
   `sum_divisors_primePower_mangoldt` counts the prime-supported divisor atoms,
   while `sum_dvd_vonMangoldt_div_le` bounds the reciprocal bottom-edge mass.
   Thus the moment estimate can reuse exact existing reindexing. A coarser
   bound with D_N in place of each D_p suffices after summing the finitely many
   small primes; no sharp aggregate constant is needed for compactness.

The two orthogonal errors add: conditional variance plus the discarded
conditional mean. First choose P large, then a valuation cutoff L large.
The remaining space has dimension independent of N. Its vectors are linear
combinations of `1_(small-prime valuations=e)/sqrt(n)` for finitely many e.
Each one-prime shell indicator is an exact finite linear combination of the
ground and valuation steps, by triangular inversion of their displayed values.
Taking products puts this space inside a fixed finite Ramanujan-conductor span.
The required inversion, coordinate projection, and uniform estimates remain
unproved here.

The corpus already supplies the needed finite divisor-to-Ramanujan inversion:
`RHTower.pm_ramanujan_sum_divisors` in
`PMPowerDampedMobiusRamanujanExpansion.lean`, whose statement and proof were
read, gives `sum_(q divides d)c_q(n)=d*1_(d divides n)` for positive d,n.
Taking real parts and the existing coefficient-identification bridge should
express each divisibility indicator in the finite normalized Ramanujan span.
Each exact valuation shell is the difference of two such indicators; products
are indicators at the product modulus because the primes are distinct.
This removes any need for a new abstract triangular-inversion theorem.
The application and its exact finite-span statement remain unformalized.

## Proposed exhaustion step

Use the actual Ramanujan Gram and residual limits from the quasimode project.
For a normalized actual eigenvector at bounded renormalized eigenvalue lambda,
its inner product with a normalized Ramanujan profile of energy E is bounded
by that profile's residual divided by `|lambda-E|`. Uniform approximation by
a fixed finite span then excludes spectral points a fixed distance from every
energy in that span. A subsequence argument must retain the established common
lower bound and properness of E(m)>=gamma+log(m).

To exclude extra multiplicity near one E, a spectral cluster of dimension at
least two contains a unit vector orthogonal to the corresponding Ramanujan
profile. All other profile coordinates are small by energy separation and the
cluster residual bound. The finite-span approximation then contradicts unit
norm. This also suggests convergence of each simple spectral projection to the
normalized Ramanujan line. A complete finite-dimensional argument with explicit
quantifiers is still required; this card is not a paper-proof completion.

A useful finite certificate would avoid constructing an infinite operator first:
for each fixed energy ceiling R, find a finite conductor set S and c>0 such
that every unit vector of energy at most R has
`sum_(m in S)|<v_(m,N),x>|^2>=c` eventually, where
`v_(m,N)=u_(m,N)/sqrt(log(N))`. The proposed approximation estimate and the
finite Gram limit should imply this. For each energy in S, choose disjoint
small windows. If a window held two orthonormal actual eigenvectors, a unit
vector in their span could be chosen orthogonal to its one Ramanujan mode.
The other mode coefficients would be small by the residual identity and the
separated energies, contradicting the certificate. All steps still require
proof. No conditional certificate is to be substituted for its actual arithmetic
construction.

The strongest useful exact target is: for every real T outside the arithmetic
energy set, the number of actual renormalized eigenvalues below T, counted with
multiplicity, eventually equals `#{m>=1:E(m)<T}`, and their simple eigenlines
converge to the corresponding Ramanujan lines. Properness follows from
`tameDifferent(m)>=0` and `log(m)->infinity`; the exact count and line convergence
do not follow from the current quasimode theorem alone.

## Scope

This is stronger than the proposed coherent ground-state completion: it would
also rule out extra bounded-energy branches of the original finite matrices.
It needs no claim that all high-energy eigenvalues or growing conductor packets
are uniformly controlled. The existing one-gap theorem and generic spectral
compactness machinery are excluded from novelty. No new result is counted.
