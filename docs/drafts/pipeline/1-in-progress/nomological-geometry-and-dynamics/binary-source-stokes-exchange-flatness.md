# Binary source--Stokes exchange flatness

- **ID:** `ngd-binary-source-stokes-exchange-flatness`
- **Stage:** 1 — in progress
- **Type:** FROZEN CONJECTURE / SOURCE-NORMAL HIGHER OPERATION
- **Status:** `[OPEN CORE] [RH-BEARING] [BINARY COEFFICIENT-CHANGING EXCHANGE]`
  `[NOT A PROOF] [NO LEAN WRITTEN]`
- **Statement:** Construct, before divisor specialization, the source-normal binary exchange cell
  comparing multiplicative clock composition with additive defect composition, and derive its
  flatness from an independent Euler--Poisson--Gamma source law.

## Frozen conjecture

Let `chi` be the pre-divisor half-density clock character and `kappa=chi-1`.  Let `Sigma(m,n)` be
the normalized rational-adelic clock simplex from the Pipeline-2 clock-curvature theorem.  On the
top-conormal coefficient stack, construct a canonical coefficient-changing exchange `2`-cell

\[
 \mathfrak X_{m,n}:
 \bigl[\text{compose clocks }m,n\text{ then take finite defect}\bigr]
 \Longrightarrow
 \bigl[\text{Baer/additively compose the two individual defects}\bigr]
\tag{1}
\]

before any Xi divisor is chosen.  Its Beck--Chevalley curvature must specialize coefficient-
faithfully to

\[
 K_{m,n,\rho}
 =\kappa_\rho(m)\kappa_\rho(n)c_\rho[\Sigma(m,n)],
 \qquad c_\rho\ne0.
\tag{2}
\]

There must be an independently constructed singular prime--infinity reporter `J` satisfying:

1. `J` is defined and proved conservative on the source class before Xi specialization;
2. its Bianchi/Stokes law follows from the literal Euler--Poisson--Gamma source, not from `(2)`;
3. `J(K_(m,n,rho))=0` for the specialized physical section;
4. it retains the corrected Kummer prime cycle and valuation coframe;
5. it is outer/non-inner and nonhomogeneous under the radial gauge;
6. it preserves multiplicity grade and the trace-one ordinary-prime pointing.

For `m=n=p`, Items 1--6 and `(2)` would give

\[
 0=\kappa_\rho(p)^2c_\rho,
\tag{3}
\]

and hence `Re(rho)=1/2`.  The whole burden lies in constructing `mathfrak X` and proving the
independent reporter law; Equation `(3)` is only the consumer.

## Why this is a higher-field conjecture

Unary source-null-homology asks one boundary to kill one measured defect.  The Pipeline-2 theorem
proves that first-order cyclic/Kummer geometry cannot do so: inner corrections preserve its prime
period.  Finite holonomy has the nonlinear law

\[
 \kappa(mn)=\kappa(m)+\kappa(n)+\kappa(m)\kappa(n).
\tag{4}
\]

Thus the missing source law must govern **composition of laws**, not one landed vector.  Its
primitive is a `2`-cell between two legal compositions, exactly the categorical level at which
Nomological Geometry and Dynamics claims curvature should live.

## Construction target

The smallest viable coefficient system must simultaneously contain:

- rational-adelic multiplication and the normalized Hochschild simplex;
- the Kummer trace--derivation period;
- Gamma/co-Poisson source normalization;
- semi-infinite prime--infinity polarization or an equivalent Tate determinant line;
- the Xi top-conormal coefficient as a later realization, never as source data.

The expected exact sequence is not fixed.  Candidate constructions must first produce the binary
cell and its reporter domain, then compute `(2)`.  Defining the cell by declaring its curvature to
be `(2)` is forbidden.

Ordinary group cohomology is explicitly excluded.  With trivial additive coefficients,

\[
 d_{grp}\kappa(g,h)=-\kappa(g)\kappa(h),
\tag{5}
\]

so the binary curvature class is zero for every character.  The missing datum must retain the
normalized primitive and use a singular coefficient-changing reporter; merely naming an `H^2`
class loses exactly the information at issue.

## Hostile falsifiers

1. The only available binary comparison is inner or differs from an inner comparison by a
   Hochschild coboundary.  Then the nonzero Kummer period survives and the conjecture fails.
2. The reporter is invariant under the radial gauge or depends only on determinant-one/reflection
   balance.  Off-centre group-algebra countermodels then survive.
3. The reporter kills the trace-one prime atom or mixes multiplicity grades.
4. Its domain condition is equivalent to `kappa=0`, zero-aperture trace membership, or an already
   critical-line-supported derived fibre.
5. It is defined after choosing `rho`, `c_rho`, or the desired zero of `(2)`.
6. A literal off-line generalized-Euler source satisfies every claimed pre-target axiom and the
   reporter law.  Then the proposed source law is not selective.
7. It factors only through the ordinary group-cohomology class of the binary curvature.  That
   class is identically zero by `(5)`.

## Countermodels every construction must defeat

1. `A=C[Q_(>0)^x]` with identity-coefficient trace and `chi_t(q)=q^t`, `t!=0`: all group, bar,
   trace, multiplicativity, and reflection laws hold, but `kappa_t(p)^2!=0`.
2. `diag(p^t,p^(-t))` preserves determinant and a hyperbolic pairing for every `t`; reflection and
   indefinite Stokes balance do not flatten `(2)`.
3. Any inner-corrected derivation comparison retains the Kummer prime period by the Pipeline-2
   rigidity theorem.

## Conjecture/proof/fail ledger

1. Unary strict landing — algebraically impossible off unit monodromy.
2. Product trace as homology cocycle — false; it measures normalized boundaries.
3. Kummer cyclic cocycle as selector — detects the atom but is radial-gauge blind.
4. Inner connection repair — impossible by cyclic-period rigidity.
5. Additive Bockstein model of finite holonomy — misses the quadratic term `(4)`.
6. Ordinary binary group cohomology — class is always zero and forgets the normalized primitive.
7. Para-`S`/target Connes exactification — supplies target uncurving but not source-normal lift.
8. **Frozen survivor:** an outer binary exchange with independent singular reporter.

## Circularity audit

Binary flatness at one divisor and one prime is equivalent to critical-line placement, so this is
not an easier criterion and not an RH proof.  Its scientific content is upstream: a candidate must
construct a source operation whose independently proved coherence has `(2)` as its physical
realization.  Assuming `J(K)=0`, defining `J` from `K`, or admitting only neutral characters is
circular.

## Gates

- [x] exact nonlinear clock law proved
- [x] inner-correction and first-order producer no-gos proved
- [x] normalized literal Hochschild source simplex constructed abstractly
- [x] physical coefficient target identified
- [ ] literal coefficient-changing binary exchange cell constructed
- [ ] independent prime--infinity reporter and domain constructed
- [ ] source Bianchi/Stokes law proved before divisor specialization
- [ ] coefficient fidelity and multiplicity preservation proved
- [ ] off-line countermodels excluded at a named source axiom
- [ ] hostile circularity audit passed

## Literature and Lean boundary

Closest parent formalisms are para-`S` modules, secondary Hochschild derivations, crossed-product
cyclic homology, and bivariant Beck--Chevalley theory.  They provide the categorical level, not the
arithmetic cell.  No Lean code should be written until the source operation and reporter are fixed
and paper-closed.

## Log

- 2026-08-08 — frozen after unary source-dagger attack produced the exact multiplicative
  Maurer--Cartan clock boundary and proved inner-corrected first-order transport cannot erase the
  Kummer period.
