# Coupled Sonin vacuum-Feshbach reduction

- **ID:** sonin-coupled-vacuum-feshbach
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper)
- **Source:** physics-literature transfer into the live coupled-Sonin source comparison
- **Statement:** Eliminating the constant-polynomial channel by its scalar Feshbach/Schur
  complement makes RH equivalent to nonnegativity on zero-constant integer tails, and a
  quotient-free coupled-Sonin Rayleigh upper bound only for their canonical target-centered
  representatives implies RH.

## Goal

Remove one complete direction from the open coupled-Sonin source comparison.  The previous
interface asks for a source upper comparison for every integer polynomial, including every choice
of its constant coefficient.  The constant direction is a one-dimensional positive vacuum block
because `normalizedPrimeArchMoment 0 > 0`.  Feshbach elimination shows that only one centered
representative of every zero-constant integer tail must be compared.

This is source-pure at the target interface: the centering scalar uses the fixed continued
prime--Gamma moment functional, not the Xi divisor and not an assumed sign.  The Sonin producer
uses only the explicit coupled column, its polynomial power vector, and concrete nondegeneracy.

## Gates

- [x] 0 → 1 in-progress: well-posed, source-pure, exact physics value identity, direct RH consumer
- [ ] 1 → 2 fully-proven: independent paper audit of all Lean-level algebra and strict comparison
- [ ] 2 → 3 formalized: targeted Lean verification and axiom inspection
- [ ] 3 → 4 publication-ready: standalone theorem, proof, provenance, and Lean certificate

## Physics value relation

Feshbach's projection method splits a quantum problem into selected and eliminated channels.  In
the scalar one-channel case its effective value is the Schur complement.  For a real moment
functional `L_s`, write

```text
p = c + q,                 q(0) = 0,
m0 = s_0 > 0,
b(q) = L_s(q),
R_s(q) = L_s(q^2) - b(q)^2/m0.
```

Then the exact value identity is

```text
L_s(p^2) = m0 * (c + b(q)/m0)^2 + R_s(q).
```

The canonical centered observable

```text
q_perp = q - b(q)/m0
```

satisfies

```text
L_s(q_perp) = 0,
L_s(q_perp^2) = R_s(q).
```

Therefore

```text
forall p, L_s(p^2) >= 0
  iff
forall q with q(0)=0, R_s(q) >= 0.
```

The reusable HTGeometry implementation is
`formal/GaloisForLFunctions/HTGeometry/VacuumFeshbachValue.lean`.

## RHTower specialization

Set `s = normalizedPrimeArchMoment`.  Lean source now defines the countable condition
`PrimeArchVacuumFeshbachIntNonnegative` on zero-constant `q in Z[X]`.  Every integer polynomial
has an integer zero-constant tail, so the positive vacuum square restores the full countable
prime--Gamma Hankel criterion.  Conversely RH makes the centered completed source value
nonnegative.  Thus the source contains the intended equivalence

```text
PrimeArchVacuumFeshbachIntNonnegative <-> RiemannHypothesis.
```

For each zero-constant integer tail define its target-centered real polynomial `q_perp`.  The new
coupled-Sonin producer asks, for every `epsilon > 0`, for one nondegenerate aperture `a` satisfying

```text
normalizedPrimeArchMoment(0) * ||V_a(q_perp)||^2
  <= (R(q) + epsilon) * Re S_0(a).
```

The left side is nonnegative and `Re S_0(a)>0`.  If `R(q)<0`, choosing
`epsilon=-R(q)/2` makes the right side negative, a contradiction.  Hence every Feshbach remainder
is nonnegative and RH follows.

### Weaker source-variational form

The target centering constant is not needed on the Sonin side.  The Mori/Feshbach least-squares
law says

```text
R_s(q) <= L_s((q-c)^2)                 for every real c,
R_s(q)  = L_s((q-b(q)/m0)^2)           at the canonical mean.
```

Therefore the source comparison may choose both its aperture and an arbitrary real scalar
counterterm:

```text
for every zero-constant q in Z[X] and epsilon>0,
  there exist a with C_a!=0 and c in R such that

  normalizedPrimeArchMoment(0) * ||V_a(q-c)||^2
    <= (R(q)+epsilon) * Re S_0(a).
```

This premise is weaker than the target-centered one: choosing `c=b(q)/m0` recovers the former
source vector, while the new interface lets the aperture-dependent Sonin source optimize its own
scalar counterterm.  The norm is nonnegative for every `c`, so the same contradiction proves
`R(q)>=0` and hence RH.  Lean source exposes this as
`SoninCoupledPrimeArchVacuumVarianceRayleighUpperBound` and
`riemannHypothesis_of_soninCoupledPrimeArchVacuumVarianceRayleighUpperBound`.

### Quotient-free Robertson form

The Feshbach remainder is the vacuum--tail Robertson determinant divided by the positive vacuum
mass:

```text
D(q) = m0*L_s(q^2)-L_s(q)^2,
D(q) = m0*R_s(q).
```

Thus the target condition is equivalently the countable two-channel uncertainty family

```text
L_s(q)^2 <= m0*L_s(q^2)       for every zero-constant q in Z[X].
```

This connects directly to the corpus's Robertson/Gram and Rayleigh--Ritz infrastructure.  On the
coupled source side, rescaling the positive error gives the exactly equivalent, fully
quotient-free interface

```text
m0^2 * ||V_a(q-c)||^2 <= (D(q)+epsilon) * Re S_0(a).
```

The Lean source proves equivalence of this interface with the source-variance interface and gives
its direct RH capstone.  The relevant declarations are
`PrimeArchVacuumRobertsonIntNonnegative`,
`primeArchVacuumRobertsonIntNonnegative_iff_riemannHypothesis`,
`SoninCoupledPrimeArchVacuumRobertsonRayleighUpperBound`, and
`riemannHypothesis_of_soninCoupledPrimeArchVacuumRobertsonRayleighUpperBound`.

The RHTower implementation is
`formal/GaloisForLFunctions/RHTower/SoninCoupledVacuumFeshbach.lean`.

## Direct corpus impact

- **Hypothesis reduction:** removes all independent constant-coefficient comparisons from the
  live coupled-Sonin Rayleigh route.
- **Countability retained:** the remaining labels are zero-constant integer polynomials; no
  uncountable test family is introduced.
- **Existing producer reused:** the source side is the already formalized
  `soninAllPrimeCoupledPolynomialPowerVector` and zeroth coupled trace energy.
- **Shared moment cone simplified:** `sequenceTraceHankelNonnegative_iff_vacuumFeshbach` and
  `sequenceTraceHankelNonnegative_iff_vacuumRobertson` expose both divided and quotient-free
  reductions for every RHTower module using `SequenceTraceHankelNonnegative`, including the
  thermal-Krylov, finite-KMS closure, Hausdorff/Bernstein, reflection-positive, and positive
  moment-measure consumers.
- **Nondegeneracy reused:** the existing equivalence `Re S_0(a)>0 <-> C_a != 0` supplies the
  positive cross-multiplication factor.
- **No density-state wrapper:** the result changes the theorem interface.  It does not merely call
  the old normalized Gram quotient a Born expectation.

## Open core

`[OPEN CORE]` Prove the weaker source-variational aperture inequality from the explicit coupled
prime-power and Gamma residual formulas. For each zero-constant tail in the strict centered
analytic-tail residual, both aperture and scalar counterterm may be selected. Feshbach elimination
does not manufacture the source comparison.

The earlier shifted-sector cones in `sonin-coupled-finite-gram-closure-rh.md` do **not**
automatically discharge the new remainder: `Q(q)>=0` alone does not imply
`Q(q)-L(q)^2/m0>=0`. The later formalized centered analytic-tail theorem now discharges one
genuine Feshbach family directly:

```text
tailL1(q) <= 8 |E_PG(q)| -> Var_PG(q) >= 0.
```

Consequently the live source comparison is required only on the strict residual
`8|E_PG(q)| < tailL1(q)`. This is a proper right-edge hypothesis reduction, not full closure; the
residual comparison remains open.

The later centered-Eisenstein residual theorem shrinks this again. It is enough to compare only
tails `q=polynomialVacuumTail(P)` where `P` is monic, Eisenstein at `2`, and has degree in any one
selected infinite set. Under `not RH`, negative residual witnesses occur at all but finitely many
degrees. The remaining comparison is therefore confined simultaneously by vacuum centering,
analytic-tail residual, fixed Eisenstein chamber, and an arbitrarily sparse infinite degree
schedule.

## Literature provenance

1. H. Feshbach, *A unified theory of nuclear reactions*, Annals of Physics 5 (1958), 357--390,
   DOI [10.1016/0003-4916(58)90007-1](https://doi.org/10.1016/0003-4916(58)90007-1).
2. H. Feshbach, *A unified theory of nuclear reactions. II*, Annals of Physics 19 (1962),
   287--313, DOI
   [10.1016/0003-4916(62)90221-X](https://doi.org/10.1016/0003-4916(62)90221-X).
3. H. Mori, *Transport, Collective Motion, and Brownian Motion*, Progress of Theoretical Physics
   33 (1965), 423--455, DOI
   [10.1143/PTP.33.423](https://doi.org/10.1143/PTP.33.423).  This is the statistical-mechanics
   projection analogue; no dynamical or memory-kernel claim is used in the theorem.

## Verification status

Source inspection only.  In accordance with the active user constraint, no Lean invocation,
scratch compilation, lint, axiom inspection, numerical check, targeted build, or full build was
run.  The declarations must not be promoted to stage 3 until targeted verification is authorized.

## Log

- 2026-07-15 — primary physics provenance checked; generic HTGeometry Feshbach identity and the
  zero-constant-tail coupled-Sonin RH consumer written source-only.  No computation or build run.
