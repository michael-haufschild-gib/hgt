# Positive prime-log polynomial jet escape

- **ID:** `positive-prime-log-polynomial-jet-escape`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) — `[PROVED] [FORMALIZED] [BRIDGE]`
- **Lane:** constrained Herglotz source variation; nonlinear finite-jet avoidance
- **Statement:** At every bounded positive prime-log gauge, every nonzero polynomial relation among
  finitely many translated actual differential jets can be escaped inside every bounded-gauge
  neighborhood by a finitely supported positive perturbation.

## The theorem

Let `T` be an infinite index set, let `t:T→R` be injective, and let

```text
A:R^(T,finite)→C^J
```

be the real Cauchy-jet control map for a finite packet `J` of distinct upper-half-plane nodes and
finite jet orders.  Suppose `A` is surjective.  Let `w_s>0` for every `s`, let `x∈C^J`, and let
`P∈C[X_j:j∈J]` be nonzero.  Then for every `eta>0` there are a finitely supported real mass
direction `a` and `0<epsilon<eta` such that

```text
w_s+epsilon a_s>0                    for every s,            (1)
P(x+epsilon A(a))≠0.                                         (2)
```

Consequently the nonvanishing locus of `P` is dense in `C^J`, its zero set is closed and nowhere
dense, and the finite jets attainable from the strict positive mass cone are locally Zariski dense
at every positive base mass.

The packet is not an auxiliary surrogate.  For the prime-log Herglotz source `g_u`, its coordinate
of order `j` satisfies

```text
g_u^(j)(z_i)=j! J_(i,j)(u),                                 (2a)
```

where `J_(i,j)` is the Cauchy packet above.  The proof establishes locally uniform summability of
every Cauchy power and differentiates the series term by term.  Since every `j!` is nonzero,
factorial diagonal substitution is an automorphism of the polynomial relation ring.  Thus escape
for normalized packets is equivalent to escape for the actual iterated derivatives.

For the prime-log carrier, take `T` to be the primes, `t_p=log p`, and

```text
w_p=2^(-p) exp(u_p).
```

The Cauchy-jet map is surjective for every finite distinct upper-half-plane node packet, so (1)--(2)
hold for the actual dyadic prime masses of every gauge `u`.  If `u` is bounded, define the new
gauge by

```text
u'_p=log((w_p+epsilon a_p)/2^(-p)).                          (3)
```

Then `u'` is bounded, agrees with `u` outside the finite support of `a`, and satisfies

```text
2^(-p)exp(u'_p)=w_p+epsilon a_p                             (4)
```

at every prime.  Thus the escape occurs inside the bounded logarithmic-gauge family, not merely in
an ambient signed mass space.  Moreover, for every `eta_g>0`, the perturbation can be chosen so
that

```text
sup_p |u'_p-u_p|<eta_g.                                     (5)
```

The finite support makes the coordinatewise logarithmic reconstruction uniformly continuous at
zero on the active coordinates, while every inactive coordinate is unchanged.

## Proof

Because a nonzero multivariate polynomial over `C` cannot vanish at every point, choose `y∈C^J`
with `P(y)≠0`.  Surjectivity gives a finitely supported real direction `a` satisfying

```text
A(a)=y-x.                                                    (3)
```

Since `a` has finite support and every `w_s` is strictly positive, there is `rho>0` such that

```text
w_s+r a_s>0
```

for every `s` and every `0≤r≤rho`.  On the affine line from `x` to `y`, put

```text
q(Z)=P(x+Z(y-x))∈C[Z].                                      (4)
```

Equation (4) is a nonzero polynomial because `q(1)=P(y)≠0`.  It has only finitely many roots.
Therefore every interval `(0,min(rho,eta))` contains an `epsilon` for which `q(epsilon)≠0`.
Equations (1)--(3) follow. `QED`

Continuity of multivariate polynomial evaluation makes its zero set closed.  The same affine-line
argument supplies a nonvanishing point in every metric neighborhood, so the complement is dense
and the zero set is nowhere dense.

## Positive carrier law

The result is best stated as a positive necessity law:

> **Finite-jet Zariski fullness.** The strict positive prime-log Herglotz cone has full algebraic
> tangent freedom on every finite translated actual differential-jet packet.

Thus a marking that is invariant under all sufficiently small carrier-preserving positive mass
perturbations cannot impose a proper algebraic condition on finitely many jets.  Its finite-jet
Zariski closure must be the whole packet space.

For an RH-oriented carrier this identifies the form of additional structure that is required.  A
selector capable of distinguishing a zeta-like source from the positive prime-log family must use
an infinite compatibility not visible in any finite algebraic jet window: for example global Euler
multiplicativity, a functional-equation polarization, a boundary kernel cone, or a prime-indexed
inverse-limit class.  This is not an RH theorem; it is a constraint on what an RH carrier theorem
must positively preserve.

Equivalently, any selector invariant under these positive gauge perturbations has full finite
differential-jet Zariski closure.  It cannot be characterized by finitely many local differential
equations involving finitely many translates.  Its defining content must survive only at the
global or inverse-limit level.

## Lean certificate

`GaloisForLFunctions.HTGeometry.PolynomialJetEscape` proves:

- `eval_mvPolynomialLine` and `mvPolynomialLine_ne_zero`;
- `exists_small_real_line_eval_ne_zero`;
- `mvPolynomial_nonzero_eval_dense`;
- `mvPolynomial_zero_set_isClosed` and `mvPolynomial_zero_set_isNowhereDense`;
- `surjective_positive_control_escapes_mvPolynomial`.

`GaloisForLFunctions.HTGeometry.PrimeLogPolynomialJetEscape` proves:

- `primeLogPositiveCauchyJet_escapes_mvPolynomial`;
- `primeDyadicCauchyJet_escapes_mvPolynomial`;
- `primeDyadicCauchyJet_escapes_mvPolynomial_in_boundedGauge`;
- `primeDyadicCauchyJet_escapes_mvPolynomial_in_gaugeBall`;
- `primeDyadic_polynomialCoefficientRelation_has_gaugeBall_escape`.

`GaloisForLFunctions.HTGeometry.PrimeLogGaugePerturbation` proves the exact reconstruction (3)--(4),
finite change support, preservation of upper boundedness and two-sided boundedness, and the uniform
smallness law (5).

`GaloisForLFunctions.HTGeometry.DiscreteCauchyJetPacket` and
`DiscreteCauchyJetDerivatives` prove the exact affine packet law and (2a).
`JetFactorialScale` proves that factorial diagonal substitution preserves every nonzero jet
polynomial.  `PrimeLogPolynomialJetEscape` then proves:

- `primeDyadic_actualDifferentialJet_escapes_mvPolynomial_in_gaugeBall`;
- `primeDyadic_actualDifferentialRelation_has_gaugeBall_escape`.

`GaloisForLFunctions.HTGeometry.RationalCoefficientClearing` proves exact simultaneous clearing of
finite `C(X)` coefficient families, simultaneous avoidance of the common pole divisor, and the
end-to-end theorem
`primeDyadic_actualRationalDifferentialRelation_has_gaugeBall_escape` for the honest specialized
rational relation.

The proof contains no `sorry`, `admit`, project axiom, opaque postulate, or unsafe declaration.

## Classification

The polynomial zero-set argument, finite-support positivity estimate, and surjective linear-control
argument belong to classical algebra, topology, and interpolation theory.  Their exact coupling to
the prime-log Herglotz source is a decisive formal bridge for the facet-sewn HT realization, but it
is not claimed as new scientific knowledge.  The candidate-new object remains the resulting
universal nonlinear constraint geometry, not these components.

## Gates

- [x] 0 → 1: exact positive nonlinear escape statement isolated
- [x] 1 → 2: complete unconditional paper proof
- [x] 2 → 3: generic theorem, prime-log specialization, and actual dyadic-weight theorem formalized
- [ ] 3 → 4: no standalone publication planned; classified as a bridge
