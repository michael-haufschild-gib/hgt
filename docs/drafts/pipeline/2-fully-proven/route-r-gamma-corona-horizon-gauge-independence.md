# Route R Gamma-corona horizon gauge independence

- **ID:** `route-r-gamma-corona-horizon-gauge-independence`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Status:** `[PAPER-PROVED] [CORPUS-NEW CLASSIFICATION] [NOT RH]`
- **Parent:** `../3-formalized/route-r-degree-six-gamma-corona-local-global-fracture.md`

## Exact statement

Let `H` be the all-cross-prime packet Hilbert space, `A` its finite arithmetic core,
`Q=H/A`, and `pi : H -> Q` the algebraic quotient.  For every `rho : XiDivisorSupport` and
every `z : H` with `pi(z) != 0`, put

```text
lift_rho(z) = c_rho * pi(z),
```

where `c_rho` is the nonzero multiplicity-leading Xi Cartier coefficient.  Then:

1. `lift_rho(z) != 0`;
2. fixed physical Gamma action on `lift_rho(z)` is
   `Gamma_23(rho) * pi(z)`;
3. quotient of the literal `(2,3)` coordinate-local action on `z` is zero;
4. physical global action equals quotient-local action iff `Gamma_23(rho)=0`;
5. the equality in item 4 is independent of the chosen nonzero corona horizon.

There is a source-labelled, orientation-symmetric full-support arithmetic horizon

```text
h_ar(p,q) = 1/(p*q),  p != q,
```

in `ell^2` of ordered distinct-prime pairs.  Its corona class is nonzero.  Therefore the current
encoded-horizon source-globalization statement is equivalent to the arithmetic-horizon statement.

## Conjecture / falsification loop

### C23 — orientation swap kills the odd port

`[FALSIFIED]`.  Lean proves distinct ordered pairs, including `(p,q)` and `(q,p)`, are separated by
normalized incidence coordinates and that the ordered witness family is linearly independent.
Composite-dilation commutativity does not identify the two Milnor-incidence atoms.  Orientation
reversal must be represented as an action, not imposed as equality.

### C24 — full permutation naturality selects a canonical nonzero horizon

`[FALSIFIED]`.  A vector in the permutation representation `ell^2(I)` fixed by every transposition
has constant coordinates.  On infinite `I`, a nonzero constant field is not square summable.
Thus the invariant subspace is zero.  The existing coefficient `2^(-Encodable.encode i)` is a
valid full-support vector but depends on a chosen enumeration.

### C25 — arithmetic selects a unique horizon

`[FALSIFIED]`.  Many positive full-support arithmetic fields are square summable, for example
`(pq)^(-s)` for every `s>1/2`.  Inspected source axioms do not select one exponent.

### C26 — horizon is gauge, not data

`[PAPER-PROVED]`.  The obstruction is independent of every nonzero corona horizon.  This absorbs
the nonuniqueness from C25 and permits a convenient intrinsic representative without claiming it
is uniquely canonical.

## Complete proof

Write `alpha_rho` for the source cooriented reflection-odd Gamma coefficient and `c_rho` for the
Cartier coefficient.  Existing exact source transport gives

```text
Gamma_23(rho) = alpha_rho * c_rho.                         (1)
```

Physical action on `Q` is `alpha_rho * id`.  Hence for any `z : H`, linearity and `(1)` give

```text
T_rho(c_rho * pi(z))
  = alpha_rho * c_rho * pi(z)
  = Gamma_23(rho) * pi(z).                                (2)
```

If `pi(z) != 0`, then `c_rho*pi(z) != 0` because `c_rho != 0`.  Literal local action is
`alpha_rho` times projection to the singleton `(2,3)` coordinate.  Its value has finite support,
so it lies in `A`; therefore

```text
pi(local_rho(z))=0.                                       (3)
```

Combining `(2)` and `(3)`, global/local equality is

```text
Gamma_23(rho) * pi(z)=0.
```

Since `pi(z) != 0`, scalar faithfulness gives equivalence with `Gamma_23(rho)=0`.  The right side
does not mention `z`, proving horizon-gauge independence and equivalence for every pair of
nonzero horizon classes.

For the arithmetic representative, define `w(p,q)=1/(pq)`.  Every coordinate is nonzero because
primes are positive.  Moreover

```text
sum_(p!=q) |w(p,q)|^2
  <= sum_(p,q) 1/(p^2*q^2)
   = (sum_p 1/p^2)^2
   < infinity.                                             (4)
```

Thus `w` defines an `ell^2` packet.  It has infinite support, while every element of `A` is the
Hilbert realization of a finitely supported coefficient field.  Hence `w` is not in `A` and
`pi(w) != 0`.  Finally `w(q,p)=w(p,q)`, so orientation swap fixes it.  Applying horizon-gauge
independence to `w` and to the existing encoded horizon proves equivalence of their globalization
statements.

All steps are unconditional.  No centered-rate vanishing, critical-line, fixed-norm, dagger, or
RH premise occurs.

## Hostile audit

- The theorem does not annihilate the port and is not an RH proof.
- It is not another zero-set wrapper: it universally classifies all possible nonzero horizon
  choices and proves the exact source-globalization interface is gauge-independent.
- It survives the continuous/closed-relation no-gos because it makes no continuity claim about
  the algebraic quotient.
- It survives absence of a canonical invariant vector by replacing uniqueness with pointed-line
  gauge independence.
- It proves the risky consequence needed operationally: a future source proof on the intrinsic
  arithmetic horizon closes the existing encoded-horizon theorem automatically.

## External boundary

- R. Meyer, *Analytic cyclic cohomology*, arXiv:math/9906205, constructs functorial analytic cyclic
  theory on complete bornological algebras; it does not canonically repair an algebraic quotient by
  a dense nonclosed core.
- A. Vershik and N. Nessonov, *Stable representations of the infinite symmetric group*,
  Izvestiya: Mathematics 79 (2015), treats richer stable representations; it does not provide a
  fixed vector in the elementary infinite permutation representation used here.
- P. Motakis and D. Puglisi, arXiv:2403.04137, and R. Hagger, M. Lindner, M. Seidel,
  arXiv:1504.00540, concern Hausdorff Calkin quotients by closed operator ideals, unlike the present
  dense-core algebraic corona.

## Frontier effect

Arbitrary `Encodable` horizon choice is removed from the RH-bearing interface.  Future producer
work may use any intrinsic nonzero arithmetic horizon; no normalization, uniqueness, or reindexing
theorem remains in the proof burden.  The sole unresolved content stays the singular
Cartier/Stokes law annihilating the horizon-independent scalar port.

## Gates

- [x] internal source and failed-route audit
- [x] external parent-theory audit
- [x] conjecture-failure-replacement loop C23--C26
- [x] dependency-closed paper proof
- [ ] exact unconditional Lean proof
- [ ] source-globalization producer
- [ ] RH

## Log

- 2026-08-07 — C23--C25 falsified; C26 proved on paper after changing primitive from canonical
  horizon vector to pointed nonzero corona line.
