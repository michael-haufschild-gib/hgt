# Tail Hadamard positive-unit law

- **ID:** `tail-hadamard-positive-unit-law`
- **Stage:** 3-formalized / not new in isolation
- **Type:** GENERAL HT CONSTRAINT LAW / OPERATOR-TAIL ALGEBRA
- **Scientific status:** `[NOVELTY UNVERIFIED]`; reduced-product algebra is `[SEARCH]`

## Statement

Let `I` be a coordinate set and let

```text
H_I = R^I / R^(I),
```

with finite-support functions quotiented out.  In addition to its tail vector space and eventual
order, `H_I` carries coefficientwise multiplication

```text
[a] hadamard [b] = [i |-> a(i)b(i)].                         (1)
```

This makes `H_I` a commutative reduced-product algebra whose unit is the all-positive tail `[1]`.
Every Boolean orientation `epsilon:I->{+1,-1}` is an involution,

```text
[epsilon] hadamard [epsilon] = [1].                         (2)
```

Among Boolean orientation tails, the positive cone contains exactly one involution:

```text
[epsilon] >= 0  iff  [epsilon]=[1].                         (3)
```

On the bounded part of the reduced product, `[1]` is an order unit: if `|a(i)|<=M`, then

```text
-M[1] <= [a] <= M[1].                                      (4)
```

## HT law

The operator-tail differential matroid remembers only the linear geometry of coefficient tails.
The Hadamard reduced product remembers a second operation that is invisible to ordinary
functional multiplication and differentiation.  Its unit canonically selects the all-positive
prime tail.

For prime Dirichlet carriers

```text
F_a(s)=sum_p a(p)p^(-s),
```

the operation `(1)` is the coefficientwise Dirichlet/Hadamard product

```text
F_a star F_b = F_(a hadamard b),
```

not the ordinary product `F_a F_b`, whose coefficients are governed by Dirichlet convolution.
Thus a carrier can be free under its ordinary differential-field operations while retaining a
canonical source under the transverse coefficient algebra.

## Positive consequence

The all-positive prime carrier is not an arbitrary polarization of a homogeneous differential
building.  It is the canonical positive unit of the tail Hadamard algebra.  Exact Bochner
positivity then selects the all-positive representative rather than only its finite-support class.

This suggests that an arithmetic HT theory should retain three compatible structures:

1. ordinary differential-field operations on analytic functions;
2. Dirichlet convolution/Euler plethysm, which builds multiplicative arithmetic functions;
3. coefficientwise Hadamard multiplication, whose positive unit marks the prime source.

Forgetting item 3 produces the artificial `GL(V)` symmetry of the unpolarized differential
building.  Restoring it reduces the symmetry to automorphisms of the reduced-product algebra and
makes the zeta tail canonical before any closed formula or Baire selection is invoked.

## RH application boundary

For zeta, the Hadamard unit identifies the all-positive prime-zeta tail.  Euler plethysm then
recovers the zeta Euler product on `Re(s)>1`.  This does not locate continued zeros.  An RH route
using this law must still connect the Hadamard unit to the functional equation and to a
reflection-positive divisor criterion.

The concrete RH research question is:

> Which analytic continuations or reflection-positive functionals are simultaneously compatible
> with ordinary multiplication, Dirichlet convolution, and the Hadamard positive unit?

Compatibility across these three products is the possible new constraint; the individual
products are classical.

## Attacks

1. **Reduced-product collision.**  The algebra `R^I/R^(I)`, the Boolean algebra `P(I)/Fin`, and
   coefficientwise products are classical.  Equations `(1)`--`(4)` alone are not new science.
2. **Hadamard-product collision.**  Hadamard products of Dirichlet series and arithmetic functions
   are established topics.  Novelty can only lie in an exact compatibility law with differential
   hypertranscendence and Euler plethysm.
3. **Unit triviality attack.**  Every unital algebra has a unit.  The content is not the existence
   of `[1]`, but that the tail classifier of a differentially free prime family admits this
   transverse algebra and that positivity makes its Boolean unit unique.
4. **Automorphism attack.**  Algebra automorphisms preserve the unit automatically but may still
   move many other orientations.  A useful rigidity theorem must classify which automorphisms also
   preserve the eventual cone and prime-coordinate/Euler structure.
5. **RH upcast attack.**  The positive unit selects a source but does not imply a statement about
   its continued divisor.

## Formal surface

`formal/GaloisForLFunctions/HTGeometry/TailHadamardReducedProduct.lean` proves:

- `finiteSupportIdeal` and the commutative quotient algebra;
- `tailHadamardClass_eq_iff`;
- `tailHadamardPositive_class_iff`;
- `allPositiveTail_hadamard_unit`;
- `primeOrientationHadamardTail_sq`;
- `primeOrientationHadamardTail_positive_iff_eq_one`;
- `bounded_tail_between_unit_multiples`.

## Gates

- [x] exact algebra, cone, involution, and order-unit statements isolated
- [x] complete paper proof
- [x] source-level formal proof without project hypotheses
- [x] narrow module build
- [x] axiom audit: only `propext`, `Classical.choice`, and `Quot.sound`
- [ ] classify cone-preserving algebra automorphisms of the tail reduced product
- [ ] derive or kill a non-routine compatibility law with the operator-tail differential matroid
- [ ] derive or kill a non-routine compatibility law with Euler plethysm
- [ ] complete primary-literature and parent-theory audit
