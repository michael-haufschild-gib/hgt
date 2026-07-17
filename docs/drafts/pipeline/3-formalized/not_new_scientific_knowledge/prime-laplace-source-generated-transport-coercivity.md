# Prime-exponential source transport has a uniform critical half-unit defect

- **ID:** `prime-laplace-source-generated-transport-coercivity`
- **Stage:** 3-formalized/not_new_scientific_knowledge
- **Type:** THEOREM / SOURCE TRANSPORT / ALL-SCALE COERCIVITY PRODUCER
- **Scientific status:** `[PROVED] [LEAN-VERIFIED] [BRIDGE] [NOT AN RH PROOF]`
- **Parent:** `prime-laplace-even-factorial-fock-incidence.md`
- **Lean:**
  `formal/GaloisForLFunctions/RHTower/PrimeLaplaceEvenFactorialSourceTransport.lean`

## Theorem

For a prime `p`, let

```text
J_p(j)=(-log p)^j
```

be the complete raw derivative jet of `x |-> p^(-x)`.  Infinite Taylor translation by an arbitrary
real amount `a` obeys the exact source eigenlaw

```text
sum_(h>=0) a^h J_p(i+h)/h! = p^(-a) J_p(i).             (1)
```

This is the exponential series identity, but its role is structural: the actual source columns
are invariant even though the full even-factorial ambient jet completion need not carry bounded
translation.

For an arbitrary finite channel set `P`, prime labels `p_q`, and complex source coefficients
`c_q`, put

```text
E(c)=sum_q |c_q|^2,
E(Tc)=sum_q |c_q|^2 p_q^(-2).
```

At the critical half-unit seam `a=1/2`, the translated energy is

```text
E(T_(1/2)c)=sum_q |c_q|^2 p_q^(-1).
```

Since every `p_q>=2`, Lean proves uniformly in the aperture and the coefficient packet

```text
E(T_(1/2)c)<=1/2 E(c),
E(c)-E(T_(1/2)c)>=1/2 E(c).                              (2)
```

At unit translation the sharper defect floor is `3/4`.  More generally, Lean proves that every
real displacement `a>=1/2` has the common floor

```text
E(c)-E(T_a c)>=1/2 E(c).                                 (3)
```

Thus the entire post-critical translation ray is source diagonal and uniformly coercive.

Lean also proves the reciprocal half-translation law

```text
T_(-1/2)J_p=p^(1/2)J_p,
E(T_(-1/2)c)>=2E(c),
E(c)-E(T_(-1/2)c)<=-E(c).                               (4)
```

This is the direction required by exact de-Poissonization of the absolute-Euler boundary source.
It is uniformly expansive, not coercive.

## Relation to the even-factorial incidence

The parent theorem proves that the complete Gamma-damped prime-by-jet matrix is Hilbert--Schmidt
for every source point `x>1/2`.  Equation `(1)` shows that its actual prime columns carry an exact
transport action; `(2)` supplies a positive all-scale defect on the source coefficient space.
The combination is the first completed incidence/transport pair on this route that does not rely
on the unbounded ambient Taylor operator.

## RH boundary

The exact Euler-safe stationarity law shows that the RH-complete Weil form is obtained by undoing
the safe Poisson factor.  At a prime frequency `log p`, this inverse transport multiplies by
`p^a`; it is the negative-displacement direction in `(1)`, not the contractive positive direction
in `(2)`--`(3)`.  Equation `(4)` therefore kills the proposed direct transfer:

```text
forward prime damping
  -> positive coefficient-energy defect,

inverse de-Poissonization required by RH
  -> uniformly negative coefficient-energy defect.      (5)
```

Moreover the energy here is the orthogonal coefficient sum.  The RH carrier is a coupled
prime--Gamma--polar--critical-Mellin Gram; its non-diagonal cross terms are absent from `(2)`.
Consequently there is no remaining theorem of the form “the completed value identity preserves
the coercivity above.”  Such a theorem would contradict `(4)` unless the coupled completion
supplied a new positive defect large enough to reverse the inverse expansion, which is precisely
the unresolved RH-bearing orientation inequality.

The positive role of this module is narrower and exact: it constructs a valid all-prime forward
transport and proves that any RH proof must use an unbounded, channel-resolved inverse incidence,
not coefficientwise coercivity.  The live chain is now

```text
all-prime even-factorial incidence
  -> source-generated forward contraction
  -> exact inverse-transport expansion obstruction
  -> [OPEN] unbounded channel-resolved Gamma/polar/Mellin inverse incidence
  -> [OPEN] positivity of its completed defect
  -> canonical Xi/Weil positivity
  -> RH.                                                  (6)
```

## Gates

- [x] prove the exact infinite-jet source translation eigenlaw for every real displacement
- [x] specialize the eigenlaw to the critical half-unit seam
- [x] prove source transport is real and strictly contractive
- [x] prove a cutoff-independent critical half-unit defect lower bound
- [x] extend the lower bound uniformly to every displacement `a>=1/2`
- [x] prove inverse half-translation has multiplier `p^(1/2)`
- [x] prove inverse half-translation expands energy by at least two
- [x] prove its coefficient-energy defect is at most minus the source energy
- [x] formalize unconditionally in Lean
- [x] exclude direct transfer of forward coefficient coercivity through de-Poissonization
- [ ] construct the unbounded channel-resolved completed inverse incidence
- [ ] prove positivity of its coupled Gamma/polar/Mellin defect
- [ ] identify that completed defect Gram with the normalized Xi/Weil form
- [ ] RH
