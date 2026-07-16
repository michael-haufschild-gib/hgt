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

## Relation to the even-factorial incidence

The parent theorem proves that the complete Gamma-damped prime-by-jet matrix is Hilbert--Schmidt
for every source point `x>1/2`.  Equation `(1)` shows that its actual prime columns carry an exact
transport action; `(2)` supplies a positive all-scale defect on the source coefficient space.
The combination is the first completed incidence/transport pair on this route that does not rely
on the unbounded ambient Taylor operator.

## RH boundary

This is an unconditional source coercivity producer, but it is not yet the **critical** coercivity
producer required to close RH.  The missing theorem is an exact completed value comparison showing
that the source defect Gram, after the forced Gamma and polar boundary coupling, is the canonical
normalized Xi/Weil Hankel form.  Transporting only the prime diagonal would discard the signed
quadrature and Gamma connection and would therefore be invalid.

The live chain is

```text
all-prime even-factorial incidence
  -> source-generated real contractive transport
  -> uniform source defect coercivity
  -> [OPEN] completed prime--Gamma defect/value identity
  -> canonical Xi/Weil positivity
  -> RH.
```

## Gates

- [x] prove the exact infinite-jet source translation eigenlaw for every real displacement
- [x] specialize the eigenlaw to the critical half-unit seam
- [x] prove source transport is real and strictly contractive
- [x] prove a cutoff-independent critical half-unit defect lower bound
- [x] extend the lower bound uniformly to every displacement `a>=1/2`
- [x] formalize unconditionally in Lean
- [ ] couple the prime defect with the forced Gamma and polar channels
- [ ] identify the completed defect Gram with the normalized Xi/Weil form
- [ ] RH
