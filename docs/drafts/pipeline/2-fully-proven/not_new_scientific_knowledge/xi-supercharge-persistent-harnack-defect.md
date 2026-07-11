# Xi supercharge curve and persistent Harnack defect

- **ID:** `xi-supercharge-persistent-harnack-defect`
- **Stage:** 2-fully-proven (paper)
- **Type:** THEOREM / BRIDGE / NOT NEW SCIENTIFIC KNOWLEDGE
- **Source:** independent superspace/real-algebraic-geometry reframe, disjoint from every route in
  `docs/reports/rhtower_status_1107.md`
- **Novelty:** parent-theory and divisor-repackaging gates failed

## Claim under construction

Put `t=-i(s-1/2)`, so physical time is the real `t`-axis and

```text
X(t) = xi(1/2+i t)
```

is real and even on real time.  Regard a curved supersymmetry relation `Q^2=X(t)` as defining the
double supercharge spectral curve `y^2=X(t)`.  A double cover sees only odd zero multiplicity, so the
faithful object must use the reduced branch divisor.  At finite level, for a real polynomial `F`
with `F(0) != 0`, let

```text
R_F = rad(F),
C_F : y^2 = t R_F(t).
```

The clock-origin factor `t` makes the branch polynomial odd-degree and removes the even-degree
ambiguity in which a real hyperelliptic curve can be maximal despite having no real branch points.

For the canonical finite zero-divisor exhaustion, the persistent Harnack defect of `C_X` is a
monotone faithful integer process.  Its jump at a cutoff is exactly the number of newly admitted
nonreal conjugate zero pairs.  Consequently RH is equivalent to vanishing of the entire persistent
defect, not to a normalized or measured limit.

## Finite theorem target

Let `R in R[t]` be squarefree of even degree `2n`, with `R(0) != 0`.  Suppose `R` has exactly `2r`
real roots.  Let `C` be the smooth projective normalization of

```text
y^2 = t R(t).
```

Then:

```text
genus(C)                         = n,
number of components of C(R)    = r+1,
HarnackDefect(C)                 = (n+1)-(r+1)
                                  = n-r
                                  = (# nonreal roots of R)/2.
```

In particular `C` is an M-curve if and only if every root of `R` is real.

### Paper proof `[PROVED HERE]`

The branch polynomial `tR(t)` is squarefree of degree `2n+1`; its finite branch points are `0` and
the `2n` roots of `R`, and infinity is the final branch point.  Riemann--Hurwitz therefore gives
genus `n`.  On the real projective line, the real branch set contains `2r+2` points after including
`0` and infinity.  The sign of the real branch polynomial alternates across consecutive simple real
branch points.  Exactly `r+1` complementary arcs have nonnegative sign.  The two sheets over each
such arc meet at its two branch endpoints, producing one real oval, while arcs of negative sign
have no real lift.  Hence `C(R)` has `r+1` components.  Harnack's bound is `n+1`, giving the formula.

In the projective chart at infinity, odd degree gives one real ramification point.  Thus the real
branch points form `2r+2` points on `P^1(R)`: the `2r+1` finite real roots of `tR(t)` and infinity.
They cut the real projective line into `2r+2` arcs.  On alternating arcs the real double cover is
empty; over each of the other `r+1` arcs the two sheets meet at both branch endpoints and form one
circle.  Nonreal conjugate branch pairs do not meet `P^1(R)`, hence add genus through
Riemann--Hurwitz without adding real ovals.  This proves the component formula and the theorem.

## Persistent Xi packet theorem `[PROVED HERE]`

Let `T` avoid zero ordinates and let `Z_T` be the finite reduced zero set of `X(t)` in the symmetric
height window `|Re(t)|<T`.  FE and Schwarz symmetry make

```text
R_T(t) = product_{rho in Z_T} (t-rho)
```

a real even squarefree polynomial, independent of the ordering of the zero packet.  Write
`deg R_T=2n_T`, and let `2r_T` of its roots be real.  Applying the finite theorem to

```text
C_T : y^2=t R_T(t)
```

gives

```text
delta_T = n_T-r_T = (# distinct nonreal zeros in Z_T)/2.
```

As `T` crosses an on-line pair, both `n_T` and `r_T` increase by one and `delta_T` is unchanged.  As
it crosses an off-line FE--Schwarz quartet, `n_T` increases by two while `r_T` is unchanged, so
`delta_T` increases by two.  Hence `delta_T` is monotone, independent of the order in which complete
symmetry orbits are admitted, and

```text
RH iff for every admissible T, delta_T=0.
```

Multiplicity causes no ambiguity because the packet is reduced; equivalently one may replace a
finite factor by `F/gcd(F,F')`.  The theorem is faithful to support, not multiplicity.

## Why this is not the old modular trace

The defect is unnormalized and cutoff-faithful.  One off-line conjugate pair changes it by one even
when its density among all zeros tends to zero.  Thus it avoids the measured-index blindness that
killed the Tomita--Takesaki/KMS route.

## Attacks

1. **Local supersymmetry:** local matrix-factorization germs remain identical nodes.  The proposed
   information is global real topology of the supercharge curve, not local vacuum data.
2. **Multiplicity:** a raw double cover misses even-order zeros.  Passing to the reduced divisor is
   mandatory; any construction that cannot produce it source-canonically fails.
3. **Even-degree false positive:** `y^2=R(t)` can be an M-curve with no real roots.  The canonical
   clock-origin branch `t=0` is load-bearing.
4. **Infinite cardinality:** the global Xi curve has infinite genus and infinitely many real ovals,
   so bare cardinalities are useless.  Only a compatible exhaustion/persistence class can be
   faithful.
5. **Parent-theory gate:** the finite component formula is classical real hyperelliptic topology.
   Scientific novelty, if any, must lie in a source-canonical, exhaustion-independent persistent
   defect for the transcendental Xi supercurve, not in the finite formula.
6. **Divisor-repackaging gate:** if the persistent defect is merely defined by counting zeros first,
   it is a bridge and must be downgraded.  The construction must arise from the analytic branched
   cover or an equivalent source-defined topology.

## Verdict

`[BRIDGE]` The theorem gives a clean quantum-supercurve interpretation of the faithful off-line
index, and unlike a modular trace it sees density-zero defects.  It nevertheless does not create a
source theorem.  Its finite input is the reduced zero packet, and the equality
`delta_T=(# nonreal roots)/2` proves that the topology is exactly a divisor recorder.  Arbitrary
real-even squarefree polynomials realize every allowed value `0<=delta_T<=n_T`; FE and Schwarz
symmetry therefore impose no maximality.  Erasing Xi vocabulary leaves classical real
hyperelliptic topology and Harnack's bound.  The parent-theory, significance, and
divisor-repackaging gates fail.

## Gates

- [x] 0 -> 1: exact finite object, multiplicity correction, and even-degree counterexample isolated.
- [x] 1 -> 2: finite topology theorem and persistent packet formula proved.
- [ ] 2 -> 3: closed; formalizing a classical divisor recorder would not advance the research goal.
- [ ] 3 -> 4: ineligible; dual novelty/significance gate failed.

## Log

- 2026-07-11 — created after the modular/KMS, local Landau--Ginzburg, characteristic-function, and
  pure-point clock attacks.  The clock-origin branch and reduced-divisor correction were identified
  as load-bearing; persistent Harnack defect isolated as the only potentially faithful new object.
- 2026-07-11 — finite and persistent packet formulas proved.  The formula itself identifies the
  construction as a classical faithful divisor recorder, so the route was downgraded before Lean
  formalization.
