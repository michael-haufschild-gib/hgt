# Prime--Hodge Poisson two-channel integral split

- **ID:** `ULF-PHPTCIS-001`
- **Stage:** 2-fully-proven
- **Type:** unconditional pre-divisor operator conservation and direct-subunit no-go
- **RH used:** no
- **Divisor used:** no
- **Parents:** `ULF-PHIN-001`, `ULF-PHPCF-001`, theta visibility/contrast Pythagorean law,
  common-recovery functional-equation information neutrality

## 1. What was wrong

A tempting direct-subunit argument declares the prime visibility remaining after an off-wall tilt
to be the integer carried by the integral--nuclear source defect. That is false. Visibility is only
one output of a lossless two-channel split. The complementary contrast channel carries exactly the
missing charge, and common recovery is information-neutral rather than a mechanism for deleting
that channel.

The integral object is the whole instrument, not either marginal.

## 2. Construction

Let

```text
H = ell2(Nat x Primes)
T = primeHodgeHistoryIntegralNuclearDefectT.
```

Thus `T` is positive and trace-class, `Tr(T)=||T||_1=1`, every basis diagonal is strictly
positive, and every same-history cross-prime matrix entry is nonzero. For horizontal grade
`a in R` and prime `p`, put

```text
v_a(p) = sech(a log(p)/2)
       = 2/(p^(a/2)+p^(-a/2)),
c_a(p) = tanh(a log(p)/2).
```

Define commuting self-adjoint diagonal contractions on `H` by

```text
V_a e_(n,p) = v_a(p)e_(n,p),
C_a e_(n,p) = c_a(p)e_(n,p).                         (PTC.1)
```

The theta likelihood identity gives

```text
V_a^2 + C_a^2 = I.                                   (PTC.2)
```

The two completed source marginals are

```text
T_vis(a) = V_a T V_a,
T_con(a) = C_a T C_a.                                (PTC.3)
```

Both remain pre-divisor, prime-marked, positive, and trace-class. For `a != 0`, both retain every
same-history cross-prime entry because all finite-prime multipliers in `(PTC.1)` are nonzero.

## 3. Theorem: exact integral-charge conservation

For every `a in R`,

```text
Tr(T_vis(a)) + Tr(T_con(a)) = 1.                      (PTC.4)
```

Equivalently, the two-Kraus instrument

```text
I_a(X) = V_a X V_a direct_sum C_a X C_a             (PTC.5)
```

is completely positive and trace-preserving on trace-class inputs. It preserves literal prime
labels and the full history coordinate.

**Proof.** Bounded congruence preserves positivity and trace class. Cyclicity of trace and
`(PTC.2)` give

```text
Tr(V_a T V_a)+Tr(C_a T C_a)
 = Tr(T V_a^2)+Tr(T C_a^2)
 = Tr(T(V_a^2+C_a^2))
 = Tr(T)=1.
```

The same calculation for an arbitrary trace-class `X` proves trace preservation in `(PTC.5)`;
Kraus form proves complete positivity. QED.

## 4. Theorem: off-wall fractionalization

Write

```text
q_vis(a)=Tr(T_vis(a)),
q_con(a)=Tr(T_con(a)).
```

Then

```text
q_vis(0)=1,                 q_con(0)=0,               (PTC.6)
0<q_vis(a)<1,               0<q_con(a)<1  if a!=0,    (PTC.7)
q_vis(-a)=q_vis(a),         q_con(-a)=q_con(a).        (PTC.8)
```

In particular, neither off-wall marginal is an integer although their sum is the fixed integer
one.

**Proof.** Let `d_(n,p)=<e_(n,p),T e_(n,p)>`. The prime--Hodge certificate gives
`d_(n,p)>0` and `sum_(n,p)d_(n,p)=1`. Diagonal trace expansion gives

```text
q_vis(a)=sum_(n,p) d_(n,p) v_a(p)^2,
q_con(a)=sum_(n,p) d_(n,p) c_a(p)^2.                 (PTC.9)
```

At `a=0`, `v_0=1` and `c_0=0`. If `a!=0`, then `log(p)>0` for every prime, hence
`0<v_a(p)^2<1` and `0<c_a(p)^2<1`. Strict positivity of every `d_(n,p)` makes both sums positive;
`(PTC.4)` makes both strictly below one. Squaring removes the reflection sign, proving `(PTC.8)`.
QED.

The signed contrast operator itself is reflection-odd:

```text
C_(-a)=-C_a,
```

whereas the two positive charges are reflection-even. Thus orientation survives in the open
amplitude even though it disappears from either marginal trace.

## 5. Joint reconstruction

The split retains more than total charge. If `Q_n` is the history-tail projection, then

```text
Tr(Q_n T_vis(a)) + Tr(Q_n T_con(a)) = Tr(Q_n T)=m_n. (PTC.10)
```

Adjacent tail differences therefore reconstruct every Kummer first-exit weight:

```text
Tr((Q_n-Q_(n+1))T_vis(a))
 + Tr((Q_n-Q_(n+1))T_con(a)) = w_n.                  (PTC.11)
```

For `a!=0`, both matrices remain nonzero between every two primes on each history grade. Hence
theta polarization neither diagonalizes the source nor squares away its cross-prime formation.
It partitions each local history flux into two complementary prime-mixed pieces.

## 6. Interpretation

The prime--Hodge object carries an integer only as a **closed-plus-open conservation law**:

```text
visible observer charge + contrast history charge = integral formation charge.
```

At the neutral wall the full unit is visible. Off wall the same unit is forced to fractionalize;
no charge is created or lost. Prime visibility tends to zero along large primes while contrast
tends in modulus to one. On the prime fibre `V_a` is compact for `a!=0`, but its lift to
`ell2(Nat x Primes)` has infinite history multiplicity and need not be compact. The conclusion is
therefore a trace-class source law, not a false global compactness statement.

This is the operator-level fusion of four previously separate organs:

1. the integral--nuclear prime--Hodge defect;
2. theta likelihood visibility/contrast polarization;
3. unsquared all-cross-prime formation;
4. information-neutral functional-equation recovery.

## 7. Consequence for the direct-subunit programme

The naive integer trap is disproved:

```text
"q_vis(a) is integral"  is not a source law.
```

It would amount to discarding `q_con(a)`, precisely what an information-neutral common recovery
cannot do. The full charge is the constant integer one for every grade, so integrality of the
whole instrument is nonselective.

The surviving RH edge is consequently not a finite-norm path from `T` to a rank-one horizon.
Actual theta completion is singular and only strongly closes the observer boundary. A viable
selection theorem must instead construct, before divisor specialization, a prime-marked pairing
of the **open contrast history** with the singular-completion ideal. It must satisfy both:

```text
(i)  a nonzero off-wall pairing is an integer;
(ii) its nuclear representative is bounded by the literal Euler budget B<1.
```

Then the direct sub-unit anchor would kill that pairing. Pairing only the closed visibility
marginal is forbidden by `(PTC.4)`; pairing the whole two-channel charge is nonselective. The new
candidate must be relative: it must measure failure of the contrast charge to close under the
prime-marked theta extension.

## 8. Hostile audit

- The abstract Kraus identity is standard. New content is its exact specialization to the
  corpus's pre-divisor, prime-mixed, integral--nuclear `T`, including strict fractionalization,
  history-tail reconstruction, and survival of every cross-prime entry.
- This is not RH. No theorem here supplies the required prime-marked singular-ideal pairing.
- It does not assume a zero, quartet, divisor ordinate, or relation horizon.
- It blocks rather than renames the visibility-integer conjecture: full information recovery
  forces the missing contrast channel to remain present.
- It does not identify the separable history--prime `T` with the distinct physical Pluecker
  singular-boundary source operator. Any such identification requires a new intertwining theorem.

## 9. Formal status

Paper proof is unconditional and dependency-closed. Lean parents already certify `T`, its
strictly positive diagonal, unit trace, history-tail laws, all-cross-prime kernel, the scalar and
operator identity `visibility^2+contrast^2=1`, and information-neutral functional-equation lifts.
No Lean module for the congruence/trace-class fusion `(PTC.3)--(PTC.11)` was written or built during
this read-only research audit.
