# Suzuki wall-field light-cone kernel completion

- **ID:** `suzuki-wall-field-light-cone-kernel-completion`
- **Stage:** 3 — formalized and Lean-audited
- **Type:** SOURCE REALIZATION / FE--XI-REAL BIPOLARIZATION / KERNEL COMPLETION
- **Scientific status:** `[PAPER-PROVED] [LEAN-PROVED] [UNCONDITIONAL] [SOURCE-SPECIFIC]`
  `[CANDIDATE NEW SCIENTIFIC KNOWLEDGE]`
  `[NOT RH]`
- **Parents:**
  `suzuki-wall-field-antidiagonal-gram-lift.md`,
  `suzuki-xireal-fe-bipolarization-completion.md`,
  `suzuki-affine-sewn-weil-robin-far-tail-factorization.md`
- **RH used:** no
- **Computation used:** no

## Exact frontier

`[CORPUS]` Common wall scaling is positivity-neutral: after projective division it cancels, and
before division its Hermitian Bezoutian contribution is only congruence.  Therefore wall density
cannot pay marked debt merely by multiplying every projective coordinate.

`[CORPUS]` Abstract Xi-real/FE bipolarization identifies fixed positive and negative light
directions `(J+R)/2` and `(J-R)/2`, but does not prove actual Suzuki prime--Gamma source realizes
them.

`[CORPUS]` Wall-field Gram kernel contains positive diagonal and far phase on FE-reflected
anti-diagonal, but current theorem does not extract source channel whose Gram completes far current.

First unresolved implication is therefore source realization, not another positivity criterion:

> Does actual critical wall field itself realize abstract light channels so that denominator-matched
> far current is their exact Gram difference and negative light Gram is exact completion?

## Conjecture under hostile test

For one prime power `n=p^(e+1)` write

```text
omega(t)=b exp(i*t*log(n)/2),
K(t,u)=omega(t) conjugate(omega(u)).
```

Define FE/Xi-real light amplitudes

```text
ellPlus(t) =(omega(t)+i*omega(-t))/2,
ellMinus(t)=(omega(t)-i*omega(-t))/2,
LPlus(t,u) =ellPlus(t) conjugate(ellPlus(u)),
LMinus(t,u)=ellMinus(t) conjugate(ellMinus(u)).
```

Define reflected far-current kernel

```text
F(t,u)=i/2 * (K(-t,u)-K(t,-u)).
```

### `SUZUKI-WALL-LIGHT-CONE-KERNEL-COMPLETION` `[PAPER-PROVED]`

For all real heights,

```text
F=LPlus-LMinus,
(K(t,u)+K(-t,-u))/2=LPlus+LMinus,
F+LMinus=LPlus.                                           (1)
```

Every finite matrix sampled from `LPlus` or `LMinus` is positive semidefinite.  On diagonal,

```text
F(t,t)=Im(omega(t)^2)
      =Im(Lambda(n)/sqrt(n)*exp(i*t*log n)).              (2)
```

For `t!=0`, Xi-real delayed-hinge atom `J(t)=-i*omega(t)^2/t^2` therefore obeys exact local Ward
completion

```text
t^2*Re J(t)+|ellMinus(t)|^2=|ellPlus(t)|^2>=0.            (3)
```

The split is the literal corpus light-cone split.  Put

```text
v(t)=(Re omega(t),Im omega(t)) in R^2.
```

Then functional-equation reflection and Xi-real quarter-turn obey

```text
R v(t)=-v(-t),
LPlus(t,u) =QPlus_1(v(t),v(u)),
LMinus(t,u)=QMinus_1(v(t),v(u)),
F(t,u)     =QFE_1(v(t),v(u)),                            (4)
```

where `QPlus_1=(Q_1+QFE_1)/2` and `QMinus_1=(Q_1-QFE_1)/2` are already formalized
positive and negative light forms.  Thus `(1)` is not merely isomorphic to abstract
bipolarization: actual wall source evaluates it exactly.

For any finite family of prime-power sources and any finite height packet, summing `(1)` gives

```text
F_packet+LMinus_packet=LPlus_packet,                     (5)
```

and both light matrices remain Gram positive semidefinite.  This is finite cofinal assembly;
no infinite all-prime vector or convergence is asserted.

## Paper proof

Write `a_t=omega(t)` and `b_t=omega(-t)`.  Expanding the two rank-one kernels gives

```text
LPlus(t,u)-LMinus(t,u)
 =i/2*(b_t*conj(a_u)-a_t*conj(b_u))
 =F(t,u),

LPlus(t,u)+LMinus(t,u)
 =1/2*(a_t*conj(a_u)+b_t*conj(b_u)).
```

These are `(1)`.  Functional-equation reflection of wall field is `b_t=conj(a_t)`.  If
`a_t=x_t+i*y_t`, then

```text
ellPlus(t) =(1+i)*(x_t+y_t)/2,
ellMinus(t)=(1-i)*(x_t-y_t)/2.                          (6)
```

Consequently

```text
LPlus(t,u) =1/2*(x_t+y_t)*(x_u+y_u),
LMinus(t,u)=1/2*(x_t-y_t)*(x_u-y_u),
F(t,u)     =x_t*y_u+y_t*x_u.
```

These are exactly the three evaluations in `(4)`.  Also
`R(x_t,y_t)=(-x_t,y_t)=-(x_t,-y_t)=-v(-t)`.  Formula `(6)` shows every finite light matrix is a
rank-one Gram matrix.  A finite source sum is Gram in the finite source-coordinate space, proving
`(5)` and packet PSD without any limit.

At `u=t`, the last display gives `F(t,t)=2*x_t*y_t=Im(a_t^2)`, proving `(2)`.  Existing exact wall
square-root weld gives, for `t!=0`,

```text
t^2*J(t)=-i*a_t^2.
```

Taking real parts yields `t^2*Re J(t)=Im(a_t^2)=F(t,t)`.  The diagonal of `(1)` now gives `(3)`;
its right side is a norm square.

Finally the two light legs are forced, not fitted.  If kernels `P,N` satisfy

```text
P-N=F,   P+N=(K(t,u)+K(-t,-u))/2,
```

then adding and subtracting the equations uniquely gives `P=LPlus` and `N=LMinus`.

## Why this is structurally stronger

Common-factor route is killed because it changes no inertia.  `(1)` is non-common: it first
mixes FE-reflected source with independently fixed Xi-real quarter-turn, then forms two separate
Gram channels.  Thus common-factor congruence theorem does not apply.

Equations `(1)--(5)` close actual wall-source realization of abstract `(J-R)/2` completion.
Missing negative light leg is not a fitted external source; it is the unique reflected combination
of the same wall field compatible with Euclidean wall Gram and FE Krein current.

They do **not** prove actual Suzuki Robin/Gamma/holonomy carrier contributes that leg.  That is now
the precise next identification rather than an unspecified positivity request.

## Hostile falsifiers

1. **Sign/orientation:** one wrong `i` changes `(2)` to `-Im(omega^2)` and destroys `(3)`.
2. **Kernel, not diagonal:** prove two-variable identity `(1)` and arbitrary finite PSD, not only
   scalar squares at `t=u`.
3. **Projective neutrality:** light amplitudes must be distinct reflected combinations, not common
   factor applied to both projective coordinates.
4. **Phase-aligned Pick no-go:** theorem must not claim scalar far Pick atom positive in UHP.
   It concerns real-height FE-reflected Hermitian current after denominator matching.
5. **Center:** divided identity requires `t!=0`; numerator identity must remain unconditional.
6. **Prime divergence:** theorem is one prime power/finite height packet.  No standalone all-prime
   Hilbert vector is claimed.
7. **Global Ward:** even exact local completion does not prove Robin/Gamma/cofinal assembly or RH.
8. **Rediscovery:** abstract light-cone factorization is already corpus `[BRIDGE]`; novelty can only
   be source-specific wall realization and far-current identity.

All eight tests pass.  Test 7 remains the live RH-bearing boundary.

## External audit boundary

`[LITERATURE]` Suzuki constructs unconditional screw/Weil source and finite-interval operator
framework (arXiv:2301.00421 and arXiv:2606.09096).  Connes--Consani provide archimedean compressed
trace positivity architecture (arXiv:2006.13771).  Targeted search found no prime-power wall
field, reflected light amplitudes above, or identity `(1)--(3)`.  General rank-one Gram and
light-cone algebra remain classical `[BRIDGE]`; independent priority audit is still required.

## Gates

- [x] internal frontier audit
- [x] external primary-source audit
- [x] exact conjecture and falsifiers
- [x] hostile algebra proof
- [x] complete paper proof
- [x] unconditional Lean formalization
- [ ] identify actual Robin/Gamma/holonomy negative-light trace with `ellMinus`
- [ ] global reflected Robin/Gamma Ward assembly and cofinal renormalization
- [ ] RH
