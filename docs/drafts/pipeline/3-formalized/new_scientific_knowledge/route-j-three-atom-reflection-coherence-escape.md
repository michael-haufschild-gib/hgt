# Route J: three-atom reflection-coherence escape

**Status:** dependency-closed paper construction and unconditional Lean 4 formalization.

## Question

The arbitrary two-active-atom theorem proves that reflected projective coherence forces the
critical line. Is that reflection principle class-complete for finite signed atomic sources?

No. Three atoms are the sharp escape.

## Full-turn source geometry

Fix `T>0`, `y!=0`, and

```text
z_+=2*pi/T+iy,       z_-=2*pi/T-iy,
r=exp(-Ty)>0,        r!=1.
```

At source times `T,2T,3T`, the spectral phases at `z_+` are `r,r^2,r^3`; at `z_-` they are
`r^(-1),r^(-2),r^(-3)`. Put

```text
g_j(r)=1-r^j,
d_j(r)=-j T r^j.                                      (1)
```

The value and imaginary-derivative rows are `g(r)` and `d(r)`.

## Common reflected value-kernel ray

Define

```text
B(r)=(-(1-r^3), 1-r^3, -r(1-r)).                      (2)
```

Direct factorization gives

```text
g(r).B(r)=0,                                           (3)
g(1/r).B(r)=0.                                         (4)
```

Indeed, `(3)` reduces to

```text
(1-r^3)[-(1-r)+(1-r^2)-r(1-r)]=0,
```

and `(4)` is the same identity after multiplication by `r^3`.

The derivative charge is

```text
M(T,r)=d(r).B(r)
      =T r(1-r)^2(1-r^2).                              (5)
```

Because `T>0`, `r>0`, and `r!=1`, this is nonzero. At the reflected height,

```text
d(1/r).B(r)=M(T,r)/r^3.                                (6)
```

Consequently `r^3 B(r)` lies in the reflected value kernel and has the same derivative charge
`M(T,r)` as `B(r)`.

This is the dimension jump absent for two atoms: two reflected value rows in three coordinates
have a common line, and `(2)` identifies it exactly.

## Exact unit-charge scalar jets

Normalize the singular directions by

```text
b=B(r)/M(T,r),       c=r^3 B(r)/M(T,r).                (7)
```

Then

```text
g(r).b=0,      d(r).b=1,
g(1/r).c=0,    d(1/r).c=1.                             (8)
```

For any real bounded derivative correction `s`, solve the first two columns for a bounded vector
`v=(v_1,v_2,0)` satisfying

```text
g(r).v=1,      d(r).v=s.                               (9)
```

The determinant is

```text
Delta(T,r)=T r(1-r)^2!=0,                              (10)
```

and the exact inverse is

```text
v_1=[-2Tr^2-(1-r^2)s]/Delta(T,r),
v_2=[(1-r)s+Tr]/Delta(T,r).                            (11)
```

Use `(11)` at `r` and at `1/r`. For every mesh width `delta>0`, define

```text
a_+(delta)=b/delta+v(r,s_+),
a_-(delta)=c/delta+v(1/r,s_-).                         (12)
```

Equations `(8)`--`(11)` give exact scalar jets

```text
G_+(z_+)=1,       H_+(z_+)=i(1/delta+s_+),
G_-(z_-)=1,       H_-(z_-)=i(1/delta+s_-).             (13)
```

Choose the source-connection corrections

```text
s_+=(1/z_+).im,       s_-=(1/z_-).im.
```

For

```text
F=iG/z,       D=(iH-F)/z,
```

the identity `D/F=H/G-1/z` and `(13)` give

```text
delta Im(D_+/F_+)=1,
delta Im(D_-/F_-)=1                                   (14)
```

exactly, not merely asymptotically.

Finally,

```text
delta a_+(delta) -> b,
delta a_-(delta) -> c=r^3 b.                           (15)
```

All three projective minors vanish, so the two nonzero limiting directions are identical in
projective space even though `y!=0`.

## Scientific consequence

The two-atom reflection theorem is arity-sharp:

```text
two active atoms + reflected projective coherence
  => centered line;

three active atoms
  => explicit off-center coherent unit-charge escape.  (16)
```

Therefore no Route-J proof may extend the two-atom argument by merely replacing a two-coordinate
ray with a finite-dimensional projective vector. At arity three, reflection leaves a genuine
common kernel carrying nonzero charge. A further no-go must use more source structure: a theta
density law, support-moment constraints, cross-mesh regularity stronger than convergence,
positivity/variation information, or a global relation tying bounded corrections across fibres.

## Novelty and theatre audit

Linear algebra of two rows in three coordinates is classical, and finite exponential
interpolation belongs to the Prony/Vandermonde literature. No novelty is claimed for those
ingredients. The corpus-new result is the exact source-specific weld:

1. explicit common reflected full-turn kernel `(2)`;
2. exact nonzero charge `(5)` and reflected `r^3` compensation `(6)`;
3. exact source-connection normalization `(11)`--`(14)`;
4. projectively equal normalized limits `(15)`.

The construction does not insert an Xi zero or a target multiplicity: `T,y,delta` are arbitrary,
and unit charge emerges from normalization of the source ray. It is nevertheless not an RH
construction. It is a universal local atomic source family, not yet a derivation from the
canonical theta/prime--Gamma source law, and it supplies charge one rather than an independently
proved match to every Xi multiplicity. Treating `(14)` as Route-J endpoint closure would be
theatre; treating it as the surviving minimal scalar mechanism is legitimate.

## Lean certificate

```text
formal/GaloisForLFunctions/RHTower/
  XiCTaylorSignedThreeAtomReflectionEscape.lean
```

Principal declarations:

```text
signedThreeAtomReflectionRay_value_zero
signedThreeAtomReflectionRay_reflectedValue_zero
signedThreeAtomReflectionRay_derivative
signedThreeAtomReflectionRay_reflectedDerivative
signedThreeAtomReflectionRayCharge_ne_zero
signedThreeAtomPlusJet
signedThreeAtomMinusJet
atomicSourceConnection_exactUnitScaledCharge
signedThreeAtomFullTurn_reflectionExactPair
tendsto_signedThreeAtomNormalizedWeights
signedThreeAtomLimitDirections_projective
```

Direct verification:

```text
lake env lean \
  GaloisForLFunctions/RHTower/XiCTaylorSignedThreeAtomReflectionEscape.lean
```

No `sorry`, `admit`, `axiom`, `opaque`, or `unsafe` declaration occurs.

## Route status

Route J remains open. The live `J-SF6` scalar core is no longer an unspecified “different support
geometry.” It has a minimal explicit form: at least three active atoms, with the common reflected
kernel `(2)` as the first survivor. Next obligation is to prove this ray cannot arise from a
source-defined theta/prime--Gamma density, or lift it into such a source without using divisor
data.
