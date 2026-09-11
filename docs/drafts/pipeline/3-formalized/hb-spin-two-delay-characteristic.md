# HB: original spin-two delay characteristic

Stage: 3-formalized for the original direct coincident-radius finite source-delay transfer. Full physical-current cancellation and RH remain unproved. Frontier map read only.

Proof chain: literal theta-cusp source → Xi occurrence → retained spin-two source → physical causal radial/left-QNM action → fixed Hawking-clock extinction → RH.

## Direct target

The [source-delay transpose](../1-in-progress/hb-spin-two-kernel-transfer.md) contains apparent singularities at the direct coincident-radius characteristic. The [proved full native primitive](hb-native-spin-two-primitive.md) supplies its two zero jets. The new proof factors those jets using the original source integrals and evaluates the resulting characteristic current and bulk contact. The original clock, principal angular source and physical faces remain attached.

## Conjecture and proof mechanism

Write `S(Z)` for the actual full spin-two native trace, and `F` for its proved double primitive, so `F''=-S`. The exact rescaled integrals are

```
U(Z)=-integral_0^1 (1-t) S(1+t(Z-1)) dt,
V(Z)=-integral_0^1 S(1+t(Z-1)) dt,
F(Z)=(Z-1)^2 U(Z), F'(Z)=(Z-1)V(Z).
```

Original source continuity makes `U,V` continuous through `Z=1`, with `U(1)=-S(1)/2`, `V(1)=-S(1)`.

At coincident physical radius `u=w`, let `k=1-u^2>0`,

```
Z=1+k(cosh h-1), A=k sinh h, B=k cosh h,
r=(Z-1)/A=sinh h/(cosh h+1),
t=(Z-1)/A^2=1/[k(cosh h+1)].
```

These exact quotient identities on `h>0` give continuous right extensions at zero: `r(0)=0`, `t(0)=1/(2k)`. For the actual delay density `W`, the source-transfer boundary and bulk become

```
C=-W r V+(W' r^2-W B r t)U,
F T W=r^2 U W''-3B r t U W'+(3B^2-A^2)t^2 U W.
```

Consequently `C -> 0`, while

```
F T W -> -3 S(1) W(0)/8.
```

The latter is a retained finite bulk contact, not a vanishing claim. Away from coincident radii the corresponding bulk contact is zero. Thus an eventual uniform radial argument must use bounded domination rather than assume the bulk extends jointly continuously across that corner.

## Original finite clock and exact transfer

The constructed source profile is

```
g_s(u,v)=exp(2sv)[(2s+1)(2s+2)chi(v)
  -s(s-1)u(3+(2s+3)u)/(2(1+u)) chi'(v)],
W(h)=integral_0^(V-h) g_s(u,v+h)g_(-s-3)(u,v) dv.
```

Here `s=physicalRate q branch` and `chi=Real.smoothTransition`. The proof identifies `g_s` with the original `timeReducedCoefficient`, including its radial prefactor and arbitrary amplitude. The moving-interval clock is rescaled to the fixed interval `[0,1]`. Compact differentiation proves its actual smoothness, and the original earlier-source flat onset gives `W(V)=W'(V)=0`. No smoothness or endpoint-vanishing premise is supplied.

In original tortoise radius `x`, `u=radialUnit x`, the invariant is literally `invariant h x x`; the original radius-frozen direct spin-two trace equals `S` at that invariant. Differentiating the displayed current gives

```
partial_h C = W S + F T W.
```

The continuous expression for `F T W` has the retained `-3 S(1)W(0)/8` limit. Its agreement with the original expression away from zero proves interval integrability without assigning the original quotient an artificial endpoint value. The proved characteristic limit and actual terminal clock jets therefore yield

```
integral_0^V W(h) nativeSpinTwoTrace(false,q,h,x,[x,X,k]) dh
  = -integral_0^V F(Z(h)) T W(h) dh.
```

This is the degenerate direct diagonal of the [now formalized full direct/image finite transfer](hb-full-spin-two-delay-transfer.md). Compact-angular/radial transport, physical current comparison and complete cancellation remain open.

## Radius-independent geometric coefficients

Put `c=cosh h`, `s_h=sinh h`. The original characteristic factorization gives the sharper exact formulas

```
C = -W s_h/(c+1) V(Z)
    +[s_h^2 W'-c s_h W]/(c+1)^2 U(Z),

F T W = U(Z)/(c+1)^2
    *[s_h^2 W''-3c s_h W'+(2c^2+1)W].
```

Every geometric coefficient is independent of `x`: all inverse powers of `1-u^2` cancel. The original moments and source clock still depend on radius. This exposes the next horizon-transport task in those actual factors rather than in spurious geometric poles. The displayed formulas are proved for every positive delay.

## Lean statements and verification

[ThetaCuspHawkingBMSpinTwoDelayCharacteristic](../../../../formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMSpinTwoDelayCharacteristic.lean), namespace `RHTower.D4BMSpinTwoDelay`, adds nine public theorems:

- `primitive_factor`, `moments_at_one`: exact normalized native moments and their original characteristic values.
- `clockProfile_original`, `clockDensity_original`: equality with the original reduced source coefficient and moving-terminal clock.
- `clockDensity_terminal`: both terminal jets from the actual flat onset.
- `diagonal_original_trace`: the original physical kernel dictionary.
- `diagonal_characteristic`: zero boundary limit and retained finite bulk contact.
- `diagonal_finite_transfer`: exact original finite-clock transfer through the degenerate characteristic.
- `diagonal_regular_formula`: the two exact expressions with radius-independent geometric coefficients.

Scratch verification passed. The exact isolated module built without warnings in 12 seconds, three jobs, using 4,136 cached own modules and 20,533 available artifact links, with twelve dependency path packages. No existing-module or umbrella build ran. Exactly the nine new public theorems were axiom-audited in a separate scratch file; each reported only `propext`, `Classical.choice`, and `Quot.sound`. The verified source and five artifacts were installed byte-identically, and the umbrella import was added once without building it. Indexing completed and the generated API contains the new declarations. Formal lint passed with existing large-file warnings; fourteen local document links passed. All owned handles reached terminal status, the owned Lean/Lake process check was clear, and scratch, audit and search files were removed. The frontier map and universal ledger were not edited. No mathematical computation ran.

## Search applicability

Own deep queries included `degenerate characteristic integration`, broad OR `removable quotient`, and `desingularization`. Candidate statements, source arguments, methods and proposed ingredient sets were inspected. The latest inventory covered 56,460 files with 377 pending/stale source files, partial semantic coverage and mostly source-only compiler metadata. The suggested degree-conjugation and theta-likelihood desingularizer groups do not establish this native-source transfer.

`HedenmalmWardGreenRemovableExtensionKernelProjection` supplies the method of proving a continuous replacement equal to the original quotient away from its puncture. Its sinhc kernel is different; the present proof derives the actual hyperbolic quotient identities. `NativeAngularGreen` supplies compact differentiation of the original fixed-interval integrals. The native primitive and endpoint FTC supply the actual source contacts and integral step.

Broad arXiv searches used coalescence, turning point and concomitant with June–September 2026 date-oriented filters. No useful recent ingredient was returned. [Mkrtchyan, Turning point processes in plane partitions with periodic weights of arbitrary period](https://arxiv.org/abs/1908.01246) (August 2019, revised November 2019) concerns correlated limiting point processes and does not supply the deterministic source-current identity; it is not a proof premise.
