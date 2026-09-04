# Reciprocal four-channel Krein--nuclear renormalization

- **ID:** `ULF-FBG-005`
- **Stage:** 2-fully-proven
- **Type:** unconditional pre-divisor bridge and exact reconstruction theorem
- **Status:** `[PAPER-PROVED] [BRIDGE] [GENERIC J-DILATION] [NOT A SELECTOR]`
- **RH used:** no
- **Divisor used:** no
- **Parents:** `ULF-FBG-001`, `ULF-FBG-002`, `ULF-DSA-002`, `ULF-PHIN-001`

## 1. Reversal of the anomaly picture

Fresh comparison falsifies the literal claim that theta formation and cubic completion have the
same one-dimensional principal frame. If `delta` is centered horizontal rate and
`lambda_p=log(p)`, theta visibility sees

```text
x_p=delta lambda_p,
```

whereas phase-matched cubic completion sees

```text
y_p=lambda_p/delta.
```

They are not equal coordinates. They are reciprocal polarizations constrained by

```text
x_p y_p=lambda_p^2.                                   (RKC.1)
```

The common anomaly is therefore not one scalar to subtract twice. It is a mixed compact/split
frame in which theta and completion occupy reciprocal legs. This card constructs that frame and
proves that its exact indefinite pullback is the prime-mixed integral--nuclear object `T`.

## 2. Local compact and split legs

Fix an arbitrary source rate

```text
0<delta<1/2                                             (RKC.2)
```

before any divisor is supplied. For every prime `p`, put `lambda_p=log(p)` and define

```text
x_p=delta lambda_p,
y_p=lambda_p/delta,

v_p=sech(x_p),            c_p=tanh(x_p),
h_p=y_p^2,                k_p=sqrt(y_p^4-1).           (RKC.3)
```

Since `lambda_p>=log(2)>2/3` and `delta<1/2`, one has `y_p>1`, so `k_p` is real. The two exact
local laws are

```text
v_p^2+c_p^2=1,
h_p^2-k_p^2=1.                                        (RKC.4)
```

The first is the theta likelihood `SO(2)` polarization. The second is the canonical `SU(1,1)`
or real `SO+(1,1)` completion dilation: `h_p^2=y_p^4` is the exact phase-matched resonant power,
and `k_p^2=y_p^4-1` is its mandatory Krein companion.

Tensor the two legs. In the ordered four-channel basis

```text
(visible-positive, contrast-positive,
 visible-negative, contrast-negative),
```

put

```text
omega_(delta,p)=(v_p h_p,c_p h_p,v_p k_p,c_p k_p),
J=diag(1,1,-1,-1).                                    (RKC.5)
```

### Theorem A: reciprocal four-channel conservation

For every prime,

```text
omega_(delta,p)* J omega_(delta,p)=1.                 (RKC.6)
```

**Proof.** Factor the two laws in `(RKC.4)`:

```text
v_p^2 h_p^2+c_p^2 h_p^2-v_p^2 k_p^2-c_p^2 k_p^2
 =(v_p^2+c_p^2)(h_p^2-k_p^2)=1.
```

QED.

Thus the actual fusion group is the tensor-product subgroup

```text
SO(2) tensor SO+(1,1) subset O(2,2),                  (RKC.7)
```

not either compact positivity or Krein completion separately.

## 3. Prime-mixed integral--nuclear lift

Let

```text
H=ell2(Nat x Primes),
T=primeHodgeHistoryIntegralNuclearDefectT.
```

Let `E` be any finite set of history--prime coordinates, `Q_E` its projection, and

```text
T_E=Q_E T Q_E.                                        (RKC.8)
```

On `Q_E H`, let `V,C,Hc,K` be the diagonal operators with entries `v_p,c_p,h_p,k_p`. All are
bounded because `E` is finite. Define the four-channel formation-completion synthesis

```text
A_(delta,E)
 = column(V Hc, C Hc, V K, C K) T_E^(1/2)
 : Q_E H -> (Q_E H)^4.                                (RKC.9)
```

### Theorem B: exact coefficient-faithful `J`-Gram reconstruction

For every finite packet `E`,

```text
A_(delta,E)* J A_(delta,E)=T_E.                       (RKC.10)
```

The ordinary positive Gram is

```text
A_(delta,E)* A_(delta,E)
 =T_E^(1/2)(2 Hc^2-I)T_E^(1/2).                       (RKC.11)
```

**Proof.** All four scalar multipliers commute. Hence

```text
A*JA
 =T_E^(1/2)
   [Hc(V^2+C^2)Hc-K(V^2+C^2)K]
   T_E^(1/2)
 =T_E^(1/2)(Hc^2-K^2)T_E^(1/2)
 =T_E.
```

Replacing the middle minus by plus gives

```text
Hc^2+K^2=2Hc^2-I,
```

which proves `(RKC.11)`. QED.

Equation `(RKC.10)` is an operator identity, not a trace cancellation. It preserves every
unsquared matrix coefficient of `T_E`, including each same-history cross-prime entry. The four
large channel Grams are allowed to grow; cancellation occurs inside the source-fixed Krein metric
before positive closure or absolute value.

### Theorem C: cofinal integral--nuclear defect

For any increasing finite exhaustion `E_N` of the history--prime coordinates,

```text
A_(delta,E_N)* J A_(delta,E_N)=T_(E_N) -> T            (RKC.12)
```

in trace norm. Consequently

```text
lim_N Tr(A_(delta,E_N)* J A_(delta,E_N))=1,
lim_N ||A_(delta,E_N)* J A_(delta,E_N)||_1=1.          (RKC.13)
```

**Proof.** Finite projections `Q_(E_N)` converge strongly to `I`. For every trace-class operator,
two-sided finite compression converges in trace norm, so `Q_(E_N)TQ_(E_N)->T`. Apply
`(RKC.10)` and the continuity of trace and trace norm on Schatten-one. QED.

This is the requested object in its correct form:

> `T` is the cofinal `J`-Gram of a reciprocal compact/split formation homotopy. It is pre-divisor,
> prime-mixed, integral, and nuclear although its positive completion wings need not be nuclear.

The word “renormalization” here means the exact identity `(RKC.10)`. No infinite scalar is
subtracted and no `infinity-infinity` trace is evaluated.

## 4. Reconstruction of the existing cubic anomaly law

The four-channel mechanism predicts the precise Route-P anomaly split. On the depth-zero prime
carrier set

```text
w_p=115/(864 p lambda_p^2).                           (RKC.14)
```

Then

```text
w_p h_p^2
 =115 lambda_p^2/(864 delta^4 p),                    (RKC.15)

w_p k_p^2
 =w_p(h_p^2-1),                                      (RKC.16)

w_p h_p^2-w_p k_p^2=w_p.                             (RKC.17)
```

These are exactly, respectively,

```text
formation metric anomaly,
phase-matched Krein companion,
unsquared primitive cubic source weight.
```

The corpus theorem
`xiWardCubicFormationMetricAnomalyTraceWeight_eq_companion_add_source` independently certifies
`(RKC.15)--(RKC.17)`, including nonsummability of the first two prime sums and summability of the
last. Thus the Route-P anomaly law is the split-leg diagonal shadow of `(RKC.10)`.

## 5. Simultaneous organ reconstruction

One rate `delta` and one prime clock `lambda_p` now generate:

1. **theta normal coordinate:** `x_p=delta lambda_p`;
2. **visibility/contrast:** `(v_p,c_p)`;
3. **projective topology:** compactified `x`-profile has degree one;
4. **Gamma cotangent:** logarithmic barrier gradient gives the cofinal Bockstein;
5. **cubic completion:** `y_p=lambda_p/delta` and its Krein companion;
6. **Euler remainder:** split metric difference is the primitive unsquared source;
7. **prime--Hodge history:** four-channel `J`-Gram recovers the full prime-mixed nuclear `T`.

The two previously incompatible scales are not a mismatch to suppress. Their product law
`x_p y_p=lambda_p^2` is the source clock. Projection to `x` gives bounded normal geometry and its
Schatten wall; projection to `y` gives unbounded completion energy and the non-trace-class
companion. Both are shadows of one reciprocal four-channel frame.

## 6. Reflection and homotopy

Replacing `delta` by `-delta` sends `x_p,y_p,c_p` to their negatives while fixing
`v_p,h_p,k_p`. A fixed diagonal channel gauge changes the signs of the two contrast coordinates.
The `J`-Gram `(RKC.10)` remains `T_E`.

As `delta->0`, the compact frame tends strongly to its visible wall while the split frame escapes
because `h_p,k_p->infinity`. Their exact `J`-pullback nevertheless remains `T_E`. This is the
homotopy defect: ordinary positive energy diverges, compact closed observation becomes neutral,
but the framed indefinite relative current is constant and cofinally nuclear.

## 7. Direct-subunit consequence and remaining gate

The theorem supplies the missing non-scalar subtraction mechanism: cancel positive completion
wings through their shared `J`-frame before taking a trace norm. It does **not** yet prove the
direct-subunit bound. Indefinite conservation alone gives no positive estimate on a completed
horizon, and `ULF-INHD-001` forbids pushing a finite source budget through a bounded map to create
a completion-born horizon.

The exact surviving theorem must construct the theta singular completion as a morphism of these
reciprocal framed `J`-Grams. Its relative nuclear norm must be native to that completion topology,
not inherited by an invalid bounded landing. Only then may the primitive budget `<1` be paired
with unsigned escape multiplicity.

## 8. Hostile novelty and correctness audit

- The reconstruction mechanism is universal: if `T>=0` is any trace-class operator and
  `B_1,...,B_4` are commuting multipliers with

  ```text
  B_1*B_1+B_2*B_2-B_3*B_3-B_4*B_4=I,
  ```

  then `A=column(B_1,...,B_4)T^(1/2)` satisfies `A*JA=T`. Therefore `(RKC.10)` by itself does
  not narrow the pre-divisor source model class. It is an exact bridge organizing already forced
  arithmetic inputs, not a new producer or selector.
- `SO(2)`, `SO(1,1)`, tensor-product pseudo-orthogonal representations, finite compression, and
  trace-ideal convergence are standard separately.
- Existing [Krein `J`-frame theory](https://arxiv.org/abs/1703.03665) studies indefinite
  reconstruction and block frame operators; multiplier-ideal theory likewise supplies generic
  ambient language. Neither searched literature source contains the prime reciprocal constraint,
  theta/Krein tensor, or arithmetic nuclear reconstruction used here.
- Corpus search found the visibility identity, the canonical Krein companion, the scalar cubic
  anomaly split, and the prime-mixed nuclear `T`, but no four-channel `J`-Gram assembling them.
- Corpus-specific content is their exact reciprocal coupling `(RKC.1)` and coefficient-faithful
  identification `(RKC.10)--(RKC.17)`. No novelty or priority claim is made for the generic
  `J`-dilation.
- The construction does not identify source and Xi horizon, does not insert a zero, and does not
  claim that an indefinite unit supplies a positive subunit inequality.
- Absolute values must be taken only after `(RKC.10)`. Taking them channelwise destroys the
  cancellation and reproduces the proved non-trace-class companion no-go.

## 9. Formal status

Paper proof is unconditional and dependency-closed. All scalar ingredients and both endpoint
operator objects are Lean-certified; finite `J`-Gram assembly and cofinal reconstruction have not
been formalized. No Lean file was written or built during this read-only research programme.
