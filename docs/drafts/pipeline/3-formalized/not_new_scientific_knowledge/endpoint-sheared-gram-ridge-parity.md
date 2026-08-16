# Endpoint-sheared Gram ridge parity

- **ID:** `endpoint-sheared-gram-ridge-parity`
- **Stage:** 3-formalized
- **Type:** THEOREM (paper), `[PAPER-PROVED] [BRIDGE]`
- **Scientific status:** `[NOT NEW SCIENTIFIC KNOWLEDGE] [POSITIVE NO-GO SURVIVOR] [NOT AN RH PROOF]`
- **Source:** the global response-correlation target `(AC25)` in
  `critical-multiplicative-compensated-cancellation-rh.md`
- **Statement:** The finite two-frequency transform of a common source Gram packet is exactly a
  sheared Gram kernel.  A real-Gram source makes the full endpoint-swap involution even, so every
  endpoint-swap-odd channel vanishes exactly.

## Exact statement

Let `R` be a finite commutative ring, let `I` be a finite source set, let `E` be a complex inner
product space, and fix

```text
rho : I -> R,
x   : I -> E.
```

Let `chi : (R,+) -> C^x` be an additive character with the unitary convention

```text
chi(s+t)=chi(s)chi(t),
conj(chi(s))=chi(-s).                                    (1)
```

Mathlib's complex inner product is conjugate-linear in its first argument.  Define the frequency
packet and the sheared double transform by

```text
X_j = sum_(n in I) chi(j rho_n) x_n,                     (2)

W(a,b)=sum_(m,n in I)
  chi(a rho_m+b(rho_n-rho_m)) <x_m,x_n>.                 (3)
```

Then

```text
W(a,b)=<X_(b-a),X_b>.                                    (4)
```

Consequently, with

```text
C(j,k)=W(k-j,k),                                         (5)
```

one has

```text
C(j,k)=<X_j,X_k>,
C(j,j)=||X_j||^2,
C >= 0,                                                  (6)

sum_(j,k) conj(c_j) C(j,k)c_k
  = ||sum_j c_j X_j||^2,                                 (7)

|W(a,b)| <= ||X_(b-a)|| ||X_b||.                         (8)
```

Assume in addition the **real-Gram condition**

```text
<x_m,x_n>=<x_n,x_m>  for all m,n.                        (9)
```

Since every complex Gram kernel is Hermitian, `(9)` is exactly the assertion that all of its
entries are fixed by complex conjugation.  Under `(9)`, the whole sheared kernel, not only its two
endpoint ridges, satisfies

```text
W(a,b)=W(a,a-b).                                         (10)
```

In particular,

```text
W(a,0)=W(a,a).                                           (11)
```

More generally, if `eta : R -> C` is endpoint-swap odd at `a`, meaning

```text
eta(a-b)=-eta(b),                                        (12)
```

then

```text
sum_(b in R) eta(b)W(a,b)=0.                             (13)
```

No asymptotic estimate is asserted.

## Complete paper proof

Expanding the right side of `(4)` using conjugate-linearity in the first argument gives

```text
<X_(b-a),X_b>
 =sum_(m,n)
   conj(chi((b-a)rho_m)) chi(b rho_n)<x_m,x_n>.
```

By `(1)`, the scalar coefficient is

```text
chi(-(b-a)rho_m)chi(b rho_n)
 =chi(-(b-a)rho_m+b rho_n)
 =chi(a rho_m+b(rho_n-rho_m)).
```

This is the coefficient in `(3)`, proving `(4)`.

Substituting `(a,b)=(k-j,k)` into `(4)` gives

```text
C(j,k)=W(k-j,k)=<X_(k-(k-j)),X_k>=<X_j,X_k>,
```

which proves the first equality in `(6)`.  The diagonal identity follows from
`<X_j,X_j>=||X_j||^2`.  For arbitrary coefficients `c_j`, sesquilinearity gives

```text
sum_(j,k) conj(c_j)C(j,k)c_k
 =<sum_j c_j X_j, sum_k c_k X_k>
 =||sum_j c_j X_j||^2.
```

This proves `(7)` and positive semidefiniteness in `(6)`.  Cauchy--Schwarz applied directly to
`(4)` proves `(8)`.

It remains to prove the parity statement.  First rewrite `(3)` as

```text
W(a,b)=sum_(m,n)
  chi((a-b)rho_m+b rho_n)<x_m,x_n>.                      (14)
```

Interchanging `m` and `n` in this finite sum and applying `(9)` gives

```text
W(a,b)
 =sum_(m,n) chi((a-b)rho_n+b rho_m)<x_n,x_m>
 =sum_(m,n) chi(b rho_m+(a-b)rho_n)<x_m,x_n>
 =W(a,a-b).
```

This proves `(10)`, and `(11)` is its specialization at `b=0`.

Finally, `sigma_a(b)=a-b` is an involutive permutation of `R`.  Reindexing the finite sum in
`(13)` by `sigma_a` and using `(10)` and `(12)` shows that the sum equals its own negative.  Since
the coefficient field is `C`, the sum is zero.  This proves `(13)`.  `QED`

## Sharpness of the real-Gram hypothesis

The endpoint equality is false for an arbitrary complex Gram packet.  Take

```text
R=Z/2Z, I={0,1}, rho(n)=n,
chi(0)=1, chi(1)=-1,
E=C, x_0=1, x_1=i.
```

Then `X_0=1+i` and `X_1=1-i`.  At `a=1`, with the conjugate-linear-first convention,

```text
W(1,0)=<X_1,X_0>= 2i,
W(1,1)=<X_0,X_1>=-2i.
```

Thus character unitarity and Hermitian Gram symmetry alone do not identify the endpoint ridges.
The additional real-Gram condition `(9)` is necessary for this route in precisely the sense exposed
by the counterexample.

## Positive-survivor insight and scope

`[POSITIVE SURVIVOR]` The failed unrestricted endpoint-ridge argument does not leave merely a
negative statement.  It exposes an exact dichotomy:

```text
arbitrary complex Gram source:
  no endpoint equality;

common real-Gram source:
  full b <-> a-b parity, hence exact annihilation of every swap-odd channel.
```

For `(AC25)`, this says that an endpoint-swap-odd part of the common physical response is absent
before estimation.  The remaining swap-even part is still a positive Gram channel and receives no
`M^(-1)` saving from `(4)`--`(13)` alone.  Therefore this theorem narrows the response-correlation
target but does not solve it or control an arbitrary signed boundary Jordan mass.

The transform identity, Gram positivity, Cauchy--Schwarz, and involution parity are finite harmonic
analysis and Hilbert-space algebra.  They are useful route-specific bridge material, not new
scientific knowledge.  No scientific-priority claim is made.

## Formal status

- [x] exact claim is dependency-closed on paper
- [x] unrestricted endpoint equality killed by an explicit two-point counterexample
- [x] strongest positive replacement upgraded from two ridges to full endpoint-swap parity
- [x] Lean source drafted in
  `formal/GaloisForLFunctions/RHTower/EndpointShearedGramRidgeParity.lean`
- [x] targeted Lean validation
- [x] axiom audit
- [x] Stage 3 promotion and umbrella/index wiring

## Log

- 2026-07-18 — paper proof closed; classified as a standard but non-trivial positive survivor of
  the unrestricted endpoint-ridge no-go.

## Lean formalization

Module: `formal/GaloisForLFunctions/RHTower/EndpointShearedGramRidgeParity.lean`
(namespace `RHTower`), wired into the `GaloisForLFunctions.RHTower` umbrella.

| Paper statement | Lean declaration |
|---|---|
| `(2)` frequency packet | `endpointFrequencyPacket` |
| `(3)` sheared double transform | `endpointShearedDoubleTransform` |
| `(14)` separated phase | `endpointShearedDoubleTransform_eq_separated` |
| `(4)` sheared Gram identity | `endpointShearedDoubleTransform_eq_inner_frequencyPacket` |
| `(6)` diagonal norm law | `endpointShearedDoubleTransform_zero_eq_norm_sq` |
| `(8)` Cauchy--Schwarz | `norm_endpointShearedDoubleTransform_le` |
| `(5)`, `(6)` unsheared Gram matrix and positivity | `endpointShearedGramMatrix`, `endpointShearedGramMatrix_apply`, `endpointShearedGramMatrix_eq_gram`, `endpointShearedGramMatrix_posSemidef` |
| `(7)` quadratic form identity | `endpointShearedGramMatrix_quadratic_eq_inner`, `endpointShearedGramMatrix_quadratic_eq_norm_sq` |
| `sigma_a(b)=a-b` involution | `endpointSwapEquiv` |
| `(10)` full real-Gram endpoint-swap parity | `endpointShearedDoubleTransform_endpointSwap` |
| `(11)` endpoint ridge equality | `endpointShearedDoubleTransform_left_ridge_eq_right_ridge` |
| `(12)`--`(13)` swap-odd annihilation | `sum_endpointSwapOdd_mul_even_eq_zero`, `sum_endpointSwapOdd_mul_endpointShearedDoubleTransform_eq_zero` |
| sharpness counterexample over `Z/2Z` | `signAddChar`, `twoPointResidue`, `twoPointSource`, `twoPoint_left_ridge`, `twoPoint_right_ridge`, `twoPoint_left_ridge_ne_right_ridge` |

Audit: direct `lake env lean` check clean, targeted module build clean, umbrella import already
wired, `#print axioms` on every capstone returns only `propext`, `Classical.choice`, `Quot.sound`.
