# CCM Clifford--Weil matrix bridge

- **ID:** `ccm-clifford-weil-matrix-bridge`
- **Stage:** 3-formalized
- **Type:** dependency-closed bridge and circularity classifier
- **Parent:** `ccm-clifford-bivariant-weil-product.md`
- **Novelty verdict:** standard Clifford/Gram algebra specialized to the exact CCM--Xi interfaces;
  useful new route infrastructure, not standalone new scientific knowledge

## Theorem

Let `C` be the literal closed nonunital rational CCM relative cyclic module and let `L_c` be its
degreewise Lefschetz translation by a class-space section `c`.  Define

```text
kappa_c = i L_c,             kappa_c^dagger = -i L_c.
```

For every `c,d`, every cyclic degree, and every chain `x`,

```text
kappa_c^dagger(kappa_d(x)) = L_(cd)(x).                       (A)
```

Thus the two Clifford phases cancel exactly on the literal closed CCM quotient.  Bilinear
extension gives the modular convolution product for finite integrated tests; analytic passage to
an entire bivariant character requires separate smoothness and summability hypotheses.

Let `H` be a complex Hilbert space and `J : H -> H` a linear isometry satisfying `J^2=1`.  For
`a in H`, set

```text
q_J(a) = Re <Ja,a>,
u_a = (a, iJa),
G_J(a) = Gram(u_a),
Gamma = [[0,i],[-i,0]].
```

Then `J` is self-adjoint, `<Ja,a>=q_J(a)` is real, and

```text
G_J(a) = [[||a||^2, i q_J(a)],[-i q_J(a),||a||^2]],           (B)
(1/2) Tr(Gamma G_J(a)) = q_J(a).                              (C)
```

The matrix `G_J(a)` is positive semidefinite without any sign hypothesis on `q_J(a)`.  Its two
channel energies satisfy

```text
(1/2)||a+Ja||^2 = ||a||^2 + q_J(a),
(1/2)||a-Ja||^2 = ||a||^2 - q_J(a).                           (D)
```

For critical-line reflection on the multiplicity-exact Xi divisor and an evaluation vector
`a=E(F)`, equation `(C)` is exactly

```text
(1/2) Tr(Gamma G_J(E(F))) = Re Weil(F,F).                     (E)
```

Consequently, positivity of all matrices in `(B)` is unconditional, whereas nonnegativity of the
scalar coefficient in `(E)` for every square-summable test is equivalent to RH.

## Proof

For `(A)`, linearity moves the inner factor `i` through `L_c`; the scalar product
`(-i)i=1`, and the exact closed-quotient action law gives `L_c L_d=L_(cd)`.

Since `J` is isometric and involutive,

```text
<Ja,b> = <J(Ja),Jb> = <a,Jb>,
```

so `J` is self-adjoint.  Taking `b=a` and using conjugate symmetry makes `<Ja,a>` real.  Expanding
the Gram matrix of `a,iJa` proves `(B)`.  Gram matrices are positive semidefinite, and direct
two-by-two multiplication proves `(C)`.  Applying the Hilbert norm addition and subtraction laws,
using `||Ja||=||a||` and `Re<a,Ja>=q_J(a)`, proves `(D)`.  The exact divisor-Hilbert realization of
the Xi Weil polarization proves `(E)`.  Finally the established full-domain Weil positivity
criterion identifies scalar nonnegativity with RH.

## Dependency audit

- No zero-location, RH, Weil-sign, or Weil-norm-completion hypothesis enters `(A)`--`(E)`.
- Matrix positivity does not imply positivity of its Clifford coefficient.
- The exact product in `(A)` is on the literal closed cyclic module; calling its integrated version
  an entire bivariant Chern product remains conditional on the missing analytic realization.
- A non-circular proof of scalar positivity still needs source arithmetic which suppresses the
  negative `J` channel, such as the proposed principal-effectivity chain homotopy.

## Gates

- [x] complete paper proof
- [x] exact recipient and convention audit
- [x] circularity classifier
- [x] unconditional formal verification
- [x] moved to Stage 3 after verification and axiom audit

Formal realization: `formal/GaloisForLFunctions/RHTower/CCM/CCMCliffordWeilProduct.lean`.
Target module build passed. Axiom audit for `(A)`, Gram positivity, coefficient extraction, exact Xi
polarization, and the full-domain RH equivalence reports only `propext`, `Classical.choice`, and
`Quot.sound`.
