# Burnol graph-cap determinant area

- **ID:** ULF-BGCA-001
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) · source-side bridge
- **Source:** `ULF-RPGT-001` · `MUST-138`
- **Statement:** The literal prime-mixed Burnol Hilbert--Schmidt synthesis defines a holomorphic
  cap in the restricted Grassmannian whose determinant-line area is exactly
  `Tr(K(1+K)^(-1))`, hence is strictly below one.

## Provenance

- `[LITERATURE]` The restricted Schatten Grassmannian, its determinant line, graph charts, and
  Kähler/Schwinger form are standard restricted-Grassmannian geometry.  Tahiri--Tumpach identify
  `Gr_res,p`, `1 <= p <= 2`, as an affine coadjoint orbit with its natural weak symplectic form.
- `[CORPUS]` `RoutePPrimitiveBurnolBaseNuclearSynthesis` constructs the literal all-prime
  Hilbert--Schmidt synthesis `A_base` and proves

  ```text
  ||A_base||_HS^2 = B_base < 1.
  ```

  `RoutePPrimitiveBurnolMatrixCompleteColligation` retains the full cross-prime Gram matrix.
- `[PROVED HERE]` The exact determinant-line area formula and its application to `A_base`.
- `[NOT CLAIMED]` No completed Xi divisor, Hardy index, or RH selection follows from this cap
  alone.  The missing sewing theorem is isolated in `ULF-TSBC-001`.

## 1. Construction

Let `H_+`, `H_-` be separable complex Hilbert spaces and let

```text
A : H_+ -> H_-
```

be Hilbert--Schmidt.  Put

```text
K = A* A.
```

Then `K` is positive trace class and `Tr K=||A||_HS^2`.  Relative to the polarization
`H_+ directSum H_-`, define the graph cap

```text
Gamma_A : D -> Gr_res,2(H_+ directSum H_-),
Gamma_A(z) = graph(z A).                              (BGCA.1)
```

It is holomorphic and lies in the big graph cell.  On that cell normalize the determinant-line
Kähler form by

```text
omega_det = (i/(2*pi)) partial delbar
  log det(I + Z* Z).                                  (BGCA.2)
```

This normalization makes the determinant line integral: a positive generator of the finite
Grassmannian Schubert sphere has area one.

The cap is pre-divisor: it uses only `A`.  For `A=A_base`, its domain basis is indexed by every
resolved prime/depth source cell and its range is the common Burnol half-line space.  Therefore

```text
K_(alpha,beta) = inner(A_base e_alpha, A_base e_beta) (BGCA.3)
```

contains the complete cross-prime Gram, before determinant or trace extraction.

## 2. Exact area theorem

**Theorem BGCA-A.** For every Hilbert--Schmidt `A`,

```text
Area_det(Gamma_A)
  := integral_D Gamma_A^* omega_det
   = Tr(K (I+K)^(-1))
   = sum_j lambda_j/(1+lambda_j)
  <= Tr K
   = ||A||_HS^2.                                      (BGCA.4)
```

If `A != 0`, the first inequality is strict.

**Proof.** Since `A` is Hilbert--Schmidt, `K=A* A` is positive trace class.  Let
`(lambda_j)` be its nonnegative eigenvalues, repeated with multiplicity.  Then
`sum_j lambda_j<infinity`.  The Fredholm determinant exists and the pullback Kähler potential is

```text
Phi_A(z)
  = log det(I + |z|^2 K)
  = sum_j log(1 + lambda_j |z|^2).                    (BGCA.5)
```

On compact subsets of the unit disk the series and both mixed derivatives converge normally:
the absolute value of each mixed second derivative is bounded by `lambda_j`.  Hence

```text
Gamma_A^* omega_det
  = sum_j (i/(2*pi)) partial delbar
      log(1 + lambda_j |z|^2).
```

For one eigenvalue `lambda>=0`, writing `z=r exp(i theta)` gives

```text
integral_D (i/(2*pi)) partial delbar log(1+lambda|z|^2)
  = 2 integral_0^1 lambda*r/(1+lambda*r^2)^2 dr
  = lambda/(1+lambda).                                (BGCA.6)
```

All summands are nonnegative, so Tonelli gives the first two equalities in `(BGCA.4)`.  Functional
calculus gives the operator expression `Tr(K(I+K)^(-1))`.  Finally

```text
0 <= lambda/(1+lambda) <= lambda,
```

with strict inequality for every positive `lambda`.  Summing proves the remaining assertions.
QED.

## 3. Arithmetic specialization

Let

```text
A_base = routePPrimitiveBurnolBaseSynthesis,
K_base = A_base* A_base.
```

The corpus proves

```text
Tr K_base = ||A_base||_HS^2 = B_base < 1.             (BGCA.7)
```

Therefore BGCA-A gives the unconditional source theorem

```text
0 <= E_base
   := Area_det(Gamma_(A_base))
    = Tr(K_base(I+K_base)^(-1))
   <= B_base
    < 1.                                              (BGCA.8)
```

`A_base` is nonzero, so in fact `E_base<B_base`; only the weaker chain in `(BGCA.8)` is needed.

This is the first direct sub-unit bound that does not ask for a source-to-completion landing.
The quantity below one is the area of a nonzero, coefficient-native formation cap in the same
restricted-Grassmannian category in which the cubic defect lives.

## 4. What the theorem does and does not preserve

The map `Gamma_(A_base)` is genuinely prime-mixed because its point at every `z` is the graph of
the full synthesis and its tangent metric is the full operator `K_base`, including off-diagonal
prime/depth entries.  The final scalar area is spectral and therefore does not, by itself,
reconstruct those labels.  Any completion sewing must act on the cap or its determinant line,
not merely on the number `E_base`.

The theorem avoids three closed routes:

1. It transports no finite source vector to a completion horizon, so the dense-core bounded
   landing no-go does not apply.
2. Its determinant line is the canonical line bundle over `Gr_res,2`, not the multi-dimensional
   top exterior target killed by `CCMEvansDeterminantLine`.
3. It moves the graph subspace with `z`; it is not a fixed-support separated Quillen response
   killed by `FZZCigarParityFixedSupportQuillenReplicaNoGo`.

It still does **not** identify this area with `Tr mathsf T_D`.  Such an identification without a
coefficient-native geometric sewing would merely rename the retired landing.

## 5. Literature boundary

- Tahiri--Tumpach, [The Restricted Schatten-class Grassmannian as affine coadjoint
  orbit](https://arxiv.org/abs/2605.22512): restricted Schatten Grassmannian and weak symplectic
  form.
- Stevenson, [The geometry of infinite dimensional Grassmannians and the
  Mickelsson--Rajeev cocycle](https://arxiv.org/abs/0802.3608): determinant bundles, connection,
  curvature, and cocycle.
- Andruchow--Recht--Varela, [Graphs of operators as points in the Grassmann
  manifold](https://arxiv.org/abs/2608.30120): graph charts and their completion boundary.

These references supply the ambient geometry.  The arithmetic insertion `A_base`, exact identity
`(BGCA.8)`, and proposed source-to-Schubert confinement role are corpus-specific.

## 6. Audit status

- Paper dependencies: closed.
- Lean status: intentionally pending; current task phase forbids Lean work.
- RH status: no claim.
- Surviving edge: construct a source-native positive sewing whose Schubert bubble charge is the
  cubic relative index and whose total energy is bounded by `(BGCA.8)`.

## Log

- 2026-09-03 — `[PROVED HERE]` exact graph-cap area and sub-unit arithmetic specialization.
