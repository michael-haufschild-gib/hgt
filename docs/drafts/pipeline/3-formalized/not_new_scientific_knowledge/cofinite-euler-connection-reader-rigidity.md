# Cofinite Euler tangent pairs determine continuous semilocal connection readers

- **ID:** `cofinite-euler-connection-reader-rigidity`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean), `[VALUE-RELATION INTERFACE]`, `[TOP-DOWN GAP REDUCTION]`
- **Scientific status:** `[PROVED] [BRIDGE] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Lean:** `formal/GaloisForLFunctions/RHTower/CriticalDiscEulerConnectionRigidity.lean`
- **Parents:** `prime-euler-unit-tangent-completeness.md`;
  `semilocal-euler-kernel-chart-differentiability.md`;
  `sonin-prime-seam-exterior-factorization.md`
- **Statement:** Compactness or vanishing of a continuous linear or polarized bilinear connection
  reader on the cofinite actual FE-paired Euler tangents propagates to the entire analytic FE-odd
  Schwarz-real source fibre. Norm derivatives and iterated mixed derivatives of compact operator
  families are compact.

## The theorem

Fix critical discs

```text
0 <= r_0 < r_1 < 1/2
```

and delete an arbitrary finite set `S` of primes. Let `t_p` be the literal actual-source
FE-paired Euler-unit tangent on the disc of radius `r_0`. Lean already proves

```text
analytic + FE odd + Schwarz real
  -> closed real span {t_p : p notin S}.                   (1)
```

The new formal theorem proves four propagation laws.

1. For every continuous real-linear reader `L` with values in an arbitrary real normed space,

   ```text
   (forall p notin S, L(t_p)=0) -> L(f)=0.                (2)
   ```

2. If `L` is operator-valued, then

   ```text
   (forall p notin S, L(t_p) is compact)
     -> L(f) is compact.                                  (3)
   ```

3. For every continuous real-bilinear reader `B`,

   ```text
   (forall p,q notin S, B(t_p,t_q)=0)
     -> B(f,g)=0.                                         (4)
   ```

4. In the operator-valued case,

   ```text
   (forall p,q notin S, B(t_p,t_q) is compact)
     -> B(f,g) is compact.                                (5)
   ```

Here `f` and `g` are arbitrary analytic FE-odd Schwarz-real germs on the larger disc, restricted
to the smaller one. The proof applies the one-variable closed-span theorem twice; compactness
propagates because compact operators form an operator-norm closed linear subspace.

The same module proves the differential input needed at finite place:

```text
F(t) compact for every t + norm derivative F'(0)=T
  -> T compact,                                           (6)

F(s,t) compact for every s,t
  + iterated norm mixed derivative d_s d_t F(0,0)=T
  -> T compact.                                           (7)
```

Thus no separate compactness estimate is needed once a prime-pair connection coefficient is
identified as the mixed derivative of a norm-analytic finite completed quasi-inner family.

## Top-down consequence

The previous semilocal source problem asked for a global Xi-zero-fibre annihilation or compactness
estimate for the tangential connection. Equations `(5)` and `(7)` reduce that problem to a finite
exact identity.

Connes--Consani prove that every finite archimedean-compensated local-factor product has compact
Hardy off-diagonal block. The analytic semilocal kernel chart supplies the finite Euler parameters.
Consequently, once the polarized connection reader on the tangent pair `(t_p,t_q)` is identified
with the mixed parameter derivative of that compact off-diagonal family, `(7)` proves its
compactness for each pair and `(5)` propagates compactness to the full analytic source fibre.

The remaining source-to-RH chain is therefore

```text
[OPEN VALUE RELATION]
normal Xi-zero-fibre Gram coboundary
  = polarized mixed derivative of the finite completed semilocal source
    modulo compact residual terms
-> compactness on every prime-tangent pair by (7)
-> compactness on the complete analytic FE-odd Schwarz source fibre by (5)
-> compact canonical two-prime Sonin Gram coboundary
-> all Xi prime-seam charges are equal
-> their common value is zero by unconditional cofinal prime decay
-> RH.                                                     (8)
```

This is strictly sharper than requesting an unexplained global connection estimate. The analytic
estimate and infinite-dimensional propagation are discharged; the open task is one finite
operator value relation compatible with the primal--dual semilocal pairing.

## Exact open problem

Start from the explicit finite Euler chart and the arithmetic connection contraction proved in
`semilocal-dual-pair-euler-connection-source-law.md`.  Construct only its completed two-parameter
prime--Gamma cutoff/resolvent Hardy block `H_{p,q}(s,t)` and the polarized
semilocal connection/normal-curvature reader `B`. Prove, on an actual Xi divisor fibre and modulo
the already controlled compact residual terms,

```text
B(t_p,t_q) = partial_s partial_t H_{p,q}(0,0).             (9)
```

The right side is compact by the formal theorem as soon as norm differentiability and compactness
of the finite family are supplied. No prime-cutoff rate, global limiting measure, Xi zero-location
assumption, or positivity hypothesis is part of `(9)`.

## Shorter scalar-Hessian alternative

The actual Euler-point scalar tangent now has the exact FE--Schwarz factorization

```text
T_p(conj(rho))-T_p(1-rho)
 =C_p(rho)(1-p^(-conj(rho))p^(-(1-rho)))
   /[(1-p^(-conj(rho)))^2(1-p^(-(1-rho)))^2].            (10)
```

Every factor multiplying `C_p(rho)` is invertible in the open strip, and every one prime seam is
faithful.  Therefore an independently constructed completed-source reader which returns

```text
T_p(conj(rho))=T_p(1-rho)                                (11)
```

for one fixed prime already closes the orientation problem.  It need not prove `(9)`, propagate
over the cofinite tangent span, or isolate an empty-chart coefficient.  Conversely, the current
cofinite compactness theorem does not produce `(11)`: it acts on FE-paired tangent germs and
operator compactness, while `(11)` is a scalar graded-reality value on an Xi fibre.  The two are
alternative source interfaces and must not be conflated.

Moreover, the literal source identity

```text
Phi_p'(s)=-log(p) T_p(s)                                 (12)
```

turns `(11)` into equality of the genuine spectral connection curvatures at the same two fibre
points.  This makes the short alternative directly addressable by a scalar normal-curvature
reader; it is not necessary to manufacture an Euler-parameter Hessian operator.  The existing
reader theorem still does not force that scalar equality, but the open producer is now a value
relation in the reader's native spectral variable.

## Scope and falsifiers

- The theorem does not define the cutoff/resolvent semilocal connection reader or prove `(9)`; the
  pre-compression scalar connection is now explicit.
- It does not claim that the metric tangent itself is compact; Lean proves the one-prime positive
  Euler metric corner is noncompact.
- It does not turn finite quasi-innerness into normal-curvature compactness without the exact
  primal--dual value relation.
- A proposed reader that is not continuous in the compact-disc norm, is not real-bilinear on the
  FE-odd Schwarz source fibre, or depends on the divisor through an inserted RH-equivalent
  selection does not satisfy this theorem's interface.
- The result uses no RH assumption and contains no Xi divisor data.

## Literature boundary

- Connes--Consani, [*Quasi-inner functions and local factors*](https://arxiv.org/abs/2008.10974),
  supplies compactness of the Hardy off-diagonal block for every finite completed local-factor
  product.
- Connes--Consani--Moscovici,
  [*Zeta zeros and prolate wave operators*](https://arxiv.org/abs/2310.18423), supplies the
  semilocal Sonin spaces and their finite-place stability.
- Burnol, [*Two complete and minimal systems associated with the zeros of the Riemann zeta
  function*](https://arxiv.org/abs/math/0203120), supplies the zero-indexed Sonine evaluation side
  relevant to the still-open value relation `(9)`.

Closedness of compact operators under operator-norm limits and propagation through a dense span
are standard functional analysis. No novelty claim is made.

## Gates

- [x] derivatives of compact operator families remain compact
- [x] iterated mixed derivatives of compact two-parameter families remain compact
- [x] arbitrary-target continuous linear annihilation propagates from cofinite Euler tangents
- [x] operator compactness propagates from cofinite Euler tangents
- [x] polarized bilinear vanishing propagates from all cofinite tangent pairs
- [x] polarized operator compactness propagates from all cofinite tangent pairs
- [x] Lean module imported by the `RHTower` umbrella
- [x] isolate the any-one-prime actual-Hessian value alternative to the bilinear reader
- [x] rewrite that alternative as one genuine spectral-connection curvature equality
- [ ] define the actual completed two-parameter semilocal Hardy block in Lean
- [ ] prove the exact zero-fibre value relation `(9)`
- [ ] extract compact canonical Sonin Gram coboundaries and close RH
