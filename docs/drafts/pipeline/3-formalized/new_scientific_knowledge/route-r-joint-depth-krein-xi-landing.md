# Route R joint-depth Krein source-to-Xi landing

- **ID:** `route-r-joint-depth-krein-xi-landing`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **RH used:** no
- **Xi zero used:** no
- **Computation used:** no
- **Parents:** `route-r-primitive-joint-depth-biorthogonal-common-test`,
  `route-r-depth-one-positive-completion-no-go`

## Frontier statement

Depth-one mass proves that independent positive Euler and Gamma/polar channels
cannot produce the completed prime--archimedean kernel: any exact correction
has a strictly negative central budget.  The primitive source and reciprocal
co-source are also different Hilbert vectors, so replacing their pairing by a
positive Gram square changes the source problem.

The literal carrier is the Hilbert direct sum

```text
K = ell2(Fin 2 x (Primes x Nat)).
```

Let `J` exchange the two `Fin 2` slots.  Lean proves that `J` is a linear
isometry, an involution, and self-adjoint.  Hence

```text
[x,y]_J = <x,Jy>
```

is a genuine Hermitian Krein form, not a Banach-product analogy.  Its
diagonal and anti-diagonal sectors satisfy

```text
[(h,h),(h,h)]_J   =  2 ||h||^2,
[(h,-h),(h,-h)]_J = -2 ||h||^2.
```

Thus the source has the negative sector forced by the quantitative
positive-completion obstruction.

## Literal off-diagonal producer

For `n=p^(e+1)`, the resolved source and co-source coordinates are

```text
L_w(p,e) = log(p) / sqrt(n) * n^(-w),
R_v(p,e) =          1 / sqrt(n) * n^(-v).
```

Put `L_w` in slot zero and `R_v` in slot one.  If `Re(w),Re(v)>0`, then

```text
[(0,R_v),(L_w,0)]_J
  = <R_v,L_w>
  = LSeries Lambda (1+w+conj(v)).
```

No geometric mean, positive square, squarefree projection, or divisor-fed
coefficient enters this identity.  Every prime and valuation-depth label is
retained until the final off-diagonal matrix coefficient.

For a positive complex Laplace displacement `u`, the canonical split

```text
w = u/2,
v = conj(u)/2
```

has `w+conj(v)=u`, so the same coefficient is the complete von Mangoldt
Laplace channel at `u`.

## Pole and Gamma completion

The polar-filled coefficient satisfies

```text
1/u + 1/(u+1) - [(0,R_v),(L_w,0)]_J
  = regularizedCriticalMellinDefect(u).
```

Under centered coordinate `z=-i(u+1/2)`, Gamma completion gives the
unconditional regular-locus identity

```text
i * (regularizedCriticalMellinDefect(u)
     + gammaRealLogConnection(u+1))
  = xiRelativeResolventTrace(z).
```

The zeta nonvanishing premise is only the domain condition for equality of
totalized logarithmic-derivative values away from meromorphic poles.  It is
not a zero-location premise.

At balanced reflection the literal coordinate cross-term is not absolutely
summable.  Therefore the source cannot be extended to that wall by pretending
both ordinary Hilbert legs still exist; pole-filled scalar continuation is
essential.

## New knowledge and anti-theatre audit

Prior source landing produced the real one-parameter scalar trace, and the
biorthogonal module produced the complex two-leg pairing.  This theorem adds
the missing geometric object: one actual Hilbert direct sum, a unitary
self-adjoint involution, an explicit negative sector, and an exact
off-diagonal source coefficient whose polar/Gamma completion is the Xi
relative resolvent.  It supplies the signed producer left alive by the
positive-completion no-go.

This is not RH and is not the transverse annihilator of the actual Green
record.  The coefficient remains rank-one in its prime/depth legs.  The
separate off-diagonal-holonomy classification shows that normalized
rank-one reflection incidence is a flat coboundary: all cycle holonomies are
blind, while uniform wall capacity is already equivalent to RH.  Therefore
the Krein landing must not be advertised as zero selection.

The exact surviving source must add a genuinely nonseparable Euler--Gamma or
divisor-coupled pre-codiagonal differential before reflection pairing.  Its
arithmetic boundary identity must annihilate the actual Green record; only
then may the already proved conservative common-test sector force RH.

## Lean certificate

```text
formal/GaloisForLFunctions/RHTower/
  EulerPrimitiveJointDepthKreinXiLanding.lean
```

Capstones:

- `xiGammaEulerPrimitiveJointDepthFundamentalSymmetry_sq`;
- `xiGammaEulerPrimitiveJointDepthFundamentalSymmetry_selfAdjoint`;
- `xiGammaEulerPrimitiveJointDepthKreinPair_antidiagonal_re_neg`;
- `xiGammaEulerPrimitiveJointDepthKreinPair_coSource_source_eq`;
- `xiGammaEulerPrimitiveJointDepthKreinSplitPair_eq`;
- `xiGammaEulerPrimitiveJointDepthKreinPoleFilled_eq_regularized`;
- `xiGammaEulerPrimitiveJointDepthKreinCompletedTrace_eq_xiRelativeResolventTrace`;
- `xiGammaEulerPrimitiveJointDepthKreinBalancedCrossTerm_not_summable`.
