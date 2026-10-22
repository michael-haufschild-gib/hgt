# Hedenmalm pointed-moment orientation boundary

- **ID:** `hedenmalm-pointed-moment-orientation-boundary`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) / EXACT OPEN-CORE BOUNDARY
- **Scientific status:** `[PROVED] [BRIDGE] [NOT AN RH PROOF]`
- **Statement:** The pointed analytic moment germ uniquely reconstructs the Hedenmalm Bezoutian,
  but nonnegativity of its Hermitian diagonal is exactly equivalent to RH.

## Result

Let `M` be the normalized pointed prime--archimedean moment germ, let

```text
T(z) = -z M(z),
B_M(z,v) = XiC(z) XiC(v) dslope(z M(z))(z,v).
```

The already formalized analytic determinacy theorem shows that the complete Taylor jet of `M`
determines `M`, its odd Euler--Gamma lift `T`, the centered function `XiC`, and the off-diagonal
Bezoutian.  The global source-recovery identity additionally gives, for every `Im z > 0`,

```text
B_M(z,conj z)
  = |XiC(z)|^2 (T(conj z)-T(z))/(z-conj z).               (1)
```

Consequently the following are equivalent:

```text
the Hermitian diagonal of B_M is nonnegative throughout the centered upper half-strip;
the continued prime--archimedean one-Cauchy diagonal is nonnegative there;
RH.                                                        (2)
```

Thus all-order moment determinacy removes source ambiguity and determines every Bezoutian value.
What it does not provide is a theorem placing those determined values in the nonnegative chamber.
The remaining Hilbert--Polya theorem is exactly that global orientation theorem for the uniquely
selected Bezoutian.

The complementary theta-source normalization is now formalized as well.  For
`z=b+ia`, `0<a<1/2`, at every regular point,

```text
B_M(z,conj z)
  = B_Xi(z,conj z)
  = Q_theta(a,b)/(2a),                                   (3)
```

where `Q_theta` is the split rank-four Hankel--Krein current and also the Fourier transform of the
actual center-mixed theta autocorrelation tangent.  Hence moment reconstruction, theta-source
incidence, and the Fourier current select exactly the same scalar, while none of the reconstruction
identities proves its sign.

The universal positive-form classification closes the adjacent analytic representation problem:
every continuous nonnegative momentum-symmetric Schwartz form has a unique positive temperate
spectral measure, and theta nullity forces that measure onto the real `Xi` divisor. This does not
orient the reconstructed scalar. Nonnegativity is an input to that classification, while the
pointed moment module supplies only the uniquely reconstructed Bezoutian. The remaining gap is
therefore not measure existence, moment determinacy, or source ambiguity; it is exactly the sign
of the actual source-selected Bezoutian.

## Positive implementation law

Any successful use of the Hedenmalm moment module must add a source-specific mechanism proving the
sign in `(1)`.  Analytic determinacy, exact reconstruction, raw moment positivity, evenness,
Schwartz decay, and entire continuation do not supply that mechanism.  In the current source
coordinate, the required additional carrier is the cofinal mixed center--frequency structure of
the theta source, equivalently the all-prime divisor-character/archimedean coupling already
isolated in `theta-wigner-eisenstein-orientation-current.md`.

The formalized local-frame obstruction sharpens this obligation.  The horizontal autocorrelation
tangent of the actual tilted theta source cannot be a finite sum of autocorrelations of
constant-coefficient polynomial differential filters.  More generally, no entire spectral
density can orient that tangent.  The canonical orientation multiplier is forced to have an
infinite singular subset indexed by translated-divisor boundary zeros, and its residue germs carry
their exact Xi multiplicities.  Thus the missing sign must enter through this non-entire
divisor-sensitive carrier, or through a genuinely nonlocal/infinite-dimensional construction
whose spectral density retains the same transverse data.  See
`hedenmalm-finite-local-autocorrelation-frame-obstruction.md` and
`hedenmalm-canonical-orientation-singularity-carrier.md`.

## Formal certificate

File:
`formal/GaloisForLFunctions/RHTower/XiHedenmalmMomentOrientationBoundary.lean`.

The theta-source normalization and Fourier-sign equivalence are in
`formal/GaloisForLFunctions/RHTower/Hedenmalm/HedenmalmCenterMixedOrientationBoundary.lean`.

Theorem surface:

```text
xiHedenmalmPointedMomentBezoutian_conj_eq_normSq_mul_sourceDiagonal
xiHedenmalmPointedMomentUpperHermitianDiagonalNonnegative_iff_source
xiHedenmalmPointedMomentUpperHermitianDiagonalNonnegative_iff_riemannHypothesis
xiHedenmalmPointedMomentBezoutian_upper_conj_eq_krein_div
thetaCuspCenterMixedFourierNonnegative_iff_riemannHypothesis
```

The proofs assume neither RH nor positivity.  The final equivalence is a boundary theorem and
must not be cited as a sign proof.

## Gates

- [x] complete analytic and algebraic proof
- [x] formalized in Lean without `sorry`, `axiom`, `opaque`, or `unsafe`
- [x] exact module build
- [x] axiom audit
- [ ] source-specific sign theorem
- [ ] RH
