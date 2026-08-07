# Burnol co-Poisson bilateral dilation source covariance

- **ID:** `burnol-copoisson-bilateral-dilation-source-covariance`
- **Stage:** 3-formalized
- **Type:** `[LITERATURE] [BRIDGE] [PAPER-PROVED]`
- **Route:** R, Gamma–co-Poisson–Sonin source-normal landing
- **Lean target:** `RHTower/BurnolCoPoissonDilationSourceCovariance.lean`

## Claim

Let (C_a\subset L_a) be the closed Burnol co-Poisson source space and
(Y_a=L_a\cap C_a^\perp).  For (a>0), (r\geq1), and normalized multiplicative dilation

\[
 (U_r f)(t)=\sqrt r\,f(rt),
\]

both orientations preserve the source filtration:

\[
 U_r C_a\subset C_{a/r},\qquad U_r^*C_a=U_{1/r}C_a\subset C_{a/r}.       \tag{1}
\]

Consequently, for every (y\in Y_{a/r}),

\[
 U_r y,U_r^*y\in C_a^\perp.                                           \tag{2}
\]

Writing (P_a) for orthogonal projection onto (L_a) and (E_a) for projection onto
(Y_a=L_a\cap C_a^\perp), one therefore has the exact projection-collapse laws

\[
 E_aU_ry=P_aU_ry,\qquad E_aU_r^*y=P_aU_r^*y.                           \tag{3}
\]

Thus the two Route-R quotient bonding maps have no hidden co-Poisson source-projection term on
their actual domain.  Their remaining failure to be a dagger pair is purely the Sonin aperture
projection loss.

## Proof

For an integrable seed (g) define

\[
 (D_rg)(x)=\sqrt r\,g(rx).
\]

The literal positive co-Poisson sum is

\[
 P_g(t)=\sum_{n\ge1}\frac{g(|t|/n)}n-
       \int_0^\infty g(1/y)\frac{dy}{y}.
\]

Termwise scalar extraction and the change of variables (y=rz) in the logarithmic correction
give

\[
 P_{D_rg}(t)=\sqrt r\,P_g(rt).                                        \tag{4}
\]

The change of variables is legitimate because a Burnol seed is integrable and supported in the
compact multiplicative window ([a,a^{-1}]), so (g(y)/y) and (g(1/y)/y) are integrable on the
positive ray.  The scaled seed is integrable.  If
(operatorname{supp}g\subset[a,a^{-1}]), then

\[
 \operatorname{supp}D_rg\subset[a/r,(ar)^{-1}]
 \subset[a/r,(a/r)^{-1}],                                             \tag{5}
\]

where the second inclusion uses (r\ge1).  Existing Sonin dilation covariance gives
(U_rL_a\subset L_{a/r}).  Equation `(4)` therefore turns every literal source object at aperture
(a) into a literal source object at aperture (a/r).

Apply the same argument with (r^{-1}).  The seed (D_{r^{-1}}g) is supported in
([ra,r/a]\subset[a/r,r/a]=[a/r,(a/r)^{-1}]), again because (r\ge1).  Hence
(U_r^*=U_{r^{-1}}) also sends every literal source object at (a) to one at (a/r).

The co-Poisson generator set contains each source vector and its cosine transform.  The cosine
involution satisfies

\[
 \mathcal F U_r=U_r^*\mathcal F.
\]

Thus both dilations preserve the full two-branch generator filtration, not only the positive
branch.  Linearity gives `(1)` on the algebraic spans.  Continuity of the unitary dilations and
closedness of (C_{a/r}) extend `(1)` to the closed source spaces.

Let (y\in Y_{a/r}) and (c\in C_a).  Using `(1)` and adjunction,

\[
 \langle U_ry,c\rangle=\langle y,U_r^*c\rangle=0,
 \qquad
 \langle U_r^*y,c\rangle=\langle y,U_rc\rangle=0.
\]

This proves `(2)`.

Finally let (x\in C_a^\perp).  Since (C_a\subset L_a), the Sonin projection (P_ax) also lies
in (C_a^\perp): for (c\in C_a),

\[
 \langle P_ax,c\rangle=\langle x,c\rangle=0.
\]

Hence (P_ax\in L_a\cap C_a^\perp=Y_a), while (x-P_ax\perp L_a), and therefore
(x-P_ax\perp Y_a).  Uniqueness of orthogonal projection gives (E_ax=P_ax).  Apply this to the
two vectors in `(2)` to obtain `(3)`.  `QED`

## Hostile audit

- This does not prove RH and does not balance the two aperture defects.  The remaining Sonin
  leakage is generally noncompact and can be nonzero.
- Dilation covariance of co-Poisson constructions belongs to Burnol's co-Poisson intertwining
  theory.  It is therefore `[LITERATURE]`, not new scientific knowledge.
- The Route-R delta is the quotient consequence `(3)`: the missing inverse–dagger landing cannot
  be blamed on, or repaired by, an additional co-Poisson source projection.  Its exact remaining
  carrier is the plain Sonin aperture leakage.
- Burnol completeness is not used.  The theorem is pre-divisor and holds on the whole quotient
  domain.

## Frontier change

Old target:

```text
first-trace edge -> co-Poisson source-error syzygy + aperture/dagger comparison
```

Reduced target:

```text
first-trace edge -> pure Sonin aperture-leakage Bockstein -> source inverse/dagger equality
```

The first arrow no longer needs a separate co-Poisson source-projection correction.  The next exact
question is whether the essential first-trace class is the principal symbol of this single Sonin
leakage operator in the source-normal completion.

## Lean status

Unconditional formalization is complete in:

- `RHTower/BurnolCoPoissonSourceDilation.lean`: literal seed covariance, both generator branches,
  and bilateral closed source-space covariance;
- `RHTower/BurnolCoPoissonQuotientDilationCollapse.lean`: bilateral source-orthogonal transport,
  quotient-to-Sonin projection collapse, and the two exact Route R bonding-map corollaries.

The headline formal endpoints are
`coPoissonQuotientForward_eq_soninProjection_of_mem_next` and
`coPoissonQuotientInverse_eq_soninProjection_of_mem_next`. They use no divisor, zero, critical-line,
completeness, growth, or dagger hypothesis.

## Sources

- J.-F. Burnol, *Entrelacement de co-Poisson*, Ann. Inst. Fourier 57 (2007), 525–602.
- J.-F. Burnol, *Two complete and minimal systems associated with the zeros of the Riemann zeta
  function*, J. Théorie des Nombres de Bordeaux 16 (2004), 65–94.
