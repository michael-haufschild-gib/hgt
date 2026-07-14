# Critical Möbius Fisher--Stein contact law

- **ID:** `mobius-critical-fisher-stein-contact-law`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) / source-side Hilbert--Pólya bridge
- **Scientific status:** `[PROVED] [BRIDGE] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Lean module:**
  `formal/GaloisForLFunctions/RHTower/MobiusCriticalFisherSteinContact.lean`
- **Parent:** `../infinite-mobius-critical-boundary-layer-product.md`

## Theorem

The normalized positive squarefree-Möbius channel has the critical logarithmic boundary density

\[
\rho(y)=e^{-y}\mathbf 1_{y>0}.
\]

Its canonical centered half-density score is

\[
s(y)=1-y.
\]

The exact moment identities are

\[
\int_0^\infty y^n\rho(y)\,dy=n!,
\qquad
\int_0^\infty s(y)\rho(y)\,dy=0,
\qquad
\int_0^\infty s(y)^2\rho(y)\,dy=1.
\]

Consequently the completed score has the four-unit energy

\[
\int_0^\infty \lvert 2s(y)\rvert^2\rho(y)\,dy=4.
\tag{1}
\]

For `u>=0`, the score Laplace transform is

\[
S(u)=\int_0^\infty (1-y)e^{-(1+u)y}\,dy
    =\frac{u}{(1+u)^2}.
\tag{2}
\]

It obeys the exact contact identity

\[
(1+u)S(u)+\frac1{1+u}=1.
\tag{3}
\]

Equivalently, after extension by zero to the negative half-line,

\[
(D+1)\big((1-y)e^{-y}\mathbf 1_{y>0}\big)
  +e^{-y}\mathbf 1_{y>0}=\delta_0
\tag{4}
\]

as a distribution.  The formal theorem proves `(3)` through the actual Laplace integrals; `(4)` is
its standard injective-Laplace interpretation and is not used as a formal distribution interface.

Let

\[
B_\sigma(u)
=\frac{\sum_n\mu(n)^2n^{-\sigma-u(\sigma-1)}}
       {\sum_n\mu(n)^2n^{-\sigma}}
\]

be the positive boundary-layer transform and let

\[
\tau_\sigma(x)
=\frac{\zeta(2\sigma)}
       {\zeta(\sigma)\zeta(\sigma+\pi x)},
\qquad
x_\sigma(u)=\frac{u(\sigma-1)}{\pi}.
\]

Then the actual all-prime channel satisfies

\[
\frac{\tau_\sigma(x_\sigma(u))}{(\sigma-1)^2}S(u)
 +\zeta(2)B_\sigma(u)
\longrightarrow \zeta(2)
\qquad(\sigma\to1^+).
\tag{5}
\]

Thus the signed Möbius response converts the centered escaped score into the boundary-minus-bulk
term, while the positive escaped density cancels the bulk and leaves one contact channel.

## Proof

The factorial moments follow from the Gamma integral

\[
\int_0^\infty y^n e^{-cy}\,dy=\frac{n!}{c^{n+1}}
\qquad(c>0).
\]

The mean, score energy, and `(1)` are the cases `n=0,1,2` after expanding `1-y` and
`(1-y)^2`.  Setting `c=1+u` gives `(2)`, and `(3)` is a rational identity.

The existing critical boundary-layer theorem gives

\[
B_\sigma(u)\longrightarrow\frac1{1+u},
\qquad
\frac{\tau_\sigma(x_\sigma(u))}{(\sigma-1)^2}
\longrightarrow\zeta(2)(1+u).
\]

Substitution of `(2)` and `(3)` gives `(5)`.

## Hilbert--Pólya contribution

The theorem identifies the boundary object which the coupled floor--Möbius construction must
transport:

```text
positive squarefree mass
  + centered logarithmic score
  + reciprocal signed Möbius response
  -> one endpoint contact channel
  -> completion factor 2
  -> four-unit incoming boundary budget.
```

This is stronger than the exponential mass-escape law alone: the tangent and its contact anomaly
are now fixed canonically, and the signed and positive critical responses are coupled in one exact
limit.  It also explains why a bulk-only estimate misses the required boundary term.

It does **not** prove that the contact channel is sent contractively to Suzuki's divisor profile
`ell_E`, and it does not prove the sign of the Hedenmalm pointed-moment Bezoutian.  Equality of the
completed score energy with the Euler-pole norm is an exact budget match, not an identification of
the two vectors.

## Formal theorem surface

- `integral_Ioi_pow_mul_mobiusCriticalExponentialDensity`;
- `integral_Ioi_mobiusCriticalExponentialScore_mul_density`;
- `integral_Ioi_mobiusCriticalExponentialScore_sq_mul_density`;
- `integral_Ioi_completedMobiusCriticalExponentialScore_energy`;
- `ofReal_integral_mobiusCriticalExponentialScore_eq_scoreLaplace`;
- `mobiusCriticalBoundaryScore_contact`;
- `tendsto_mobiusCriticalBoundaryScore_contact`.

The direct module build succeeds without placeholders or project axioms.

## Open core

`[OPEN CORE]` Construct, from the completed Euler--Gamma source and before reading the Xi divisor,
a closed nonexpansive continuation which sends the contact channel in `(5)` to the distinguished
anti-causal Xi boundary profile.  Equivalently, prove that the floor-discrepancy branch supplies
the bulk cancellation in the same graph norm in which the Möbius score produces the endpoint
contact, and that the resulting boundary vector is `ell_E`.

Only that source-to-divisor orientation theorem would convert `(1)` into
`C_E(0,0)<=4` and hence RH.

## Gates

- [x] critical score identified canonically
- [x] centeredness and unit Fisher energy proved
- [x] exact four-unit completed energy proved
- [x] score Laplace transform proved
- [x] signed-score plus positive-density contact identity proved
- [x] actual all-prime critical contact limit proved
- [ ] closed archimedean graph realization of the contact identity
- [ ] source-defined contact-to-divisor contraction
- [ ] Hedenmalm Bezoutian orientation
- [ ] RH
