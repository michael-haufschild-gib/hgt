# Standard Cheeger middle extension as arithmetic Hodge domain

- **ID:** `deninger-standard-cheeger-middle-extension-as-arithmetic-domain`
- **Stage:** 5-failed
- **Type:** NO-GO WITH POSITIVE SURVIVOR
- **Label:** `DAC_STANDARD_CHEEGER_MIDDLE_EXTENSION_ARITHMETIC_NO_GO`
- **Parent:** `deninger-derived-coefficient-hilbert-hodge-descent`
- **Claim tested:** use the ordinary unweighted \(L^2\) Cheeger
  ideal-boundary domain on the real-oriented compactification of every
  arithmetic log collar and identify its de Rham complex with
  Deninger's Rost--Schmid/residue coefficient.

## Local Witt audit

At a finite log-toric stage,
\[
 \overline Z_{L,v}
 \cong
 \operatorname{Hom}(\ker\lambda_v,\mathbb C^\times)
 \times\mathbb C_z ,
 \qquad D_{L,v}=(z=0).
\]
Holding the tangential character fixed, the real oriented normal
blow-up has link \(S^1\).  The link dimension is odd, so this stratum
is Witt in the sense of Albin--Leichtnam--Mazzeo--Piazza.  The same
holds for the real stationary product germ: its normal quotient is
\(\mathbb R^2/\{\pm1\}\), whose link is again a circle.

Thus no non-Witt middle-link Lagrangian is needed locally.  For a
suitably scaled incomplete-edge metric, the minimal and maximal
unweighted \(L^2\) de Rham domains agree at these normal strata.

## No-go theorem

`[PROVED HERE] [DAC_STANDARD_CHEEGER_MIDDLE_EXTENSION_ARITHMETIC_NO_GO]`

The resulting canonical unweighted \(L^2\) middle extension cannot be
Deninger's arithmetic coefficient with its finite-place residue
differential.

### Proof

On a punctured normal disc write \(z=re^{i\theta}\).  For every
oriented conformal metric in real dimension two, the \(L^2\)-density
of a one-form is conformally invariant.  Hence it is enough to use the
Euclidean metric.  Then
\[
 d\log z=\frac{dr}{r}+i\,d\theta
\]
has
\[
 \int_{0<|z|<\epsilon}|d\log z|^2\,d\operatorname{vol}
 =
 4\pi\int_0^\epsilon\frac{dr}{r}
 =
 \infty.                                                        \tag{1}
\]
More generally, a smooth logarithmic one-form with nonzero Poincaré
residue has a nonzero \(d\log z\) leading coefficient, so `(1)` shows
that it is not in the unweighted \(L^2\) domain.  Consequently
Poincaré residue vanishes on the logarithmic part admitted by that
domain.

By `DAC_PRO_LOG_STEIN_KUMMER_RESIDUE_SQUARE`, however,
\[
 \operatorname{Res}_v(d\log\chi^a)=v(a),
\]
and nonzero valuations are load-bearing in the source
Rost--Schmid differential.  The ordinary Cheeger middle extension
therefore kills a source Kummer generator on which the arithmetic
coefficient has nonzero boundary.  It cannot be cohomologically
faithful or residue-compatible.

## Strongest positive survivor

The real-oriented log collar is conformal to a cylindrical
\(b\)-metric.  The logarithmic generator is not \(L^2\), but it is an
**extended** unweighted \(L^2\) form:
\[
 d\log z\in\bigcap_{\epsilon>0}x^{-\epsilon}L^2
 \setminus L^2,\qquad x=|z|.                                  \tag{2}
\]
Hunsicker's extended Hodge theory for fibred cusp/cylindrical ends
identifies such leading coefficients as boundary data and proves that
the resulting boundary-data image is Lagrangian for the Green form.
The exact source survivor is therefore an extended
Calderón/Green domain, not ordinary middle-extension \(L^2\).

This survivor is developed in
`DAC_ARITHMETIC_EXTENDED_CUSP_HODGE_BOUNDARY` and
`DAC_KUMMER_RELATIVE_CALDERON_POISSON_DOMAIN`.

## Hostile audit

- The no-go does not reject Cheeger ideal boundary conditions in their
  stated compact stratified setting.
- Odd link dimension really makes the local arithmetic normal strata
  Witt; adding an arbitrary mezzoperversity would be noncanonical.
- Failure is residue faithfulness, not local self-adjointness.
- A decaying coefficient metric could make \(d\log z\) square
  integrable, but it would define a different weighted/rigged theory
  and must prove power, cup, and residue compatibility.
- No zeta zero, RH premise, CCM object, or numerical computation is
  used.

## References

- Pierre Albin, Eric Leichtnam, Rafe Mazzeo, Paolo Piazza,
  *Hodge theory on Cheeger spaces*, arXiv:1307.5473.
- Eugenie Hunsicker, *Extended Hodge Theory for Fibred Cusp
  Manifolds*, arXiv:1408.3257.
- `DAC_PRO_LOG_STEIN_KUMMER_RESIDUE_SQUARE`.
- `DAC_PRO_LOG_KUMMER_CUSP_HODGE_EXTENSION`.

## Log

- 2026-07-27 — Audited the exact Witt criterion and proved that
  standard unweighted middle extension deletes every nonzero
  logarithmic residue.  Retained extended \(L^2\) Green boundary data
  as the positive survivor.
