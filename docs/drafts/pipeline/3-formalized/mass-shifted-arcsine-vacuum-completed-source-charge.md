# Mass-shifted arcsine-vacuum completed source charge

- **ID:** `mass-shifted-arcsine-vacuum-completed-source-charge`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `docs/reports/mass-shifted-spectral-trace-route.md` §9.3 exact open core
- **Statement:** Full arcsine vacuum can be subtracted inside current completed adaptive source, before division by newborn norm; resulting charge vanishes on arcsine vacuum, has exact signed adjacent-degree innovation, and extends as finite positive literal arithmetic source through every occupied strict frontier.

## Goal

Replace singular Christoffel wall reporter by admission-sensitive arithmetic producer itself.  No
orientation map, fixed linear reporter, posterior quotient, or reflection aggregation may enter
source formation.

## Gates

- [x] 0 → 1: pole-free source conjecture isolated
- [x] 1 → 2: literal source identity, Jacobi charge, innovation, vacuum, and boundary proofs closed
- [x] 2 → 3: unconditional Lean module direct-checked, targeted-built, umbrella-wired, axiom-audited
- [ ] 3 → 4: publication-ready; degree-uniform mixed mass--innovation estimate remains open

## Exact source law

Let

\[
 V_n=n+\frac38,
 \qquad
 \mathfrak C_n(y)=2\mathcal S_n(y)-32V_nN_{n+1}(y),                 \tag{1}
\]

where `S_n` is current canonical adaptive shear and `N_(n+1)` is current newborn admitted norm.
At square mass `y=w²`, exact completed source identity is

\[
 \boxed{
 \mathfrak C_n(w^2)
 =\mathcal A_{w}^{\sharp,\mathrm{mix}}(P_{n,w})-32V_nN_{n+1}(w^2).}
                                                                    \tag{2}
\]

Thus source is current admitted mixed rational--Gamma-minus-von-Mangoldt `P^sharp` aggregate;
vacuum subtraction occurs inside source before any newborn division.

After normalized admission, covariant charge is

\[
 \boxed{
 J_n(s)=E_n(s)-16V_n\beta_{n+1}(s).}                                \tag{3}
\]

Whenever current Christoffel scale is nonzero, this equals scale times signed wall deviation
`D_n`; on every coordinate-dilated arcsine tower it is identically zero, and for shifted Xi it
tends to zero at every fixed degree.

## Exact degree innovation

Define `I_n=J_(n+1)-J_n`.  Writing `alpha_j`, `beta_j` for current Jacobi coordinates,

\[
\begin{aligned}
 I_n={}&(\alpha_{n+1}-\alpha_n)\sum_{j<n}\alpha_j
 +\alpha_n\alpha_{n+1}-n\alpha_n^2+(n+2)\alpha_{n+1}^2\\
 &+(1-n)\beta_n+(16n+7)\beta_{n+1}-(15n+20)\beta_{n+2}.             \tag{4}
\end{aligned}
\]

Newborn denominator removal makes degree transport exactly additive:

\[
 \boxed{J_{n+k}=J_n+\sum_{j<k}I_{n+j}.}                             \tag{5}
\]

Negative newest-edge coefficient in (4) proves centered source is intrinsically signed.  Static
positivity/action conjecture is false at algebraic level; global theorem must control cumulative
mixed mass--degree innovations.

## Strict-frontier continuation

At every occupied strict frontier `y=tau_(n+1)`, corpus gives

\[
 N_{n+2}(y)=0,
 \qquad
 \mathcal S_{n+1}(y)>0.
\]

Therefore

\[
 \boxed{
 \mathfrak C_{n+1}(y)=2\mathcal S_{n+1}(y)>0.}                      \tag{6}
\]

The charge is continuous at `y`, hence positive on a right germ.  Divergent Christoffel wall is
only `C/(32N)` in positive chamber: pole belongs to posterior reporting quotient, not arithmetic
source.

## Conjecture → proof/fail loop

1. **Raw walls form positive trace. Failed:** universal dimension tax forces divergence.
2. **Subtract newborn observer defect. Failed:** visible arcsine Gauss vacuum still grows linearly.
3. **Full centered wall is positive action. Failed:** exact innovation (4) has negative newest-edge
   coefficient and no universal static sign.
4. **Pole is source-intrinsic. Failed sharply:** (2) and (6) prove source charge is finite,
   continuous, and positive through strict contact.
5. **Positive survivor:** pole-free completed source charge with exact additive degree innovation.
   Remaining obstruction is one degree-uniform mixed mass--innovation estimate, not producer or
   local-contact construction.

## Novelty audit

Corpus search found no prior arcsine-vacuum completed source charge or exact innovation (4).
Classical Jacobi sum rules such as [Killip--Simon](https://arxiv.org/abs/math-ph/0112008),
generalized-Jacobi recurrence asymptotics such as
[Vanlessen](https://arxiv.org/abs/math/0212014), and Xi orthogonal expansions such as
[Romik](https://arxiv.org/abs/1902.06330) do not contain current admission-selected
rational--Gamma/von-Mangoldt source, its newborn-vacuum subtraction, or strict-frontier identity
(6).  Route-specific novelty remains `[NOVELTY UNVERIFIED]` pending publication review.

## Lean certificate

Module:

`formal/GaloisForLFunctions/RHTower/XiShiftedArcsineVacuumCompletedSourceCharge.lean`

Principal declarations:

- `arcsineVacuumRenormalizedRelativeArithmeticSource_eq_jacobiCharge`
- `arcsineVacuumRenormalizedJacobiDegreeInnovation_eq`
- `arcsineVacuumRenormalizedJacobiCharge_add_eq_sum_innovations`
- `coordinateDilated_arcsineVacuumRenormalizedRelativeArithmeticSource_eq_zero`
- `xiShiftedCanonicalAdmissionArcsineVacuumCompletedSourceCharge_eq_literal`
- `xiShiftedCanonicalAdmissionArcsineVacuumCompletedSourceCharge_pos_at_strict_frontier`
- `continuousAt_xiShiftedCanonicalAdmissionArcsineVacuumCompletedSourceCharge_at_strict_frontier`
- `xiShiftedStrictFrontier_literalArcsineVacuumCompletedSourceCharge_pos`

Verification:

- direct `lake env lean` passes;
- targeted module build passes;
- eight principal axiom checks report only `propext`, `Classical.choice`, `Quot.sound`;
- no `sorry`, `admit`, `axiom`, `opaque`, or `unsafe` declaration occurs;
- module is imported by `RHTower.lean`.

## RH impact

Missing producer now exists at exact requested type and local pole is removed.  RH is not proved.
Remaining theorem is sharply reduced:

> Along false-RH cofinal strict frontiers, show cumulative mixed mass--degree innovations in (5)
> cannot sustain infinitely many positive boundary charges (6) while normalized fixed-degree
> charges recede to zero.

Fixed-mass admission transgression is an exact endpoint cocycle and cannot supply this estimate.
Required object must couple mass evolution and degree renewal.

## Log

- 2026-08-13 — conjectured pole-free source, proved literal/Jacobi/contact laws, derived exact signed degree innovation, formalized and audited

