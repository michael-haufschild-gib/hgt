# Narrow-sector tied-power transport does not orient a flat Hankel face

- **ID:** `mass-shifted-tied-power-sector-orientation-no-go`
- **Stage:** 3 — formalized in Lean 4
- **Type:** EXACT COUNTERMODEL / POSITIVE-SURVIVOR CLASSIFICATION
- **Status:** `[LEAN-PROVED] [FALSIFIED] [NOVELTY UNVERIFIED] [NOT RH]`
- **Source:** `docs/reports/mass-shifted-spectral-trace-route.md` · §9.3 Exact open core

## Killed conjecture

The earlier arbitrary signed-weight transport no-go might be irrelevant to Xi because shifted Xi
moments have the tied-power form

\[
 s_k=\Re\sum_j z_j^{k+1},
 \qquad z_j(h)=\frac{z_j}{1+h z_j},
\]

with conjugation-stable atoms in a narrow sector around the positive real axis.  Conjecture:
these additional local source constraints orient the first unseen flat-Hankel extension.

**Verdict:** `[FALSIFIED]`.

## Exact countermodel

Define two four-atom clouds

\[
 Z_+=\{11,9,10+i,10-i\},
 \qquad
 Z_-=\{11+i,9+i,9-i,11-i\}.
\]

Both are conjugation-stable.  Every atom has positive real part and satisfies the strict squared
Xi endpoint cone

\[
 84^2|z|^2<85^2(\Re z)^2.
\]

Let

\[
 s_k^\pm=\Re\sum_{z\in Z_\pm}z^{k+1}.
\]

Binomial expansion gives

\[
 (s_0^+,s_1^+,s_2^+,s_3^+)=(40,400,4000,40004),
\]

\[
 (s_0^-,s_1^-,s_2^-,s_3^-)=(40,400,4000,39984).
\]

Hence both sources have the same positive head `[40]`, the same singular size-two Hankel face

\[
 \begin{pmatrix}40&400\\400&4000\end{pmatrix},
\]

and the same monic null polynomial `p(X)=X-10`, represented by `c=(-10,1)`.  Their projective
extension coordinates are nevertheless

\[
 R_+=L_+(X^2p)=s_3^+-10s_2^+=4,
 \qquad
 R_-=L_-(X^2p)=s_3^--10s_2^-=-16.
\]

The source evolution is not artificial.  For every complex atom and every `k`,

\[
 f_{z,k}(h)=\left(\frac z{1+hz}\right)^{k+1}
\]

obeys the exact complex mass-shift law

\[
 f'_{z,k}(0)=-(k+1)z^{k+2}.
\]

Summing over either cloud gives the complete tied-power moment hierarchy.  Thus conjugation,
narrow-sector control, weight=node tying, and exact Möbius transport coexist with both outgoing
orientations on one fixed positive singular face.

The magnitude constraint is not an escape.  Rescale both clouds by `1/256`:

\[
 \widetilde Z_\pm=\frac1{256}Z_\pm.
\]

Every atom then satisfies both exact corpus inequalities

\[
 84^2|z|^2<85^2(\Re z)^2,
 \qquad 41^2|z|^2<4,
\]

the second being `|z|<2/41`.  Both rescaled sources share the same positive singular face with
monic null polynomial `X-5/128`, while their remainders are

\[
 \widetilde R_+=2^{-30}>0,
 \qquad
 \widetilde R_-=-2^{-28}<0.
\]

Thus the countermodel satisfies the full local sector-and-radius geometry used for centered Xi
reciprocal-square atoms, not only a qualitative right-half-plane condition.

## Proof

Write the positive cloud as `10+w` with `w∈{1,-1,i,-i}` and the negative cloud as
`10+w` with `w∈{1+i,-1+i,-1-i,1-i}`.  In both clouds

\[
 \sum w=\sum w^2=\sum w^3=0.
\]

For the positive cloud `w^4=1` atomwise, so `sum w^4=4`; for the negative cloud
`w^4=-4` atomwise, so `sum w^4=-16`.  The displayed power sums follow from the binomial theorem.
The Hankel and remainder claims are then direct substitutions.  Sector inequalities reduce to
the eight strict integer inequalities after `|z|^2=(Re z)^2+(Im z)^2`.

For transport, differentiate the quotient at `h=0` and apply the power rule:

\[
 \frac d{dh}\left(\frac z{1+hz}\right)^{k+1}_{h=0}
 =(k+1)z^k(-z^2)=-(k+1)z^{k+2}.
\]

Every step is exact; no asymptotic or numerical experiment enters. `square`

## Positive survivor and representation lesson

The no-go does not say the completed Xi source is arbitrary.  It classifies what cannot supply
the missing constitutive law:

> No theorem using only finite tied-power form, conjugation symmetry, the corpus endpoint sector,
> exact mass-shift recurrence, and current-face positivity can orient the first unseen extension.

The global source incidence omitted by this model is precisely that all atoms arise from one
completed entire Xi function with its normalized Gamma and Euler source identities.  Therefore
`docs/notes.md` is useful only in its source-conditioned **joint**-realizability sense: local
spectral and transport marginals still form a product large enough to contain both signs.

## Literature audit

Current moment-problem literature treats positive representing measures, flat extensions, and
degenerate Hankel extensions.  It does not supply a source-dynamic orientation theorem for these
complex tied-power clouds.  Closest audited sources are Malik Amir's 2026 `K`-moment survey and
Bolotnikov's degenerate Hamburger extension classification.  This elementary no-go is recorded as
`[NOVELTY UNVERIFIED]`, not as a priority claim.

## Lean certificate

- Module: `GaloisForLFunctions.HTGeometry.TiedPowerSectorOrientationNoGo`
- Endpoint-scale module: `GaloisForLFunctions.HTGeometry.TiedPowerEndpointOrientationNoGo`
- Capstones: `HTGeometry.tiedPowerNarrowSectorOrientationNoGo` and
  `HTGeometry.tiedPowerEndpointOrientationNoGo`
- Supporting tied-power moment, conjugation, sector, face, remainder, and Möbius-derivative
  theorems are all unconditional.

## Log

- 2026-08-09 — tied-weight conjecture formed from `docs/notes.md` and the first-unseen tangent law.
- 2026-08-09 — conjecture falsified by two explicit conjugation-stable narrow-sector clouds;
  dependency-closed paper proof completed.
- 2026-08-09 — exact no-go and complete complex Möbius hierarchy formalized; direct Lean check
  passed and module was wired into `GaloisForLFunctions.HTGeometry`.
- 2026-08-09 — strengthened to exact `2/41` radius as well as `85/84` sector; endpoint-scaled
  opposite remainders and complete closed capstone formalized.
- 2026-08-09 — targeted `lake build` passed for both modules.  `#print axioms` reports only
  `propext`, `Classical.choice`, and `Quot.sound`.  Repository lint reaches both modules through
  the HTGeometry umbrella; its nonzero exit is caused solely by concurrently added unrelated
  RHTower/HTGeometry modules not yet wired into their umbrellas.
