# Prime/Gamma Stokes-wall Xi Malgrange correction curvature

- **ID:** route-p-prime-gamma-wall-xi-malgrange-correction-curvature
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Labels:** `[PROVED HERE]` `[CANDIDATE NEW SCIENTIFIC KNOWLEDGE]` `[IRREGULAR-RH]` `[POSITIVE-SURVIVOR]`
- **Source:** exact prime/Gamma Stokes-wall Fredholm tau and canonical completed-Xi seam germ
- **Statement:** First-jet normalization forces the logarithmic Malgrange correction to have curvature `2c²(P_wall(d)-P_Xi)`; this curvature has strictly positive real part for every `d ≥ 1` and throughout a punctured right neighborhood of the wild wall.

## Goal

Extract strongest positive rigidity law exposed by scalar prime/Gamma wall no-go. Any viable irregular-Riemann--Hilbert realization must add a genuine even Stokes correction; scalar irregular-time rescaling cannot absorb it.

## Gates

- [x] 0 → 1  in-progress: well-posed, source/target provenance explicit, attack idea fixed
- [x] 1 → 2  fully-proven: complete algebraic paper proof, `[PROVED HERE]`, no open dependency
- [ ] 2 → 3  formalized: Lean theorem, targeted check, new declarations axiom-audited
- [ ] 3 → 4  publication-ready: standalone paper and novelty review

## Exact theorem

Put

`c_Xi = normalizedPrimeArchMoment(0)/2`,

`L_d(z) = log D_d(c_Xi z)`, and

`A_d(z) = canonicalXiSeamLog(z) - L_d(z)`.

For every `d>0`,

`A_d(0)=0`, `A_d'(0)=0`, and

`A_d''(0) = 2 c_Xi² (P_wall(d)-P_Xi)`.

Consequently `Re A_d''(0)>0` for every `d≥1`, and eventually as `d→0+`.

## Frontier and literature audit

- Corpus contains wall/Xi projective mismatch and scalar-rescaling no-go, but no canonical correction germ or exact curvature law.
- Bertola's Malgrange-form/Fredholm construction identifies tau functions as local analytic sections and explains normalization non-uniqueness; it does not compute this prime-log/Xi correction jet: <https://arxiv.org/abs/1703.00046>.
- Isomonodromic moment/Fredholm determinant work realizes tau functions and solvability divisors, but does not contain this arithmetic Stokes anomaly: <https://arxiv.org/abs/0805.0446>.
- Recent `q`-Painlevé Fredholm-tau constructions give determinant and connection formulas, not the completed-Xi first-jet-normalized curvature defect: <https://arxiv.org/abs/2501.01419> and <https://arxiv.org/abs/2608.03345>.
- Search found no exact formula or sign theorem for this prime/Gamma wall correction. Audit result only; no priority claim.

## Hostile audit

- **Circularity:** none. Uses closed Xi moment bounds and exact Fredholm coefficients, not RH or target zero locations.
- **Normalization:** `c_Xi` is forced by first-jet equality because positive-aperture wall coefficient one is exactly `1`.
- **Branch issue:** both tau germs equal `1` at zero; existing local complex-log derivative theorems apply on the slit-plane neighborhood.
- **Gauge issue:** constant multiplicative tau gauges disappear after logarithmic differentiation; scalar time gauge is fixed by first jet.
- **Sign issue:** `c_Xi>0`; `P_Xi<9/80`; `P_wall(d)>9/80` on proved regions.
- **Global-monotonicity loophole:** no monotonicity of pair coherence is asserted or used.
- **Verdict:** `SURVIVES PRELIMINARY ATTACK`.

## Dependency-closed paper proof

For `d>0`, the normalized one-label Fredholm coefficient is `a₁(d)=1`. Therefore

`L_d'(0)=c_Xi a₁(d)=normalizedPrimeArchMoment(0)/2`

equals `canonicalXiSeamLog'(0)`, proving `A_d'(0)=0`. Both logarithms vanish at zero, so `A_d(0)=0`.

Write `a₂(d)` for the two-label Fredholm coefficient. Existing logarithmic differentiation gives

`L_d''(0)=c_Xi²(2a₂(d)-a₁(d)²)`.

By definition

`P_wall(d)=(a₁(d)²-2a₂(d))/(2a₁(d)²)`;

because `a₁(d)=1`, this is `L_d''(0)=-2c_Xi²P_wall(d)`.

For Xi,

`canonicalXiSeamLog''(0)=-normalizedPrimeArchMoment(1)/2`

and

`P_Xi=normalizedPrimeArchMoment(1)/normalizedPrimeArchMoment(0)²`.

Since `c_Xi=normalizedPrimeArchMoment(0)/2`, Xi curvature is `-2c_Xi²P_Xi`. Subtraction yields

`A_d''(0)=2c_Xi²(P_wall(d)-P_Xi)`.

Now `c_Xi>0` and `P_Xi<9/80`. The explicit cold theorem gives `Re P_wall(d)>9/80` for all `d≥1`, hence `Re A_d''(0)>0`. The wild-wall boundary theorem gives the same wall inequality eventually in `d→0+`, hence the punctured-collar conclusion. ∎

## Positive-survivor meaning

- **Exact mechanism:** scalar normalization fixes odd first jet but leaves unavoidable positive even curvature.
- **Strongest positive survivor:** canonical first-jet-flat correction germ with exact projective-defect curvature.
- **New insight:** viable Xi realization must alter even Stokes/Malgrange data; scalar clock change and constant tau gauge are insufficient.
- **Next live core:** construct this positive-curvature anomaly from independent prime--Gamma microlocal data, then prove its full Fredholm coefficient law.

## Log

- 2026-08-25 — formed after rejecting unsupported global coherence monotonicity.
- 2026-08-25 — external prior-art audit found general Malgrange/Fredholm mechanisms but no arithmetic correction-curvature law.
- 2026-08-25 — promoted to 2-fully-proven after normalization, branch, sign, and circularity audits closed.
