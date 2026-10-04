# Affine critical source cone does not determine the third slope

- **ID:** tt-third-slope-affine-cone (C71)
- **Stage:** 5-failed
- **Type:** FALSIFIED candidate; exact positive survivor formalized.
- **Route:** TT, actual global third-minor slope.
- **Statement:** The strict coarse cone, even supplemented by
  q>1/12−7/(72k), contains a negative third-slope point.

## What fails

C70 proves the added inequality on the actual modular source. It
does not imply the slope sign pointwise. This closes only that static
cone criterion. It does not falsify an actual-source statement or RH.

Let h=1/k, r=k²(9−V), t=k(1−3Z), b(h)=1/12−7h/72. The exact
regularized minor and slope are P=h¹⁷p and Q=h¹⁹S. Write
C=6²⁴·1990656·1679616>0 and A=6²⁴·24⁹·720>0.

## Dependency-closed proof and positive survivor [PROVED HERE]

Shift the transverse coordinate to s=t−r*b(h). Exact moment jets give

    P(0,r,r/12)=0,
    ∂h P(h,r,r*b(h))|₀=0,
    ∂h² P(h,r,r*b(h))|₀=2A−Cr²/6.

These are obtained from the full source moments, retaining all mixed
terms. In this shifted chart the conjugated vector field g satisfies

    g(0,r,0)=(0,−108r,0),
    ∂h g_h=∂h g_s=0,
    ∂h² g_s=−9r²/2,
    ∂s P=12C.

Differentiate the exact regularized slope identity

    Q=(6−h)H(P)+(17h−66)(Hh/h)P.

The zeroth and first h jets vanish. In the second jet of H(P), only
two terms survive: (−108r)∂r(2A−Cr²/6)=36Cr² and
(−9r²/2)·12C=−54Cr². Multiplication by six yields
∂h²Q=−108Cr². Also ∂sQ=7776C, from the exact critical-face identity
Q(0,r,t)=−648C(r−12t).

Now displace quadratically: t=r*b(h)+a*h². The full second jet is
108C(144a−r²). Polynomial division by h twice gives an exact factor

    Q(h,r,r*b(h)+a*h²)=h² B_(r,a)(h),
    B_(r,a)(0)=54C(144a−r²).

Continuity proves a strict positive slope for all sufficiently small
positive h when r²<144a, and a strict negative slope when 144a<r².
No sign is asserted at equality. This exact second transverse sign
classification is the nontrivial positive survivor, not a restatement
of the failed cone claim.

For the counterexample take r=1, a=1/288. Then t>b(h), while the slope
is negative for sufficiently small positive h. Set V=9−h², K=1/h,
Z=(1−th)/3. All coarse inequalities hold strictly: V tends to 9 from
below, K diverges, Z tends to 1/3 from below, K²(9−V)=1<361/25, and
the exact velocity polynomial tends to 1/2>0. Moreover
(1−3Z)/(K(9−V))=t>b(h). This gives the unconditional existential
counterexample to the strengthened static criterion.

## New mathematical question

The candidate source invariant q−Tq²>b(h), T=r*h², matches the new
threshold to leading order: substituting t=r*b(h)+a*h² gives leading
coefficient a/r−r/144. Its global actual-source proof remains open.
The normalized defect z=(q−b)/T−q² has an exact candidate evolution
z′=(k/u)([A₁(1−2Tq)+2V]z+R), where A₁ is C70's rate polynomial.
C70 supplies z≥−q², so a negative-tail escape can be excluded without
assuming boundedness of a new rescaled remainder. The hard remaining
step is an inward forcing law at R=0 while z≤0. This is not yet proved.

## Lean certificate

Seven production leaves under `formal/GaloisForLFunctions/RHTower/`:
`ThetaCuspRatioCriticalSecondJets`, `ThetaCuspRatioCriticalMinorSecondJet`,
`ThetaCuspRatioAffineCriticalFlow`, `ThetaCuspRatioAffineSlopeSecondJet`,
`ThetaCuspRatioAffineSlopeBoundary`, `ThetaCuspRatioQuadraticSlopeBoundary`,
`ThetaCuspRatioAffineConeObstruction`.

Capstones in `HTGeometry.ThetaRatioInfinity`:
`affineMinor_second`, `affineSlope_second`, `quadraticSlopeCore_zero`,
`quadraticSlope_sign`, `exists_affineCone_negative_slope`.
All seven passed serial foreground `lake env lean` leaf audits;
no full/umbrella builds, external coefficient arithmetic, or raised
heartbeat limits. All are wired into `RHTower.lean`. Imported type/axiom audit of eleven capstones passed: only `propext`,
`Classical.choice`, `Quot.sound`. Logs: `/tmp/tt_c71_prod_*.log`,
`/tmp/tt_c71_production_axioms.log`. Index passed. Lint exit 1 solely from twelve unrelated missing umbrella imports;
no C71 finding. Full log: `/tmp/tt_c71_lint.log`.

## Log

- 2026-10-04 — Affine cone criterion falsified; exact second transverse
  classification proved and formalized. Actual global slope remains open.
