# TT — Global sign on the exact nonlinear boundary

- Route: TT; complete ratio-source third slope.
- Status: scratch proof kernel checked, production dependency audit in progress.
- Parent: `tt-third-slope-nonlinear-cone.md`.
- No source-sign, RH, or additional axiom premise is admitted.

For 0<h≤4/5, 0<r≤361/25, 9-r*h²>0, 0<t, h*t<1 and
`t-h²*t²=r*(1/12-7*h/72)`, the complete physical-source third slope is
strictly positive. These are the stated boundary domain constraints; they do
not supply the sign being proved.

The exact parameter coverage gives `t=b(h)*s`,
`r=s*(1-h²*b(h)*s)`, with `0<s<(6/5)*(361/25)`. The full reduced boundary
core is positive on the enclosing closed parameter rectangle. Its complete
tensor Bernstein reconstruction has 97 by 37 coefficients. Every coefficient
has a strictly positive rational certificate. The reconstruction, source
regularization, positive scale, and positive drift factor give the physical
source theorem without dropping a source term.

## Validation

All97 coefficient rows, the global core and the source transfer passed direct
`lake --old env lean` scratch audits. Each row has all37 individual signs and
its universal Fin37 theorem. All final capstones use only `propext`,
`Classical.choice`, `Quot.sound`. Source transfer audit3 repaired real/complex
casts; earlier unsuccessful audits are not evidence.

The dependency closure contains627 modules:45 affine-boundary modules,
7 regular-core modules and575 full coefficient/reconstruction/sign modules.
They are staged in
`formal/GaloisForLFunctions/RHTower/ThetaCusp/ThetaCuspRatioBoundaryCertificate/` and
wired into RHTower. Debug printing and scratch API examples were removed.
Their production module identities require serial direct leaf reaudits;
scratch caches were not renamed or copied. Manifest:
`/tmp/tt_c77_production_manifest.json`.

## Remaining hard problem

This theorem closes the exact boundary sign. Strict interior surplus positivity
is still open. It does not prove the full source quadratic, fourth Schur gap,
all-rank closure, or RH. No umbrella or full build is part of this audit.
