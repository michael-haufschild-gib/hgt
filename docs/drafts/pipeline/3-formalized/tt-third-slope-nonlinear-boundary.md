# Third-slope cubic contact after the nonlinear source barrier

- ID: tt-third-slope-nonlinear-boundary
- Parent: C73, tt-third-slope-nonlinear-cone
- Route: TT
- Stage: 3-formalized; ten production leaves audited and wired.
- Claim: on the cubic sheet B(h,r) below, the scaled third-slope polynomial
  has an exact factor h³, with leading coefficient 1944A−63Cr².
- This does not establish global positivity on the nonlinear source cone
  or the actual orbit, the fourth Schur gap, all-rank closure, or RH.

## Corpus basis and exact claim

C70 gives q>b(h), C71 shows a negative second transverse slope survives,
and C72 now proves q−Tq²>b(h) for every actual x>0. In compact coordinates,
C72 is t−h²t²>r*b(h). The cubic polynomial

    B(h,r)=r*(1/12−7h/72)+(r²/144)h²−(7r²/432)h³

agrees with the implicit boundary t−h²t²=r*b(h) through degree three.
It is a matching polynomial sheet; it is not asserted to lie exactly on
that implicit boundary for nonzero h.

Write P=scaledMinor, Q=scaledSlope, C=principalMass>0 and A=axisMinorMass>0.
The claim is

    Q(h,r,B(h,r))=h³ L_r(h),
    L_r(0)=1944A−63Cr²=63C*(122880/7−r²).

Thus fixed r has positive slope on a positive punctured neighborhood of
h=0 if r²<122880/7, and negative slope if the inequality is reversed.
No sign is claimed at equality. The actual kinetic range 0<r<361/25
lies on the positive side of this new threshold. This passes the next
necessary boundary test for C73; it does not prove its full cone sign.

## Dependency-closed derivation

Make the triangular change t=s+B(h,r), retaining the complete source
field. The transformed field is

    Fh=Hh(h,r,s+B), Fr=Hr(h,r,s+B),
    Fs=Ht(h,r,s+B)−B_h Fh−B_r Fr.

Its polynomial flow conjugacy follows from the product rule and the
three coordinate identities. On h=s=0 its needed derivatives are

    Fh=0, Fh_h=0, Fh_hh=−72, Fr=−108r,
    Fs=Fs_h=Fs_hh=0, Fs_hhh=−63r²/4.

For an independent check of the last identity, the coefficients of
h⁰,h¹,h²,h³ of the substituted original field are respectively

| Component | h⁰ | h¹ | h² | h³ |
|---|---:|---:|---:|---:|
| Hh | 0 | 0 | −36 | −12+3r |
| Hr | −108r | 72r | 24r+6r² | −3r² |
| Ht | −9r | 33r/2 | −3r/2−r² | −7r/6+r²/4 |

Subtract B_h Hh and B_r Hr coefficientwise. The first three coefficients
vanish; the cubic coefficient is −21r²/8. No transverse term is dropped.

Let P̃(h,r,s)=P(h,r,s+B). The exact moment identities give

    P̃0=P̃_h=0, P̃_hh=2A,
    P̃_hhh=C*(28160/9−7r²/12), P̃_s=12C.

The new third-minor identity is assembled from the first jets of moments
2,4,6, second jet of moment8 and third jet of moment10. Each is obtained
by symbolic differentiation of the existing split moment polynomials and
has a successful Lean audit. Its chain rule is

    P̃_hhh = affineJet3(P)+(r²/24)affineJet1(P_t)−(7r²/72)P_t.

Differentiate the h-jets in r: P̃_r=P̃_hr=P̃_hhr=0 and
P̃_hhhr=−7Cr/6. The cubic product rule now gives

    (flow F P̃)_hhh=−432A−63Cr².

The exact normalized slope identity is

    Q̃=(6−h)flow F P̃+(17h−66)L̃ P̃,

where L̃0=0 and L̃_h=−36. All lower slope jets vanish, while
Q̃_hhh=11664A−378Cr². Divide by 3! and factor the univariate polynomial
using its first three vanishing coefficients. Finally A/C=5120/9,
giving the displayed threshold and the two signs by continuity.

## Lean audit

Ten production leaves, `ThetaCuspRatioCubicJetAlgebra` through
`ThetaCuspRatioCubicSlopeBoundary`, passed final direct
`lake --old env lean` audits. All imports are wired in `RHTower.lean`;
no umbrella/full build. Twenty imported capstones passed the separate
`/tmp/TTC73ProductionAxioms.lean` audit with exactly `propext`,
`Classical.choice`, `Quot.sound`, and no added axiom or admitted proof.

Manifest: `/tmp/tt_c73_production_modules.txt`. Final logs:
`/tmp/tt_c73_final_*.log`; imported axiom log:
`/tmp/tt_c73_TTC73ProductionAxioms_pass1.log`. Index refresh exited0. Lint exited1 with fourteen unrelated umbrella
omissions and no C73 finding. Superseded ten scratch sources/caches cleaned. Global C73 remains open; joint polynomial normal form
and a uniform nonlinear-cone tail are the next proof targets.
