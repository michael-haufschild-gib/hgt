# Odd-contact null-flag source landing (2026-08-12)

Formalized in `RHTower/XiShiftedCanonicalAdmissionDegreeCenteredArithmeticSource.lean`.

## Exact law
For monic null polynomial `P`, parity lift `A=P*X^m`, and shifted-Xi Pade defects vanishing below `2*n+(2*m+1)`,
[
\widehat T_{w,n+m}(A)=2(A.nextCoeff)^2\Delta_{2n+2m+1}(w^2;P).
]
Riccati square completion vanishes on complete visible null flag. No inverse-Hankel quotient or head PosDef hypothesis is used on plateau.

At genuine two-sided crossing with `0<w^2<41/2`, same `m` is contact lift, PSD plateau length, and first failing extension. First odd defect equals strictly negative completed prime-Gamma shifted square `S=L(X*A^2)<0`; producer is `2(A.nextCoeff)^2*S <= 0`, strict if `A.nextCoeff != 0`.

## New capstones
- `xiShiftedRiccatiCompletedDegreeCenteredArithmeticSource_liftedNull_eq_firstOddDefect`
- `xiShiftedTraceCoupledRiccatiCompletedSource_liftedNull_eq_sq_mul_firstOddDefect`
- `exists_liftedNull_traceCoupledRiccatiCompletedSource_landing_of_genuine_crossing`

Targeted build passed 11797/11797. Axiom audit: only propext, Classical.choice, Quot.sound.

## Higher principle / residual
Contact order, local flat plateau length, first indefinite extension, and arithmetic landing index are one invariant. Generic plateau exclusion is false. Remaining exact route burden: exclude trace-zero barycenter degeneracy or build nondegenerate positive completion; relate local flat contact to global terminal-frontier plateaus; prove quantitative frontier separation outrunning parabolic envelope. RH not proved.