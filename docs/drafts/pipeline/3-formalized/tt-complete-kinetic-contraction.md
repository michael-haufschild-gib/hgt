# TT C79 — Complete kinetic contraction source

Status: exact algebraic source representation formalized. Global source sign and RH remain open.
Parent: P1:tt-kinetic-contraction-source.

## Exact theorem

Write b=1/12-7h/72, r=s*(1-h²*b*s), V=9-r*h² and Z0=(1-h*b*s)/3.
There are fixed complete polynomials C(h,s,e), D(h,s) such that

 h20*reducedSlope(V,1/h,e*Z0)=h4*D(h,s)+(1-e)*C(h,s,e).

D is the existing exact reduced nonlinear-boundary core. This retains the
entire source at every nonzero complex clock, including V=0. The polynomial
identity `complete_kinetic_contraction` has no hypotheses. Nonzero h in its
source-value version is solely the coordinate inversion condition.

## Dependency-closed proof

1. Copy every literal square-moment monomial, clearing h^(n+1), for orders
   2,4,6,8,10. Prove both its value and full original Lie derivative.
2. Assemble the whole signed determinant and its h23 derivative transport.
3. Pull back v=9-r*h². Exact field conjugacy gives H=hD; D at zero clock
   retains -108r*d_r+36(3z-1)*d_z and kills r*(3z-1).
4. Every cleared moment of order>=4 is divisible by h. Their literal first
   coefficients are 12^7*3^6*(3z-1), 12^9*3^8*(3z-1), and
   12^11*3^10*(3z-1) at orders6,8,10. The resulting rank-one cancellation
   makes the complete minor h³*M. This is exact polynomial division.
5. The complete slope is h4*[(6-h)*D(M)+18h*(4-h)*(12+4h)*v*z*M].
6. The original slope drift factor descends through this division because
   v=9-r*h² is coprime to h. Polynomial cancellation proves the reduced
   source incidence through the drift seam, without a v≠0 premise.
7. Substitute the exact nonlinear-boundary parametrization and kinetic
   contraction. The e1 slice is h4*D. Polynomial division by 1-e gives C.

## Formal files and audit

Fifteen production leaves, prefix `ThetaCuspRatioKinetic`, in RHTower:
ClockMoment2/4/6/8/10, ClockAlgebra, ClockMoments, ClockMinor, ClockDefect,
ClockMomentJets, ClockMinorCore, ClockSlope, ClockSourceCore, ClockReduced,
Contraction. Every leaf passed direct `lake --old env lean -o ... FILE`;
all wired, no umbrella build. Imported174-theorem audit passed with only
propext, Classical.choice and Quot.sound. Capstone types checked.
Logs: /tmp/tt_c79_production_axioms.log; /tmp/tt_c79_*_production*.log.

Lint completed with11 unrelated umbrella omissions; no C79 omission or
forbidden declaration reported. No raised limits, added axioms, numerical
sampling or external coefficient arithmetic. Source transcription only;
algebra checked by Lean.

## Precise frontier

C>=0 on the finite-clock box is CONJECTURAL. No global sign, RH proof or
RH counterexample follows from this identity alone. Next attack: the full
mixed Bernstein sign, retaining every kinetic coefficient and lower clock
term. The paper kinetic-degree17 bound still needs formal source closure.
If a basis coefficient is negative, that alone is not a value counterexample.
