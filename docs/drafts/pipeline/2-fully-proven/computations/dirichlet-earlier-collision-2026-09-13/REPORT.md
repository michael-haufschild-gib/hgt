# Nearby collisions do not identify the onset of a witnessed nonreal zero

## Question and source

For already validated nonreal zeros of a constrained source deformation, locate nearby real double roots and vary the compensated product strength. The source is multiplied by `1+lambda*(a*h1+b*h2)+kappa*lambda^2*a*b*h12`; `(a,b)` is the stated direction normalized to length one. The two cosine polynomials preserve source mass and second moment, and their corrected product preserves those same moments. `parameters.json` contains the precision-specific coefficients. Theta uses the literal completed-theta kernel; the control uses the completed primitive conductor-5 character source. A positive multiplier does not assert positivity of that character kernel.

## Outcome

5 solves attempted; 3 admitted solver instances, 3 distinct local double roots, 2 explicit solver failures. Every admitted instance was refined at100/160 digits and independently checked by190-digit source integration of F and F_t at the root and at height+.125. Duplicate theta seeds are retained as repeat instances, not counted as distinct discoveries.

| Direction | Product strength kappa | Double-root height t | Deformation lambda | Sufficient multiplier bound |
|---|---:|---:|---:|---:|
| -1,1 | .5 | 19.9929609435 | 0.0182040246366 | 0.02582546594 |
| -1,1 | .75 | 20.1594137147 | 0.0192072397809 | 0.02729854558 |
| -1,1 | 1 | 20.8704781883 | 0.0589893257314 | 0.08512642933 |

The conductor-5 product witness already exists at lambda≈0.0512742166214, but the nearby double-root solve returns lambda≈0.0589893257314, ABOVE the witness. At kappa0.5/0.75 it finds smaller-lambda roots near heights19.993/20.159. At strengths0/0.25 the solver leaves the admitted height region. These observations cannot distinguish a return of the witness to the real axis from a nearby unrelated branch.

## Validation and uncertainty

Maximum coordinate difference between100/160-digit solutions: 8.81483841126694701669963911117139433453097530729560358137058724E-96. Maximum error of independent190-digit source integration against the shifted-completion formula: 6.959337153312462214189761973471049443732916256606648159612905976110262868981715846323272351521684672E-191, after normalization by `exp(-pi*t/4)*(1+t*t)^0.875`. The source integral includes the fixed tail truncation x=4 used in the independently checked evaluator. No interval arithmetic or complete contour count was performed. Numerical precision and independent formula agreement do not certify zero ancestry.

Whole guarded run: 248.534s; recorded worker time: 649.297s. Original download hashes verified before reporting; preserved in REMOTE-SHA256SUMS. Environment and source hashes are saved. No Lean build.

## Meaning for HB/RH and next discriminator

The intended reverse localization did not establish which collision produced each nonreal witness. Nearest-height Newton association can select an entry, a return, or an unrelated branch. The useful survivor is a set of validated local double roots and a sharper experimental question: continue each original complex witness backward and forward in deformation, with step refinement, and attach a collision only inside the traversed parameter bracket. These are arithmetic source deformations. The complete HB action, its corrections/readers/boundaries, and source-enforced extinction remain unidentified by this experiment.
