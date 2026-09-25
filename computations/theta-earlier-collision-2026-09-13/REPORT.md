# Nearby collisions do not identify the onset of a witnessed nonreal zero

## Question and source

For already validated nonreal zeros of a constrained source deformation, locate nearby real double roots and vary the compensated product strength. The source is multiplied by `1+lambda*(a*h1+b*h2)+kappa*lambda^2*a*b*h12`; `(a,b)` is the stated direction normalized to length one. The two cosine polynomials preserve source mass and second moment, and their corrected product preserves those same moments. `parameters.json` contains the precision-specific coefficients. Theta uses the literal completed-theta kernel; the control uses the completed primitive conductor-5 character source. A positive multiplier does not assert positivity of that character kernel.

## Outcome

20 solves attempted; 18 admitted solver instances, 13 distinct local double roots, 2 explicit solver failures. Every admitted instance was refined at100/160 digits and independently checked by190-digit source integration of F and F_t at the root and at height+.125. Duplicate theta seeds are retained as repeat instances, not counted as distinct discoveries.

| Direction | Product strength kappa | Double-root height t | Deformation lambda | Sufficient multiplier bound |
|---|---:|---:|---:|---:|
| -1,1 | 0 | 111.305858693 | 0.0090964180391 | 0.01286427776 |
| -1,1 | .25 | 111.320037284 | 0.00856122970889 | 0.01211408 |
| -1,1 | .5 | 111.331238805 | 0.00814215702993 | 0.01152682 |
| -1,1 | .75 | 111.340487086 | 0.00779871585297 | 0.0110456611 |
| -1,1 | 1 | 111.348351289 | 0.00750853248775 | 0.01063919939 |
| 1,-1 | 1 | 134.568642298 | 0.0176127128003 | 0.02502110405 |
| 1,-1 | .75 | 134.607384402 | 0.0188081987271 | 0.02669542677 |
| 1,-1 | .5 | 135.032481234 | 0.0387807543998 | 0.05511811116 |
| 1,-1 | 1 | 162.47364779 | 0.0241425558688 | 0.03435498818 |
| 1,-1 | .75 | 162.527378081 | 0.0241268794699 | 0.03427954717 |
| 1,-1 | .5 | 162.582706078 | 0.0242574647613 | 0.03441237744 |
| 1,-1 | .25 | 162.641980282 | 0.0245754396725 | 0.03480990464 |
| 1,-1 | 0 | 163.388745687 | 0.0578905673452 | 0.08186962547 |

The two witnesses near height111 produce the same five nearby collision solutions at matching kappa. Their additive and product endpoints have lambda≈0.00909641803910 and0.00750853248775. Independent kappa solves alone do not establish that these are one continuously tracked branch.

For the additive witness near163.219+0.303674i, the nearby double root occurs at lambda≈0.0578905673452, ABOVE its witness lambda≈0.0448980005604. This point cannot automatically be labeled the entry threshold for that witness. Product strengths0.25..1 lead to another cluster near heights162.64..162.47 and lambda≈0.0241..0.0246. For the witness near134.883, strengths0 and0.25 left the admitted height region; those failures do not exclude collisions.

## Validation and uncertainty

Maximum coordinate difference between100/160-digit solutions: 9.189188787595767817540670574266088119637126064349609039641106291919E-91. Maximum error of independent190-digit source integration against the shifted-completion formula: 3.329520311168747209324975108668155791208943598194006959053062061992865649146289961127228426716139666E-145, after normalization by `exp(-pi*t/4)*(1+t*t)^0.875`. The source integral includes the fixed tail truncation x=4 used in the independently checked evaluator. No interval arithmetic or complete contour count was performed. Numerical precision and independent formula agreement do not certify zero ancestry.

Whole guarded run: 189.040s; recorded worker time: 1438.253s. Original download hashes verified before reporting; preserved in REMOTE-SHA256SUMS. Environment and source hashes are saved. No Lean build.

## Meaning for HB/RH and next discriminator

The intended reverse localization did not establish which collision produced each nonreal witness. Nearest-height Newton association can select an entry, a return, or an unrelated branch. The useful survivor is a set of validated local double roots and a sharper experimental question: continue each original complex witness backward and forward in deformation, with step refinement, and attach a collision only inside the traversed parameter bracket. These are arithmetic source deformations. The complete HB action, its corrections/readers/boundaries, and source-enforced extinction remain unidentified by this experiment.
