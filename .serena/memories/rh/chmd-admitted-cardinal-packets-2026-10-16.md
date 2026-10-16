# CHMD admitted cardinal frames — 2026-10-16

Status: significant structural contribution FORMALIZED; unconditional RH goal remains ACTIVE and unproved. Read user attachment at each new turn. No web, old research Markdown, numerical experiments, subagents, full builds, heartbeat increases, or commits used.

Card: docs/drafts/pipeline/3-formalized/chmd-admitted-cardinal-packets-2026-10-16.md.

## Closed obstacle
Previous exact strip cardinal functions used a rational polar filter with artificial poles and lacked literal full graph admission. New construction removes full analytic multiplicity using L=replicate(xiZeroMult a,a), realizes the polynomial numerator X+1/4 within degree<=length L, and normalizes by the nonzero terminal transform. This gives actual smooth theta-dominated even sources with full exponential moments and first-jet decay. Their transform is exactly 1 on {a,-a}, 0 at every other Xi zero, and 0 at both polar points. Re(a)>0 and XiC a=0 index the construction; no simplicity, RH, admission, or positivity premise is added.

## Five wired leaves (742 lines, 67 explicit declarations)
- ThetaDivisorCardinalSource (171 lines): fullDivisionList; thetaDivisionList_full; xiZeroMult_pos_of_zero; fullDivision_sourceTransform_ne_zero; cardinalNotch; divisorCardinalSource_regularity / transform / poles. Analytic order cancellation is finite ENat cancellation, not division at a removable singularity by assertion.
- ThetaCardinalOrbitReadout (145): paperFT/sourceTransform convention bridge, unsignedOrbitIndicator A, cardinalRealSource a c=Re(c*u), cardinalOrbitValue=(c*A+conj(c)*B)/2 with B(z)=A(conj z). gammaOf_carrier_injective and finite four-point orbit support prove actual full W summability.
- CHMDCardinalOrbitEnergy (145): complete signedZeroEnergy equals c.re^2*Kplus-c.im^2*Kminus. Both masses are nonnegative finite sums retaining original zeta multiplicities. Re(a)>0, Im(a)!=0 implies Kplus=Kminus. Im(a)=0 implies Kminus=0. No actual nonreal zero is asserted.
- CHMDPolarGraphMoments (85): sourcePair_ground_eq_cosh for any literal source AE identity. Compact even ground pairing equals negative polar Fourier real value; strong bulk graph convergence and unconditional Fourier cutoff convergence extend this to the theta-relative decay class. sourcePair_ground_eq_polar is the reusable primitive bridge.
- CHMDCardinalGraphGeometry (196): exists_carrier_gammaOf_eq converts every Xi zero to actual zeta carrier using unconditional strip and xi/zeta correspondence. cardinalPositiveMass_pos_of_zero gives Kplus>0. CardinalGraphFrame records actual real/imag vectors, source AE representatives, compact approximability, ground orthogonality, energies Kplus and -Kminus, and zero mixed pairing. exists_cardinalGraphFrame discharges ALL analytic and domain obligations. Frame.energy gives E(r*p+s*q)=r^2*Kplus-s^2*Kminus; Frame.primitive puts every combination in primitive space. Frame.nonreal_energy is Kplus*(r^2-s^2); nonreal_linearCombination_eq_zero_iff proves an actual 2D plane. exists_positive_primitive_cardinal_frame has NO hypotheses: Hardy supplies positive real Xi zero, positive-energy primitive vector, exact normalized transform 1 at center.

## Verification
All five `lake --old build <leaf>` passed, no own warnings. Final plain `lake env lean <leaf>` passed sequentially for every leaf; all five logs empty. 113 explicit `have := @Name` mathlib probes passed. #print axioms audited all 67 declarations: only propext, Classical.choice, Quot.sound. Umbrella imports each leaf exactly once. `scripts/formal_tools.py lint` exited 0 (only existing large-file warnings). Guarded `formal_tools.py index` exited 0, wrote API/GAPS/OVERVIEW, reported 0 changed/0 removed because cache was already refreshed. No umbrella/full build.

Source SHA256:
ThetaDivisorCardinalSource c7d2f2869028e5e79a52aaaea37014c394aa32587a96c5cef1f4bf34c22a181e
ThetaCardinalOrbitReadout 2b1f38ec904eefb67133b3e4a1f1adadfb84d39b301e22c0d23fa54dd3e07876
CHMDCardinalOrbitEnergy ec3d82bca764ac9f1cad8e1552845fa74763773b8e9d128ee2febd48cb5841f2
CHMDPolarGraphMoments 123accfe9ba48c574ae46ae8e13ca6315061f3956a10f36878af333da5ebf904
CHMDCardinalGraphGeometry d149fa5a00f51d0fbbceff041da6edcb2364a3ffc684c367242d32e951420eac

## Boundary / next structural question
No primitive positivity, family completeness, exclusion of nonreal zeros, or RH proved. Next: continuous signed evaluation representers against arbitrary completed graph vectors, then actual radical identification. Even packets alone do not settle odd sector. Need prove evaluation/representation or density rather than assume a complete cardinal expansion. Actual graph retains every prime atom and original signed form.

## Lean lessons
Polynomial has .differentiable, not .analyticAt: compose square then .analyticAt. ENat.add_left_injective_of_ne_top cancels finite right summand; use conv_lhs to rewrite only that summand. Use lipschitzWith_smul, div_left_inj' (prime), sub_left_injective, no map_ite. In sourceTransform unfold partially applied source before const_mul rewrite. Function equality rewrites may not match eta-reduced real/im lambdas under complex casts: obtain polar equation separately via simpa only [function equality]. Bridge imports do not expose EvenSector.bulkCutoff_neg; its one-line definition proof avoids adding a large dependency.
