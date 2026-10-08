# Next conjecture — vanishing mass defect on the cofinal exposing diagonal

Status: OPEN PRODUCER. No Lean or paper proof of the lower inequality.
Universal WP02 remains OPEN. This replaces neither the literal receiver nor its
quantifiers. The reduction below is a paper argument, not a new positivity theorem.

## Exact candidate

There exist K>=0 and N0 such that for every N>=N0, put A_N=log(N)/2+1.
For EVERY finite family of actual complex C2 polar tests f_i with apertures
<=A_N, nonnegative coefficients alpha_i, and t>=0, if

    2*pi*sum_i alpha_i atomCoeff(f_i,n) = t*exposingWeightTrunc(N,n)

for EVERY integer n>=2, then

    sum_i alpha_i archEnergy(f_i)
      >= t*(T-tau_N)
         - K/(1+log N) * sum_i alpha_i integral |paperFT(f_i)|^2.

N0 may be enlarged to at least 1. Include t=0; it is not a disposable edge case.
All samples beyond N, through and beyond the aperture cutoff, are exactly zero.
No mass normalization, bound on number of rows, coefficient bound, positivity
premise, cone point, or assumed RH enters the candidate.

[OPEN CORE] Prove this signed lower estimate from the actual gamma source and
matching constraints. Neither the exterior coercivity certificate nor the
primitive logarithmic estimate proves the finite core inequality.

## Why a vanishing negative error would suffice

Take any fixed original matched family at cutoff n0 and aperture A, with
Fourier mass M0. Append t times the existing repair rows at n0<n<=N.
Their energy cost is <=t*(tau_n0-tau_N) and their apertures are <=A_N.
For sufficiently large N the original rows also fit A_N.

The exact packet Fourier-mass identity gives, for the two coefficients 1,s
with s=+1 or -1,

    FourierMass(twoPointResonator(n,s)) = 4*pi*resonatorMass(n).

Consequently the normalized repair row has Fourier mass |w(n)|, and the
whole appended mass is exactly M0+t*sum_(n0<n<=N)|w(n)|. This is uniformly
bounded in N: the corpus's exposingMajorant=(log n+boxConst)|w(n)| is summable,
boxConst>=0, and log n>=log 2>0 for n>=2. Thus the proposed negative error
tends to zero on this FIXED original family plus its canonical repairs.
Subtracting the repair energy cost and passing to the limit gives the exact
original inequality E0>=t*(T-tau_n0), including t=0. The cutoff/level condition
holds on the diagonal since N<=floor(exp(2*A_N)).

The old tail-repair API's word 'mass' denotes box budget, not Fourier L2 mass.
The displayed Fourier-mass identity must be verified and connected to the
literal repair definitions before any Lean reduction is claimed. Sources read:
WeilWorkExposingRayPacketCoercivity.exposingPacket_fourier_mass;
WeilPositivityPrimeBlindDuality.twoPointResonator/resonatorMass/twoPointCoeff;
WeilWorkExposingRayTailRepair.exposingRepairCoeff/energy_le_tail_sub/level_le.

## Audit and research direction

The cofinal reduction mechanism is already in WP02 PROOF.md. Adding a bounded
repair-mass error is a standard extension, not scientific novelty. Do not spend
a cycle formalizing only another conditional receiver. First seek an actual
lower estimate or a nontrivial quantitative survivor that controls arbitrary
matched families. A rate slower than 1/log N is acceptable if proved to vanish;
a fixed negative mass loss is not sufficient.

Cycle18 deep query 'exposing diagonal cofinal vanishing mass error lower bound
tail repair' finished non-partial with68,565 indexed/inventoried files. All20
candidates and20 source arguments inspected. It retrieved the actual tail
repair and completed-error/head identities, not a proved lower producer.
Compiler enrichment remains incomplete; no absence claim.

Additional cycle18 audit rejected recycling the ground-state transform:
STATUS MUST-786 and prior loop rows377--388 already isolate its signed prime
fluctuation and the zero-surplus obstruction to lossy path comparison.
Prime-torus moment realization also retains no frequency-cost bound by itself;
WP01 TORUS-DENSITY.md records the logarithmic-moment tightness obstruction.
Neither is an unconditional source of the candidate estimate.

The new PrimitiveSharpness result explains a concrete obstacle: the old
primitive surrogate loses a fixed quarter of Fourier mass for every adaptive
parameter. This cannot be absorbed by a coefficient tending to zero. Its
sharpened logarithmic survivor must still be coupled to actual matched traces;
further constant tweaks or a routine upper-family spectral limit do not pay
that obligation. Seek signed trace-dependent gamma compensation at the full
family level, retaining the pole constraints and the frequency variable.
