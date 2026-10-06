# BAG uniform local Mellin Sobolev transfer

2026-10-06,01ax. Dependency-closed paper proof and Lean production closure.
LocalMellinSobolevTransfer630lines/API1. Complete scratch81394/log08 terminal0
PASS/exported axiomprint standard3 only; final production14804/log01 empty
PASS; imported production axiom61350/log01 standard3 only; index6054 PASS,
API1/importonce16686; scoped diffcheckPASS. Lint49164/log01 terminal1:
362warnings,10 unrelated unreachable modules; no ownedfinding, global lint
not clean. Exact modules: RHTower.Sieve.TwistedSelbergCoefficient,
Factorization,Forms,GcdLog,GcdLogForms,RatioForms,Summability;
ThetaCuspRatioKineticBlockCoefficients10; ThetaCuspRatioKineticDriftReader;
VerticalProgressionRatioForm. Logs /tmp/bag-local-mellin-sobolev-*01ax.log.

For every theta in(0,1), one constant C controls the full logarithmic Fourier
H^(1+theta) energy of the literal localized profile for ALL sigma in[1,2]^2
and ALL physical Schwartz inputs f by the same full physical Fourier energy.
The profile is exactly exp(-sigma dot u)*chi(exp(-u))*f(exp(-u)), with the
fixed chi equal1 on a neighborhood of the complete stationary box[1/4,4]^2.
Both sides are nonnegative Lebesgue integrals with weight
(1+|xi0|+|xi1|)^(2+2*theta). Finiteness is derived, not assumed.

Proof. The measure-preserving Euclidean-to-pair coordinate map, with a swap
for the second axis, turns the proved planar log chart bound into either
Euclidean directional energy estimate. Its negative physical direction is
retained. Nonnegative Tonelli exchanges the transverse coordinate and shift;
both logarithmic Jacobians are included by LocalLogFractionalEnergy.

Apply that chart estimate to each literal physical coefficient A*f, B_i*f,
C_i*D_i f from CompactMellinLocalization. Their common support is in the
fixed positive box(1/8,8)^2, their joint parameter compactness supplies uniform
physical fractional-energy and mass estimates. The exact first logarithmic
Euler derivative is the sum of the B_i and C_i terms. Its difference energy
is bounded by twice the two full difference energies. This gives an actual
uniform bound using the directional physical Fourier energies and masses of
f and its matching first derivative; it assumes no high Schwartz budget.

For mass, the exact one-dimensional log substitution gives density1/x.
A supported nonnegative function in[a,b] therefore has log-pullback mass at
most a^-1 times physical mass. Apply it in both coordinates and use the
proved uniform A multiplier mass to bound the actual localized output mass.

Native Fourier differentiation of D_i f is exactly2*pi*I*xi_i*Fourier(f).
Consequently its norm square is(2*pi)^2*|xi_i|^2*|Fourier(f)|^2. The strictly
positive directional Gagliardo constant identifies the full fractional
energy of D_i(output) with a positive constant times the axial spectral
moment of order2+2*theta. This converts the exact Euler estimate into each
output axial moment bound. Each physical input moment and derivative mass
is dominated by the full physical Fourier weight. The scalar estimate
(1+|a|+|b|)^p <= 3^p*(1+|a|^p+|b|^p), p=2+2*theta, converts output mass and
its TWO DIAGONAL axial moments into the COMPLETE two-dimensional weight.
No mixed-jet product estimate is used. Admission follows separately from
Schwartz directional derivative admission and the positive Gagliardo law.

Route contribution: closes the hard local fractional transfer across order
one. Actual BAG selected physical energy supplies theta<1/2. The remaining
attachment must keep the exact Fourier scaling2*pi and normalized physical
prefactor; exterior logarithmic energy, complete Mellin line tails,
lower-growth source envelope, moving-test signed cancellation, the full
original sharp-action bridge, growing moments/cofactors and deterministic
common-height return remain open. RH remains unproved.
