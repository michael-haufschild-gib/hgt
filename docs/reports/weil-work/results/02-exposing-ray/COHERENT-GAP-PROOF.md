# Positive total-energy floor for the geometric completion

Status: dependency-closed paper argument, formalized and final leaf audits passed. Original WP02 remains OPEN. This is a lower bound for the explicit cycle-9 completion, not arbitrary repairs.

## Admission of the actual C2 sources

For a compactly supported C2 complex function f, write F=mathlib's Fourier transform f. The corpus identifies F(xi)=paperFT(f)(-2*pi*xi), proves integrability of |paperFT(f)|^2 and of its product with the archimedean symbol, and proves classical/L2 Fourier compatibility. The exact CCM weight is

    w(xi)=1-2*gammaHardyPhaseRate(0)+archimedeanWeilSymbol(xi).

Evenness and the nonzero real scaling tau=-2*pi*xi show w|F|^2 is integrable. Therefore F defines a vector in the weighted Fourier L2 space. Its inverse Fourier class is f; compact support in [-a,a] puts it in the kernel defining the exact CCM form domain. Its polar coefficients are literally integral exp(±x/2)f(x)dx, hence vanish if the actual paper Fourier values at ±i/2 vanish. No C-infinity approximation or extra regularity premise is needed.

At a=log(2)/2 the corpus theorem `ccmRestrictedWeilSourceQuadratic_halfLogTwo_eq` removes all pole and prime terms. Fourier change of variable gives the exact form value archEnergy(f)/(2*pi), with physical norm squared integral |f|^2. The established one-tenth ground gap yields

    (2*pi/10) integral |f|^2 <= archEnergy(f).

This is a transfer of an existing strict small-aperture result, not a new general positivity theorem.

## Nonzero short source and its uniform gap

For s in [1/201,1/200], the actual f_s=farPolarTest(s) is C2, polar-constrained, and supported in radius s+17/50<log(2)/2. The actual Fejer profile is one at 0 and ±s; therefore f_s(0)=1-1/cosh(s/2)>0. Continuity makes its L2 class nonzero. The transferred gap proves archEnergy(f_s)>0 for each such s.

The real-frequency multiplier is 1-c_s*cos(tau*s), with 0<c_s<=1. Its squared modulus is at most four, so the absolute energy integrand is dominated by the integrable function 4*|paperFT(psi)|^2*|A|, independently of s. Pointwise continuity and dominated convergence give continuity of s -> archEnergy(f_s). Compactness of the closed step interval now gives delta>0 with delta<=archEnergy(f_s) throughout it. Compactness is applied only AFTER strict source positivity and continuity are proved.

## Exact coherent cost

With the cycle-9 q(s)=exp(-s/2), N>=1, the weight at (0,0) is (1+q^2)/(1+q^(2N))>=1. All weights are positive, so mass(N,s)>=1. Thus

    delta <= mass(N,s)^2*archEnergy(f_s).

The existing exact energy identity identifies this expression with the total energy of farPolarTest(N*s) and its actual finite variance repairs. This proves the stated floor, including the step selected for every X>=4.

## Attack verdict and scope

The zero-total-energy endpoint is unavailable to this particular geometric completion. The positive survivor is an exact uniform cost invariant, stronger than merely saying its cost is bounded. The existing ground gap is its main analytical parent; external scientific novelty is unestablished. Other coherent completions are not excluded, and this theorem does not establish PBAP or the universal exposing-ray lower bound. The next source mechanism must address that distinction.

## Refinement-invariant strengthening (formalized)

The compactness argument above is unnecessary. For |x|<=3/10 and 0<=s<=1/200, all three arguments x, x-s, x+s have absolute value at most 61/200 < 17/50-17/1000. The actual flatBump plateau theorem gives psi(x)=psi(x-s)=psi(x+s)=1. Hence f_s(x)=1-c_s on an interval of length 3/5. Its squared L2 norm is at least `(3/5)*(1-c_s)^2`. The C2 ground-gap transfer therefore gives

    (3*pi/25)*(1-c_s)^2 <= archEnergy(f_s).

Evaluating the exact geometric multiplier identity at tau=0 gives

    mass(N,s)*(1-c_s)=1-c_(N*s).

Multiplying the energy bound by the nonnegative squared mass proves

    (3*pi/25)*(1-c_(N*s))^2 <= mass(N,s)^2*archEnergy(f_s).

This also covers N=0 and s=0. If N*s>=4, monotonicity of cosh on nonnegative arguments gives c_(N*s)<=1/cosh(2)<1. The fixed positive constant `(3*pi/25)*(1-1/cosh(2))^2` is therefore a lower bound. By the existing exact energy identity this is the total energy of the actual source and actual variance repairs. The estimate is uniform under arbitrary finite refinements, not just steps in [1/201,1/200]. All ingredients are source identities, the established ground gap, or analytic inequalities; no computation is used.

This stronger survivor closes the zero-cost endpoint of the entire geometric family at macroscopic separation. It still does not constrain alternative coherent completions, so the universal exposing-ray lower inequality remains OPEN. The stronger statement has been returned to the conjecture and corpus-audit stage before its Lean implementation.

The same pointwise bound gives the uniform constant `(3*pi/25)*(1-c_(X0))^2>0` for ANY fixed X0>0 and Ns>=X0. Taking X0=1/201 and N>=1 recovers the original compact-step conjecture. Taking X0=4 gives the macroscopic completion floor. These are direct monotonicity corollaries of the exact source bound, not new analytical assumptions.
