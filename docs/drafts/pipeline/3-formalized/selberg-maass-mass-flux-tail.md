# Actual Maass cusp mass decay and finite tail energy

- **ID:** SELBERG-MAASS-MASS-FLUX-TAIL
- **Stage:** 3-formalized; targeted final audit in progress.
- **Parent:** [Constructive Selberg loop](../1-in-progress/selberg-quarter-conjecturing-loop.md), cycle 22.
- **Scope:** Literal principal-congruence Maass cusp eigenforms, with positive sub-quarter eigenvalue for the decay and infinite-tail conclusions.

## Exact result

Let `w=N+1`, `k=2*pi/w`, and `A=1/k`. For the actual source chart `F(x+iy)`, define

`M(y)=(1/w)*integral_0^w |F|^2 dx`,

`J(y)=(1/w)*Re integral_0^w F_y*conj(F) dx`,

`G(y)=(1/w)*integral_0^w (|F_x|^2+|F_y|^2) dx`.

At every positive height the source PDE gives `M'=2J` and `J'=G-lambda*M/y^2`. The literal physical quarter-energy slice `Q` satisfies `Q/w=J'+(lambda-1/4)*M/y^2`.

For every actual eigenform with `0<lambda<1/4`,

`M(y) <= M(A)*exp(-k*(y-A))` for `y>=A`, and `J(y)->0` as `y->infinity`.

For every `Y>0`, the actual functions `M`, `M/y^2`, `J'`, `G`, and `Q` are integrable on `(Y,infinity)`, and

`integral_Y^infinity G = -J(Y) + lambda*integral_Y^infinity M/y^2`,

`(1/w)*integral_Y^infinity Q = -J(Y) + (lambda-1/4)*integral_Y^infinity M/y^2`.

These statements use the existing actual Maass object. There is no separate modal ansatz, lift assumption, exponential-decay premise, or terminal-flux premise. They do not prove the global Selberg quarter bound.

## Corpus-derived conjecturing loop

The inspected `HTGeometry.WaveEnergyFlux` suggested differentiating literal energy and using the source equation plus Green integration. `HTGeometry.PeriodicCuspBoundaryGap` suggested exploiting the first allowed horizontal frequency, but its holomorphic argument does not apply to Maass data. The replacement tested here is a second-order mass inequality.

The real conjugation and integration-by-parts proofs in `SuzukiWeilDifferentialPairing` and `SuzukiPHatSpectralCoefficient` supplied the needed actual Hermitian pairing pattern. `HTGeometry.DifferentialInequalityComparison` and `SelbergBesselBoundaryEnvelope` supplied integrating-factor comparison patterns. `ThetaCuspReflectedSquaredNormalizedFluxLogConvexNoGo` supplied secant arguments connecting derivative sign to a limiting function. `ThetaCuspHawkingBMCuspFluxReconstruction` supplied the source-tail reconstruction pattern, retaining the terminal term until its value is proved.

The candidate mass/flux chain survived proof. Lean exposed no additional source assumption: finite tail energy follows from convexity and the actual PDE, without an interchange of the Fourier series with an infinite height integral.

## Dependency-closed paper proof

1. Define the literal real Hermitian horizontal pairing. Real C² regularity makes its products and directional derivatives integrable on each finite period. Local compact domination differentiates it in height. Horizontal Green integration has zero endpoint contribution because both the source and its first horizontal derivative are periodic. Integrate the actual hyperbolic PDE after multiplication by the conjugate source. These steps prove `M'=2J` and `J'=G-lambda*M/y²`.
2. The previously proved physical Parseval identities identify mass and both derivative energies with their convergent coefficient series. Their linear combination gives the quarter-slice identity. The source cusp filter bounds the source uniformly by `sqrt(epsilon/2)` at large height; integrate its square to prove `M->0`.
3. The already-proved actual exceptional constant term is zero. Every remaining integer frequency has squared frequency at least `k²`. Termwise order between the convergent nonnegative Parseval series gives `G>=k²*M`. For `y>=1/k`, `lambda/y²<=k²/4`, hence `M''>=k²*M>=0`.
4. Thus `M'` is increasing on this ray. Every later secant slope dominates its value at the initial endpoint. Those secant slopes tend to zero because `M->0`, proving `M'<=0`.
5. Differentiate `B(y)=exp(-k*y)*(M'(y)+k*M(y))`. Its derivative is `exp(-k*y)*(M''-k²*M)>=0`. Since `M'<=0`, `B(y)<=k*exp(-k*y)*M(y)->0`. Monotonicity therefore forces `B<=0`. The derivative of `exp(k*y)*M(y)` is nonpositive, giving the explicit exponential estimate.
6. A backward unit secant bounds `-M'(y)` between zero and `M(y-1)`. Therefore `M'->0`, and `J=M'/2->0`. Above the cutoff, `J'>=k²*M/2>=0`. The inspected improper fundamental theorem gives integrability of `J'` and its integral `-J(A)`. Domination gives integrability of `M`.
7. Actual source regularity makes `M`, `G`, and `J'` continuous at positive heights. Adjoin a finite compact interval to extend the tail integrability to any `Y>0`. Dominate `M/y²` by `M/Y²`. The exact flux equation then proves integrability of `G`, and the quarter-slice equation proves integrability of `Q`. Integrate those identities using the proved vanishing terminal flux. This proves both infinite-tail equalities.

## Lean implementation and audit

- `GaloisForLFunctions.RHTower.SelbergMaassBoundaryFlux`: actual Hermitian pairing, Green identity, mass/flux derivatives, physical quarter-slice identity, mass limit, first-frequency energy bound.
- `GaloisForLFunctions.RHTower.SelbergMaassCuspDecay`: actual second-derivative lower bound, exponential mass decay, vanishing mass derivative and flux, integrable flux derivative.
- `GaloisForLFunctions.RHTower.SelbergMaassTailEnergy`: finite physical mass and energy above every positive height, exact infinite-height gradient and quarter-energy balances.

All three complete scratch files and direct source checks passed without warnings. All three modules are wired into `RHTower.lean`. Targeted final builds, axiom checks, index refresh, and the latest lint result are recorded after their completion.

## Remaining source question

The physical infinite-tail interface is now proved. Next test the actual Maass version of the critical Bessel square decomposition, retaining its nonnegative remainder, and justify its sum over Fourier modes using the just-proved tail integrability. The existing Bessel energy theorem only accepts compact real C¹ profiles; it cannot yet be applied directly to an actual complex, noncompact Maass mode. The boundary-form comparison, compact quotient-core inequality, and all-congruence Selberg conclusion remain unproved.
