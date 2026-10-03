# Route PM: actual complete-band Hilbert and Mellin energy

- **ID:** pm-ramanujan-band-hilbert
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean audited)
- **Continuation:** `../1-in-progress/pm-ramanujan-band-spectral-escape.md`.

## Exact statement

For natural cutoffs 1<=X, Y and any real epsilon, let S(N) be the actual complete denominator band, with all weights and cofactors retained. Define

    g(u)=exp(-u/2)*S(floor(exp u)),
    T(tau)=zeta(s)/s * sum_(X<q<=Y) a_epsilon(q)*J_s(q),
    s=1/2+i*tau.

The actual source g belongs to L1 and L2 on the full real line. Its complete critical Mellin trace satisfies

    T(tau)=Fourier(g)(tau/(2*pi)),
    integral |g(u)|^2 du
      = sum_(n>=0) |S(n+1)|^2/[(n+1)(n+2)],
    integral |T(tau)|^2 d(tau) = 2*pi*integral |g(u)|^2 du.

Consequently T represents an L2 vector. For any L2 frequency test h, its literal integral pairing is the Hilbert inner product with that vector and satisfies

    |integral conjugate(h(tau))*T(tau) d(tau)|^2
      <= 2*pi*||h||^2 * sum_(n>=0)|S(n+1)|^2/[(n+1)(n+2)].

No unknown signed-energy estimate is a hypothesis. The finite-source bound used for admission may depend on both cutoffs.

## Dependency-closed paper proof — [PROVED HERE]

Every q in the band exceeds one, so the audited primitive is periodic and bounded. Summing the finitely many actual weighted primitive bounds gives |S(N)|<=C. For u<0, floor(exp u)=0 and S(0)=0. For u>=0, |g(u)|<=C*exp(-u/2). This proves L1 and L2 admission, with measurability supplied by the measurable natural floor and the finite coefficient function.

The logarithmic source equals the logarithmic Mellin source of t -> S(floor(1/t)) on the critical line. The audited complete finite-band Mellin formula and the logarithmic Mellin--Fourier law give T=Fourier(g) at the rescaled frequency. Plancherel supplies the factor 2*pi and L2 admission of T; the L1 source identifies the classical Fourier integral with its L2 representative.

Substitute x=exp u in the source norm. The result is integral_(x>0)|S(floor x)|^2/x^2. Below one the integrand vanishes, except for an irrelevant endpoint. Apply `hasSum_stepGram` to Re(S) and Im(S) separately. Their sum equals |S|^2 and recovers the exact original reciprocal-weight energy. The complete square remains inside the integral and series at every step.

Realize g and T by their MemLp representatives. Their representatives agree almost everywhere with the literal functions. The L2 inner-product integral and Cauchy--Schwarz then give the displayed pairing and bound. Compact frequency tests are included; critical-line point evaluation is never used as a bounded functional.

## Contribution and remaining hard problem

This identifies the actual complete signed energy with a Hilbert norm and makes the frequency test used by the cleared cutoff identity bounded on that norm. The actual moving-dilation law, compact tested analytic continuation and scalar Abel argument still require formalization. No uniform estimate as the cutoff grows is inferred from the finite-source admission. The small-damping signed-energy ceiling and RH remain open.

## Verification status

`PMRamanujanBandHilbert.lean` contains all displayed identities, admission and bounded-pairing results. Its targeted `lake --old build GaloisForLFunctions.RHTower.PMRamanujanBandHilbert` passed (only this leaf built, 249 seconds). The final actual-file `lake env lean GaloisForLFunctions/RHTower/PMRamanujanBandHilbert.lean` passed with no diagnostics. All twenty-two public declarations passed separate `/tmp` axiom queries: only `propext`, `Classical.choice`, and `Quot.sound`. Umbrella import is wired once. Global lint reports eleven unrelated unreachable modules and no finding for this leaf. No heartbeat increase, numerical experiment, full build or umbrella build was used.
