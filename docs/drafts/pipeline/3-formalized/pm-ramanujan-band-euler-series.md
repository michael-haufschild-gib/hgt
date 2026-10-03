# Route PM: complete arithmetic band Euler identity

- **ID:** pm-ramanujan-band-euler-series
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Lean:** `PMRamanujanBandEulerSeries.lean`, thirteen public declarations.
- **Continuation:** `../1-in-progress/pm-ramanujan-band-spectral-escape.md`.

## Exact result

For epsilon>0, Re(z)>1 and Re(s)<9/16, the literal Ramanujan weights and finite-primitive Mellin symbols satisfy

    zeta(z) * sum_q a_epsilon(q)*J_s(q)*q^(epsilon+s-z)
      = alpha*zeta(1+z-s)*H_epsilon(z,s).

The arithmetic series is absolutely convergent. Every actual denominator is retained; its q=0 term vanishes and its q=1 term is alpha. Both zeta factors remain in a cleared identity, suitable for subsequent analytic continuation without inserting a zero-free premise.

## Dependency-closed paper proof

The divisor symbol is exactly the Dirichlet convolution

    J_s = [n -> n^(1-s), zero at n=0] * mu.

Both factors are multiplicative. The denominator product over prime divisors also factors exactly on coprime inputs. Therefore

    f(q)=mu(q)*J_s(q)*q^(epsilon+s-z)/D_epsilon(q)

is multiplicative, with f(0)=0 and f(1)=1. The actual coefficient is alpha*f(q).

Absolute convergence is supplied independently of this factorization. The proved bound |a_epsilon(q)|<=q^(-1-epsilon) gives

    |a_epsilon(q)*J_s(q)*q^(epsilon+s-z)|
      <= |J_s(q)/q^(1+z-s)|.

The L-series of the convolution on the right is absolutely summable for Re(z)>1 and Re(s)<1: the power factor contributes exponent -Re(z), and the Mobius factor is bounded by one. This is the exact divisor-sum majorant, with no omitted cofactors. Positive alpha allows transfer to absolute summability of f.

For each prime, all exponent>=2 terms vanish by the Mobius prime-power law. The Euler product is therefore product_p(1+f(p)). Multiplying the audited source-specific prime correction identity by the two nonzero local denominators gives

    (1+f(p))/(1-p^(-z)) = H_p(z,s)/(1-p^(-(1+z-s))).

The absolutely convergent arithmetic product, correction product and two classical zeta products have unique limits. Multiplying these limits and restoring alpha proves the displayed cleared identity.

## Frontier contribution and limits

This closes the complete infinite arithmetic-series identification required by the two-variable band calculation. It uses actual source coefficients and retains the complete product boundary. The literal cutoff integral, finite-band Hilbert/Plancherel identification, paired analytic continuation and spectral escape theorem remain open. The complete small-damping energy ceiling remains the RH-producing problem; this leaf does not prove or refute RH.

## Audit — 2026-10-02

- Full scratch proof passed with no diagnostics after repairs.
- `lake --old build GaloisForLFunctions.RHTower.PMRamanujanBandEulerSeries`: exit 0; only this new leaf built (306 seconds).
- Final actual-file `lake env lean GaloisForLFunctions/RHTower/PMRamanujanBandEulerSeries.lean`: exit 0, no diagnostics.
- All thirteen public declarations passed `/tmp` axiom queries; only `propext`, `Classical.choice`, `Quot.sound`.
- Umbrella wired once; no umbrella build. Global lint reports eleven unrelated unreachable modules, no own-module finding.
- No added axiom, sorry, RH premise, numerical experiment, heartbeat increase or subagent.

Search132 and direct corpus inspection supplied reusable convolution and Euler-product machinery. Search133 checked the next cutoff bridge; it returned partial semantic retrieval. All returned candidates, source arguments and ingredient obligations were inspected; its generic indicator/Gamma chain does not supply the actual moving-band integral.
