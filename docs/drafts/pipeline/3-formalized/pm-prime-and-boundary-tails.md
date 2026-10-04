# PM prime and boundary tails

- **Status:** formalized and audited, 2026-10-04.
- **Route:** PM; coupled prime-square source.
- **Module:** `formal/GaloisForLFunctions/RHTower/PMPowerDampedMobiusPrimeTail.lean`.
- **Frontier effect:** closes the density-preserving prime tail and quantitative boundary-mass tail required by the signed convolution argument. Full convolution, rough inversion, square-scale sign and complete energy compensation remain open.

## Exact results

For some absolute positive `C`, whenever `2<=a<=b` and `L-log(b)>=8`,

`sum_(a<q<=b, q prime) 1/(q*(L-log q)^4)`
` <= C/(log(a)*(L-log(b))^3)`.

For each `0<epsilon<1/2`, there exist positive `C,R` such that, whenever
`2<=a<=b<=X/R` and `log(X)-log(b)>=8`, the literal source satisfies

`sum_(a<q<=b, q prime) q^(-epsilon)*|A_epsilon(q/X)|`
` <= C*X^(1-epsilon)/(log(a)*(log(X)-log(b))^3)`.

For some `C>=0` and all sufficiently large real `H`,

`|integral_H^infinity w_epsilon(x) dx| <= C/log(H)^3`,

where `w_epsilon(x)=x^(epsilon-2)*A_epsilon(1/x)`.
No RH, small-damping L2 admission, prime-sign or convolution premise is used.

## Proof

Apply finite Abel summation to
`g(t)=1/(t*(L-log(t))^4*log(t))`. On the stated interval `g>=0` and
`g'<=0`. The unconditional linear theta bound and integration by parts give
`sum <= C*(a*g(a)+integral_a^b g)`; the lower endpoint is retained.
Bounding `1/log(t)` by `1/log(a)` and integrating the exact primitive
`1/(3*(L-log(t))^3)` proves the prime-density tail. The audited log-four
actual-source envelope then gives the prime-source theorem.

For the mass tail, the same envelope bounds the integrand by
`C/(x*log(x)^4)`. On `x>H>1`, this is at most
`(C/log(H)^2)/(x*log(x)^2)`. The existing exact square-log tail integral
and the norm-integral inequality give the third logarithmic power.

## Audit

- Scratch proof passed, followed by targeted `lake --old build +GaloisForLFunctions.RHTower.PMPowerDampedMobiusPrimeTail:olean`.
- Only this leaf was newly built; dependencies were replayed.
- Final `lake env lean GaloisForLFunctions/RHTower/PMPowerDampedMobiusPrimeTail.lean` passed with empty output.
- `/tmp` axiom audit of all three exports reports only `propext`, `Classical.choice`, `Quot.sound`.
- Module wired once into RHTower; no umbrella build.
- Index passed; all three exports appear in `formal/LEAN_API.md`.
- Global lint reports eighteen unrelated unreachable modules, including six `ThetaCuspRatio...` leaves; no PM failure. This is not a global lint pass.
- No numerical experiment, added axiom, placeholder, heartbeat increase, commit or push.

## Next hard step

The actual centered kernel must now be combined with the signed prime-head
transfer. Its finite error follows on paper from zero mass, first moment
`-D_epsilon`, and the second absolute logarithmic moment. The prime-square
source identity must retain its semiprime sector, including prime squares.
Complete signed prime-update compensation remains the RH-strength target.
