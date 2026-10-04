# PM signed prime convolution

- **Status:** formalized and audited, 2026-10-04.
- **Route:** PM; coupled prime-square source.
- **Module:** `formal/GaloisForLFunctions/RHTower/PMPowerDampedMobiusPrimeConvolution.lean`.
- **Frontier effect:** identifies the complete signed prime convolution with the negative boundary jet, uniformly across the square-root cutoff band. Finite rough inversion, the square-inclusive semiprime sector and complete signed energy compensation remain open.

## Exact asymptotic

For every `0<epsilon<1/2` and `delta>0`, all sufficiently large real `X`
satisfy, simultaneously for every `sqrt(X)/2<=a<=sqrt(X)`,

`|log(X)^2/X^(1-epsilon)`
`  *sum_(a<q<=X, q prime) q^(-epsilon)*Re(A_epsilon(q/X))`
`  +Re(D_epsilon)| < delta`.

The source and boundary jet are the literal PM objects. No RH, canonical
L2 admission, prime-sign, or unproved asymptotic premise is used.

## Finite estimate and proof

The module also proves a finite error bound, eventually in `X`, uniformly
for `R<=H<=sqrt(X)` and `2<=a<=X/H`. The normalized error is at most

`K*(log(X)/log(H)^3+1/log(H)+1/log(X)`
`  +log(X)^2*H^(epsilon+2)*exp(-c*sqrt(log(X)))`
`  +log(X)^2/(log(a)*log(H)^3))`.

Split the actual finite prime sum at `X/H`. The audited head transfer
identifies its large-prime portion with the moving boundary kernel. The
audited density-preserving tail controls its small-prime portion. The
actual kernel error identifies the signed main term with `-Re(D_epsilon)`.

For `X=exp(s^5),H=exp(s^2)`, the kernel errors vanish as inverse powers of
`s`. Uniformly in the stated lower-cutoff band, `log(a)>=s^5/4` eventually,
so the prime tail contributes at most `4/s`. The head error is eventually
at most `s^10*exp(-s^2)`, since
`c*sqrt(s^5)>=(epsilon+3)*s^2`. The existing power-times-exponential limit
finishes the parameterized proof. The inverse substitution
`s=(log X)^(1/5)` transfers it to every sufficiently large real `X`.

## Audit

- Scratch finite estimate, uniform parameter limit and all-real-X asymptotic passed.
- Targeted `lake --old build +GaloisForLFunctions.RHTower.PMPowerDampedMobiusPrimeConvolution:olean` passed; only this leaf was newly built.
- Final `lake env lean GaloisForLFunctions/RHTower/PMPowerDampedMobiusPrimeConvolution.lean` passed with empty output.
- `/tmp` axiom audit of the definition and all three theorems reports only `propext`, `Classical.choice`, `Quot.sound`.
- Wired once into RHTower; no umbrella build.
- Index passed; all four public declarations appear in `formal/LEAN_API.md`.
- Global lint reports twelve unrelated unreachable modules, no PM failure; not a global lint pass.
- No numerical experiment, added axiom, placeholder, heartbeat increase, commit or push.

## Remaining hard problem

The canonical prime core must be identified with its full-source, prime
and semiprime contributions at reciprocal scale `X` between `3*P^2/2` and
`7*P^2/4`. The semiprime contribution must retain prime squares and its
unordered-pair factor one half. Only after this exact identity and uniform
counting bound can the proposed negative core sign be claimed. Neither
this convolution theorem nor that local sign supplies complete signed
prime-update compensation.
