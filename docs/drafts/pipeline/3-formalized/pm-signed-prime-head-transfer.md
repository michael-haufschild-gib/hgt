# PM signed prime-head transfer

- **Status:** formalized and audited, 2026-10-04.
- **Route:** PM; coupled prime-square source.
- **Module:** `formal/GaloisForLFunctions/RHTower/PMPowerDampedMobiusPrimeHead.lean`.
- **Frontier effect:** transfers the actual signed prime head to its boundary-moment kernel with a uniform unconditional error. Complete prime convolution and signed energy compensation remain open.

## Exact results

Write `A_epsilon` for the literal power-damped Möbius Fermi source and
`w_epsilon(v)=v^(epsilon-2)*A_epsilon(1/v)`. For every `epsilon>=0`, there
are positive constants `c,K` such that, eventually in real `X`, uniformly
for `sqrt(X)<=u<=X/2`,

`|sum_(u<q<=X, q prime) q^(-epsilon)*Re(A_epsilon(q/X))`
` - integral_u^X t^(-epsilon)/log(t)*Re(A_epsilon(t/X)) dt|`
` <= K*X^3*u^(-epsilon-2)*exp(-c*sqrt(log X))`.

For `X>0,H>=1`, reciprocal substitution identifies the integral at `u=X/H`
exactly with

`X^(1-epsilon)*integral_1^H Re(w_epsilon(v))/(log X-log v) dv`.

Thus, uniformly for `2<=H<=sqrt(X)`, the corresponding error is at most

`K*X^(1-epsilon)*H^(epsilon+2)*exp(-c*sqrt(log X))`.

No RH, small-damping L2 admission, source-sign, or prime-sum premise is used.
Parameter restrictions state the domain of these auxiliary theorems.

## Proof

The unconditional theta PNT error is uniform on `[sqrt(X),X]` after reducing
its exponential constant. Abel summation gives a weighted prime-band error
`K*X^2*u^(-epsilon-1)*exp(-c*sqrt(log X))` for every upper endpoint in `[u,X]`.

The actual divisor coefficients lie in `[0,1]`. Their finite summatory count
at `b/q` is expanded at all cofactors `n<=floor(b/u)`, retaining the exact
cutoff `n*q<=b`. Finite interchange therefore expresses the prime count
as a sum of prime-band differences with upper endpoints `b/n`. The same
finite indicator expansion expresses the integral as the matching weighted
integral differences. Summing the individual errors costs at most `b/u`.
Applying this twice, at `b=X` and `b=X/2`, preserves the actual signed dyadic
source and proves the head bound, including prime and cofactor endpoints.

The measurable reciprocal map `v -> X/v` has absolute derivative `X/v^2`.
Its image of `[1,H]` is `[X/H,X]`; finite endpoint changes have zero measure.
Change of variables gives exactly the displayed boundary weight. The power
identity `X^3*(X/H)^(-epsilon-2)=X^(1-epsilon)*H^(epsilon+2)` gives the
cofactor-cutoff form.

## Audit

- Targeted `lake --old build +GaloisForLFunctions.RHTower.PMPowerDampedMobiusPrimeHead:olean` passed. Only this leaf was newly built; dependency jobs were replayed.
- Final `lake env lean GaloisForLFunctions/RHTower/PMPowerDampedMobiusPrimeHead.lean` passed with empty output.
- A `/tmp` audit of all three public exports reports only `propext`, `Classical.choice`, `Quot.sound`.
- Module imported once by the RHTower umbrella; no umbrella build.
- `scripts/formal_tools.py index` passed and the three declarations appear in `LEAN_API.md`.
- Global lint reports thirteen unrelated unreachable modules, including `RoutePNativeMassPrefixMoments`; no PM failure. This is not a global lint pass.
- No numerical experiment, added axiom, placeholder, heartbeat increase, commit, or push.

## Remaining frontier

The active proof is in `../1-in-progress/pm-prime-square-coupled-source.md`.
The head uses a subexponential cofactor cutoff. The actual prime tail must
retain its density factor; the quantitative zero-mass tail and dominated
centered-kernel limit then recover the negative boundary jet. Finite rough
inversion must include prime squares before the proposed square-scale sign
can be claimed. None of these local results supplies the required complete
signed prime-update compensation inequality.
