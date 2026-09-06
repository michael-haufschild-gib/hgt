# The literal Weil pole matrix and its integrated prime error

- **Stage:** 3-formalized
- **Lean:** `CCMRestrictedWeilPrimePoleMatrix`, `CCMRestrictedWeilFullPoleMatrix`, `CCMRestrictedWeilPoleCompression`, `CCMRestrictedWeilPoleIntegratedPrimeError`; 25 public theorems and seven definitions, wired into `RHTower`.
- **Chain:** exact prime–Gamma source → explicit pole matrix → integrated prime-error control → pole exclusion → RH. Matrix and quantitative arithmetic handoff are closed. Uniform estimates and both directions of the RH criterion are also closed in [the fixed-pole criterion package](weil-fixed-exponential-pole-rh-criterion.md). All-aperture positivity remains open.
- **Corpus seeds:** actual pole operator domain/action, prime-polar arithmetic action, source cancellation, ground source variance, full-form reflection, elementary Mertens, and the rectangular/moving-Cauchy/Landau families. The new identification is with the actual physical pole compression; generic two-dimensional diagonalization is reused mathematics.

## Conjecture → proof / fail → pivot
1. Ground-source variance is sharp in the proved Hermitian swap model. Equality in that abstract bound cannot by itself exclude a zero constrained ground.
2. **Conjecture:** the pole energy appearing in the actual ground bound has an explicit matrix whose self and cross entries retain different prime information. **Proved:** the self entry collapses to two arithmetic cumulatives; the cross entry retains a moving prime tent.
3. **Conjecture:** full Gamma and pole terms cancel the apparent linear-radius main term in the self entry. **Proved:** actual operator-domain admission and its boundary action give both Gamma entries and the exact cancellation.
4. **Conjecture:** the complete pole-plane sign test is one real matrix comparison. **Proved:** arbitrary complex coefficients diagonalize in even and odd directions, giving exactly `|C|≤A`.
5. **Conjecture:** the cross entry exposes an integrated Chebyshev error, with reciprocal-prime contribution controllable independently. **Proved:** exact physical pairing gives the identity below; elementary Mertens bounds the reciprocal correction linearly.
6. **Positive successor:** uniform diagonal/boundary estimates and integrated-error pole exclusion establish an exact fixed-pole RH criterion in [the successor package](weil-fixed-exponential-pole-rh-criterion.md). Its all-aperture sign remains open.

## Exact statements
Set `p_±=1_[-a,a] exp(±x/2)`, `N=2sinh(a)`, `M=2a`, `kappa=-EulerGamma-log(2pi)`, and `X=exp(2a)`. Let `A=Q(p_+)`, `C=Re Q(p_+,p_-)`, `B_a(x)=B(a-x,a+x)`, `B_0=integral B_a`, `B_1=integral exp(x)B_a`. All integrals are on `[-a,a]` unless stated otherwise.

For each visible prime-power index, the literal symmetric prime transport atom has entries

`<T_n p_+,p_+>=2(exp(a)/n-exp(-a))`,

`<T_n p_+,p_->=(2a-log n)(1+1/n)`.

Thus `P_self=2exp(a)M_1(X)-2exp(-a)psi(X)` and `P_cross=sum Lambda(n)(1+1/n)(2a-log n)`. Every prime power in `2≤n≤floor X` remains present.

The Gamma entries are `kappa N-exp(a)+(2a+1)exp(-a)+B_1` and `kappa M-2a²+B_0`. All real exponential weights of `B_a` are integrable, and these boundary masses are nonnegative. The exact polar Gram action then gives

`A=kappa N-exp(a)+(2a+1)exp(-a)+B_1+2MN-P_self`,

`C=kappa M+2a²+N²+B_0-P_cross`.

Substituting `M_1(X)=2a+E_M(2a)` proves

`A=kappa N-exp(a)+(1-2a)exp(-a)+B_1-2exp(a)E_M(2a)+2exp(-a)psi(X)`.

The complete form satisfies

`Q(c p_+ + d p_-)=A(|c|²+|d|²)+2C Re(conjugate(c)d)`

`=(A+C)|c+d|²/2+(A-C)|c-d|²/2`.

Therefore nonnegativity on this plane is exactly `|C|≤A`, equivalently nonnegativity of `Q(p_++p_-)` and `Q(p_+-p_-)`. These pole vectors do not satisfy the two moment constraints. The normalized actual constrained parity ground separately exists with

`4|F(u)|²≤(mu-lambda)[2(A+rC)-2lambda(N+rM)]`, `r=±1`.

Define admitted physical integrals

`D=integral [exp(a-x)-psi(exp(a-x))] dx`,

`R=integral E_M(a+x) dx`.

The source cancellation proves

`C=D+kappa M+exp(-2a)-1+B_0-R`,

`|R|≤(log 4+5)M`,

`|D-C|≤B_0+(|kappa|+log 4+5)M+1`.

Consequently positive literal compression implies `|D|≤A+B_0+(|kappa|+log 4+5)M+1`. This last theorem proves an implication; it does not prove compression positivity.

## Dependency-closed paper proof
The prime atom is supported on the two exact overlap intervals. Multiplying the positive exponential by the same or opposite pole reduces each pairing to an exponential or constant integral. The finite sums then give the cumulative and tent formulas. The actual Gamma L² representative paired with each pole admits the boundary weights; subtract the continuous bulk and evaluate its elementary antiderivative. The rank-two pole operator contributes the exact Gram products. Reflection fixes the two self entries and exchanges the cross entries; the actual cross formula is real, so ordinary complex scalar expansion gives parity diagonalization.

For the integrated-error identity, pair the already identified full source defect with the negative pole. The exponentials cancel pointwise, leaving `B_a+exp(a-x)-psi(exp(a-x))-E_M(a+x)`. Monotonicity of both arithmetic cumulatives on compact intervals proves integrability of the separate errors. Integrate the elementary uniform Mertens bound, retaining interval length `2a`; the residual exponential term lies between zero and one. No numerical approximation or unproved interchange enters.

## Audit
- Scratch checks passed with `lake env lean /tmp/hgt-pole-matrix.zBBHEr/{PrimeMatrix,GammaMatrix,Compression,IntegratedError}.lean`, run separately in the foreground.
- Named final audits passed with `lake --old --log-level=error build GaloisForLFunctions.RHTower.<module>` for each of the four leaves; no full or umbrella build.
- `lake env lean /tmp/hgt-pole-matrix.zBBHEr/Axioms.lean` audited every public theorem and definition. All 32 depend exactly on `[propext, Classical.choice, Quot.sound]`; no added axiom or oracle.
- `python3 scripts/formal_tools.py lint` passed; existing large-file warnings only. `git diff --check` passed.
- No numerical experiments, remote computations, background builds, or commits.

## Remaining mathematical obligation
The all-aperture actual matrix sign remains open. Uniform bounds for `B_0` and `A/exp(a)` hold for every positive aperture, and the integrated-error/resolvent bridge proves exact RH completeness of this fixed physical family in [the successor package](weil-fixed-exponential-pole-rh-criterion.md). The constrained zero-ground exclusion and RH remain open. No route is retired by these identities.
