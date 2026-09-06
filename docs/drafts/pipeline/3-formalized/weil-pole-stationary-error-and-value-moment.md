# Actual stationary pole error and the independent value moment

Status: formalized and audited. RH remains open.

Leaves: `CCMRestrictedWeilPoleFirstJets`, `CCMRestrictedWeilPoleStationaryError`, `CCMRestrictedWeilPoleLogMoment`, namespace `RHTower`.

Proof chain: actual prime–Gamma pole positivity → square-root integrated Chebyshev control → bounded actual critical resolvent → mathlib RH. These results constrain the stationary locations and identify the additional arithmetic comparison needed for even minimum values.

## Conjecture → proof / fail → pivot

1. The actual first jets should cancel their apparent radius growth and isolate the pointwise prime error. **Proved exactly**, retaining ordinary and reciprocal Mangoldt cumulatives and the complete Gamma boundary slope.
2. The remaining diagonal jet should admit a uniform square-root bound, forcing the same scale for prime error at even stationary points. **Proved**, including actual interior minima on prime-power gaps. No RH premise supplies this estimate.
3. The two arithmetic masses in stationarity might determine the value. **False for nonnegative weights even on genuine prime-power support.** The entire fixed-mass family on 2,3,4 is classified; its cross values fill an explicit nondegenerate interval. This diagnoses generic moment recovery, not the literal Mangoldt source.
4. **Positive survivor:** the actual cross value has one exact additional weighted logarithmic moment, with a necessary and sufficient even-energy lower threshold. Proving that threshold from actual arithmetic, including at stationary minima, remains open.

Starting material: the existing exact chamber, boundary differential, diagonal bound and prime-power gap modules. Corpus searches for logarithmic moments and moment nonidentifiability locate related moment carriers but no source comparison used in these proofs. Every identity below is derived from the admitted finite atoms and boundary primitives.

## Exact first jets

Use `X=exp(2a)`, `kappa=-EulerGamma-log(2pi)`, `M1(X)=sum_{2≤n≤floor X}Lambda(n)/n`, `EM(t)=M1(exp t)-t`, and `L(t)=-log(1-exp(-t))`. Derivatives below are derivatives of the frozen chamber at its own cutoff, so no differentiation through a floor function is asserted.

The cross-slope weight is exactly

`W(a)=sum Lambda(n)(1+1/n)=psi(X)+M1(X)`.

Differentiating the complete chamber expressions and substituting `M1(X)=2a+EM(2a)` gives

`A'_a(a)=2kappa cosh(a)+(3-2EM(2a))exp(a)+(2a-3-2psi(X))exp(-a)+B1'(a)`,

`C'_a(a)=2[kappa+X-psi(X)-exp(-2a)+L(2a)-EM(2a)]`.

The apparent `a exp(a)` term has canceled from the diagonal jet. The exact even first derivative is `2(A'_a+C'_a)`. Consequently every stationary even test satisfies

`X-psi(X)=-A'_a(a)/2-kappa+exp(-2a)-L(2a)+EM(2a)`.

These are exact identities for the actual arithmetic cumulatives, not asymptotic expansions.

## Uniform slope and stationary error bounds

Write the already admitted positive weighted boundary primitives as

`F(a)=exp(a)/2 integral_0^(2a) exp(-t)L(2t) dt`,

`G(a)=exp(-a) integral_0^(2a) exp(t)[L(t)-L(2t)/2] dt`.

For `t≥0`, `L(t)≥0` and `L(2t)≤L(t)`, including the totalized value at zero. Thus `F,G≥0` and `F+G=B1`. Their exact differential law is

`B1'=F-G+exp(-a)L(4a)+2exp(a)[L(2a)-L(4a)/2]`.

For `t≥2`, `L(t)≤1`: `exp(t)≥1+t` bounds `exp(-t)≤1/2`, while monotonicity of log and `log 2≤1` bound the logarithm. Together with `B1≤K_B exp(a)`, `K_B=2log 2+pi+1`, this proves

`|B1'(a)|≤(K_B+4)exp(a)` for `a≥2`.

Let `C_E=log 4+5`, `C_psi=log 4+4`, and

`K_J=2|kappa|+K_B+12+2C_E+2C_psi`.

The corpus bounds `|EM|≤C_E`, `0≤psi(X)≤C_psi X`, together with `a exp(-a)≤1`, imply

`|A'_a(a)|≤K_J exp(a)` for `a≥2`.

Set `K_S=K_J/2+|kappa|+C_E+2`. The stationary equation now yields the unconditional theorem

`a≥2 and E_even,ch'(a)=0 ⇒ |exp(2a)-psi(exp(2a))|≤K_S exp(a)`.

If an actual even-energy minimum lies in the interior of a prime-power gap starting at radius at least two, the previous minimum theorem gives incoming stationarity. Both entire frozen functions agree with the current ones there. The same bound therefore applies at that actual minimum. This theorem does not require the later curvature threshold, provided an actual interior minimum is supplied. Boundary minima are not included.

This controls the location's instantaneous prime error, not the energy value, and does not give the bound at arbitrary radii.

## Exact additional moment in the value

Define the actual finite moment

`H(a)=sum_{2≤n≤floor X}Lambda(n)(1+1/n)log n`.

Expanding every affine cross atom gives, for every real chamber coordinate `s`,

`C_ch(a,s)=C_sm(s)-2s[psi(X)+M1(X)]+H(a)`.

Hence the actual even test is nonnegative exactly when

`2a[psi(X)+M1(X)]-A(a)-C_sm(a)≤H(a)`.

This is a source comparison still to prove. No statement that the two cumulatives determine the logarithmic moment is used.

## Complete fixed-mass classification and sharp value interval

Replace Mangoldt coefficients only in this auxiliary finite model by nonnegative weights `(u,v,w)` at 2,3,4. The fixed mass conditions

`u+v+w=6`, `u/2+v/3+w/4=2`

hold exactly for

`(u,v,w)=(2t,6(1-t),4t)`, `0≤t≤1`.

Solving the two linear equations gives `u=w/2`, `v=6-3w/2`; nonnegativity gives `0≤w≤4`. This proves both directions and exhausts the model.

For the same diagonal and cross kernels as the actual atoms, the model responses are

`D_t(s)=4exp(s)-12exp(-s)`,

`C_t(s)=16s-8log 3-t Delta`, `Delta=13log 2-8log 3>0`.

The strict inequality is proved by `3^8<2^13` and logarithmic monotonicity, using kernel-checked arithmetic rather than a numerical experiment. The diagonal function and cross derivative are identical for every `t`, whereas the cross value fills exactly

`[16s-13log 2, 16s-8log 3]`.

Both endpoints are attained. Every intervening value has the explicit parameter `t=(16s-8log 3-y)/Delta`. The Lean range theorem is an equivalence including this realization, not merely a pair of bounds.

Adding a common smooth source and subtracting these atom responses preserves equality of the derivatives while shifting the energy height. These weights are not the literal Mangoldt coefficients. This is a rigorous obstruction to generic recovery from positivity and the two masses; it is not a counterexample to actual Weil positivity or RH. The [closed shortcut card](../5-failed/weil-pole-first-jet-value-recovery.md) records the positive survivor.

## Verification

- Foreground `lake env lean` passed for `/tmp/hgt-pole-stationary.HKnfTH/Jet.lean`, `Bounds.lean`, and `Moment.lean`.
- All three named leaf builds passed with `lake --old --log-level=error build GaloisForLFunctions.RHTower.<leaf>`. The leaves are wired into `RHTower.lean`; no full or umbrella build was run.
- `lake env lean /tmp/hgt-pole-stationary.HKnfTH/Axioms.lean` audited all 34 public declarations (26 theorems, 8 definitions): exactly `[propext, Classical.choice, Quot.sound]`. No added axiom or computation oracle.
- `python3 scripts/formal_tools.py lint` passed, with existing large-file warnings. `git diff --check` passed. All owned Lean/Lake sessions completed; an unrelated concurrent `ThetaTiltLogDensity.lean` check was left untouched.
- No numerical experiment, remote computation, background build, subagent, or commit.
