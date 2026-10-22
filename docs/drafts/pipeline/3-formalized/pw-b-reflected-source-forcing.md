# PW-B reflected forcing and the complete inverse-dilation current

- **ID:** PW-B-REFLECTED-FORCING-2026-09-11
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean 4)
- **Statement:** Positive-gain reflection changes the connection shift and the full forcing, and conjugates the complete arithmetic current to a weighted inverse-dilation current. Its Gamma-source forcing mismatch persists at every shift. The inverse-gain companion fixes the Gamma source but preserves a nonzero forcing instead of eliminating it.

## Proof and positive survivor

Write `phi(t)=sinh(t)-t/2`, `p(t)=cosh(t)-1/2`, `a(t)=exp(2*phi(t))`,
`T f(t)=a(t)f(-t)` and `L_z f=f'-(p+z)f`. Oddness of `phi` gives `T*T=1`;
evenness of `p` and `a'=2*p*a` give the exact forced identity
`L_(-z)(Tf)=-T(L_z f)`. At a common shift this is
`L_z(Tf)=-T(L_z f)-2*z*Tf`. Neither term can be dropped.

For the literal Gamma profile `q(t)=exp(t/2-exp(t))`, direct differentiation gives
`L_z q=r_z=(1-exp(t)-cosh(t)-z)*q(t)`. At the reflection-fixed point `t=0`,
`r_z(0)=(-1-z)*q(0)` while `L_z(Tq)(0)=(1-z)*q(0)`. Their difference is
`-2*q(0)`, nonzero and independent of `z`. Thus no shift makes these complete
forcings agree. The earlier domain uniqueness theorem cannot identify this pair.
The positive survivor is the exact transformed forcing and its nonzero local
source term, not a vanishing Ward law.

The strongest positive companion uses `R f(t)=a(t)^(-1)*f(-t)`. The literal
carrier identity is `a(t)*q(t)=q(-t)`, so `R q=q`. For the inverse connection
`Lminus_z f=f'+p*f-z*f`, its full forcing is
`rminus_z(t)=(-sinh(t)-z)*q(t)`. This satisfies the same-shift reflected forcing
identity `-R(rminus_z)-2*z*Rq=rminus_z` at every complex `z`.
Thus changing the gain orientation restores exact source fixation and complete
forcing covariance, but does not select a spectral shift. At zero shift the
forcing is still `-sinh(t)*q(t)`, which is not the zero function. The negative
statement above concerns `T`, and is not a prohibition of this companion `R`.

For arbitrary coefficients `c(n)`, put `J_c f(t)=sum_n c(n)*f(t+log(n))` and
`K_c f(t)=sum_n c(n)*a(t)/a(t-log(n))*f(t-log(n))`. Since `a` never vanishes,
each term of `K_c(Tf)(t)` is exactly `a(t)` times the corresponding term of
`J_c f(-t)`. Consequently summability is equivalent at those points, and
`K_c(Tf)=T(J_c f)` for the complete sums. This is an inverse-dilation current;
it is not the original outgoing current applied to `Tf`.

Apply this exact transport to the corpus's canonical Möbius preimage
`F_h(t)=deningerMobiusPreimage h (exp(t))`. For its exponentially decreasing
Schwartz source, the existing full arithmetic identity is
`J_Lambda F_h(t)=deningerMobiusDerivative h (exp(t))`. Transport retains the
entire Möbius-log source on the right. It does not set that source to zero.
The bare Gamma profile does not decay faster than every exponential at the
negative end; it is not silently identified with this Schwartz source.

This domain distinction has an explicit witness: at `t=-v`, `v>=0`, the
unit-exponent weighted norm of `q` is `exp(v/2-exp(-v))`. Since `exp(-v)<=1`
and `exp(x)>=x+1`, choosing `v=2*(|C|+2)` makes that norm exceed any proposed
bound `C`. Thus no exponentially decreasing Schwartz source equals `q`.
This excludes that particular source-class identification; it does not exclude
extending the arithmetic convolution proof under weaker, one-sided decay.

## Remaining RH obligation

Original arithmetic source -> source-forced fixed-grade PW balance -> zero
Deninger Ward charge -> RH. Exact current conjugation and correct forcing are
necessary transport data. A producer must still derive the required equality or
boundary correction on the actual source. No Xi occurrence or RH proof is claimed.

## Verification

Paper identities, source-domain obstruction, scratch formalization, direct leaf
checking, the targeted final leaf build and formal lint passed. All 18 public
theorems passed the axiom audit with only `propext`, `Classical.choice`, and
`Quot.sound`. All owned Lean processes finished. The prior uniqueness theorem remains specific to the positive
connection and its stated arithmetic admission; it is not transferred to the
inverse connection.

- Module: `formal/GaloisForLFunctions/RHTower/ThetaCusp/ThetaCuspHawkingParikhWilczekReflectedSourceForcing.lean`.
- Positive survivors: `pwReflectedMobius_connection`,
  `pwLogInverseGainReflection_gamma_fixed`, and
  `pwGammaInverseConnectionForcing_reflected_balance` in namespace `RHTower`.
- Closed obstructions: `pwGamma_reflected_same_forcing_impossible`,
  `pwGammaInverseConnectionForcing_zero_ne_zero`, and
  `pwGammaSource_not_deningerExpSchwartz`.
- Scratch: `/tmp/pwb-reflected-forcing.lean`; axiom audit:
  `/tmp/pwb-reflected-forcing-axioms.lean` (18 public theorems).
- Checks used `lake env lean` and only the named leaf for final `lake build`.
  The module is wired into `GaloisForLFunctions.RHTower`; no umbrella build ran.
- Logs: `/tmp/pwb-reflected-forcing-{direct,build,axioms,lint,index}.txt`.
  Build emits an informational `ring_nf` hint but succeeds; no proof hole is used.
- Formal indices refreshed; public declaration names checked for source collisions;
  `git diff --check` passed. No numerical experiments or conditional RH theorem.

## Search and method audit

Five deep searches examined inverse-dilation conjugation, Möbius preimage bounds,
reflection forcing, one-sided Laplace decay and inverse-gain source fixation. Dilation/Sonin identities supply
transport mechanisms, not forcing cancellation. Adiabatic Möbius bounds still
use the exponentially decreasing source. A proposed ingredient set mixed
unrelated measure derivatives with existing energy invariance and was rejected.
A lexical `Mobius expShift` query had no hits. Broadening found twisted Möbius
Laplace sources and Mellin kernels for a source-domain follow-up. Saved partial
coverage and stored proof methods: `../1-in-progress/pw-b-reflected-forcing-searches.json`.

Broad arXiv renewal, sewing, screening and memory searches found the September
[range-renewal paper](https://arxiv.org/html/2609.05290v1). Its geometric
smoothing obtains local masses using conditional discovery gaps and uniform
integrability; those probabilistic hypotheses are not available for this signed
arithmetic source. The recent [second-order renewal paper](https://arxiv.org/html/2608.06392v1)
separates integrated-tail and local corrections. Its representative Tauberian
transfer requires positivity and eventual monotonicity; neither is supplied
for the Möbius source. No theorem from either paper is imported. The August
garment-sewing result is unrelated to the required arithmetic forcing.
