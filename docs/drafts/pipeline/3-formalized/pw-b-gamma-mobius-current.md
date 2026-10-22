# PW-B actual Gamma/Möbius source and complete Euler current

- **ID:** PW-B-GAMMA-MOBIUS-CURRENT-2026-09-11
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean 4)
- **Statement:** The literal half-density Gamma source has a nonzero, convergent canonical Möbius preimage. Positive-integer dilation reconstructs the source exactly; the full von Mangoldt current equals its convergent Möbius-log series. Reflection transports that current with the complete source retained.

## Source and proof

For `y>0`, the original log profile `q(u)=exp(u/2-exp(u))` pulls back to
`Q(y)=q(log(y))=sqrt(y)*exp(-y)`. Define

`M(x)=sum_n mu(n)*Q(n*x)` and
`E(x)=-sum_n mu(n)*log(n)*Q(n*x)`.

Thus `M(x)=sqrt(x)*sum_n mu(n)*sqrt(n)*exp(-n*x)` for `x>0`.
The factor `sqrt(n)` is retained; this is not the ordinary Möbius--Laplace
source. Values of the auxiliary pullback at zero are irrelevant because all
series terms carrying a zero arithmetic index have zero coefficient.

For `c>0`, multiply the exponential tangent bound at `u-log(c)` by `c`:

`c*u-exp(u) <= c*log(c)-c`.

At `c=5/2` and `u=log(y)` this gives `|Q(y)| <= C/y^2`, where
`C=exp((5/2)*log(5/2)-5/2)>0`. This explicit one-sided bound avoids the
two-sided exponentially decreasing Schwartz condition which the actual
Gamma profile fails.

For coefficients `b(0)=0` with `sum_m |b(m)|/m^2` convergent, the absolute
value of `b(m)*mu(n)*Q(m*n*x)` is bounded by

`(C/x^2)*(|b(m)|/m^2)*(1/n^2)`.

The zero-product terms vanish. The double majorant is summable. Taking
`b(m)=1` for positive `m` proves convergence for Möbius reconstruction;
taking `b=Lambda` uses the corpus's unconditional convergence of
`sum Lambda(m)/m^2`. Grouping by the product `m*n` is now justified.
The two exact divisor identities are

`sum_(d|N) mu(N/d) = [N=1]`,
`sum_(d|N) Lambda(d)*mu(N/d) = -mu(N)*log(N)`.

They yield, for every `x>0`,

`sum_(m>=1) M(m*x)=Q(x)` and `sum_m Lambda(m)*M(m*x)=E(x)`.

The Möbius-log series is itself absolutely summable by the same source bound
and the known convergence of `sum log(n)/n^2`. The first identity, together
with `Q(1) != 0`, proves that `M` is nonzero somewhere on the positive ray.

For `F(t)=M(exp(t))`, the complete log-coordinate current is
`J_Lambda F(t)=E(exp(t))`. Write `T f(t)=a(t)*f(-t)` for the already
proved singular reflection, and
`K_Lambda f(t)=sum_n Lambda(n)*a(t)/a(t-log(n))*f(t-log(n))`.
Its exact transport gives

`K_Lambda(TF)(t)=a(t)*E(exp(-t))`.

The transformed series converges. This is the inverse-dilation current of
the reflected response; no claim identifies it with the outgoing current
of that response. The full Möbius-log source remains on the right.

## Scope and remaining obstacle

This closes the actual-source admission gap in the transported arithmetic
identity. It does not prove that `E` vanishes, construct a physical operator
domain, identify Xi occurrences, prove a Mellin continuation, or establish RH.
The arithmetic current `E` is not identified here with the differential
forcing of the Gamma profile or of its Möbius preimage.

The proof chain remains actual arithmetic source -> source-forced fixed-grade
PW balance -> zero Deninger Ward charge -> RH. The missing producer must
derive balance or its full boundary correction from this source. The next
admission test concerns inverse-connection homogeneous modes and the actual
source's behavior at the other end of the ray; outgoing-current convergence
alone does not supply the desired uniqueness there.

## Verification

Scratch verification, direct leaf checking, the targeted final leaf build,
formal lint and all 15 public theorem axiom audits passed. Dependencies are
only `propext`, `Classical.choice` and `Quot.sound`; no added axioms or proof
holes. No numerical experiments were used. All owned Lean processes finished.

- Module: `formal/GaloisForLFunctions/RHTower/ThetaCusp/ThetaCuspHawkingParikhWilczekGammaMobiusCurrent.lean`.
- Closed package: `RHTower.pwGammaMobius_source_current_closed`.
- Actual reflected connection: `RHTower.pwGammaMobius_reflected_connection`.
- Scratch: `/tmp/pwb-gamma-current.lean`; axiom audit:
  `/tmp/pwb-gamma-current-axioms.lean`.
- Checks used `lake env lean` and only the named leaf for final `lake build`.
  The umbrella import is wired; no umbrella or full build ran.
- Logs: `/tmp/pwb-gamma-current-{scratch,direct,build,axioms,lint,index}.txt`.
  An informational `ring_nf` hint remains; the build succeeds.
- Formal indices refreshed; public declaration names checked for source
  collisions; `git diff --check` passed.

## Search and method audit

Three deep searches covered source exponential bounds, arithmetic product
fibres and coercivity modulo a kernel. Declarations, source arguments, stored
methods and proposed ingredient sets were inspected; coverage is partial.
The direct source bound and arithmetic identities were verified against the
current Lean toolchain. A retrieved gapped pseudo-inverse requires symmetry,
a specified kernel and transverse coercivity not supplied by this source;
an entire-function polynomial classification likewise retains its growth
hypothesis. Neither is used as a Ward cancellation premise.
Artifact: `../1-in-progress/pw-b-gamma-current-searches.json`.

Broad arXiv searches on polymers, resetting, coercivity and pinning reached
July/August 2026 papers. The [memory coercivity analysis](https://arxiv.org/html/2607.12482v1)
distinguishes positive dissipation from a uniform lower bound; the
[ENO parity analysis](https://arxiv.org/html/2607.19283v1) retains kernel
obstructions in its positive estimates. The [pinning paper](https://arxiv.org/abs/2607.19732)
separates covariance from a bulk barrier. These motivate checking retained
homogeneous modes. Their hypotheses are not identified with the arithmetic
source, and no external theorem enters the formal proof.
