# SZ: negative forcing at critical normalization

- Stage: 3-formalized; paper proof and final Lean/axiom audits complete.
- Route: SZ, actual nonlinear prime forcing of the signed ramp age equation.
- Target: there exists c>0 such that every integer tail contains n>=1 with
  D_n < -c*sqrt(n), without any RH or sign premise.
- Objects: M_n=sum_(j<=n) Lambda(j)/sqrt(j), m_n=1+M_n/2,
  U_n=2*sqrt(n)*m_n-n-psi(n)-1, D_n=m_n^2-psi(n)-1.

## Paper proof

Write kappa=-(2+gammaHardyPhaseRate(0))>0. The exact transform of
U(T) is -logDeriv G(s)/(s*(2*s-1)). The source identities for G and
Gamma give central real residue -kappa. For 0<c<kappa, shifting U by
c*exp(T/2) leaves residue c-kappa<0. Apply the compact-head Landau
lemma to U(T)*exp(-T/4)+c*exp(T/4). Its transform is analytic along
the real ray above1/4; no nonreal zero-free premise is used. Thus
U(T)<-c*exp(T/2) cofinally. On each arithmetic cell U+c*sqrt(x)
is a concave quadratic in sqrt(x), so some endpoint also satisfies
U_n<-c*sqrt(n).

For n>=1 set W_n=U_n/sqrt(n). Exact cancellation of the prime jump gives

    (W_(n+1)-W_n)*sqrt(n)*sqrt(n+1)
      =(sqrt(n+1)-sqrt(n))*(psi(n)+1-sqrt(n)*sqrt(n+1)).

Actual Chebyshev Omega-minus yields arbitrarily late n with
psi(n)+1<n, hence decreasing W steps. Omega-plus yields arbitrarily
late increasing steps. After any prescribed cutoff choose a decreasing
step, then a low W value, then an increasing step. A minimum over this
finite interval is internal and no larger than that low value.

At its minimizing index r=n+1 the two adjacent step inequalities give

    sqrt(n)*sqrt(n+1) >= psi(n)+1,
    sqrt(r)*sqrt(r+1) <= psi(r)+1.

Consequently r <= psi(r)+1 < r+Lambda(r). Since
Lambda(r)/sqrt(r) <= log(r)/sqrt(r) -> 0, take the entire interval late
enough that its atom weight is below c/2. The exact equation for W_r<-c
then yields m_r<sqrt(r)-c/4. As m_r>=0,

    D_r=m_r^2-psi(r)-1 <= m_r^2-r < -(c/4)*sqrt(r).

Every weight, endpoint and positive square remains. No assumption on
critical zero locations, a prime asymptotic at square-root precision,
or an eventual sign is made.

## Contribution and limit

Earlier unscaled D escape could vanish after critical normalization.
This mechanism supplies a fixed negative normalized amplitude on every
tail. It does not give eventual negativity, a uniform two-sided forcing
bound, or the canonical-head Gamma--prime--polar inequality.

## Corpus and audit log

- Deep search1222838: partial, compiler coverage pending; candidates,
  source arguments and ingredient sets inspected. No suitable sign
  producer was retrieved. Search misses do not establish absence.
- Source inspected: potential Laplace/escape and first-contact leaves,
  ChebyshevSchmidtOmega, mathlib logarithm-vs-power asymptotics and finite
  minimum selection. No numerical experiment.
- Scratch31233 failed on real/complex cast algebra and exponential
  reassociation. Scratch75107 fixed those and verified the continuous
  critical theorem, but failed on cell unfolding and an unavailable
  square-root exponential name. Scratch85314 passes all three new
  potential declarations, with only propext, Classical.choice, Quot.sound.
- Final potential production audit7468 exited0 without diagnostics.
  Nonlinear valley and forcing proof is in scratch audit40158; it is
  not yet installed or certified.

- Scratch40158 accepted finite-minimum selection and the valley estimate,
  but failed on the multiplied normalized increment, inconsistent cast
  normalization, a one-line tactic scope, and the namespace of mathlib's
  logarithm asymptotic. Scratch44171 repaired these and exited0; the
  unconditional nonlinear capstone has only the standard three axioms.
- New leaf CCMPrimeMomentCriticalEscape is wired once into RHTower.
  Final production audit32271 exited0 without diagnostics. No umbrella build was requested or run.

- Global lint42518 exited1: 37 unreachable-module errors; no
  forbidden declaration or error named CCMPrimeMomentPotentialEscape or
  CCMPrimeMomentCriticalEscape. The earlier lint76951 output was truncated
  on stderr, so42518 captured the complete diagnostics. Existing unrelated
  reachability failures were left unchanged.

## Final verification

- Final commands in formal: `lake --old env lean` on
  `GaloisForLFunctions/RHTower/CCMPrimeMomentPotentialEscape.lean` and
  `GaloisForLFunctions/RHTower/CCMPrimeMomentCriticalEscape.lean`, each
  with its matching `.lake/build/lib/lean/...olean` output. Audits7468
  and32271 exited0 without diagnostics, serial foreground execution.
- Final scratch audit61451 exited0. All9 public declarations across
  the two touched leaves depend only on propext, Classical.choice,
  Quot.sound. Actual mathlib signatures were also checked using `have :=
  @Name`; the first all-public audit31143 failed only on unresolved
  universe levels in that ancillary Finset signature probe. Instantiating
  its carrier types fixed it; no production theorem changed.
- The new leaf has exactly one umbrella import; no umbrella build.
- Global lint42518 remains red only for37 unrelated unreachable modules.
  Neither touched leaf has a lint error. No added axiom or placeholder.
- Eventual primitive sign, uniform critical forcing control, the full
  canonical-head sign and RH remain open. This card closes the critical
  negative-excursion theorem only.
