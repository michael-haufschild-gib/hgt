# RN-P-7ad: exact finite-prefix current compensation

2026-10-04. Formalized: 53 public theorems across four leaves.
Parent: ../../1-in-progress/rn-finite-current-integrated-compensation.md.

Write k for the literal theta source, p=-(log k)', c=p', q=c(0),
J=H(0,0), I=integral t*k'(t)^2, gamma=I/J-q/2>0,
W(x,t)=k(t+x)^2/k(x)^2, and L for the audited interior current profile.
For every T>0 the actual diagonal current satisfies

  lim x->0+ (integral_0^T W(x,t)*Ican(x,x,t) dt)/x
    = integral_0^T W(0,t)*L(t) dt-gamma/2.

Moreover, eventually as T->0+, eventually as x->0+,
the actual weighted current prefix is strictly negative. The node threshold
may depend on T. This establishes signed compensation on short prefixes;
it does not establish the global finite-pair sign or an improper limit exchange.

## Dependency-closed paper proof

Compact node averages extend the actual normalized packet a and primitive B
smoothly across x=0. Their values are -p and t; their node jets are
alpha-(c+p^2)/2 and b, respectively, with alpha=I/J. Source secant averages
extend in the same way, giving Creg=a+s_x B and its continuous node jet C1.
The regularized bulk is

  Greg=W*[snode_x B-(p(t+x)-p(x))*Creg].

It and its node derivative are jointly continuous. Its value at x=0 is
the time derivative of F0=W(0,t)*(t*c-p)/2. Its node jet is G1.
The exact finite-interval transport identity retains the entire endpoint flux:

  integral_0^T W*Ican = integral_0^T Greg-diagonalFlux(x,T),
  diagonalFlux=W*lambda*Creg.

At x=0 the two terms cancel. For fixed T>0, compact differentiation of the
bulk and ordinary differentiation of the endpoint give prefix derivative
integral_0^T G1-F1(T). No uniform domination of Ican/x is assumed.

The moving-tail correlation identity proves
  d/dt secondLeft(t,t)=2*(p+t*c-t*p^2)*k^2,
and hence b'=2*p*b+t*(2*alpha-p^2). Substitution gives the exact identity
F1'=G1-W(0,t)*L(t) for t>0. The actual center jets give F1(0+)=gamma/2;
L extends continuously to zero with value zero. Compact FTC therefore gives
integral_0^T G1-F1(T)=integral_0^T W(0,t)*L(t)-gamma/2.
This tends to -gamma/2<0 as T->0+, proving the stated nested eventual sign.

## Validation

Final foreground sequence48501 exited0 using `lake --old env lean` on:
- ThetaFinitePairPacketExtension.lean (15 public theorems)
- ThetaFinitePairRegularizedBulk.lean (22)
- ThetaFinitePairPrefixLimit.lean (10)
- ThetaFinitePairProfileFlux.lean (6)

All53 public `#print axioms` queries ran in /tmp and returned exactly
propext, Classical.choice, Quot.sound. No additional axiom, unresolved proof,
RH assumption, numerical experiment, heartbeat increase or subagent.
PrefixLimit emits an informational ring-normalization suggestion; all four
source audits exit successfully. Imports are wired into RHTower.lean;
no umbrella or full build was run.

Lint42205 exited1 with15 unrelated unreachable modules and no own-leaf or
forbidden-declaration error. Exact unrelated names are retained in the working
log. Global finite-pair compensation, general anchors, arbitrary rank, and
arithmetic RH transfer remain open.
