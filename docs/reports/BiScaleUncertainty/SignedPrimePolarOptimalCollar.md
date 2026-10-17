# Signed optimal collar compensation

Let f be any real compact continuous source, h its autocorrelation, and g its
backward collar average at A=exp(a), width d=exp(b). Set R=h(0), B=∫g²,
C=∫gf=H(0), M=mass N, and η=exp(c)>0. The previous exact gauge package gives

U=3(10+e(L)²)B+3(2T+d)[2(R-h(d))/d²+B/4]∫₀ᴸe²,

where L=log(N+2), e(x)=exp(-x/2)(ψ(exp x)-exp x), and T is the actual source
radius. Every integral is admitted by the previous packages. In particular
Q_N(g)≤U and U≥30B≥0.

## Actual signed trial family

For every real t, actual compact source linearity gives
P_N(f)=tP_N(g)+P_N(f-tg). The exact remainder energy is

||f-tg||²=R-2tC+t²B.

The weighted square inequality and the admitted mass bound on P_N(f-tg) give

Q_N(f)≤F(t):=(1+η)t²U+(1+1/η)M²(R-2tC+t²B).

No sign is imposed on C or t. Thus negative covariance can be exploited by a
negative smoothing coefficient. The primes and the full polar continuum remain
in the actual packet throughout this split.

## Exact minimizer and degeneracy

Define D=(1+η)U+(1+1/η)M²B, E=(1+1/η)M²C, t*=E/D, and

V=(1+1/η)M²R-E²/D.

Real zero division is interpreted as zero. Then **for every real t**,

F(t)-V=D(t-t*)².

Proof: D≥U≥30B≥0. If D≠0, expand and complete the square. If D=0, then
B=0. Integral Cauchy–Schwarz gives C²≤BR=0, so C=E=0. The quadratic is
constant and the displayed equality holds with t*=0. This discharges the
degenerate case using actual source geometry, with no nonvanishing premise.

Consequently Q_N(f)≤F(t*)=V≤F(t), V≥0, and the exact classification is

F(t)=V if and only if D=0 or t=t*.

This is optimality within this certified scalar trial family, not among all
possible packet bounds or all smoothing sources. Quadratic minimization itself
is not claimed as a new theorem of analysis.

## Comparison and global transport

Define Z=min(M²R,V). Then Q_N(f)≤Z≤M²R. At η=1, F(1) is exactly the
previous correlationGaugeBound, so Z≤correlationGaugeBound. Thus this choice
never worsens either of those two existing bounds. For other η, the comparison
is with its corresponding weighted trial family.

The exact threshold for strict improvement over the mass estimate is

Z<M²R if and only if M²R/η<E²/D.

It includes every degenerate case with the same zero-division convention.
Thus the signed covariance must pay for the weighted-splitting overhead; the
mere availability of a smooth collar does not assert a strict gain.

At N=N₀(f)+K, existing global coherent transport gives

(D∞(h)-W∞(u,v))²≤Z·δ(u,v),

where δ(u,v) is the actual squared source-to-transport-collar distance.
For any independent positive parameter τ=exp(r), existing Lévy transport gives

|D∞(h)-W∞(u,v)|≤τJ(u,v)
 +Z/[2τ exp(2v)]∫_[exp(u),exp(u)+exp(v)]exp(-y/2)sinh(y)dy.

Both substitutions preserve order because δ and the reciprocal-weight integral
are nonnegative. No derivative of f, arithmetic error bound, grid blindness,
nonzero source, or nonzero denominator is assumed.

This package resolves the fixed-coefficient loss and supplies an exact signed
compensation certificate. It does not remove the actual residual, prove a
cutoff-uniform bound, or establish an arithmetic asymptotic. Corpus searches
found finite-partition Gram optimization and smooth gauge bounds, not this
actual collar compensation endpoint. No external novelty claim.

Both Lean leaves pass direct `lake --old env lean <leaf> -o <leaf.olean>` with
empty diagnostics. Twelve endpoint axiom reports in `/tmp/spp7-final-axioms.log`
contain only propext, Classical.choice, Quot.sound. Printed main signatures have
only actual source and numerical inputs. Imports are wired; index refresh passes.
Global lint reports six unrelated missing umbrella imports, listed in
`SignedPrimePolarTransport-FACTS.md`; there are no task-local errors.
