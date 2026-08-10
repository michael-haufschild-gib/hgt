# Route N C12-C13 (2026-08-10)

## C12 exact Route-N/Route-R Krein gauge
Retaining the difference of the two critical-horizon marked channel masses gives
Q_t(p)=p^(-|t|)(p^(-t)-p^t)/p.
For source activation Fisher density d(p)=p/(p+1)^2, define g(p)=p*d(p)=p^2/(p+1)^2.
Then prime by prime, for every real t:
RouteR_critical_wall(t,p)=g(p)*Q_t(p).
Uniformly 1/4 <= g(p) <= 1 and g^-1 <= 4. Thus g and g^-1 preserve ell1 and induce inverse quotient maps on C^Primes/ell1. Route N Krein class is exactly gauge-conjugate to Route R wall class, stronger than previous equality modulo ell1. Q_t is summable iff t=0. Orientation was already in Route N's doublet; positive total energy erased it.

Lean:
formal/GaloisForLFunctions/RHTower/HedenmalmGammaSewnRouteRKreinGaugeBridge.lean
Direct lake env lean passed. Umbrella wired.

## C13 ambient cokernel base-change no-go
For theta Fredholm cokernel conormal g_z(x)=k(x) exp(-i conjugate(z)x), exact weighted mass identity:
normSq(g_z(x))/k(x) = |k(x)*sourceChar(2z,x)|.
Hence weighted mass is integrable whenever |Im(2z)|<1. Every Xi zero has |Im z|<1/2, so every actual Xi root conormal already belongs to ambient weighted theta source space.

On this full conormal strip, joint ambient+Gamma marked landing still has sharp independent condition |Im z|<u. For every fixed 0<u<1/2, z=i*u gives an ambient weighted conormal but fails damping-u marked landing. Therefore no total ambient base change can send all conormals to fixed damping fibre; failure occurs without assuming boundedness or linearity.

Consequent universal principle: completion cannot precede localization. Missing producer must be a singular map on divisor-supported Fredholm torsion before pointwise root evaluation. Root-only landing for every positive damping is formally iff RH; it remains open, not proved.

Lean:
formal/GaloisForLFunctions/RHTower/HedenmalmGammaSewnCokernelBaseChangeNoGo.lean
Direct lake env lean passed. Umbrella wired.

Docs updated:
- docs/drafts/pipeline/1-in-progress/hedenmalm-prime-normal-jordan-grade-separation.md (N.23-N.27)
- docs/drafts/pipeline/1-in-progress/rh-current-frontier-map.md

Status: NOT RH. Do not retry bounded/total ambient conormal maps, ordinary Hilbert-Gram completion, or count Route N/R walls independently.