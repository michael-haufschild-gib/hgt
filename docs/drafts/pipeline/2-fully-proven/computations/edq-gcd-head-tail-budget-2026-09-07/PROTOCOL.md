## Full-tail closure attack: reciprocity and the cost of splitting the source

The primary [Bettin--Conrey formula (13)](https://msp.org/ant/2013/7-1/ant-v7-n1-p08-p.pdf)
expresses the fractional-part autocorrelation using the Vasyunin sums V.
Combining that formula with the corpus's exact normalized generator gives,
for positive h,k, g=gcd(h,k), a=h/g and b=k/g, the paper identity

`2hk*G_BD(h,k)=(k-1)log h+(h-1)log k
 +pi*(V(1/h)+V(1/k)-g*V(a/b)-g*V(b/a))`.

All universal constant terms cancel under this normalization. The identity
uses the complete autocorrelation before subtracting its three normalization
terms; it does not replace the actual weighted Gram by a uniform period mean.
For coprime balanced h,k of size N, the elementary complete cotangent bound
`|V(h/k)|<=C*k*log k` still permits an O(N log N) pairwise absolute budget.
The required saving is in the signed coefficient-weighted aggregate. The
reciprocity relation for c_0 uses a modular inverse in passing from V to c_0;
the original Möbius coefficient cannot be silently replaced by the coefficient
at that inverse. No new Lean representation module is being built from this
formula without a successful estimate of that signed aggregate.

Before assuming that the initial polynomial must cancel predominantly against
the later tail, freeze a direct diagnostic using the already computed complete
gcd groups. For the same eight raw/tapered sources, split each exact group at
k=X (X=M for raw, X=M/4 for the taper). Write C_r=H_r+T_r. Also define
`K_r=sum_(gcd(d,e)=r)a(d)a(e)/(de)` and
`P_r=K_r*sum_(k<=X)k/(k+1)`, the exact quadratic head contribution.
Compute H_r by the actual finite residue Gram, retaining all affine offsets;
use the stored complete C_r intervals to bound T_r. The new unknown is the
budget lost by separating these actual pieces, not their signed total.

Two predeclared finite tests, at the same threshold four as the full-group
experiment: (A) `sum_r |H_r|+sum_r |T_r|<=4D`; (B)
`sum_r |P_r|+sum_r |H_r-P_r|+sum_r |T_r|<=4D`.
Report every group's head, polynomial, corrected head and tail interval,
including failures; do not fit thresholds or add scales after seeing results.
Failure of (A) directs the next proof attempt to complete groups. Failure of
(B) with (A) surviving means polynomial subtraction helps algebraically but
its separate absolute budget loses the observed cancellation. Passing these
finite tests is guidance only and supplies no uniform or Lean bound.

Run eight independent Python workers on the authorized RunPod under a
60-second limit, reusing the previous full-source results instead of recomputing
their tails. Validate divisor inversion against the direct gcd Gram at M=64;
validate the full initial sum against `F(k)=k*H-1` through X, and verify
`sum_r K_r=H^2`. Keep the existing analytic infinite-tail bounds and distinguish
floating-point sensitivity from formal numerical certification.

