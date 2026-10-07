# Paper proof: all-order polar differential tail sign

Write s=(-1)^k and f=s F_k. Exact cusp calculus gives

    f(x)=S_Q(x), Q=s*(P_(k+2)-(1/4)P_k),
    deg Q=k+4, leading(Q)=4*pi^2*(2*pi)^(k+2)>0.

The leading term follows from P_j's exact top coefficient 4*pi^2*(-2*pi)^j; lower-degree subtraction cannot change it. Therefore Q(v)>=1 for v sufficiently large. For x>=R>=0 every theta term is nonnegative and the n=1 term yields f(x)>=exp(-pi*exp(2x)). This is a bound on the full theta series. Exact derivative parity gives f(-x)=s*f(x).

The full-series bound in the corpus is |S_Q(x)|<=C exp(x/2) exp(2*d*x) exp(-pi*exp(2x)) for x>=0. Set a=pi/2, V=exp(2x), m=d+1. Since x>=0,

    exp(x/2+2*d*x) <= V^m exp(-x),
    V^m exp(-a V) <= m! / a^m.

The second inequality is the nonnegative m-th Taylor term of exp(aV). Parity extends this to every real x. Thus for some B>0,

    |f(x)| <= B exp(-a exp(2|x|)) exp(-|x|).

Consider the convolution I(y)=integral f(t) f(y-t) dt. It equals s times the autocorrelation of f, hence s times that of F_k. The envelope proves integrability by domination with B^2 exp(-|t|).

If f(t)f(y-t)<0, either t<R or y-t<R. In either case one absolute argument is at least y-R. The full product envelope therefore bounds every negative contribution below by

    -E(y) exp(-|t|), E(y)=B^2 exp(-a exp(2(y-R))).

No portion of the integral is discarded without this bound. On J=(y/2-1,y/2+1], for y>=2(R+1), both arguments are >=R and <=y/2+1. The lower envelopes give f(t)f(y-t)>=L(y), where L(y)=exp(-2*pi*exp(2)*exp(y)). Consequently I(y)+2E(y)>=2L(y), since J has length2 and integral exp(-|t|)=2. Finally 2E(y)<=L(y) for all sufficiently large y: the negative exponent in E is a positive constant times exp(2y), which dominates the exponent proportional to exp(y) in L. The corpus's existing analytic error-absorption lemma establishes this without numerical evaluation. Thus I(y)>=L(y)>0 and proves the claimed all-order sign.

Fourier verification is separate from tail sign. Linearity and the corpus derivative transform give

    FT(F_k)(z)=(-iz)^k*((-iz)^2-1/4)*riemannPhiTransform(1/2+i*z).

At z=+/-i/2 the polynomial factor vanishes; at both Weil evaluations every derivative transform is zero by the existing exact radical theorem. These are actual unconditional identities. F_k is not compactly supported. This proof makes no compact-test admissibility or finite-mixture energy claim. Compact truncation followed by the polar differential operator, including its derivative boundary errors, is the next unpaid construction step.
