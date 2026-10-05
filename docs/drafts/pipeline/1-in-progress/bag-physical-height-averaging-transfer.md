# BAG actual physical height averaging and moving-profile transfer

01aw. HARD OPEN. Route BAG; follow U4, not a replacement for its audit.
Corpus: ChiPrimeGaussianCubicMovingMellin, CubicConeMellin,
CubicTransverse, CubicWindowTransition, ChiHyperbolicFourierTransition,
CubicSharpEdges. Search35342 nonpartial66002files, generation1248427=current,
noerrors, refreshincomplete. All20 candidate+20 source statements inspected;
exact physical amplitude/transition/window definitions inspected.

The normalized actual test is L³/N times bagCubicConeLineProfile. Its log
node is exp(-u), its Mellin line is sigma+2pi*i*t. The height window is the
literal smooth bump centered3/2, supported[1,2]. Original cutoff edges
have width N^(1/4), hence relative width N^(-3/4). The sharp/smooth error
is proved at that scale. Replacing these with fixed relative edges is not
paid by the current error theorem. No uniform Schwartz seminorm is known.

Conjecture P1: the full normalized cone profile has a stationary limit
H(x,y)=2pi*integral_R F(Ry)*F(Rx)*conj(F(R))*W(R*x*y), where
F=1_[1,2]*smoothAFECutoff and W is the ACTUAL height window. This formula
is only a conjecture for the actual profile: neither stationary replacement
nor a norm remainder is proved. It follows formally from the corpus exact
bilinear multiplier after scaling r=NR, its dual frequencies by1/N, and
letting multiplier exp(-2pi*i*R*xi*eta/N) tend to1. Dominated convergence
cannot be asserted uniformly for the shrinking-edge Fourier amplitudes.

If P1 holds, its Mellin transform at s_i=1+2pi*i*t_i is exactly the triple
box integral with amplitude
  2pi*F(p)*F(q)*conj(F(r))*W(p*q/r)*q^(s1-1)*p^(s2-1)*r^(-s1-s2).
Thus its three log frequencies are t1,t2,-t1-t2. One integration by parts
in EACH of the independent p,q,r variables suggests the anisotropic bound
C/((1+|t1|)*(1+|t2|)*(1+|t1+t2|)). This uses only uniform first variation
of each cutoff, not arbitrarily high derivatives. It gives axial quadratic
decay and full-plane integrability. An actual-family counterpart plus
convergence in the corresponding source-weighted topology is the target.
Neither the formal stationary triple integral nor this decay bound has yet
been audited. U3's T^54 envelope alone is insufficient for this class.

Exact structural identity exposed by the original phase:
phi=P*Q/R-x*P-y*Q+x*y*R is invariant under
(P,Q,R,x,y)->(lambda*P,mu*Q,lambda*mu*R,x/lambda,y/mu).
The physical height argument P*Q/R is also invariant. Therefore logarithmic
physical scaling fields may transfer Mellin derivatives without N loss.
Their repeated application hits the same cutoff derivatives, so this
identity by itself does not supply the conjectured three-factor decay.
Equivalent invariant coordinates w=P*Q/R,u=x*P,v=y*Q give
phi=(w-u)*(w-v)/w. A rigorous oscillatory/Mellin interchange would expose
a universal kernel and the full three-cutoff height convolution. Absolute
interchange over positive x,y is NOT available from the present formulas.

Next work: finish U4 audit; prove or refute actual height-averaged weak
regularity/tails via the exact multiplier or invariant coordinates. Any
needed arithmetic envelope must match this physical function class;
changing a numerical exponent without enabling that transfer is not a
frontier advance. No physical cancellation, norm saving or RH claim.
