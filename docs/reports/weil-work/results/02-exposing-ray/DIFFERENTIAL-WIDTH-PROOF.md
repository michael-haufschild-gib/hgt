# Paper proof: subcritical translation width

## Full-theta envelope

The corpus defines Phi^(k)=S_(P_k) as the complete cusp series and proves exact derivative parity. For any fixed polynomial Q and x>=0 its full-series estimate is

    |S_Q(x)| <= C_Q exp(x/2+2*deg(Q)*x) exp(-pi*exp(2x)).

Fix 0<a<pi, d=pi-a, m=deg(Q)+1, V=exp(2x). Then exp(x/2+2*deg(Q)*x)<=V^m exp(-x). The m-th nonnegative Taylor term of exp(dV) gives V^m exp(-dV)<=m!/d^m. Therefore |S_Q(x)|<=B_Q exp(-a exp(2x)) exp(-x). Derivative parity extends the norm bound to all real x. The same proof applies to the polar derivative polynomial P_(k+2)-P_k/4, preserving the previous source results.

## Uniform finite synthesis

Fix orders k_j and their positive envelope constants B_j. Let H=1+sum_j B_j. Then every B_j<=H. If |x_j|<=R, triangle inequality gives |t|-R<=|t-x_j|, hence

    |Phi^(k_j)(t-x_j)|
      <= H exp(R) exp(-a exp(-2R) exp(2|t|)) exp(-|t|).

Put B=H exp(R)>0 and M(c)=sum_j |c_j|. Triangle inequality for the complete complex sum proves

    |f_c,x(t)| <= B M(c) exp(-b exp(2|t|)) exp(-|t|),
    b=a exp(-2R)>0.

This retains all coherent complex interference. The envelope constant B M(c) is allowed to be zero, so no nonzero-source premise or artificial additive coefficient mass is needed.

## Actual correlation and integer trace

For real t,y, |y|<=|t|+|t-y| and the arithmetic-geometric mean bound imply

    exp(2|t|)+exp(2|t-y|) >= 2 exp(|y|).

Also exp(-|t-y|)<=1. Thus

    |f(t)*conj(f(t-y))|
      <= B² M(c)² exp(-2b exp(|y|)) exp(-|t|).

The right side has integral 2B² M(c)² exp(-2b exp(|y|)). Continuity and this domination prove integrability of the full complex product, including every cross term. The Bochner norm inequality bounds the actual Weil autocorrelation by that integral. Adding its two values at +/-log(n), then taking real part, gives

    |atomCoeff(f,n)| <= 4B² M(c)² exp(-2b*n), n>=1.

No formal integral assigned zero for a nonintegrable source is used. This is the quantitative positive tail theorem, valid for every a<pi.

## Uniform separation and amplification

Let r0=2*pi*exp(-2), the already formalized literal exposing decay rate. If R<1, choose a=pi*exp(R-1). Then 0<a<pi and

    s=2a exp(-2R)=2*pi*exp(-(R+1)) > r0.

Set r=(r0+s)/2 and delta=s-r>0. The literal lower-envelope theorem gives D>0 with eventually w(n)>=D exp(-r*n), where w=exposingWeight. The exact exponential product identity turns the previous estimate into

    |atomCoeff(f,n)| <= (4B²/D) M(c)² exp(-delta*n) w(n),

uniformly over c and allowed positions. No division by early zero or negative values of w occurs.

For a finite signed mixture, triangle inequality and finite-sum linearity yield the same bound with M(c)² replaced by S=sum_i |alpha_i| M(c_i)². Every row and signed weight remains present. If |T(n)|>=w(n), eventual strict positivity of w permits cancellation, and multiplication by exp(delta*n) gives exp(delta*n)<=C*S. This is a necessary exponential coefficient budget for matching a late exposing coefficient.

For fixed data, C*S*exp(-delta*n) tends to zero by geometric-sequence convergence. Thus for every epsilon>0, eventually |T(n)|<=epsilon*w(n). If T(n)=q*w(n) eventually with q nonzero, choose epsilon=|q|/2 and contradict w(n)>0. This proves the fixed-mixture no-go along with its quantitative positive survivor.

## Arbitrary centers and limitations

Substitution t-s in the absolutely integrable autocorrelation proves atomCoeff(f(.-s),n)=atomCoeff(f,n). Recenter each row independently: x_ij becomes x_ij-s_i, with unchanged trace and coefficient budget. Consequently the amplification law applies to arbitrary windows of total translation width below two.

The literal unit-shift source uses endpoints +/-1, and its existing autocorrelation expansion explains the slower ray exponent r0. Strict width <2 is essential. This proof does not classify width-two sources or their exact trace proportions.

S is homogeneous under compensating source/weight rescaling but is not an intrinsic norm. Large coefficients can cancel when translations cluster. No energy estimate in terms of S follows. Derivative orders growing with n, unbounded-width families, arbitrary compact polar tests, finite-head repair, and the universal WP02 energy lower inequality all remain outside this theorem.
