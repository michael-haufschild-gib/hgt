# RN: positivity of the matched finite-pair transport packet

2026-10-04. Formalized in ThetaFinitePairPacketTail and ThetaFinitePairPacketPositivity; 11 public theorems.
Route RN; follows rn-finite-pair-sturm-crossing.md and its source classification.
Target is the actual N_x(t)=a_x(t)+s_x(t)B_x(t)>0 for every x>0,t>=0.
This is not the full Schur coordinate-current sign.

Notation: k=actual theta source, p=-(log k)', c=p', v=c',
H=actual first-moment kernel, J=H(0,0)>0, h=H(0,x)>0.
O=hH(t,t)-JH(t,t+x)>0 for t>0,
a=(1-(h/J)k(t)/k(t+x))/x, B=O/(xJk(t)k(t+x)),
s=(p(t+x)-p(t))/x, j=ts-p(t), F=s'-2js.

The exact source ODEs already audited for a,B yield
  N'=(p(t)+p(t+x)+2j)N+F B.
The finite-pair crossing theorem gives a unique tau>0 with F positive before
tau, zero there and negative afterward. j>0 and O>0 on t>0.

Set rho=k(t)k(t+x), Z=rho*N and
  W(t)=exp(-2*integral_0^t j(u)du)*Z(t).
All functions are continuously differentiable on the nonnegative ray. Since
rho'=-(p(t)+p(t+x))*rho, the exact derivative is
  W'=exp(-2*integral_0^t j)*F*O/(xJ).
Therefore W strictly increases on [0,tau] and strictly decreases after tau.
The old normalized-row theorem gives H(0,x)/(k(0)k(x))<J/k(0)^2;
thus a(0)>0 and W(0)=k(0)k(x)a(0)>0.

Here is the complete endpoint argument, retaining the actual source.
Decreasing c/p implies that p(t+x)/p(t) decreases for t>0, by differentiation.
Thus for t>=1,
  0<s(t)<=C_x*p(t), C_x=p(1+x)/(x*p(1)).
The positive-kernel identity for O gives 0<O<=h*H(t,t). The audited actual
source comparison p(t)*H(t,t)<t*k(t)^2 therefore yields
  0<=s(t)*O(t)<=C_x*h*t*k(t)^2 ->0
by weighted Schwartz decay.
Meanwhile
  rho*a=(k(t)k(t+x)-(h/J)k(t)^2)/x ->0.
Thus Z=rho*a+sO/(xJ)->0. Since j>=0 on the positive ray, the exponential
factor lies in (0,1] there, so W->0 as well. No asymptotic series or numerical
rate is needed.

For t>=tau, strict decrease and zero limit imply W(t)>0: monotonicity first
gives W(t+1)>=0, then W(t)>W(t+1). For 0<=t<=tau, W(t)>=W(0)>0.
Division by the positive exponential and rho proves N_x(t)>0 everywhere.

The proof is source-specific. Gaussian curvature gives F=0 and N=0, so the
strict conclusion is not asserted for arbitrary positive kernels. It is
compatible with the Gaussian saturation recorded in the parent card.

Validation completed 2026-10-04:
- Both leaf exports with `lake --old env lean -o ...` passed with empty diagnostics.
- Required direct audits `lake env lean GaloisForLFunctions/RHTower/ThetaFinitePairPacketTail.lean`
  and `lake env lean GaloisForLFunctions/RHTower/ThetaFinitePairPacketPositivity.lean`
  passed with empty diagnostics.
- All11 public theorem axiom queries passed in /tmp: exactly propext,
  Classical.choice, Quot.sound. No added axiom or analytic premise.
- Both leaves wired into GaloisForLFunctions/RHTower.lean; no umbrella build.
- Formal lint reports14 unrelated unreachable modules; no own-leaf error or
  forbidden proof declaration.

The actual N ODE, weighted source-tail endpoint, damping and complete positivity
transfer are closed. Full coordinate-current compensation still has an additional
signed coefficient. The canonical-speed certificate in
rn-finite-pair-canonical-speed.md proves A*N<0 while retaining that coefficient.
General anchors, arbitrary rank and arithmetic RH transfer remain open.
