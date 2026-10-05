# BAG full physical-window hyperbolic transition

- ID: C28.56ag.4, continuation01a9.
- Route: complete signed physical BAG cubic.
- Parent: ../1-in-progress/bag-complete-hyperbolic-transition-action.md.
- Status: dependency-closed paper proof; both production leaves and all19
  public declaration axiom audits passed. See the matching P3 card.
- Scope: exact two-coordinate physical slice for EVERY r>0 and x,y,
  with every Mellin frequency and the entire edge transition retained.
  No signed cubic saving or full lattice Poisson transfer is claimed.

## Statement and actual amplitudes

Write e(u)=exp(2*pi*i*u). For Schwartz f,g on the real line set

    T_r(f,g)(s,t) = integral_(xi,eta)
      hat(f)(xi)*hat(g)(eta)*e(s*xi+t*eta-r*xi*eta) dxi deta.

The product is absolutely integrable: both Fourier transforms are Schwartz
and the character has norm one. For every r>0,

    integral_q integral_p f(p)*g(q)*e(p*q/r+x*p+y*q) dp dq
      = r*e(-r*x*y)*T_r(f,g)(-r*y,-r*x).                 (1)

Both physical amplitudes are retained. This is not a Taylor expansion of T_r.

For an actual smooth band cutoff eta at scale N>1 define

    f_tau(p) = eta(p)*V(p/N)/log(p) * exp(-i*tau*log(p)),
    C_R(tau) = (2*pi)^(-1)*M(i*tau)*exp(i*tau*log(R)),

where V is the LITERAL smoothAFECutoff and M is the entire Mellin transform
of the LITERAL bagPhysicalHeightWindow W from ag.af.2b. Each f_tau is Schwartz
and has the same pointwise norm as f_0. The complete physical window slice is

    J(N,eta;r,x,y) = integral_q integral_p
      f_0(p)*f_0(q)*W(p*q/(r*N))*e(p*q/r+x*p+y*q) dp dq.

Then, absolutely convergently in tau,

    J(N,eta;r,x,y) = integral_tau C_(r*N)(tau) *
      r*e(-r*x*y)*T_r(f_tau,f_tau)(-r*y,-r*x) dtau.      (2)

The source's already proved smooth-band comparison supplies an unconditional
family eta_N with N^(1/4)-width edge strips whose signed sharp/smooth cubic
difference is o(N/log(N)^2). Thus the actual family, not an assumed test
regularity or summability hypothesis, admits (2) for all sufficiently large N.

## Proof

1. Invert the eta-coordinate Fourier transform in T_r. Absolute product
   integrability is the product of the two Fourier L1 norms, so this gives

       T_r(f,g)(s,t) = integral_xi hat(f)(xi)*e(s*xi)*g(t-r*xi) dxi.

   At s=-r*y,t=-r*x, substitute q=-r*x-r*xi. The Jacobian is r.
   The remaining Fourier integral is exactly the p-integral in (1).
   Absolute integrability of the physical product follows from f,g in L1.
   No integral of a bare plane wave is interpreted as a delta distribution.

2. The actual formula V'(p)=-exp(-(log p)^2/4)/(2*sqrt(pi)*p) makes V smooth
   to EVERY order on p>0: its derivative is smooth there, and the derivative
   characterization of C-infinity applies. For p>1, all factors of f_tau are
   smooth and log p is nonzero. At p<=1, eta vanishes in a neighborhood because
   N>1. Compact support comes from eta. This proves the asserted Schwartz
   membership even for the original scale-dependent edge cutoffs.

3. Apply the corpus's full Mellin inversion on real part zero. On p,q,R>0,

       W(p*q/R) = integral_tau C_R(tau) *
         exp(-i*tau*log(p))*exp(-i*tau*log(q)) dtau.

   This follows from log(p*q/R)=log p+log q-log R. The entire frequency line
   remains. Each Mellin phase has unit modulus, and M(i*tau) is integrable.

4. Substitute this identity into J. The full three-variable absolute majorant
   is (2*pi)^(-1)*|M(i*tau)|*|f_0(p)|*|f_0(q)|, which is integrable by the
   product L1 theorem. Fubini is therefore justified before regrouping.
   If p or q is nonpositive the corresponding slice is zero; no logarithmic
   identity is used outside its positive domain. The result is the integral
   of C_(r*N)(tau) times the complete physical kernel for f_tau,f_tau. Apply
   (1) pointwise. Integrability of the transition expression follows from the
   same Fubini argument and exact kernel equality, without a tau-dependent
   Fourier-seminorm majorant.

5. Select the actual eta_N from exists_primeGaussianCubic_smooth_band_negligible_error.
   On the eventual good scales construct every f_(N,tau) as above; on the
   finitely irrelevant bad scales set the Schwartz family to zero. All cutoff
   properties, the exact slice formula, (2), and the original negligible
   sharp/smooth comparison are retained in one existential theorem.

## What this does and does not settle

The edge-width conflict from the attempted stationary-value replacement is
avoided by an exact transition. All two-coordinate physical amplitudes, the
moving W argument, reciprocal logarithms and Mellin tails are retained.
No smoothness order, summability or analytic estimate is assumed for V or W.

The new theorem concerns the CONTINUUM slice; it is not yet the full lattice
Poisson identity for the critical prime source. Every integer lift, the
remaining r-variable, both literal contraction projectors and the signed
critical atom tensor must remain in that assembly. Its complete near-cone
and transverse-tail estimate at o(N/log(N)^2) remains the hard open problem.
Growing moments, moving cofactors, common-height self-return and RH remain open.
