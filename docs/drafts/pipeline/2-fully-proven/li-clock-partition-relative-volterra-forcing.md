# Actual partition relative Volterra forcing

- **ID:** LI-CLOCK-PARTITION-RELATIVE-VOLTERRA-FORCING
- **Stage:** 2-fully-proven
- **Type:** THEOREM on paper; exact central-clock formalization OPEN
- **Source:** [actual density/endpoint boundary](../3-formalized/li-clock-partition-density-ratio-endpoint-boundary.md), [literal finite Volterra law](../3-formalized/li-clock-finite-partition-volterra-positive-area.md)
- **Statement:** For both literal half-tilted partition clocks on one full nonvanishing central disk, `2*(P_A-P_U)*B_W=D_N`, with positive complete four-coordinate Borel kernel `B_W` and the exact signed mixed-moment forcing `D_N`. No inference of inverse or compensation sign.

## Scope and status

This target was already present in section7 of the independently audited272-line density paper; its original source search and complete root/cross-agent paper audit apply. It is separated explicitly from the exact density/source/classification and endpoint comparison leaves; those consumers do not formalize central-clock relative convolution. Full nonvanishing on a common closed disk, both entire-clock series, all factorial/binomial factors, convolution associativity and differentiation, and literal signed four-coordinate source interpretation remain required. Do not mark this card formalized on the signed-density identity alone.

Canonical signed density, exact antisymmetric ratio coupling, compact support and complete continuous-test four-coordinate law have Lean proofs in the owned density consumer. That does not prove the relative clock law. No new Lean scope released for this card. Root owns integration; existing leaves remain frozen. Actual residual `Re(C-K_N+H_N)>=0` and RH remain OPEN.

## Gates

- [x] Original source research and complete272-line author/root/independent paper audit PASS.
- [x] Exact normalization/symmetrization and signed source burden preserved.
- [ ] Both literal partition clocks and common full central disk formalized.
- [ ] Complete relative Volterra/convolution derivative and mixed-source series formalized.
- [ ] Independent full proof/source audits and named/direct/all-public foundational checks.

## Audited original paper section7

## 7. Exact signed relative Volterra obstruction and domain ledger

Let P_A and P_U be the literal real partition clocks. Their central coefficients are
  P_A(t)=sum_{j>=0} kappa_A,2j+2*t^(2j+1)/[(2j+1)!]^2,
where kappa_A,2j+2=deriv^(2j+1)(logDeriv A_N)(.5), with no alternating sign.
Installed LiClockPairedEtaFinitePartitionVolterra.lean:752,:764 state this normalization.
The symmetrized MGF logarithmic derivative uses q_A(.5+z)-q_A(.5-z),
not the unpaired q_A(.5+z); this gives the factor TWO in
  2 P_A*B_A=t B_A', 2 P_U*B_U=t B_U'.
Here star is Volterra convolution on [0,t], t>=0.
Installed :1002 requires N>0, r>0 and A_N(.5+i*z)!=0 on the FULL closed central disk.
Such a disk exists by center positivity and analyticity; a common r<1/2 works for A and U.
Circle-only nonvanishing suffices for the literal gap contour split, but not for central-series
reduction or the cumulant recurrence. These are distinct premise ledgers.

Set H=P_A-P_U, Q=B_A*B_U. Associativity and subtraction on compact intervals give
  2 H*Q=(tB_A')*B_U-B_A*(tB_U').
All functions are entire-clock restrictions; compact absolute convergence justifies exchanges.
Put X distributed as rho_A and Y independently as rho_U; W=X+Y has four original half-tilted
coordinates. The positive full Borel kernel of W is B_W=Q', B_W(0)=1. Differentiating gives
  2 H*B_W=D_N(t),
  D_N(t)=sum_{j>=0} E[(X-Y)(X+Y)^(2j+1)] *
                   t^(2j+2)/((2j+2)!*(2j+1)!).
To check factors, at degree 2n in the differentiated right side its binomial numerator is
  sum_{a+b=n}(2a-2b)*choose(2n,2a)*d_A,a*d_U,b
  =2n*E[(X-Y)(X+Y)^(2n-1)].
The denominator is [(2n)!]^2, yielding exactly (2n)!*(2n-1)! above.
The first term equals (d_A,1-d_U,1)*t^2/2, consistent with 2H*1 and H'(0).

A proposed radial monotone-likelihood-ratio mechanism would use
  sigma_N(w)=1/2 int_{J_w} (2x-w)*(r_N(x)-r_N(w-x))*rho_U(x)*rho_U(w-x)dx,
  J_w={x:|x|<L and |w-x|<L}.
This is the signed pushforward density of (X-Y) at W=w.
For w>0, sign(2x-w)=sign(|x|^2-|w-x|^2). An increasing radial ratio would make the integrand
nonnegative; a decreasing ratio would make it nonpositive. Sections 3-5 disprove BOTH premises
for the actual source. This failure does not prove that sigma_N changes sign or that D_N has
any particular sign. It rejects this specific comparison route, not every arithmetic mechanism.
Because r_N is the same constant kappa on both retained endpoint neighborhoods,
sigma_N(w)=0 for |w|>2L-epsilon (the allowed interval is invariant under x<->w-x).
This is a signed forcing support survivor, with N-dependent edge gap only.

The literal finite completed response is F_N=C-K_L+H on regular circles, as installed in
LiClockPairedEtaArithmeticCancellation.lean:559
`liClockPairedEtaFiniteClockResponse_eq_completion_sub_contiguous_add_gap`.
Its positivity therefore needs the residual Re(C-K_L+H)>=0.
Positive B_W or a nonnegative smoothed forcing alone does not imply a pointwise inverse sign.
The exact relative law preserves the signed burden; it is not an independently proved growing-window
producer. Actual source and full completion must remain in any future missing inequality.

## Log

- 2026-09-30 09:17 UTC — Preserved original relative central-clock target on its own Stage2 card before any new formal work. Current two consumers certify density/source/classification and sharp endpoint bounds; full relative-clock expansion remains explicit formal-open work. No target discarded, no inverse-sign or RH claim.
