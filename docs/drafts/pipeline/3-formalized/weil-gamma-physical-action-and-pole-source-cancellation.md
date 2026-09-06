# Actual Gamma boundary action and exact Weil pole-source cancellation

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Modules:** `RHTower.CCMRestrictedWeilGammaMixedJump` (5 public theorems), `RHTower.CCMRestrictedWeilGammaPolarAbsoluteBound` (2), `RHTower.CCMRestrictedWeilGammaPolarAction` (2, 1 definition), and `RHTower.CCMRestrictedWeilPolarSourceCancellation` (5, 2 definitions). All four are wired into `RHTower.lean`.
- **Predecessors:** [Scalar Gamma integral and actual operator domain](weil-gamma-polar-jump-boundary-integral.md); [literal prime-pole arithmetic action](weil-prime-pole-arithmetic-action.md).
- **Open continuation:** [Signed boundary–arithmetic control of Weil pole forcing](../1-in-progress/weil-gamma-pole-boundary-action.md).

## Full proof chain and scope
Exact prime–Gamma action → control of constrained ground forcing → exclusion of a zero ground → positive floors at every aperture → weighted pole exclusion → RH. These four modules close the physical Gamma operator identification and the full source cancellation. They do not give the signed comparison needed to exclude a constrained zero ground.

## Conjecture → proof / pivot loop
1. **Candidate:** the exact scalar Gamma integral is the coefficient function of the actual pole-profile operator image. A separate per-lag almost-everywhere identity does not itself justify integrating that identity. **Proof obligation exposed:** joint integrability and identification with the complete form pairing.
2. **Stronger positive survivor:** the jump ratio is bounded below by minus one finite interval indicator. This gives a direct absolute-integral bound retaining the positive endpoint tails. **Proved.**
3. **Mixed-form conjecture:** the quadratic Gamma energy identity extends to the complete complex mixed form, with absolute integrability. Four-term complex polarization, including the imaginary cross terms, proves it. Translation unitarity and adjoint compression identify its physical mixed jump. **Proved.**
4. **Proof-method pivot:** the actual pole-profile operator-domain theorem already supplies an L² representative. Instead of assuming global L² regularity of a guessed logarithmic coefficient, prove physical Fubini against compact interior tests, then apply local smooth-test separation. Support and null endpoints finish the global coefficient identity. **Proved.**
5. **Cancellation conjecture:** exact polar Gram entries remove the Gamma radius/ramp terms and the Chebyshev exponential main profile when the three actual operator terms are combined. **Proved as an unrestricted operator identity and a completed constrained pairing.**
6. **Remaining conjecture:** the surviving boundary-minus-arithmetic-error expression controls constrained ground forcing strongly enough to exclude a zero ground. **Open; no sign is assumed in any theorem.**

## Dependency-closed paper proof
For positive aperture `a`, let `p±=1_[-a,a] exp(±x/2)`. Every truncated real exponential is already proved to belong to the actual unrestricted Weil Friedrichs domain. Write `J_a` for the physical embedding of the complete archimedean form domain, and `U_h` for full-line translation. The established quadratic identity is

`integral_0^infinity rho(h)||U_h J_a u-J_a u||² dh=||u||_form²-||J_a u||₂²`,

with `rho(h)=exp(-h/2)/(1-exp(-2h))`. Its finite nonnegative integral gives real absolute integrability. Applying it to `u+v`, `u-v`, `u-i v`, and `u+i v` gives the absolutely integrable complex polarization

`integral rho(h)<U_h J_a u-J_a u,U_h J_a v-J_a v> dh`

`=<u,v>_form-<J_a u,J_a v>₂`.

The convention is conjugate-linear in the first variable. Unitarity of `U_h`, adjointness of `U_-h`, and the exact aperture compression `S_h` give

`<rho(h)(2f-S_h f),g>=rho(h)<U_h f-f,U_h g-g>`.

This identifies the mixed integral with the actual complete form, rather than only its diagonal energy.

For positive endpoint distances `R,L`, the literal positive-pole jump ratio is

`J(R,L,h)=rho(h)[2-exp(h/2)1_(h≤R)-exp(-h/2)1_(h≤L)]`.

When `h≤R`, adding the missing negative contribution can only decrease this expression. Put `t=exp(-h/2)`, so `0<t<1`. The resulting full jump is

`rho(h)[2-exp(h/2)-exp(-h/2)]=-(1-t)/[(1+t)(1+t²)]≥-1`.

When `h>R`, the remaining bracket is at least one, hence nonnegative. Thus `J≥-1_(0,R]` on the positive ray. Since `|J|≤J+2·1_(0,R]`, the previously proved scalar integral yields

`integral |J(R,L,h)| dh ≤ integral C + R + B(R,L)`,

where `C=2rho-exp(-h)/(1-exp(-h))` has mass `-Re digamma(1/4)-EulerGamma-log 2`, and

`B(R,L)=-(1/2)log(1-exp(-2R))-(1/2)log(tanh(L/2))>0`.

For a smooth real test `g` compactly supported in `(-a,a)`, the function

`(h,x) ↦ g(x)exp(x/2)J(a-x,a+x,h)`

is jointly measurable: all continuous factors and both measurable cutoff regions are retained. Both endpoint distances stay positive on the compact support. Continuity of `B` there and the absolute bound dominate the integral in `h` by a constant times `|g(x)|`. Therefore the joint function is absolutely integrable and Fubini applies. The exact per-lag source representative and the complete mixed-form identity give the pairing of the actual excess multiplier image with `g` as the integral of

`exp(x/2)[-(a-x)-Re digamma(1/4)-EulerGamma-log 2+B(a-x,a+x)]g(x)`.

The actual excess image is L², hence locally integrable. The explicit coefficient is continuous on the open aperture, hence locally integrable there. Its difference from the conjugate of the actual representative pairs to zero against every real smooth compact interior test. The corpus smooth-test separation theorem forces that difference to vanish almost everywhere in the open aperture. Taking conjugates, using real-valuedness of the profile, aperture support, and the two null endpoints proves the global cutoff representative.

Restore the fixed scalar using `2 gammaHardyPhaseRate(0)=Re digamma(1/4)-log pi`. The actual normalized compressed Gamma image is therefore

`A_a p+=p+[-(a-x)+kappa+B(a-x,a+x)]`,

where `kappa=-EulerGamma-log(2pi)`.

The cross-pole inner product is the integral of one on the aperture, so `<p-,p+>=2a`; more generally this holds for every pair of opposite real slopes. The existing exact norm identity gives `<p+,p+>=2sinh(a)`. Applying the literal two rank-one operators yields

`polarOp p+=2a p++2sinh(a)p-`.

The existing prime-action theorem retains every prime power:

`P_a p+=p+[psi(exp(a-x))+M(exp(a+x))]`,

where `M(Y)=sum_(2≤n≤floor Y) Lambda(n)/n`. Define `E_psi(Y)=psi(Y)-Y` and `E_M(t)=M(exp t)-t`. Since

`p+ exp(a-x)=exp(a)p-`, `2sinh(a)-exp(a)=-exp(-a)`,

and `-(a-x)+2a-(a+x)=0`, the actual operator `H_a=A_a+polarOp-P_a` satisfies

`H_a p+=p+[kappa+B(a-x,a+x)-E_psi(exp(a-x))-E_M(a+x)]-exp(-a)p-`.

This is an almost-everywhere formula for an actual domain vector's operator image. Subtracting `kappa p+` and adding `exp(-a)p-` defines an actual aperture L² defect whose coefficient is exactly `p+[B-E_psi-E_M]`. For any completed constrained form vector `f`, both exponential moments vanish, so

`<H_a p+,f>=integral_[-a,a] exp(x/2)[B(a-x,a+x)-E_psi(exp(a-x))-E_M(a+x)]f(x) dx`.

Absolute integrability of this product follows from the two actual L² representatives. No prime main term, radius term, or Gamma normalization is bounded separately before cancellation. No sign of the surviving integral is asserted.

## Verification
- Scratch checks with `lake env lean`: mixed form, absolute bound, physical action, and full cancellation PASS; scratch directory `/tmp/hgt-gamma-mixed.f4pHe7EZ/`.
- Named final `lake --old --log-level=error build GaloisForLFunctions.RHTower.<module>` audits PASS for all four listed leaves. No full or umbrella build.
- `lake env lean /tmp/hgt-gamma-mixed.f4pHe7EZ/FinalAudit.lean`: all 14 public theorems depend exactly on `[propext, Classical.choice, Quot.sound]`; actual mathlib `RiemannHypothesis` printed and remains unproved.
- No numerical experiment, computational oracle, added axiom, or unproved premise supplies the identities.
- Final `python3 scripts/formal_tools.py lint`: PASS (`formal lint passed`); existing large-file warnings remain. Logs: `/tmp/hgt-gamma-mixed.f4pHe7EZ/FinalLintRepaired.txt` and `.err`.
- `git diff --check`: PASS. All owned Lean/build processes are terminal.
- The initial global gate exposed the existing unwired `ThetaTiltLogDensity` leaf. Two smoothness-order bound proofs were repaired, the leaf was wired and individually built, and its 16 existing public theorems were axiom-audited with the same three standard dependencies. These are an integration repair, separate from the 14 new source-action theorems above.
