# FZZ-P: higher original screening collisions

- **ID:** FZZ-P-HSC
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** [current frontier](rh-current-frontier-map.md#fzz-p--parity-delay-mellin-orientation), [first-strip cutoff audit](fzz-p-continued-screening-mark.md)
- **Statement:** Derive the original angular Taylor subtraction at exponent `-6`, including both punctures and all differentiated counterterms.

## Goal

Fixed theta/FZZ source → complete mixed Ward law in an independently fixed phase frame → balanced vacuum delay → passivity → RH. Eight first-strip source theorems now close the original marked cutoff and derivative interchange. The external-leg receiver uses `k=4`, whose displayed position exponent `2(1-k)=-6` is outside that strip. This card attacks that missing source domain; it does not assume a full physical cancellation.

## Gates

- [x] Well-posed original source and non-circular angular-average attack.
- [ ] Original angular recurrence with parameter differentiation justified.
- [ ] Exact cubic inverse-power angular average and local remainder.
- [ ] Higher original cutoff counterterms at both punctures.
- [ ] Original marked cutoff and full source normalization at the receiver level.
- [ ] Dependency-closed paper proofs and data-only Lean statements, targeted build and complete axiom audit.

## Approach

For `Q(r,theta)=1-2r*cos(theta)+r^2`, let `A_m(r)` be the original normalized angular integral of `Q^(-m)`. On `0<r<1`, the current corpus proves `A_1=(1-r^2)^(-1)` through the Poisson kernel. A compact parameter–angle rectangle stays away from `Q=0`; continuous parameter derivatives have a common bound, so dominated differentiation should give

`r*A_m'(r)=m*((1-r^2)*A_(m+1)(r)-A_m(r))`.

Two applications predict `A_2=(1+r^2)/(1-r^2)^3` and `A_3=(1+4r^2+r^4)/(1-r^2)^5`. The latter predicts local expansion `1+9r^2+36r^4+O(r^6)`, hence two power divergences and a logarithmic divergence at exponent `-6`. Derive the actual original angular equality and remainder before using these predictions in a planar cutoff integral.

The other marked puncture also needs new terms. The predicted first angular Taylor coefficients for regular exponent `a` are `1,a^2/4,a^2*(a-2)^2/64`; their derivatives at `a=-6` are `0,-3,-21`. Prove these as original source coefficients; do not extrapolate the first-strip absence of a second-collision marked correction.

## Evidence and constraints

Read current sources: `SteinhausTorusJensenFloor.circleAverage_inv_normSq_one_sub_mul` (original inverse-square Poisson average); `ThetaCuspHawkingBMNativeCircleMean.average_hasDerivAt` (compact derivative bound before differentiation); `BarnesDoubleZetaDeepContinuation.barnesConeKernelAnalytic_taylor_three` (exact Taylor polynomial plus admitted remainder). They provide methods, not an identified full FZZ source or Ward theorem.

Deep/all-view searches run over the current corpus; coverage and applicability are recorded as results arrive. No numerical experiments, added proof axioms or unproved source identities are permitted. Public source statements use real data charts; all analytic and integrability requirements must be discharged internally.

## Log

- 2026-09-11 — created after the eight first-strip cutoff/derivative theorems passed scratch, leaf build, all axiom audits and global lint. RH, the full mixed Ward producer and the phase frame remain open.


The angular scratch `/tmp/fzzp_higher_screening_angular.lean` passed cleanly with six public theorems, including the exact corrected radial cutoff limit. Its proof body was promoted unchanged to `formal/GaloisForLFunctions/RHTower/FZZCigarHigherScreeningAngular.lean`, wired into the umbrella, and is undergoing its leaf audit. It uses a fixed compact parameter–angle rectangle contained in `0<r<1`, bounds the continuous derivative there, and invokes the current parametric-integral theorem. This is local polar integration of the original collision kernel, not Jacobian averaging of the marked torus selector. The next scratch `/tmp/fzzp_higher_screening_plane.lean` drafts the original polar-annulus transport, finite-annulus integrability and reflected puncture limits; it has not yet been checked.

The deep/all-view recurrence query returned partial generation 823347 with semantic deadline expiry; all 20 candidate and 20 method names were inspected, with no proposed ingredient set. It supplied current circle-average transport and Poisson identities. Broad recent arXiv searches for multipole, resurgence and orthogonality returned older papers; a stricter June–September search for multipole, Laurent and contour returned no hits. Those empty or out-of-range results are not evidence of absence of applicable research.

## Exact angular and radial derivation

Write `d=1-r^2`. Since `Q >= (1-r)^2 > 0`, every inverse power and its parameter derivative is continuous on a compact parameter–angle rectangle around an interior radius. Compactness supplies an integrable constant bound for differentiation. The pointwise identity

`r*d_r(Q^(-m)) = m*((1-r^2)*Q^(-m-1)-Q^(-m))`

then integrates to the recurrence. The admitted Poisson average gives `A_1=1/d`. Differentiating gives `A_1'=2r/d^2`, so the recurrence yields `A_2=(1+r^2)/d^3`. Differentiating again gives `A_2'=4r*(2+r^2)/d^4`, hence `A_3=(1+4r^2+r^4)/d^5`.

The exact remainder, rather than an unspecified asymptotic term, is

`H(r)=(100-275r^2+316r^4-171r^6+36r^8)/(1-r^2)^5`,

with `A_3=1+9r^2+36r^4+r^6*H`. It is continuous through `r=0` and on `[0,1/2]`. Thus `r^(-5)*(A_3-1-9r^2-36r^4)=r*H` is integrable there. This proves integrability after angular integration; it does not assert absolute integrability of a planar integrand after merely radial subtraction.

The singular radial primitive is

`P(r)=-1/(4r^4)-9/(2r^2)+36*log r`.

For `0<epsilon<=1/2`, the fundamental theorem gives

`int_epsilon^(1/2) r^(-5)*A_3(r) dr + P(epsilon)
 = int_epsilon^(1/2) r*H(r) dr + P(1/2)`.

Dominated convergence removes the lower endpoint in the remainder integral. Multiplying by the polar factor gives the counterterm `-(pi/2)*epsilon^(-4)-9*pi*epsilon^(-2)+72*pi*log epsilon`. The planar-annulus transport and both marked punctures remain separate obligations until explicitly checked.

## Current method and distant-paper intake

- Deep/all-view query `polar annulus inverse power Taylor remainder integrable`: partial generation 823348; semantic backend timeout and reranking deadline, no ingredient set. All 20 candidate and 20 method names were inspected. The useful methods were original polar-annulus transport in `DaiYoshikawa.AnnulusMonomialIntegral` and compact-product Fubini in `HTGeometry.CauchyPompeiu`.
- Hybrid query `circleAverage annulus integral compact source`: partial generation 823348, semantic coverage incomplete. All 20 candidate and 20 method names were inspected. Current circle-average angle shifts and the same original annulus transport supply the next planar step.
- Broad searches for resonance, locality and holonomy found [Information locality of a quantum locally recoverable code](https://arxiv.org/abs/2608.04403) (5 August 2026) and [Prometheus–Pandora dynamics](https://arxiv.org/abs/2607.02839) (3 July 2026). Abstracts inspected; no applicable analytic source or Ward identity identified, and no computations run.
- [Resurgence of high-energy string amplitudes](https://arxiv.org/html/2604.07444v1) is dated 8 April 2026, outside the preferred window. Sections 3.2.1–3.2.3 retain periodic ambiguity in their difference-system solutions and leave the higher-dimensional connection problem open. It supplies no complete phase normalization for this route.
- [Covariant Berry connection](https://journals.aps.org/prresearch/pdf/10.1103/1369-2jzh) was published 9 July 2026. Equations (3), (6), (15) retain metric evolution and the derivative correction to a Hermitian-frame Hamiltonian. Inference for this route: that construction alone cannot identify the original fixed-frame generator or cancel its mixed response. No transfer theorem or new universal rule is asserted from this intake.

## Next conjecture: exact whole-plane finite value

**CONJECTURE, not Lean-proved:** with independent circular punctures at zero and one and precisely the preceding local corrections, the whole-plane finite part of `K(-6,-6)` is `-84*pi`.

This candidate comes from the original source, not a substituted special-function value at a pole. Set `f(z)=1/(z^3*(z-1)^3)`, so `K(-6,-6)=|f|^2` off the punctures. Its partial fractions are

`f(z)=-z^(-3)-3z^(-2)-6z^(-1)
       +(z-1)^(-3)-3(z-1)^(-2)+6(z-1)^(-1)`.

A single-valued real harmonic potential away from the punctures is

`U(z)=Re(1/(2z^2)+3/z-1/(2(z-1)^2)+3/(z-1))
      +6*log|z-1|-6*log|z|`.

Its proposed exact energy identity is `|grad U|^2=K(-6,-6)`. The local expansion at zero has inverse-square coefficient `1/2`, inverse-linear coefficient `3`, logarithmic coefficient `-6`, and regular constant `-7/2`. At one these coefficients are `-1/2,3,6,7/2`. In the inward flux `-int U*(partial_r U)*r dtheta`, the opposite radial powers' cross terms cancel. Each puncture should therefore contribute

`pi/(2*epsilon^4)+9*pi/epsilon^2-72*pi*log epsilon-42*pi+o(1)`.

Green's identity on the finitely punctured disk, together with vanishing outer flux, would give the stated `-84*pi`. The remaining work is explicit: verify the original energy identity, admit the multiply punctured Green formula, bound both local remainders and outer flux, and compare with the independently removed cutoff definition. A deep/all-view corpus search for the required Dirichlet-energy method is running. No phase-frame or mixed Ward conclusion follows from this candidate alone.
