# BAG complete transverse critical action

- **Stage:** 3-formalized

Route: complete signed physical BAG cubic. Continuation01ac.
Paper proof and production Lean leaf complete. This exposes the full phase;
it proves no growing-N cancellation estimate.

Write f_tau(p)=eta(p)*V(p/N)/log(p)*exp(-i*tau*log(p)) and
C(R,tau)=(2*pi)^(-1)*exp(i*tau*log(R))*M_W(i*tau), exactly as in the
audited physical-window transition. For w=(xi,upsilon,zeta), define

    T_tau(r,xi,upsilon)
      = integral_alpha integral_beta
          exp(2*pi*i*(r*upsilon*alpha+r*xi*beta-r*alpha*beta))
          * Fourier(f_tau)(alpha)*Fourier(f_tau)(beta),
    B(r,xi,upsilon) = integral_tau C(r*N,tau)*T_tau(r,xi,upsilon).

The literal full physical Fourier coefficient is

    Fourier(A_N)(w)
      = integral_r 2*pi*conj(f_0(r))
          * exp(-2*pi*i*r*(zeta+xi*upsilon))*B(r,xi,upsilon).

Both the outer r-row and every positive-r inner Mellin profile are integrable.
The reciprocal r in A_N cancels the exact r Jacobian of the transition on
positive support. At nonpositive r, the actual cutoff is zero.

Proof. A volume-preserving measurable equivalence sends Euclidean Fin-3
coordinates to (r,q,p). Continuity and compact support make the actual Fourier
kernel integrable. Full product Fubini gives both the iterated integral and
outer-row integrability. Factor the exact Fourier exponential and apply the
previous full physical-window transition at x=-xi,y=-upsilon. Its arguments
become (r*upsilon,r*xi); its phase combines with exp(-2*pi*i*r*zeta) to give
the displayed transverse defect. Factoring the nonzero scalar
r*exp(-2*pi*i*r*xi*upsilon) also proves Mellin integrability of B.

Every integer lift is retained: replace each Fourier coefficient in the
already proved Poisson lattice by this exact integral. No interchange of the
integer sum with either integral is asserted or needed. Thus the entire
critical atom tensor under both literal contraction projectors equals the
smoothed physical cubic with this full transverse lifted test. The
unconditional actual cutoff family retains compactness, its plateau, all
shifted-lattice norm summability, and the negligible normalized difference
from the ORIGINAL sharp cubic.

Production: ChiPrimeGaussianCubicTransverse, eight public declarations.
Final leaf audit91858: exit0, empty log, lake --old env lean with -o.
Axiom90906: exit0, all eight names depend only on propext, Classical.choice,
Quot.sound. Index64921: exit0, all eight API entries verified and umbrella
import once. Lint19602: exit1,33 unrelated unreachable modules, no error
in this leaf or active proof-debt declarations. Global lint is not clean.

Hard problems still open: signed near-cone and tail action at
o(N/log(N)^2), growing moments, moving cofactors, common-height self-return,
and RH. The full transition varies with r and both transverse frequencies;
the extracted phase alone does not justify stationary substitution or
discarding near-resonances.

## Lean certificate

- [x] 2 → 3: Lean `GaloisForLFunctions.RHTower.ChiPrimeGaussianCubicTransverse`, `GaloisForLFunctions.RHTower.ChiPrimeGaussianCubicWindowTransition`, `GaloisForLFunctions.RHTower.ChiHyperbolicFourierTransition`; `lake env lean` + module build pass; axiom audit `[propext, Classical.choice, Quot.sound]` only

Modules (all `lake env lean`/`lake build --old` clean, every public constant audited to `[propext, Classical.choice, Quot.sound]`, wired into the RHTower umbrella; statements re-verified claim by claim against this paper card):
`GaloisForLFunctions.RHTower.ChiPrimeGaussianCubicTransverse`; base `GaloisForLFunctions.RHTower.ChiPrimeGaussianCubicWindowTransition`, `GaloisForLFunctions.RHTower.ChiHyperbolicFourierTransition`.

| Claim | Declaration |
|-|-|
| definitions `T_τ(r,ξ,υ)`, `B(r,ξ,υ) = ∫ C(rN,τ)T_τ` | `bagCubicTransverseTransition`, `bagCubicTransverseProfile` |
| `Â_N(w) = ∫ 2π conj(f₀(r)) e(−r(ζ+ξυ)) B(r,ξ,υ) dr`, outer row and inner Mellin profile integrable | `bagCubicPhysicalFourier_eq_transverse`, `integrable_bagCubicTransverseProfile`, `integral_three` |
| every integer lift replaced by the exact integral; critical action of the transverse lifted test | `bagCubicTransverseFourier`, `bagCubicTransverseLiftedTest`, `bagLiftedFourierTest_eq_transverse` |
| unconditional actual family with all properties and the negligible normalized difference | `exists_bagCompleteTransverseCriticalAction` |

No growing-N cancellation estimate or RH is claimed.

The earlier Lean certificate of this lane is `../bag-complete-transverse-critical-action.md` (stage 3, flat folder).

## Log

- 2026-10-05 — Lean certificate audited; every numbered claim mapped to a declaration; moved to 3-formalized.
