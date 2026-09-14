# Photonic scalar monodromy bridge

Own investigation only; continues `mem:rh/photonic_native_return_2026_09_13`. Goal remains unfinished: native PTC topology must generate zeta, zeros, critical line. User insists optimize Lean, no heartbeat hacks, no numerical work, single foreground Lean process, targeted leaf builds only.

## Certified artifact

`formal/GaloisForLFunctions/RHTower/PhotonicReturnMonodromy.lean` (240 lines), wired immediately after PhotonicParabolicReturn in RHTower.lean. New scratch `lake env lean /tmp/ptc-monodromy-germ.lean` passed. Final `lake build GaloisForLFunctions.RHTower.PhotonicReturnMonodromy` passed, only leaf newly built (46s; 8831 cached/dependency jobs). `/tmp/ptc-monodromy-axioms.lean` audits all 11 public theorems; each uses only propext, Classical.choice, Quot.sound. No options/axioms/sorry/admit/unsafe/opaque/evaluation commands. All owned handles exited; no other agents' processes touched.

Functions: photonicRegularPhase s z is the two-channel Hurwitz Fourier combination at shifts 1 ± z/(2π), exponent 1-s. This is holomorphic at phase zero. Exact real boundary equals ζ(s)+jonquiereRemainder s θ. Its value is ζ(s), derivative iζ(s-1). photonicProjectedReturn is photonicUpper (H 0) (-I * deriv H 0), proved equal to the full certified photonicReturn in the strip.

photonicReturnLift s w = jonquiereLead s * exp((s-1)w) + H_s(exp w). Proved holomorphic over a sufficiently small punctured phase disk, and at w=log θ equals actual expZeta(θ/(2π),s) for positive θ≤π. Character μ(s)=HurwitzOrbit.monoScalar(1-s). Exact deck law at w+2πi; μ≠1 in open strip; deck difference never zero there (Gamma lead and exponential nonzero). Canonical projector (F(w+2πi)-μF(w))/(1-μ)=H_s(exp w). This resolves scalar subtraction ambiguity without positing an abstract assumed representation.

## Optimization facts

Generic HasDerivAt.add/sub + simpa selected incompatible normed-space instances from imported CStarAlgebra paths. Typed chain-rule intermediates plus specialized HasDerivAt.const_add/const_sub closed proofs at default limits. No benchmark claim. AnalyticAt.comp_of_eq handles basepoint 1 versus 1±0/(2π); direct comp cannot reduce those to definitional equality. AnalyticAt.div_const has implicit constant; analyticAt_const.mul supplies constant multiplication. Typed HasDerivAt is necessary for the long combined derivative certificate.

## Existing frontier, don't duplicate

`XiHurwitzConstraintOrientation.openCriticalStrip_monoScalar_negativeReal_iff` already proves negative-real exp(-2πis) iff Re(s)=1/2 in open strip. Its proof and relevant reflection/character statements were source-read, not freshly rebuilt. `HeatEnergyTangent.jonquiereTangent_eq` already supplies iζ(s-1). `Hurwitz.AnchorTransversality` supplies complex-shift analytic anchor and derivative; `AnalyticContinuation.continuedHzeta_eq_hzeta` is the convergence-branch connection. The continuation definition uses ζ restoration, so the new proven boundary equality is essential, not a definition-only nativity claim.

## Next hard target

`docs/drafts/pipeline/1-in-progress/photonic-time-crystal-topology/detuning-monodromy.md` contains full matrix paper derivation. Actual physical detuning at simple band edge exchanges Floquet labels: set c=tr M/2=cosh X, A=M-cI, A²=sinh² X I. Response is (F(X)+F(-X))/2 I + (F(X)-F(-X))/(2 sinh X) A. Regular coefficients are even analytic in X; odd numerator cancels sinh X. At positive parabolic M0=I+N their specialization is ζs I+ζ(s-1)N. Physical coordinate τ=X² has singular characters ν=exp(πi(s-1)) and -ν; square has μ. Physical projector (Tτ²-μ)/(1-μ). This ramified physical family identification is NOT Lean-certified yet. Scalar lift deck law must not be presented as already proving physical detuning monodromy.

Use actual binary family from prior construction: α=arctan(4/3), two slab phases kα, frequencies k and 4k. tr M(k)=2-(25/4)sin²(kα), derivative at1=-6α, M(1) has trace -2. Positive family M(k)² has half-trace derivative 12α at1, so nondegenerate ramification. In phase φ, normalized odd quotient can use dslope: (dslope H 0 φ + dslope H 0 (-φ))/(2*I*dslope Complex.sin 0 φ). `RHTower.AnalyticDividedDifference.analyticAt_dslope_of_analyticAt` source-read and available, not rebuilt. Need actual physical family, not arbitrary assumed transfer family.

Confinement remains open. Maxwell flux vanishes on kernels; conjugate partners do not force each character real. Gaussian metaplectic lead gives d/2 and is a density, not finite trace; homogeneous PTC has opposite-momentum modes, so no justified universal single-mode half. Cahen Aug2026 https://arxiv.org/html/2608.22443v1 prop5.4 and PTC geometry https://arxiv.org/html/2511.17317v1 inspected. Classical Jonquiere source https://dlmf.nist.gov/25.12.E12.

## Logs / audit

Own card README.md, FACTS.md, detuning-monodromy.md updated. No general universal-law STATUS edits: findings route-specific. Latest lint failed only unrelated unwired RHTower.Sieve.KloostermanGlobalCollisionCoprime, HTGeometry.Arxiv2609KineticVariance, HTGeometry.Arxiv2609ThurstonIdentifiability plus size warnings. Neither photonic leaf unwired. Index succeeded (9 changed). Worktree is very dirty/shared, preserve others. No commit/push. Exact requested hgt-fields-medalist skill remains unavailable; user asked for path previously, no reply. Read/used docs/meta methods and hgtl7 alternative already disclosed.