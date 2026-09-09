# HB original Fourier–Mellin value: finalized

Goal ACTIVE; RH UNPROVED. Frontier map READ ONLY. No agents authorized. No numerical experiment. Do not re-audit these completed modules or run an umbrella build. Continue at original combined-period constant/cutoff assembly, then source-faithful continuation to physical s=q/2.

## Completed result
Eight canonical leaves under formal/GaloisForLFunctions/RHTower/, prefix ThetaCuspHawking:
BMCuspHermitianMean (97 lines, 5 public theorems), BMCuspScalarEnergy (91,5), BMNativeFourierEnergyBounds (90,3), BMNativeFourierMassAdmission (100,5), BMNativeFourierMellinInterchange (92,9), BMNativeFourierBesselValue (110,4), BMNativeFourierDirichletValue (88,5), BMNativeFourierCompletedValue (66,1). Total 734 lines, 37 new public theorems. Namespaces RHTower.D4BMCuspProjection except EnergyBounds in RHTower.D4BMJointSource.

Let q:XiZeroCopy, u=center q=q-1/2. Original amplitude a_N(u,y)=c_N(u)*sqrt(y)*K_u(2pi(N+1)y), c_N=(N+1)^u sum_(d|N+1)d^(-2u). amplitudeMass M=sum_N norm(a_N)^2.

Exact actual scalar Hermitian energy: integral_0^1 norm(scalar_u)^2=norm(principal_u)^2+8M. Derived from original paired-wave conjugation/orthogonality, retaining complex coefficients. Original scalar^2/2=globalSquareResidual+full cutoff P_h plus existing global residual and norm P_h bounds gives norm scalar^2<=A+B S2. Actual mean S2 gives M<=A+B(y^2+D2*y^-1). Weighted full Bessel tails give y^r M bounded for any real r on y>=1. Thus weighted M is integrable at both height ends for r>2.

nativeFourierMellin_integral_norm_summable proves SUMMABILITY OF INTEGRALS OF NORMS of the original complex y^(s-2)*a_N^2, for every Xi q and Re s>2. nativeFourierMellin_integral_eq_tsum proves the actual original complex interchange. nativeFourierMellin_integrable admits the actual full complex diagonal. Norm estimates do not replace phase by energy.

Actual Bessel scaling and original coefficient divisor identity give nativeFourierMellin_lseries for EVERY Xi q, Re s>2:
I(q,s)=integral_0∞ y^(s-2) sum_N a_N^2 dy=(2pi)^(-s)*B(s,u)*L(sigma_(-2u)^2,s-2u),
B(s,u)=2^(s-3)/Gamma(s)*Gamma(s/2+u)*Gamma(s/2)^2*Gamma(s/2-u).
Original term identification is originalCoefficient_eq_dirichletTerm; reindexing originalCoefficient_tsum_eq_lseries also handles nonsummable convention, while nativeRamanujan_summable separately proves genuine series admission in the right-half Xi chamber.

For Re q>1/2 and Re s>2, nativeRamanujan_value identifies actual L-series with zeta(s-2u)*zeta(s)^2*zeta(s+2u)/zeta(2s). This uses underlying Ramanujan negative divisor shifts, NOT old generic Re P>1 source packing (outside Xi strip).

Capstone nativeDiagonalPeriod_fourLambda:
4 Lambda(2s)*I(q,s)=Lambda(s+2u)*Lambda(s)^2*Lambda(s-2u)/2,
WITH EXPLICIT Re q>1/2 AND Re s>2. The ONE HALF is original half-square normalization. Do not silently replace it with full-square factor eight. Right-half restriction only belongs to arithmetic/fourLambda value; Fourier admission and Gamma–L-series identity apply to every Xi q. No RH, source-bound, interchange or arithmetic-identification premise added. This is a component of native J, NOT whole native J or its physical continuation.

## Audit and installation complete
All eight scratch lake env lean checks passed. All eight final individual canonical lake build <module> passed serially in isolated cache-only workspace. No warnings; final CompletedValue emitted harmless informational ring_nf suggestion. Exactly 37 new public theorem axiom closures returned only propext, Classical.choice, Quot.sound; none used Lean.ofReduceBool. Axiom probe initially could not resolve new cache artifacts; adding only the 16 new olean/ilean artifacts to private import cache resolved it; all 37 then checked successfully. No old axiom re-audit.
Eight canonical sources and 16 olean/ilean artifacts installed with byte verification; 24 hashes reverified twice and immediately before cleanup. Eight imports wired exactly once into RHTower.lean following BMNativeCutoffMellinValue. No umbrella/full build. New source dependencies are canonical.
One index refresh completed. One static lint --check-generated exited 1 with exactly four unrelated HTGeometry modules unreachable from their umbrella: FokasLenellsContourFifth, FokasLenellsContourMoment, FokasLenellsOriginIntegrability, FokasLenellsOriginWeightedProfile. No errors in new HB leaves, no proof-debt or generated-index error. Do not chase other tasks' live modules or repeat gate without justification.
Scoped whitespace and new documentation links passed. Owned foreground processes all terminal. Verified no owned Lean/Lake process remained. Removed only /tmp/hb-native-fourier.YZVXeY (resolved /private/tmp/...), including private hardlinked dependency cache, audit workspaces/logs. No marker existed. Installed files remain intact.

## Durable docs
New formal proof card docs/drafts/pipeline/3-formalized/hb-native-fourier-mellin-value.md has exact math, proof, 8-leaf audit, lint outcome, remaining scope.
Active docs/drafts/pipeline/1-in-progress/hb-native-square-residual-mellin-value.md now marks Fourier interchange/evaluation closed and identifies next constant/cutoff assembly target.
Physical hb-qnm-parameter-continuation.md has closed original Fourier diagonal section; old cutoff Mellin proof card links it.
STATUS F20i-y adds route-independent requirement: retain original complex source when norm majorants justify interchange, with new exact theorem evidence. Frontier map NOT edited.

## Next actual mathematical obstacle
Already native J=Lambda(2s)*integral y^(s-2)[A_u^2/2+4sum a_N^2-C_q(y)]. Full cutoff orbit P_h=h_q+P_nonparabolic, latter zero at y>=1/2, h_q=eta*A_u^2/2. Prior batch proves admitted reflected lower cutoff moment:
Lambda(2s) integral_(0,1/2] y^(s-2) C_q(y)dy=Lambda(2s-1) integral_(2,∞) y^(-s-1)h_q(y)dy, Re s>2.
Next derive exact original constant/cutoff combined contribution KEEPING (1-eta)A_u^2/2 together. Do not split separately divergent parabolic integrals at infinity. Assemble whole native J with actual Fourier value before claiming a fourLambda formula. Then derive meromorphic continuation agreeing with that original combined integral on its convergence chamber and reaching s=q/2 (outside current chamber). Original outgoing response, physical advanced/adjoint left pairing, complete source nonvanishing, independent extinction still open. No reason for numerical experiments for these deterministic analytic steps.

## Corpus research and useful Lean details
Broad Parseval search exposed 320 declarations/112 modules, Ramanujan 274/36. Read original paired-wave means, positive row/mean and modular source bounds, actual two-K Mellin capstone, underlying Ramanujan product and generic mixed-source algebra. Fokas/Higgs user searches were already fully delivered in previous turn (1727 declarations/113 modules and 285/26); no repeat required. See mem:hawking_bm_native_cutoff_orbit_mellin_2026_09_09 for previous batch/search context.
Use explicit starRingEnd ℂ for conjugation; integral_conj/integral_ofReal/integral_re are root declarations. Typed lambda integral equalities avoid rw failure from Pi.add/Pi.pow. ContinuousAt.comp needs explicit f for y->![0,y] or Lean chooses wrong vector partial application. Use Real.rpow_eq_pow for original amplitude square-root algebra. Avoid rw [<- hp] with hp product=1 (rewrites every 1); calc and forward rw suffice. Qualify D4BMGlobalAngularResponse.center in simp (Set.center ambiguity). No integrable_tsum helper by guessed name; actual DCT series + integral_tsum_of_summable_integral_norm used. ArithmeticFunction.coe_zeta_mul_apply is complex coefficient theorem. Avoid huge shell *.lean globs; rg directory --glob '*.lean'.
