FZZ-P-D1 source-global holomorphic exact-Fermi generator route killed and formalized.

Artifact:
- Lean: formal/GaloisForLFunctions/RHTower/FZZCigarParitySourceGlobalHolomorphicFermiFlowNoGo.lean
- Card: docs/drafts/pipeline/3-formalized/fzz-p-source-global-holomorphic-fermi-flow-no-go.md
- Umbrella import added to formal/GaloisForLFunctions/RHTower.lean.

Capstone:
RHTower.not_exists_analytic_horizontalRealPart_eq_fzzCigarParityReflectedFermiInformationVelocity.

Proof chain:
1. fermiMellinNormalizer σ >= (exp 1 + 1)^-1 / σ, hence log partition -> +∞ at σ->0+.
2. MVT + strict log-mean monotonicity gives fermiLogMean -> -∞.
3. Positive reflected variances imply exact FZZ reflected-Fermi force -> -∞, velocity -> +∞.
4. If holomorphic G on 0<Re z<1 has Re G(z)=v(Re z), exp(G(z+it)-G(z)) has constant modulus, hence is constant. Differentiate: G' vertically invariant. Existing open-strip profile rigidity makes G' constant; MVT makes v affine.
5. Affine v is bounded near 0, contradicting exact velocity blow-up.

Positive survivor:
Every holomorphic horizontally stratified generator has affine horizontal profile. Exact FZZ/PW realization must introduce ordinate dependence, antiholomorphic/Wirtinger structure, singular boundary-domain behavior, or divisor/source feedback.

Audits:
- lake env lean source PASS.
- targeted lake build module PASS.
- #print axioms only propext, Classical.choice, Quot.sound.
- no banned declarations.
- formal_tools lint was run; global red only from unrelated concurrently owned unwired RiemannGaussian/RatFuncLaurentDifferential modules, no error in this module.
- No computations used.
- Goal remains active; this kills implementation class, not full FZZ-P/PW-B route.