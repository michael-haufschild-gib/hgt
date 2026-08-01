CJKP-1 formalized literal RHT source closure after JKPIT-1.

New module:
formal/GaloisForLFunctions/RHTower/CCMFirstClockJuliaKMSPrimePowerResolution.lean
Card:
docs/drafts/pipeline/3-formalized/needs-audit/ccm-julia-kms-prime-power-resolution.md
Working log appended:
docs/drafts/pipeline/1-in-progress/rh-whole-formal-corpus-frontier-audit.md
RHT umbrella wired.

Whole-corpus collision audit consumed, did not rediscover:
- CCMFirstClockBlockSubdivisionTransfer already has criticalMellinAtomWeight = Lambda * oddBlockFock degree-one defect.
- VonMangoldtGammaDepthOneCauchy already has literal depth-one Gamma anomaly + Julia/Stinespring factorization.
- VonMangoldtGammaJuliaBianchiJointGram already has forced finite cross block.
- CCMFirstClockJuliaScaleFourTransfer resolved continuous Gamma only.
- prior Julia prime-order attenuation cannot distinguish exponents.

New math:
D(x)=1/(2sinh x), J(x)=D(x)-4D(4x).
D(h/2)(1-exp(-h))=exp(-h/2).
Thus for q>=2:
criticalMellinAtomWeight(q)=Lambda(q)(1-q^-1)D(log q/2).
Also formalized exactly through finiteExponentialDepthOneAnomalyCoefficient.
Define literal layers L_j(q)=Lambda(q)(1-q^-1)4^jJ(4^j logq/2), tail T_n similarly.
Then w(q)=sum_{j<n}L_j(q)+T_n(q), layers nonnegative, layers/tail strictly positive on prime powers.
Entire ccmFirstClockPrimeSineMass has exact atomwise finite innovation telescope.
Formal phase no-go: negative sine phase remains negative at every positive layer.

New exponent-sensitive order law:
F(x)=1-1/(cosh x cosh2x) is first captured fraction, strictly increasing x>0.
R(x)=1-F=1/(cosh x cosh2x) strictly decreasing.
L_0(q)=w(q)F(logq/2), T_1(q)=w(q)R(logq/2).
For 2<=q<r, F_q<F_r and R_r<R_q; this distinguishes p^e vs p^f unlike prime-base attenuation.

RH limit:
still diagonal in q; sign of each counter-phased atom preserved. First-clock sine has alternating bands, so one monotone filter cannot isolate both negative bands. Open core: non-diagonal cross-frequency or inter-scale quadratic inequality before sine evaluation, likely use existing forced VonMangoldtGammaJuliaBianchiJointGram.

Audit:
direct Lean green;
lake build GaloisForLFunctions.RHTower.CCMFirstClockJuliaKMSPrimePowerResolution green 9377/9377;
11 capstones axioms exactly [propext, Classical.choice, Quot.sound];
lint new module clean, global lint fails only unrelated umbrella gaps RHTower.ZetaGammaProjectiveHorizonSchwarzianDiamond, HTGeometry.ProjectiveHorizonActualSchwarzianDiamond, HTGeometry.SymmetricGroupCommutator.
Not RH.