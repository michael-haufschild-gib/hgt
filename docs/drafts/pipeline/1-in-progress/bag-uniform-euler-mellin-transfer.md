# BAG uniform Euler control and actual Mellin transfer

01at. Route BAG. M1 actual complete pointwise source now Lean proved;
M2 entire mixed profile has zero signed vertical integral. These results
close genuine source/leading-profile gaps. Hard next problem: transfer
cancellation under the actual full moving Mellin integral.

Conjecture U1: for each A>=0 there are c_A,C_A>0 such that eventually in N,
for every real a with |a|<=A and every real tau, the ORIGINAL product
Q_N(a/logN+i*tau)=product_(p<=N)(1-p^(-1-a/logN-i*tau)) satisfies
c_A <= |Q_N|*|zeta(1+1/logN+i*tau)| <= C_A.
No compact-frequency restriction. Uniform comparison, not constant
optimization, is the missing ingredient for an integrable mixed bound.

Corpus mechanism: Sieve.PrimeCosineSum exact head/tail split,
PrimeTailBound.tsum_primeTailTerm_le, PrimeSigmaShift.abs_sum_weight_shift_le,
ZetaLogPrimeSum.abs_log_norm_riemannZeta_sub_tsum_re_le, EulerLogCompare.
At a=0 the logarithms differ from the same prime cosine sum by bounded
quadratic remainders, bounded head abscissa shift, and bounded prime tail.
For signed a/logN, finite log-product change costs at most
C*exp(A)*|a|*sum_(p<=N)(logp/p)/logN: every local nome eventually has
modulus <=2^(-3/4)<1; the difference of nomes costs
exp(A)*|a|*logp/(p*logN). MertensFirst closes this uniformly.
All finite factors are nonzero since their real exponent exceeds3/4.

Next U2: on bounded frequencies the filled residue (s-1)zeta(s)
is continuous/nonzero on Re(s)>=1. Hence |Q_N| is comparable to
1/logN+|tau|. Mixed compact sectors should then have source/logN^2
bounded by C/(1+|logN*tau_near|)^2. Prove the full masked/leave-one-out
source bound; never assume rational row denominators globally nonzero.
Combine with M1 and M2; joint box needs its own removable mass control.

Actual physical profiles are N-dependent with shrinking relative edge
layers. Do not assume a fixed Schwartz profile, bounded seminorms, a
stationary replacement, or negligible global tails. These remain hard
source obligations after any compact arithmetic cancellation theorem.
Plan: exact U1 paper proof -> symbolic Lean -> audited uniform source
bound -> actual physical integral, preserving both cofactors and masks.
No computations, subagents, blanket build or added premises.

01at U1 scratch34083 emptyPASS; production98291 emptyPASS after removing
unneeded CharacterDistanceGrowth import. New leaf
ChiRamanujanUniformEulerComparison302lines/API1; umbrella wired once.
Axiom61123 and index76878 running. This closes unrestricted-frequency
Euler comparison; no growing integral interchange follows yet.
Search53080 nonpartial65973files gen1247538;coverage1247544/current1247547,
noerrors,refreshincomplete; all20candidate+20source inspected. Retrieved
actual finite cubic majorant and full labelled product. For full source
bounds use products excluding the <=3 labelled primes; dividing by the
unlabelled local factor can fail at its zeros. All local Euler complements
are bounded away from zero when real exponents stay>=3/4.

U2 paper consequence: existing exists_residue_global_polynomial_disks
provides a single M>0 with |R(s)|,|1/R(s)|<=M*(1+|t|)^9 for
s=1+1/logN+it, N>=3, R(s)=(s-1)zeta(s). U1 gives
exp(-B)<=|Q|*|zeta(s)|<=exp(B). Therefore with C=exp(B)*M,

  |s-1| <= C*(1+|t|)^9*|Q|,
  |Q| <= C*(1+|t|)^9*|s-1|.

This is uniform in ALL t and |a|<=A, eventual N. No zero-free or residue
premise is added. On compact frequencies this yields the pole-scale
comparison |Q| comparable to 1/logN+|t|; the global weighted form is stronger.
It is a direct dependency-closed consequence, now being formalized.

01at U1 CLOSED: ChiRamanujanUniformEulerComparison302lines/API1,
criticalFiniteEulerProduct_zeta_comparison. All frequencies and bounded
signed logarithmic displacement, original prime cutoff. Scratch34083 and
production98291 emptyPASS, axiom61123standard3, index76878PASS/API/importonce.
Lint15525terminal1:one unrelated CompletionLogDerivZeroPairs unreachable,
174warnings,noneowned. P2/P3/frontier current. No integral saving inferred.
U2 actual global pole-scale comparison now scratchauditing: existing residue
factor bounds yield |s-1| <=C(1+|t|)^9|Q_N| and reverse inequality uniformly.
Full labelled bound will retain finite products with <=3 primes removed;
local unlabelled zeros rule out blindly bounding rational responses.

U3 full-source mechanism derived from actual local identities (01at):
set alpha=rho1/L+i*t1,beta=rho2/L+i*t2, z=1/p, a=p^-alpha,b=p^-beta.
For an unmarked prime, H_p=(1-za)(1-zb)*weightedEuler z (za)(zb)
equals C_p*(1-z*b/a)*(1-z*a/b)/((1-z/a)*(1-z/b)). For each marked prime,
the same cofactor-completed factor is EXACTLY responseNumerator k z a b,
using MixedLabelRows.responseNumerator_eq; k=3 retains the allowed p=q
collision. There are <=3 marked primes. These numerators are uniformly
bounded on z in[0,1/2] and the compact annuli exp(-A)<=|a|,|b|<=exp(A).
They have no denominator responseBase. Thus their bound survives every
zero of the unlabelled local factor.

The remaining finite C_p product is uniformly bounded by
exp(sum cubicMajorant*p^-3/2), even with the marked primes removed.
Restoring the <=3 removed factors of the two numerator and two denominator
Euler products costs a constant only: all local nomes have norm<=3/4.
Thus every original completed label product is bounded by a constant times
its three logp/p weights, normalization^3, the two zeta factors, and
J_N=|Q_N(beta-alpha)*Q_N(alpha-beta)/(Q_N(-alpha)*Q_N(-beta))|.
Summing the original mask costs at most (sum logp/p)^3; Mertens normalization
cancels this cubic scale. No collision is discarded, and no responseBase
is divided out.

Combining U2 and existing residue bounds suggests the complete actual bound
|Z_N(t1,t2)| <= C*(1+|t1|+|t2|)^54 *
  [L^2/(1+(L*t1)^2)+L^2/(1+(L*t2)^2)]
for fixed positive rho1,rho2, eventual N, ALL real t1,t2. The real pole
shifts rho_i/L are comparable to1/L with constants depending on rho_i.
The difference numerator satisfies epsilon^2+(t1-t2)^2 <=
2*((epsilon^2+t1^2)+(epsilon^2+t2^2)). This is U3, not yet Lean proved.

U4 proposed consequence: (1/L)*integral Z_N*Psi ->0 for every FIXED Schwartz
Psi. Uniform weighted total variation follows from U3. Near one axis,
rescale t1=x/L; M1 gives exp(-2gamma)*G(rho1+i*x), whose whole signed integral
is zero by M2. Opposite axis needs exact source symmetry. A joint box of
widthdelta contributes O(delta), then delta->0. Away axes vanishes;
Schwartz tails follow from U3. Formal proof and exact decomposition remain.
This is fixed-test cancellation only; actual physical Psi_N is not fixed.

Physical research target retained: normalized actual Mellin profile
Psi_N=(logN)^3/N * actual moving physical profile. Its scale-dependent
cutoffs have shrinking edge layers. A fixed-test theorem cannot be applied
by substitution. Need a proved source-weighted tail/compactness theorem or
a direct signed integral estimate. Possible mechanism to investigate:
integration in the full original height variable smooths the limiting
cone cutoff before taking its two-variable Mellin transform. No uniform
Schwartz seminorm, stationary replacement, Sobolev regularity, or physical
cancellation has been established by this paragraph.

01at U2 CLOSED: ChiRamanujanUniformPoleControl/API1,
criticalFiniteEulerProduct_pole_comparison. Original finite Q_N has two-sided
pole-distance control with global frequency weight. Scratch84975 and
production74521 emptyPASS; axiom58622standard3; index13262PASS/API/importonce.
Lint14201terminal1:3 unrelated unreachable modules,174warnings,noneowned.
P2/P3/frontier current. U3 full actual labelled envelope dependency-closed
paper now P2 bag-uniform-complete-source-envelope. Lean compact numerator,
finite regular product and nonvanishing Euler-ratio controls are auditing
in /tmp/bag-uniform-local-01au.lean. No unlabelled local-factor inverse is
introduced. Actual physical-profile/tail transfer remains hard open.

01au formal U3 factor bound: compact numerator controls, exact four local
replacements (including p=q), local Euler-ratio lower bound, finite product
bound and full masked norm sum are now in one scratch. Both original
cofactors attached; Mertens normalization pays the entire three-label mass.
The only remaining last audit error was final commutative rearrangement;
corrected and foreground77483 running. Main actual-source contract:
criticalCompletedConeEuler_uniform_factor_bound, for fixed positive rho_i
and ALL real frequency pairs, eventual original cutoff. No local unlabelled
nonvanishing or analytic estimate is a premise. Still not production/audit
complete. Scratch /tmp/bag-uniform-local-01au.lean is current,596lines.

Search58644 nonpartial65987files gen1247932,coverage1247938/current1247941,
noerrors,refreshincomplete; all20candidate+20source inspected. It retrieves
old fixed-test cubic kernels, not the new growing source envelope. Exact
source/mathlib norm components verified. Next scratch
/tmp/bag-uniform-envelope-01au.lean develops poleSize=1/logN+abs(t), its
comparison with actual complex pole distance, and the global moving-zeta
bound. Not audited yet. Intended envelope can use the equivalent integrable
kernel L^2/(1+L*abs(t))^2; constants unspecified, no numerical optimization.

Two failed edit invocations accidentally launched unchanged scratch builds:
80048 and71463; both immediately terminated using their exact owned PIDs,
terminal143 confirmed before replacement. No other process touched.
All subsequent mutations use verified tool patches/separate execution.

01au U3a CLOSED: original full masked/cofactor source bounded uniformly by
both zeta and exact four finite Euler factors. All realfrequency pairs,
positivefixedrho_i,eventualoriginalN; no local unlabelled inverse/premise.
Scratch63282PASS; production58554emptyPASS,590lines/API1 afterunusedprivate
helpers/importsremoved. Axiomprintedstandard3 incleancombinedscratch57460
PASS (oneprivateunusedbinderwarning nowfixed). Index10670PASS/API/importonce.
Lint99416globalFAIL:7 unrelated unreachable plus HTGeometry/HankelSingularHeight
line75 active sorry,174warnings; noneowned. P3/frontiercurrent.
Full integrable axes envelope scratch42221 running, combining U3a with U2
and unconditional moving-residue bounds. No numerical experiment/RH claim.

01av U3b CLOSED: ChiRamanujanUniformSourceEnvelope323lines/API1,
criticalCompletedConeEuler_uniform_axes_bound. Entire original source,
all frequencies, fixed positive rho_i, original growing cutoff. Polynomial
weight T^54 times the two L²/(1+L*abs(t_i))² profiles. Scratch22515PASS;
production14320emptyPASS; axiom44362standard3; index37670PASS/importonce;
lint2483terminal1:nineunrelatedHTGeometryunreachable,174warnings,noownederror.
P2/P3/frontier current. Raw envelope still needs test decay.
New U4 nearest-axis partition removes separate joint-box/compact-uniform
steps for fixed tests; P1 bag-signed-source-sector-transfer contains full
paper mechanism. Actual moving physical profile/tails still hard open.
