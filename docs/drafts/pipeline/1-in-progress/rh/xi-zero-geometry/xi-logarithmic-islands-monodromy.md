# Logarithmic inverse islands and finite joint monodromy

- **ID:** RH-XILIM-20261007
- **Stage:** 1-in-progress; C1-log and C2-finite fully formalized; novelty and further scope audits continue
- **Parent:** `xi-marked-joint-monodromy.md`
- **Related:** `../2-fully-proven/xi-finite-cover-monodromy.md`
- **Verdict:** SURVIVES PRELIMINARY ATTACK; novelty not certified

## Exact competing claims

C1-log: For every real a and positive M,R there is a holomorphic map h on
D(0,M), taking values in Re(s)>R, such that
xi(h(w))*exp(-a*h(w))=exp(w) for every w in that disk.
There is no premise concerning zeros, RH, or critical values. Its derivative
identity makes h locally injective. These inverse islands are much stronger
than mere occurrence of every nonzero value far to the right.

C2-finite, strengthened and formalized: for every finite real slope set A,
write Gamma as product_(a in A) pi1(C minus {0,-1},1/2), mu for the actual
marked-source monodromy, and w:Gamma->Z^A for zero winding. For every
homomorphism q:Gamma->G with G finite, q(image mu)=q(w^(-1)(diagonal Z)).
Surjectivity is unnecessary and the empty family is included. This is a
finite-image statement; it does not assert equality of the discrete image.
The discrete normal closure does equal w^(-1)(diagonal Z). Both endpoints
are fully audited on `../../../3-formalized/xi-marked-finite-monodromy.md`.

Competing obstruction: logarithmic critical/asymptotic values may prevent
arbitrarily large inverse disks. If that happens, determine their exact
location and retained finite monodromy obstruction. Generic Schottky value
existence alone cannot decide this, and unrelated entire functions need not
have these islands. Even C2-finite would not supply a divisor-selection law
or prove RH.

## Analytic paper proof

On the simply connected half-plane Re(s)>1, the nonvanishing holomorphic
function d_a=xi*exp(-a*s) has an analytic logarithm L_a. No normalization of
its imaginary part is needed. Its derivative is

L_a'(s)=1/s+1/(s-1)+(1/2)*psi(s/2)-(1/2)*log(pi)+zeta'(s)/zeta(s)-a.

Put C=sum_n |Lambda(n)/n^2|, finite by absolute convergence at2. For sigma>=2,
termwise norm monotonicity bounds |zeta'/zeta(s)| by C. The corpus's
`DigammaVerticalMinimum.digamma_real_le_re_digamma_add_mul_I` and
`DigammaTwoSided.log_sub_inv_le_re_digamma` give
Re psi(s/2)>=log(sigma/2)-2/sigma>=log(sigma/2)-1.
The two rational terms have nonnegative real part. Consequently
Re(xi'/xi)(s)>=(log(sigma/2)-1-log(pi))/2-C.
This explicit bound tends to infinity with sigma, uniformly in Im(s).
Choose R_a>=2 making this lower bound at least a+1. Then
Re L_a'(s)>=1 throughout Re(s)>R_a. These inputs have been read in the
actual corpus; no critical-strip statement or RH assumption is used.

Integrating on the straight segment in the right half-plane gives
Re((L_a(z)-L_a(v))/(z-v))>=1, hence
|L_a(z)-L_a(v)|>=|z-v|. In particular L_a is injective and has no critical
point. For a disk centered at s with radius r<Re(s)-R_a, Rouche applied to
L_a(z)-L_a(s) and the constant target perturbation shows that its image
contains D(L_a(s),r). Injectivity and the inverse-function theorem make the
inverse holomorphic. No compact-surface uniformization or Koebe theorem is
needed for this step.

Fix requested M,R>0 and choose B>=max(R,R_a). The already formalized
`RHTower.exists_xi_tilt_eq_of_nonzero` supplies z with Re(z)>B+M+1 and
d_a(z)=1. That theorem uses Schottky growth and Xi ray growth, independently
of the present inverse-island argument. Choose r=M+1. The closed source disk
lies in Re(s)>B. Apply the preceding image-disk argument there to obtain a
holomorphic inverse H on D(L_a(z),r), taking values in D(z,r). Define
h(w)=H(L_a(z)+w) for |w|<M. Then Re(h(w))>B>=R and
d_a(h(w))=exp(L_a(z)+w)=d_a(z)*exp(w)=exp(w). This proves C1-log.
It also gives injectivity of h and h'(w)!=0 by differentiating the identity.

Dependency closure: the only analytic constructions beyond the listed
corpus results are the holomorphic logarithm on a simply connected zero-free
domain, the fundamental theorem along a segment, Rouche on a closed disk,
and the holomorphic inverse-function theorem. Their hypotheses were checked
above. The original vertical-decay/implicit-level-curve detour is unnecessary.
Lean implementation of these constructions remains pending; paper proof has
no open mathematical premise.

## Finite joint paper proof

Let K_n be the kernel of zero winding in the nth free group, embedded in
Gamma, and K their product. The ratio d_m/d_n=exp((log n-log m)*s) implies
zero-winding vectors of all actual source loops are diagonal; hence
image(mu) is contained in w^(-1)(diagonal Z).

A finite list of based loops from K_n lifts under exp to closed logarithmic
loops in C minus the odd multiples of pi*i. Their compact images fit in one
disk D(0,M), also containing a common logarithmic basepoint. Apply C1-log for
a=log n with R sufficiently large. On this whole disk, for m>n the other
marked values have modulus <1/2, and for m<n they have modulus >2, since
|d_m(h(w))|=exp(Re(w)+(log n-log m)*Re h(w)). The other marked functions are
nonzero exponentials on the whole disk and avoid -1 there, so their loop
images are nullhomotopic. The nth component realizes the selected loops.
Connecting the source basepoint conjugates this entire finite packet by one
element of Gamma. Such a connecting path exists: the deleted set is a finite
union of discrete zero sets of nonzero entire functions, hence locally finite;
its complement in the plane is path connected. Choose once a target path
from the original nth target basepoint to1. This identifies K_n with closed
zero-winding loops based at1; their exponential lifts start and end at0.
Comparison with the image of the source connecting path is a single loop,
so the conjugator is common to every loop of that packet. Other coordinates
stay trivial under this basepoint transport.

For a fixed finite quotient G, choose a finite packet whose q-images generate
q(K_n). This subgroup is normal in G, so the common conjugation leaves it
unchanged. Thus q(image mu) contains q(K_n) for every n and hence q(K).
An actual simple Xi zero supplies a source meridian with zero-winding vector
(1,...,1). In Gamma/K=Z^S its image generates the diagonal. Together with
the upper inclusion, this proves C2-finite. The basepoint transport and the
normality argument must be made explicit; conjugators may vary with n and
with the chosen finite quotient, which is why discrete equality is not claimed.

The same islands at w=pi*i give isolated simple zeros of 1+d_n away from all
other marked divisors. Together with a simple Xi zero they show that the
parent divisor lattice is exactly diagonal Z in the a-coordinates plus all
of Z^S in the b-coordinates. This identifies C2-finite as the finite-quotient
version of the parent's C1, rather than an unrelated maximality claim.
The reverse lattice inclusion follows at every divisor point: xi has the same
order in each d_n (the exponential factors are units), and all auxiliary
orders are integers. Xi zeros never coincide with auxiliary zeros because
1+d_n=1 there. A small meridian around the actual simple Xi zero therefore
has exactly the diagonal a-vector and zero b-vector. The empty set S gives
the trivial group and lattice. These observations cover all finite S.

## Audit started

Direct deep query: `xi logarithm inverse disk Stirling right half plane a
point simple univalent`, output `/tmp/rh-xi-log-islands-search-20261007.json`.
This card was created while the rational-factor final assembly was checking;
that predecessor remains the active code task. External exact ancestry and
hostile statement audit are pending. No scientific novelty claim yet.

Corpus audit update: deep query returned partial=true (decomposition worker
disconnected), inventory68216; all twenty candidate and twenty source
statements plus proposed ingredients inspected. Useful actual sources:

- `RHTower/DigammaVerticalMinimum.lean`, lines30-123 read: exact
  `digamma_real_le_re_digamma_add_mul_I` and `re_logDeriv_Gammaℝ_real_le`.
- `HTGeometry/GammaDigammaStirlingBound.lean`, lines220-296 read:
  `norm_digammaStirlingDefect_le`, defect=psi-log+1/(2z), with bound6/|z|^2
  on Re(z)>0, |z|>=2. This provides a direct uniform real-part lower bound
  and can replace the separate real-digamma divergence proof. Existing file
  has a scoped large-heartbeat option; do not copy or change that option.
- `RHTower/XiWardInteriorTraceSplit.lean`, lines215-290 read: exact
  `logDeriv_xi_eq_arithmetic` opens the two poles, Gamma_R, and negative
  von Mangoldt L-series. Absolute L-series summability at2 is already in
  mathlib; monotonicity of term norms in Re(s) gives one uniform constant
  for Re(s)>=2. Tending that constant to zero is unnecessary: logarithmic
  digamma growth eventually dominates it.
- `RHTower/XiStripInverseDecay.lean` read through its end: uniform decay of
  XiC on every bounded horizontal strip. Rotate back to xi to get decay on
  every fixed vertical line, with no fresh Gamma vertical asymptotic proof.

External first audit: Goldstein--Grigutis, J. Math. Inequal.18(2024),829-845,
DOI10.7153/jmi-2024-18-45, introduction read. It cites Lagarias' vertical
minimum for Re(xi'/xi) at sigma>10, later improved by Garunkstis. Thus the
far-right derivative input is classical, not itself a novelty claim. Source:
https://files.ele-math.com/articles/jmi-18-45.pdf. None of its conditional
critical-strip discussion is an input here. Exact inverse-island and joint
finite-monodromy ancestry audit remains active.

Second hostile audit, 2026-10-07: Alvarez-Parrilla--Mucino-Raymundo,
`Geometry of transcendental singularities of complex analytic functions and
vector fields`, arXiv:2205.13588v2, Complex Manifolds11(2024),0005,
DOI10.1515/coma-2024-0005. Full PDF text extracted; all Xi/monodromy hits and
pp53-55 (§6.3 and §7) read. Its Xi application studies the time integral
integral dz/xi(z), not the inverse of xi; §7 explicitly leaves the latter
perspective for further work. It does not settle C1-log or C2-finite.
Primary source: https://arxiv.org/abs/2205.13588.
Exact inverse-island / joint-monodromy searches returned no exact antecedent;
this is a limited negative search result, not a novelty certificate.
Analytic inputs and the inverse-disk lemma are BRIDGE material. C2-finite
remains SURVIVES PRELIMINARY ATTACK relative to the inspected sources.

Formal construction plan: first prove the unconditional uniform far-right
lower bound for Re(xi'/xi); then the generic half-plane logarithm and inverse
disk lemma; then instantiate C1-log. Separately assemble the finite-packet
topology and normal-subgroup argument, retaining the finite-quotient scope.
No RH consequence is claimed at any of these intermediate stages.

Construction checkpoint: `RHTower/XiLogDerivFarRight.lean` now proves the
absolute-series bound at2, the explicit logarithmic lower bound above, and
`exists_re_logDeriv_xi_ge_halfPlane` with no analytic premise. Scratch Lean
check and targeted `lake --old build +...XiLogDerivFarRight` pass; leaf wired
into RHTower. Final actual-source and public-axiom audits remain pending.
Imported digamma and Xi arithmetic identities have standard axiom closures.

Second corpus query, `positive real derivative holomorphic injective
coLipschitz logarithm half plane inverse ball`, returned partial=true
(text retrieval interrupted), inventory68221. All20 candidate and20 source
statements inspected; proposed ingredient grouping mostly irrelevant.
Useful exact hit: `Bottcher/Univalence.lean` (read completely),
`Bottcher.injOn_of_re_deriv_pos`, standard axioms verified. It supplies the
Noshiro-Warschawski step. Quantitative expansion follows by applying it to
f(z)-c*z for |c|<1, excluding any difference quotient with modulus<1.
Mathlib `Analysis/Complex/OpenMapping.lean` lines1-90 read: its
`DiffContOnCl.ball_subset_image_closedBall` supplies an image disk with half
the boundary lower bound. Use source radius2*M+2 instead ofM+1; this proves
the same C1-log and removes any need to formalize Rouche. The inverse can be
`Function.invFunOn` on the open half-plane, with holomorphy obtained from
`HasStrictDerivAt.to_local_left_inverse`. No inverse continuity premise is
needed there. The normalized primitive uses `RightHalfPlanePrimitive`.

Analytic construction checkpoint2: both generic leaves build. The actual
`RHTower.exists_xi_tilt_exp_lift_ball (a M R : Real) (hM : 0<M)` passes Lean:
there exists h holomorphic on ball(0,M), with Re(h(w))>R and
xi(h(w))*exp(-a*h(w))=exp(w) throughout. R is arbitrary, with no positivity
restriction. Four leaves are wired; targeted Xi build followed by four actual
source audits and seven public axiom audits is running in one owned chain.
No final-audit success is yet claimed. Proof uses no raised heartbeat option.

Final analytic audit now PASS: four targeted builds, four actual-source checks,
seven public standard-axiom closures, four unique imports, exact scratch/source
comparisons followed by removal of four obsolete proof scratches. Closed
child: `../../../3-formalized/xi-logarithmic-inverse-disks.md`. This supersedes the
pending-audit status in the preceding checkpoint. Global lint exits1 on six
unrelated HTGeometry leaves listed in the child. Index refresh now exits0,
regenerating LEAN_API, LEAN_GAPS, LEAN_OVERVIEW; evidence
`/tmp/rh-xi-islands-index.log`.

Topology discovery query: `fundamental group punctured complex plane
exponential covering winding kernel path lift`, deep300s, partial=false,
inventory68227; all20 candidate and20 source statements and ingredients read.
`Bottcher/Pi1CMinusZero.lean` has actual exponential cover, lift endpoint
degree, degree bijection, and multiplicative/transitive loop laws.
`Bottcher/WindDynamics.lean` has winding of arbitrary continuous nonzero
functions, product additivity, and vanishing for an exponential. Read its
lines1-145 and Pi1CMinusZero lines1-125,426-472. `HTGeometry/TorusChartFundamentalGroup`
lines1-80 and `RHTower/PrimeAFComplexUnitsKOne` lines1-105 also give actual
fundamental-group/exponential-period equivalences. Prefer these existing
carriers over a fresh winding abstraction. Countable-complement path
connectedness is already available and avoids a separate local-finiteness
path construction.

Next analytic assembly: the islands separate every finite set of distinct
real exponential slopes, not only integer logarithms. Choose R>0 such that
|a-b|*R>M for all other slopes b. On an a-island,
log|d_b(h(w))|=Re(w)+(a-b)*Re(h(w)); its absolute value is positive because
|Re(w)|<M<|a-b|*Re(h(w)). Thus d_b avoids the entire unit circle on the
whole logarithm disk. This strengthens the modulus-separation input and
supplies the exact domain for the coordinate-nullhomotopy construction.

Separation scratch now passes Lean. Before promoting the simple marked-value
corollary, the exact corpus comparison found
`XiSignedFactorZeroSeparation.exponential_translate_label_injective_at_zero`:
equal-radius coefficients of norm greater than1/2 already have globally
disjoint translated Xi zero sets unless both real rate and coefficient agree.
Thus all-real-label isolation alone is already established. The stronger
new formal target is arbitrarily far-right **simple** minus-one points.

Its dependency-closed proof: choose B>=2 with Re(xi'/xi)>=a+1 on Re(s)>=B.
The existing nonzero-value occurrence theorem gives d_a(s)=-1 beyond max(B,R).
Then d_a'(s)=d_a(s)*(xi'/xi(s)-a) is nonzero because the second factor has
real part at least1. Hence the zero of1+d_a has analytic order1. If d_b(s)=-1
too, taking norms of the exact ratio gives exp((a-b)*Re(s))=1, forcing b=a
because Re(s)>0. This last argument independently recovers the needed local
separation, but is not claimed as new knowledge. Verdict BRIDGE: these two
analytic consequences assemble inputs to C2; they do not prove C2 or RH.

Topology assembly checkpoint: both analytic leaves now pass scratch Lean and
targeted builds. Their actual-source/axiom closure audit is running. Generic
closed-logarithm lifts have been written from the existing exponential-cover
endpoint degree; finite unions of compact path images supply one disk.
Actual source-space and packet proofs are written in scratch, not yet checked.
The source basepoint can be fixed at0: every real marked value there is1/2.

Normal-packet corpus query `normal subgroup finite conjugation packet image`
returned partial=false, inventory68234, no exact prior packet theorem.
All20 candidate and20 source statements inspected. Useful existing primitives:
Subgroup.Normal.conj_mem/conj_mem' and Subgroup.mem_map. Compiler metadata is
mostly source-only and background index refresh incomplete; applicability will
be checked in this toolchain. No new scientific claim for this elementary step.

Refined dependency-closed group statement: if N is normal in Gamma and every
finite subset T of N has one conjugate lying in H, then q(N)<=q(H) for every
homomorphism q to a finite group. Surjectivity is unnecessary. Choose one
representative t(y) in N for each y in finite q(N), then a common conjugator g
for their finite set. For n in N, normality puts g^-1*n*g in N. Choose the
representative with image q(g^-1*n*g). Its conjugate by g lies in H and has
image q(n). This proves the claim without requiring q(N) normal in the whole
codomain. It remains a BRIDGE to the actual Xi packet construction.

Final analytic consequence audit PASS: both new targeted builds and actual
source checks; all three public axiom closures standard. Closed child:
`../../../3-formalized/xi-separated-simple-marked-values.md`. Both leaves wired.
This supersedes the running-audit checkpoint above. Generic closed-log-loop
scratch now also passes; its final-source audit remains for topology assembly.

Both generic topology/algebra scratches pass: closed logarithmic loop packets,
and finite-image containment from commonly conjugatable normal packets. Their
targeted builds are running before the actual source-space scratch check.

Quantifier audit: C2-finite and its paper proof hold for every finite set of
distinct **real slopes**, not only integer logarithms. Replace log(n) by a
throughout. The separated-island theorem already proves exactly the needed
real-slope statement; countability of each auxiliary zero set and the common
source basepoint0 are unchanged. The finite normal-packet proof uses no
arithmetic property of the labels. This is the strengthened exact target of
the current formal assembly, still with the finite-image/discrete distinction.

Additional external ancestry check: Fried, arXiv:1012.5297v5 (2011), §7.2.5,
Lemma7.11 and discussion read at https://arxiv.org/html/1012.5297v5.
It records the classical Picard/uniformization obstruction: an algebraic curve
parametrized by nonconstant entire functions has compactification of genus0
or1, with related Laurent factorization results. This supports the BRIDGE
verdict of the earlier single-cover/rational-factor work; it supplies no
joint marked Xi finite-image theorem in the inspected passage. Broad exact
joint searches still returned no exact antecedent, not a novelty certificate.

Basepoint simplification: realize target packets directly at1/2, the common
value of every mark at source0. Normalize each target loop by its nonzero
basepoint, lift from0, then add a fixed logarithm w0 of that basepoint. All
translated closed lifts and w0 fit in one disk (include the singleton w0 even
for an empty packet). The island then has selected-coordinate basepoint1/2.
The selected image of any source connecting path from0 to the island base is
already a loop at1/2. Thus it supplies the common conjugator directly, without
an additional arbitrary target path or a winding basepoint-change lemma.
For other coordinates the disk nullhomotopy is unchanged. This is the same
dependency-closed C2 proof with simpler basepoint bookkeeping.

The actual finite marked-source domain now passes scratch Lean and a targeted
build: its complement is countable, so the domain is path connected; source0
maps to1/2 in every coordinate. The generic shifted logarithmic packet lemma
also passes, including the empty-index case by adjoining the basepoint to the
compact union. Actual packet realization is now checking at arbitrary target
basepoint. Its earlier basepoint1 version had only the final dependent-path
conversion unresolved; no analytic premise remained. Generic path transport
and common-conjugator comparison now pass scratch Lean. Final topology audits
remain pending until the actual packet result closes.

Packet cycle closed: `../../../3-formalized/xi-marked-loop-packets.md`. All five
actual-source checks and all25 public standard-axiom closures pass. Imports
unique, no admissions/heartbeat changes, matching scratches removed. Index
refreshed; global lint has five unrelated unreachable HTGeometry modules
listed on the child. Actual packet realization includes an arbitrary common
target basepoint. The next assembly fixes that point at1/2, packages existing
zero winding as a fundamental-group homomorphism, and constructs the common
conjugator in the actual joint image. Full C2 is still not formalized.

The actual common-conjugator and product-kernel inclusions now pass scratch
Lean in XiMarkedConjugatePackets (three public theorems). For each coordinate,
take representatives of an arbitrary finite kernel packet, realize it at1/2,
connect its source basepoint to0, and transport the entire packet along that
one path. Apply the finite normal-packet lemma to the coordinate embedding
preimage of the actual joint range. Subgroup.pi_mem_of_mulSingle_mem assembles
all coordinates. No surjectivity premise on the finite-group homomorphism.
NormalizedWindingHom, PointedPacketTransport and XiMarkedMonodromyMap also
pass scratch; final source/axiom audits remain pending for this assembly.

Simple-meridian search `simple analytic zero local inverse loop winding
degree one`, budget90, partial=false, inventory68260; all20 candidate and20
source statements inspected. Compiler enrichment remains mostly pending.
The existing WindingXi.windingNumber_xi_zero identifies a small-circle
winding with actual Xi order; CircleDegree.degZ_eq_of_lift identifies the
exponential-cover degree with any lifted endpoint. Their elementary bridge
uses the existing continuous logarithm on the real parameter line, composed
with the affine interval parametrization and subtracting its initial value.
Thus the existing simple-zero provider can supply a degree-one local loop
without repeating the analytic argument principle.

Basepoint plan for the final diagonal generator: normalize C* by division
by its basepoint, a homeomorphism, and use degZ bijectivity. A local loop of
degree1 makes the actual Xi map onto pi1(C*) at its local basepoint (integer
powers and injectivity). Naturality of path transport, already formalized,
carries surjectivity to source0. Normalized degree then supplies a source0
loop of degree1. This avoids a new winding invariance theorem for moving
basepoints; only surjectivity is required. The finite-image proof then removes
the diagonal winding by a power of that source loop and applies the already
proved product-kernel inclusion. This is a dependency-closed completion plan,
not yet a completed formal endpoint.

Finite-kernel cycle closed on `../../../3-formalized/xi-marked-finite-kernel-image.md`:
four actual-source checks and all17 public axiom closures pass, using only
standard axioms. This supersedes their pending audit note above. The winding
API bridge also passes scratch. Generic basepoint surjectivity and the actual
simple-zero meridian remain in scratch; no full finite-image equality claim.

Both generic bridges now pass scratch: real-parameter winding equals the
exponential-cover degree under affine interval parametrization, and a local
winding-one loop makes normalized winding onto at any joined source basepoint.
The latter uses normalization by a punctured-plane homeomorphism, degree
bijectivity and naturality of transport; no orientation choice is needed.

External follow-up: Eremenko--Lyubich, Ann. Inst. Fourier42(1992),989--1020,
https://www.numdam.org/item/AIF_1992__42_4_989_0.pdf, §2 pp993--994 read.
Its global logarithmic-coordinate construction assumes bounded singular
values of the inverse (class B), which has not been established here for Xi
or all its real exponential marks. It cannot replace our explicit local
inverse disks. Zelenko's 2021 generic inverse-monodromy theorem,
https://arxiv.org/abs/2105.14015, also does not identify this actual joint image.
Exact Xi/joint/profinite queries again supplied no exact antecedent among the
inspected results. This limited search remains insufficient to certify novelty.

Positive survivor exposed by the packet proof: the discrete normal closure
of the actual joint image is exactly the diagonal-winding subgroup. This
does not identify the discrete image itself. Dependency-closed proof: a
singleton kernel packet gives a conjugate of each single-coordinate kernel
element inside the actual image. Every normal subgroup containing that image
therefore contains all coordinate kernels and their product. The primitive
actual diagonal element then fills the diagonal-winding subgroup. Conversely
that subgroup is normal (winding targets are abelian) and contains the image.
The universal normal-containment statement proves both inclusions exactly.
This is a consequence of the current packet mechanism, not a new scientific
novelty claim. It should be formalized after the primitive generator closes.
Corpus query `Xi marked monodromy normal closure diagonal winding subgroup`
returned partial=false, inventory68266; all20 candidate and20 source statements
inspected. Exact relevant hits were our new winding-map declarations; generic
normal-closure primitives are present in mathlib and will be checked in Lean.

Actual meridian scratch and targeted build PASS. The full finite-image
equality `finite_image_jointMap_eq_diagonal` now passes scratch Lean with
no analytic premise: for every finite real slope set A and every homomorphism
to any finite group, the image of actual joint monodromy equals the image of
the diagonal-winding subgroup. Promoted and wired; its target build and the
discrete normal-closure consequence are checking. Final source/all-public
axiom audits still pending, so this is not yet marked Stage3.

The discrete normal-closure equality also passes scratch. Five leaves now
promoted and wired: H:PuncturedWindingBaseChange (6 public),
R:WindingNumberDegreeBridge (1), R:XiMarkedMeridian (2),
R:XiMarkedFiniteMonodromy (3), R:XiMarkedNormalClosure (3). The final owned
Lean chain builds only XiMarkedNormalClosure, then runs actual-source
`lake env lean` on all five leaves and all15 public axiom closures via
`/tmp/rh-marked-finite-final.sh`. Evidence will be in
`/tmp/rh-XiMarkedNormalClosure-build.log`, `/tmp/rh-final-<leaf>.log`, and
`/tmp/rh-marked-finite-axioms.log`. A separate non-Lean index/lint chain writes
`/tmp/rh-marked-finite-index.log` and `/tmp/rh-marked-finite-lint.log`.
No full build, admission, heartbeat change, or RH conclusion.
The label C2-finite belongs to this card; the parent's abstract cubic C2 is
a different claim and is not closed by this result.

FINAL finite-image cycle PASS: all five targeted builds, all five final
actual-source checks and all15 public standard-axiom closures. Imports
unique; no admissions/heartbeat changes; matching proof scratches removed.
Closed child `../../../3-formalized/xi-marked-finite-monodromy.md` records exact
quantifiers and evidence. Index refreshed; global lint has seven unrelated
unreachable modules, listed on the child. This supersedes pending audit
notes above. Discrete image equality, the parent's abstract cubic C2, RH,
and scientific novelty certification remain open.
