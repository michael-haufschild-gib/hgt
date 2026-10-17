# Hyperbolic multiplier lifting of odd states

- **ID:** BSU-HML
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean), continuing research program
- **Scope:** Independent BiScale Uncertainty; no RH claims.
- **Objective:** Transfer multi-node information through Pillars VI and IX to odd secant/plastic functionals. The supplied research brief requires 100 significant contributions; supporting lemmas are not separate contributions.

## Plan

1. Audit actual multiplier, secant, clique and crossover definitions and prior corpus results.
2. Prove a transfer with every Gram defect and signed companion term retained.
3. Formalize in BiScaleUncertainty; targeted build, direct-source and axiom audits, umbrella wiring, lint.
4. Record crisp facts and failed conjectures in a dedicated ledger; continue to stronger transfers.
5. Prove the hyperbolic squared-jump identity and use source-derived support envelopes to
   remove the cosine companion in the actual secant increment. Retain measured Gram leakage.
6. Bound the full original secant energy by integrating the uncompensated Gram bound over
   disjoint collars; audit support dependence before pursuing the distinct plastic receiver.
7. Derive an exact positive-remainder decomposition of the actual plastic crossover,
   retain its signed hyperbolic moment, and transfer the verified multi-node bound into it.
8. Audit inherited multiplier zeros on actual smooth odd sources: construct a six-packet
   family, prove exact zero-lag/source energy and positive multiplier leakage laws, and
   extract the quantitative survivor before rejecting that inference.
9. Use the exact leakage boundary to seek source-centered weighted control, keeping
   the full prime-grid problem and negative odd moment explicit.
10. Replace multiplier Gram leakage by an exact centered source cross-correlation
    and a source Gram bound on node differences; integrate its penalty into the
    actual plastic receiver, with no inherited zeros or unknown moment estimate.
11. Project the difference packet off the original source. Prove its Schur residual
    energy, sharpen the actual leakage receiver, and compare the resulting envelope
    with every scalar centering choice. Audit zero-energy cases explicitly.
12. Coalesce arithmetic pair differences into actual lag packets. Establish the
    exact collision energy, doubled source-zero range, and defect-aware full receiver.
13. Prove a dyadic collision bound uniform in chain length, derive the even
    multiplier frame radius from source variance, and transfer the error-aware
    bound into the full odd functional.
14. Use long actual multiplier translation packets to control their integral,
    eliminate the independent negative odd moment, and derive a radius-free
    moment penalty on the full source logarithmic grid. Retain finite source
    errors in an unconditional plastic receiver.
15. Replace the collar support envelope by an actual fourth hyperbolic moment
    and a signed variational jump bound; transfer this into a source-data Gram
    receiver and the original secant/plastic functionals.
16. Eliminate the free fourth-moment controls along a canonical hyperbolic ray.
    Prove its attained optimum, signed-source activation criterion, continuity,
    and full secant/plastic receiver, including zero-energy sources.
17. Replace the logarithmic-grid hypothesis in the support-radius-free moment
    penalty by explicit original-source lattice correlation budgets. Derive a
    uniform multiplier frame for arbitrary signed weights and the unconditional
    full optimized plastic receiver; recover the old source-zero constant exactly.
18. Retain signed cancellation in the coherent moment direction. Prove the exact
    eventual affine correction law, remove its finite boundary intercept from the
    moment limit, quantify the improvement over absolute lattice budgets, and
    transfer the sharper unconditional penalty to the full plastic receiver.

`update_plan` and `multi_tool_use.parallel` are unavailable in this session. This card carries the plan; independent reads use `Promise.allSettled`.

## Verified starting facts

- Pillar VI transfers a zero of `h_f` to equality `h_C=h_S`, not to a zero of either multiplier autocorrelation.
- Actual Pillar IX Lean theorem uses alpha=1/2 and denominator cosh(x/2)^2;
  exact transfer identities are recorded in the owned ledger.
- Worktree has unrelated concurrent research edits; preserve them.
- Canonical field overview is now `formal/GaloisForLFunctions/BiScaleUncertainty/README.md`.
  User made it read-only. Fully read its updated 242 lines on 2026-10-17;
  retain signed source errors in main results (Trap 9). Do not restore or edit
  the deleted old README. Keep discoveries in this card and the owned ledger.

## Completion gates

- [x] Read supplied brief and complete field README.
- [x] Run corpus search; inspect actual Pillar VI and IX theorem bodies.
- [x] Dependency-closed paper theorem with unconditional measured-defect formulation.
- [x] Exact Lean theorem verified and wired into the BiScale umbrella.
- [x] Dedicated knowledge ledger and truthful contribution accounting: twelve substantive results,
  with 198 public supporting theorem audits; supporting lemmas are not contributions.
- [x] Uncompensated transfer into the full secant energy, source-derived support factor retained.
- [x] Actual signed plastic crossover receiver, including positive remainder, odd sine moment,
  and original origin coefficient; no inferred multiplier blindness.
- [x] Smooth odd fixed-energy family with a source zero at log(2), exact positive
  multiplier leakage law, and unconditional unboundedness relative to source energy.
- [x] Centered source difference-Gram control replaces multiplier off-diagonal
  data in the full secant/plastic receiver; weighted energy minimizer is exact.
- [x] Source Schur projection dominates every scalar-centered envelope, transfers
  into the full receiver, and proves exact mean-centering optimality on source cliques.
- [x] Arithmetic source difference packets coalesce into exact weighted collision
  energy; doubled source zeros control multiplier leakage without inherited zeros.
- [x] Uniform dyadic frame, coherent-packet odd-moment control, fourth-moment jump
  transfer and attained hyperbolic-ray certificate reach the full original functional.
- [x] Intrinsic source-lattice budgets remove the source-zero hypothesis from the
  uniform multiplier frame and support-radius-free odd-moment/plastic receiver.
- [ ] Repository-wide lint clean: concurrent unrelated modules remain unwired (latest gate below).
- [ ] Complete original 100-contribution objective.

## Dependency-closed paper result: compensated Gram transfer

Let f be any real continuous compactly supported source. Set C=C_(1/2)f,
S=S_(1/2)f, R=h_f(0), R_C=h_C(0), R_S=h_S(0). For any finite node family t_i,
real collar offset y and real weights b_i, put x_i=t_i-y,
v_i=b_i/cosh(x_i/2)^2, W=sum_i v_i, and

G_S(v,t)=sum_(i,j) v_i v_j h_S(t_j-t_i).

Define the actual compensated secant collar

L=sum_i [b_i h_f(x_i)/cosh(x_i/2) + v_i (R_C-h_C(x_i))].

Then, with no zero-grid, parity, sign, or unproved analytic assumption,

L = R_C W - sum_i v_i h_S(x_i)
  >= R_C W - sqrt(R_S G_S(v,t)).

Proof: Pillar IX gives h_f(x)/cosh(x/2)=(h_C(x)-h_S(x))/cosh(x/2)^2.
Adding the displayed cosine increment cancels h_C exactly. For the bound,
P(u)=sum_i v_i S(u+t_i) has squared L2 norm G_S; the target S(u+y) has
squared norm R_S and pairing sum_i v_i h_S(t_i-y). Cauchy–Schwarz gives
the bound, including zero-radius and zero-packet cases. Compact support and
continuity prove all L2 admissions. Thus no lower bound is assumed as an input.

The measured off-diagonal defect D=G_S-R_S sum_i v_i^2 gives the equivalent
penalty sqrt(R_S (R_S sum_i v_i^2+D)). When S really is a clique, D=0 and
the result becomes R W + R_S (W-sqrt(sum_i v_i^2)); this is exactly the
multi-node clique lower bound transferred to the compensated odd secant
functional. Oddness is used only to identify S as even, already proved in
Pillar VI. No implication from source oddness or source clique zeros to D=0
is assumed; that additional assertion needs an independent proof or counterexample.

More explicitly, the ordinary clique bound survives with the unconditional
penalty sqrt(R_S max(D,0)):

L >= R W + R_S(W-sqrt(sum_i v_i^2))-sqrt(R_S max(D,0)).

Indeed, square the nonnegative quantity
R_S sqrt(sum_i v_i^2)+sqrt(R_S max(D,0)). Its square is at least
R_S(R_S sum_i v_i^2+D), since the cross term is nonnegative and D<=max(D,0).
Taking square roots and inserting the exact Gram bound proves the claim.
Negative defects improve the exact bound and incur zero penalty here.

Every term is continuous in y when b_i(y) is continuous. Hence the bound
integrates over any compact interval. This transfers a genuine collar
functional, not just isolated samples.

For any signed kernel samples k_i, take b_i=k_i cosh(x_i/2). Then v_i=k_i/cosh(x_i/2)
and the same theorem reads

sum_i [k_i h_f(x_i)+(k_i/cosh(x_i/2)) Delta_C(x_i)]
 >= R_C sum_i k_i/cosh(x_i/2)
    -sqrt(R_S G_S((k_i/cosh(x_i/2))_i,t)).

This gives an exact finite-collar receiver for the actual signed plastic kernel
`2 cosh(x/2)-levyCoshKernel c |x|`. It does not remove its companion or prove a
global plastic functional bound.

The full Gram identity is
G_C(v,t)-G_S(v,t)=sum_(i,j) v_i v_j cosh((t_j-t_i)/2) h_f(t_j-t_i).
On a source clique it reduces to R sum_i v_i^2. It does not diagonalize G_S.

Finally, writing Delta_C=R_C-h_C and Delta_S=R_S-h_S,

(R-h_f(x))/cosh(x/2)
 = R(1/cosh(x/2)-1/cosh(x/2)^2)
   +(Delta_C(x)-Delta_S(x))/cosh(x/2)^2.

This exact sign audit rules out dropping the companion term from this identity when
transferring a lower bound for Delta_S. The second result below instead uses a
weighted-jump identity and actual source support to bound the uncorrected secant energy.
The plastic kernel is the separately defined piecewise `levyCoshKernel`; it
must not be silently identified with the smooth secant weight.

## Prior-art boundary

Corpus lexical `sinhMultiplier` search found only existing Pillar VI/IX declarations;
full text found no existing transfer with multiplier Gram defects. Hybrid search
reported unmeasured semantic coverage, so absence is not a novelty certificate.
External exact-phrase search was inconclusive. The classical parent is ordinary
Hilbert-space Cauchy–Schwarz; no claim of a new general Hilbert inequality is made.
Kolountzakis–Révész, [On a problem of Turán about positive definite functions](https://arxiv.org/abs/math/0204086),
studies support-constrained positive-definite integral extrema, not this signed
multiplier transfer. The contribution sought here is an audited field-specific
bridge with the previously omitted defects retained, not a literature-priority claim.

## Verification evidence

- Final direct-source compilation, exit 0, no warnings:
  `lake --old env lean GaloisForLFunctions/BiScaleUncertainty/HyperbolicMultiplierGramTransfer.lean -o .lake/build/lib/lean/GaloisForLFunctions/BiScaleUncertainty/HyperbolicMultiplierGramTransfer.olean`
- All 13 theorem `#print axioms` checks passed in `/tmp`: only `propext`,
  `Classical.choice`, `Quot.sound`; no assumed analytic premise or computational axiom.
- Verified source SHA256: `12ec9a1f19c416d8d0601c1c1e133880318a69cb43d84e3a133034fd8b387444`.
- Umbrella import verified; `scripts/formal_tools.py index` completed and the new declarations
  appeared in `formal/LEAN_API.md`. Owned-file whitespace check passed.
- `scripts/formal_tools.py lint --check-generated` exited 1: unrelated concurrent modules
  `AsymptoticTailCoercivityAndNyquistTrap5Closure`, `MultiCosetGramPackingAndNyquistDensity`,
  and `ProducerConsumerDualityAndNymanBeurlingBridge` were unreachable from their umbrella;
  `LEAN_API.md` and `LEAN_OVERVIEW.md` drifted during concurrent work. Existing large-file
  warnings also appeared. No repository-wide clean-gate claim is made.
- No full or umbrella build, numerical experiment, commit, or push was run.

The original target is not complete. The second result removes the cosine companion
for the secant functional at a support-dependent scale; the third result transfers it
into the actual plastic receiver. Multiplier leakage and the negative odd moment remain
uncontrolled. The 100-contribution objective stays active.
The fourth verified result below formalizes the six-packet odd family: original
energy and its log(2) zero stay fixed while multiplier leakage grows without bound.
This closes the single-log-zero inference audit; stronger grid or weighted control
remains necessary for the full receiver.

## Second verified result: uncompensated jump transfer

For m(u)=sinh(alpha u), g=mf, and f in C_c(R), expansion and translation give

integral m(u)m(u+x)(f(u)-f(u+x))^2 du
 = 2[cosh(alpha x)h_g(0)-h_g(x)].

Proof: the two diagonal terms become
integral m(u)[m(u+x)+m(u-x)]f(u)^2 du
=2 cosh(alpha x) integral m(u)^2 f(u)^2 du, while the cross term is -2h_g(x).
All integrands are continuous with compact support. The identity holds for
sign-changing m; positivity is supplied by its autocorrelation expression,
not by assuming the multiplier product is pointwise nonnegative.

Choose B>0 from compactness so |u|<=B on the source support. At alpha=1/2 set
K_B(x)=sinh(B/2)sinh((B+|x|)/2)>0. Whenever (f(u)-f(u+x))^2 is nonzero,
one endpoint lies in the source support and the other has modulus at most B+|x|.
Thus m(u)m(u+x)<=K_B(x); this remains valid if the product is negative.
Multiplication by the nonnegative squared jump and integration yield

cosh(x/2)R_S-h_S(x) <= K_B(x)[R-h_f(x)].

No companion remains and there is no additive commutator loss. B is derived
from the actual compact source, not assumed as an unknown analytic input.

For arbitrary nonnegative weights q_i, x_i=t_i-y, v_i=q_i/K_B(x_i), the full
Gram Cauchy–Schwarz bound gives the uncorrected increment transfer

sum_i q_i[R-h_f(x_i)]
 >= R_S sum_i v_i cosh(x_i/2)-sqrt(R_S G_S(v,t)).

Choose q_i=b_i^2 sech(x_i/2) for an actual secant collar. On a true multiplier
clique the last term is R_S sqrt(sum_i v_i^2). With measured defect D, the
explicit weaker lower bound is
R_S[sum_i v_i cosh(x_i/2)-sqrt(sum_i v_i^2)]-sqrt(R_S max(D,0)).
This recovers positive multi-node clique information in the original functional,
at a support-dependent scale. It does not assert inherited multiplier zeros,
a support-independent constant, or the full all-grid odd sign theorem.

The continuous collar bound admits compact-interval integration. Disjoint arithmetic
collars sum through the exact tiling identity and are dominated by the global
nonnegative secant integral. These analytic steps are proved in Lean below.

### Global receiver: dependency-closed paper proof

Write F(x)=[R-h_f(x)]sech(x/2). Autocorrelation Cauchy–Schwarz gives
0<=R-h_f(x)<=2R. Since sech(x/2)<=2exp(-x/2),
0<=F(x)<=4R exp(-x/2). Thus F is continuous and integrable on (0,infinity)
for every compact continuous source; no derivatives are needed.

For d=|delta| and n>=0, take t_k=kd, k=0,...,n-1, b_k=1, and evaluate the
finite bound at -y. Its weights are
v_k(y)=sech((kd+y)/2)/K_B(kd+y).
The source radius makes every denominator strictly positive, so these weights,
their finite Gram quadratic form, and its square root are continuous. Therefore

integral_0^d [R_S sum_k v_k(y)cosh((kd+y)/2)-sqrt(R_S G_S(v(y),t))]dy
 <= integral_0^d sum_k F(kd+y)dy
 = integral_0^(nd) F(x)dx
 <= integral_0^infinity F(x)dx = J_sech(f).

The middle identity is the exact disjoint-collar tiling theorem; the last inequality
uses the established integrability and pointwise nonnegativity. d=0 and n=0 are
included. Choosing delta=log(2) yields dyadic logarithmic nodes. The theorem retains
the full measured sine Gram and does not claim that source prime-blindness
diagonalizes that Gram. It bounds the actual global secant energy, not the separate
piecewise plastic crossover functional.

### Literature boundary

The weighted-jump expansion belongs to the established ground-state representation
method; no priority claim is made for that general mechanism. Frank–Seiringer,
*Non-linear ground state representations and sharp Hardy inequalities*
(https://arxiv.org/abs/0803.0503) supplies background on nonlocal ground-state
representations. The contribution formalized here is the concrete signed-sinh
identity, source-support envelope, and uncompensated full-Gram secant transfer.
The corpus searches returned no exact lexical match; their semantic coverage was
unmeasured, so they do not establish literature novelty.

### Verification of the second result

- Final actual-source compile exited 0 without warnings:
  `lake --old env lean GaloisForLFunctions/BiScaleUncertainty/HyperbolicJumpEnergyTransfer.lean -o .lake/build/lib/lean/GaloisForLFunctions/BiScaleUncertainty/HyperbolicJumpEnergyTransfer.olean`
- All 19 public theorem axiom audits via `/tmp/hml_jump_axioms.lean` returned only
  `propext`, `Classical.choice`, `Quot.sound`; no assumed analytic input.
- Source SHA256: `56fb077bbe28fbae0d143d8a62f68db8bbcc87c5c3c941c2e0b43feea856e2b4`.
- Umbrella import added; `scripts/formal_tools.py index` exited 0.
- `scripts/formal_tools.py lint --check-generated` exited 1. Current unreachable concurrent
  modules: `CoprimeLogSobolevCoercivity`, `CoprimeSobolevInterpolation`,
  `InfiniteGridPolarRecovery`, `LogarithmicCompressionEnergy`,
  `SobolevLogarithmicTransport`, `SobolevTraceEnergy`. Existing large-file warnings
  also appeared. Neither owned multiplier-transfer module was flagged. No global
  clean-lint claim; no changes to others' unfinished modules.
- Count: 2/100 substantive bridges. The exact jump identity, its support estimate,
  finite clique-penalty bound, and integrated full secant bound form one contribution.

## Third verified result: the actual plastic receiver

Fix the existing plastic threshold c*=screwSignThreshold>0. Let k(x)=levyCoshKernel c* x
and V=levyCoshPotential c*. For a real compact continuous source f, set
E=integral f(u)cosh(u/2)du, O=integral f(u)sinh(u/2)du, R=h_f(0), and

P(f)=V R + integral_(u,v) f(u)f(v)[2cosh((u-v)/2)-k(|u-v|)]du dv.

This is the original signed plastic crossover (excluding any separately added
gamma-origin constant). No sign assumption on f is made. Existing compact-support
admission supplies BddSupp directly, so all pair integrals below are integrable.
The exact kernel jump identity and hyperbolic product factorization give

P(f)=2 integral_(x>0) k(x)[R-h_f(x)]dx + 2(E^2-O^2).

Pillar IX and 2 archLevyDensity(x)=archLevySinhWeight(x) yield, for x>0,

2k(x)-sech(x/2) =
  4cosh(x/2)-sech(x/2), if x<=c*;
  archDualLevySinhWeight(x), if x>c*.

Both pieces are positive. The core is bounded; the tail starts at c*>0 and
decays exponentially. More directly, the remainder integrand is a difference
of two integrable functions, since k is integrable and 0<=R-h_f<=2R.
Thus, with R_pl(f)=integral_(x>0)[R-h_f(x)][2k(x)-sech(x/2)]dx>=0,

P(f)=J_sech(f)+R_pl(f)+2(E^2-O^2).

Combining this exact decomposition with the previous verified disjoint-collar
Gram bound L(f;delta,n)<=J_sech(f) gives the actual crossover lower bound

L(f;delta,n)+2(E^2-O^2) <= P(f).

The stronger bound retains the entire positive remainder:
L(f;delta,n)+R_pl(f)+2(E^2-O^2) <= P(f).

For an unconditional odd-source specialization, construct F(u)=[f(u)-f(-u)]/2
from arbitrary f in C_c. F is compact continuous and odd, its cosine moment is
zero by change of variables u -> -u, and S_(1/2)F is even by Pillar VI. Hence

L(F;delta,n)-2[integral F(u)sinh(u/2)du]^2 <= P(F).

For any origin coefficient a, the full original expression is also retained:
a R + 2(E^2-O^2) + L(f;delta,n)
 <= (a+V) integral f^2 + integral_(u,v) f(u)f(v)[2cosh((u-v)/2)-k(|u-v|)]du dv.
This includes the existing gamma-origin constant as a direct specialization.

The negative odd moment remains explicitly on the right side of the underlying
positivity test. No prime-blind source condition has been converted into a multiplier
clique or used to erase that moment. This advances the actual plastic functional,
but does not prove its unconditional nonnegativity or an odd all-grid sign theorem.
The jump identity and moment factorization were already in the corpus; the verified
contribution is their exact secant/positive-remainder assembly and multiplier-Gram
receiver for signed and canonically odd sources, not a new claim about those ingredients.

### Verification of the third result

- Corpus search `research 'plastic crossover hyperbolic multiplier jump kernel'`
  found the existing jump/pair identity and crossover bounds; semantic coverage was
  unmeasured. Focused lexical search `research 'levyCoshKernel archSechHalfWeight'
  --mode lexical --exclude-module PlasticCrossoverGramReceiver --per-module 0 --explore 0`
  returned no matching declaration. This is not a literature-novelty certificate.
- Actual-source final compile exited 0 with no warnings:
  `lake --old env lean GaloisForLFunctions/BiScaleUncertainty/PlasticCrossoverGramReceiver.lean -o .lake/build/lib/lean/GaloisForLFunctions/BiScaleUncertainty/PlasticCrossoverGramReceiver.olean`
- All 18 public theorem `#print axioms` audits in `/tmp/hml_plastic_axioms.lean`
  returned only `propext`, `Classical.choice`, `Quot.sound`.
- Source SHA256: `c34e886a83d099242571f9bdcb2b4e49fd3841608fad2448b9615e2ee49cd923`.
- Umbrella import added; `scripts/formal_tools.py index` exited 0.
- Count: 3/100. Exact positive remainder, signed receiver, odd-source construction,
  and origin-coefficient form are one contribution, not separate items.
- Latest `scripts/formal_tools.py lint --check-generated` exited 1. Unreachable concurrent
  modules: `RHTower.NonTemperedShiftedZetaPairCountermodel`, `RHTower.WeilConeMismatchWitnesses`,
  `RHTower.ZeroCountRemainderNotIntegrable`, `BiScaleUncertainty.LogarithmicPathKernel`,
  `BiScaleUncertainty.PairedCosetSphereDuality`, `BiScaleUncertainty.SignedCosetProductCoupling`.
  `formal/LEAN_API.md` and `formal/LEAN_OVERVIEW.md` also drifted during concurrent work.
  Existing large-file warnings remain. No owned transfer/receiver module was flagged.
- Owned documentation whitespace check passed; final source hash and generated API entries
  rechecked. Scratch API/axiom files and captured lint output removed after recording results.

## Fourth verified result: exact odd leakage family

Use the existing smooth even packet phi from
`formal/GaloisForLFunctions/RHTower/EvenSectorSmoothBlindInterpolationObstruction.lean`.
Its squared mass m>0; its support diameter is strictly below d/10, d=log(2)>0.
The earlier memory only named its basename; it is in RHTower, not BiScaleUncertainty.
All new code remains in BiScaleUncertainty and reuses this packet without modifying it.

For arbitrary real T put t=|T| and a_j=t+j d, j=1,2,3. Define
f_T(u)=-phi(u-a_1)+phi(u-a_2)+phi(u-a_3)
       +phi(u+a_1)-phi(u+a_2)-phi(u+a_3).
This is smooth, compact and odd. All six supports are disjoint. At lag d only
four ordered overlaps survive: a_1->a_2, a_2->a_3, -a_2->-a_1, -a_3->-a_2.
Their coefficient products are -1,+1,-1,+1. Thus h_fT(0)=6m and h_fT(d)=0.

Set M=integral cosh(u)phi(u)^2 du>=m>0. Evenness of phi gives
integral sinh(u)phi(u)^2 du=0. The exact weighted diagonal overlap is

integral sinh((u+a)/2)sinh((u+b)/2)phi(u)^2 du
 = [cosh((a+b)/2)M-cosh((a-b)/2)m]/2.

Therefore the same four surviving overlaps give
h_(S_(1/2)fT)(d)=[cosh(t+5d/2)-cosh(t+3d/2)]M
 =2 sinh(t+2d)sinh(d/2)M>0.

This is a counterexample to inheritance at the actual logarithmic node log(2),
not a source satisfying the entire infinite prime grid. The negative statement
does not retire hyperbolic lifting; it rejects only a diagonal substitution.

Positive survivor: exact quantitative law, fixed source energy 6m, and a single
positive packet invariant M that determines all leakage in this family. Since
sinh(t+2d)>=t+2d, the leakage is unbounded while h_fT(0) and h_fT(d) remain fixed.
Thus no bound depending only on original origin energy can control multiplier
leakage even within smooth odd sources with this fixed source zero. A valid
receiver must retain actual multiplier Gram data or additional position/moment data.
All overlap, smoothness, support, mass, and unboundedness steps are formalized;
no numerical computation or unverified zero-grid inheritance is admitted.

### Verification of the fourth result

- Actual-source final compile exited 0 with no warnings:
  `lake --old env lean GaloisForLFunctions/BiScaleUncertainty/OddMultiplierLeakageFamily.lean -o .lake/build/lib/lean/GaloisForLFunctions/BiScaleUncertainty/OddMultiplierLeakageFamily.olean`.
- All 12 public theorem axiom audits in `/tmp/hml_leak_axioms.lean` passed with only
  `propext`, `Classical.choice`, `Quot.sound`; the scratch file imports the emitted module.
- Final source SHA256: `fd8f41743e0b8a24bb2a4ebd43594b172a93ffef3c3066c9a631afedaa500ef0`.
- Main theorems: `OddMultiplierLeakage.source_sinh_autocorr_lag` and
  `OddMultiplierLeakage.exists_odd_logZero_large_sinhCorrelation`.
- The packet's existing smoothness, evenness, support and positive mass are reused.
  The actual-source family, fixed energy, exact logarithmic source zero and quantitative
  unbounded multiplier leakage constitute one result: count 4/100. No external-priority claim.
- Narrow failed inference and its fully formalized positive survivor are recorded in
  `docs/drafts/pipeline/5-failed/odd-single-log-zero-multiplier-inheritance-2026-10-17.md`.
  Hyperbolic lifting and the full infinite-grid problem remain active.
- Umbrella import and both README entries added; `scripts/formal_tools.py index`
  exited 0. Generated API contains all 12 public theorem entries.
- Latest `scripts/formal_tools.py lint --check-generated` exited 1: concurrent
  `BiScaleUncertainty.CompactSourceGraphAdmission`, `CompactSourceResistanceMass`,
  `FiniteCopyTailRigidity`, and `FiniteTranslationTrains` were unreachable from their
  umbrella; `formal/LEAN_API.md` drifted after index refresh. Existing large-file
  warnings remain. No owned multiplier-transfer, receiver or leakage module was flagged.
- Owned documentation whitespace check passed. Scratch API/axiom files and captured
  lint output removed after recording results; no owned Lean process remains.

## Fifth verified result: centered source-Gram control

Let F=(f(u)-f(-u))/2 for arbitrary f in C_c(R), and let alpha,lambda be arbitrary
real parameters. Put S=sinh(alpha u)F, q_lambda=(cosh(2alpha u)-lambda)F,
R=h_F(0), M=integral cosh(2alpha u)F(u)^2 du and
W=integral cosh(2alpha u)^2 F(u)^2 du. These are actual compact continuous
sources and finite integrals; no source or multiplier zero is assumed.

Odd reflection u -> -u-x shows
integral cosh(2alpha u)F(u)F(u+x)du
 =integral cosh(2alpha(u+x))F(u)F(u+x)du.
Average these integrals, use hyperbolic addition and Pillar VI, obtaining

integral q_lambda(u)F(u+x)du
 =2cosh(alpha x)h_S(x)+(cosh(alpha x)^2-lambda)h_F(x).

For finite nodes t_i and real weights v_i let P={(i,j): i,j in s, i!=j},
d_ij=t_j-t_i and a_ij=v_i v_j/[2cosh(alpha d_ij)]. Then the actual sine clique
defect D=G_S-R_S sum_i v_i^2 has the exact decomposition

D=E_lambda+integral q_lambda(u)[sum_P a_ij F(u+d_ij)]du,
E_lambda=sum_P a_ij[lambda-cosh(alpha d_ij)^2]h_F(d_ij).

The square integral of the packet is precisely
G=translationGramEnergy F P a d. Thus, by the existing integral Cauchy--Schwarz
theorem (reused, not claimed new),

|D-E_lambda| <= sqrt(Q_lambda G), Q_lambda=h_(q_lambda)(0),
D <= U_lambda := E_lambda+sqrt(Q_lambda G).

This is a source-only bound on every off-diagonal multiplier Gram contribution.
The source Gram is evaluated on differences of the original nodes; its cross
entries are retained. On an actual source clique E_lambda=0, but the new
difference-node Gram need not be diagonal. No such diagonal substitution is made.
The exact centering cost is Q_lambda=W-2lambda M+lambda^2 R, hence
R Q_lambda=(R lambda-M)^2+(R W-M^2), with R W-M^2>=0. This identifies the
weighted variance exposed by the preceding unbounded-leakage family. For R>0
the energy minimum occurs at lambda=M/R; the formal main bound needs no
nonzero-energy premise and admits every lambda.

At alpha=1/2 substitute U_lambda for D in the previously verified uncompensated
clique penalty. For the source-derived weights v_i, the new lower bound is

R_S[sum_i v_i cosh((t_i-y)/2)-sqrt(sum_i v_i^2)]
 -sqrt(R_S max(U_lambda,0)).

It is below the existing full multiplier-Gram bound, since D<=U_lambda and
sqrt(R_S G_S)<=R_S sqrt(sum v_i^2)+sqrt(R_S max(D,0)). All coefficients are
continuous in collar offset y; source correlations in the difference-node Gram
are fixed. Integrate over the existing disjoint arithmetic collars, then apply
P(F)=J_sech(F)+R_plastic(F)-2O(F)^2. The resulting lower bound retains the
positive plastic remainder and negative odd moment, but uses only source Gram
data and the actual centered weighted source energy to control leakage.

Scope: removes the unknown multiplier off-diagonal Gram from the receiver, not
the support factor in the jump envelope, weighted-moment growth, or the negative
odd moment. Source zeros remain explicit data. Corpus searches found existing
packet-Gram, Cauchy--Schwarz and receiver tools; the broad hybrid search had no
exact lexical hit, and the focused search was partial with unmeasured semantic
coverage. No external novelty claim or numerical experiment is involved.

### Verification of the fifth result

- Actual-source final compile exited 0 with no warnings:
  `lake --old env lean GaloisForLFunctions/BiScaleUncertainty/CenteredHyperbolicGramControl.lean -o .lake/build/lib/lean/GaloisForLFunctions/BiScaleUncertainty/CenteredHyperbolicGramControl.olean`.
- Scratch API checks and all 15 public theorem axiom audits in
  `/tmp/hml_center_api.lean` passed; only `propext`, `Classical.choice`, `Quot.sound`.
- Final source SHA256: `943a494e19a78335bbc2bb288adf016474e44c5ea747a3937528aa39a529f85e`.
  The previous four source hashes also match their recorded verified versions.
- Main theorems: `CenteredHyperbolicGram.odd_defect_abs_sub_correction_le`,
  `centered_energy_minimizer`, `odd_secantEnergy_ge_centered`, and
  `odd_plasticCrossover_ge_centered`. Final receiver retains the full positive
  plastic remainder and precise negative odd moment.
- Source hypotheses, Bessel/Cauchy--Schwarz, and generic moment minimization are not
  separate contributions. The exact odd mixed-correlation representation, source
  difference-Gram control, centering law and actual functional receiver count once:
  5/100, with 77 public supporting theorem audits across the five modules.
- Concurrent `HyperbolicMultiplierIncrementAndOddSignCoercivity.lean` appeared during
  this work. Its actual source was read: it supplies joint cosine/sine increment and
  signed-collar bounds retaining multiplier samples. It does not contain this centered
  mixed-correlation identity or source-only off-diagonal replacement. Its results are
  not included in our count, and its documentation does not establish closure of the
  remaining full odd positivity problem. No concurrent file was changed by this audit.
- Boundary: the energy-minimizing center need not minimize the entire envelope away
  from a source clique, because E_lambda also depends on lambda. The pair-difference
  Gram remains full. Support dependence, weighted variance growth, full-grid coercivity,
  and negative odd-moment domination remain open.
- Umbrella import and both README entries added. `scripts/formal_tools.py index`
  exited 0; generated API includes the new receiver and minimizer declarations.
- Latest `scripts/formal_tools.py lint --check-generated` exited 1 on eight concurrent
  modules unreachable from the BiScale umbrella: `CappedBlockSupport`,
  `CappedCosetSphereDuality`, `CompactSourceGraphCoercivity`, `CompactSourcePairVariance`,
  `FullGridCappedCollarEnergy`, `HyperbolicMultiplierIncrementAndOddSignCoercivity`,
  `KreinKantorovichMeasureTransportAndPrimePolarPairing`, and
  `SignedKreinCollarAndPrimeDeficitTransfer`. No owned lifting module was flagged;
  no generated-file drift was reported in this snapshot. Existing large-file warnings remain.
- New source, owned ledger and card have no trailing whitespace. Broad shared-file
  `git diff --check` reports an unrelated new blank line at EOF in the concurrently
  expanded formal README; its content was preserved. Scratch API/axiom file and
  captured lint output removed after recording the audit; no owned Lean process remains.

## Sixth verified result: source-orthogonal leakage envelope

For the actual difference packet P=sum a_p F(.+d_p), set R=h_F(0),
K=<F,P>=sum a_p h_F(d_p), G=||P||^2, mu=M/R and Q=||q_mu||^2.
The centered weighted source q_mu is orthogonal to F, including R=0 because
the existing variance inequality forces M=0 there. Likewise K=0 when R=0.
Thus P_perp=P-(K/R)F satisfies
||P_perp||^2=G-K^2/R=:H>=0 and <q_mu,P_perp>=<q_mu,P>.
Consequently the actual odd multiplier defect obeys

|D-E_mu| <= sqrt(Q H), U_perp=E_mu+sqrt(Q H).

This replaces the full packet Gram by its source-orthogonal residual. It is
not inferred pair-difference orthogonality: every source Gram entry remains.
For arbitrary c, put z=c-mu. The exact centering laws give
E_c=E_mu+zK, Q_c=Q+Rz^2, G=H+K^2/R (R>0).
The elementary two-dimensional identity
(a^2+x^2)(b^2+k^2)-(ab-xk)^2=(ak+xb)^2
with a=sqrt Q, b=sqrt H, x=z sqrt R, k=K/sqrt R proves
U_perp<=E_c+sqrt(Q_c G). When R=0, M=K=0 gives equality.
Hence the projected envelope improves every previously available scalar center,
including signed source correlations. Substituting it in the uncompensated
collar penalty yields a stronger full secant/plastic lower bound.

On a source clique, each h_F(d_p)=0, so K=0 and every E_c=0. Therefore the
projected envelope equals the previous envelope at mu, and mu already minimizes
the whole scalar-centered envelope. This is an exact boundary: projection onto
F cannot supply a further clique gain. Away from a source clique the Schur
subtraction removes a real packet cost and the envelope dominates every center.
No strict improvement for every source, or full-grid coercivity, is claimed.

Paper proof and exact formalization are dependency-closed. Corpus search
`research "centered hyperbolic Schur projection difference packet" --module
BiScaleUncertainty --any --per-module 2 --explore 0` returned 204 declarations
in 26 modules. Hybrid search was partial (71.12s), with unfinished text/source
retrieval and unmeasured semantic coverage. Inspected actual existing abstract
Schur--Krein and translation-packet proofs. Their classical projection and
Cauchy--Schwarz mechanisms are reused, not counted as separate contributions;
the contribution is the exact multiplier-envelope comparison, source-clique
boundary and improved actual receiver. No external novelty claim.
Support envelope, remaining residual Gram, and negative odd moment remain.

### Verification of the sixth result

- Actual-source final compile exited 0 without warnings:
  `lake --old env lean GaloisForLFunctions/BiScaleUncertainty/ProjectedHyperbolicGramControl.lean -o .lake/build/lib/lean/GaloisForLFunctions/BiScaleUncertainty/ProjectedHyperbolicGramControl.olean`.
- All 16 public theorem axiom audits and mathlib API checks in
  `/tmp/hml_project_api.lean` passed; only `propext`, `Classical.choice`, `Quot.sound`.
- Verified source SHA256:
  `27a0251e688b257952cca194ea612814c5c73f5b9e1e3a01349932f9411b0384`.
  The imported fifth module still matches its recorded source hash.
- Main results: `ProjectedHyperbolicGram.projectedDefectUpper_le_every_center`,
  `sourceClique_centering_boundary`, `odd_secantEnergy_ge_projected`, and
  `odd_plasticCrossover_ge_projected`. Main receiver has no analytic hypotheses;
  the local clique boundary explicitly states the ordinary source-zero condition.
- Finite-sum coercion and squared-source support proofs were made explicit after
  initial elaboration errors. No heartbeat limit was raised and no statement weakened.
- Umbrella import and both README entries added. Index refresh exited 0 and the
  generated API contains every new public theorem. This is contribution 6/100,
  with 93 public supporting theorem axiom audits across the six modules.
- Latest `scripts/formal_tools.py lint --check-generated` exited 1 after a second
  successful index refresh. Four concurrent unrelated modules were unreachable:
  BiScale `CappedSupportComparison`, `RoughModulusGraphDecomposition`,
  `RoughSobolevModulus`, and RHTower `FermiNymanDyadicFoldGeometry`. Generated
  `LEAN_API.md`, `LEAN_GAPS.md`, and `LEAN_OVERVIEW.md` drifted again as concurrent
  modules changed. Existing large-file warnings remain. No owned lifting module
  was flagged; no unrelated source was changed to clear the global gate.
- Source, ledger, master card and umbrella whitespace checks passed. A broad
  shared README check reports an unrelated trailing blank line in the report copy;
  concurrent content was preserved. API/axiom scratch and captured lint output
  were removed. No owned Lean, index or lint process remains.
- The exact source-clique boundary and strongest positive survivor are recorded in
  `docs/drafts/pipeline/5-failed/source-line-projection-extra-clique-gain-2026-10-17.md`.
  Mean centering is now exhausted for extra exact-clique gain; the remaining
  difference-node Gram and weighted variance need substantive new control.
  Full original goal remains active at 6/100.

## Seventh verified result: arithmetic lag collision energy

Take nodes t_i=i delta, 0<=i<=N, and real weights v_i. For each slot r=0,...,2N,
let d_r=(r-N)delta and

b_r = sum_(i,j distinct, N+j-i=r) v_i v_j / [2cosh(alpha d_r)].

The original difference packet is exactly sum_r b_r F(.+d_r), and b_N=0.
Its Gram energy is therefore

G=R A+Z, A=sum_r b_r^2,
Z=sum_(r!=s) b_r b_s h_F((s-r)delta).

Equal integer index differences must be combined before squaring: replacing A by the sum
of squares of individual pair coefficients discards their cross terms.
At a positive lag k, b_(N+k) equals
[sum_(i=0)^(N-k) v_i v_(i+k)]/[2cosh(alpha k delta)].
No source assumption is needed for these identities. With source zeros at
m delta for 1<=m<=2N, the existing arithmetic-clique theorem gives Z=0.
The theorem uses the doubled range; it does not infer those zeros from the
original clique range through N delta. For the odd source, E_mu=0 and K=<F,P>=0 under the larger
zero range, hence |D|<=sqrt(V A), V=RW-M^2. This identifies an explicit
weighted additive-collision cost for multiplier leakage.

For arbitrary actual compact sources retain E_mu, K and Z. Substitute the
exact expression R A+Z-K^2/R into the source Schur receiver and integrate over
the existing disjoint collars. The resulting full secant/plastic theorem must
remain unconditional; zero-range statements are local specializations, not
assumed analytic inputs to the final construction. At delta=0, different integer
slots can represent the same real displacement; the full cross-lag error retains
those additional coincidences. If N>0, the doubled-range assumption then forces
zero source energy. No nonzero-step or positive-energy assumption is added to the
unconditional receiver. Support and negative odd moment remain.

Corpus search `research "difference packet repeated lag arithmetic Gram hyperbolic"
--module BiScaleUncertainty --any --per-module 2 --explore 0` found 348 declarations
in 38 modules; hybrid partial58.45s, text/source retrieval unfinished, semantic
coverage unmeasured. Read actual finite-train lag grouping, arithmetic clique,
and packet Gram proofs. Their grouping/orthogonality mechanisms are reused;
the multiplier collision law and actual receiver form this single contribution.

Possible next question, not an established result: use the aperiodic weight
correlations and hyperbolic denominator to bound A uniformly by a multiple of
(sum v_i^2)^2 on dyadic chains, producing a multiplier frame bound from actual
source variance. This requires a separate proof and corpus audit.

### Verification of the seventh result

- Final direct actual-source compilation exited 0 without warnings:
  `lake --old env lean GaloisForLFunctions/BiScaleUncertainty/ArithmeticMultiplierCollisionControl.lean -o .lake/build/lib/lean/GaloisForLFunctions/BiScaleUncertainty/ArithmeticMultiplierCollisionControl.olean`.
- All 24 public theorem axiom audits and mathlib API checks passed in
  `/tmp/hml_collision_api.lean`; only `propext`, `Classical.choice`, `Quot.sound`.
- Source SHA256:
  `ea5f7325683aa67f27d59ecaf8319b851f675324abc2a95cab2c3c87f46abaf8`.
  Imported projected module still matches its prior verified source hash.
- Main theorems: `ArithmeticMultiplierCollisions.differenceGram_eq_collision_add_error`,
  `odd_defect_abs_le_variance_collision`, `odd_logGrid_defect_abs_le_variance_collision`,
  `collisionDefectUpper_of_double_zeros`, and `odd_plasticCrossover_ge_collision`.
  The full receiver is unconditional on actual compact input; grid specializations
  explicitly state their source-domain conditions. No multiplier-zero hypothesis is added.
- One finite-bijection proof and two integral rewrites needed explicit elaboration.
  Final source has 377 lines, no warnings, no heartbeat changes or weakened statements.
- Umbrella import and both README entries added. Index refresh exited 0; generated
  API contains all new declarations. Contribution count 7/100, supporting theorem
  axiom audits 117 in total. Full original goal remains active.
- `scripts/formal_tools.py lint --check-generated` exited 1 on nine concurrent
  unrelated modules unreachable from their umbrella: RHTower
  `FermiNymanDyadicFoldGeometry`; BiScale `AnnularCorrelationTransport`,
  `CappedCollarArrayComparison`, `CappedCollarCutoffComparison`,
  `CappedSupportComparison`, `EulerMaclaurinLevyQuadratureAndSFreeCellBounds`,
  `FullGridCappedCollarHierarchy`, `MultiShellOriginBudgetAndGlobalPrimeCollarSynthesis`,
  and `SignedWeilFunctionalCoercivityAndRHBridge`. No owned lifting module was flagged;
  no generated drift was reported in this snapshot. Existing large-file warnings remain.
- Source/docs/umbrella whitespace checks passed. Owned API/axiom scratch and lint
  capture were removed after recording results. All owned Lean, index and lint
  handles completed; no full build, numerical experiment, commit or push was run.

## Eighth result: uniform dyadic multiplier frame bound

Let d=log2, alpha=1/2, W2=sum_(i=0)^N v_i^2. For positive lag k, finite
Cauchy--Schwarz gives |sum_i v_i v_(i+k)|<=W2. Reflection equates positive
and negative lag amplitudes, while the central amplitude is zero. Since
[2cosh(k d/2)]^2>=exp(k d)=2^k, the exact collision formula gives

A=2 sum_(k=1)^N b_(N+k)^2 <=2 W2^2 sum_(k=1)^N 2^(-k)<=2 W2^2.

Thus doubled source zeros imply |D|<=sqrt(2V) W2 and
G_S<= [R_S+sqrt(2V)] W2, uniformly in N and signed weights. This is an actual
multiplier frame bound supplied by original source variance, not inherited zeros.

For arbitrary actual odd F retain the previous E_mu and cross-lag error Z.
Writing Q=||q_mu||^2 and Q R=V, the exact centered source bound gives
D<=E_mu+sqrt(2V)W2+sqrt(Q max(Z,0)). Hence
G_S<=[R_S+sqrt(2V)]W2+E_mu+sqrt(Q max(Z,0))=:U.
The original jump collar is bounded below by
R_S sum_i v_i cosh((i d-y)/2)-sqrt(R_S max(U,0)).
Continuity and existing disjoint-collar tiling transfer this bound into
full J_sech and P(F), with the positive remainder and negative odd moment retained.
No source-zero or unknown analytic input is assumed by that final receiver.

For completeness, Q(RA+Z)=VA+QZ<=2V W2^2+Q max(Z,0). Both terms on the
right are nonnegative. Squaring sqrt(2V)W2+sqrt(Q max(Z,0)) adds a nonnegative
cross term and proves the claimed root estimate. The signed E_mu is retained;
max(U,0) preserves a real continuous receiver for every compact input. Actual
odd sources satisfy G_S<=U, so this envelope bounds their actual Gram energy.
All coefficient functions are finite sums of continuous transfer weights;
sqrt and max preserve continuity. Integrating the pointwise comparison against
the existing full-Gram collar theorem proves the unconditional secant receiver.
The exact plastic decomposition then gives the displayed plastic receiver.
On doubled source zeros, both E_mu and Z vanish and the frame receiver reduces
exactly to penalty sqrt(R_S (R_S+sqrt(2V)) W2). Zero-energy sources and N=0
need no exceptional definition. This uniform bound can be weaker than exact
collision/Schur control; no pointwise domination of that earlier receiver is claimed.

Corpus search `research "hyperbolic collision frame bound geometric aperiodic correlation"
--module BiScaleUncertainty --any --per-module 2 --explore 0`: 460 declarations,
71 modules, hybrid partial67.40s; text/source retrieval unfinished and semantic
coverage unmeasured. Existing profile-stable dyadic bounds retain an actual
within-chain operator error; they do not prove this source-variance frame radius.
Finite Cauchy--Schwarz and geometric summation are supporting mechanisms.
Final actual-source compilation and all 19 public theorem axiom audits passed without warnings.
No literature-priority or optimal-constant claim.

### Verification of the eighth result

- Final direct actual-source compilation exited 0 without warnings:
  `lake --old env lean GaloisForLFunctions/BiScaleUncertainty/DyadicMultiplierFrameBound.lean -o .lake/build/lib/lean/GaloisForLFunctions/BiScaleUncertainty/DyadicMultiplierFrameBound.olean`.
- Source SHA256:
  `f40cd139089ff168e6522ece36565284fe7e62530df457e3b58256d0d9c5adec`.
  All seven earlier owned module hashes still match their verified sources.
- Main results: `DyadicMultiplierFrame.dyadic_collisionEnergy_le`,
  `odd_sinhGram_le_frame_of_double_zeros`, `odd_logGrid_defect_abs_le_frame`,
  `odd_sinhGram_le_frameGramUpper`, `frameJumpBound_of_double_zeros`, and
  `odd_plasticCrossover_ge_frame`. The full receiver assumes only actual compact
  input and chain length; grid statements are explicit local specializations.
- Final source has 379 lines. One range-sum rewrite and one simplifier-order issue
  required explicit rewrites; no theorem was weakened and no heartbeat limit changed.
- Umbrella import and both README entry 11/module-map row 58 added. Index refresh
  exited 0 and all 19 public theorems appear in generated API.
- `scripts/formal_tools.py lint --check-generated` exited 1 on one unrelated
  concurrent module unreachable from its umbrella:
  `GaloisForLFunctions.BiScaleUncertainty.CappedSupportActivation`.
  No owned lifting module was flagged and no generated drift was reported in this
  snapshot. Existing large-file warnings remain. Do not claim a repository-wide pass.
- All 19 public theorem axiom audits and mathlib API checks passed via
  `lake --old env lean /tmp/hml_frame_api.lean`; only `propext`, `Classical.choice`,
  `Quot.sound`. This completes contribution 8/100, with 136 public supporting
  theorem audits across eight modules. The full original goal remains active.
- Owned API/axiom scratch and lint capture were removed; absence verified.
  All owned Lean, index and lint handles completed. Final source/docs/umbrella
  whitespace checks passed. No full build, numerical experiment, commit or push.

## Ninth result: coherent packet mass and odd-moment elimination

Let d=log2, S=sinh(u/2)F(u), O=int S, C=R_S+sqrt(2V), with F the canonical
actual odd source. For any compact source g define P_N(u)=sum_(i=0)^N g(u+id).
Its integral is (N+1)int g and its squared L2 norm is the actual translation
Gram. If B=multiplierSourceRadius(g)+1, its support lies in (-B-Nd,B].
Interval Cauchy--Schwarz gives

(N+1)^2 (int g)^2 <= (2B+Nd) G_g(1).

For g=S use the verified unconditional frame upper U_N, with its E_mu and Z
terms retained. Define M_N=(2B+Nd)max(U_N,0)/(N+1)^2. Then O^2<=M_N,
so every previous frame collar integral I_K gives the unconditional theorem
I_K+R_plastic-2M_N<=P(F). Moment chain length N and collar length K are independent.

For full source logarithmic blindness, every finite multiplier Gram is at most
C(N+1). Thus (N+1)O^2<=(2B+Nd)C. If O^2>dC, an integer N larger than
(2BC-O^2)/(O^2-dC) contradicts this inequality. Therefore O^2<=dC and
I_K+R_plastic-2dC<=P(F). This removes the separate linear hyperbolic moment
and its support radius from the penalty; the collar still has its source-support
factor and C still contains actual weighted variance. No universal positivity,
multiplier zeros or numerical experiment is claimed. Standard compact-support
mass/energy duality and interval Cauchy--Schwarz are supporting mechanisms.

Initial corpus query "odd hyperbolic moment variance multiplier frame" with
--module BiScaleUncertainty --any --per-module 2 --explore 0: 393 declarations
in 38 modules, hybrid partial57.36s, text/source retrieval unfinished and semantic
coverage unmeasured; compiled snapshot coverage was partial. Existing results
retain the independent odd moment. Second query "translate packet mass support
frame integral" with the same filters: 442 declarations in 84 modules,
hybrid partial58.06s; text/source retrieval unfinished, semantic coverage
unmeasured. Read actual finite-translation support/Gram laws and the existing
interval Cauchy--Schwarz proof; neither states this odd-moment/frame bound.
Paper derivation, final actual-source compilation and all 12 public axiom audits complete.

### Verification of the ninth result

- Final direct actual-source compilation exited 0 without warnings:
  `lake --old env lean GaloisForLFunctions/BiScaleUncertainty/DyadicHyperbolicMomentControl.lean -o .lake/build/lib/lean/GaloisForLFunctions/BiScaleUncertainty/DyadicHyperbolicMomentControl.olean`.
- Source SHA256:
  `a963bbb08e6d77c842f11009fef217ca83f783faf79a5f911bc1128f8dc8eef5`.
  Imported dyadic frame source still matches its verified hash.
- Main results: `DyadicHyperbolicMoment.integral_sq_le_chain_gram`,
  `odd_moment_sq_le_budget`, `odd_plasticCrossover_ge_momentBudget`,
  `odd_logGrid_moment_sq_le_frame`, and `odd_logGrid_plasticCrossover_ge_frame`.
  The finite moment-budget and plastic capstones are unconditional on actual compact
  input, with independent chain lengths N and K. The logarithmic-grid specialization
  states its source-domain condition explicitly and adds no analytic premise.
- All proofs compiled on the first source check, which reported one unused-variable
  warning. Making the continuity proof's shift explicit removed it. Final source has
  187 lines; no weakened theorem, heartbeat change, full build or numerical experiment.
- Umbrella import and both README entry 12/module-map row 62 added. Both index
  refreshes exited 0; generated API contains all 12 public theorems and three definitions.
- All 12 public theorem axiom audits and mathlib API checks passed via
  `lake --old env lean /tmp/hml_moment_api.lean`; only `propext`, `Classical.choice`,
  `Quot.sound`. This completes contribution 9/100, with 148 public supporting
  theorem audits across nine modules. The full original goal remains active.
- Latest `scripts/formal_tools.py lint --check-generated` exited 1 on four unrelated
  concurrent modules unreachable from the BiScale umbrella: `CorrelationOriginEnergy`,
  `InfiniteGridOriginConcentration`, `SignedPrimePolarGramTransport`,
  `SignedPrimePolarPacket`. It also reported concurrent generated drift in
  `formal/LEAN_API.md` and `formal/LEAN_OVERVIEW.md` after the second successful
  index refresh. No owned lifting module was flagged. Existing large-file warnings
  remain; no repository-wide clean gate is claimed.
- Owned API/axiom scratch and lint capture removed; absence verified. All owned
  Lean, search, index and lint handles completed. Final source/docs/umbrella
  whitespace checks passed. No full build, numerical experiment, commit or push.

## Tenth result: fourth-moment variational jump receiver

Write m(u)=sinh(alpha u), S=mf, T=||m^2 f||^2, R_S=||mf||^2, and
H(x)=T cosh(alpha x)^2+(T+R_S)sinh(alpha x)^2. For h(u)=f(u)-f(u+x)
and w(u)=m(u)m(u+x), the earlier exact law gives int w h^2=2A,
A=cosh(alpha x)R_S-hS(x), while int h^2=2Delta_f(x).

The endpoint estimate h^2<=2(f(u)^2+f(u+x)^2), translation invariance and
sinh addition give int w^2 h^2<=4H(x). Indeed the symmetric endpoint weight is
m(u)^2[m(u+x)^2+m(u-x)^2]
=2[m(u)^4 cosh(alpha x)^2+(m(u)^4+m(u)^2)sinh(alpha x)^2].
Integrating the nonnegative square (h-lambda*w*h)^2 then yields, for every real
lambda, Delta_f(x)>=2lambda A-2lambda^2 H(x). This avoids division and exceptional
zero-energy cases; no source-support radius enters H or this inequality.

At alpha=1/2, choose finite nodes t_i, real amplitudes b_i and real controls a_i.
Put x_i=t_i-y, v_i=2 b_i^2 sech(x_i/2)a_i and
Q=sum_i 2b_i^2 sech(x_i/2)H(x_i)a_i^2. Summing the variational inequality and
using the actual multiplier Gram gives
secantJumpCollar >= R_S sum_i v_i cosh(x_i/2)-sqrt(R_S G_S(v))-Q.
No sign constraint on controls or weights is needed. On dyadic chains for actual
odd F, replace G_S by the verified frameGramUpper(F,N,v), retaining every source
error. Continuous finite weights permit integration over disjoint collars, giving
a full original secant receiver with no support-radius factor. The exact plastic
decomposition gives an unconditional signed receiver; the ninth moment budget
replaces its separate odd moment. On the full logarithmic source grid, its moment
cost is 2log2(R_S+sqrt(2V)), so neither collar nor moment term contains a support radius.

This trades support dependence for an actual fourth hyperbolic moment and an
explicit quadratic control cost. It need not dominate the earlier support envelope
for every source. No universal positivity, optimal control or inherited multiplier
zeros is claimed. Optimizing lambda is unnecessary for the unconditional theorem.

The fourth moment is tied exactly to the previous source variance. The identity
cosh(2alpha u)=1+2sinh(alpha u)^2 gives M=R+2R_S and W=R+4R_S+4T.
Consequently V=RW-M^2=4RT-4R_S^2, including R=0. Thus this receiver introduces
no independent fourth-moment invariant beyond the existing energies and variance.
The exact polynomial identity 4RT=V+4R_S^2 is included in this contribution's
paper proof and formal audit, not counted as a separate contribution.

Corpus query "hyperbolic weighted jump fourth moment support envelope" with
--module BiScaleUncertainty --any --per-module 2 --explore 0: 449 declarations
in 75 modules, hybrid partial47.97s; text/source unfinished, semantic coverage
unmeasured and compiler freshness partial. Actual existing jump identity,
support-envelope proof and Gram transfer were inspected; no fourth-moment
variational receiver appeared in returned candidates. Paper derivation complete;
Final actual-source compilation and all 18 public theorem axiom audits passed without warnings.

### Verification of the tenth result

- Final direct actual-source compilation exited 0 without warnings:
  `lake --old env lean GaloisForLFunctions/BiScaleUncertainty/FourthMomentJumpReceiver.lean -o .lake/build/lib/lean/GaloisForLFunctions/BiScaleUncertainty/FourthMomentJumpReceiver.olean`.
- Source SHA256:
  `8d9747052621b15517162d5e00e039c667a1fb0de1c5af6c6495e54d5d159e24`.
  Imported ninth module still matches its verified source hash.
- Main results: `FourthMomentJump.fourthEnergy_variance_identity`,
  `weighted_jump_square_le_fourth`, `source_increment_ge_variational`,
  `secantJumpCollar_ge_fourthGram`, `odd_secantEnergy_ge_fourthFrame`,
  `odd_plasticCrossover_ge_fourthFrame_momentBudget`, and
  `odd_logGrid_plasticCrossover_ge_fourthFrame`.
- Pointwise variational and full secant/plastic receivers are unconditional on actual
  compact input and signed real controls. Only the final logarithmic-grid moment
  specialization states source-domain zeros. No multiplier-zero or analytic premise.
- Final source has 402 lines. Integral rewrites required explicit lambda-form
  integrability statements because Pi function addition/subtraction was not reduced
  by the rewrite matcher. No proof statement was weakened and no heartbeat limit changed.
- Umbrella import and both README entry 13/module-map row 67 added. Generated API
  contains all 18 public theorems and six definitions. Both index refreshes exited 0.
- All 18 public theorem axiom audits and mathlib API checks passed via
  `lake --old env lean /tmp/hml_fourth_api.lean`; only `propext`, `Classical.choice`,
  `Quot.sound`. This completes contribution 10/100, with 166 public supporting
  theorem audits across ten modules. The full original goal remains active.
- Latest `scripts/formal_tools.py lint --check-generated` exited 1 on seven unrelated
  concurrent modules unreachable from the BiScale umbrella:
  `HyperbolicGaugeChebyshevEnergyRepresentation`, `InfiniteGridStrictEnergyLoss`,
  `ShortSupportEnergyInjection`, `SignedPrimePolarHalfLineDomain`,
  `SignedPrimePolarHalfLineTransport`, `SmallSourceCorrelationStability`,
  `UnitEnergySmallSources`. It also reported concurrent generated drift in
  `formal/LEAN_API.md` after the second successful refresh. No owned lifting module
  was flagged; existing large-file warnings remain. No repository-wide pass is claimed.
- Owned API/axiom scratch and lint capture removed; absence verified. All owned
  Lean, search, index, lint and auxiliary read handles completed. Final source/docs/
  umbrella whitespace checks passed. No full build, numerical experiment, commit or push.

## Eleventh paper theorem: attained hyperbolic-ray certificate

For actual compact f, d=log2, x_i=id-y and c_i=cosh(x_i/2), define
B=sum_(i=0)^N c_i^2, D=(1/2)sum_i H(x_i)c_i^3,
U=frameGramUpper(f,N,c), A=R_S B-sqrt(R_S max(U,0)).
Every original-source signed correlation remains in U. No grid zeros are assumed.
On canonical odd F, the controls a_i=lambda*c_i^2/2 produce weights v_i=lambda*c_i.
The actual Gram scales by lambda^2, so the fourth-moment collar transfer and
source frame upper bound yield lambda*A-lambda^2*D <= secantJumpCollar for lambda>=0.

Set lambda*=max(A,0)/(2D), C=max(A,0)^2/(4D), with total real division.
If T>0, each H>=T*c_i^2>0, hence D>0. Completing the square shows
lambda*A-lambda^2*D<=C for every lambda>=0, with equality at lambda*.
If T=0, 4RT=V+4R_S^2 and V>=0 force R_S=0, hence H=D=A=C=lambda*=0.
Thus the attained optimum and nonnegative actual collar certificate hold for
every source, including the degenerate case. This is an optimum only along the
chosen ray, not over every control vector.

For fixed f,N, C(y) is continuous: if T>0 its denominator never vanishes;
if T=0 it is identically zero. Moreover C>0 iff A>0, equivalently
(R_S B)^2 > R_S max(U,0). This is an exact signed-source activation test.
On doubled source-zero chains U=(R_S+sqrt(2V))*B, giving the specialized
threshold R_S*(B-1)>sqrt(2V) when R_S>0. Specialization is secondary;
main result and receiver retain all signed source data.

Integrating C(-y) over 0..d and tiling the disjoint dyadic collars gives
I_C<=J_sech(F). Hence I_C+R_plastic-2O^2<=P(F), unconditionally, and
I_C+R_plastic-2momentBudget(F,M)<=P(F) for independent M. Full-grid moment
specialization may replace this cost by 2d(R_S+sqrt(2V)). No universal positivity
of the full functional, global vector optimum, or external novelty is claimed.

Corpus query "hyperbolic fourth moment variational control optimization signed collar"
with --module BiScaleUncertainty --any --per-module 2 --explore 0 returned
1037 declarations/83 modules, partial59.05s. Text/source retrieval unfinished,
semantic coverage unmeasured and compiler freshness partial. Existing fourth-moment,
source-frame and origin-allocation proofs inspected; no corresponding attained
hyperbolic-ray receiver appeared in returned candidates. Classical scalar quadratic
optimization is supporting machinery, not a separately counted contribution.
Paper proof, final direct-source compilation and all public axiom audits complete.
Global lint remains nonzero only on unrelated concurrent modules listed below.

### Verification of the eleventh result

- Final actual-source compile exited 0 without warnings:
  `lake --old env lean GaloisForLFunctions/BiScaleUncertainty/OptimizedHyperbolicRayReceiver.lean -o .lake/build/lib/lean/GaloisForLFunctions/BiScaleUncertainty/OptimizedHyperbolicRayReceiver.olean`.
- Source SHA256 `862c9717d24a6f8a0f1efb03367e34432176d26340faf9656bc38be36167602c`;
  324 lines, six definitions and 16 public theorems. Imported tenth module's
  source hash revalidated unchanged. No source edit after the successful compile.
- Namespace `HyperbolicRay`; main results `optimalScale_attains`,
  `odd_collar_ge_optimized`, `optimizedCollar_pos_iff`,
  `odd_secantEnergy_ge_optimized`, and `odd_plasticCrossover_ge_optimized_momentBudget`.
  All primary receivers are unconditional on canonical odd compact inputs.
- Umbrella import added. Index refresh exited 0; all 22 public declarations indexed.
  The axiom scratch's theorem-name list matches all 16 public source theorems exactly.
- Canonical README was fully read and never edited; unchanged SHA256
  `80c91d482d9dfcfeb86508edcf5551d34d34a5ef333d3fab64be78e75dd67507`.
  The old README remains deleted. User's read-only instruction persists.
- Lean proof details: unfold before rewriting half-scale energy zeros, since simp
  normalizes 1/2 to inverse 2 before specialized rewrites. Supply the full summand
  explicitly to `Finset.single_le_sum`. Positive real multiplication was handled
  with scalar positive differences, avoiding an inapplicable global monotonicity class.
  No mathematical statement weakened; no heartbeat changes or full build.
- `lake --old env lean /tmp/hml_ray_api.lean` exited 0 without warnings. All 16
  public theorems depend only on `propext`, `Classical.choice`, `Quot.sound`.
  The module and its supporting lemmas count as one contribution: **11/100**,
  with 182 public theorem audits across eleven modules. Goal remains ACTIVE.
- `scripts/formal_tools.py lint --check-generated` exited 1, reporting five unrelated
  modules unreachable from the BiScale umbrella: `AnnularCorrelationSource`,
  `HyperbolicGaugeChebyshevEnergyRepresentation`, `MultiNodeSignedCliqueWeilCoercivity`,
  `SignedPrimePolarCoherentSchur`, `WeilFullFunctionalAndPrimitiveHyperplaneBridge`.
  No owned lifting module or generated-file drift was flagged. Existing large-file
  warnings remain; no repository-wide clean gate is claimed.
- Owned `/tmp/hml_ray_api.lean` and `/tmp/hml_ray_lint.txt` removed; absence verified.
  All owned source, API, search, index and lint processes finished. Final source/docs/
  umbrella whitespace checks passed. No numerical experiment, commit or push.

## Twelfth paper theorem: unconditional lattice-budget moment receiver

For actual compact f, d=log2, define h_k=h_f(kd), k in Z. Compactness makes
the support of k -> h_k finite. Put Gamma=sum_Z |h_k|. Let mu=M/R be the
existing mean, Q=||q_mu||^2, and set e_0=0,
e_k=(mu-cosh(kd/2)^2)*h_k/(2cosh(kd/2)) for k!=0. Put E=sum_Z |e_k|.
Both are intrinsic finite lattice sums, not hypotheses or chosen support radii.
Correlations may have either sign; the costs use their absolute values explicitly.

An even finite-support lattice kernel k obeys the Schur bound
sum_(i,j) w_i w_j k(j-i) <= (sum_Z |k|) sum_i w_i^2:
2w_iw_j k <= (w_i^2+w_j^2)|k|, symmetry exchanges the two sums, and each
translated finite row injects into Z. Apply it to h to bound the coalesced
source difference Gram by Gamma*A_collision <= 2Gamma*W2^2. Apply it to e
to bound the exact sourceCorrection by E*W2. Therefore, for canonical odd F,
G_S(w) <= C(F)*W2 for every N and signed w, where
C=R_S+E+sqrt(2Q Gamma)>=0. No source-zero assumption enters this frame.

The existing coherent-packet support estimate gives
(N+1)^2 O^2 <= (2B+Nd) C (N+1). An Archimedean integer-growth contradiction
eliminates B and N, yielding O^2 <= d*C unconditionally. Consequently the
already verified optimized collar I_C satisfies
I_C+R_plastic-2d*C(F)<=P(F), with neither an independent odd moment nor an
explicit support-radius factor. A finite moment budget remains potentially
sharper; no domination of every previous bound or universal positivity is claimed.

If all positive dyadic source samples vanish, Gamma=R and E=0. The exact law
Q*R=V recovers C=R_S+sqrt(2V), hence the old source-zero receiver. This is
a secondary specialization; main theorem admits every signed source correlation.
The new insight is the precise lattice-correlation cost replacing the global
blindness hypothesis in a uniform frame and support-radius-free moment penalty.
Classical Schur bounds and the Archimedean limit argument are supporting machinery.

Corpus searches: initial full-control query returned 835 declarations/85 modules,
partial57.83s; targeted lattice/moment/frame query returned 599 declarations/93
modules, partial78.38s. Both had unfinished text/source retrieval, unmeasured
semantic coverage and partial compiler freshness. Actual centered/collision/frame,
coherent-packet and Schur proofs were inspected. No corresponding unconditional
lattice-budget moment receiver appeared in returned candidates. No external
priority claim. Paper derivation, direct-source compilation and all public axiom
audits complete. Global lint has unrelated concurrent wiring errors listed below.

### Verification of the twelfth result

- Final actual-source compile exited 0 without warnings:
  `lake --old env lean GaloisForLFunctions/BiScaleUncertainty/SourceLatticeMultiplierFrame.lean -o .lake/build/lib/lean/GaloisForLFunctions/BiScaleUncertainty/SourceLatticeMultiplierFrame.olean`.
- Source SHA256 `68a380d612b38045195d2f1aa62428ffeb050afe993bc7e72da5f203559a3302`;
  318 lines, five definitions and 16 public theorems. Eleventh source hash
  revalidated unchanged. No source edit after the successful compile.
- Namespace `SourceLattice`; capstones `odd_sinhGram_le_latticeFrame`,
  `odd_moment_sq_le_latticeFrame`, `odd_plasticCrossover_ge_latticeFrame`,
  and exact secondary recovery `latticeFrame_of_source_zeros`.
  Main frame admits arbitrary signed weights; main moment and plastic receivers
  have only actual compact input (plus the collar cutoff for the latter).
- Finite support and summability of both lattice costs are derived from actual
  source compactness. Generic Schur and coherent-packet arguments are supporting
  machinery, not separate contributions. No support-radius quantity enters the
  definitions of either cost or the final moment penalty.
- Umbrella import added; axiom scratch names match all public source theorems.
  README remains read-only and unchanged, SHA256
  `80c91d482d9dfcfeb86508edcf5551d34d34a5ef333d3fab64be78e75dd67507`.
- Lean details: specify the function explicitly in reverse `Finset.sum_image`
  rewrites. Use `Int.eq_nat_or_neg` plus sample evenness to transfer positive
  lattice zeros to all nonzero integer lags. No statement weakened or heartbeat
  changed; no full build, numerical experiment, commit or push.
- `lake --old env lean /tmp/hml_lattice_api.lean` exited 0 without warnings.
  All 16 public theorems use only `propext`, `Classical.choice`, `Quot.sound`.
  Source/axiom lists match exactly. Index refresh exited 0; all 21 public declarations
  indexed. This completes contribution **12/100**, with 198 public supporting
  theorem audits across twelve modules; full goal remains ACTIVE.
- `scripts/formal_tools.py lint --check-generated` exited 1 on ten unrelated
  modules unreachable from the BiScale umbrella: `CoprimeAlternatingProjectionRate`,
  `CoprimeProjectionAngleNorm`, `CoprimeProjectionAnglePolynomial`,
  `CoprimeProjectionNeighbors`, `SignedGramCapacity`, `SignedGramCutoffComparison`,
  `SignedGramCutoffHierarchy`, `SignedGridEnergySources`, `SignedGridTailEquivalence`,
  `SignedGridTraceCompactness`. No owned lifting module or generated-file drift
  was flagged. Existing large-file warnings remain; no repository-wide pass claimed.
- Owned `/tmp/hml_lattice_api.lean` and `/tmp/hml_lattice_lint.txt` removed;
  absence verified. All owned source, API, search, index and lint handles finished.
  Final source/docs/umbrella whitespace checks passed; source and README hashes
  unchanged. No numerical experiment, commit or push.

## Thirteenth paper theorem: signed coherent correction and exact boundary law

Use the preceding actual source samples e_k, Gamma, Q, R_S. Set
sigma=sum_(k in Z)e_k and tau=2sum_(m>=0)(m+1)e_(m+1), finite intrinsic sums.
Because e is even and e_0=0, sigma=2sum_(m>=0)e_(m+1). Uniform-chain pair
counting gives exactly
sourceCorrection(F,N,1)=2sum_(m=0)^(N-1)(N-m)e_(m+1).
Once N covers the finite sample support this is (N+1)sigma-tau. Thus boundary
effects have an exact fixed intercept, while the extensive coefficient is signed.

Keep the already proved square-root bound sqrt(2Q Gamma)*(N+1). Then actual
coherent multiplier Gram satisfies G_S(1)<=C_signed*(N+1)-tau for all large N,
where C_signed=R_S+sigma+sqrt(2Q Gamma). This is a coherent-direction statement,
not an arbitrary signed-weight frame bound: negative correction samples cannot
be discarded for general coefficient vectors.

The packet support inequality implies O^2<=d*C_signed, d=log2. To remove the
fixed intercept without assumptions on its sign, write m=N+1 and expand the
bound into (O^2-d*C_signed)m^2 <= K*m+J, with fixed actual K,J. Since m>=1,
the right side is <=(|K|+|J|)m. If O^2>d*C_signed, an integer larger than
both the support cutoff and (|K|+|J|)/(O^2-d*C_signed) contradicts it.
In particular C_signed>=0 for every canonical odd source; no max or nonnegativity
premise is inserted.

The absolute predecessor exceeds this coefficient by
C_abs-C_signed=sum_Z(|e_k|-e_k)=2sum_Z max(-e_k,0)>=0.
Every negative correction sample forces strict improvement. The original plastic
receiver therefore strengthens by exactly 2d*(C_abs-C_signed), while retaining
the same optimized collar. Source-zero recovery remains exact. No universal
positivity of the full functional, general signed-vector frame with C_signed,
or external novelty is claimed. Classical triangular counting and the scalar
limit argument support this one research contribution.

Corpus audit: signed coherent/lattice query returned826 declarations/86 modules,
hybrid partial63.16s, unfinished text/source stages, unmeasured semantic coverage,
partial compiler freshness. Targeted lexical Toeplitz query returned732/103.
Actual source lattice, packet, lag-coalescence and finite-train grouping laws read;
no corresponding signed correction limit receiver appeared in returned candidates.
Paper proof complete; formalization pending.
