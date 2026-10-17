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

`update_plan` and `multi_tool_use.parallel` are unavailable in this session. This card carries the plan; independent reads use `Promise.allSettled`.

## Verified starting facts

- Pillar VI transfers a zero of `h_f` to equality `h_C=h_S`, not to a zero of either multiplier autocorrelation.
- Actual Pillar IX Lean theorem uses alpha=1/2 and denominator cosh(x/2)^2. Both README copies now match it.
- Worktree has unrelated concurrent research edits; preserve them.

## Completion gates

- [x] Read supplied brief and complete field README.
- [x] Run corpus search; inspect actual Pillar VI and IX theorem bodies.
- [x] Dependency-closed paper theorem with unconditional measured-defect formulation.
- [x] Exact Lean theorem verified and wired into the BiScale umbrella.
- [x] Dedicated knowledge ledger and truthful contribution accounting: five substantive results,
  with 13, 19, 18, 12, and 15 public supporting theorems respectively.
- [x] Uncompensated transfer into the full secant energy, source-derived support factor retained.
- [x] Actual signed plastic crossover receiver, including positive remainder, odd sine moment,
  and original origin coefficient; no inferred multiplier blindness.
- [x] Smooth odd fixed-energy family with a source zero at log(2), exact positive
  multiplier leakage law, and unconditional unboundedness relative to source energy.
- [x] Centered source difference-Gram control replaces multiplier off-diagonal
  data in the full secant/plastic receiver; weighted energy minimizer is exact.
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

## Sixth candidate: source-orthogonal leakage envelope

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
collar penalty should yield a stronger full secant/plastic lower bound.

On a source clique, each h_F(d_p)=0, so K=0 and every E_c=0. Therefore the
projected envelope equals the previous envelope at mu, and mu already minimizes
the whole scalar-centered envelope. This is an exact boundary: projection onto
F cannot supply a further clique gain. Away from a source clique the Schur
subtraction removes a real packet cost and the envelope dominates every center.
No strict improvement for every source, or full-grid coercivity, is claimed.

Paper mechanism is dependency-closed; formalization pending. Corpus search
`research "centered hyperbolic Schur projection difference packet" --module
BiScaleUncertainty --any --per-module 2 --explore 0` returned 204 declarations
in 26 modules. Hybrid search was partial (71.12s), with unfinished text/source
retrieval and unmeasured semantic coverage. Inspected actual existing abstract
Schur--Krein and translation-packet proofs. Their classical projection and
Cauchy--Schwarz mechanisms are reused, not counted as separate contributions;
the contribution is the exact multiplier-envelope comparison, source-clique
boundary and improved actual receiver. No external novelty claim.
Support envelope, remaining residual Gram, and negative odd moment remain.
