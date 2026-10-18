# RFHM: simultaneous prime-support and actual-theta completion

- **ID:** RFHM-THETA-COMPLETION-2026-10-18
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** Current RFHM candidate; native `JointAncestryGammaThetaBooleanClosedCreation` and `GammaSewnSynchronizedLcmContraction`.
- **Statement:** For every positive aperture, complex formation parameter, independent prime phase assignment, and fixed additional theta grade, the literal Gamma-weighted packets admit a nonzero all-support Hilbert source, exact forward creation covariance, and norm-convergent finite-prime cutoffs.

## Goal and limits

Construct a simultaneous, coefficient-faithful all-prime/all-compound source in the existing Gamma–theta carrier. Remove a global Hilbert-admission burden without normalizing away the actual theta grades or the synchronized coefficients. This does not identify the source with prime-Poisson multiplication, establish reflection sewing, or prove RH. The existing divisor-gauge and inverse-covariance obstructions remain applicable to their stated representations.

## Plan

1. Complete: audit native coefficients and prior completion results; attack the proposed estimate.
2. Complete: dependency-closed paper proof for squarefree incidence and Gaussian moment growth, specialized to the actual Gamma–theta source.
3. Complete for this change: four canonical individual Lean audits, umbrella wiring, 29 theorem axiom audits, 38 API probes, source hashes, and diff checks. Repository-wide lint ran and reports the unrelated unwired module recorded below. No umbrella builds.

## Formal result and validation

- Framework: `formal/GaloisForLFunctions/BiScaleUncertainty/SquarefreeGaussianCompletion.lean`.
- Arithmetic producer: `formal/GaloisForLFunctions/RHTower/GammaThetaSupportWeightBounds.lean`.
- Native completed source: `formal/GaloisForLFunctions/RHTower/GammaThetaFullSupportSource.lean`.
- Creation and exhaustion: `formal/GaloisForLFunctions/RHTower/GammaThetaFullSupportCreation.lean`.
- Main declarations: `memLp_jasGammaThetaFullSourceFun`, `jasGammaThetaFullSource_section`, `jasGammaThetaFullSource_ne_zero`, `summable_jasGammaThetaFullSupport_energy`, `jasGammaThetaFullSource_creation_covariance`, and `tendsto_jasGammaThetaFullSource_primeCutoffs`, all in `RHTower`.
- Each leaf passed `lake --old env lean <leaf> -j1 -o <olean> -i <ilean>` with no errors or warnings. Finished modules are wired into their respective umbrellas.
- `/tmp/hgt-rfhm-axioms.lean` passed: all 29 public theorems use only `[propext, Classical.choice, Quot.sound]`; all 38 API probes passed.
- `scripts/formal_tools.py lint` exited 1 solely because `GaloisForLFunctions.BezoutValuationIncidence.RenormalizedMobiusDefectAndFirstOctaveCancellation` is unreachable from its umbrella. This untracked module is outside this change and was not modified. Existing large-file warnings also remain. No new leaf is reported by lint.
- Audit evidence: `/tmp/hgt-rfhm-audit-manifest.json`, `/tmp/hgt-rfhm-source-sha256.txt`, and `/tmp/hgt-rfhm-{core,weights,source,creation,axioms,lint}.log`. Final source hashes checked against all four verified leaves.
- RH remains open. Next turn should rotate to a different family, rather than continuing PA/JAS/RFHM by default.

## Conjecture and attack

Write `W_x(P)` for `gammaSewnSynchronizedLcmWeight x P` and `Theta_k` for `jointAncestryCompletedThetaGradeL2 k`. Proposed conclusion:

`sum_P |z|^(2 |P|) W_x(P)^2 ||Theta_|P|||^2 < infinity`.

The source coefficient is a synchronized geometric sum. For positive aperture, each insertion into an unoccupied support should be bounded by the completed singleton coefficient, itself at most `1/(p+1)`. Hence `0 < W_x(P) <= product_(p in P) 1/(p+1)`.

Square-summability of these prime weights gives a head/tail bound for every finite product `product_p (1 + t^2 a_p^2)`: for every positive epsilon it is bounded by a finite constant times `exp(epsilon t^2)`. The head is a fixed polynomial; the tail has arbitrarily small square mass. With `t = |z| exp(y)`, the literal theta envelope `exp(9 |y|/2 - pi exp(2 |y|))` should absorb this bound. Tonelli then supplies simultaneous support/grade admission.

Attack points: the Boolean vacuum is exceptional in the synchronized geometric formula; prime insertion must be unoccupied; use squared norm summability rather than an unjustified sum of norms; retain the actual theta grade and all compound coefficients. A new bounded grade-successor operator would contradict the corpus and is not claimed.

## Audit log

- 2026-10-18 — Rotated after verified PA work to RFHM candidate. The proposed unrelated integer-successor carrier was rejected: no native-source covariance or Xi landing. Existing Boolean closed creation and Gamma–theta closed creation were found and will be reused.
- 2026-10-18 — Deep corpus searches completed for covariance and synchronized compound kernels. Source inventory complete; compiler applicability mostly source-only and semantic coverage unavailable. No numerical experiments, web search, or external novelty audit.
- 2026-10-18 — Canonical individual Lean audits passed for `BiScaleUncertainty/SquarefreeGaussianCompletion.lean` (three general completion theorems) and `RHTower/GammaThetaSupportWeightBounds.lean` (six unconditional arithmetic bounds). Both wired into umbrellas. Actual source completion and native creation covariance remain under formal verification.
- 2026-10-18 — `RHTower/GammaThetaFullSupportSource.lean` passed its canonical individual audit and is wired. This verifies actual product-space admission, independent prime phases, every fixed additional theta grade, exact support-coordinate recovery, nonvanishing, and simultaneous support-energy summability. Creator/cutoff leaf remains under verification.

## Dependency-closed paper proof [PROVED HERE]

The result also holds with every fixed additional actual theta grade `r >= 0`, and yields a forward creation equation on the completed source.

1. Let `a_p = 1/p`. The native aperture node at aperture one is exactly `a_p`. The sewn multiplier `C_x(p)` lies in `(0,1)` for `x>0`. On a nonempty unoccupied support, write `q=p^(-x)` and `R=product_(l in P) l^(-x)`. Both lie in `(0,1)`. The insertion gain is
   `C_x(p) [a_p/(1+a_p)] (1-q)(1-R)/(1-qR)`.
   Since `(1-q)(1-R) <= 1-R <= 1-qR`, this gain is at most `a_p/(1+a_p) <= a_p`. The singleton formula gives the same bound from the vacuum. Induction with the exact insertion identity proves `0<W_x(P)<=product_(p in P) a_p`, including the empty support. The sharper bound with `1/(p+1)` follows by the same induction but is unnecessary for admission.

2. For any summable nonnegative family `b_i` and any `epsilon>0`, there is `C>0` such that every finite set `S` and every `u>=0` satisfy
   `product_(i in S)(1+b_i u) <= C exp(epsilon u)`.
   Choose a finite head `H` with complementary sum less than `epsilon/2`. Put `delta=epsilon/[2(|H|+1)]`. The inequality `delta u <= exp(delta u)` gives
   `1+b_i u <= (1+b_i/delta) exp(delta u)`.
   Bound the head by `product_H(1+b_i/delta) exp(delta |H| u)` and the tail by `exp(u sum_tail b_i)`. Since `delta |H|<epsilon/2`, the asserted estimate follows. This is uniform in `S` and retains every compound; no bounded-grade assumption occurs.

3. Consequently, if `u,w` are measurable and nonnegative and `exp(c u) w` is integrable for some `c>0`, then
   `sum_(P finite) integral [product_(i in P)b_i] u^|P| w`
   is finite. For an arbitrary finite collection of supports, include all their indices in a finite set `S`, enlarge its nonnegative sum to the entire powerset, and use the exact powerset expansion `sum_(P subset S) product_(i in P)(b_i u)=product_(i in S)(1+b_i u)`. Step 2 gives an integrable bound independent of `S`. Bounded nonnegative partial sums imply summability. Fubini then places every measurable complex family dominated in squared modulus by these terms in the actual counting-measure product `L2`.

4. Take `b_p=|z|^2/p^2`, `u(y)=exp(2y)`, and `w_r(y)=exp(2r y) Phi(y)^2`, where `Phi` is the literal completed theta source. The prime reciprocal squares are summable by restriction of the integer p-series. The corpus's unconditional envelope is
   `0<Phi(y)<=U exp(9|y|/2-pi exp(2|y|))`.
   Hence `exp(u(y)) w_r(y) <= U^2 exp((2r+9)|y|-(2pi-1)exp(2|y|))`.
   Since `exp(2a)>=1+2a+2a^2` for `a>=0` and `2pi-1>5`, the exponent is bounded above by `C_r-a`: the remaining quadratic has negative leading coefficient and a finite explicit maximum. Therefore this function is dominated by an integrable multiple of `exp(-|y|)`. Step 3 proves the desired completion for every `z`, `x>0`, and `r`.

5. Define the completed source by the unchanged coordinate formula
   `F_(x,z,r)(P,y)=z^|P| W_x(P) exp((|P|+r)y) Phi(y)`.
   Step 4 proves it belongs to the existing `JASGammaThetaL2`. Every fixed support coordinate retains its complete complex coefficient and literal theta grade. Multiplication by `exp(y)` sends this source to the admitted source with `r+1`. The unoccupied insertion energy is bounded by `a_p exp(y)`, so the source lies in the domain of each native closed creator. After the toggle, its value vanishes on supports missing `p`. On supports `Q` containing `p`, the exact gain ratio cancels `W_x(Q.erase p)`, while the successor power identity and `|Q.erase p|+1=|Q|` give
   `z * (C_(x,p) F_(x,z,r))(Q,y) = F_(x,z,r)(Q,y)`.
   Thus `z C_(x,p) F_(x,z,r) = 1_(p in support) F_(x,z,r)` in the actual Hilbert carrier, also at `z=0` without division. This is forward creation covariance; it asserts neither inverse-preimage invariance nor a bounded theta-grade shift.

The proof uses only existing unconditional source formulas, the p-series, finite powerset algebra, and standard integration/completion. It does not depend on the location of Xi zeros. Full prime-Poisson identification and reflection orientation remain open.

Independent prime phases are retained as well: replace `z^|P|` by `product_(p in P) [z exp(i tau_p)]`, for any real phase assignment `tau`. Its modulus remains `|z|^|P|`, so the same proof applies verbatim. The forward law has scalar `z exp(i tau_p)` at prime `p`. This strengthened statement is included in formalization; no phase averaging occurs.

The admission theorem also discharges cofinal norm exhaustion. Multiply the completed source by the indicator that every prime in its support is at most `N`. These multipliers are measurable contractions and converge pointwise to one because every support is finite. Dominated convergence in `L2` proves norm convergence of the literal finite-prime cutoffs to the completed source. The exact coordinate formula identifies what each cutoff retains; no convergence hypothesis is added.

## Significance and boundary audit

- **Removed burden:** simultaneous Hilbert admission across the entire finite-prime-support lattice, with support cardinality advancing the actual unbounded theta ladder. Prior native files gave individual grades, finite compound retention, and closed prime creators. The new source needs no assumed global coefficient budget or cutoff-convergence premise.
- **Mechanism:** a finite-head/small-tail estimate makes the squarefree generating product have arbitrarily small exponential type in the Gaussian moment variable. The literal double-exponential theta cusp absorbs it. A total-square-mass estimate alone would leave an artificial bounded formation disk.
- **Coefficient fidelity:** no prime phase averaging, no replacement of synchronized Gamma coefficients, and no normalization of theta grades. The empty support remains the nonzero theta vacuum.
- **Boundary:** all positive apertures admit this source, including off-wall parameters. The forward occupied-support equation is not the impossible unital prime-coordinate intertwiner ruled out in the corpus. Prime-Poisson identification and Xi reflection remain open; RH is not proved.
