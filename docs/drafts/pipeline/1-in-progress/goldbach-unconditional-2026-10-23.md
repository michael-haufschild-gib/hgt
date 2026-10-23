# Unconditional binary Goldbach

- **ID:** goldbach-unconditional-2026-10-23
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** user task, `/Users/michael/.codex/attachments/91822624-9448-4930-99d7-19b89769b9bd/pasted-text-1.txt`
- **Statement:** Every even natural number greater than two is the sum of two primes.

## Goal

Prove `∀ n : ℕ, ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧
p + q = 2 * (n + 2)` without added analytic hypotheses or axioms.
This parametrization includes precisely all even natural numbers at least four.
Directly related Lean modules belong in `formal/GaloisForLFunctions/goldbach/`,
with their own umbrella. Completion requires a compiled proof of this exact
statement and an audit of its dependencies; a reduction or partial result does
not satisfy the goal.

## Gates

- [x] 0 → 1: exact target, source audit started.
- [ ] 1 → 2: complete dependency-closed paper proof, no open core.
- [ ] 2 → 3: exact theorem compiled with `lake --old env lean`, axiom audit passed.
- [ ] 3 → 4: standalone publication and novelty audit.

## Constraints

- Search local Lean corpus before mathlib; verify source statements behind hits.
- No numerical experiments, finite verification, added assumptions, proof holes,
  or raised elaboration limits.
- One foreground Lean command at a time; never build umbrellas or aggregate targets.
- Preserve unrelated existing worktree edits.
- Paper proof precedes Lean. A failed route requires positive-survivor analysis.

## Internal evidence

- `scripts/formal_tools.py research Goldbach --mode lexical --per-module 0`
  returned no declaration matches. This is an index observation, not proof that
  no related machinery exists.
- Semantic searches for prime sums and sieve parity are being checked against
  their exact source statements.
- `formal/README.md` contains older instructions allowing analytic hypotheses
  and umbrella builds. They conflict with current task and AGENTS.md; do not use them.

## External evidence (checked 2026-10-23)

- Li–Liu, [Theorem (1+1.9) on the Goldbach Conjecture](https://arxiv.org/abs/2606.05224),
  v2 dated 2026-08-08: preprint states an unconditional prime-plus-restricted-semiprime
  theorem; the abstract does not assert binary Goldbach.
- Zhao, [The exceptional set of Goldbach problem and Linnik's constant](https://arxiv.org/abs/2511.05631),
  v2 dated 2026-01-23: preprint states `E(X) = O(X^(7/10))`, with ineffective constant.
  This does not show the exceptional set is empty.
- Akeno, [On the level of distribution of Goldbach primes and its applications](https://arxiv.org/abs/2606.29559),
  2026-06-28: preprint states level of distribution `1/6` for almost all even targets.
  Its almost-all quantifier cannot be silently changed to every target.
- Full proofs, ancestry, subsequent work, and claimed complete proofs still need
  inspection. Abstracts are not imported proof dependencies.

## Current open core

`[OPEN CORE]` Establish a positive two-prime representation count for every even
target. Local distribution, average estimates, and identities must be audited
for the exact point at which they would imply pointwise positivity.

## Research cycles

No conjecture beyond the target has yet passed the paper-proof and novelty gates.

### Cycle 1: carry rough-sign control to the prime-detecting scale

The October frontier includes [Guo's rough-sign manuscript](https://github.com/aster2024/openai-math-followups/tree/main/rough-goldbach-parity),
whose LaTeX introduction was inspected directly. It states four sign patterns
at `z=exp((log N)^(1/10))`, and explicitly excludes a fixed-power cutoff.
The group exponent is below `0.47`; the moment length has exponent `0.52`;
the proof keeps resulting residue moduli subpower. A cutoff `N^δ` is outside
that argument. The underlying graph and zero-free inputs remain unaudited here.

**Exact candidate C1.** There exist absolute `c>0,N0` such that, for every
even `N≥N0`, at least `c N/(log N)^2` ordered decompositions `a+b=N` satisfy
`N/3≤a,b≤2N/3`, `minFac(a),minFac(b)>(2N/3)^(1/3)`, and
`λ(a)=λ(b)=-1`.

**Attack and verdict: BRIDGE.** The cubic detector makes C1 precisely a
quantitative balanced binary-prime assertion. It is a standard consequence
of the expected Hardy–Littlewood asymptotic restricted to the balanced interval and is substantially
stronger than merely positive representation count. Renaming it as a
rough-sign estimate does not prove it or remove the prime-correlation core.
No claimed proof or Lean hypothesis has been introduced.

**Positive result extracted:** the exact cubic primality detector, its prime-cube
boundary, and an integer signed-moment identity for the prime-pair count.
Complete paper proof and Lean certificate:
[boundary card](../3-formalized/not_new_scientific_knowledge/goldbach-parity-cubic-boundary.md).
These are known elementary bridges, not a claim to have moved the scientific frontier.

**Internal audit:** `PowerSievedLiouvilleRecurrence.lean` proves positivity for
infinitely many even totals of a different power-sieved sequence. It neither
asserts every total nor supplies a roughness cutoff that forces primes.
`SuccessorStateObstructionAndPhaseRefinement.lean` distinguishes multiplicative
state from additive phase; its exact finite observation identities supply no
pointwise prime-pair lower bound. Semantic searches later returned partial
results with `local worker disconnected or request cancelled`; lexical searches
were retained and no zero-hit completeness claim is made.

The subsequent exact `Chowla` corpus search exposed
`RHTower/Sieve/AveragedChowlaInterface.lean`. Its source was checked:
`uniformCorrelationSmall_of_averagedChowla` takes
`hAC : AveragedChowlaUniform ...` explicitly. It is an interface reduction,
not an unconditional discharge of the missing correlation theorem; it is
not imported by the Goldbach module. The `prime slot` lexical search produced
different Gamma/geometry slot notions, not a checked prime-slot cancellation
theorem usable here.

**Updated external lead:** [Pintz–Althöfer, 2026-10-11](https://arxiv.org/abs/2610.15559)
states an exceptional-set exponent `7/12+ε` using a common zero-free half-plane.
[Lü–Wang–Wu, 2026-10-14](https://arxiv.org/abs/2610.20242) states Möbius cancellation
on shifted primes. Both are primary-source leads, not verified dependencies.
Neither abstract states binary Goldbach.

**Next exact question:** Can complete multiplicativity control the *signed*
root sum at a polynomial sieve level while retaining its local bias? An
absolute correlation estimate that ignores one-point biases is not a valid
replacement. The needed target is the signed combination `R0-2R1+R2`,
not an unsupported assertion that all three correlations are small.

### Cycle 2: one-point bias and polynomial-level root averaging

**Candidate C2.** Put `z(N)=floor(N^(1/3))+1`, and use the exact support and
moment definitions on the boundary card. There exist `c>0,N0` such that
`R1(N,z(N))≤-c N/(log N)^2` for every even `N≥N0`.

This asks for a strict negative one-point Liouville bias after sieving both
summands. It would suffice for positivity: pointwise `λ(a)λ(b)≥-1`, hence
`R2≥-R0`, and the audited identity gives `4G≥-2R1>0`.
This is a deduction on paper, not a new analytic hypothesis inserted into Lean.
It does not handle the initial range without a further argument.

**Attempted proof and first unresolved step.** Expanding the roughness filter
produces residue restrictions depending on both the target and the sieve
divisors. An unsifted Liouville estimate cannot be applied to this weighted
sum without a uniform error theorem. The needed uniform statement was not
found among the inspected corpus declarations or established from the
current external manuscripts. `[OPEN CORE]`: a strict signed estimate for
this polynomially sifted, reflected one-point sum. Verdict: **BRIDGE**;
the candidate is unproved and no scientific novelty is claimed for the reduction.

**Sharper source check.** Lü–Wang–Wu's
[root-averaging argument and Appendix A](https://arxiv.org/html/2610.20242v1)
use an error of size `A B S^2 min(A,B)^(-1/100)` in their root count.
For their balanced Type II boxes with auxiliary product `Y=x^o(1)`,
`A B=x^(1+o(1))` and `min(A,B)≤x^(1/2+o(1))`. Substituting even one
prime label of size `x^(1/3)` into that error leaves relative upper-bound
size at least `x^(2/3-1/200+o(1))`; the displayed error estimate supplies
no small error there. This diagnoses a failed *direct use of that bound*,
not a lower bound for the actual error and not a proof that another
root-averaging argument is impossible. The full external proof remains unaudited.

### Cycle 3: a weight approaching a prime detector

**Source audit.** Guo's [Jordan-weight reduction](https://github.com/aster2024/openai-math-followups/tree/main/almost-prime-pairs-reduction)
was read through the full mass, tail, and one-point proofs, not only its
abstract. It uses `σ=c/log X` and `Jσ(n)=∏_{p|n}(1-p^(-σ))`.
Its unsigned lower bound is obtained on `X^θ`-rough pairs and contains
`(1-exp(-cθ))^(2K0)`, with fixed `K0=ceil(1/θ)+1`. Its one-point bound
requires `c≥c0(ε)=θ^(-1)log(100B/ε)`, where
`B=2ceil(1/θ)+2`. The proof compares a truncated weight `U` with the full
weight using `aU≤W≤U`, `a=(1-exp(-cθ))^B`; this comparison loses its useful
relative error when `c→0`. These are dependencies in the displayed proof,
not a disproof of estimates obtainable by a different argument.

The source explicitly leaves the weighted two-point contraction unproved.
Its reflection remark supplies a large-`c` one-point statement, but does not
assert the additional uniform tail and joint estimates for varying targets.
Its fixed-`c` mass estimate cannot be used with `c=c(N)→0` without controlling
both constants and thresholds. Distinct prime factors in `Jσ` also mean its
first-order coefficient detects prime powers, not just primes.

**Exact candidate C3.** For `N≥4` and `0<c≤1`, set

`w(N,c,n)=μ(n)^2 ∏_{p|n}(1-exp(-c log p/log N))` for `2≤n≤N-2`.

Let `P(N,c)` be the sum of `w(N,c,a)w(N,c,b)` over ordered positive pairs
`a+b=N`, `a,b≥2`, with `λ(a)=λ(b)=-1`. Put `c(N)=(log N)^(-2)`.
There exist absolute `κ>0,N0` such that every even `N≥N0` satisfies

`P(N,c(N)) ≥ κ c(N)^2 N/(log N)^2`.

The squarefree factor and the removal of the unit are essential parts of
this candidate. They are not present in the quoted Jordan-weight theorem.

**Elementary coefficient audit (paper only).** Let `G(N)` count all ordered
prime pairs summing to `N`. Then

`0 ≤ P(N,c) ≤ c^2 G(N) + N c^4/27`.

Indeed, `1-exp(-ct)≤ct` for `t≥0`. For a squarefree summand `n≤N`, write
`t_i=log p_i/log N`; these are positive and sum to at most one. Every
weight is at most `c`. A composite with negative Liouville sign has at
least three prime factors. The first three factors have product at most
`c^3/27`, by the three-variable arithmetic–geometric mean inequality;
all remaining factors are at most one. Thus a pair with a composite
endpoint contributes at most `c^4/27`. There are fewer than `N` pairs.
A prime pair contributes at most `c^2`. Zero squarefree weights do not
contribute. This proves the displayed bound, including prime-power removal.

C3 would therefore give `G(N)≥κN/(log N)^2-N/(27(log N)^4)>0`
for all sufficiently large even `N`. The exact initial range still needs
a separate argument. Conversely, a quantitative balanced prime-pair lower
bound gives C3: for balanced primes and large `N`, each prime weight is
at least `c/4`. Verdict: **BRIDGE**, not a new analytic theorem or a
scientific advance. The elementary coefficient bound is unformalized;
no conditional analytic interface was inserted into Lean.

`[OPEN CORE]`: prove the weighted lower bound with a parameter tending to
zero, including its squarefree restriction and its uniformity in the
reflected target. The cited mass proof supplies a higher power of `c`,
and its signed proof works in the opposite parameter range. C3 remains
an active target, not a retired impossibility claim.

### Cycle 4: audit the elementary Liouville–Goldbach mechanism

Read the primary [proof outline](https://github.com/CaptainSude/Liouville-Goldbach/blob/main/lean/PROOF.md),
the paper's reduction and commuting-symmetry argument, and the statement
in `lean/LiouvilleGoldbach/Main.lean`. The repository reports a complete
Lean proof that every even `N>2` has a negative-negative Liouville pair.
Its Lean toolchain and dependency closure have **not** been replayed here,
and none of its files has been imported into this project.

The elementary proof first obtains positive-positive pairs at `2r` for
prime `r>3`. In its general final branch it writes `N/2=rsc` with `r,s`
prime and `λ(c)=1`, then multiplies such a pair by `sc`. Since `sc≥2`,
both outputs share a nonunit factor. If both outputs were prime, both
unscaled summands would have to be one, contradicting their sum `2r>2`.
This branch therefore produces **no prime pair**, irrespective of the
choice of the positive-positive pair. The diagonal branch produces primes
only when `N/2` is prime; the small-factor branch rescales the base pairs
at `8,12,18`, which remain prime pairs only for scale one.

This diagnoses a failure of directly transferring that construction to
Goldbach; it does not criticize its stated Liouville theorem. Common-factor
classification is elementary and is not counted as novel positive salvage.
The source's actual positive theorem remains its Liouville representation
result. The source does not claim its scaling preserves primality.

**Candidate C4 (separate, unproved).** Every even `N≥8` has a pair
`a+b=N`, `gcd(a,b)=1`, `λ(a)=λ(b)=-1`.
This tests whether the common-factor defect can be removed before imposing
the cubic roughness threshold. It still permits coprime odd-parity
composites and therefore does not imply Goldbach. The universal statement
has not passed the novelty audit. Corpus queries `LiouvilleGoldbach` and
`liouville coprime` returned no declarations; these are limited lexical
observations, not absence claims. The external searches located Mangerel's
2024 paper and the newer sources above, but no checked proof of this exact
all-target coprime statement.

**First failed transfer.** Restricting the commuting-symmetry proof to
units modulo an even target invalidates its doubling step: doubling
sends units to nonunits. A prime-modulus intermediate argument can also
produce even-even pairs, whose gcd is two. Neither operation preserves
C4's support. `[OPEN CORE]`: obtain replacement reflection and dilation
relations on the unit support, or prove a uniform primitive signed count
by an independent argument. Verdict: **SURVIVES PRELIMINARY ATTACK** as a
conjecture; no dependency-closed proof or novelty claim yet.

**Second novelty attack: eventual version already follows from a parent.**
Guo's rough-sign theorem, if its stated proof and dependencies are valid,
already gives C4 for sufficiently large even targets. On its support, a
common prime divisor of `a,b` divides `N` and exceeds
`z=exp((log N)^(1/10))`. The number of noncoprime pairs is at most

`N ∑_{p|N, p>z} 1/p ≤ N log N/(z log 2)`.

This is `o(N/(log N)^(1/4))`, hence smaller than each asserted sign-pattern
count. Removing these pairs preserves all four signs, balance, squarefreeness,
and the growing factor-count bound when the latter two are imposed. This
deduction is elementary; it has not supplied a new analytic input or replayed
the parent proof. Revised verdict: **BRIDGE**. The eventual claim is a
routine consequence of a stronger claimed parent; the exact finite-threshold
claim remains unproved here. C4 is not the leading route toward Goldbach.

### Cycle 5: audit a claimed signed-affine prime lower bound

A primary preprint by Juan Moreno Borrallo claims eventual Goldbach through
a centered Liouville dispersion estimate. Its Fourier removal step requires
a separate audit: fixed-order subpower derivative bounds do not justify its
specified cutoff `exp(sqrt(log X))` with `O_B(X^(-B))` error.
An adaptive subpower cutoff does give a valid replacement by diagonalization.
The paper's actual weight class and downstream uses still need checking;
neither the full result nor its negation has been established here.
See [active dispersion audit](goldbach-signed-affine-dispersion-audit.md).

**Further proof attack.** Lemma 10.4's short-fibre argument uses
`u≤X/A` as though it implied `u≤sqrt(X)` while `A≤sqrt(X)`. A primitive
one-form family shows that its listed size assumptions allow a semiprime
cofactor. Full two-form support is not asserted for that family.

More decisively, Proposition 10.5's second Type I invocation omits the
affine slope from the progression modulus: `a≡r (mod ud)` and
`h=b₂a-T` give exactly `h≡b₂r-T (mod b₂ud)`. Theorem 4.3 requires the
full product modulus below `X^(1/2-η)`, whereas `b₂≍X/A≥X^(1/2-o(1))`.
That displayed application cannot supply the claimed estimate. A new
average retaining `b₂` would need proof. The exact image and period
classification is now
[formalized](../3-formalized/not_new_scientific_knowledge/goldbach-affine-progression-conductor.md);
it is known algebra, not a new analytic theorem.

`[OPEN CORE]` for this repair: bound the actual long-modulus average,
retain the semiprime-cofactor branch, and justify centering before Cauchy.
The direct Type I transfer is invalid as written; the broader dispersion
route has not been proved impossible and remains active.

**Repair attempt checked.** The local averaged-short-interval capstones
retain spectral-majorant or limiting assumptions; their exact source was
read. Wei's quantitative short-progression theorem has logarithmic modulus
range and averaging over starting points, so it does not supply the
polynomial modulus or every-target quantifier needed here. The unit
cofactor `u=1` contains the entire prime-first branch, so deleting short
fibres would delete a central analytic contribution.

### Cycle 6: retain root congruences through the cofactor energy

Derived a finite common-cofactor inequality and its maximal version:
`Σ_{q≤Q} max_{t≤H}|Σ_{h≤t,q|h}u(h)S(h)|
 ≤(HΣ_{q≤min(Q,H)}1/q)^(1/2)(E E₂)^(1/4)`,
where `|u|≤1`, `E=Σ|S|²`, and `E₂=Στ(h)²|S|²`.
This does not permit replacing the common inner sequence by an arbitrary
modulus-dependent sequence.

For actual label sums, the summed root energy has exact Gram kernel
`D_w(h gcd(a,b))`. Its difference from the common-cofactor part is a
positive quadratic form supported on shared labels. An elementary
divisor-moment argument bounds the unweighted shared-label remainder;
the analytic small-energy estimate and the final sum of absolute root
sums remain distinct requirements. The latter cannot use `H/q` as the
outer-support count when a label shares primes with `q`.
See [energy card](goldbach-common-cofactor-energy.md) for complete finite
derivations and the remaining terminal-label case.

The same audit corrected a structural overstatement: a product-residue
restriction can be a matching of orthogonal row and column blocks, hence
an operator-norm contraction. It need not be a single endpoint projection.
This supplies neither a modulus-density factor nor the required family
average. No unrelated twin-prime files were changed.

**New external lead.** Guo's October 22 manuscript gives an explicit
varying-target adaptation for `μ(N−p)`, conditional on specified LWW
arguments and a zero-free input. Its Goldbach assembly, root count,
character energy, and change dictionary were read. It retains subpower
auxiliary moduli and an iterated-limit removal of marks. It neither
states nor supplies the required polynomially sifted signed estimate.
See [source audit](goldbach-varying-shift-source-audit.md).

Verdict: active transfer investigation; no new scientific theorem or
unconditional prime-correlation input has been established.

### Cycle 7: quantify the mass on which auxiliary marks vanish

For fixed `0<α<β<1`, let `P_N` consist of primes between
`exp((log N)^α)` and `exp((log N)^β)`, with divisors of `N` removed.
Candidate M1 is the classical-sieve asymptotic

`Σ_{p<N, gcd(N−p,P_N)=1}log p ~ N(log N)^(α−β)`.

A Bonferroni/Bombieri–Vinogradov derivation and its uniformity checks are
recorded on the [mark-avoidance card](goldbach-mark-avoidance-mass.md).
Every nonempty mark using only these primes vanishes on that entire set.
Consequently the mass sets a sharp support floor for absolute or squared
approximation of one, even after enlarging the approximation class.
At the source's encompassing exponents `0.1,0.2`, this floor is larger
than the expected weighted two-prime scale `N/log N`.

This concerns an absolute-error transfer only. It makes no assertion
that the signed residual has the wrong sign or cannot be estimated.
The surviving arithmetic count, its local dependencies, and its exact
formalization still require audit. The route has not been closed or
reported as a novel discovery.

### Cycle 8: retain shared marking primes in reflected Type I

The [Type I card](../2-fully-proven/goldbach-retained-modulus-type-i.md)
now contains a complete classical paper deduction. It bounds the actual
marked reflected Type I sum, averaged over odd squarefree root moduli
q≤N^(51/100) coprime to N, with no requirement that q avoid the marking
primes. Arbitrary coefficients of size at most log N are allowed for
d≤N^(1/5); every fixed logarithmic accuracy is available.

The proof retains l=lcm(a,q), extracts g=gcd(r,N), and applies maximal
Möbius Bombieri–Vinogradov to the reduced modulus dr/g at length N/(lg).
The complete root average is paid by

`Σ_(q≤Q)1/lcm(a,q)≤τ(a)(1+log Q)/a`.

Both finite truncation errors retain their actual root-divisor
multiplicities. The target-common-factor discard and the primitive
affine divisor moments were proved with their gcd costs intact. The
same argument works throughout the strict classical range 2u+θ<1
for d≤N^u and q≤N^θ.

The primary maximal Möbius-BV statement was checked in Murty–Vatwani
(2018), Proposition 3, p. 115, citing Siebert–Wolke (1971). Its uniform
coprimality extension is proved on the card by a smooth-divisor
convolution. This is a classical consequence, not a novelty claim or
a prime-correlation theorem. Exact Lean closure remains open: the
corpus search has not supplied a checked maximal Möbius-BV theorem.
The signed Type II estimate and signed removal of marks are unchanged
open inputs. No analytic premise was added to Lean.

The zero-free source audit also located the actual upstream Lean
solution and its comparator mapping. Its endpoint and assembly were
read; the full import/axiom closure was not checked locally. That is
a precise dependency lead, not a new certificate or a Goldbach proof.

### Cycle 9: actual reflected marked prime root averages

Opened [R1 and R2](goldbach-reflected-marked-root-average.md). R2 asks,
for each fixed θ<1 and precision A, for a fixed number of pools such that

`Σ_(q≤T^θ, q odd squarefree, (q,T P_T)=1)
 max_(T/4≤t≤T/2)|Σ_(T/4<p≤t, q|T−p)log p μ(T−p)W_T(T−p)|
 ≪ T(log T)^−A`.

This is an actual prime sum with independent endpoints. The pool-coprime
modulus restriction is explicit. It does not prove Goldbach, since its
mark vanishes on large prime complements.

**Paper transfer completed.** A common Fourier envelope removes the
endpoints with polylogarithmic frequencies; its error is paid after
summing the root progressions. Choosing U=V=T^((1−θ)/8) puts Type I
in the proved range. For Type II, the common-cofactor inequality combines
small unweighted energy with the coarse divisor-weighted energy
`E₂≪TY(log T)^17`. Every prime-power, target-unit, repeated-mark, and
Mellin-tail error retains its actual root-divisor multiplicity. This
gives the full R2 transfer from the reflected source energy.

**Source audit.** Replayed LWW Sections 4.2–4.7 and Appendix A against
Guo's index-T lattice, unit-root density, and character average. No gap
was found in the inspected moment/root/memory chain. The source's weaker
zero-free-rectangle major-arc proof has a genuine shorter-variable range
issue; a higher moment and rescaled prime-sum endpoint repair it on paper.
Under the stronger fixed seven-eighths theorem, Guo already records a
contour shortcut avoiding this exceptional-character argument altogether.
Its major-arc twists are modulo kT; only their quotient is induced from
the small modulus k. This conductor distinction is now explicit.

**Remaining dependency.** The actual upstream zero-free proof closure is
still not locally verified. Its certificate construction and successor
endpoint were followed further, but not every analytic dependency. Thus
R2 stays in stage 1; no new unconditional prime theorem or Lean analytic
premise is claimed. The shared-prime Type II case and signed removal of
marks on prime-detecting support remain separate open questions.

**Corpus revisit.** A semantic search for positive additive prime
convolution returned the actual PM prime-convolution theorem and the
Steinhaus prime-occupation bound. Their Lean statements were read:
`pmPowerDampedFermiSource_prime_convolution_error` concerns a smooth
PM kernel at q/X, while `sum_normSq_primeConvolution_le_occupation`
is a multiplicative convolution upper bound. Neither supplies the
pointwise reflected prime correlation. The prime-square Fourier and
heat-echo cards likewise distinguish exact reconstruction from the
missing moving-scale arithmetic estimate; they were inspected as leads,
not used as new Goldbach inputs.

### Cycle 10: make the RH–Goldbach relationship exact

The user requested Lean bridges between the two problems. The detailed card is
[RH–Goldbach bridges](../3-formalized/not_new_scientific_knowledge/goldbach-riemann-hypothesis-bridges.md).

Let `w(n)=1_(n prime) log n` and let `B(N,t)` count ordered pairs weighted
by `w(a)w(b)`, with `a,b≤N` and `a+b=t`. Finite partition gives
`Σ(t≤2N)B(N,t)=θ(N)²`. The existing corpus von Koch equivalence, mathlib's
unconditional prime-power correction, and Chebyshev's linear upper bound
give the dependency-closed paper theorem

`RH ↔ Σ(t≤2⌊x⌋)B(⌊x⌋,t)−x² = O(x sqrt(x) log²x)`.

At a single target, exact expansion gives
`Σ(a+b=t)w(a)w(b)=2θ(t)−(t+1)+Σ(a+b=t)(w(a)−1)(w(b)−1)`.
The left side is positive exactly when t is a sum of two primes. Thus the
two statements use the same actual prime weights, but the RH average bound
and every-target reflected-correlation lower bound are distinct requirements.
No equivalence of ordinary RH and ordinary binary Goldbach is inferred.

**Verdict: BRIDGE**, not new scientific knowledge. Published literature
already supplies the stronger classical triangular-average RH equivalence.
The finite identities and boxed criterion are formalized in
`goldbach/RiemannHypothesisBridge.lean`; all fourteen theorem closures passed
the direct compile and standard-axiom audit. In particular,
`riemannHypothesis_iff_boxedPrimePairMass_error` and
`goldbach_iff_reflectedPrimeCorrelation` are unconditional equivalences;
the triangular criterion is not being represented by an assumed interface.
The Goldbach task still requires arithmetic
control of the reflected correlation on the support missed by the marks.

### Cycle 11: move marks onto the predecessor and attack the signed term

Following the user's direction to prioritize original proof work, moved
the marks from a possible prime complement n to n−1. The old support
vanished at every large prime n; the new support permits them. This
changes the sufficient weighted target and avoids requiring subsequent
removal of these marks. It does not assert a prime pair exists there.

The [new Type I deduction](../2-fully-proven/goldbach-predecessor-mark-type-i.md)
is complete on paper throughout 2u+θ<1. Its reduced modulus is
a d r/g at length T/(qg). Aggregating all mark/roughness factorizations
of that modulus costs a fixed logarithmic power, because their degree
was truncated at O(log log T). The proof pays both truncation errors
with the actual root multiplicities. This is a classical BV consequence;
no scientific novelty or new Lean analytic certificate is claimed.

The [direct balanced-term attempt](goldbach-transverse-mark-correlation.md)
then bounds the diagonal and nearby slopes and retains the exact
two-mark CRT. Shared marks force gcd(a₁,a₂)|n₁−n₂. On each resulting
progression the signs are λ(A_i−Dn_i v), with A_i≡1 mod a_i and
determinant DT(n₁−n₂). Thus the marks no longer furnish divisors of
the signed arguments. The old multiplicative cancellation step is
invalid here; multiplying the signs instead produces a quadratic
Liouville sum, outside the proved linear Type I estimate.
For the actual Möbius assembly, both squarefreeness indicators must
also remain in that quadratic sum; no λ-to-μ transfer is assumed.

The far-slope signed average is still unproved. Its exact sufficient
bound and the weaker alternative retaining the original coefficient
signs are recorded on the working card. Neither Goldbach nor RH has
been proved. No additional external audit is being counted as progress
on this missing estimate.

### Cycle 12: the user's RH-language reformulation

Read the twelve requested programme READMEs and their actual source
declarations. The [formalized language bridge](../3-formalized/not_new_scientific_knowledge/goldbach-rh-language-reformulation.md)
uses the existing RH divisor response, squarefree projection and unit
removal. Its quadratic damping coefficient is the prime-pair weight.
The same target is also the actual SAEI incidence energy, reflection-even
minus reflection-odd energy, and mass minus reflection defect. These
identities and equivalences are unconditional; no signed estimate is
assumed. The square-divisor-tail second moment was also closed in Lean;
the full signed bilinear comparison remains paper-level.

The [damping-parity card](../3-formalized/not_new_scientific_knowledge/goldbach-damping-reflection-parity.md) now gives
a further dependency-closed paper deduction. Symmetric gauge turns
damping reversal into multiplication by μ(k). Its odd sector is a product
of hyperbolic sine factors on squarefree negative-Möbius support. Doubling
damping multiplies each endpoint by at least 2 to the number of its prime
factors. Every supported pair containing a composite therefore amplifies
by at least 16. A prime pair gives a quadratic coefficient and limiting
amplification four. Thus, for each target N,

    N has a prime pair ⇔ ∃ε>0, O_N(2ε)<16 O_N(ε).

The exact finite two-scale equivalence is formalized, without a
hypothesis asserting the inequality. Its leaf check passes without warnings;
six audited closures contain only standard Lean foundations. The requested research-language
translation is substantive work under the user's latest steering.
The original goal still requires proving this strict inequality at every
even target, or closing the earlier signed estimate. The new equivalence
does not discharge that arithmetic obligation.

### Cycle 13: test projective parity transport on the integer rectangle

Previous goal turn was progress: the finite two-scale criterion and its
source identities were checked and audited. The present turn attacked a
specific cancellation mechanism for the retained matrix μ(T−mn).

On rational coordinates m and T/n, a fractional linear map g has the
exact difference-kernel transformation law, with its determinant and one
denominator per coordinate. The proposed next step was to cover a positive
fraction of a balanced integer rectangle by a small common family of such
maps, then use their parity transformations. The integrality step fails:
a return denominator divides det(g), and the induced column map has
determinant T²det(g). A polylogarithmic family of nondiagonal maps of
polynomial height therefore has only a vanishing fraction of integer
returns. Diagonal maps preserve mn itself and give no new sign change.

This fixed-family coverage premise is
[retired with its exact scope](../5-failed/goldbach-projective-parity-returns.md).
Its [positive survivor](../3-formalized/not_new_scientific_knowledge/goldbach-projective-integral-returns.md)
is the sharp 2τ(|det|) return bound, exact inversion classification, and
joint/family return budget. These are now unconditional Lean theorems;
the leaf and six closures pass audit. No analytic cancellation estimate
was proved and no scientific novelty is claimed for this elementary audit.

The same check rules out two silent repairs: homogeneous transport moves
the target, while removable row/column sign gauges leave all bilinear unit
tests and cycle signs unchanged. A new correspondence argument must retain
the fixed target, count its integral returns, and estimate the residual
arithmetic signs with both squarefree masks. It cannot assume any of them.

## Current verified state and continuation

- Goldbach target is **not proved**; main goal remains active.
- The boundary module and all ten declaration closures passed direct Lean
  compilation and axiom audit; only standard foundational axioms occur.
- The affine-progression conductor module and all three declaration
  closures also passed direct compilation and axiom audit. Its period
  classification certifies that a frozen slope cannot be silently removed
  from an arithmetic progression modulus.
- The RH–Goldbach bridge module and all fourteen theorem closures passed
  direct compilation and axiom audit. RH is equivalent to a prime-only boxed
  average error law; Goldbach requires the separate pointwise correlation bound.
- Cycle 12's same-source, incidence-energy and finite two-scale extensions
  also pass direct compilation and closure audits. They add unconditional
  reformulations, not the missing all-even positivity theorem. The quantitative
  [two-scale minorant](../2-fully-proven/goldbach-odd-damping-extraction-minorant.md)
  is proved on paper and remains unformalized.
- Exact scientific advance claimed: **none**. The certified bridge prevents
  a false passage from rough negative parity to primality.
- Research next: attack the actual missing signed estimate, not another
  detector identity. C2 requires the polynomially sifted one-point bias;
  C3 isolates the corresponding coefficient at a vanishing weight parameter.
  **Current user-directed bridge:** Cycle 12's source-language and
  two-scale bridge is complete. Attack its strict arithmetic inequality.
  The scale audit explains the joint range ε log N<log 4 in the un-gauged
  comparison; fixed-damping mass estimates do not supply that uniform input.
  Cycle 13 excludes a polylogarithmic family of fixed projective maps as
  a dense integer pairing mechanism. Any adaptive correspondence must
  pay its actual return multiplicities and keep the additive target.
  Cycle 11's predecessor-mark far-slope signed covariance remains an
  alternative analytic frontier. Its Type I deduction is closed on paper. Pursue the
  original analytic argument, rather than extending the source audits
  listed below or replacing its missing bound with a Lean premise.
  Audit the claimed dispersion theorem in Cycle 5 after repairing its
  Fourier cutoff; check whether subsequent estimates use only a subpower
  frequency range or rely on its unsupported explicit cutoff.
  Do not spend another cycle re-proving the cubic detector or upgrading
  an almost-all result to an every-target statement.
  Current continuation also includes the exact shared-label remainder
  in Cycle 6 and the signed residual on the mark-avoidance support in
  Cycle 7. Completing a classical unsigned count does not discharge
  either signed input. Newer varying-shift claims remain dependencies
  to audit, not unconditional inputs.
  Cycle 8 closes the reflected Type I part on paper, including shared
  marking primes. Its exact analytic Lean dependencies remain to be
  formalized; do not replace them by assumptions or spend another
  cycle re-deriving the lcm identity.
  Cycle 9 completes the pool-coprime marked root-average transfer and
  paper replay of the reflected moment chain. Its precise remaining
  source obligation is the external fixed zero-free proof closure.
  Neither that theorem nor a stronger marked level can determine the
  signed mass where every mark vanishes. The next conjecture must address
  that missing arithmetic information, rather than another cutoff transfer.
- C1–C4 are active targets, not retired routes. No actual
  counterexample to Goldbach has been produced.
- Integration: `goldbach/Main.lean` imports the completed leaves and is imported by
  `MainTheorems.lean`; umbrellas were not built. Index regeneration passed.
  The most recent whole-repository lint is recorded on the Cycle 12 language
  bridge card: unrelated reachability/root-leaf diagnostics and a generated
  overview changing under concurrent edits; no Goldbach finding. No new
  whole-repository lint run is claimed for the damping-parity extension.
  All owned commands terminated; no pending build or scratch job remains.
  Cycles 6–9 changed research cards only; no Lean proof was added or
  recompiled, and no new repository-wide verification is claimed.

## Log

- 2026-10-23 — Read original task and repository rules; recorded exact acceptance
  criterion before proof work. Existing unrelated worktree changes left intact.
- 2026-10-23 — Audited Jordan-weight constants and elementary Liouville scaling;
  recorded C3, its coefficient bound, and C4 with its failed support transfer.
  No new Lean claim, complete Goldbach proof, or scientific advance in this batch.
- 2026-10-23 — C4's eventual version reduced to the stronger rough-sign claim;
  opened a direct audit of the claimed signed-affine lower bound and derived
  an adaptive-cutoff repair of its Fourier-removal argument on paper.
- 2026-10-23 — Derived the common-cofactor and shared-label energy formulas,
  audited the varying-shift source, and isolated the mark-avoidance
  approximation floor. Goal remains unproved and active.
- 2026-10-23 — Proved the reflected marked Type I estimate on paper,
  retaining shared marking primes and all root-averaged errors. Moved
  its classical deduction to stage 2; Lean and signed Type II remain open.
- 2026-10-23 — Replayed the reflected signed moment chain and completed
  the actual marked prime root-average transfer at every fixed level
  below one. Recorded all averaged errors and the outstanding external
  zero-free proof closure. Goldbach and signed mark removal remain open.
- 2026-10-23 — Formalized exact prime-only RH–Goldbach bridges at the user's
  request. Paper proof, direct compile, and fourteen axiom checks passed. The same
  prime weights support an averaged RH criterion and a separate pointwise
  Goldbach criterion. Neither conjecture has been proved.
- 2026-10-23 — Derived the predecessor-mark Type I estimate and attacked its
  balanced term directly. Recorded the CRT compatibility, affine determinant,
  paid diagonal/near-slope contribution and exact unresolved far-slope sum.
  No new Lean certificate or scientific novelty claimed in this cycle.
- 2026-10-23 — Completed the requested twelve-programme dictionary and the
  actual-source damping, reflection and incidence bridges. Then proved and
  formalized damping reversal as Möbius parity and the exact finite two-scale
  Goldbach criterion. Leaf check and six closure audits passed; no analytic
  premise or placeholder. Recorded the stronger coefficient minorant separately
  as paper-only. The original Goldbach goal remains active and unproved.
- 2026-10-23 — Attacked a projective cancellation mechanism for the signed
  matrix. Proved its dense integral-return premise false and formalized the
  sharp positive return law, inversion classification and family budget.
  Direct leaf check and six closure audits passed without analytic premises.
  The missing strict inequality and signed covariance remain open.
