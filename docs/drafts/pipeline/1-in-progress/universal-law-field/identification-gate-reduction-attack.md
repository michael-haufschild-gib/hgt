# Identification-gate reduction attack (ULF-INV-9, branch ii typed)

- **ID:** ULF-INV-9-ATTACK
- **Stage:** 1-in-progress
- **Type:** TYPED ATTACK PLAN / REDUCTION TEMPLATE WITH NAMED LEMMA OBLIGATIONS
- **Source:** the open core of ULF-INV-9 (charter §7.10): type the interchange step so the
  corpus's cap laws apply
- **Status:** [TYPED] [TWO LEMMAS NAMED] [CIRCULARITY RISK RECORDED] [NOT RH] [NO LEAN]

## 1. The reduction template

Target no-go (branch ii of ULF-INV-9): uniform identification of the Hermitian extension with
tests' own prime+Gamma expressions, with modulus-only error control over a modulation-invariant
decisive class, implies a uniform-in-frequency prime bound of exactly the type convicted by the
corpus's cap 2 (`UniformDistanceAverage.dampedSize_ge_of_uniform`: any distance uniform on
\(|\tau|\le T\) is priced at the prime mass \(\sum_{p\le z}1/p\)).

Shape: modulating a test by \(e^{i\tau x}\) translates its spectral samples along the divisor;
a family of admissible pairs \((F_\tau,G_\tau)\), one per height window, with (a) polarization
bounded below and (b) prime-kernel modulus profile independent of \(\tau\), converts "uniform
identification with modulus-only error" into a uniform-in-\(\tau\) statement about damped
prime expressions — the object cap 2 prices. Conclusion of the template, if the lemmas hold:
the interchange step cannot be closed with modulus-only error control below the prime-mass
threshold; it must consume frequency-nonuniform (input-axis) arithmetic. That would prove the
last gate of the Weil-polarization lane is input-wall-grade, completing ULF-INV-9(ii).

## 2. Named lemma obligations

- **L1 (window supply).** For every height \(\tau\) large, there is an admissible Cauchy-packet
  pair anchored within \(O(1)\) of height \(\tau\) whose evaluation has \(\ell^2\)-norm bounded
  below uniformly in \(\tau\). Ingredients the corpus owns: Riemann–von Mangoldt counting
  (`mathlib-zero-counting-jensen-nevanlinna` layer) gives zeros within \(O(1)\) of every large
  height; the packet-evaluation norm needs a local divisor-mass lower bound — the risky half.
- **L2 (profile invariance).** The prime-side kernel of the modulated pair has modulus profile
  independent of \(\tau\) (modulation only rotates phases at each \(\log n\)). Expected from the
  explicit kernel `primeArchSourceRelativeTrace`; must be checked against its actual form, not
  assumed.

## 3. Risks, recorded before work

1. **Circularity risk (the serious one).** L1's uniform norm lower bound is a statement about
   the divisor's local \(\ell^2\) mass; if it secretly requires zero-density input of the same
   strength the no-go concludes is necessary, the reduction proves nothing. The attack must
   check whether RvM-average counting (unconditional, corpus-owned) suffices for L1, or whether
   L1 needs short-gap information (which would itself be wall-grade — and that outcome would
   still be informative: the reduction would relocate, not fail).
2. **Quantifier risk.** Cap 2 prices *distance-type* uniform statements; the reduction must land
   on exactly that type. If the uniform identification statement lands on a *size*-type bound
   instead, the applicable cap is the coefficient-free one, and the reduction needs the
   collided-pair form (`max_le_of_modulusOnly_bound`). Both landings are acceptable; a landing
   on neither kills the template.
3. **Class-size risk.** "Decisive" (rich enough to decide eigen-span positivity) must be strong
   enough to force the modulation orbit into the class; a class decisive but not
   modulation-invariant escapes the template, and the no-go would then hold only for the
   invariant subclass — still meaningful, scope reduced.

## 4. Exit conditions

- L1+L2 proved, template lands on a cap: ULF-INV-9(ii) becomes a stage-2 theorem — the last
  analytic gate of the lane is input-wall-grade, by reduction, unconditionally.
- L1 requires wall-grade input: record as relocation (the gate's hardness moves into L1);
  the no-go survives in conditional form; refreeze accordingly.
- Template lands on neither cap type: attack dies; record verdict and the surviving typing.

## Log

- 2026-08-09 — created: interchange step typed as a modulation-uniformity reduction onto the
  corpus's cap 2, with two named lemma obligations and three recorded risks; this executes the
  "first unprovable point" instruction of charter §7.10.

## 5. Progress — 2026-08-09 (same session): both lemmas green at schematic level

**L2 VERIFIED (source-level).** `primeArchSourceRelativeTrace z =
-i·[LSeries Λ at (1/2 + zi) - logDeriv archFactor(1/2 + zi)]`
(`XiRelativeResolventFlux.lean:84`). Under spectral translation z -> z + tau (the modulation
image), the prime component becomes sum_n Λ(n) n^{-1/2} e^{-i·tau·log n} e^{-iz·log n}: each
term rotates by a unimodular phase on the FIXED positive profile Λ(n)n^{-1/2} — exact modulus
invariance. The difference-quotient kernel (T(w̄)-T(z))/(z-w̄) translates coherently (denominator
invariant under joint translation). The archimedean component drifts by O(log tau) (Stirling),
which lands precisely in the frame's input-axis A·L normalization — typed, not a defect.

**L1 FEASIBLE without wall-grade input (schematic).** The circularity risk resolves favorably at
the mechanism level: the unconditional local zero count N(tau+1) - N(tau) ≍ log tau (classical
von Mangoldt/Backlund; corpus zero-counting/Jensen layer) supplies ≍ log tau divisor points
within distance 1 of every large height, giving the packet-evaluation norm² a lower bound
c·log tau — growing, not merely uniform. Caveat kept open: this is schematic against the
corpus's exact divisor-sampling weights (the square-summable quotient normalization); the
weight-level check is the remaining L1 obligation, but the mechanism is RvM-local, not
short-gap, so the serious circularity risk of §3.1 is retired.

**Remaining open core = the landing (risk 2 realized as predicted).** The produced uniform
statement is a damped Dirichlet SIZE bound (|sum Λ(n)n^{-1/2-i·tau}·weights| uniform in tau up
to O(log tau) drift), not literally a distance bound; the applicable corpus object is the
dampedSize floor half of the Perron layer rather than the distance half. The reduction's final
step is therefore: land the uniform size statement on `dampedSize_ge_of_uniform`'s hypothesis
shape or exhibit the collided-pair form. This is the single remaining obligation before
ULF-INV-9(ii) becomes a stage-2 theorem.

## 6. Landing plan — 2026-08-09: target hypothesis read in source; one derivation remains

`sq_le_prime_mass_of_uniform` (`Sieve/UniformDistanceAverage.lean:247`) requires exactly:
a bounded-by-1 sequence f and a level delta with
`forall t, |t| <= T -> delta <= sqrt(mulDistSqPair f (charFn t) (primesLE z))` — a uniform
pretentious-DISTANCE lower bound against the character family. The bridge from my uniform SIZE
statement to this shape is the Halász size<->distance dictionary, which the corpus already owns
(`route_e/multiplicative_euler_bound_distance_form`, `halasz_uniform_distance_final_form`):
smallness of a damped multiplicative expression at frequency tau IS a distance lower bound from
charFn tau.

Landing chain (each arrow corpus-owned except the first):
  error representation for the interchange defect (test's own prime expression minus packet
  limit, on the modulation orbit)
    -> uniform modulus-only control of the defect = uniform smallness of a damped multiplicative
       expression in tau                                     [REMAINING DERIVATION]
    -> uniform distance lower bound via the Halász dictionary [corpus]
    -> mulDistSqPair hypothesis of sq_le_prime_mass_of_uniform [read in source]
    -> delta^2 <= prime mass + 4*primeInvLogConst/T           [corpus cap]
    -> no modulus-only uniform identification below the prime-mass threshold: ULF-INV-9(ii).

The single remaining derivation is the error representation, which requires fixing the decisive
class concretely (candidate: the modulation orbit of one fixed non-core admissible test with
nonzero fibrewise mean; its interchange defect against the packet limit is then one explicit
conditionally convergent sum). All other links are read-in-source or corpus-owned. Obligations
outstanding: this derivation + the L1 weight-level check (§5).

## 7. Corrections from source — 2026-08-09: candidate class refuted; gate re-aimed

Two facts read in source overturn §6's candidate class:

1. `xiWeilEvaluationLp_mem_xiWeilCauchyHilbertSubspace` (`XiWeilCauchyCoreMultiplicity.lean:425`):
   EVERY admissible test's evaluation vector lies in the closed Cauchy core. The fibrewise
   mean-zero complement (nonzero iff some zero is multiple) contains no test evaluations at all —
   it is purely divisor-side. The "non-core test with nonzero fibrewise mean" of §6 does not
   exist; that candidate is refuted and withdrawn.
2. The corpus's identification family is broader than the attack assumed: the full sharp
   rectangular Guinand–Weil identity is formalized
   (`rectangularCorrectedXiWeilValue_eq_primePolarSource`,
   `XiGuinandWeilRectangularFullFormula.lean`), so prime+Gamma identification holds not only for
   finite Cauchy packets and their abstract l^2 limits but for the two-parameter rectangular
   family sharply.

RE-AIM. The decisive class for eigen-span positivity is the theta-eigenfunction family
(antidiagonal Gram; positivity on its span <=> RH + simplicity, unconditional). The gate
question, now exact: prime-sum identification for EIGEN-tests. Two branches, unchanged in type:
(i) establish it — extend the corpus's identity family to the eigenfunctions (their transforms
satisfy (alpha+z)F = -XiC z, so their prime side is one explicit object; group-3-adjacent
constructive work); or (ii) the wall no-go via the §6 landing chain, now aimed at the
eigen-family's modulation structure instead of a nonexistent mean-zero class. The L1
window-supply lemma survives re-aiming unchanged (it never referenced the mean-zero space);
L2 likewise. The error-representation derivation now targets: eigen-test prime expression minus
its packet-limit value — with the eigen-transform identity supplying the explicit form.

Method note, recorded: this is the second time in one session a candidate object was refuted by
reading one more module (first: the Hadamard/Schur rediscovery; now: the mean-zero class).
Corpus-first discipline continues to pay for itself; both refutations cost one grep each.

## 8. Branch decision — 2026-08-09: branch (i) is concretely closable-shaped; verifications executed

Source reads (`HedenmalmThetaEigenTransform.lean`): the transform identity
`(alpha+z)·F(z) = -XiC z` makes the eigen-test's divisor evaluation the FIBER DELTA at -alpha
(the removable quotient vanishes at every other zero; its value on the fiber is constant, so
the vector lies in the fiber-sum direction — consistent with core membership and with the
antidiagonal Gram, which this explains structurally). Hence the decisive class is exactly the
delta family, and the interchange defect D(alpha,beta) = [eigen-pair's own prime+Gamma
expression] - [antidiagonal Gram value] is one explicit object per pair of zeros.

Two admissibility verifications executed (arithmetic-level):

- **Decay rate:** the eigenfunction decays like e^{-|x|} at a zero (corpus:
  `norm_hedenmalmThetaEigen_mul_exp_le`, both-sided at zeros), i.e. u(log n) ~ n^{-1}, so the
  prime side sum_n Λ(n) n^{-1/2} u_alpha(log n) conj(u_beta(log n))-type converges ABSOLUTELY
  (rate 1 > 1/2). No conditional convergence remains for eigen-pairs: the interchange question
  for this class has no summability obstruction at all.
- **Strip coverage:** the machinery's hypothesis |alpha.im| < 1 holds UNCONDITIONALLY for every
  Xi zero (centered spectral coordinates put all zeros' imaginary parts in (-1/2, 1/2)).

CONSEQUENCE. Branch (i) — establishing the prime-sum identification for the eigen family — is a
bounded piece of constructive work with corpus machinery (the (18a) substrip decay bounds, the
Guinand-Weil assembly used for the rectangular family), not a wall. If it closes, the corpus's
unconditional "eigen-span positivity <=> RH + simplicity" transfers to actual prime-sum form:
a new exact group-3 producer with the interchange genuinely closed — the last analytic gate of
the Weil-polarization lane would be DONE, and the residual would be pure group-3 positivity,
which is the honest wall by the trichotomy. Branch (ii)'s no-go re-aims accordingly: it would
apply only to classes with genuine conditional convergence, i.e. NOT to the decisive class —
the wall-grade suspicion of ULF-INV-9 is likely FALSE for the decisive class and true only for
the broad algebra. Refreeze pending the branch-(i) derivation: the next cycle assembles the
archimedean term for eigen-pairs via the corpus's rectangular-family machinery.

Method note: the gate narrowed twice today by reading (packet closure covers all tests;
rectangular family already identified) and now shows a closable shape. The "wall" the memory
recorded as the lane's remaining gate appears, for the decisive class, to be a bounded
derivation — the third instance this session of the corpus being further along than its own
frontier notes.

## 9. Branch (i) assembly skeleton — 2026-08-09, typed against corpus lemmas

Goal: W(u_alpha, u_beta) = q_W(u_alpha, u_beta) for all pairs of Xi zeros, where W is the
eigen-pair's own (absolutely convergent) prime+Gamma expression and q_W the antidiagonal Gram.

Steps, each typed:

1. **Delta approximation, unconditional (new lemma-level observation).** The eigen-delta is
   constant on its multiplicity fiber, and single-anchor normalized Cauchy evaluation vectors
   have fiber-constant components; as the anchor approaches the reflected zero, the normalized
   vector converges in l^2 to the fiber-sum direction = the eigen-delta — REGARDLESS of
   simplicity. (Simplicity governs density of the whole core, not reachability of the
   fiber-constant directions; the multiplicity-annihilation theorem
   `xiWeilFiberSum_eq_zero_of_inner...` is exactly the complementary statement.) So the
   identification for the decisive class does not need simplicity — only the limit interchange.
2. **Packet-limit value.** By `tendsto_primeArchSource_packetSum_of_tendsto`, the prime sums of
   the approximating packets converge to q_W(u_alpha, u_beta).
3. **Residue-limit computation.** The packet prime expression for two single anchors is the
   difference quotient (T(b-bar) - T(a))/(a - b-bar) times normalizations; T is the resolvent
   trace with poles at divisor points (residues = multiplicities,
   `primeArchSourceRelativeTrace_eq_xiRelativeResolventTrace` on the overlap). The normalized
   limit as anchors approach the reflected zeros picks out residue data: cross pairs vanish
   (matching antidiagonality), diagonal pairs give the derivative-normalized residue. To prove:
   the two-variable limit exchange (anchor limits vs the tsum defining T) — this is the ONE
   genuinely analytic step; absolute convergence of the eigen side (rate 1 > 1/2, §8) and the
   (18a) substrip bounds are the dominating inputs.
4. **Own-expression identification.** The eigen-pair's own W: prime part
   sum_n Λ(n) n^{-1/2}(convolution of eigenfunctions at log n) — absolutely convergent;
   archimedean part = explicit convergent integral of logDeriv archFactor against the product of
   removable quotients ((18a) decay). Steps 2+3 give the packet route to the same value; step 3's
   limit exchange identifies the two. On completion: "eigen-span positivity <=> RH + simplicity"
   in genuine prime-sum form — the gate closed for the decisive class.

Remaining verification list (bounded): (a) the l^2 delta-approximation limit (step 1) against
the corpus's exact sampling weights; (b) the two-variable limit exchange (step 3) — dominated
convergence with (18a) + rate-1 decay; (c) assembly of the archimedean integral in the corpus's
normalization. No step requires input-axis arithmetic; ULF-INV-9's wall suspicion is expected
to die on the decisive class and will be recorded as such when (a)-(c) close.

## 10. Verification (b) attacked — 2026-08-09: route refinement, exchange bypassed

Direct attempt at the two-variable limit exchange exposed its real difficulty: the anchors leave
the far-right domain as they approach the divisor, so the termwise series representation of the
resolvent trace is unavailable at the limit — the exchange would need the full contour assembly
(the same weight of work as the corpus's rectangular FullFormula chain).

Better route, found in the corpus's own method notes (weil-polarization-layer-state, final
trick): **integrate the defining ODE against the distribution, not the solution against the
kernel.** The eigenfunctions satisfy (D + alpha) u_alpha = -k with k the theta cusp source, and
the corpus proved the transform identities by integrating the EQUATION against free modes — no
convolution theorem, no Fubini. Applied to the pairing: W(u_alpha, u_beta) — the eigen-pair's
own prime+Gamma expression — can be computed by integrating the two ODEs against the
explicit-formula distribution, converting the pairing into (i) boundary terms, vanishing by the
both-sided e^{-|x|} decay AT zeros, plus (ii) the theta-source pairings, which are corpus-owned
objects (the thetaCusp prime/theta identities). The anchor-limit route and its exchange are
bypassed entirely; step 3 of §9 is replaced by:

  3'. ODE-against-distribution assembly: W(u_alpha,u_beta) = boundary terms (vanish at zeros,
      rate-1 decay) + algebraic combination of theta-source prime pairings [corpus lookup
      required: the exact thetaCuspFullSource prime identity] + arch bookkeeping.

Updated verification list: (a) delta-approximation weights (unchanged); (b') the theta-source
prime-pairing lookup and the two integrations by parts with decay boundary terms (elementary,
corpus-aligned — replaces the hard exchange); (c) archimedean normalization (unchanged). The
load-bearing item is now a lookup-plus-integration-by-parts, not an interchange — consistent
with §8's finding that the decisive class has no summability obstruction. ULF-INV-9's wall
suspicion on the decisive class is one corpus lookup away from its recorded death.

## 11. Theta-source lookup executed — 2026-08-09: all assembly ingredients located

`ThetaCuspFinitePrimeSource.lean`: `thetaCuspFullSource x = tsum thetaCuspSourceTerm` (the
all-integer theta-cusp state, Gaussian-type terms with proved decay envelopes); the
finite-prime resolvent series `finitePrimeThetaCuspResolventSeries` with n^{-1/2}·logTranslate
structure; absolute convergence on the seed proved
(`summable_finitePrimeThetaCuspResolventSeries_seed`); and the exact source identity
"k_N = R_N(1/2)·a" in norm-convergent smooth-integer series form. The k-pairings the
ODE-against-distribution assembly needs are therefore corpus-owned, absolutely convergent
objects, and the prime side enters through exactly the n^{-1/2}-weighted log-translates the
eigen-pair series produces.

STATE OF BRANCH (i): every ingredient is located and verified to exist in source — the ODE and
transform identities (§8), the fiber-delta structure (§9.1), the packet-limit theorem (§9.2),
the bypass device (§10), and now the source identity and its summability layer. What remains is
the derivation itself: the two integrations by parts with boundary terms killed by rate-1 decay
at zeros, the reduction of the cross pairings to the theta-source series, and the archimedean
normalization — a bounded multi-page paper proof against exact corpus normalizations, the
natural next major cycle, with Lean certification to follow in a Lean-enabled session. On its
completion: ULF-INV-9's wall suspicion dies on the decisive class (recorded verdict), and the
positive survivor is the corpus's eigen-span equivalence in genuine prime-sum form — the
Weil-polarization lane's last analytic gate closed at paper level.
