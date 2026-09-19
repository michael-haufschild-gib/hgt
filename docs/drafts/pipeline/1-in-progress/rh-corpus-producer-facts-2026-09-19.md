# RH producer facts — this task only

Evidence levels: **Lean checked** means a successful scratch invocation in this task;
**source inspected** means the exact existing declaration/proof was read; **paper** means
an argument not yet kernel-checked here. No proof or falsification of RH has been obtained.

| Fact / no-go | Evidence | Meaning for the whole route |
| --- | --- | --- |
| Signed four-point pairing matches the raw Euler monomial, but the singleton does not. | **Lean checked:** `/tmp/hgt-euler-signed-pairing-producer-test.lean`; standard Lean axioms. | Direct vacuum pairing cannot represent the full arithmetic source. The even shared-sign moment survives, already in the corpus. |
| No analytic square root of `(s−1)ζ(s)/s²` exists throughout `Re(s)>0`. | **Lean checked:** `/tmp/hgt-pole-cleared-root-parity-test.lean`; actual odd-order critical-line zero; standard Lean axioms. | Excludes that larger domain. Does not exclude the required signed root on `Re(s)>1/2`. |
| Existing cusp root extension uses zero-freeness of its domain before constructing the root. | **Source inspected:** `XiSymmetricLittlewoodZeroFreeCuspDyadicRoots.lean`, extension proof. | Cannot supply continuation through the remaining strip independently of the missing zero-free law. |
| Paired eta continuation `H_h` is defined as an entire factor times `zetaPoleUnit`. | **Source inspected:** `PairedEtaRootContinuationBoundary.lean`, `J_h`, `H_h`, convergence proofs. | Its continuation is not an independent continuation of the arithmetic root. |
| The inspected negative full-Xi Hankel theorem assumes nonreal folded divisor nodes; Gaussian negativity outside the completed aperture is an implication, not existence. | **Source inspected:** `XiShiftedTraceHankelMultiOrbitInertia.lean:95`; `XiPolynomialGaussianExplicitFormula.lean:473`. | Neither constructs an RH counterexample. More such detection theorems would leave existence unpaid. |
| Existing outer-node persistence and adjacent-history supply require a positive containing Hankel block. | **Source inspected:** `FiniteExtremeNodePersistence.lean:26`; `XiShiftedCanonicalAdmissionAdjacentHistoryBudget.lean:57`. | They cannot inductively establish that same next block without an independent source sign law. |
| The actual adjacent-amplitude correction is added as `A² C`; its first derivative vanishes at each current root. | **Source inspected:** `XiShiftedCanonicalAdmissionVacuumFreeHardEdgeSourceCapacity.lean:45–174`. | It preserves the old transverse jet. A quadratic correction is not automatically a two-point interlacing completion that repairs boundary orientation. |
| Even strictly positive interlacing roots do not force this correction to have real roots. For `A=X−1/16`, `B=(X−1/32)(X−1/2)`, it is `−4(x−15/64)²−269/1024<0`. | **Lean checked:** `literal_quadratic_completion_positive_interlacing_counterexample` in `/tmp/hgt-quadratic-completion-test.lean`; exit 0; standard Lean axioms only. | Rejects the generic two-point-completion transfer. Does not identify this pair with actual Xi admissions or decide their signs. The existing exact transverse-jet survivor remains valid and was axiom-audited. |
| Full Born–Witten Ward moments are positive scalar multiples of raw theta moments; the first atom's superpotential is negative at the endpoint. | **Source inspected:** `PrimeArchThetaBornWittenRobinSteinWard.lean`, exact Ward recurrence, endpoint sign, full-source identity. | This supplies raw moment positivity, not positivity of the logarithmic cumulant Hankel form. Replacing the signed integrand by a positive measure is unjustified. |
| The literal two-prime Möbius–Riesz cell changes sign at `√M=√(np)+√(nq)−√n`: positive strictly between `√n` and that wall, negative beyond it. | **Lean checked:** `literal_primeCell_sign_wall` in `/tmp/hgt-prime-riesz-cancellation-test.lean`; standard Lean axioms. | One-prime cancellation cannot be iterated as a nonnegative-cell induction. The exact positive interval is the surviving source sign law. |
| The complete signed tail obeys `T(kM,kn)=√k T(M,n)` and has `T(2n,n)>0`, `T(6n,n)<0` for every `n≥1`. | **Lean checked:** `tail_dilate`, `literal_tail_both_signs_on_every_scale` in the same scratch file; exact square-root identities, no numerical enclosures. | Mixed signs persist at every scale; they are not an artifact of selecting a four-term subcell. |
| The actual source channel `primeFreeDivisorIncrement 1 * T(6,1)` is strictly negative. | **Lean checked:** `literal_primeFreeDivisor_source_channel_negative`; `primeFreeDivisorIncrement 1=2γ−1>0`. | Termwise positivity of the completed source pairing is false. These results leave its joint signed bound, hence RH, open. |
| Literal divisor-product blocks sum to the completed `Λ−1+2γδ₁` atom, and their full Riesz window equals the complete Abel source. | **Source inspected:** `primeFreeDivisorIncrement_mobius_convolution_eq_atom`, `increment_rieszTail_eq_completedPrimePolarGamma_window`. | Exact convolution already supplies this cancellation identity; repeating it does not supply signed global control. |
| Completing each product block to zero and marking its original entries gives total `(0,S(M))`, where `S(M)` is the complete source. | **Paper:** explicit two-coordinate calculation in this task's producer card, using the inspected convolution identity. | The tested zero-sum ordering lift retains the unknown source in its marked coordinate. Unmarked prefix control loses the required readout. No conclusion about the open complete-prime-path conjecture follows. |
| A finite sign law preserving each literal prime coefficient in expectation has every prime sign `−1` on every positive-weight outcome. | **Paper:** `E ε_p=-1`, `ε_p+1≥0`, hence `ε_p=-1` on support. | This coefficientwise faithful randomization cannot supply the free signs in the tested discrepancy transfer. Other randomized constructions are not excluded. |
| No uniform quadratic budget controls both the literal half-prime head and the completed source; no fixed multiple of the original diagonal controls both either. | **Source inspected:** `not_uniform_halfPrimeHead_and_total_quadratic`, `not_uniform_halfPrimeHead_and_total_diagonal` in `MobiusDivisorLatePrimeCompensation.lean`. | A metric construction that controls every partial selection would contradict an existing actual-source theorem. A path-specific construction must avoid the forbidden intermediate states; the complete-path conjecture is not refuted. |
| Actual unused quotient-2/7/14 primes simultaneously neutralize the current head and prime-two fibre. A square-root-sized ordered batch ends with pair energy at most `R²M`, releases both original receiving squares plus `M` from raw energy, and keeps every prefix below `Q(P)+R²M`. | **Lean checked:** `eventually_exists_mobiusDivisorReceivingPairNeutralization` and the premise-free fixed-core capstone `eventually_exists_mobiusDivisorInitialReceivingPairNeutralization`; `/tmp/hgt-two-receiving-neutralization.lean`, exit 0 without warnings. | Produces a new actual state and its complete finite path. Other fibres, growing quotient ranges, renewed windows, and complete exhaustion remain uncontrolled. |
| The normalized Abel source's subpower-growth criterion is already equivalent to RH. Prescribed stream repair already retains all prefixes and uses linear helper cost plus one square-root reserve payment. | **Source inspected:** `CCMFUSuzukiMobiusDivisorAbelSubpower.lean` and `MobiusDivisorPrescribedStreamRepair.lean`. | Adding either receiver or prefix bookkeeping again would not close the missing source exhaustion. |
| Actual distinct quotient-2/11/15 primes produce inherited covariance at least `(g*k-J)*M` at every prefix, with fixed `g>0`, bounded signed displacement `H√M`, and a uniform quadratic successor-energy ceiling. All preparation subsets share that ceiling. | **Lean checked:** `eventually_exists_mobiusDivisorPositiveDebtBatches`, `/tmp/hgt-positive-debt-batches.lean`, exit 0 without warnings. Constants are fixed before arbitrary batch length; actual windows and fixed core are supplied unconditionally. | Closes the positive real circuit → actual prime batch gap. Reduces the entire external prime-two cost, including inherited paired fibres. Does not supply sufficient capacity for arbitrary quadratic debt, renewed windows, growing quotient fields, or exhaustive processing. |

## Recent-paper transfer facts

Broad arXiv queries used `renewal`, `reflection`, `rigidity`, `interlacing`, and `gluing`,
preferring January–September 2026. Publication/version dates were checked on opened papers.

- [Jordaan–Kumar, April/August 2026](https://arxiv.org/html/2604.25692v2),
  Theorem 2.1 and §3: mixed recurrence plus real simple zeros and existing interlacing
  produces completed interlacing and positive-residue square identities. **Route effect:**
  no direct removal of the Xi positive-block premise; the source correction needs its own
  real-root and recurrence verification.
- [Wu, May 2026 submission](https://arxiv.org/html/2605.00633v1), Lemmas 4.1–4.2:
  periodic separating arcs and their constructed adjoints force bounded-step descent of
  integer intersection complexity. **Route effect:** finite accounting alone is weaker;
  no corresponding source operation or integer descent has been constructed for Xi.
- [Ding–Ge–Li, 2026](https://arxiv.org/html/2609.20180v1), Proposition 3.7 and
  Lemmas 3.8–3.9: partner spectra, a common closed-form domain, and an exact signed
  potential difference give spectral comparison. **Route effect:** no transfer without
  identifying actual arithmetic operators, their domains, and that signed difference.
- [Nguyen–Phan–Kalagnanam, March 2026 submission](https://arxiv.org/html/2604.00260v1),
  paired-reversal expansion: reversal cancels the order-dependent second-order term;
  a higher-order remainder remains. **Route effect:** this does not identify or cancel
  the complete arithmetic boundary-excursion current.
- [Akbas–Sra, September 2026 submission](https://arxiv.org/html/2609.20785v1),
  Theorem A.5: simultaneous sum/variance splitting supplies an unsigned prefix
  bound for zero-total families; the general-family proof retains the total,
  and its signed conclusion selects signs. **Route effect:** the explicit marked
  arithmetic lift retains `S(M)`; preserving prime coefficients fixes all prime
  signs. Neither tested transfer produces the missing source control.
- [Liang, August 2026 submission](https://arxiv.org/html/2608.11986v1),
  Theorem 1.1, Lemma 2.1 and §2.2: positive left/right eigenvectors of a finite
  irreducible Metzler operator produce the profile/corrector saddle; strict
  convexity uses positive paired edge weights. **Route effect:** the literal
  irreversible merger has a missing reverse edge. This paper does not directly
  furnish its source-preserving metric, and a uniform metric controlling every
  partial selection is already excluded by the inspected source theorem.
- [Fadin–El Housni–Topaloglu, August 2026](https://arxiv.org/html/2608.14275v1),
  Lemma 6.1 and §6.1, found through the broad `inventory` query: weak
  substitutability permits marginal-preserving restriction to available
  products; the policy still consumes supplied finite stock. **Route effect:**
  this does not renew prime-window capacity or produce missing source
  directions after exhaustion. No such substitutability law for the actual
  arithmetic packets was established here.
- [Beliaev–Hegde, June 2026](https://arxiv.org/html/2606.15630v1),
  introduction, found through the broad `excursion` query: the proposed
  fluctuation scaling starts from a stationary random measure and specified
  low-frequency spectral behavior. **Route effect:** no identification of
  the deterministic completed source with such a measure was established;
  this paper supplies no premise for the actual-prime construction.

## Joint actual-prime producer

- `eventually_exists_mobiusDivisorJointDebtNeutralization` passed the full
  scratch kernel check. One distinct quotient-2/11/15 batch of length
  `ceil(A*sqrt M)` neutralizes the actual head/{2} receiving pair, releases
  both initial squares plus M, and lowers complete external prime-two cost
  by at least `M*sqrt M`. Every raw-energy prefix is at most `Q(P0)+R^2*M`.
  Fixed-core preparation is supplied without external hypotheses.
- Mechanism: start inward return at minus the normalized receiving pair;
  sum the positive affine covariance certificate. Packet-square reserve
  dominates covariance by `(x-y)^2>=0`, so the same primes pay both costs.
  **Route effect:** receiving repair and inherited-debt removal are compatible
  actual operations. This does not produce renewed windows, growing-field
  coverage, or a complete order for every cutoff.
- [Aliabadi, May 2026](https://arxiv.org/html/2605.11054v1), Lemmas 2.1–2.2,
  found through broad `paving`: Johnson-stable excluded sets give basis
  exchange; a vertex-transitive regular cover gives an entropy bound.
  **Route effect:** no basis-exchange or vertex-transitivity law was
  established for admissible arithmetic packets. Neither paper hypothesis
  was imported into the joint producer.

## Changing-core all-cutoff production

- `exists_mobiusDivisorUniformReserveHistory` passed scratch Lean without
  warnings. It constructs fresh prime pairs and cores of cardinality 2n,
  starting empty. Every even and odd state has
  `Q_M(state) <= Q_M(empty)+M^2` for all n and all integer M. Each pair after
  the first releases `c_n*M^2` eventually in M, with `c_n>0`.
- The complete prime correlation is supported on `p <= M/r`; the existing
  absolute tail theorem therefore pays a prime insertion by `K(P)*M^2/p`
  at every cutoff. Choose source-reserve pairs beyond the changing core's
  threshold and charge them to a telescoping budget.
  **Route effect:** an infinite changing core and one all-cutoff budget are
  compatible with actual reserve production. Exhaustion is still independent:
  this construction selects sparse primes and does not include an arbitrary
  omitted small prime. No RH conclusion follows.
- Broad `resampling` search found [Finke et al., June/August 2026](https://arxiv.org/html/2606.25603v1), §§1.2 and 2.1. Their construction
  preserves a target measure through ancestor sampling and adjusted weights;
  they expressly separate validity from convergence rates. No law admitting
  repeated prime ancestors or changed arithmetic coefficients was proved here.
  The history constructor uses neither such resampling nor a paper assumption.

## Evidence limits

Corpus retrieval includes unrestricted deep/method lanes (`source_arguments`, `proof_ideas`,
`ingredient_sets`). Completed queries still report incomplete source/semantic/compiler
coverage. This fact log does not claim exhaustive reading or absence of an unknown producer.
Numerical experiments were not used. Other tasks' fact logs are untouched.
The quadratic-completion deep/method query timed out at its judging stage; its available
results were inspected. No completeness conclusion follows from that partial search.

The prime-pairing results now live in
[`CCMFUSuzukiMobiusRieszPrimeCellSign.lean`](../../../../formal/GaloisForLFunctions/RHTower/CCMFUSuzukiMobiusRieszPrimeCellSign.lean),
namespace `RHTower.MobiusRieszCancellation`. The module is wired into `RHTower.lean`.
Its named `lake build` passed; cached dependencies replayed existing warnings. The new module
and its combined scratch check emitted no warnings. A separate import-only scratch audit
confirmed the standard three axioms for all seven public theorems. No new axioms were added.

Latest `scripts/formal_tools.py lint` returned exit 1 for unrelated unreachable HB
angular/Peierls modules in the shared tree; it reported no error for the new module.
Indexes were regenerated. No full or umbrella build ran.

The coupled receiving-pair producer now lives in
[`MobiusDivisorReceivingPairNeutralization.lean`](../../../../formal/GaloisForLFunctions/RHTower/MobiusDivisorReceivingPairNeutralization.lean).
Its byte-identical named-module Lake audit passed in an isolated package
with existing dependency oleans; only the new leaf compiled. Both public
theorems passed the external import/axiom audit, using only `propext`,
`Classical.choice`, and `Quot.sound`. The unconditional capstone supplies
its own fixed-core preparation bound. The module is wired once, its required
olean and ilean are cached, and indexes were refreshed. Current global
lint reports the same 28 unrelated unreachable Hawking/BM modules, with no
error naming this leaf. RH remains open.

The actual positive-covariance producer is now in
[`MobiusDivisorPositiveDebtBatches.lean`](../../../../formal/GaloisForLFunctions/RHTower/MobiusDivisorPositiveDebtBatches.lean).
Its byte-identical named-module audit passed with cached dependencies
(109 seconds, only this leaf compiled). The separate import/axiom check
passed with exactly `propext`, `Classical.choice`, and `Quot.sound`.
Required oleans are cached, the umbrella import is unique, and indexes
are refreshed. Global lint's 28 unrelated unreachable-module errors are
identical to the preceding audit; none names this producer. No full or
umbrella build ran. This result supplies actual finite debt-removing batches,
not the remaining complete prime order.

The joint producer in the same leaf passed its byte-identical named-module
Lake audit (171 seconds; only this leaf compiled). The external import and
axiom audit exited 0 for both public theorems, with only `propext`,
`Classical.choice`, and `Quot.sound`. New oleans are cached, the umbrella
import remains unique, and generated indexes were refreshed. Global lint
has exactly the same 28 unrelated errors as before. No full or umbrella
build ran. The result is an unconditional finite producer; RH remains open.

`MobiusDivisorUniformReserveHistory.lean` passed the byte-identical named
leaf build (53 seconds) and the external import/axiom audit. Its sole public
producer uses only `propext`, `Classical.choice`, and `Quot.sound`. The olean
and ilean are cached, the umbrella import is unique, and indexes refreshed.
Global lint now has 29 unrelated unreachable modules (the preceding 28 plus
`MaassFiniteDeckCuspidalDirichlet`); none names this leaf. No full or umbrella
build ran. Its uniform history is sparse, so exhaustion and RH remain open.

The new initial-pair producer is closed in scratch Lean:
`exists_mobiusDivisorUniversalInitialPrimePartners` constructs q(n)>n, prime,
with every subset of {p,q(n)} below the original complete diagonal for every
prime p and every integer cutoff. Its private separation argument has no
parent-quotient condition: either both parent channels share the positive
unit mean, or the distant child channels vanish. Combining this with the
existing two-large-prime theorem makes the partner threshold independent of p.
This removes the finite small-prime exclusion for initial pairs; it supplies
no continuation from a changed core. The byte-identical named-module audit
passed (70 seconds, only the leaf compiled). External import/axiom and library
name probes passed: `propext`, `Classical.choice`, `Quot.sound` only. Olean
and ilean are cached; umbrella import is unique; index refresh passed. Global
lint reports 28 unrelated unreachable modules, with no new error (the earlier
Maass reachability error was resolved elsewhere). No full/umbrella build ran.

Broad 2026 arXiv search found [Hénard's avalanche paper](https://arxiv.org/html/2608.10992v1).
Its regeneration law uses independent exponential refreshes and interval
range. No corresponding law for the arithmetic source has been established;
its branching/tail mechanism supplies no Lean premise or producer here.

`exists_mobiusDivisorCommonReserveProducer` passes scratch Lean. For every
finite prime cutoff N and epsilon>0 it produces a fresh prime a>N and
arbitrarily large actual fresh pairs p<q, a<p. At every integer M, all three
prefixes cost at most epsilon*M^2 above Q(P), simultaneously for every
P subset of the primes below N. One common positive eventual quadratic
reserve from p,q holds in every nonempty prepared state P+a, regardless
of parity. Empty P is included in the cost guarantee and explicitly excluded
from the strict reserve guarantee.

The source mechanism is the shared interior negative band near a, inherited
from every W_P(1)>0. This avoids the previously proved far-ratio parity
incompatibility. It does not compare the two states' reserve sizes, so a
prescribed prime's debt need not decrease. Preparation cost is paid, but
exhaustion and payment of arbitrary existing debt remain open. The byte-identical
named leaf audit passed (52 seconds, only this leaf compiled). External import,
axiom, and library-name audits passed; the producer uses only `propext`,
`Classical.choice`, `Quot.sound`. Olean and ilean are cached, the umbrella import
is unique, and index generation passed. Global lint reports 29 unrelated
unreachable modules (previous 28 plus `CCMRestrictedWeilPolarSymmetricBoundaryRenormalization`),
with no error naming this leaf. No full or umbrella build ran.

The simultaneous reserve also lowers every member of a fixed finite successor
family. It does not lower the full successor envelope: primes between the
fixed field cutoff N and the later physical cutoff M are not quantified in
that family. Setting N=M is invalid because the produced preparation prime
lies above N and strict release holds only on a later parent tail. This
quantifier gap must be closed by a source construction, not diagonalization.

Broad searches for echo, reciprocity, and refocusing led to
[Bauermeister, 2605.21871v1](https://arxiv.org/html/2605.21871v1).
Its distinction between refocusing and strong refocusing is realized by
changing a Lorentzian metric. No freedom to make such changes to the fixed
arithmetic source has been established; no theorem from that paper enters
the common-reserve proof.

The p=1 physical correlation theorem applies without primality: its primitive
is twice the head primitive and its density is halved. This identifies the
complete fixed-core energy with rho(P)*W_P(1). For two original states with
positive coefficient debt, continuity and the insertion renewal produce a
negative weighted difference of dilation means after a common sufficiently
large prime. The two inserted densities have the same factor a/(a+1), so
this sign compares actual pair reserves. This resolves the missing relative
sign; it does not make preparation itself decrease debt or pay the whole debt.
The full public producer passes scratch Lean and its byte-identical named
leaf audit (30 seconds, no warnings). It gives an unconditional alternative:
nonpositive original coefficient debt, or arbitrary-distance preparations and
arbitrary-distance actual pairs that release both energies and strictly
reduce their difference on a common eventual tail. Both original states have
the epsilon*M^2 all-cutoff budget at every prefix. The axiom output lists
only `propext`, `Classical.choice`, `Quot.sound`. The final external import,
axiom, and library-name probes passed without warnings. Polymorphic `have :=
@Name` probes require explicit universe levels on this toolchain.
Caches, the unique umbrella import, and the index are installed. Global lint
has 28 unrelated unreachable modules and no error in this producer.

Broad 2026 searches for synchronization and metastability found
[Bund–Leshem–Medina, 2604.17285v1](https://arxiv.org/html/2604.17285v1).
Section 8.2 explicitly enumerates the finite resolution set, simulates each
stable input, and combines outputs by a containing multiplexer. That bounded
finite construction gives no arithmetic rule for uniform growing-core debt
payment. No computational experiment or premise from the paper was used.

The private two-cluster scratch now checks actual prime supply in the
windows (T,(1+eta)T] and (rT,(1+eta)rT], with equal cardinality
ceil(s*sqrt(T)), together with inverse-square-root weight bounds. Its
finite-product exponential error is at most exp(sum norms)*sum norm-squares;
the majorant has no exponential cardinality loss. These are ingredients of
the still-open complete coefficient-payment producer, not a completed result.
The source's positive first block is already unconditional in
DivisorContinuousUnitMoment. Integer-period integration in mathlib allows
log(T)=2*pi*n/d, so a positive periodic gate can replace the proposed full
Bessel averaging step; that sign-transfer proof remains open.

The broad latest-first arXiv search for homogenization also exposed
[Arulseelan, 2609.20718v1](https://arxiv.org/html/2609.20718v1).
Theorem 4.4 produces orthogonal projection dilations using a copy supply,
but explicitly requires every finite input subsum to have norm at most 1/2.
Its rotation lemma also requires x+y≤E before constructing the next
contraction. Thus this mechanism does not supply the missing bounded
arithmetic preparation budget; no premise from it enters the prime proof.

`exists_mobiusDivisorInheritedPrimeInsertionProducer` is closed in Lean:
every inherited nonempty finite prime core P and missing prime r admit actual
fresh S beyond any bound with E(P union S+r)<E(P union S), plus a positive
quadratic release on one common tail of actual integer cutoffs. Two shrinking
prime windows, exact integer-period gates and the strict amplitude gap
sqrt(1+alpha^2)<1+alpha force the complete Mellin cosine integral positive.
Actual Euler products have a global bound; their squared-norm errors converge
pointwise to zero, so dominated convergence transfers the full integral sign.
No Bessel averaging, numerical experiment, source sign premise or added axiom
is used. Updated named leaf audit: 106 seconds; external axiom/name probe: only
propext, Classical.choice, Quot.sound. Cache, unique umbrella import and index
are installed; 28 unrelated global lint reachability errors remain.

This preserves arbitrary inherited P, unlike the prior complementary-core
field construction. It does not prove E(P union S+r)≤E(P), a uniform
preparation budget across changing cores, or exhaustive all-cutoff coverage.

`exists_mobiusDivisorBudgetedInheritedPrimeInsertionProducer` now strengthens
the actual producer: one K(P,r)>0 is chosen before the helper-distance bound B;
every T⊆S and every integer M satisfy E_M(P union T)≤K*M^2 and
E_M(P union T+r)≤K*M^2. Strict coefficient and eventual quadratic release are
preserved. All helpers are actual fresh primes; the original public producer
retains its original statement. The discrete proof retains both quotient
endpoints and all labels. Its private transport is K -> K*(1+4/sqrt(p));
induction gives (9/25)*exp(4*sum 1/sqrt(p)) at every cutoff. The cluster's
bounded total inverse-square-root mass makes K independent of distance and
helper cardinality. Both public axiom audits contain only the standard three
axioms; regular caches, unique umbrella import and index are updated.

K still depends on the inherited P and prescribed r. Neither this budget nor
favorable marginal release proves combined preparation-and-insertion energy
is below the original inherited energy. The next source test uses the exact
head-insertion identity in MobiusDivisorDilationMeanRenewal and the exact
density/diagonal identity in MobiusDivisorPrescribedDebtReserveProducer.
No impossibility theorem for combined payment has yet been checked.
