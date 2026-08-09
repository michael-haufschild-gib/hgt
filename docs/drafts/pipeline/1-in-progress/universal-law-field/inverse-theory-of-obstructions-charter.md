# Inverse theory of obstructions — field charter

- **ID:** ULF-INV-0
- **Stage:** 1-in-progress
- **Type:** FIELD CHARTER / RECHARTER OF THE UNIVERSAL-LAW PROGRAM
- **Source:** user directive 2026-08-09 (go above the routes; find the theory the no-gos point to)
- **Claim:** The corpus's certified no-gos, read together, are not failures of routes but a
  partial axiomatic specification of one missing mathematical object; the field's work is to
  extract that specification as proved necessity theorems, calibrate it against the three worlds
  where RH-analogues are theorems or sharp open problems, and prove rigidity: what the
  specification forces, independently of existence.
- **Status:** [FIELD CHARTER] [N1 PROVED] [CALIBRATION TABLE FIRST PASS]
  [RIGIDITY LOCATED IN-CORPUS] [NEXT CONJECTURE FROZEN] [NOT RH] [NO LEAN]

## 1. Method (the Weil-specification move)

Do not attack RH and do not re-enter routes. Treat every machine-checked no-go as a **necessity
clause** about any theory that could close the positivity wall, prove each clause as an
unconditional theorem ("any object admitting the excluded operation contradicts corpus theorem
X"), and study the resulting axiom system: consistency (models in the solvable worlds), rigidity
(what the axioms force), and discriminating consequences (what they predict before existence).
Historical template: Weil cohomology — specified by the Lefschetz argument and Serre's
coefficient no-go years before étale construction; the no-go located the theory.

## 2. The specification, first extraction

| axiom | content | necessity source | status |
|---|---|---|---|
| N1 | the pairing cannot factor through multiplicative regularization of prime moment data: such limits are constant across Mertens-normal Beurling systems and zero-blind | ULF-INV-1 (proved, this session) inverting `tendsto_mul_regularized` | **proved** |
| N2 | the object has structure invisible to Hankel/moment coordinates: within linear block combinations and entrywise normalizations of log-jet Grams, finite ⊕ positive ⊕ Hankel is impossible, and the no-defect escape is Hamburger-circular; a positive geometric truncation (indicator/region) is required and regions do not exist in moment coordinates | producer-map §§15,17,20–22 (Lean-backed) | corpus-proved; needs the categorical restatement |
| N3 | the theory must contain an upper-bound engine of trace type: RH is an upper bound on a count; all corpus engines bound below; zero-density moment methods cap at (2−2σ)(2σ−1); in the solved worlds the upper bound comes from finite positive traces (count ≤ trace) | lane-elimination derivation (W5) + Selberg/Deligne parents | corpus-derived; scope = corpus engine list |
| N4 | systole constraint: any trivializing normalizer pays \|E′(0)/E(0)\| ≥ (log 2)/2; the length spectrum of the arithmetic flow starts at log 2 | `PrimeIsingTreeCentralMassFloorLaw` | corpus-proved; geometric reading to be made exact |
| N5 | cusp axiom: the archimedean-prime corner is noncompact; the trace must be relative/truncated, and by N2 the truncation must be geometrically positive, not spectrally subtractive | `archimedeanPrimeEulerQuadraticCorner_not_isCompactOperator` + §§20–22 | corpus-proved; reading to be made exact |

Each "reading to be made exact" is a work item: state the geometric clause so that the corpus
theorem is literally its contrapositive, not an analogy.

## 3. Three-world calibration (first pass; each row checkable, to be deepened)

| world | space exists? | RH-analogue | what carries positivity | which axioms bite |
|---|---|---|---|---|
| 𝔽_q varieties (Deligne) | yes | **theorem** | duality/purity + tensor-power (family) amplification | all of N1–N3 satisfied via cohomology; no cusp |
| finite graphs (Ihara) | yes (the graph; universal cover = tree) | can **fail** (non-Ramanujan) | when true: spectral comparison with the universal cover | trilemma false (finite dimension); shows existence of a space is NOT sufficient — polarization is the load-bearing part |
| Selberg/Maass (Γ\ℍ) | yes, fully explicit | λ₁ ≥ 1/4 **open ~60 years**; progress (3/16 → Kim–Sarnak) only via functorial/family amplification | self-adjointness gives positivity of the Laplacian, but not the eigenvalue bound | N5 present (cusps, Eisenstein); shows even space + positivity + trace formula ≠ RH-analogue without amplification or purity |

Calibration conclusions (these are the field-level findings of this pass):

1. **Existence of a space is not the target.** Graphs and Γ\ℍ have the space and can still fail
   or stay open. The load-bearing structures in every solved or advanced case are
   **polarization/purity** and **amplification in families** — never single-object analysis.
2. The corpus already contains the rigidity half: its Deninger layer proves the weight-one
   polarization axioms are **equivalent** to Re = 1/2 (group 3 of the trichotomy). So the
   metatheorem "specification ⟹ RH-grade positivity" exists in-corpus for the polarization
   clause; the entire problem is pushed into: *where can a polarization come from?* The axioms
   N1–N5 are constraints on exactly that question — this is what distinguishes the inverse
   theory from a restatement.
3. The graph world supplies the dictionary entry for the corpus's one live object: the
   **UV model plays the role of the universal cover** (the tree), whose spectral band forces
   Ramanujan; N5 says the arithmetic cover, unlike the tree comparison, cannot be reached
   trace-classically — the comparison must be resolvent/relative.

## 4. Frozen next conjecture (ULF-INV-2): the amplification gap

> The corpus's certified caps are single-object statements, and their hypotheses **fail** for
> family/tensor-amplified engines: the coefficient-free cap (instantiation at the constant
> sequence), the uniform-distance cap (single-frequency escape is already noted in-corpus), and
> the (2−2σ)(2σ−1) moment ceiling are each provably inapplicable to an engine that couples a
> positive family average with a duality constraint. Conversely, no corpus no-go closes the
> amplified class.

`[OPEN CORE]` Prove, cap by cap, either (i) an exact theorem that the cap's hypothesis set
excludes family-amplified engines (locating the escape hatch the corpus leaves open — the first
corpus-derived *positive* pointer, since every solved world used exactly this hatch), or (ii)
an extension of the cap to the amplified class (a new wall, publishable as such). Either outcome
is new knowledge; the corpus's Selberg-class degree-2 layer (conductor 1 done, 2–4 live) is the
in-corpus amplification front to test against. First unprovable point: a definition of
"family-amplified engine" tight enough to be theorem-bearing and wide enough to contain
Kim–Sarnak-shaped mechanisms.

## 5. Anti-theatre gate for this charter

Reject the recharter if: the necessity axioms remain paraphrases (each must be stated so the
corpus theorem is its exact contrapositive); the calibration rows stay tables instead of becoming
exact statements with proofs or citations checked lane-deep; ULF-INV-2 resolves into pure
classification with no engine-shaped consequence; or six months of cycles produce only
specification and no rigidity/consistency theorem.

## Log

- 2026-08-09 — chartered after user directive; N1 extracted and proved (ULF-INV-1); calibration
  first pass recorded with its two conclusions (polarization+amplification are load-bearing;
  UV model = universal cover); ULF-INV-2 frozen.

## 6. ULF-INV-2 opening move (executed, to be hardened next cycle)

The escape hatch is already witnessed inside the corpus. The coefficient-free cap quantifies over
bounds valid for EVERY bounded completely multiplicative g separately; the de la Vallée Poussin
3-4-1 engine — formalized in-corpus with explicit constant (`zeta-three-four-one` layer) — does
not have that form: its input is a coupled positivity identity across the power family
{g^0, g^1, g^2} (a nonnegative trigonometric polynomial), not a per-g majorant. So the cap's
hypothesis class provably excludes it, and its output (the classical zero-free region) is exactly
the historical instance of an amplified engine beating every single-test bound. The corpus's own
ZFR-exponent memories then locate the NEXT cap: trig-polynomial amplification is itself bounded
by the c/log t barrier, escaped historically only by higher amplification types (Vinogradov
bilinear structure; Guth-Maynard). Work items: (1) state and prove the exclusion "coupled
positivity identities are not in the cap's hypothesis class" against the corpus's formal cap
statement (read `CoefficientFreeCap` lane-deep first); (2) define amplification degree so that
the corpus caps become fixed-degree theorems; (3) attempt the degree-1 cap (the exact barrier of
the VP family) as the first new wall theorem of the inverse theory, checking the optimal-constant
literature (Kondratyev; Mossinghoff-Trudgian school) before claiming anything.

## 7. ULF-INV-4 literature audit outcome, and the exact axiom restatements

### 7.1 Audit outcome (2026-08-09)

The degree-1 barrier is occupied: it is Landau's extremal problem for nonnegative cosine
polynomials with the coefficient condition, whose positive floor is classical and whose modern
optima are the Mossinghoff-Trudgian school (R0 = 5.573412 at polynomial degree 16,
arXiv:1410.3926; optimal-cosine-polynomial sequels arXiv:2404.05928, arXiv:2411.01385; plus
known method-step optimality results for the Titchmarsh bound). ULF-INV-4 therefore demotes its
d=1 clause to a cited anchor and retains as open exactly the general-d statement: no engine
whose purchasing data are poles/analytic invariants of a FIXED finite twist/tensor family
reaches kappa < 1. The d=1 anchor makes the conjecture's shape credible; the general statement
is not in the literature found and remains the target, now with the corpus's formal engine
framework as the intended proof habitat.

### 7.2 N2, exact contrapositive

Define the moment category M: objects are Mertens-normal weights w >= 0 with their log-jet
feature Grams H^N_ij = sum_{n<=N} w(n) phi_i(log n) phi_j(log n); admissible operations are
(a) entrywise (Hadamard) normalizations, (b) linear combinations of the block Grams of a feature
pair, (c) aperture limits of (a)/(b). Corpus theorems: (a)-limits are subleading-blind
(`tendsto_mul_regularized`; cross-system form ULF-INV-1); (b) satisfies the
finite/positive/Hankel exclusion (`blockCombination_nonneg_iff`,
`mixed_vanishes_of_second_block_discarded`, `successorHead_form_neg`); any PSD Hankel limit is a
Hamburger moment matrix, i.e. the sought object itself (producer-map §22). AXIOM N2 (exact): any
theory presenting a finite, positive, Hankel, subleading-sensitive pairing contains an operation
outside M — not entrywise, not block-linear, not an aperture limit of such.

### 7.3 N4, exact contrapositive

Corpus theorems (`PrimeIsingTreeCentralMassFloorLaw`): for every finite tree T,
|Z_T'(0)/Z_T(0)| >= (log 2)/2; the floor persists under locally uniform limits; XiC is even so
the unfactored form is excluded; hence any factorization Z = E * XiC realized through tree
limits forces |E'(0)/E(0)| >= (log 2)/2. AXIOM N4 (exact): in any tree-limit realization of the
arithmetic partition function, every zero-free normalizer pays the mass floor (log 2)/2 — the
theory's length spectrum begins at log 2 and no gauge choice evades its first mass.

### 7.4 N5, exact contrapositive

Corpus theorem: `archimedeanPrimeEulerQuadraticCorner_not_isCompactOperator`. AXIOM N5 (exact):
any model whose archimedean-prime comparison corner is compact or trace-class is NOT a faithful
model of the corpus corner; a faithful model represents the corner noncompactly, its finite
numbers arise from relative/truncated traces, and by N2 the truncation is not expressible as a
block-linear subtraction in moment coordinates — it requires structure (regions/indicators)
absent from M.

### 7.5 N3, scoped (flagged: necessity relative to the certified engine list)

Within the corpus's certified engine class (lower-bound engines; zero-density moment engines
with the (2-2sigma)(2sigma-1) ceiling, `ZeroDensityMomentCrossing`), no unconditional upper
bound on the off-line count below the ceiling exists. AXIOM N3 (scoped): an adequate theory
contains an upper-bound mechanism outside that class; in every solved world it is a finite
positive trace on the transfer flow (count <= trace). This clause is necessity-relative-to-E,
not absolute; promoting it to absolute requires enlarging the certified engine list — a standing
work item, not a hidden assumption.

### 7.6 Specification status after this pass

N1 proved (ULF-INV-1). N6 proved (ULF-INV-3). N2, N4, N5 stated as exact contrapositives of
named Lean/corpus theorems (this section). N3 scoped with its relativity flagged. Open:
ULF-INV-4 general-d barrier; the rigidity/consistency theorem for the axiom system
(the charter's §5 gate); deepening the calibration rows into cited exact statements.

### 7.7 ULF-INV-4 second anchor: the family-degree collapse (Siegel/Page)

The known phenomenology already exhibits a FAMILY-degree collapse matching the conjectured
barrier: for a real character chi the degree-2 family {1, chi, chi^2} degenerates (chi^2 = 1
re-hits the pole), the positive-polynomial purchase provably fails to exclude one real zero
(Page's barrier, Davenport ch. 14), and its repair (Siegel) is ineffective — the price of
remaining at bounded family degree. Any proposed definition of engine degree for ULF-INV-4 must
therefore make THREE known results its instances: the Landau extremal floor (coupling degree),
the Page/Siegel collapse and ineffectivity (family degree 2), and the Kim-Sarnak partial bound
(family degree 4). A definition failing to reproduce all three is wrong; one reproducing them
becomes the barrier's proof skeleton. This is the sharpened open core; no new theorem is claimed
in this note.

### 7.8 Fork constraint instantiations — executed to verdict: explanatory ceiling reached

Executed against both fork shapes; recording the outcome and closing the direction.

1. **Infinite-rank constraint (exact, trivial):** the polarized pairing any adequate theory
   provides must have infinite rank — zeta has infinitely many nontrivial zeros
   (Riemann-von Mangoldt), and a finite-rank positive pairing bounds only finitely many spectral
   parameters. Consequence: upstream worlds with locally finite-type cohomology/zeta invariants
   (counting-polynomial F1 geometries, monoid-scheme zetas built from finitely many integers)
   cannot source the import; only infinite-rank upstream structures (scaling-site/adelic type)
   survive the filter. Correct, one paragraph, and — hostile verdict — INSIGNIFICANT as new
   knowledge: no serious program proposes finite-rank sources.
2. **Fork (a) consistency checks:** the Lee-Yang floor (N4) and the corner noncompactness (N5)
   are design constraints any Deninger-shape flow already matches qualitatively (shortest orbit
   log 2; archimedean fixed point with divergent naive trace). Making them quantitative produced
   consistency readings, not discriminating theorems.

VERDICT: the fork-instantiation direction has reached its explanatory ceiling — further work
here re-describes the two programs without constraining them beyond what N1-N7 already state.
Direction CLOSED under the goal's anti-explanatory clause. The program's remaining
theorem-capable targets are: (i) the input-axis formalization (joining ULF-INV-7's pattern cap
with the corpus's ZeroDensityMomentCrossing ceiling into one two-axis map — bridge-grade,
pursue only if a genuinely new clause emerges); (ii) attacks on the residual class itself —
the signed/explicit-formula boundary where the frame meets group 3 — which is the original
positivity problem, now reached from above with the full constraint list attached.

### 7.9 N7 refined to N8: the anti-holomorphic involution axiom (signed-engine boundary, exact)

Lane-deep read of the Weil-polarization gate layer (XiWeilPolarization, XiWeilLineConjHilbert,
XiThetaEigenGramLaw, ScrewCurvatureSumOfSquares; memories weil-polarization-layer-state,
weil-carrier-is-sum-of-complex-squares) gives the frame's residual class an exact description:

- Unconditionally, the corpus's sharpest carrier factors as the BILINEAR sum 16·sum g_rho^2; the
  explicit formula evaluates holomorphic tests and can reach sum g^2, never sum |g|^2; the whole
  gap is the convergent imaginary energy 2·sum (Im g_rho)^2. The Hermitian form itself EXISTS
  unconditionally as an l^2 inner product (line-conjugation isometry), its eigen-Gram is
  antidiagonal, and positivity on the eigen-span is equivalent to RH + simplicity — all in Lean.
- The remaining gate is not convergence or closure: it is identifying the continuous Hermitian
  limit with an actual prime sum for tests outside the resolvent core (and core density is
  equivalent to zero simplicity).

AXIOM N8 (refinement of N7). The adequate theory supplies a SOURCE-COMPATIBLE ANTI-HOLOMORPHIC
INVOLUTION: an involution on the test/space side (not merely the divisor side — the corpus's
conjugation-no-sign no-go proves divisor-side conjugation input yields no positivity) whose
fixed sesquilinear extension of the explicit-formula pairing is identified with the prime source
on an involution-stable dense class. Under N8 the bilinear/Hermitian gap closes on the reachable
class and the corpus's unconditional equivalences take over — this is where group 3 begins, by
construction, and no claim is made past it.

Quantitative shadow: the defect of any candidate involution is the imaginary energy — an exact,
convergent, corpus-formalized functional. The two-fork law applies verbatim to N8: the
involution is either native geometry over Q (fork a: in Deligne's world it is the Weil pairing's
compatibility with Frobenius — the reality of the polarization) or imported (fork b). The
session's terminal frontier statement: every corpus no-go is a proof that N8's involution cannot
be manufactured from moment, majorant, pattern, or pole data; the specification N1-N6 + N8 with
the import law is the complete current form of the inverse theory.

### 7.10 ULF-INV-9 frozen: the identification gate is wall-grade

Grounding read executed: `tendsto_primeArchSource_packetSum_of_tendsto`
(`XiQuotientRealDecay.lean:354`) proves the prime+Gamma double sum equals the Hermitian inner
product for finite far-right Cauchy packets and extends along l^2-convergent packet sequences by
continuity of the inner product — the identification never touches a general test's OWN prime
expression, which is a conditionally convergent double object requiring an interchange step.

FROZEN (ULF-INV-9): the identification of the Hermitian extension with tests' own prime+Gamma
expressions, uniformly over any class rich enough to decide eigen-span positivity, is
wall-grade: it cannot be established from l^2/majorant/positive-pattern structure alone
(the INV-7 frame and the corpus's coefficient-free/modulus caps bound that toolbox), and
requires input-axis arithmetic (the A*L terms) — i.e., the last gate of the Weil-polarization
lane is of the same type as the MR/input wall, not bookkeeping.

`[OPEN CORE]` Prove either: (i) an unconditional identification for a decisive class — which
would transfer the corpus's unconditional "eigen-span positivity <=> RH + simplicity" to actual
prime-sum form (group-3 by construction, as expected at this boundary); or (ii) the no-go: a
uniform identification on a decisive class implies a bound of the capped type, contradicting
the cap laws unless arithmetic input enters. Either resolution is new knowledge about the exact
location of the last analytic gate. First unprovable point: typing the interchange step so that
the cap laws apply to it (the interchange is not literally a per-g majorant; the no-go needs a
reduction, not a citation).
