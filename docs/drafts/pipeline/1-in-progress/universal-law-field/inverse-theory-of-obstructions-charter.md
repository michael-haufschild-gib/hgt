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
