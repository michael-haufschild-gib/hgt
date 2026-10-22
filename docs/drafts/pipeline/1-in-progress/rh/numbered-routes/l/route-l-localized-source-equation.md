# Route L: localization with the complete source forcing retained

- **ID:** RH-L-C58
- **Stage:** 1-in-progress
- **Target:** Full-source physical/cyclic reader agreement at the original anchor.
- **RH status:** UNPROVED

Chain: complete original source → fixed-reader agreement → conormal vanishing → RH. C57 tested analytic transfers without deriving the central equality. The current test keeps the actual source forcing in every localized equation before attempting injectivity.

## Conjecture–test–pivot record

### 1. Homogeneous localization from the actual source equation

**Conjecture tested:** the localized source supplies a homogeneous equation to which contraction or injectivity can be applied.

The literal equation is `G_m-G_(m+1)=f_m`. The source files prove that every other primitive is `G_m+c`, with endpoints `c` and `P+c`, where `P` is the complete original periodization. Indeed, subtracting the two source equations makes their difference constant in the integer cell index. Thus a common primitive correction leaves the jump exactly `P`. The damping-two source has a nonzero Fourier coefficient of this jump at every original prime period and integer mode.

**Result:** this proposed homogeneous equation is not supplied by localization. A reader may still annihilate a nonzero jump, but that requires a proof for that specific reader. This does not refute full-source reader agreement.

**Positive statement retained:** exact classification of all original primitives and their two endpoints, already proved in `DeningerL1GreenCellCalculus.lean`, together with the actual nonzero coefficients in `DeningerL1LocalGreenBoundary.lean`. No duplicate theorem added.

### 2. Coercive or resolved-composite cancellation

`DeningerPrimeKummerCoercivityLocalization.lean` proves a positive gap for native positive Tate-circle modes and no uniform positive gap for the signed prime-log lattice. Its compressed-operator inverse theorem requires coercivity. The corpus energy inequalities retain forcing or require an unforced solution; neither supplies the missing source cancellation.

`DeningerGreenInternalDefectCancellationLaw.lean` cancels the two internal defects after composition. `DeningerGreenResolvedSourceConservativityCriterion.lean` identifies full componentwise vanishing with RH; its conservative-sector implication requires both sector support and conservativity. The completed reflected-Gaussian defect bound does not supply a fixed-point equation for the defect.

**Result:** neither a local spectral gap nor composite cancellation produces the individual physical-reader equality. The positive local coercivity and exact internal cancellation are already formalized.

### 3. A single joint boundary correction

Broad newest-first arXiv `localization` found Li–Sun, [Cusp restrictions and Bunke–Naumann invariants with level structure](https://arxiv.org/html/2609.11924), September 10, 2026. Lemma 4.3 constructs one rational weight-two modular form with prescribed parity at both cusps. Theorem 4.6 produces an integral boundary witness and one rational global source witness for an imported half-integral modular form. Their equality holds in the bounded rational numerator; quotienting then annihilates the class. Lemma 7.1 supplies the weighted constant-term residue relation. At level three with input `h=1`, the integral witness has constants `(0, 2/3)`. Its weighted reader `CT∞+3 CT₀` equals `2`, although the quotient class vanishes. The rational global correction has weighted reader zero. These are exact consequences of the displayed formulas, not numerical experiments.

**Transfer test:** the paper constructs simultaneous correction, but does not identify our complete source with its integral modular input or show that our fixed complex reader descends through its integral and rational-source indeterminacies. The example above prevents inferring scalar-reader vanishing from quotient annihilation alone.

The corpus has actual joint-source Laplace identification in `ThetaCuspHawkingBMJointSourceCausalCuspSourceIdentification.lean`, with every cutoff channel retained. It is an equality with that source's original cusp residual, not an identification with this paper's modular-form lattice. The Maass cusp transport identities require an actual Maass cusp eigenform and retain the flux and tail squares.

The more directly relevant `MobiusThetaSourceDaggerMinimalBoundaryLaw.lean` gives the exact source-residue formula

```text
residue(paracyclic defect on x)
  = (half-density mate gain - 1) * Cρ * ordinary-prime trace(x).
```

At the actual multiplicity grade, `Cρ ≠ 0`, and ordinary-prime atoms have trace one. The same file defines residue annihilation as a proposition and proves its RH equivalence. The search model described that definition as a proof; inspection of the declaration and its source prevents using it as an unconditional producer. This is a leading-source identity, not a substitute for complete-source agreement.

**Result:** a full-source correction must be constructed and its physical image evaluated before any quotient can be used. No such correction was derived here. The joint-cusp construction remains a possible method with an unproved source map; it is not retired or claimed transferred.

## Whole-corpus and method search audit

All three searches used deep mode, `--any`, a 120-second budget, and cached-index search. Every returned candidate statement, source-method assumption, and ingredient group was inspected: 20 candidates and 20 source arguments per search; one proposed ingredient group each, no proof ideas. Definitions, source-only metadata, and model-generated method descriptions were not treated as kernel verification.

| Search artifact | Index generation | Coverage snapshot | Result |
| --- | --- | --- | --- |
| `route-l-localized-source-equation-search.json` | 879982 | 57069 files, 47449 Lean files, 735524 declarations; generation 879991 | Partial; forcing, coercivity, and injectivity obligations remain |
| `route-l-joint-boundary-correction-search.json` | 879995 | 57070 files, 47449 Lean files, 735524 declarations; generation 880010 | Partial; actual source identification and quotient-reader compatibility absent from inspected hits |
| `route-l-global-residue-source-search.json` | 880032 | 57070 files, 47449 Lean files, 735524 declarations; generation 880045, current 880046 | Partial; exact leading-source defect retained |

All report interrupted text/source retrieval and unmeasured semantic completeness. No claim of exhaustive absence follows. Broad `recurrence` results supplied no usable mathematical transfer. The September quantum-symmetry paper was screened at abstract level only; its HTML was unavailable, and no theorem was used.

## Exact frontier and verification

Full-source fixed-reader agreement remains unproved. This turn tested proposed transfers against retained forcing and exact source residues; it did not close a new mathematical step toward the central equality.

Next attack: construct a correction on the complete original source and calculate its fixed physical image, preserving original prime, native Tate depth, every multiplicity copy, the nonzero Xi coefficient, Gamma normalization, and horizontal anchor. In particular, account for the coupled native-depth tail rather than replacing it by its leading source or declaring its boundary zero.

No Lean code changed; no new Lean theorem, scratch check, or build was claimed. No heartbeat change, numerical experiment, or axiom-printing audit was performed. All three research processes completed. No new route-independent STATUS entry was added: the tests do not establish a new universal constraint beyond the existing ledger.
