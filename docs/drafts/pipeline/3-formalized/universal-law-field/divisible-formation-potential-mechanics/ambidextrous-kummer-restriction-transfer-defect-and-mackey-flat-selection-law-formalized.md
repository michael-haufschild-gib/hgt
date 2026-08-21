# ULF-DFPM-5 — Lean certification record

**Card:** `ambidextrous-kummer-restriction-transfer-defect-and-mackey-flat-selection-law.md`
**Status:** every theorem of the card is Lean-certified, unconditional and axiom-clean.

## Card result → Lean declaration

| Card | Statement | Lean |
|---|---|---|
| (ART.1) | restriction `R_{m,n} : C_m → C_n` | `depthRestriction` |
| (ART.2) | covariant inclusion `T_{n,m} : C_n → C_m` | `depthInclusion` |
| (ART.3) | functoriality of both towers | `depthRestriction_comp`, `depthInclusion_comp` (via `div_mul_div_of_dvd_dvd`) |
| (ART.4) | restriction is always flat | `depthRestriction_flat` |
| (ART.5) | the ambidextrous defect | `ambidextrousDefect`, `ambidextrousDefect_eq` |
| (ART.6) | the crossed three-depth composition law | `ambidextrousDefect_cocycle` |
| Thm 3.1 | four-way exact selection | `ambidextrousDefect_tfae` |
| (ART.7) | the doubling defect is `[-q]` and is nonzero for `q ≠ 0`, `\|q\| < n` | `ambidextrousDoublingDefect_eq`, `ambidextrousDoublingDefect_ne_zero`, `ambidextrousDefect_doubling` |
| Cor 3.2, (ART.8) | the cofinal doubling family reconstructs the charge | `doublingDefect_reconstructs`, `eq_of_doublingDefect_eq` (via `intCast_inj_of_natAbs_lt`) |
| (ART.9)–(ART.10) | the regular ambidextrous packet | `AmbIndex`, `ambShift`, `ambPacketUnitary`, `ambPacketDefect` |
| Thm 4.1, (ART.11) | compact ⟺ Schatten ⟺ `q = 0` | `ambPacket_tfae` (via `isCompactOperator_ambPacketDefect_iff`, `movedSet_ambShift_infinite`) |
| Thm 4.1, (ART.12) | the essential norm is exactly `2` | `isGLB_essNorm_ambPacketDefect` (via `two_le_norm_ambPacketDefect_sub`, `norm_ambPacketDefect_le_two`) |
| §5, (ART.13) | information isometry of the lifted functional-equation action | `formationLiftKernel_klDiv_isometry` |
| §5, (ART.14) | the essential norm is a charge invariant | `isGLB_essNorm_ambPacketDefect` + `essNorm_ambPacketDefect_charge_invariant` |
| Cor 6.1 (1)–(4) | Mackey-flat divisor selection for an arbitrary local charge family | `mackeyFlatSelection_tfae` |
| Cor 6.1, Euler shell | the four conditions are equivalent to RH | `riemannHypothesis_tfae_mackeyFlat` (via `localFormationCharge_eq_zero_iff` and ULF-DFPM-1's `riemannHypothesis_iff_zetaZeroFreeRight`) |

## Modules

| Module | Role |
|---|---|
| `HTGeometry/ConstitutiveAmbidextrousKummerSelection.lean` | pre-existing finite selector |
| `HTGeometry/AmbidextrousKummerDepthCalculus.lean` | §2–§3 in full |
| `HTGeometry/LpReindexCompactDichotomy.lean` | reusable reindexing Calkin engine |
| `HTGeometry/AmbidextrousKummerCalkinProperness.lean` | §4 and the abstract Cor 6.1 |
| `RHTower/MackeyFlatDivisorSelection.lean` | Euler-shell specialization, (ART.14) |
| `HTGeometry/ConstitutiveFunctionalEquationPacketLift.lean` | pre-existing, supplies (ART.13) |

All are wired into `GaloisForLFunctions.HTGeometry`, `GaloisForLFunctions.RHTower` and
`GaloisForLFunctions.HTGeometry.UniversalLawField`.

## Proof notes

The card's (ART.12) argument routes through a `2`-adic valuation, a choice of odd primes and a
weakly-null orthonormal sequence of exact `(−1)`-eigenvectors.  The Lean proof replaces this with
**approximate** `(−1)`-eigenvectors — the chain vectors
`∑_{j ≤ m} (−1)^j / √(m+1) · e_{σ^j x}` — whose defect norm is `√((4m+2)/(m+1)) → 2`.  This needs
only that the shift has arbitrarily long injective chains, which `ambShift_chains` supplies for
every nonzero charge, and it removes the prime selection entirely.  Weak nullity is likewise
replaced by a finite totally-bounded-net plus pigeonhole argument on the range of the compact
correction, so no limiting subsequence is extracted.

## New reusable results

`HTGeometry/LpReindexCompactDichotomy.lean` is charge-free infrastructure: for any permutation `e`
of an index set, the defect `U_e − I` on `ℓ²` is compact iff `{i | e i ≠ i}` is finite, and its
distance to the compact operators is at least `2` whenever `e` has arbitrarily long injective
chains.  It is the engine behind both (ART.11) and (ART.12) and is independent of this card.

## Verification

* `lake env lean` on all new modules: 0 errors, 0 warnings.
* `#print axioms` over the 66 public declarations of the four ambidextrous modules: only `propext`,
  `Classical.choice`, `Quot.sound`.
* No `sorry`, `admit`, `axiom`, `opaque`, `unsafe`, and no added hypotheses.

## Not claimed

Source covariant-inclusion horizontalness — the card's declared `[SOURCE BIFLATNESS OPEN]` gate —
is future work, not a theorem of the card.  Corollary 6.1 remains an equivalence, not an RH proof.
