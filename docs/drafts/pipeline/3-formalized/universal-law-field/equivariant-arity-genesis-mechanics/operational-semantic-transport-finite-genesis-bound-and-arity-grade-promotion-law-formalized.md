# Operational semantic transport, finite-genesis bound, and arity-grade promotion — formalized

- **ID:** ULF-EST-1
- **Stage:** 3-formalized
- **Lean module:** `GaloisForLFunctions.HTGeometry.ConstitutiveSemanticTransportArityPromotion`
- **Umbrella:** `GaloisForLFunctions.HTGeometry.UniversalLawField`
- **Status:** [LEAN-CERTIFIED] [MECHANISM NOT OBJECT] [NO ROUTE PREMISE] [NOT RH]

## Certified mechanism

Lean certifies the following route-independent laws.

1. A reporter `r` is determined by reporter `q` exactly when every intervention invisible to `q`
   is invisible to `r`.
2. Adjoining `r` to `q` strictly contracts the old invisible-intervention doctrine exactly when
   `r` splits an old `q`-fibre.  The proof constructs a one-state overwrite witness.
3. Every effective reporter birth on a finite carrier strictly increases attained-image
   cardinality.  If the initial image has size `b`, a history has length at most `|X|-b`.
4. The constant-reporter bound `|X|-1` is sharp on every finite nonempty carrier.
5. Successive support arities form split associated grades: restriction to arity `m+1` has kernel
   the next invisible tail, with canonical zero-extension section.
6. Translation is invisible before promotion exactly when its coefficient lies in the old tail;
   every coefficient removed by promotion has an explicit detected `(m+1)`-support.
7. A permutation-closed reporter doctrine containing one support contains every support of the same
   arity.

Together these certify the mechanism

```text
failure witness
  -> symmetry-closed reporter grade
  -> strict contraction of legal invisible interventions
  -> finite termination or arity/carrier/admission escape.
```

They do not construct a source-native witness.  That remains the next field gate.

## Headline declarations

- `reporterDeterminedBy_iff_invisible_mono`
- `reporterInvisible_pairedReporter_iff`
- `pairedReporter_strict_contraction_iff`
- `reporterRange_card_lt_of_strict_refinement`
- `finite_reporter_genesis_bound`
- `sharp_finite_reporter_genesis_on_type`
- `arityGradeRestrict_zeroExtend`
- `arityGradeZeroExtend_mem_tail`
- `arityGrade_kernel_iff`
- `supportTranslate_invisible_iff`
- `next_arity_detected`
- `finsetOrbitPerm_image`
- `symmetry_closed_support_promotes_grade`

## Audit

- direct module elaboration: passed
- project formal lint: passed
- umbrella wiring: complete
- umbrella build: `lake build GaloisForLFunctions.HTGeometry.UniversalLawField` passed
  (`11,479` jobs); replay warnings were pre-existing, while the new module built cleanly
- axiom print: no project axioms; declarations use only `propext`, `Classical.choice`, and
  `Quot.sound` where required
