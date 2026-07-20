# Reciprocal ABCD projective HT horizon law

- **ID:** `reciprocal-abcd-projective-ht-horizon-law`
- **Stage:** 3-formalized
- **Type:** `[LEAN-PROVED] [BRIDGE] [REDISCOVERED] [NO RH CLAIM]`
- **Area:** `HTGeometry`; reciprocal electrical two-ports and paraxial optics
- **Lean target:**
  `formal/GaloisForLFunctions/HTGeometry/ReciprocalABCDProjectiveHorizon.lean`
- **Parents:**
  `formal/GaloisForLFunctions/HTGeometry/ProjectiveImmittanceHorizon.lean`
- **Statement:** The reciprocal ABCD law `a*d-b*c=1` discharges every nondegeneracy premise in
  the projective-immittance HT preservation and reciprocal jet-horizon classification, so one
  physically canonical hypothesis yields both conclusions simultaneously.

## Exact claim

Let `F` be a characteristic-zero differential field, `E/F` a differential-field extension, and
`x in E` hypertranscendental over `F`.  For `a,b,c,d in F`, assume the reciprocal transfer law

```text
a*d-b*c=1.                                                   (1)
```

Writing

```text
M(x)=(a*x+b)/(c*x+d),                                       (2)
```

the claim is

```text
M(x) is hypertranscendental over F,                          (3)

(for every n, JetTail_F(M(x^-1),n)=JetTail_F(M(x),n))
  iff d^2=c^2.                                               (4)
```

Thus reciprocity supplies the exact determinant interface, while the pole condition `d^2=c^2`
still classifies folding of the complete impedance/admittance jet flags.

## Internal frontier

- `[CORPUS]` `hypertranscendentalOver_projectiveImmittanceChart` proves `(3)` from the abstract
  nondegeneracy premise `a*d-b*c != 0`.
- `[CORPUS]` `projectiveImmittanceChart_inv_all_jetTailField_eq_iff` proves `(4)` from the same
  abstract premise.
- `[CORPUS]` `smithReflectionChart_inv_all_jetTailField_eq` is the single Smith-chart
  specialization `(a,b,c,d)=(1,-1,1,1)`.
- `[LOCAL-RESEARCH]` No declaration in the generated API joins the reciprocal ABCD law to both
  projective HT preservation and the complete reciprocal-horizon classification.

## External frontier

- `[LITERATURE]` Kogelnik--Li, *Laser Beams and Resonators*, Applied Optics 5 (1966),
  DOI `10.1364/AO.5.001550`, writes the paraxial ray-transfer law and records `AD-BC=1` for the
  canonical ABCD normalization.
- `[LITERATURE]` Reciprocal two-port transmission matrices obey the same determinant-one law;
  cascades multiply their chain matrices.  This is standard network theory, not an HGT result.
- `[LITERATURE]` Projective/Mobius action of determinant-one ray-transfer matrices is standard
  first-order optics.  No scientific novelty can come merely from substituting `(1)` into an
  existing nondegenerate projective theorem.

## Hostile audit

1. **Parent-theory attack.**  `(1)` implies `a*d-b*c != 0` because `1 != 0`; `(3)` and `(4)` are
   then immediate specializations of compiled parent theorems.  The exact result is
   `[REDISCOVERED] [BRIDGE]`, not new scientific knowledge.
2. **Certificate attack.**  The theorem does not construct a reciprocal electrical or optical
   realization of an arithmetic source.  It only says what follows once its ABCD coefficients
   satisfy the physical reciprocity law.
3. **Passivity attack.**  Determinant one expresses reciprocity/area preservation, not positive
   realness, losslessness, causality, or a Herglotz sign.  It cannot close the RH source-effectivity
   wall.
4. **Coordinate-normalization attack.**  In ray coordinates not normalized by refractive index,
   the raw ray matrix may have determinant `n_in/n_out`; the theorem applies after the canonical
   symplectic normalization, or directly only when `(1)` is true.
5. **Novelty attack.**  The only local delta is interface closure: a physically named equality
   replaces an arbitrary nonzero determinant premise and composes two existing theorem surfaces.

**Verdict:** `BRIDGE`.

## Complete paper proof `[PAPER-PROVED]`

From `(1)`, rewriting gives `a*d-b*c=1`, hence `a*d-b*c != 0` because a field is nontrivial.
Apply `hypertranscendentalOver_projectiveImmittanceChart` to obtain `(3)`.  Apply
`projectiveImmittanceChart_inv_all_jetTailField_eq_iff` with the same nonzero determinant witness
to obtain `(4)`.  Conjoin the results.  No analytic, passivity, realization, or RH premise enters.

The proof is dependency-closed: both invoked results are compiled corpus theorems and `(1)` is the
only additional hypothesis.  Exact-statement searches for ABCD hypertranscendence, differential
algebra, and jet-horizon laws recovered standard special-linear/projective optics but no HGT
statement.  That negative search does not support novelty: the hostile parent-theory attack already
shows the result is an immediate specialization.

## No-go closure

- **Exact killing theorem/mechanism:** The claimed novelty is killed by direct specialization of
  the existing nondegenerate Mobius/projective parent theorems.
- **Strongest positive survivor:** The reciprocal ABCD equality is a canonical hypothesis
  discharge that joins HT preservation and complete reciprocal-horizon folding in one theorem.
- **New insight:** Electrical chain matrices and paraxial optical ray matrices meet the same local
  HGT connector exactly at determinant one; reciprocity does not supply passivity.
- **Status:** paper proof displayed above; Lean pending exact toolchain check.

## Gates

- [x] internal theorem surfaces and generated API audited
- [x] external ABCD parent law checked
- [x] exact claim and hostile parent-theory verdict recorded
- [x] dependency-closed paper proof promoted to Stage 2
- [x] exact unconditional Lean theorem and axiom audit

## Lean verification

- `lake env lean GaloisForLFunctions/HTGeometry/ReciprocalABCDProjectiveHorizon.lean`: passed.
- `reciprocalABCD_projective_hypertranscendence_and_horizon_law` states the exact conjunction
  `(3)`--`(4)` with no added route premise.
- A scratch `#print axioms` audit reports only `propext`, `Classical.choice`, and `Quot.sound`.
- `lake build GaloisForLFunctions.HTGeometry.ReciprocalABCDProjectiveHorizon`: passed.
- Generated indexes were refreshed.  Repository lint finds the module reachable and reports no
  proof debt in it; the only hard failures are unrelated HilbertMetric umbrella wiring for the
  concurrently edited `GaussianJetPositivity` and `ThreePointCorrelationLocal` modules.

## Log

- 2026-07-20 -- Created at Stage 1 after the expanded electrical/optical census isolated the
  determinant-one reciprocity law as a direct existing-interface discharge.
- 2026-07-20 -- Parent specialization proof closed; exact-statement search confirmed that the only
  defensible status is `[BRIDGE] [REDISCOVERED]`; promoted to Stage 2 before Lean work.
- 2026-07-20 -- Exact combined theorem formalized, axiom-audited, and built; moved to Stage 3
  without scientific-novelty promotion.
