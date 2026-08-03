# Hostile journal-level review

Manuscript: *Boundary migration, derived acyclicity, and countable continuity of C*-envelopes*

Review date: 2026-08-03

Target standard: a renowned broad mathematical journal in the *Advances in Mathematics* /
*Mathematische Annalen* range. This is an internal hostile review, not a claim of external human
peer review or acceptance.

## Recommendation

**PASS — submission-quality at target standard after the corrections recorded below.**

The paper proves a concise universal law: on the maximal quotient category where canonical
C*-envelope maps exist, the envelope functor is countably continuous after passage to Fréchet
local C*-envelopes, equivalently every resulting Shilov ideal tower is `lim¹`-acyclic. The law is
not a disguised Mittag–Leffler hypothesis: a separate realization theorem puts any prescribed
sequence of separable unital C*-algebras into the link deficits of a split tower while the global
obstruction still cancels. Combined with the escape/deficit calculus and composition exactness,
this is a coherent theory rather than a repackaged diagram chase.

I would not advertise the work as Annals/JAMS-level. The target above is credible because the
central theorem crosses operator-system boundary theory, pro-C* limits, homological algebra, and
representable K-theory, and because the arbitrary-deficit theorem rules out the obvious pointwise
explanation.

## Hostile objections and dispositions

### 1. “The universal-cover kernel formula is cited incorrectly.”

**Sustained, then fixed.** KPTT Theorem 3.7 alone gives the complete-order embedding into the
quotient cover; Corollary 3.9 supplies the universal C*-algebra identification. Proposition 2.1
now cites both. The theorem remains valid.

### 2. “Acyclicity may be circular: continuity is assumed to prove continuity.”

**Rejected.** The Roos sequence is first proved for arbitrary vector-space towers. Independently,
coordinate arguments identify the local Shilov ideal in the universal-cover limit and prove that
the stage-envelope limit has zero local Shilov ideal. Joița's uniqueness theorem then identifies
the two generated local covers. Only afterward does exactness force `lim¹=0`.

### 3. “The local-envelope uniqueness theorem may not match the topology.”

**Rejected after source check.** Joița Theorem 3.18 concerns separable unital Fréchet locally
C*-algebras with countable indexed C*-seminorms and a surjective unital local complete isometry
between generating systems with trivial local Shilov ideals. Here both copies of the limit system
have the stage norms as their indexed matrix seminorms, so the identity is exactly such a map.

### 4. “The derived sequence silently assumes restricted Shilov maps are surjective.”

**Rejected.** Only ambient universal-cover maps are assumed surjective. The connecting map is
constructed from representative mismatches. Its surjectivity uses recursive ambient lifts. The
restricted maps may be zero; this is explicitly discussed and formally modeled.

### 5. “Arbitrary deficits are cosmetic because the constructed graph may not generate its cover.”

**Rejected after proof expansion.** A sentinel sent to zero exposes the new central projection;
the generator block then produces the full new summand. In a tower, future sentinels are sent to
the unit in every earlier summand, so the current sentinel remains a full unitary until used.
Essentiality of `C_0((0,1],D)` kills every candidate boundary ideal. These checks establish both
generation and stage minimality.

### 6. “Splitness should force the deficit to be tame.”

**Refuted by theorem.** Every separable unital C*-algebra occurs. Therefore dimension,
nuclearity, type, ideal lattice, representation theory, and K-theory are unrestricted.

### 7. “The spectral-closure statement substitutes ordinary topology.”

**Rejected.** The manuscript explicitly uses spectral closure and cites Kennedy–Kim–Manor
Proposition 9.2. It does not make the false ordinary-closure replacement.

### 8. “The topological `lim¹` quotient need not be Hausdorff.”

**Handled.** Theorem 6.1 calls it the quotient topology of `coker Δ_J`; it does not claim the last
term is Fréchet or Hausdorff. For actual Shilov towers the term vanishes.

### 9. “The formalization is theatre because operator systems are encoded as arbitrary vector spaces.”

**Rejected with a scope correction.** The paper and claim trace state exactly what Lean proves:
the quotient algebra, composition, Roos, comparison, and coherent-representative obligations.
They also state exactly what it does not prove: positivity, Shilov minimality, boundary
representations, and local C*-envelope uniqueness. No analytic theorem is replaced by an axiom or
a structure field containing the conclusion. The formal supplement is meaningful but partial.

### 10. “Novelty is an artifact of terminology.”

**Rejected provisionally.** Primary-source comparison and exact/near-exact searches found the
ingredients separately but not the escape/deficit pair, maximal quotient category, composition
sequence, Shilov `lim¹` law, countable envelope continuity, or prescribed cancellation tower.
The arbitrary realization and global cancellation are theorem-level content independent of the
names.

### 11. “The paper is too narrow for a broad journal.”

**Rejected at the stated target, but this is the main editorial risk.** The one-map theory alone
would be a specialist note. The inverse-limit law plus arbitrary link-defect cancellation makes a
general structural statement connecting four established subjects. The K-theory consequence and
maximality theorem broaden reach. Concision (11 pages) is not lack of depth; proofs close the
nontrivial topology and construction details.

## Verification record

- TeX engine: Tectonic.
- PDF: 11 pages, no warnings, undefined references, overfull boxes, or underfull boxes.
- Visual audit: title/abstract, theorem pages, derived sequence, construction, and bibliography.
- Text extraction audit: no leaked TeX tokens such as `qquad`.
- Lean foreground check: `lake env lean GaloisForLFunctions/HTGeometry/ShilovBoundaryMigrationDefect.lean` passed.
- Targeted final build: `lake build GaloisForLFunctions.HTGeometry.ShilovBoundaryMigrationDefect` passed (`2997/2997`).
- Axiom audit: main formal results depend only on `propext`, `Classical.choice`, and `Quot.sound`.
- Forbidden-token audit: new module contains no `sorry`, `admit`, project `axiom`, `opaque`, or `unsafe` declaration.
- Umbrella: new module imported by `GaloisForLFunctions.HTGeometry`.
- Global repository lint: fails on unrelated pre-existing unreachable modules in `RHTower` and
  three unrelated `HTGeometry` modules; it does not flag the new module as unreachable.

## Scores

| Criterion | Score | Comment |
|---|---:|---|
| Correctness | 4.6/5 | Dependency-closed paper proof; analytic layer still awaits human specialist verification. |
| Originality | 4.7/5 | No collision found; new theorem package and arbitrary-deficit tower are distinctive. |
| Significance | 4.3/5 | Broad structural law, though within operator-system boundary theory. |
| Depth | 4.4/5 | Derived exactness, local minimality, and recursive sentinel construction all essential. |
| Exposition | 4.6/5 | Compact, self-contained proof path; exact source ancestry now explicit. |
| Reproducibility | 4.5/5 | Compiled manuscript, claim trace, literature audit, and unconditional Lean algebraic core. |

## Final hostile verdict

No known fatal mathematical gap remains. No result is sold as Lean-formalized when it is not. No
novelty claim rests only on renamed standard objects. Manuscript is at credible submission quality
for a renowned broad journal in the stated range. Actual publication remains contingent on
external peer review and priority checking.

