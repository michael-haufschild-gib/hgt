# Attaching a simply connected cap: surjection and exact kernel

- **ID:** OPEN-CAP-PI1-20261009
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean; all eight public declarations verified)
- **Parent:** `../1-in-progress/xi-single-mark-infinite-cover-exclusion.md`
- **Statement:** If X=U∪V is an open cover, U and U∩V are path connected, and V is simply connected, inclusion π₁(U)→π₁(X) is onto; its kernel is the normal closure of the image of π₁(U∩V).

## Goal

Supply the local topological operation needed when capping a finite peripheral cycle in the exact image cover. This is a corpus-derived implementation of a Van Kampen consequence, not a claim of external novelty. Extension to a locally finite family of caps, construction of the analytic surface, and intrinsic uniformization remain separate open obligations.

## Corpus basis

`DifferentialGeometry.Topology.VanKampen.AmalgamatedProduct` constructs the fundamental-group pushout for an open cover with path-connected members and intersection. `SimplyConnectedUnion` relates simple connectedness to the trivial fundamental group. No web sources or numerical experiments used.

## Complete paper proof

[PROVED HERE, relative to the checked corpus Van Kampen theorem]

Fix basepoint in U∩V. Write A=π₁(U), C=π₁(U∩V). Since π₁(V)=1, Van Kampen identifies π₁(X) with A amalgamated with the trivial group over C. Every generator from the second factor is trivial; every base generator is already the image of its left-factor representative. Products therefore lie in the image of A, proving surjectivity.

Let N be the normal closure in A of the image of C. Commutativity of the pushout square makes that image trivial in π₁(X), so N lies in the inclusion kernel. Conversely, the quotient homomorphism A→A/N and the trivial map π₁(V)→A/N agree on C. The pushout produces π₁(X)→A/N whose composite with inclusion is the quotient map. Any element killed by inclusion is therefore in N. This proves the exact kernel.

The statement concerns a genuine open-cover construction and imposes no surjectivity hypothesis. It does not yet assert that all caps have been attached, or that the completed Xi image cover exists.

## Log

- 2026-10-09 — extracted from the vendored Van Kampen declarations; complete paper argument recorded before Lean work.
- Both exact-kernel and surjectivity declarations passed their first Lean check. Production leaf build passed. Basepoint independence then passed after correcting a cast simplification.

## Directed-union step

Every loop class in a directed open cover of X is the image of a loop class in one cover member. The continuous image of the unit interval is compact, so the corpus's `IsCompact.elim_directed_cover` puts the complete loop in one member. Restrict the path to that subtype; composing with inclusion recovers the original path exactly. This does not require simple connectedness of any member.

This argument passed Lean on its first check. It reduces a family of caps to finite stages once those stages are supplied, without imposing finiteness of the total set of caps. The next obligation is to connect finite attachments to this compactness theorem; the global capped surface is not yet constructed.

## Arbitrary disjoint cap family: exact next theorem and paper proof

Let U be open and path connected in X. Let (V_i) be pairwise disjoint, open, simply connected sets with each U∩V_i path connected. If U∪⋃V_i=X, then π₁(U,a)→π₁(X,a) is onto for every a∈U. No finiteness or local-finiteness assumption on the index family is needed.

For a finite index set S, put W_S=U∪⋃_{i∈S}V_i. Induct on S. The empty stage is U. When adjoining V_j with j∉S, disjointness gives W_S∩V_j=U∩V_j. The relative version of the single-cap theorem therefore makes π₁(W_S)→π₁(W_{S∪{j}}) surjective; its composite with the induction map from U is surjective. Path connectedness of each stage follows from the same nonempty connected overlap. The W_S form a directed open cover of X. By compactness, any target loop comes from some W_S, and the finite-stage result lifts its class to U.

This strengthens the planned loop-detour argument: arbitrary disjoint caps suffice. It still requires the actual cover and cap charts to be constructed. Formalization of relative attachment and finite-stage induction is in progress.

### Stronger overlap condition exposed by formalization

Disjointness is unnecessary: it suffices that V_i∩V_j⊆U for distinct i,j. The same induction works because a point in W_S∩V_j either already lies in U or lies in some V_i with i∈S, hence in U by the weaker overlap condition. Thus W_S∩V_j=U∩V_j still holds. This directly fits puncture charts that each avoid all other punctures, even if their unpunctured parts overlap. The stronger exact theorem is being formalized, rather than retaining an unnecessary disjointness premise.

The stronger arbitrary-family theorem now passes Lean, including relative attachment and the finite-stage induction. No warnings.

## Puncture-deletion corollary

Let A be closed, X\A path connected, and each a∈A have an open simply connected neighborhood V_a meeting A exactly in {a}, with V_a\{a} path connected. Then π₁(X\A)→π₁(X) is onto. The puncture neighborhoods cover A and any overlap between distinct neighborhoods is contained in X\A, so the checked family theorem applies. This is the precise puncture-avoidance ingredient needed by the completed image cover. The neighborhood hypotheses must still be verified on its constructed charts; the theorem does not assume its own surjectivity conclusion.

## Verification

- `HTGeometry/OpenCapFundamentalGroup.lean`: four public declarations, production leaf build PASS; final direct source check PASS, empty `/tmp/hgt-open-cap-final.log`.
- `HTGeometry/OpenCapFamily.lean`: four public declarations, production leaf build PASS, 1752 jobs; final direct source check PASS, empty `/tmp/hgt-cap-family-final.log`.
- All eight public declarations: axiom audit PASS, only `propext`, `Classical.choice`, `Quot.sound`; `/tmp/hgt-open-caps-axioms.log`.
- Both modules wired to the HTGeometry umbrella. Index refreshed; new-source whitespace check PASS.
- Global lint FAIL on ten unrelated unreachable modules: RHTower.ChronologicalBudgetGapLaw; RHTower.ThetaCuspRatioKineticLeading.JetHeads, KineticCoefficients, MinorLeading, ReflectionHeads; HTGeometry.ApertureConeCalculus, ApertureConeWinding, ApertureLogTranslation, ApertureOpenHistoryIdeal, BoundaryCoronaCStarAlgebra. No error in the new modules and no forbidden-declaration error. `/tmp/hgt-open-caps-lint.log` records the exact snapshot; concurrent work changes this global list.

- Final source checks complete; obsolete implementation/API scratch files removed. Audit script and logs retained.
