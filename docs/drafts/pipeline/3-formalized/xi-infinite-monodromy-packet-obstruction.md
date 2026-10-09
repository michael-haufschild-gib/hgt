# Infinite monodromy versus finite conjugate packets

- **ID:** XI-INFINITE-PACKET-20261008
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `RHTower/XiMarkedConjugatePackets.lean`, `XiMarkedFiniteMonodromy.lean`, `XiMarkedNormalClosure.lean`.
- **Statement:** Finite common-conjugator packets, surjective integer winding, full normal closure and full images in every finite group do not force equality of the actual monodromy subgroup.

## Scope and plan

User goal remains unconditional Lean proof or disproof of RH through geometry/topology. No web, numerical experiments, energy, positivity, spectral or Fourier route. This card audits a possible inference in the existing geometric machinery; it does not retire actual Xi monodromy or assert RH.

1. Read actual marked Xi declarations and search corpus for an equivalent countermodel. Done.
2. Complete exact countermodel and positive coset classification on paper. Done below.
3. Formalize the unconditional example; direct leaf audit, axiom audit, umbrella wiring and index. Done. Global lint blocked by unrelated omissions and concurrent generated-index drift, detailed below.
4. Return to actual Xi: determine additional source information that could exclude this example. Open.

`update_plan` is unavailable in this tool session; this file holds task state.

## Corpus evidence and conjecture attack

The actual Xi image H in a finite product of twice-punctured-plane groups lies in the common-winding subgroup D. Every finite packet in a coordinate winding kernel admits a common conjugate in H. Existing code proves both equality in every finite group image and normalClosure(H)=D. The latter was already present and must not be duplicated.

Candidate inference: these facts imply H=D. **Verdict: FALSE**, by the following exact group action. This refutes only the abstract inference, not the assertion that the actual Xi image might equal D.

Corpus searches: `/tmp/hgt-xi-monodromy-exact.json` (partial); `/tmp/hgt-finite-packets-countermodel-search.json`; exhaustive `rg` over usages of the actual joint-map declarations. Search results do not certify mathematical novelty. External audit omitted by explicit user instruction; absence from training data is unverifiable.

## Dependency-closed paper proof

Let F be the free group on x,y. Its sheets are S={*} disjoint-union Z. Let rho act by x(*)=* and x(j)=j+1 on integer sheets, while y swaps * and integer 0. Let w:F→Z be exponent sum of x, N=ker(w), and H the stabilizer of *.

For every g, rho(g)(j)=j+w(g) on all but finitely many integer sheets. Both generators and their inverses have this property; composition preserves it because translation preserves finite sets. Consequently every n in N fixes all but finitely many integer sheets.

For a finite packet T⊂N choose j fixed by all rho(t), t∈T. The word c=y*x^(-j) sends j to *, so c*T*c^(-1)⊂H. This is the precise finite-packet condition used by the Xi theorem.

The literal generator x belongs to H and has winding one. Thus the countermodel retains a primitive zero meridian, strengthening the first integer-line example which supplied only a general winding-one word. Consequently w(H)=Z. The subgroup is proper because y moves *. The action is transitive: x^j*y(*)=j. The map F/H→S, gH↦rho(g)(*), is a bijection; equality of images is exactly h^(-1)g∈H. Hence the index is infinite. Under this bijection x fixes * and translates Z, while y swaps * and 0.

For any homomorphism q:F→G with G finite, the existing finite-normal-packet theorem gives q(N)⊂q(H). For arbitrary g, n=g*x^(-w(g)) belongs to N and g=n*x^(w(g)); hence q(g)∈q(H). Thus q(H)=q(F) for EVERY finite G.

Likewise normalClosure(H)=F: singleton packets put every n∈N into the normal closure; x∈H supplies every winding class by the same decomposition.

## No-go closure and positive survivor

- **Killing mechanism:** common conjugators can escape to integers outside each finite support. No one conjugator need work for the whole kernel.
- **Positive survivor:** exact infinite coset space F/H≃({*} ⊔ Z), with x fixing * and translating Z, and y swapping * with integer 0, despite complete finite-quotient and normal-closure saturation. This is an explicit model of information retained by a nonnormal infinite cover and lost by those tests.
- **Significance limit:** an abstract inference obstruction, not a new source theorem. It discharges no RH zero-location premise. External novelty unverified; do not claim significant novel knowledge solely from formalization.
- **Next actual-source conjecture:** the marked Xi subgroup equals D. `[OPEN CORE]`: a source argument must control based transport, beyond independently conjugating every finite packet. No proof currently known here.

## Log

- 2026-10-08: read source declarations; rejected duplicate normal-closure conjecture; derived explicit free-group countermodel and full coset classification. Strengthened to retain the actual primitive-meridian constraint. `HTGeometry/InfinitePacketObstruction.lean` now contains the full example and exact coset action; scratch compilation passes without warnings. Production audits pending.

## Verification

- `lake build --old +GaloisForLFunctions.HTGeometry.InfinitePacketObstruction`: PASS (1019 jobs; only targeted dependency closure).
- Final `lake env lean GaloisForLFunctions/HTGeometry/InfinitePacketObstruction.lean`: PASS, no diagnostics.
- All 28 named public declarations checked using `/tmp/hgt-infinite-packet-axioms.lean`: only `propext`, `Classical.choice`, `Quot.sound`, or no axioms. Capstone `packet_data_do_not_force_equality` has no hypotheses.
- `cosetEquivSheets`, `cosetEquivSheets_x`, `cosetEquivSheets_y` formalize the full positive survivor, including generator actions.
- Umbrella import added once. Index regenerated successfully.
- `scripts/formal_tools.py lint --check-generated`: FAIL outside the new module. Eleven unreachable leaves: RHTower/{ChronologicalOffLineZeroFloor,GammaSiteLeeYangChainXiObstruction,LeeYangChainQuarterTurnZeroCount,MobiusRieszCausalCalculus,PaperPrimeSeamIdealTrace,XiRealRootedEigenLimitRH}; HTGeometry/{ApertureConeCalculus,ApertureConeWinding,ApertureLogTranslation,ApertureOpenHistoryIdeal,BoundaryCoronaCStarAlgebra}. Also LEAN_API/LEAN_OVERVIEW drift after index regeneration. No global-clean claim.
- Evidence logs `/tmp/hgt-infinite-packet-{build,axioms,final,index,lint}.log`.

## Next cycle

Actual source conjecture and its hard obligations continue in `../1-in-progress/xi-single-mark-infinite-cover-exclusion.md`. The completed abstract no-go is not counted as an RH proof or a certified scientific novelty.
