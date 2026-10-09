# Critical-value continuation and connected parameter covering

- **ID:** ORDERED-CRITICAL-VALUE-COVERING-20261009
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean); realization bridge
- **Parent:** `../1-in-progress/finite-planar-polynomial-realization.md`
- **Target:** Restriction of the actual additive-constant map B to distinct ordered critical values is a surjective proper finite covering with path-connected total space. Every collision-free path of critical values has a unique polynomial-parameter lift from each prescribed starting parameter.

## Corpus audit

The documented lexical critical-cover query found the actual properness/local-inverse modules and existing covering adapters. Source inspection verifies `IsProperMap.restrictPreimage` in installed Mathlib `Topology/LocalAtTarget.lean`; no new proper-restriction theorem is needed. `Bottcher/ProperLocalHomeoCovering.lean` proves proper local homeomorphisms are coverings and their fibers finite. `Topology/Homotopy/Lifting.lean` supplies existence and uniqueness of path lifts. The lexical query `holomorphic nonzero locus path connected` returned no declarations; the existing polynomial complement proof suggests the analytic-line extension below. No external sources consulted; external novelty unverified.

## Complete paper proof [PROVED HERE]

Write Cfg for the open set of injective ordered tuples and Reg=B^{-1}(Cfg). Both are open. Regard B as a map Reg→Cfg. Properness survives target restriction by the inspected theorem. Local invertibility holds at every point of Reg because distinct critical values imply distinct critical positions. Composing with the open source inclusion and cancelling the open target inclusion proves the restricted map is a local homeomorphism. The checked proper-local-homeomorphism theorem now makes it a covering. Its fibers are compact by properness and discrete by local invertibility, hence finite. Surjectivity follows by restricting the separately proved surjectivity theorem for B. The inspected covering theorem lifts every continuous path uniquely from each chosen preimage of its initial point. Composing a lift with the source inclusion gives a continuous actual polynomial parameter curve; the polynomial coefficients are continuous along it by the already proved smoothness of every coefficient.

For connectedness, first prove an analytic extension of the corpus polynomial-complement argument. Let E be a complex normed vector space and f:E→C differentiable everywhere. If f(x) and f(y) are nonzero, then g(t)=f(x+t(y−x)) is entire on C and g(0)≠0. The inspected isolated-zero theorem gives a codiscrete nonzero locus, since its alternative g≡0 contradicts g(0)≠0. Thus the zero set is discrete. Every subset of the second-countable plane is Lindelöf, and a discrete Lindelöf subset is countable. The checked countable-complement theorem makes C minus these zeros path connected. Choose a parameter path from 0 to 1 in that complement and compose with the complex affine line. This joins x to y while avoiding f=0. The same proof handles constant affine lines.

Apply this statement to D(v)=∏_{i<j}(B(v)_i−B(v)_j). The actual B is complex smooth, so D is differentiable. Its nonzero locus is exactly Reg. Nonemptiness was proved by finding a local inverse target meeting the dense configuration set. Hence Reg is path connected. Consequently arbitrary two parameters over distinct values can be joined inside Reg, and their image path has that parameter path as its unique lift. In particular the covering's path transport is transitive on each fiber: for two parameters over one configuration, the projected joining path is a loop and its lift joins those parameters.

## Scope

This is continuation of actual polynomials, not yet identification of their covering monodromy with arbitrary prescribed planar transposition data. That identification, collision control, and finite planar completions of actual Xi pieces remain required. No RH implication or uniformization is assumed.

## Lean certificate

`HTGeometry/EntireNonzeroPathConnected.lean` (3 declarations) and `HTGeometry/OrderedCriticalValueCovering.lean` (17 declarations) pass production leaf builds, all 20 standard-only public axiom audits, and final actual-source `lake env lean` checks. Both final logs are empty. Both modules are wired into HTGeometry. The final theorem `OrderedCriticalValueMap.monodromy_regularMap_transitive` uses the actual covering's checked path-lifting monodromy. Its fibers are finite and nonempty, its total space is path connected, and every critical-value path lifts uniquely from a selected parameter.

The entire-function avoidance theorem works on any complex normed vector space, without a finite-dimensional assumption. The critical-value family is an actual application of it, through the product of value differences.

Collision-fiber finiteness and unique continuation endpoints are now fully audited in `ordered-critical-value-collision-fibers.md`. Prescribed polynomial covering monodromy remains a separate unresolved obligation.

- 2026-10-09 — index refresh passed (`/tmp/hgt-critical-covering-index.log`). Authoritative lint reports one unrelated unreachable module, `RHTower.ChronologicalBoundedRowMobiusRigidity`; no own-module or forbidden-declaration errors (`/tmp/hgt-critical-covering-lint.log`).
