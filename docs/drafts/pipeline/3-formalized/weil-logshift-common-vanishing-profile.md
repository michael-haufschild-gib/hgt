# Common vanishing profile for regular amplitudes and their sensitivity

Status: FORMALIZED. Dependency-closed paper proof and four public Lean theorems verified.

## Corpus question

Does the finite-dimensional `C₀` operator admit a single nonnegative vanishing profile controlling every amplitude, rather than only a constant operator-norm bound? Can the same profile control differences on native regular affine fibres?

Only local Lean sources were consulted. The lexical corpus search for uniform vanishing envelopes and finite-dimensional operators found the common normalization and `C₀` receiver. Exhaustive targeted source searches found no existing matching finite-dimensional `C₀` profile theorem. Installed mathlib sources supply basis coordinates, finite sums, continuity, and cocompact limits.

## Dependency-closed proof

Let E be a finite-dimensional real normed space, X any topological space, and S:E→linear C₀(X,Real). Choose a finite basis b and C equal to the operator norm of its continuous coordinate map. Then every coordinate satisfies abs(coord_i(a))<=C norm(a). Define

g(x) = C sum_i abs(S(b_i)(x)).

Every basis image is continuous and vanishes at infinity. Absolute values, a finite sum, and multiplication by C preserve both properties, so g belongs to `C₀`; it is nonnegative. Expand S(a) in this basis and apply the triangle inequality to obtain abs(S(a)(x))<=norm(a) g(x). This works for every linear S; no separate continuity assumption on S is necessary.

For a finite-dimensional affine coefficient family F, homogenize as in the existing common-operator theorem: H(a,t)=F.linear(a)+t F(0). Its actual regular subspace is finite dimensional. Apply the generic profile result to the normalized `C₀` operator on that subspace. The lift of each regular amplitude is (a,1), of norm at most 1+norm(a), and differences of lifts have norm exactly norm(a-b). Therefore the actual normalized receiver Phi satisfies

- abs(Phi(a)(y)) <= (1+norm(a)) g(y);
- abs(Phi(a)(y)-Phi(b)(y)) <= norm(a-b) g(y).

Use the same origin-kernel unweighting as the prior native receiver to identify regular coefficient amplitudes with bounded-history amplitudes regular at some shift. All series contracts retain `HasSum`.

For any real radius R and epsilon>0, (1+max(R,0))g(y) tends to zero along the cocompact filter. Eventually it is below epsilon. The two inequalities above then simultaneously give uniform smallness of all values with norm(a)<=R and all differences with norm(a-b)<=R. The difference statement imposes no bound on the base amplitudes themselves. Empty regular fibres require no extra premise.

## Intended artifacts

- `WeilLogShiftC0VanishingEnvelope.lean`: generic finite-dimensional linear envelope and common affine coefficient profile.
- `WeilLogShiftVanishingProfileReceiver.lean`: native history profile and simultaneous uniform tail/sensitivity theorem.

## Verification log

Pending local API checks, direct leaf compile/export, axiom audit, umbrella wiring, indexing, and formal lint. No external sources, numerical experiments, additional axioms, or unproved analytic premises.

Local API scratch passed after marking basis-construction examples noncomputable. `WeilLogShiftC0VanishingEnvelope.lean` passed direct compile/export cleanly. The generic result needs only a linear map into C0 and works over any topological parameter space X. Native receiver compile is pending.

Native profile and joint uniform-tail/sensitivity leaf compiled/exported cleanly after replacing one addition-order-sensitive radius estimate with `linarith only [ha, le_max_left R (0 : Real)]`. Both owned leaves now pass direct checks; four-theorem axiom audit is running.

## Final checkpoint

- Both direct `lake --old env lean` leaf compile/export checks exited 0 with clean logs. Fresh oleans verified.
- All four public theorem axiom audits contain exactly `propext`, `Classical.choice`, `Quot.sound`.
- Both umbrella imports unique. Index refresh exited 0; all four theorems indexed exactly once in their expected modules.
- Fresh formal lint exited 1 with six unrelated unreachable modules: `RHTower.BaezDuarteBurnolMultiplicity`, `HTGeometry.PaperGenericMinorNormalRelations`, `HTGeometry.PaperHankelNormalRelations`, `HTGeometry.PaperSquareRankNormalRelations`, `HTGeometry.PaperVeroneseNormalRelations`, and `HTGeometry.QKrawtchoukCompanionTriangular`. No owned-leaf errors or proof debt.
- No full builds, external sources, numerical experiments, additional axioms, or heartbeat changes.

Public results: `exists_finiteDimensional_c0_vanishing_envelope`, `exists_weilLogShift_affine_vanishing_profile`, `exists_weilLogShift_history_vanishing_profile`, and `exists_weilLogShift_history_uniform_vanishing_and_sensitivity`.

Exact new insight: the whole finite-dimensional regular family is controlled by one nonnegative function vanishing at infinity. The same function controls differences. Consequently, one fixed normalization has uniform decay over every bounded regular amplitude set and uniform decay of response differences over every bounded amplitude separation, even when the base amplitudes themselves are unbounded. All series contracts retain `HasSum`.

The profile is not claimed optimal, and no explicit shift-decay rate is asserted. A next conjecture is to promote pointwise evaluation of a finite-dimensional `C₀` operator to a `C₀` family of continuous linear functionals. Its operator norm would provide a basis-independent sharp profile for a fixed operator. This has not yet been corpus-audited or formalized; investigate local APIs and existing results before new code.
