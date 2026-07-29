# Pure-pair event fracture, derived connection, and Plebanski bridge (2026-07-28)

Primary card: `docs/drafts/pipeline/1-in-progress/four-dimensional-higgs-event-fracture-law.md`.

## Exceptional pure-pair source

- Baez–Bokor–Boyle, arXiv:2607.10833: bi-Cayley Jordan-pair state space is complex chiral Spin(10) `16`; minimal tripotents are pure quantum states; two collinear minimal tripotents select exact global `G_SM=(SU3×SU2×U1)/Z6`; their common Peirce-half triple is `M_{3,2}(C)`.
- Krasnov, arXiv:2209.05088: same compatible pure-spinor pair selects `R10=R6⊕R4` and aligned Pati–Salam structure. Each spinor determines a maximal isotropic complex 5-plane; compatible pair intersection has dimension 3, leaving relative dimensions 2+2.
- Crucial no-go: pair compatibility/all linear combinations pure is `B1(e1,e2)=0` for the unique vector bilinear `B1:Sym²(16)→10`; compatible pair does not directly yield a nonzero vector10.
- Positive survivor: a transverse deformation has first defect `d/dε|0 B1(e1,e2(ε))∈V10`; this is an event displacement, not the carrier itself.
- Conjecture: `PURE-PAIR ACTUALIZATION LAW`: elementary event is transverse failure of two compatible exceptional pure states to remain jointly Cartan-pure; interface transmits common6, has relative4 kernel, creates Lorentzian coker4. Open core `PURE-PAIR DEFECT TO EVENT INTERFACE`.
- Lean bridge: `HTGeometry/PurePairFiveThreeFracture.lean` proves exact 5/5/3 dimension arithmetic and 6/4 split, without assuming pure-spinor geometry.

## Event complex and connection descent

Local split model: `E_mat=K4⊕I6`, `E_obs=C4⊕I6`, `T(k,i)=(0,i)`. For arbitrary `A_K,A_I,B_C`, choose `A=A_K⊕A_I`, `B=B_C⊕A_I`; then `BT=TA`. Commutators/curvatures remain parallel. Only image connection is transmitted; kernel and cokernel connections are independent. An invertible parallel bridge would instead force conjugacy and lock source/target.

Physical conjecture `EVENT COHOMOLOGY CURVATURE LAW`: kernel curvature→weak; transmitted traceless unitary curvature→color; determinant compatibility in `S(U2×U3)`→hypercharge/EM; Lorentzian coker curvature→gravity; off-diagonal variation→Higgs/solder sector. Distinguish event conversion `η:K→C` (may be nonparallel) from gravitational soldering `e:C→TM`. Open core `EVENT DERIVED CONNECTION`.

Lean bridge: `HTGeometry/EventConnectionDescent.lean`.

## Quaternionic/Plebanski gravity bridge

The outgoing four-coker is the quaternionic `Spin(4)` bidoublet. Bhoja–Krasnov arXiv:2405.15408v2 proves: an SO(3)-covariant SU(2)-structure triple `Σ^i` with `Σ^i∧Σ^j∼δij` determines a Riemannian metric; intrinsic torsion is a unique SO(3) connection; within local intrinsic-torsion-quadratic actions, diffeomorphism + local SO(3) invariance selects one action up to scale, whose critical points are Einstein. This is Riemannian and leading-order only.

New exact Lean module `HTGeometry/EventPlebanskiSimplicity.lean` proves in the actual complex exterior algebra, for a four-coframe:
`Σ1_τ=τ e01+e23`, `Σ2_τ=τ e02−e13`, `Σ3_τ=τ e03+e12`,
`Σi_τ∧Σj_τ=2τ δij vol`; `vol≠0`; triple linearly independent for `τ≠0`; `τ=1` Euclidean quaternionic endpoint, `τ=I` complex chiral endpoint, `τ=0` degenerate. It does not select Lorentzian reality or prove gravity.

Frozen post-freeze conjecture `UNIVERSAL EVENT–EINSTEIN AGREEMENT LAW`: every nondegenerate continuum phase glues event-created four-cokernels; event law selects Lorentzian reality and soldering; leading local invariant mismatch cost is quadratic intrinsic torsion, hence stationary vacuum histories are Lorentzian Einstein spacetimes. Public: “Every quantum event creates its own spacetime. Gravity is the unique way those spacetimes can agree.”

Open core `EVENT PLEBANSKI REALITY AND UNIQUENESS`: derive soldering without prior manifold; select anti-linear Lorentz reality and exactly one time direction; derive required locality/derivative-order/invariance; extend uniqueness to Lorentz slice; derive sourced Einstein/universal free fall; unify all curvature sectors in one exceptional invariant action; obtain finite observable.

Main unresolved blocker remains compact→Lorentz real-form selection. Compatibility of `τ=I` is not selection. No Nature manuscript or empirical claim yet.

## Exceptional cubic actualization survivor

Primary card: `docs/drafts/pipeline/1-in-progress/exceptional-cubic-actualization-law.md`. Frozen public law: “Spacetime is not where quantum events happen. Every quantum event casts a piece of spacetime.” Time and all four forces are conjectured shadows of one event. Conjecture was frozen under truth-hunch-before-proof rule; proof route remains unknown.

Baez–Schwahn flag gives standard orthogonal split `H2(O)=H2(C)⊕C³`. Conditional on a semisimple-core-equivariant rank-six event map whose image is the color `C³`, trace projection has kernel equal to event image, so the cokernel is canonically the nested qubit `H2(C)`, not an arbitrarily chosen four-space. Cubic determinant on `diag(s,X(t,x,y,z))∈H3(C)⊂H3(O)` factors exactly as `s(t²−x²−y²−z²)`.

Lean completion:
- `HTGeometry/EventConnectionDescent.lean`: `splitCokernelProjection_ker_eq_range`, canonical `splitEventCokernelEquiv`, quotient representative classification.
- `HTGeometry/ExceptionalCubicLorentzSlice.lean`: Hermitian complex-corner matrix, exact determinant factorization, primitive-idempotent Lorentz slice, lower-block identification.
Focused builds and formal lint pass; axioms only `propext`, `Classical.choice`, `Quot.sound`.

Do not overclaim: this proves conditional algebraic kinematics only. Open core: select the event map physically; interpret quotient as outgoing event; select Lorentz reality/future; causal composition; separate weak from Lorentz curvature; fix volume; construct soldering; derive unique one-curvature Einstein–Dirac–YM–Higgs IR theory; extract a parameter-reducing prediction.