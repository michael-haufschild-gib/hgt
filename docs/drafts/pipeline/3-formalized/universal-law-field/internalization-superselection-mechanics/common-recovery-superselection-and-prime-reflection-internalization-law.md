# Common-recovery superselection and prime-reflection internalization law

- **ID:** ULF-ISM-1
- **Stage:** 3 — formalized in Lean 4
- **Type:** THEOREM / CROSS-ORGAN INTERNALIZATION CLASSIFICATION
- **Source:** functional-equation packet formation + prime-Poisson source sectors + closed
  source-linear sewing
- **Statement:** Common Markov recovery and every measurable-embedding observer action preserve
  source superselection.  For the reflected prime-Poisson source, recovered measure-class
  equivalence and nonzero closed source-linear internal sewing occur at exactly the same locus,
  `sigma = 1/2`.
- **Status:** `[PAPER-PROVED] [LEAN-FORMALIZED] [DEPENDENCY-CLOSED] [SOURCE-LITERAL]`
  `[FORMATION + INFORMATION + POSITIVITY + INTERNALIZATION] [NOT RH]`
- **Lean:** `HTGeometry.ConstitutiveRecoverySuperselectionInternalization`

## 1. External action versus internal implementation

Let `mu,nu` be finite measures on a measurable source `X`, and let `kappa : X -> Prob(H)` be one
common Markov recovery kernel.  Packet formation is

\[
 \operatorname{Form}_\kappa(\mu)=\mu\otimes\kappa.
 \tag{ISM.1}
\]

This is an **external** operation: it appends conditional history while retaining `X` as the first
coordinate.  Write

\[
 \mu\simeq_{mc}\nu
 \quad\Longleftrightarrow\quad
 \mu\ll\nu\text{ and }\nu\ll\mu
 \tag{ISM.2}
\]

for equality of measure class.  Internal implementation is stricter.  A positive source law gives
its multiplication representation on `L^2(mu)`.  A reflected source symmetry is internally
implemented only when there is a nonzero closed densely defined single-valued relation intertwining
the two source multiplication representations.

The distinction is structural: a stochastic operation may transport two laws while their source
representations remain in disjoint superselection sectors.

## 2. Recovery reflects measure class and singularity

### Theorem 2.1 — common-recovery reflection law

For finite `mu,nu` and a common Markov kernel `kappa`,

\[
 \boxed{
 \operatorname{Form}_\kappa(\mu)\ll\operatorname{Form}_\kappa(\nu)
 \iff \mu\ll\nu,}
 \tag{ISM.3}
\]

and therefore

\[
 \boxed{
 \operatorname{Form}_\kappa(\mu)\simeq_{mc}
 \operatorname{Form}_\kappa(\nu)
 \iff \mu\simeq_{mc}\nu.}
 \tag{ISM.4}
\]

Likewise

\[
 \boxed{
 \operatorname{Form}_\kappa(\mu)\perp
 \operatorname{Form}_\kappa(\nu)
 \iff \mu\perp\nu.}
 \tag{ISM.5}
\]

### Proof

A Markov fibre is nonzero at every source point.  The composition-product absolute-continuity
classification gives `(ISM.3)` for a common nonzero fibre kernel.  Apply it in both directions for
`(ISM.4)`.  The composition-product singularity classification gives `(ISM.5)` under the same
nonzero-fibre condition.  Equivalently, in the forward direction, a base singularity witness `A`
lifts to `A x H`; in the reverse direction common nonzero conditional laws cannot manufacture a
fibre singularity.  `[PROVED]`

This strictly sharpens the earlier KL-isometry statement.  Recovery preserves the entire
Lebesgue-decomposition phase, not only a numerical information distance.

### Theorem 2.2 — lifted actions cannot repair superselection

Let `A : X -> X` be a measurable embedding.  If `mu perp nu`, then after packet formation and the
canonical lifted action,

\[
 \widehat A_\kappa\operatorname{Form}_\kappa(\mu)
 \perp
 \widehat A_\kappa\operatorname{Form}_\kappa(\nu).
 \tag{ISM.6}
\]

### Proof

Formation-action naturality identifies the two lifted laws with
`Form_kappa(map A mu)` and `Form_kappa(map A nu)`.  A measurable embedding preserves mutual
singularity under pushforward.  Equation `(ISM.5)` then preserves it through common recovery.
`[PROVED]`

Thus an information-neutral functional-equation lift is also **superselection-neutral**.  It can
move or re-present a sector; it cannot turn two disjoint source sectors into one internal sector.

## 3. Literal prime-Poisson reflection source

Let `mu_(sigma,t)` be the already constructed ordinary-prime product-Poisson law on the infinite
prime torus.  For `0<sigma<1`, the source theorem proves

\[
 \mu_{\sigma,t}\simeq_{mc}\mu_{1-\sigma,t}
 \iff \sigma={1\over2},
 \tag{ISM.7}
\]

and the two laws are mutually singular off the wall.  The squared local parameter displacement is
the prime-clock reflection energy, and its sum converges exactly at `sigma=1/2`.

### Corollary 3.1 — recovery-invariant prime wall

For every common Markov recovery kernel,

\[
 \boxed{
 \operatorname{Form}_\kappa(\mu_{\sigma,t})\simeq_{mc}
 \operatorname{Form}_\kappa(\mu_{1-\sigma,t})
 \iff \sigma={1\over2}.}
 \tag{ISM.8}
\]

If `sigma != 1/2`, the two formed laws remain mutually singular, including after every common
measurable-embedding lift.  `[PROVED from Theorems 2.1--2.2 and the prime-Poisson Kakutani law]`

## 4. Exact internalization classification

The prime-Poisson source-linear superselection theorem independently proves

\[
 \boxed{
 \operatorname{Sew}(\sigma,t)\ne0
 \iff \sigma={1\over2},}
 \tag{ISM.9}
\]

where `Sew` means a nonzero closed densely defined single-valued relation intertwining the two
continuous prime-source multiplication representations.

### Theorem 4.1 — external/internal capstone

For every `0<sigma<1`, height `t`, and common Markov recovery kernel `kappa`, the following are
equivalent:

1. the reflected recovered packets have the same measure class;
2. the unrecovered reflected prime laws have the same measure class;
3. a nonzero closed source-linear reflected sewing exists;
4. `sigma = 1/2`.

Off wall, every measurable-embedding functional action followed by common recovery preserves
mutual singularity, while every closed source-linear sewing is zero.  At the wall, the two source
laws coincide and the diagonal identity graph supplies nonzero sewing.

### Proof

`(1) iff (2)` is `(ISM.4)`.  `(2) iff (4)` is `(ISM.7)`.  `(3) iff (4)` is `(ISM.9)`.
The off-wall lifted statement is Theorem 2.2; the critical sewing is the identity-graph
construction used in `(ISM.9)`.  `[PROVED]`

## 5. Field consequence

This theorem supplies a coordinate-free distinction that the earlier route vocabulary blurred:

\[
 \boxed{\text{external symmetry} \ne \text{internal source implementation}.}
 \tag{ISM.10}
\]

- Functional equation gives an external involution.
- Common recovery gives an exact stochastic lift and preserves information.
- Positive source laws generate GNS/multiplication sectors.
- Infinite prime formation creates a measure-class superselection wall.
- Internal sewing is the missing lift of the external arrow into the source-representation
  category.

This suggests **internalization superselection mechanics** as one actual field organ: objects are
source-positive representations; external arrows are measurable/stochastic law transports;
internal arrows are provenance-preserving closed correspondences.  Proof routes are different
attempts to internalize the same externally available symmetry.  Their no-gos are not all one
curvature; they are witnesses that the proposed arrow remains external after the route's doctrine
and completion.

The literal prime theorem makes the interpretation falsifiable: any claimed common recovery that
internally sews an off-wall prime sector must violate common-kernel formation, measurable
embedding, closedness, single-valuedness, density, or source-linearity.

## 6. Exact RH handoff and hostile boundary

For a supplied Xi divisor point `rho`, existing Lean proves internal prime-Poisson sewing iff
`Re rho=1/2`.  Therefore RH would follow from the still-open, genuinely source-side statement:

> completed pre-divisor prime--Gamma formation internally implements its external
> functional-equation arrow on every admitted Xi error fibre.

The theorem here does **not** prove that statement.  It proves something necessary and new for the
field architecture: stochastic recovery, KL neutrality, phase recurrence, or external FE symmetry
cannot supply internalization.  A successful producer must construct a nonzero closed
provenance-preserving source correspondence before divisor selection; it cannot be obtained by
adding a common latent kernel.

It also does not identify hypertranscendence with ordinary noncompactness.  Existing asymptotic-type
superselection may refine the morphism class further, but no such implication is used here.

## Gates

- [x] external and internal morphism classes separated
- [x] common recovery shown to reflect absolute continuity and singularity
- [x] lifted measurable actions shown unable to repair singularity
- [x] literal infinite-prime source instantiation
- [x] exact recovered-measure-class/internal-sewing equivalence
- [x] dependency-closed paper proof
- [x] Lean formalization
- [ ] pre-divisor prime--Gamma construction of internal sewing
- [ ] RH selection

## Log

- 2026-08-30 — extracted after the functional-equation packet lift and prime-Poisson
  superselection theorems were compared at mechanism level.  The result identifies common recovery
  as superselection-neutral and makes internal implementability, rather than external symmetry, the
  exact missing source law.
- 2026-08-30 — Lean certifies exact reflection of absolute continuity, measure class, and mutual
  singularity through common Markov recovery; persistence under every measurable-embedding lifted
  action; the literal recovered prime-Poisson critical wall; and equivalence with nonzero closed
  source-linear sewing.  Scratch and direct foreground elaboration pass.  Targeted leaf build
  `GaloisForLFunctions.HTGeometry.ConstitutiveRecoverySuperselectionInternalization` passes
  (`10504/10504`); no umbrella build was run.  Headline axiom prints report only `propext`,
  `Classical.choice`, and `Quot.sound`.  Module is wired into the universal-law umbrella.
