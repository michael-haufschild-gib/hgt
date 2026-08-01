# Strict nuclear passage of Hodge projectors

- **ID:** `deninger-strict-nuclear-hodge-projector-passage`
- **Stage:** 3-formalized
- **Type:** THEOREM (paper)
- **Label:** `DAC_STRICT_NUCLEAR_HODGE_PROJECTOR_PASSAGE`
- **Parent:** `deninger-arithmetic-calderon-green-intermediate-extension`
- **Statement:** compatible finite-stage Hodge projectors and Green
  identities pass coordinatewise to strict projective limits; they
  pass to restricted direct sums under the exact weighted uniform
  estimates.

## Projective-limit theorem

Let \((E_i,r_{ji})\) be a projective system of Hausdorff locally
convex spaces and let
\[
  E=\varprojlim_i E_i
\]
carry the initial projective-limit topology.  Suppose continuous
linear maps
\[
  P_i:E_i\to E_i
\]
satisfy
\[
  P_i^2=P_i,\qquad r_{ji}P_j=P_ir_{ji}.                       \tag{1}
\]

`[PROVED HERE] [DAC_STRICT_NUCLEAR_HODGE_PROJECTOR_PASSAGE]`

There is a unique continuous projection
\[
  P:E\to E,\qquad P((x_i)_i)=(P_ix_i)_i.                     \tag{2}
\]
Its range is closed and
\[
  \operatorname{ran}P
  \cong
  \varprojlim_i\operatorname{ran}P_i                         \tag{3}
\]
as a topological vector space.

If compatible differentials, codifferentials, and Green operators
\((Q_i,Q_i^\dagger,G_i)\) obey
\[
  1-P_i
  =
  Q_iQ_i^\dagger G_i+Q_i^\dagger Q_iG_i,                    \tag{4}
\]
then their coordinatewise limits obey the same identity on \(E\).

### Proof

Compatibility `(1)` says `(2)` takes compatible families to
compatible families.  Every coordinate map
\(\pi_iP=P_i\pi_i\) is continuous, so initiality of the projective
topology makes \(P\) continuous.  Idempotence is coordinatewise.
Since
\[
  \operatorname{ran}P=\ker(1-P),
\]
the range is closed.  A compatible family lies in
\(\operatorname{ran}P\) exactly when each coordinate lies in
\(\operatorname{ran}P_i\), proving `(3)`.  Equation `(4)` passes
coordinatewise because equality in a projective limit is detected by
all coordinate maps.

## Restricted-direct-sum theorem

Let \(E_i\) carry seminorms \(p_{i,\alpha}\), and let the arithmetic
restricted sum use seminorms
\[
  p_\alpha(x)
  =
  \sum_i w_{i,\alpha}p_{i,\alpha}(x_i),\qquad w_{i,\alpha}>0. \tag{5}
\]
If
\[
  p_{i,\alpha}(P_ix_i)
  \le C_\alpha p_{i,\alpha}(x_i)                             \tag{6}
\]
with \(C_\alpha\) independent of \(i\), then the coordinatewise
projection preserves `(5)` and
\[
  p_\alpha(Px)\le C_\alpha p_\alpha(x).                      \tag{7}
\]
Thus it extends continuously to the completed restricted sum.
Compatible Green identities pass to that completion.  The same proof
works for mixed \(L^1/L^2\) graph seminorms by applying `(6)` in each
channel.

### Proof

Multiply `(6)` by \(w_{i,\alpha}\), sum over \(i\), and use
monotone convergence of the nonnegative seminorm series.  This gives
`(7)`.  Idempotence and the Green identity hold on finite-support
families and extend by density and continuity.

## Arithmetic consequence

The finite Kummer, prime-cusp, and real-apex Hodge projections already
exist.  Therefore the limit problem has only two genuine obligations:

1. prove exact compatibility with every transition,
   residue/corestriction, and Milnor incidence map;
2. prove place-independent bounds `(6)` in every nuclear and mixed
   source seminorm.

Once these hold, no additional abstract limit theorem is missing:
the nuclear source harmonic projector, closed harmonic range, and
Green identity follow from this theorem.

The constants in `(6)` may depend on the seminorm label but not on the
field/place/lattice stage.  Merely having a bounded projector at every
finite stage is insufficient.

For the uncoupled local boundary sum, the required energy estimate is
already uniform: each local Hodge/Dirichlet projector is orthogonal in
its natural energy space, hence
\[
  p_{i,\mathrm{energy}}(P_ix_i)
  \le p_{i,\mathrm{energy}}(x_i)
\]
with \(C_{\mathrm{energy}}=1\), independently of place and packet.
The coordinatewise inequality passes to every weighted
\(L^1/L^2\) sum.  Remaining estimate concerns the
Milnor-incidence and Meyer \(Z\)/Fourier correction of this uncoupled
projector in the full source seminorm family.  The theorem does not
replace corrected global projector by orthogonal local sum.

## Gates

- [x] 0 → 1 in-progress: exact strict-limit statement
- [x] 1 → 2 fully-proven: complete proof
- [x] 2 → 3 formalized
- [ ] 3 → 4 publication-ready

## Log

- 2026-07-27 — Proved projective-limit and restricted-direct-sum
  passage.  Isolated compatibility and weighted uniform estimates as
  the only remaining global projector inputs.
- 2026-08-02 — Formalized both theorems in Lean.

## Lean status

### Both theorems landed

`formal/GaloisForLFunctions/RHTower/DeningerProjectorLimitPassage.lean`.  Axiom audit for all 12
declarations: `propext, Classical.choice, Quot.sound` or less.

Projective-limit theorem:

- `deningerProjectiveLimit` — the limit of a system of topological modules over a preordered index,
  realized as the submodule of compatible families inside the product.  Its topology is the
  subspace topology of the product, which is the initial (projective-limit) topology used in the
  card; local convexity is not needed for any of the statements below, and Hausdorffness enters
  only through `T1Space` in the closed-range claim.
- `deningerCoordinateOperator` — **`(2)`**: compatibility `(1)` makes the coordinatewise family
  preserve compatible families, and the map is continuous because it is the corestriction of a
  product map.  Its coordinates are `deningerCoordinateOperator_apply`.
- `deningerCoordinateOperator_unique` — **the uniqueness in `(2)`**: a continuous linear map on the
  limit is determined by its coordinates.
- `deningerCoordinateOperator_idem` — idempotence is coordinatewise.
- `deningerCoordinateOperator_mem_range_iff` — **`(3)`**: a compatible family lies in the range
  exactly when each coordinate lies in the corresponding stagewise range.  Since both sides carry
  the induced topology of the limit, this membership identity *is* the identification of `ran P`
  with `lim ran P_i` as topological vector spaces.
- `deningerCoordinateOperator_range_isClosed` — the range is closed, being the kernel of `1 - P`.
- `deningerLimitGreen` — **`(4)`**: the Green identity `1 - P = QQ†G + Q†QG` passes verbatim to the
  limit, because equality in a limit is detected coordinatewise.

Restricted-direct-sum theorem:

- `deningerWeightedSum_summable` — a stagewise bound `p_i ≤ C q_i` with `C` independent of the
  stage keeps the weighted sum `(5)` finite, by comparison with the summable majorant.
- `deningerWeightedSum_le` — **`(6)` ⟹ `(7)`**: the same constant bounds the weighted sum
  seminorm, so the coordinatewise projection is continuous for it and extends to the completed
  restricted sum.
- `deningerEnergyProjection_weightedSum_le` — the uncoupled local boundary case named in the card:
  each stagewise energy projection is an orthogonal projection, hence norm nonincreasing, so the
  constant is `1` uniformly in the place and packet, and the weighted `L¹`-of-`L²` sum contracts.

### Remaining

Nothing in the theorem.  Its two named obligations stay open and are not formalization work: exact
compatibility of the actual Kummer, prime-cusp and real-apex projectors with every transition,
residue/corestriction and Milnor incidence map, and place-independent bounds `(6)` in every nuclear
and mixed source seminorm — in particular for the Milnor-incidence and Meyer `Z`/Fourier correction
of the uncoupled projector.
