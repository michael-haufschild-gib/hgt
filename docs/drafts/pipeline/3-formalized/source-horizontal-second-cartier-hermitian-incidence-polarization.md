# Second-Cartier Hermitian incidence polarization

- **ID:** source-horizontal-second-cartier-hermitian-incidence-polarization
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean 4)
- **Source:** `source-horizontal-second-cartier-pointed-krein-boundary-relation.md`
- **Claim:** The actual Xi-selected pointed Krein relation has a canonical nonlinear transverse
  boundary shell obtained by fixing the complex unit--ghost incidence. The shell is covariant for
  every nonzero prime character, admits both source orientations and both ghost signs, is
  coefficient- and multiplicity-faithful, is not additive, and carries a strictly positive
  actual-Xi Krein orbit without assuming unit character modulus.

## Public sentence

Physical selection is an invariant orbit shell, not a linear choice of one representative from
each boundary fibre.

## Exact frontier

`[CORPUS]` The pointed jet is `K = C ⊕ C²`, with unit `U=(1,0,0)`, ghost
`G_c=(0,c,c)`, and transfer

\[
T_\lambda(u,a,b)=(\lambda u,S_\lambda(a,b)),\qquad
(S_\lambda(a,b))_+=(\bar\lambda)^{-1}(a+b),
\]

for every `lambda != 0`. The linear boundary relation has exactly `C U` as vertical fibre, retains
the actual Xi coefficient and support multiplicity, and is Krein-isometric for every nonzero
character. A nonzero complex-linear anchor intertwining the ghost and unit weights forces
`|lambda|=1`, hence cannot exist on a strict-right Xi fibre.

`[CORPUS]` Hahn--Jordan source selection is genuinely nonlinear and preserves opposed real source
grades, but it is real/order-valued. It contains no covariance law for the complex prime phase.

`[LITERATURE]` Linear and multivalued unitary boundary relations in Krein spaces are standard
(Derkach--Hassi--Malamud--de Snoo, *Trans. AMS* 358 (2006), 5351--5400). Invariant Hermitian
kernels and `J`-unitary invariants are likewise standard. Opposite-weight torus representations
classically have product invariants. None of these sources provides the present Cartier/Xi
coefficient, divisor multiplicity, or arithmetic prime-character specialization. Exact priority is
unverified.

## Conjecture loop

### C1 -- radial/Jordan transverse section

Select the anchor from `|a+b|` or positive/negative Jordan parts.

**Verdict:** `[FALSIFIED]`. Under prime transfer the ghost sum scales by
`(star lambda)^-1`, so radial data sees only `|lambda|^-1`; Jordan data is not even defined on the
complex phase orbit. Neither transforms by the anchor weight `lambda`. Adding a compensating phase
would fit the Xi character into the definition rather than derive a source law.

### C2 -- nonlinear fixed section

Choose one nonlinear anchor `u=A(v)` and demand equivariance.

**Verdict:** `[FALSIFIED]` in every complex-homogeneous/linear completion by
`sourceHorizontalSecondCartierPointedKrein_anchor_covariance_norm_eq_one`; strict-right Xi fibres
admit none. A general fitted set-theoretic section has no source naturality and is insignificant.

### C3 -- balanced Hermitian incidence shell

Do not choose an anchor. Preserve the opposite-weight complex incidence

\[
I(u,a,b)=u\,\overline{a+b}.
\]

At scale `c`, define the nonlinear polarized boundary relation

\[
\mathcal P_c=\{(v,w)\in\mathcal R_c:
I(w)=\overline{[U,G_c]}=2\bar c\}. \tag{P}
\]

**Verdict:** `[LEAN-PROVED]`. If `r=(bar lambda)^-1`, then

\[
I(T_\lambda w)=\lambda u\,\overline{r(a+b)}
=\lambda u\,\lambda^{-1}\overline{a+b}=I(w),
\]

using only `lambda != 0`. No norm-one condition appears.

## Universal-shadow map

| Existing theorem/failure | Shadow of `(P)` |
|---|---|
| Linear-anchor unitarity firewall | A section separates the opposite weights; `(P)` pairs them before selection. |
| Pointed relation admits all nonzero characters | `(P)` is a level set of its conserved complex matrix coefficient. |
| `G` and `-G` order collision | `(P)` is quadratic and contains the opposite polarized points together, without ordering either. |
| Jordan selection beats grade forgetting | `(P)` is likewise nonlinear, but preserves complex phase rather than projecting to a real order. |
| Full-vertical completed-relation no-go | `(P)` stays in the finite pointed jet and cuts the vertical line to one point whenever source ghost sum is nonzero. |

## Exact theorem

For every `c != 0` and `lambda != 0`:

1. `P_c` is transfer-covariant and source-orientation-swap invariant;
2. its fibre over every source `v` with `c(v_1+v_2) != 0` contains exactly one jet, whose anchor is
   `2 star(c) / star(c(v_1+v_2))`;
3. over forward and inverse source orientations it selects `(2,c,0)` and `(2,0,c)`, exchanged by
   source swap; over the ghost it selects `H_c=U+G_c`, while over the negative ghost it selects
   `-H_c`;
4. both `H_c` and `-H_c` belong to `P_c`, but zero does not, so `P_c` is not additive;
5. `T_lambda H_c` remains in `P_c` and has the same Krein square as `H_c`;
6. for the actual Xi endpoint scale, this square is strictly positive;
7. support-fibre summation of the selected actual polarized ghost restores exact analytic
   multiplicity.

## Paper proof

- Relation membership fixes the last two jet coordinates to `(c v_1,c v_2)`.
- The extra equation is `u star(c(v_1+v_2))=2 star(c)`. When its second factor is nonzero, field
  cancellation gives the displayed unique anchor and direct substitution gives existence.
- At `v=(1,1)`, the anchor is `1`; at `v=(-1,-1)`, it is `-1`.
- At the two basis orientations the anchor is `2`; swap exchanges the two selected points.
- Both opposite points have the same quadratic incidence. Their sum is zero, whose incidence is
  zero, while `2 star(c) != 0`; hence nonadditivity.
- Transfer sends the anchor by `lambda` and the ghost sum by `(star lambda)^-1`. Conjugating the
  latter produces `lambda^-1`, so incidence is invariant. Existing relation covariance supplies
  the other half of membership.
- Swap fixes the ghost sum and anchor, hence fixes incidence and preserves the underlying relation.
- Existing Krein isometry gives square conservation. Direct substitution at `H_c` gives
  `2c+2 star(c)`.
- The actual scale is the complex coercion of the positive real Wold--BV ghost energy; its star is
  itself, so the square is `4c` with positive real part.
- Actual scale is constant on each support fibre. Therefore the polarized ghost is constant there,
  and finite summation multiplies it by the fibre cardinality, already equal to analytic
  multiplicity.

All steps are algebraic and use no RH, same-fibre fixed-star law, moderation, scalar Loewner order,
or unit-character hypothesis. `[PAPER-PROVED]`.

## Hostile falsifiers

- If incidence covariance needs `|lambda|=1`, C3 is circular.
- If the shell is additive or a hidden linear graph, it does not escape the proved firewall.
- If either ghost sign is lost, it is not reflection/orientation faithful.
- If actual positivity uses a fitted scalar rather than the literal Wold--BV scale, it is not
  source-derived.
- If multiplicity is counted in the definition rather than recovered by support-fibre summation,
  it is not coefficient faithful.

## Novelty boundary

The opposite-weight product invariant and nonlinear level set are `[REDISCOVERED]`. The exact
Cartier/Xi realization is `[NOVELTY UNVERIFIED]`. Scientific delta is categorical: corpus now has a
concrete nonlinear physical orbit shell beyond both scalar/moderation firewalls, and the remaining
RH-strength step becomes rigidity/compactness of this shell rather than existence of a nonlinear
receiver.

## Formalization

- Module:
  `GaloisForLFunctions.RHTower.SourceHorizontalSecondCartierHermitianIncidencePolarization`
- Core invariant: `sourceHorizontalSecondCartierKreinHermitianIncidence_transfer`.
- Nonlinear shell: `sourceHorizontalSecondCartierKreinPolarizedBoundary`.
- Genuine nonlinearity:
  `sourceHorizontalSecondCartierKreinPolarizedBoundary_not_additive` and
  `sourceHorizontalSecondCartierKreinPolarizedBoundary_not_submodule`.
- Exact transverse fibre:
  `sourceHorizontalSecondCartierKreinPolarizedBoundary_unique` and
  `sourceHorizontalSecondCartierKreinPolarizedBoundary_existsUnique`.
- Actual Xi endpoint:
  `sourceHorizontalActualXiSecondCartierKreinHermitianPolarization_capstone`.
- Status: scratch and production-file checks passed with `lake env lean`; exact leaf build and
  axiom audit recorded below.

## Log

- 2026-08-18 -- C1 and C2 killed by exact phase-covariance and linear-anchor firewalls.
- 2026-08-18 -- C3 frozen with complete algebraic proof; hostile statement audit in progress.
- 2026-08-18 -- All five hostile falsifiers passed. Abstract invariant classified as rediscovered;
  exact source/Xi theorem promoted to Stage 2 for Lean formalization.
- 2026-08-18 -- Formalized unconditional Hermitian incidence conservation, two orientations,
  opposite signs, exact unique fibre, nonadditivity, no-submodule theorem, actual Xi positivity,
  prime transfer, and divisor multiplicity. Promoted to Stage 3.
