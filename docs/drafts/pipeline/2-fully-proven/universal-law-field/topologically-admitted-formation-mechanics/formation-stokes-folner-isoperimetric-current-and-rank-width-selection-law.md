# Formation Stokes/Følner isoperimetric current and rank-width selection

- **ID:** ULF-TAFM-10
- **Stage:** 2-fully-proven
- **Type:** THEOREM PACKAGE
- **Source:** ULF-TAFM Laws VI, X, XIII, XIV; finite determinant-flux exactness; source-boundary
  route organs
- **Status:** dependency-closed paper proof; Lean formalisation complete

## 1. Result

A locally formed bulk character on a finite directed packet is exactly a cut-boundary flux. Its
absolute value is bounded by positive boundary traffic. Consequently:

- uniform local edge capacity on a formation Følner family forces neutral bulk character;
- a nonzero character forces inverse-isoperimetric blow-up of some boundary edge current;
- on rank-`d`, width-`w` box packets, nonzero character forces positive rank density `d/w`.

This supplies a generative mechanism for the traffic properness used in ULF-TAFM-9. It does not ask
for one global potential, pointwise zero carry, or a postulated local traffic ceiling. It derives
sublinear total traffic from local conservation plus vanishing boundary density.

## 2. Finite formation packet

Let `V,E` be finite types, let `t,h:E→V` be tail and head maps, let `J:E→ℝ` be an oriented edge
current, and let `S⊂V` be a finite observed interior. Define

`div J(v) = Σ_{h(e)=v} J(e) - Σ_{t(e)=v} J(e)`.                    `(10.1)`

Write `1_S` for the indicator of `S` and put

`δ_S(e)=1_S(h(e))-1_S(t(e))`.                                     `(10.2)`

The cut flux, positive cut traffic, and edge boundary are

`Flux_S(J)=Σ_e δ_S(e)J(e)`,                                       `(10.3)`

`Traffic_S(J)=Σ_e |δ_S(e)J(e)|`,                                  `(10.4)`

`∂_E S={e : (h(e)∈S)≠(t(e)∈S)}`.                                 `(10.5)`

The definitions allow loops, multiple edges, disconnected packets, and arbitrary current signs.

## 3. Exact cut Stokes law

### Theorem 10.1 — finite formation Stokes identity

For every finite packet,

`Σ_{v∈S} div J(v)=Flux_S(J)`.                                     `(10.6)`

### Proof

Expand `(10.1)` and exchange the two finite sums. For each edge `e`, the incoming sum contributes
`J(e)` exactly when `h(e)∈S`, and the outgoing sum contributes `J(e)` exactly when `t(e)∈S`.
Its total coefficient is therefore `δ_S(e)`. Summing over edges gives `(10.6)`. Internal edges have
coefficient `1-1=0`; external edges have coefficient `0-0=0`; loops cancel identically. No
connectivity premise is used. ∎

### Theorem 10.2 — traffic domination and exact cut support

One has

`|Flux_S(J)|≤Traffic_S(J)=Σ_{e∈∂_E S}|J(e)|`.                      `(10.7)`

If `M≥0` and `|J(e)|≤M` for every edge, then

`Traffic_S(J)≤M |∂_E S|`.                                        `(10.8)`

### Proof

The first inequality is the triangle inequality for the finite sum `(10.3)`. The coefficient
`δ_S(e)` is zero when the two endpoint-membership values agree, and is `1` or `-1` when they differ.
Thus `|δ_S(e)J(e)|` is respectively `0` or `|J(e)|`, proving the equality in `(10.7)`. Summing the
edgewise bound `|J(e)|≤M` over `∂_E S` proves `(10.8)`. ∎

## 4. Bulk current and Cheeger bound

### Theorem 10.3 — bulk current is bounded by boundary capacity

If `div J(v)=χ` for every `v∈S`, then

`|S||χ|≤Traffic_S(J)`.                                            `(10.9)`

Under the uniform edge bound of Theorem 10.2,

`|S||χ|≤M|∂_E S|`.                                                `(10.10)`

### Proof

The left side of `(10.6)` is `|S|χ`. Taking absolute values and using `(10.7)` gives `(10.9)`;
then apply `(10.8)`. ∎

For `|S|>0`, `(10.10)` is the formation Cheeger inequality

`|χ|≤M |∂_E S|/|S|`.                                              `(10.11)`

It is an upper bound on sustainable bulk character, not an ordinary spectral Cheeger inequality.

## 5. Følner selection and positive survivor

### Theorem 10.4 — formation Følner selection

Fix `χ∈ℝ` and `M≥0`. Suppose a family of finite formation packets satisfies the hypotheses of
Theorem 10.3 with the same `χ,M`, and has the following weighted Følner property:

for every `ε>0`, some packet satisfies

`M|∂_E S|<ε|S|`.                                                   `(10.12)`

Then `χ=0`.

### Proof

If `χ≠0`, take `ε=|χ|>0` in `(10.12)`. The selected packet satisfies

`|S||χ|≤M|∂_E S|<|χ||S|`,

a contradiction. ∎

The usual conditions `|S|>0`, `|∂_E S|/|S|→0`, and a fixed finite `M` imply `(10.12)`.

### Theorem 10.5 — inverse-isoperimetric current blow-up

Suppose `χ≠0`, `S` is nonempty, and `div J=χ` on `S`. Then `∂_E S` is nonempty and

`max_e |J(e)| ≥ |S||χ|/|∂_E S|`.                                 `(10.13)`

More generally, any common edge bound `M` obeys the same lower bound.

### Proof

If `∂_E S` were empty, `(10.9)` would give the positive number `|S||χ|≤0`, impossible. For a
nonempty boundary, `(10.10)` gives `|S||χ|≤M|∂_E S|`; divide by the positive boundary cardinality.
Taking `M=max_e|J(e)|` is legal for a finite boundary. ∎

Thus failure of selection has a quantitative positive survivor: boundary current must diverge at
least as inverse formation-isoperimetric ratio.

## 6. Rank-width law

Consider a legal rank-`d`, width-`w` box packet, with `d,w>0`, bulk cardinality `w^d`, and boundary
port count at most `2d w^(d-1)`. The latter is the sum of the two codimension-one faces in each of
the `d` directions.

### Theorem 10.6 — box rank-width current bound

Under a uniform edge-current bound `M≥0`,

`w|χ|≤2Md`.                                                        `(10.14)`

### Proof

Theorem 10.3 gives

`w^d|χ|≤2Md w^(d-1)`.

Since `w,d>0`, `w^(d-1)>0` and `w^d=w·w^(d-1)`. Cancel the positive common factor to obtain
`(10.14)`. ∎

### Corollary 10.7 — sublinear rank selects neutrality

For any family of such boxes with fixed `χ,M`, if for every `ε>0` some packet satisfies

`2Md<εw`,                                                           `(10.15)`

then `χ=0`. In particular, `d/w→0` forces neutrality.

### Proof

Assume `χ≠0`, set `ε=|χ|`, and combine `(10.14)` with `(10.15)`. ∎

If `M>0`, `(10.14)` also gives the positive survivor

`d/w≥|χ|/(2M)`.                                                    `(10.16)`

Unbounded channel rank alone therefore does not cause noncompactness. Off-neutrality requires rank
at least linear in legal packet width, unless local current capacity itself diverges.

## 7. Formation isoperimetric profile

For a formation doctrine `D`, source grade `a`, and volume threshold `N`, define conceptually

`h_D(a,N)=inf Traffic_S(J)/|S|`,                                   `(10.17)`

where the infimum ranges over legal observer-closed packets for `a` with `|S|≥N` and exact local
bulk current. Then `(10.9)` implies

`|χ(a)|≤h_D(a,N)`                                                  `(10.18)`

for every `N` for which the admissible class is nonempty. A cofinal vanishing profile selects
neutrality. A positive profile classifies where open lifted history survives closed observation.

The formal core uses the equivalent quantified packet inequalities and does not require
completeness facts about the infimum.

## 8. Relation to ULF-TAFM-9

ULF-TAFM-9 assumes absolute carry traffic is uniformly bounded on one compact-phase ball. The
present theorem supplies a weaker asymptotic mechanism. If legal near-identity return words admit
local packets with uniformly bounded edge currents and vanishing boundary density, their total
boundary traffic is sublinear in packet volume. Exact bulk current grows linearly, so it vanishes.

Thus the source producer is no longer “construct a global potential” or “prove every carry is
zero.” It is:

1. construct a divisor-independent local formation complex;
2. prove bulk current is its divergence;
3. prove a uniform local edge-current bound;
4. exhibit observer-closed Følner packets.

Each failure has a different mathematical signature and cannot be hidden inside one existential
map.

## 9. Cross-organ meaning

- **Packet/carry:** positive traffic is total variation of cut current.
- **Recurrence:** visible phase closure permits long observer-closed packets; lifted history remains
  as boundary flux.
- **Positivity:** absolute value quotients oriented flux into nonnegative traffic without erasing its
  lower bound.
- **Hypertranscendence:** independent channel rank affects formation boundary density through the
  rank-width ratio, not by mere infinitude.
- **No-go theorems:** compactness, BV, graph-domain, and normal-family failures become evidence that
  local capacity or formation Cheeger density cannot vanish in that gauge.
- **Selection:** vanishing source formation profile annihilates the real character before any zero
  receiver is chosen.

## 10. Hostile audit

1. Internal cycles and loops cancel from flux but may contribute microscopic traffic away from the
   cut; the theorem claims only cut traffic.
2. Boundary sign cancellation cannot defeat `(10.9)` because `(10.7)` takes total variation after
   exact oriented conservation.
3. No connectivity assumption is present.
4. Finite Stokes exactness uses no amenability, recurrence, topology, or RH.
5. Følnerness without uniform local capacity does not select; current may grow on sparse boundary.
6. Uniform capacity without vanishing boundary density does not select.
7. Rank may grow without obstruction when width grows faster. Hypertranscendence is not identified
   with noncompactness.
8. Existing multiplicative determinant-flux exactness is compatible but does not contain the real
   cut variation, isoperimetric, Følner, or rank-width laws.
9. Route-specific seam-flux estimates can instantiate the local-capacity side, but no such
   instantiation is assumed here.
10. No RH claim is made. Literal arithmetic formation locality and a uniform source edge bound
    remain open.

## 11. Dependency audit

- Theorems 10.1--10.3: finite sums, indicators, triangle inequality, cardinality of a constant sum.
- Theorem 10.4: contradiction using the quantified weighted Følner property.
- Theorem 10.5: positivity and division by a positive finite cardinality.
- Theorems 10.6--10.7: natural-power identity, positive cancellation, and the quantified
  rank-width property.

All dependencies are elementary and unconditional. No hidden compactness, density, zero-location,
or analytic convergence premise occurs.

## 12. Literature boundary

The standard parents are finite network divergence, Følner amenability, Cheeger/isoperimetric
profiles, discrete BV/Wulff theory, and bounded cohomology. Quantitative nearby work includes
<https://arxiv.org/abs/2402.16787> and <https://arxiv.org/abs/2509.22260>. The theorem package fuses
these ingredients with formation current, positive carry traffic, observer closure, and
rank-width selection. No novelty criterion is imposed.

## Gates

- [x] 0 → 1: mechanism frozen after corpus and primary-literature audit
- [x] 1 → 2: dependency-closed finite Stokes, traffic, Følner selection, and rank-width proofs
- [x] 2 → 3: Lean formalisation including missing additive cut-flux infrastructure
- [ ] 3 → 4: literal source packet functor and arithmetic uniform-current estimate
