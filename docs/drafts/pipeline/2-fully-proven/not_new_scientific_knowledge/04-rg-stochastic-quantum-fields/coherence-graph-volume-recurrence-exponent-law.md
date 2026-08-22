# Coherence-graph volume and recurrence-exponent law

- **ID:** `coherence-graph-volume-recurrence-exponent-law`
- **Stage:** 2-fully-proven
- **Type:** THEOREM / GRAPH OPTIMALITY / METRIC-DIOPHANTINE BRIDGE
- **Source:** extracted positive survivor from
  `mixed-state-coherence-graph-recurrence-dimension-law.md`
- **Scientific status:** `[PAPER-PROVED] [BRIDGE] [NOT NEW SCIENTIFIC KNOWLEDGE AS
  ABSTRACT DYNAMICS]`
- **Statement:** For every finite positively weighted coherence graph of positive quotient rank,
  `|V|-components` is simultaneously the small-return volume exponent, the worst-spectrum
  recurrence exponent, and the recurrence exponent for almost every fixed spectrum. Rank zero is
  the stationary boundary: the observer energy vanishes identically and the first positive return
  is one.

## Frontier

- `[CORPUS]` `finiteObserverCoherenceGraph_phaseCapacity` proves the exact quotient phase rank
  `r=|V|-c(G)`.
- `[CORPUS]` `exists_finiteQuantumObserver_graphRank_distance_recurrence` proves the universal
  upper deadline with exponent `r`.
- `[LITERATURE]` Dirichlet approximation, torus shrinking targets, Borel--Cantelli, spanning
  forests, and graph Laplacians are established parents.
- `[LITERATURE]` torus-translation shrinking-target behavior is arithmetic for individual
  exceptional translations. The valid fixed-spectrum claim must therefore be almost-everywhere,
  not universal.
- `[LITERATURE]` Dodson, arXiv:0710.4264, reviews the Khintchine--Groshev and Borel--Cantelli
  mechanisms that already determine the almost-every simultaneous-approximation exponent.
- `[LITERATURE]` Rousseau and Saussol, arXiv:0807.0970, relate recurrence of observations to the
  dimension of the pushed-forward measure under strong mixing. Their theorem does not apply to
  torus rotations, but it confirms that observation dimension is the established parent invariant.
- `[LITERATURE]` Chan et al., arXiv:2005.00492, use Kronecker approximation to characterize
  approximate quantum fractional revival on graph Hamiltonians. They do not identify a
  coherence-union quotient rank or prove the weighted minimax exponent below.
- Exact-object search found no source stating the observer-union graph law. Its abstract
  Diophantine mechanism is nevertheless classical, so the result is supporting bridge
  mathematics rather than a novelty claim.

## Exact theorem

Let `G=(V,E)` be a finite graph with positive undirected edge weights `a_e` and
`r=|V|-c(G)>0`. For a matrix-observer family one takes
`a_{ij}=W_{ij}+W_{ji}` on each undirected edge. Put

```text
Phi_a(z)=sum_(e={u,v}) a_e |z_u-z_v|^2,
mu_a(epsilon)=Haar{z in T^V:Phi_a(z)<=epsilon^2}.
```

Choose one spanning forest `F`, let `ell_e` be the number of forest edges in the forest path
joining the endpoints of `e`, and put

```text
K_F=sum_(e in E) a_e ell_e^2.
```

### Theorem `[PAPER-PROVED] [BRIDGE]`

For every `0<epsilon<=2 min(sqrt(K_F), min_(f in F)sqrt(a_f))`,

```text
(epsilon/(pi sqrt(K_F)))^r
 <=mu_a(epsilon)
 <=epsilon^r/(2^r product_(f in F)sqrt(a_f)).              (1)
```

For the least deadline `T_a(epsilon)` that works for every phase vector,

```text
lim_(epsilon->0)
 log T_a(epsilon)/log(1/epsilon)=r.                        (2)
```

For Haar-almost every fixed phase vector `omega`,

```text
lim_(epsilon->0)
 log tau_a(epsilon;omega)/log(1/epsilon)=r,                (3)
```

where `tau_a` is its first positive recurrence clock.

Thus the graph exponent in the corpus upper theorem is necessary, both in the minimax sense and
for almost every fixed spectrum. Exceptional arithmetic spectra may recur faster.

## Paper proof

### Forest coordinates and target volume

Choose one root per component and orient `F` away from the roots. The map

```text
(z_v) -> ((z_root), (z_child/z_parent)_(f in F))
```

is an integer-monomial torus automorphism, with inverse obtained by multiplying ratios along
unique root-to-vertex paths. It preserves normalized Haar measure and has exactly `r` edge-ratio
coordinates.

If every forest chord is at most `delta`, every edge chord is at most `ell_e delta`; therefore
`Phi_a<=K_F delta^2`. Taking `delta=epsilon/sqrt(K_F)` gives the lower inclusion in `(1)`.

Conversely, `Phi_a<=epsilon^2` forces each forest chord to be at most
`epsilon/sqrt(a_f)`. For `0<=delta<=2`, normalized circle Haar satisfies

```text
delta/pi <= Haar{|z-1|<=delta} <=delta/2.
```

Product Haar in forest coordinates gives `(1)`.

### Universal upper exponent

Partition every forest circle into `Q` arcs. Among `Q^r+1` projective orbit points, two occupy
one box. Their difference supplies `1<=n<=Q^r` with every forest chord at most `2pi/Q`.
Consequently,

```text
tau_a(epsilon;omega)
 <=ceil(2pi sqrt(K_F)/epsilon)^r                           (4)
```

for every `omega`.

### Minimax lower exponent

Every positive power map preserves Haar. By `(1)`,

```text
Haar{omega:exists 1<=n<=N, Phi_a(n omega)<=epsilon^2}
 <=N C_F epsilon^r,
```

where `C_F=(2^r product_(f in F)sqrt(a_f))^-1`. Choosing a fixed fraction of
`C_F^-1 epsilon^-r` leaves positive avoiding measure. Together with `(4)`, this proves `(2)`.

### Almost-everywhere fixed-spectrum exponent

For rational `gamma>0`, set `epsilon_n=n^(-1/r-gamma)`. Equation `(1)` and power-map Haar
invariance give a summable series of hit probabilities. The first Borel--Cantelli lemma implies
that almost every `omega` satisfies

```text
Phi_a(n omega)>epsilon_n^2
```

for all sufficiently large `n`. Phase vectors with an exact positive return form a countable
union of proper torsion subtori and have Haar measure zero. Hence
`tau_a(epsilon;omega)->infinity` for almost every `omega`. If
`n=tau_a(epsilon;omega)` is large, the Borel--Cantelli inequality forces

```text
n>epsilon^(-r/(1+r gamma)).
```

Intersect over positive rational `gamma` and combine with `(4)` to obtain `(3)`.

### Rank-zero boundary

If `r=0`, every component is a singleton, hence `E` is empty and `Phi_a=0`.
Therefore `mu_a(epsilon)=1` for every positive `epsilon` and
`T_a(epsilon)=tau_a(epsilon;omega)=1`. This boundary is excluded from
`(1)`--`(3)` because their logarithmic denominator describes a positive-dimensional
shrinking target.

## Hostile attack

1. **“Every fixed Hamiltonian has exponent `r`.”** `FALSIFIED`; commensurate spectra can be
   periodic. The exact survivor is the almost-everywhere theorem `(3)` plus universal upper and
   minimax equality.
2. **“This is a new shrinking-target theorem.”** `REDISCOVERED` as abstract dynamics. The
   quantum delta is that observer-union coherence components determine the target codimension and
   therefore the recurrence exponent. The manuscript must cite the parent theory and must not score
   the exponent mechanism itself as novelty.
3. **“Weak added edges cause a discontinuous practical exponent.”** At fixed resolution they
   affect constants and cross over only below their weight scale. The asymptotic exponent is a
   high-resolution statement.
4. **“Hilbert--Schmidt distance is operational.”** Not established by this card; a separate
   operational transfer theorem is required.

Verdict: `SURVIVES AS A SUPPORTING BRIDGE`. `[OPEN CORE]` is exact Lean formalization of
`(1)`--`(3)` and the rank-zero boundary.

## Gates

- [x] 0 → 1: exact theorem and dependency-closed paper proof
- [x] 1 → 2: exact-object literature audit and formal statement normalization
- [ ] 2 → 3: unconditional Lean theorem and axiom audit
- [ ] 3 → 4: integrate only after operational transfer theorem is proved
