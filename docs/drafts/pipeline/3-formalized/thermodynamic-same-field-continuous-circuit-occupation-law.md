# Thermodynamic same-field continuous-circuit occupation law

- **ID:** thermodynamic-same-field-continuous-circuit-occupation-law
- **Stage:** 3-formalized
- **Type:** FORMALIZED
- **Source:** corpus-wide recurrence/complexity audit, 2026-08-27
- **Statement:** One countable absolutely summable static nearest-neighbour qubit Pauli field has vanishing upper completed-time operator-norm occupation of the complete global-phase-saturated continuous two-qubit circuit image at gate budget `2^n / (64 (n+1))` on every literal prefix.  These are the same compatible prefixes that already realize recurrence, hard excursions, a paired-prefix laboratory ramp, diverging consecutive-return gaps and UHF convergence.

## Goal

Upgrade finite-alphabet polynomial-depth occupation extinction to the physically standard continuous `SU(4)` two-qubit gate model at a near-Hilbert gate budget.  The Hamiltonian field must be selected once, before system size, time, circuit architecture, and gate parameters.  Result must be a frequency law, not only existence of hard intervals.

## Literature boundary

- Oszmaniec--Kotowski--Horodecki--Hunter-Jones prove saturation and recurrence for random local circuits and stochastic local Hamiltonian evolution, not deterministic evolution of one compatible time-independent nearest-neighbour field.
- Kotowski--Oszmaniec prove finite-dimensional recurrence-time bounds and generic saturation for random Hamiltonians, not completed-time occupation of the full continuous low-circuit image for one static local thermodynamic family.
- Dumas--Fischler give quantitative torus filling under Diophantine conditions, without local-Hamiltonian synthesis or continuous-circuit target entropy.
- Corpus already proves near-Hilbert continuous-circuit hard excursions and consecutive re-entry on one field, and separately finite-alphabet polynomial-depth completed-time occupation extinction.  Search found no continuous-circuit completed-time occupation theorem, either per prefix or on the compatible field.
- Primary-source search found no exact deterministic static-local same-field occupation theorem.  This is bounded absence evidence, not proof of priority.

## Exact frontier labels

- `[CORPUS]` `eventually_nearHilbertContinuousCircuitEntropy_lt_projectiveBooleanCarrier` gives fixed-resolution entropy strictly below `2^(2^n-1)` at gate budget `s_n = 2^n / (64(n+1))`.
- `[CORPUS]` `maximallyProjective_unitaryEvolution_continuousCircuitTarget_consecutiveVisitGaps_of_entropy` gives genuine continuous-circuit excursions and re-entry, but no occupation frequency.
- `[CORPUS]` `exists_thermodynamicSameFieldPolynomialCircuitPlateauLaw` gives completed-time occupation extinction only for every fixed finite alphabet and polynomial word budget.
- `[LITERATURE]` Oszmaniec--Kotowski--Horodecki--Hunter-Jones, PRX 14 (2024), prove saturation and recurrence for random local circuits and stochastic time-dependent local Hamiltonians.  Their paper states that a specific time-independent Hamiltonian remains out of reach.
- `[LITERATURE]` Kotowski--Oszmaniec, arXiv:2601.10409v3 (3 August 2026), prove finite-dimensional recurrence bounds and random-Hamiltonian saturation, not low-circuit occupation for a deterministic local field.
- `[LITERATURE]` Cui--Schuster--Mao--Huang--Brandao, arXiv:2510.08434, prove constant-local time-independent Hamiltonian ensembles fail Haar `2`-design/PRU tests.  This neither implies nor obstructs occupation extinction on the Hamiltonian's spectral torus.
- **Exact residue:** no checked source or corpus theorem gives a completed-time upper density for the full continuous `SU(4)` two-qubit circuit image of one compatible deterministic time-independent bounded-degree field.
- **Hostile verdict:** `SURVIVES PRELIMINARY ATTACK`.  Priority remains provisional pending independent expert review.

## Conjecture C1 — strengthened and frozen

For `d = 2^n - 1`, `s_n = 2^n / (64(n+1))`, and the complete phase-saturated image `K_{n,s_n}` of all continuous two-qubit circuits with at most `s_n` gates, define

`A_{n,eps} = {x in T^d | infDist(P_V(x), K_{n,s_n}) <= eps}`.

At fixed `eps = 1/20`, every maximally projective spectrum obeys

`limsup_T occupation_T(A_{n,eps}) <= E(n,s_n) * q^d`,

where

`q = 2 asin(3/5) / pi < 1/2`

and `E` is the existing quarter-net entropy.  Consequently

`E(n,s_n) q^(2^n-1) -> 0`.

There exists one field `p` satisfying the complete recurrence-desert/UHF lifecycle such that this bound holds for the canonical physical eigenbasis of every literal `(k+3)`-qubit prefix, with `n=k+3`.  No coefficient, Hamiltonian, circuit architecture or gate parameter is redrawn when `k` changes.

## Dependency-closed paper proof

Let `P_{e,V}: T^d -> U(2^n)` be the zero-anchored spectral matrix map, with `d+1=2^n`.  Let `K_{n,s}` be the image of all circuits of at most `s` arbitrary `SU(4)` two-qubit gates, saturated by every unit global phase.  Define

`A(e,V,s) = {x : infDist(P_{e,V}(x), K_{n,s}) <= 1/20}`.

The set is closed because `K_{n,s}` is compact, distance to a compact set is continuous and `P_{e,V}` is continuous.

### 1. Replace the continuous circuit image by one finite net

The existing quarter-net theorem supplies a finite set `N_{n,s}` such that every circuit matrix `C` of gate count at most `s` is within operator distance `1/4` of some `W in N_{n,s}`, and

`|N_{n,s}| <= E(n,s)`.

If `x in A(e,V,s)`, compactness of `K_{n,s}` realizes the infimum: some unit scalar `c` and circuit `C` satisfy

`||P_{e,V}(x) - c C|| <= 1/20`.

Choose `W in N_{n,s}` with `||C-W|| <= 1/4`.  Since `|c|=1`,

`||P_{e,V}(x)-cW|| <= 1/20+1/4 = 3/10`.

Thus `A(e,V,s)` is contained in the union, over `W in N_{n,s}`, of phase-saturated one-centre tubes `T_W(3/10)`.

### 2. One-centre tube lemma

For general `r>=0`, suppose `x,y in T_W(r)`.  Choose unit scalars `c_x,c_y` with

`||P(x)-c_x W|| <= r`, `||P(y)-c_y W|| <= r`,

and put `z=c_x/c_y`.  Then `|z|=1` and the triangle inequality gives

`||P(x)-zP(y)|| <= 2r`.

Conjugating by `V` does not change operator norm.  The matrix becomes diagonal, so every diagonal coordinate has modulus at most `2r`.  The zero-anchored coordinate is `1`; hence `|1-z|<=2r`.  Each non-anchor coordinate then satisfies

`|exp(ix_j)-exp(iy_j)|`
`<= |exp(ix_j)-z exp(iy_j)| + |z-1| <= 4r`.

Therefore `x-y` lies in the anchored coordinatewise chord target

`B_{4r}={u : |exp(iu_j)-1|<=4r for every j}`.

If the tube is nonempty, fix `y` in it.  Translation invariance of Haar measure gives

`mu(T_W(r)) <= mu(B_{4r})`.

If it is empty, the same inequality is trivial.  For `4r<2`, the exact product-Haar formula is

`mu(B_{4r}) = [2 asin((4r)/2)/pi]^d`.

At `r=3/10`, this is `q^d` with `q=2 asin(3/5)/pi`.

### 3. Continuous-circuit occupation bound

Finite subadditivity and the net-cardinality bound give

`mu(A(e,V,s)) <= E(n,s) q^d`.

For a maximally projective energy list, anchored gaps are rationally independent, so centered physical-time phase laws converge weakly to Haar measure on `T^d`.  Since `A(e,V,s)` is closed, the closed-set half of Portmanteau gives

`limsup_{T->infinity} occupation_T(A(e,V,s)) <= mu(A(e,V,s))`
`<= E(n,s) q^d`.

No boundary-null, chaos, random-matrix, circuit-genericity or time-averaging hypothesis is added.

### 4. Near-Hilbert thermodynamic decay

Set `s_n = floor(2^n/(64(n+1)))` and `d_n=2^n-1`.  The existing entropy theorem gives, eventually,

`E(n,s_n) < 2^d_n`.

Moreover `q>=0` and `2q<1`: `3/5 < sin(pi/4)=sqrt(2)/2`, so monotonicity of `asin` on `[-1,1]` gives `asin(3/5)<pi/4`.  Hence

`0 <= E(n,s_n)q^d_n < (2q)^d_n -> 0`,

because `d_n -> infinity`.  This proves the claimed vanishing envelope.

### 5. One physical field, every literal prefix

The existing unconditional lifecycle theorem selects one countable absolutely summable static nearest-neighbour Pauli coefficient field `p`.  Every literal `(k+3)`-qubit restriction has a maximally projective canonical spectrum and is the literal partial sum of the same field.  Apply Step 3 with `n=k+3`, `d=2^(k+3)-1`, the canonical eigenvalue enumeration and canonical unitary eigenbasis of that physical prefix.  The spectral representation of `exp(-itH_k)` differs from `P_{e,V}` only by the anchor eigenphase, already absorbed by `K_{n,s}`'s global-phase saturation.  Therefore the phase occupation is exactly the physical operator-norm occupation near all circuits of at most `s_n` gates.

Since `k -> k+3` is cofinal, Step 4 gives vanishing cost along every literal prefix.  Conjoining this property with the already discharged recurrence-desert lifecycle yields one existential theorem with no caller-supplied hypothesis.

## Hostile proof audit

- **Uncountable circuit family:** paid once by a finite metric net; no invalid union bound over gate parameters.
- **Global phase:** retained throughout and eliminated only by a proved anchor estimate; no determinant gauge is assumed observable.
- **Eigenbasis dependence:** finite bound is uniform in `V`; physical capstone specializes to canonical eigenbasis of actual local Hamiltonian.
- **Target boundary:** only closed-set limsup is claimed; no unsupported boundary-zero assertion.
- **Thermodynamic order:** complete centered-time limit is taken separately at each finite prefix before `k -> infinity`.
- **Haar overclaim:** Haar measure is only on spectral phase torus, not full unitary group; result is compatible with static-Hamiltonian non-Haar theorems.
- **Plateau overclaim:** theorem proves asymptotically vanishing upper occupation, not pointwise monotonicity or a contiguous plateau covering all late times.
- **Locality:** final field uses onsite and nearest-neighbour Pauli terms on one static one-dimensional path; coefficients are selected once.
- **Exact physical bridge:** global-phase saturation converts zero-anchored spectral capture to operator-norm circuit capture of `exp(-itH_k)` without changing tolerance.

`[PAPER-PROVED]`: exact statement and dependency-closed proof survive hostile audit.  Lean formalization must copy this statement without weakening.

## Proof architecture

1. Cover every continuous circuit by the existing operator-norm quarter net.
2. Enlarge capture radius from `1/20` to `3/10` around one phase-saturated net point.
3. Prove a new one-center projective tube lemma: any nonempty radius-`r` tube lies in a translate of the anchored chord target of radius `4r`.
4. Use exact Haar measure of the anchored target and finite-union subadditivity.
5. Transfer Haar bound to completed-time upper occupation by maximal-projective equidistribution.
6. Combine the public near-Hilbert entropy inequality with `4 asin(3/5)/pi < 1` to prove thermodynamic decay.
7. Specialize to the one existing compatible countable local field.

## Proof obligations

- [x] compact/closed phase-saturated one-center tube — paper proof closed
- [x] one-center tube containment in translated anchored chord target — paper proof closed
- [x] one-center exact Haar upper bound — paper proof closed
- [x] full continuous-circuit tube finite-net union bound — paper proof closed
- [x] completed-time upper occupation theorem for every maximally projective finite spectrum — paper proof closed
- [x] near-Hilbert entropy-times-volume limit — paper proof closed
- [x] same-field thermodynamic capstone — paper proof closed
- [x] targeted source checks, final module build, axiom audit, umbrella wiring, lint
- [x] paper replacement and experimental consequence audit

## No-go pivots

- If radius `4r` loses exponential margin against the existing entropy carrier, reduce circuit capture error or refine net radius using the general continuous-circuit metric-entropy theorem.
- If direct global-phase tube containment is topologically awkward, prove disjointness of Boolean translates of a one-center tube at `2r < 1`; Haar packing gives the stronger `2^{-d}` bound.
- If same-field eigenbasis transport is the only obstruction, first close the generic finite-dimensional physical theorem and then add the canonical orthonormal-eigenbasis bridge rather than weakening circuit model.

## Log

- 2026-08-27 — created in 1-in-progress after mandatory corpus and primary-literature audit; C1 active.
- 2026-08-27 — exact-conjecture corpus and primary-source audit repeated.  Strengthened from paired prefixes to every literal prefix.  Closed paper proof and hostile audit; finite and thermodynamic formalization remain.
- 2026-08-27 — formalized the generic completed-time law, exact physical operator-norm bridge, near-Hilbert thermodynamic decay, and one-field capstone.  Targeted source checks and targeted capstone build passed.  Axiom audit reports only `propext`, `Classical.choice`, and `Quot.sound`; forbidden-token scan is clean.  Both modules are umbrella-wired without umbrella builds.  Repository lint reaches both new modules and fails only on sixteen unrelated pre-existing unowned imports.
- 2026-08-27 — integrated as primary same-field occupation clause in unified standalone manuscript while retaining earlier finite-alphabet Choi law as complementary resolved-target result.  Experimental section now gives a one-sided circuit-witness falsification protocol and explicitly states compiler failure cannot certify hardness.  Tectonic build passed without warnings; all affected pages were rendered and inspected with no overlap, clipping or broken references.
