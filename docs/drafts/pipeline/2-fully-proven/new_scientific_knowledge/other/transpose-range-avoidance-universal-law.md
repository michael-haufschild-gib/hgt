# Transpose-range avoidance universal law

- **ID:** transpose-range-avoidance-universal-law
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Source:** `4-publication-ready/two-sided-singular-gelfand-defects/main.tex` · universal-law extraction
- **Statement:** `[CONJECTURE; NOVELTY UNVERIFIED]` Closed subspaces whose images are dense under every member of an observer family are classified, under annihilator duality, by weak-star closed subspaces avoiding every transpose range; finite injective dense noncoercive Hilbert observers therefore admit common blind defects of every finite codimension.

## Goal

Identify one source-pure operator law from which graph-coordinate classification, the two-sided singularity criterion, hyperplane construction, the explicit rigged-Hilbert counterexample, and all finite-codimensional extensions follow as corollaries.  This card concerns bounded observer maps only; it must not assume any spectral conclusion, rigged-space conjecture, or HGT/RH target.

## Gates

- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [x] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [ ] 2 → 3  formalized: Lean theorem `<name>`, `lake build` green, `check_axioms.sh` PASS
- [ ] 3 → 4  publication-ready: standalone paper (theorem + proof + Lean certificate + Door-2)

## Competing conjectures

### C1 — annihilator classification for arbitrary Banach observer families

`[CONJECTURE; PRIORITY OPEN]` Let `E` and `F_i` be Banach spaces and let
`T_i : E → F_i` be bounded maps with dense range.  For every norm-closed subspace `M ≤ E`,

```text
closure(T_i(M)) = F_i for every i
  iff
M^perp ∩ range(T_i') = {0} for every i.
```

Moreover `M ↦ M^perp` is an inclusion-reversing bijection from common dense-image closed
subspaces onto weak-star closed subspaces of `E*` disjoint from every transpose range.

### C2 — exact hyperplane threshold for arbitrary families

`[CONJECTURE; PRIORITY OPEN]` A proper common dense-image hyperplane exists exactly when

```text
E* ≠ union_i range(T_i').
```

For a finite nonempty family over `R` or `C`, this is equivalent to failure of surjectivity of every
`T_i'`, hence to failure of a lower bound for every `T_i`.

### C3 — finite blindness hierarchy for Hilbert embeddings

`[CONJECTURE; HARD CORE]` Let `T_1,...,T_r : E → F_i` be bounded injective maps between Hilbert
spaces, each with dense range and no lower bound.  For every finite `n ≥ 1` there is a closed
codimension-`n` subspace `M ≤ E` such that every `T_i(M)` is dense in `F_i`.

Proposed mechanism: every `range(T_i*)` is a proper nonclosed operator range and therefore has
infinite algebraic codimension; construct an `n`-plane `D` with
`D ∩ range(T_i*) = {0}` for all `i`, then take `M = D^perp`.

### C4 — unrestricted infinite-dimensional strengthening

`[OPEN PROBLEM; NOT A PAPER CLAIM]` Under C3 there is always an
infinite-dimensional closed `D` disjoint from all adjoint ranges.  Operator-range literature must
decide this.  If false, extract exact spectral criterion and extremal finite-rank survivor.

### C5 — Pythagorean observer all-or-infinite law

`[CONJECTURE; HARD CORE; PRIORITY OPEN]` Let `P : G → H₁` and `Q : G → H₂` be bounded,
injective, densely ranged Hilbert operators, and assume the joint observer is stable:

```text
∃ c > 0,  c‖x‖² ≤ ‖Px‖² + ‖Qx‖²  for every x ∈ G.
```

Then exactly one of the following holds.

1. One marginal observer is bounded below, and the only closed `M ≤ G` with both images dense is
   `M = G`.
2. Neither marginal is bounded below, and there is a closed infinite-dimensional `D ≤ G` with
   `D ∩ range(P*) = D ∩ range(Q*) = {0}`.  Consequently `M = D^perp` has infinite codimension
   and both `P(M)` and `Q(M)` are dense.

After normalizing `P*P + Q*Q` to the identity, put `C=P*P`; then `Q*Q=I-C`, the two adjoint
ranges are `range(C^(1/2))` and `range((I-C)^(1/2))`, and marginal noncoercivity is exactly
`0,1 ∈ spectrum(C)`.  Disjoint spectral bands accumulating at both endpoints should produce an
orthonormal sequence whose closed span avoids both square-root ranges.

## Door passport sketch

- **Allowed source data:** Banach/Hilbert spaces; bounded maps; dense range; injectivity; lower-bound
  failure; annihilators; transpose/adjoint ranges; finite-dimensional linear avoidance.
- **Forbidden target data:** quasi-Gelfand conclusion, canonical graph equality, zeta/RH spectral
  input, hidden completeness assumption.
- **Non-circularity:** observer maps are fixed before defect `M` is selected; every conclusion is
  expressed through their independently defined transpose ranges.
- **Door-2 obligation:** distinguish standard annihilator identities and closed-range theorems from
  any genuinely new simultaneous-family classification or finite-rank hierarchy.

## Internal prior-art audit

- `finite-observable-conormal-corona.md` proves an algebraic finite-coordinate conormal vanishing
  law, but not the bounded-operator-family theorem.
- `ccm-exterior-range-observability-law.md` records standard one-operator Hilbert range duality and
  is explicitly classified as not new knowledge.
- `PreQuasiGelfandTwoSidedSingularDefect.lean` proves the two-observer hyperplane instance only.
- `resolved-test-completeness-law.md` already cites that two-leg result; it does not contain the
  arbitrary-family annihilator lattice or finite blindness hierarchy.

## External prior-art audit

- Fillmore--Williams, *Adv. Math.* 7 (1971), supplies classical operator-range structure,
  including infinite algebraic codimension of a nonclosed Hilbert operator range and complementary
  square-root range technology; no exact C5 statement was located.
- Drewnowski (1984) proves spaceability of the complement of one nonclosed Fréchet operator range.
- Kitson--Timoney, *JMAA* 378 (2011), prove spaceability when the linear span of a countable family
  of operator ranges is nonclosed.  This does not apply to a graph pair: its two adjoint ranges sum
  to the whole graph Hilbert space.
- Araújo--Barbosa--Raposo--Ribeiro, *Mathematika* 71 (2025), treat unions under additional
  subspace/infinite-codimension hypotheses, not the complementary pair in C5.
- Ribeiro, arXiv:2510.11332v2 (2025), Remark 4.1 claims an arbitrary-family extension.  Its last
  inference only proves disjointness from a countable subfamily: from
  `F ⊂ Xtilde \ Y₀` and `Y₀ ⊂ Y` it incorrectly concludes `F ⊂ X \ Y`.  A nonclosed algebraic
  hyperplane, written as the span of its one-dimensional bounded operator ranges, is an immediate
  counterexample: its complement contains no two-dimensional subspace.

## Approach

1. Prove C1 directly by Hahn–Banach separation and transpose injectivity.
2. Derive C2 using finite-union avoidance and prove `T'` surjective iff `T` is bounded below.
3. Prove that a bounded operator range of finite algebraic codimension is closed.  Apply this to
   each nonclosed adjoint range in C3, then inductively avoid finitely many sums
   `range(T_i*) + D_k`.
4. Audit C4 against Fillmore–Williams/Dixmier operator-range theory and construct a sharp no-go or
   spectral classification.
5. Prove C5 by joint-observer normalization, Douglas range equality, and a two-endpoint spectral
   block construction.  Specialize to canonical graph coordinates, where the stability identity is
   exact.
6. Formalize exact dependency-closed core and specialize it to graph-coordinate observers.

## Paper proof

### Theorem A — observer--annihilator duality

`[PROVED HERE; STANDARD INGREDIENTS]` Let `E` and `(F_i)_{i∈I}` be Banach spaces over `R` or
`C`, and let `T_i:E→F_i` be bounded with dense range.  For a norm-closed subspace `M≤E`,

```text
closure(T_i(M)) = F_i for every i
  iff
M^perp ∩ range(T_i') = {0} for every i.                         (A.1)
```

The annihilator map is an inclusion-reversing bijection between common dense-image closed
subspaces `M` and weak-star closed subspaces `D≤E*` satisfying
`D ∩ range(T_i')={0}` for every `i`.

**Proof.** Fix `i`.  Hahn--Banach says `T_i(M)` is dense exactly when the only
`g∈F_i*` vanishing on it is zero.  Such a `g` vanishes on `T_i(M)` exactly when
`T_i'g∈M^perp`.  Dense range of `T_i` makes `T_i'` injective, so a nonzero such `g` exists exactly
when `M^perp∩range(T_i')` contains a nonzero vector.  This proves (A.1).  The classical bipolar
theorem for the dual pair `(E,E*)` gives
`M = preannihilator(M^perp)` for norm-closed `M` and
`D = preannihilator(D)^perp` for weak-star closed linear `D`; these operations reverse inclusion.
Restricting this bijection by (A.1) proves the last assertion.  No reflexivity is used. `□`

### Theorem B — exact hyperplane threshold

`[PROVED HERE]` Under Theorem A, a proper common dense-image hyperplane exists if and only if

```text
E* ≠ union_i range(T_i').                                      (B.1)
```

For a finite nonempty observer family, (B.1) is equivalent to every `T_i` failing to be bounded
below.

**Proof.** Every norm-closed hyperplane has the form `ker φ` for a nonzero `φ∈E*`, and
`(ker φ)^perp=span{φ}`.  Theorem A therefore says it is common dense-image exactly when
`φ` belongs to none of the transpose ranges, proving (B.1).  A finite union of proper linear
subspaces cannot cover a vector space over an infinite field, so for finite `I`, (B.1) holds exactly
when no `T_i'` is onto.

For any bounded `T:E→F`, `T'` is onto exactly when `T` is bounded below.  If `T'` is onto, the
open mapping theorem supplies `C` such that every `φ∈E*` has a preimage `g` with
`‖g‖≤C‖φ‖`; dual norming gives `‖x‖≤C‖Tx‖`.  Conversely, if `T` is bounded below, its range is
closed and `T^{-1}:range(T)→E` is bounded.  Given `φ∈E*`, the functional
`φ∘T^{-1}` on `range(T)` extends by Hahn--Banach to `g∈F*`, and `T'g=φ`. `□`

### Theorem C — finite blindness hierarchy

`[PROVED HERE]` Let `T_1,...,T_r:E→F_i` be bounded injective maps between Hilbert spaces, each
with dense range and no lower bound.  For every integer `n≥1` there is a closed codimension-`n`
subspace `M≤E` such that every `T_i(M)` is dense.

**Proof.** Put `R_i=range(T_i*)`.  Each `R_i` is a nonclosed operator range.  Indeed, closedness
of `R_i` would imply closedness of `range(T_i)` by the closed-range theorem; dense range would then
make `T_i` onto, and injectivity plus the bounded inverse theorem would make it bounded below.

A bounded operator range of finite algebraic codimension is closed.  To see this, write
`R=range(S)` and choose a finite-dimensional algebraic complement `L`, so `R∩L={0}` and
`R+L=E`.  After replacing the domain of `S` by its Banach quotient modulo `ker S`, the bounded map
`(x,l)↦Sx+l` is a continuous bijection from a Banach space onto `E`; its inverse is bounded, and
the image `R` of the closed first summand is closed.  Hence every `R_i` has infinite algebraic
codimension.

Construct `D_k` inductively.  Start with `D_0={0}`.  If `dim D_k=k<n` and
`D_k∩R_i={0}` for every `i`, then `R_i+D_k` is proper because `codim R_i` is infinite.  A finite
union of these proper subspaces cannot cover `E`; choose
`v_k∉union_i(R_i+D_k)` and set `D_{k+1}=D_k+span{v_k}`.  If
`a v_k+d∈R_i` with `d∈D_k`, then `a=0` (otherwise `v_k∈R_i+D_k`) and next `d=0`, so
`D_{k+1}∩R_i={0}`.  At the end `D=D_n` is finite-dimensional and closed.  Theorem A in Hilbert
form, with `M=D^perp`, makes every image dense; `codim M=dim D=n`. `□`

### Theorem D — stable two-observer coercivity--wildness dichotomy

`[PROVED HERE; NOVELTY UNVERIFIED]` Let `P:G→H_1` and `Q:G→H_2` be bounded injective densely
ranged Hilbert operators.  Assume their joint observer is bounded below:

```text
‖Px‖² + ‖Qx‖² ≥ c‖x‖²                                         (D.1)
```

for some `c>0`.  Exactly one of the following alternatives holds.

1. One of `P,Q` is bounded below.  Then `G` is the only closed `M≤G` for which both marginal
   images are dense.
2. Neither is bounded below.  There is a closed subspace `D≤G`, isomorphic to `ℓ²`, such that
   `D∩range(P*)=D∩range(Q*)={0}`.  Thus every closed `L≤D` yields a common dense-image defect
   `M=L^perp`.  In particular defects exist in every finite codimension and in countably infinite
   codimension, and the defect lattice contains an order-reversed copy of the full closed-subspace
   lattice of `ℓ²`.

**Proof.** Let `S=P*P+Q*Q`.  Condition (D.1) makes `S` positive and boundedly invertible.  Put
`U=S^(-1/2)`, `P₀=PU`, and `Q₀=QU`.  Then

```text
P₀*P₀ + Q₀*Q₀ = I.
```

Set `C=P₀*P₀`; thus `0≤C≤I` and `Q₀*Q₀=I-C`.  Injectivity of `P,Q` gives
`ker C=ker(I-C)={0}`.  Polar decomposition gives the exact range identities

```text
range(P₀*) = range(C^(1/2)),
range(Q₀*) = range((I-C)^(1/2)).                               (D.2)
```

Bounded-below status is invariant under precomposition by the isomorphism `U`.  Therefore, in the
second alternative, `0,1∈spectrum(C)`.  Since the endpoint kernels vanish, both endpoints are
non-isolated spectral accumulation points.

We prove the spectral block lemma needed below.  Choose pairwise disjoint Borel intervals
`I_{k,n}` accumulating at `0` and `J_{k,n}` accumulating at `1`, indexed by `(k,n)∈N²`, such that

```text
I_{k,n} ⊂ (0,4^(-n-1)],
J_{k,n} ⊂ [1-4^(-n-1),1),
```

and every corresponding spectral projection of `C` is nonzero.  This is possible by recursively
choosing distinct spectral points tending to each non-eigenvalue endpoint and disjoint
neighborhoods around them.  Choose unit vectors `e_{k,n}` and `f_{k,n}` in those spectral
subspaces.  All these vectors are mutually orthogonal.  With `a_n=2^(-n-1)`, put

```text
v_k = α (sum_n a_n e_{k,n} + sum_n a_n f_{k,n}),
```

where the fixed `α>0` normalizes the vectors.  The `v_k` form an orthonormal sequence; let `D₀`
be their closed span.

We claim `D₀` misses both ranges in (D.2).  Take nonzero
`x=sum_k b_k v_k` and choose `k` with `b_k≠0`.  If `x=C^(1/2)y`, project to `I_{k,n}`.  Spectral
commutation and the upper endpoint bound give

```text
|α b_k| a_n
  = ‖E(I_{k,n})x‖
  = ‖C^(1/2)E(I_{k,n})y‖
  ≤ 2^(-n-1) ‖E(I_{k,n})y‖.
```

Hence `‖E(I_{k,n})y‖≥|α b_k|` for every `n`, contradicting Bessel's inequality for the mutually
orthogonal spectral projections.  Thus `x∉range(C^(1/2))`.  Applying the same argument on
`J_{k,n}` to `I-C` proves `x∉range((I-C)^(1/2))`.

Since `P₀*=UP*` and `Q₀*=UQ*`, the closed infinite-dimensional subspace
`D=U^(-1)D₀` misses both original adjoint ranges.  Theorem A, applied to every closed `L≤D`,
shows that `P(L^perp)` and `Q(L^perp)` are dense.  This proves alternative 2.

For alternative 1, suppose for instance that `P` is bounded below and `M≤G` is closed with
`P(M)` dense.  The restriction `P|M` is bounded below, hence has closed range; therefore
`P(M)=H_1`.  For every `x∈G`, choose `m∈M` with `Pm=Px`; injectivity gives `m=x`, so `M=G`.
The two alternatives are mutually exclusive and exhaustive. `□`

### Corollary E — graph relation law

`[PROVED HERE; NOVELTY UNVERIFIED]` Let `B` be a closed, densely defined, injective, densely
ranged operator between Hilbert spaces, and give `graph(B)` its graph Hilbert norm.  If `P,Q` are
its coordinate contractions, then

```text
P*P + Q*Q = I.                                                  (E.1)
```

Consequently the lattice of closed graph restrictions having dense domain and dense range is
trivial when `B` is bounded or bounded below, and otherwise contains an order-reversed copy of
the closed-subspace lattice of `ℓ²`.  In the latter case there are restrictions in every finite
graph codimension and in countably infinite graph codimension.

**Proof.** Identity (E.1) is polarization of
`‖(x,Bx)‖_graph²=‖x‖²+‖Bx‖²`.  The coordinate maps are injective and densely ranged under the
hypotheses.  `P` is bounded below exactly when `B` is bounded; `Q` is bounded below exactly when
`B` is bounded below.  Apply Theorem D. `□`

### Proposition F — failure of the claimed uncountable-family extension

`[PROVED HERE]` Remark 4.1 of arXiv:2510.11332v2 is false.  Let `X` be any infinite-dimensional
Banach space admitting a discontinuous algebraic functional `φ`, and let `Y=ker φ`.  Then `Y` is
a nonclosed algebraic hyperplane.  For each `y∈Y`, the map `T_y:K→X`, `T_y(a)=ay`, is bounded and

```text
Y = span(union_{y∈Y} range(T_y)).
```

But `X\Y` is not even two-lineable: every two-dimensional linear subspace intersects the
codimension-one subspace `Y` nontrivially.  Hence it is not spaceable.  The proof in that remark
contains exactly the invalid inference recorded in the external audit. `□`

## Open core

- External priority of C1–C3.
- Exact operator-range theorem governing C4.
- Full verification of spectral block construction and its nonseparable edge cases in C5.
- Whether C3 extends from Hilbert spaces to a useful reflexive Banach class.
- Lean representation of finite-dimensional common transverse subspaces without choice leaks or
  forbidden axioms.

## Log

- 2026-08-03 — created directly in `1-in-progress` after internal corpus audit; C1–C4 frozen before proof; all novelty labels remain open.
- 2026-08-03 — external audit separated known one-range/nonclosed-span spaceability from C5; found fatal inclusion reversal in arXiv:2510.11332v2 Remark 4.1 and froze hyperplane counterexample.
- 2026-08-03 — Theorems A--D, graph Corollary E, and counterexample Proposition F proved dependency-closed on paper; unrestricted C4 retained only as a non-claimed open problem.
