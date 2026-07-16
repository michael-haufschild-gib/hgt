# Before There Was Time: the holographic horizon measures quantum noncommutativity

- **ID:** `holographic-horizon-commuting-line-contact-geometry`
- **Stage:** 1-in-progress
- **Type:** THEOREM / CONJECTURAL CLASSIFICATION / DIFFERENTIAL ALGEBRA / PROJECTIVE GEOMETRY
- **Scientific status:** `[CHORD THEOREM LEAN-PROVEN] [ABSTRACT RANK THEOREM LEAN-PROVEN]`
  `[GENERAL-HYPERSURFACE BOUND PAPER-PROVEN] [TOTAL-INCOMPATIBILITY COROLLARY PAPER-PROVEN]`
  `[NOVELTY PROVISIONAL]`
- **Paper lane:** *Before There Was Time: The Holographic Horizon Measures Quantum Noncommutativity*

## 1. The horizon--commutator theorem `[LEAN-PROVEN]`

Let `V` be a finite-dimensional law space over a characteristic-zero field `K`, let

```text
rho : V -> Der_K(L)
```

be linear, and fix one observable `x ∈ L`.  Define its complete ordinary differential-algebraic
horizon

```text
H_x={v∈V : x,rho(v)x,rho(v)^2x,... are algebraically dependent over K}.   (1)
```

For `v,w∈H_x`, if the two derivations commute, then

```text
K v + K w ⊆ H_x.                                                         (2)
```

Equivalently, if some direction `a v+b w` is hypertranscendental while both endpoints are DA,
then

```text
[rho(v),rho(w)] != 0.                                                    (3)
```

This is not a metaphorical curvature claim.  It is the contrapositive of the unconditional
Kähler principal-symbol superposition theorem.  Lean proves `(2)` and `(3)` for an arbitrary law
vector space and arbitrary field extension.

## 2. The new geometric object

Assume the projectivized horizon is a projective scheme `X⊂P(V)`.  Let `C_rho⊂Gr(2,V)` be the
commuting-plane locus

```text
C_rho={A∈Gr(2,V) : [rho(v),rho(w)]=0 for every v,w∈A}.                   (4)
```

The theorem forces

```text
C_rho ⊆ LinContact(X),                                                   (5)
```

where `LinContact(X)` consists of projective lines whose set-theoretic intersection with `X` is a
projective linear subspace: empty, one point, or the whole line.  A commuting line cannot cut the
horizon in two points and then escape it.

`LinContact(X)` is the first external object forced by the horizon rather than supplied to it.
It is not the horizon topology alone: it is the incidence geometry of lines against the complete
ordinary-DA scheme.  It bounds which pairs of laws may coexist compatibly.

## 3. Holographic commutator-rank theorem `[LEAN-PROVEN ABSTRACT FORM]`

The bracket is an alternating bilinear map and therefore factors uniquely as

```text
B_rho : Λ²V -> Der_K(L),       v∧w |-> [rho(v),rho(w)].                  (6)
```

Let `A=Λ²V`.  If every linear subspace `U⊂A` with

```text
codim_A(U) < r                                                        (7)
```

contains the Plücker symbol of a line with two DA points and one HT point, then

```text
rank(B_rho) ≥ r.                                                       (8)
```

Indeed, if the rank were below `r`, rank--nullity would make `ker(B_rho)` satisfy `(7)`.  The
assumed escaping secant in that kernel has nonzero commutator by `(3)`, contradicting its kernel
membership.  Lean proves this argument for arbitrary finite-dimensional `V`; the geometric
secant-forcing premise is explicit and no projective-dimension result is hidden as an axiom.

Equivalently, if `C_X⊂Gr(2,V)` is the locus of contained lines and lines whose intersection with
`X` is supported at one point, projective intersection theory gives the general numerical law

```text
rank(B_rho) ≥ dim Gr(2,V) - dim C_X,                                  (9)
```

with the stronger `rank(B_rho)≥dim Gr(2,V)+1` when `C_X` is empty.

## 4. Degree counts commutators `[PAPER-PROVEN]`

Let `K` be algebraically closed of characteristic zero, let `dim(V)=n+1`, and suppose that the
exact projective horizon is a general degree-`d` hypersurface `X⊂P^n`.  Then

```text
rank(B_rho) ≥ min(d-1, 2n-1).                                        (10)
```

Proof.  Write `G=Gr(2,V)`, so `dim G=2n-2`, and let `N=dim P(Λ²V)`.  Every point of
`P(ker B_rho)∩G` represents a commuting line.  By `(2)`, a commuting line meeting `X` in two
distinct points must be contained in `X`.  Since `K` is algebraically closed, every other
commuting line is a line whose degree-`d` intersection divisor is supported at one point, hence
has contact order `d` there.

For a general hypersurface, Ikeda's order-`d` incidence variety of pairs `(p,l)` has dimension

```text
2n-d-1                                                     if d≤2n-1,
empty                                                       if d≥2n.
```

The Fano scheme of contained lines has smaller dimension when nonempty.  Thus `dim C_X≤2n-d-1`
for `d≤2n-1`, and `C_X` is empty for `d≥2n`.  If `k=dim ker(B_rho)`, the projective dimension
theorem applied to `P(ker B_rho)` and `G⊂P(Λ²V)` gives

```text
dim(P(ker B_rho)∩G) ≥ k + (2n-2) - dim(Λ²V).
```

Containment in `C_X` yields `rank(B_rho)≥d-1`.  When `C_X` is empty, the same theorem yields
`rank(B_rho)≥2n-1`.  This proves `(10)`.

The exact-horizon hypothesis is nonvacuous: the already Lean-proven universal realization theorem
`exists_completeJet_horizon_eq_finiteHomogeneousZeroLocus` realizes every homogeneous
hypersurface as the complete DA horizon of one observable in a rational differential field.

## 5. High-degree horizons force total incompatibility `[PAPER-PROVEN]`

Under the hypotheses of Section 4, if

```text
d ≥ 2n,
```

then every two linearly independent laws are noncommuting:

```text
v,w linearly independent  ==>  [rho(v),rho(w)] != 0.                 (11)
```

Indeed, a general degree-`d` hypersurface contains no projective line in this range.  Ikeda's
order-`d` incidence variety is also empty.  Hence every projective line meets `X` in at least two
distinct points and also leaves `X`.  If `rho(v)` and `rho(w)` commuted, all derivations associated
with their two-dimensional span would commute.  Two horizon intersection points on that line and
one point outside the horizon would then contradict the commuting-chord theorem.

For a plane horizon, `n=2`.  Every bivector in `Λ²V` is decomposable when `dim V=3`; therefore a
general plane curve of degree at least four forces

```text
B_rho : Λ²V -> Der_K(L)  injective,     rank(B_rho)=3.                (12)
```

This is a rigidity theorem about every realization, not a property of the free construction.
A general quartic exact hypertranscendence horizon permits no commuting independent pair of laws
and no linear cancellation among their three commutator channels.

## 6. Why this could matter

Equation `(10)` says that algebraic complexity visible on a one-observable hypertranscendence
horizon cannot be implemented with arbitrarily cheap noncommutativity.  Each additional degree
forces another independent commutator channel until the universal projective ceiling `2n-1` is
reached.  This turns a differential-algebraic boundary into a quantitative measurement of the
minimum noncommutative complexity of every realization.

Equations `(11)--(12)` remove the remaining qualitative ambiguity in the high-degree regime.  The
horizon does not merely require that some quantum channel be present: it forbids every classical
two-law sector.  In three law dimensions a quartic horizon already determines maximal
noncommutativity of the full principal commutator symbol.

`[CONJECTURE -- PHYSICAL READING]` In a pretemporal QFT observable algebra, `V` is a reconstructed
finite space of regular constraint-compatible infinitesimal laws.  Before a time direction is
selected, `X` is the finite-law holographic horizon and `(5)--(6)` bound the number of quantum
commutator channels already forced by that horizon.  A physical claim requires an independently
constructed local observable algebra, state, and regularity class; the abstract theorem alone is
not evidence about cosmology or black holes.

## 7. Anti-theatre and parent gate

Known ingredients not claimed as novelty:

- separate D-algebraicity for commuting derivations implies finite mixed transcendence degree;
- Kähler connections, Lie brackets of derivations, and polarization;
- commuting varieties of Lie algebras;
- Grassmannians, Fano schemes of lines, tangent/contact lines, and Plücker geometry;
- projective dimension bounds for linear spaces avoiding a projective variety.

The parent geometry is explicit.  Ikeda proves that the order-`m` point--line incidence variety of
a general degree-`d` hypersurface is smooth of dimension `2n-m-1` for `m≤2n-1`, and empty for
`m≥2n`.  The projective intersection inequality is classical.  Neither is claimed as new.

Exact searches have not located the implication from a varying-derivation complete DA horizon to
the exterior commutator kernel, the general contact-defect law `(9)`, the degree bound `(10)`, or
the total-incompatibility theorem `(11)--(12)`.  Searches explicitly coupling plane quartics,
commutator maps, derivations, and hypertranscendence returned no relevant parent.  This is an
absence-of-hit result, not a priority certification.  The candidate novelty is the coupling of
complete ordinary differential algebra, Kähler principal symbols, Plücker kernel geometry, and
commutator rank.  Unlike the earlier qualitative statement that nonlinear horizons require some
noncommutativity, `(10)--(12)` are quantitative or rigid and apply to every realization.

Primary comparison points:

- A. Ikeda, *The varieties of tangent lines to hypersurfaces in projective spaces*, Theorem 3.2,
  `https://arxiv.org/abs/1012.2186`;
- Stacks Project, Lemma 33.34.3, projective intersection dimension,
  `https://stacks.math.columbia.edu/tag/0B2R`;
- J. van der Hoeven, *Computing with D-algebraic power series*, Proposition 24, for the known
  commuting-derivation finite-rectangle parent of the Kähler superposition input.

## 8. Counterexample attacks

1. A line can meet a hypersurface at one point with full multiplicity; tangent and flex lines must
   be included in `LinContact(X)`.
2. Lines contained in `X` are compatible with `(5)` and may support large commuting families.
3. Nonzero values of the bracket on many decomposable tensors do not by themselves imply a rank
   bound; cancellations in `Λ²V` require a genuine linear-avoidance theorem.
4. Several observable roots can enlarge the visible horizon without increasing the same bracket
   rank; the one-root hypothesis must remain explicit.
5. A singular or reducible `X` may have a huge line-contact locus and no useful lower bound.
6. The free-word universal realization proves nonvacuity, but its generated Lie algebra need not be
   finite-dimensional; it does not prove sharpness of `(10)` inside a fixed physical gauge algebra.
7. The bound is on the linear rank of the derivation bracket image, not on operator norm, entropy,
   or a measured quantum energy.  Those require representation and state data.

8. Pairwise noncommutation in `(11)` does not imply injectivity of `B_rho` when `n≥3`: a nonzero
   kernel vector may be a sum of decomposable bivectors even though the kernel contains no
   decomposable point.  The plane conclusion `(12)` uses the special fact that every bivector in
   three dimensions is decomposable.

## 9. RH impact

The result is a source filter, not an RH proof.  If a completed-`L` construction proposes a
degree-`d` one-function law horizon, `(5)--(10)` demand explicit independent commutator channels
or show that the model cannot realize its claimed geometry.  No current arithmetic construction
supplies such a horizon or bracket map.

## 10. Lean route

1. [DONE] Define the general linear derivation-law jet and dependence horizon.
2. [DONE] Prove commuting chords lie entirely in the horizon.
3. [DONE] Prove an escaping hypertranscendental chord forces noncommutation.
4. [DONE] Factor the derivation bracket through `Λ²V`.
5. [DONE] Prove the abstract exterior-subspace avoidance rank theorem.
6. [DONE] Prove the abstract nonzero-bivector secant criterion for commutator-map injectivity.
7. [DONE] Prove the law-plane escaping-secant criterion for pairwise noncommutation.
8. Formalize the projective dimension specialization and Ikeda incidence input for `(10)--(12)`.
9. Construct sharp examples and determine whether equality in `(10)` is realizable inside a
   finite-dimensional Lie algebra.

No rank theorem may infer injectivity merely from pointwise nonvanishing on a spanning set of
decomposable tensors.
