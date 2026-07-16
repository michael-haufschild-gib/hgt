# Before There Was Time: the holographic horizon measures quantum noncommutativity

- **ID:** `holographic-horizon-commuting-line-contact-geometry`
- **Stage:** 1-in-progress
- **Type:** THEOREM / CONJECTURAL CLASSIFICATION / DIFFERENTIAL ALGEBRA / PROJECTIVE GEOMETRY
- **Scientific status:** `[CHORD THEOREM LEAN-PROVEN] [ABSTRACT RANK THEOREM LEAN-PROVEN]`
  `[GENERAL-HYPERSURFACE BOUND PAPER-PROVEN] [TOTAL-INCOMPATIBILITY COROLLARY PAPER-PROVEN]`
  `[MAXIMAL FREE ENDPOINT LEAN-PROVEN] [HEISENBERG REPRESENTATION LEAN-PROVEN]`
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

Let `A=Λ²V`, `G=Gr(2,V)⊂P(A)`, and let `C_X⊂G` be the locus of contained lines and lines whose
intersection with `X` is supported at one point.  Define the **horizon commutator index**

```text
kappa(X)=max{dim K : K⊂A linear and P(K)∩G⊂C_X},
chi_HT(X)=dim(A)-kappa(X).                                             (9)
```

Then every realization satisfies the sharp projective-obstruction law

```text
rank(B_rho) ≥ chi_HT(X).                                               (9a)
```

Indeed `ker(B_rho)` itself occurs among the subspaces in the definition of `kappa(X)`.  This is
the general principal-symbol theorem: the exact horizon determines a projective linear-avoidance
invariant that lower-bounds every possible commutator symbol.

Projective intersection theory gives the coarser but easier numerical consequence

```text
rank(B_rho) ≥ dim Gr(2,V) - dim C_X,                                  (9b)
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

For a plane horizon, `n=2`, every bivector in `Λ²V` is decomposable and `G=P(Λ²V)=P²`.  Thus
`kappa(X)` is controlled by projective linear spaces contained in the line-contact locus itself.
For a general plane curve:

```text
degree 1:  chi_HT(X)=0,
degree 2:  chi_HT(X)=2,   because C_X is the dual conic and contains no line,
degree 3:  chi_HT(X)=2,   because C_X is the finite flex-line locus,
degree ≥4: chi_HT(X)=3,   because C_X is empty.                       (12)
```

Therefore every general conic or cubic horizon already requires at least two independent
commutator channels: there is no rank-one phase.  A general plane curve of degree at least four
forces

```text
B_rho : Λ²V -> Der_K(L)  injective,     rank(B_rho)=3.                (13)
```

This is a rigidity theorem about every realization, not a property of the free construction.
A general quartic exact hypertranscendence horizon permits no commuting independent pair of laws
and no linear cancellation among their three commutator channels.

### 5.1 The holographic sandwich `[LEAN-PROVEN UPPER ENDPOINT]`

The universal free-word realization has injective `B_rho` for every finite homogeneous projective
horizon.  Hence

```text
chi_HT(X) ≤ rank(B_rho) ≤ dim(Λ²V),                                   (14)
```

for every realization, and the upper endpoint is always attained by an exact realization of the
same horizon.  For a general plane curve of degree at least four the two endpoints coincide at
three, so the horizon fixes commutator rank completely.

The canonical faithful operator representation sends `f∈L` to multiplication by `f` and each
derivation law to its linear action on `L`.  Lean proves

```text
[rho(v),M_f]=M_(rho(v)f),
ad_(rho(v))^n(M_x)=M_(rho(v)^n x),                                    (15)
```

and proves that this operator embedding preserves injectivity of `B_rho`.  Thus the horizon is
exactly recoverable from nested Heisenberg-commutator symbols, not merely analogous to them.

### 5.2 Horizon--Lie realization conjecture `[CONJECTURE -- FIELD-SCALE TARGET]`

For a finite projective horizon `X`, take the minimum over all exact one-observable differential-
field realizations of `X`.  The strong classification claim is

```text
min rank(B_rho) = chi_HT(X).                                          (16)
```

The lower bound is `(9a)` and the realization space is nonempty by the universal theorem.  The
unproved direction is sharp realization of every maximally admissible kernel.  Algebraically this
asks for a cyclic module over the quadratic law algebra

```text
T(V) / <K>
```

whose one-direction torsion variety is exactly `X`, while all prolongations across the relations
`K⊂Λ²V` remain compatible.  A proof of `(16)` would classify the least noncommutative complexity
of every finite hypertranscendence horizon by a projective invariant.

`[CONJECTURE -- SPENCER ALTERNATIVE]` If `(16)` fails, the excess minimum rank is measured by
higher formal-integrability obstructions of the horizon ideal as a module over `T(V)/<K>`.  The
resulting corrected index is a tower of principal-symbol/Spencer classes whose first layer is
`chi_HT(X)`.  Thus a counterexample to the strong equality would still produce genuinely new
horizon invariants rather than merely kill the program.

The fully commuting endpoint `K=Λ²V` is not open: the Lean-proven free-tail obstruction already
shows that an arbitrary terminal symbol cannot be followed by the independent tail used in the
universal construction.  The new sharp problem is the partially commuting case.  A prescribed
proper kernel `K` must annihilate the first symbol through its Spencer prolongation equations and
must satisfy every higher compatibility identity.  Line-contact geometry is exactly the
degree-two necessity; whether it controls the full prolongation tower is the content of `(16)`.

## 6. Why this could matter

Equation `(10)` says that algebraic complexity visible on a one-observable hypertranscendence
horizon cannot be implemented with arbitrarily cheap noncommutativity.  Each additional degree
forces another independent commutator channel until the universal projective ceiling `2n-1` is
reached.  This turns a differential-algebraic boundary into a quantitative measurement of the
minimum noncommutative complexity of every realization.

Equations `(11)--(15)` remove the remaining qualitative ambiguity in the high-degree regime.  The
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
- rank and support varieties of modules over group, Hopf, and Lie algebras;
- Grassmannians, Fano schemes of lines, tangent/contact lines, and Plücker geometry;
- projective dimension bounds for linear spaces avoiding a projective variety.

The parent geometry is explicit.  Ikeda proves that the order-`m` point--line incidence variety of
a general degree-`d` hypersurface is smooth of dimension `2n-m-1` for `m≤2n-1`, and empty for
`m≥2n`.  The projective intersection inequality is classical.  Neither is claimed as new.

Exact searches have not located the implication from a varying-derivation complete DA horizon to
the exterior commutator kernel, the horizon commutator index `(9)`, the degree bound `(10)`, or the
total-incompatibility theorem `(11)--(14)` or the Heisenberg-horizon coupling `(15)`.  Searches explicitly coupling plane quartics,
commutator maps, derivations, and hypertranscendence returned no relevant parent.  This is an
absence-of-hit result, not a priority certification.  The candidate novelty is the coupling of
complete ordinary differential algebra, Kähler principal symbols, Plücker kernel geometry, and
commutator rank.  Unlike the earlier qualitative statement that nonlinear horizons require some
noncommutativity, `(9)--(15)` are quantitative or rigid and apply to every realization.

Rank/support varieties are a serious neighboring parent for `(16)`: they detect directions or
elementary subalgebras on which a module fails to be free, especially for restricted Lie algebras
and finite group schemes in positive characteristic.  The proposed characteristic-zero object is
different: it records finite versus infinite cyclic power orbit of one vector, must realize an
arbitrary projective horizon, and couples the result to the kernel of the law commutator map.
No exact parent for that combined realization problem was found.

Primary comparison points:

- A. Ikeda, *The varieties of tangent lines to hypersurfaces in projective spaces*, Theorem 3.2,
  `https://arxiv.org/abs/1012.2186`;
- Stacks Project, Lemma 33.34.3, projective intersection dimension,
  `https://stacks.math.columbia.edu/tag/0B2R`;
- J. van der Hoeven, *Computing with D-algebraic power series*, Proposition 24, for the known
  commuting-derivation finite-rectangle parent of the Kähler superposition input.
- J. F. Carlson, E. M. Friedlander, and J. Pevtsova, *Elementary subalgebras of Lie algebras*,
  `https://arxiv.org/abs/1408.3913`, for the neighboring modular rank-variety theory.

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
   decomposable point.  The plane conclusion `(13)` uses the special fact that every bivector in
   three dimensions is decomposable.
9. The values in `(12)` are forced lower bounds.  Maximal free realizations have rank three for
   every curve; sharp rank-two realization for a general conic or cubic is a separate existence
   problem and is not claimed.

## 9. RH impact

The result is a source filter, not an RH proof.  If a completed-`L` construction proposes a
degree-`d` one-function law horizon, `(5)--(15)` demand explicit independent commutator channels
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
8. [DONE] Prove that every finite projective horizon has an exact realization with injective
   commutator symbol.
9. [DONE] Prove the canonical Heisenberg operator realization and preservation of commutators.
10. Formalize the projective kernel-avoidance invariant, the projective dimension specialization,
   and the Ikeda incidence input for `(9)--(13)`.
11. Construct sharp examples and determine whether equality in `(9a)` is realizable inside a
   finite-dimensional Lie algebra.

No rank theorem may infer injectivity merely from pointwise nonvanishing on a spanning set of
decomposable tensors.
