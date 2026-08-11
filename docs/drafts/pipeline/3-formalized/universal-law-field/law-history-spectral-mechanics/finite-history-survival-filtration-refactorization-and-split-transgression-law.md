# Finite-history survival filtration, refactorization, and split-transgression law

- **ID:** ULF-LHSM-1
- **Stage:** 3-formalized
- **Type:** ROUTE-INDEPENDENT MECHANISM THEOREM
- **Statement:** Every finite linear law history carries a canonical future-tail survival
  filtration; refactoring one stage inserts an exact refinement; and split local failures cancel
  through a canonical transgression even when both local defect spaces are nonzero.
- **Status:** [PAPER-PROVED] [DEPENDENCY-CLOSED] [MECHANISM NOT OBJECT]
  [FINITE HISTORY] [EXACT REFACTORIZATION] [SPLIT TRANSGRESSION]
  [LEAN-CERTIFIED] [AXIOM-AUDITED] [UMBRELLA-BUILT] [NOT RH]

## 1. Finite law history

Let `k` be a field and let

\[
 V_0\xrightarrow{d_1}V_1\xrightarrow{d_2}\cdots
 \xrightarrow{d_m}V_m,
 \qquad m\ge 1,
 \tag{LHS.1}
\]

be linear maps. For `0<=i<=m`, let

\[
 T_i=d_m\cdots d_{i+1}:V_i\longrightarrow V_m,
 \qquad T_m=\operatorname{id}_{V_m}
 \tag{LHS.2}
\]

be the complete future tail. Thus `T_(i-1)=T_i d_i`. Put

\[
 C=V_m/\operatorname{im}T_0
 \tag{LHS.3}
\]

and write `pi:V_m->C` for the quotient map.

Define the `i`-th survival layer by

\[
 F_i=\pi(\operatorname{im}T_i)\subseteq C.
 \tag{LHS.4}
\]

## 2. Finite-history survival theorem

### Theorem 2.1

The subspaces in (LHS.4) form a canonical exhaustive filtration

\[
 0=F_0\subseteq F_1\subseteq\cdots\subseteq F_m=C.
 \tag{LHS.5}
\]

For every `1<=i<=m`, there is a canonical linear equivalence

\[
 \boxed{
 F_i/F_{i-1}\cong
 V_i/(\operatorname{im}d_i+\ker T_i).}
 \tag{LHS.6}
\]

The equivalence is induced by

\[
 v\longmapsto [\pi(T_i v)]\in F_i/F_{i-1}.
 \tag{LHS.7}
\]

### Proof

Since `T_(i-1)=T_i d_i`,

\[
 \operatorname{im}T_{i-1}\subseteq\operatorname{im}T_i,
\]

so the `F_i` are nested. At `i=0`, the image of `T_0` is zero in its own quotient, hence
`F_0=0`. At `i=m`, `T_m=id`, so `F_m=C`. This proves (LHS.5).

Fix `i>=1`. The map in (LHS.7) is surjective by the definition of `F_i`. Its kernel consists of
those `v` for which

\[
 T_i v\in\operatorname{im}T_{i-1}
 =T_i(\operatorname{im}d_i).
\]

Equivalently, there is `u in V_(i-1)` such that

\[
 T_i v=T_i d_i u,
\]

or

\[
 v-d_i u\in\ker T_i.
\]

Therefore the kernel is exactly

\[
 \operatorname{im}d_i+\ker T_i.
\]

The first isomorphism theorem gives (LHS.6). `square`

## 3. Exact refactorization theorem

Suppose one stage is refactored as

\[
 d_i=h g,
 \qquad
 V_{i-1}\xrightarrow{g}W\xrightarrow{h}V_i.
 \tag{LHS.8}
\]

The total map `T_0` and total defect `C` do not change. Define the inserted survival layer

\[
 G=\pi(\operatorname{im}(T_i h)).
 \tag{LHS.9}
\]

### Theorem 3.1

Refactorization inserts one canonical intermediate layer

\[
 F_{i-1}\subseteq G\subseteq F_i
 \tag{LHS.10}
\]

and one canonical short exact sequence

\[
 \boxed{
 0\longrightarrow G/F_{i-1}
 \longrightarrow F_i/F_{i-1}
 \longrightarrow F_i/G\longrightarrow0.}
 \tag{LHS.11}
\]

Its new grades are

\[
 \boxed{
 G/F_{i-1}\cong
 W/(\operatorname{im}g+\ker(T_i h)),}
 \tag{LHS.12}
\]

\[
 \boxed{
 F_i/G\cong
 V_i/(\operatorname{im}h+\ker T_i).}
 \tag{LHS.13}
\]

Equivalently, after substituting these canonical grade descriptions, refactorization gives the
direct exact law

\[
 \boxed{
 0\longrightarrow
 \frac{W}{\operatorname{im}g+\ker(T_i h)}
 \longrightarrow
 \frac{V_i}{\operatorname{im}(h g)+\ker T_i}
 \longrightarrow
 \frac{V_i}{\operatorname{im}h+\ker T_i}
 \longrightarrow0.}
 \tag{LHS.14}
\]

Thus refactorization does not add an independent summand. It resolves one old grade into an exact
extension of two new grades.

### Proof

From `d_i=h g`,

\[
 \operatorname{im}(T_i h g)
 \subseteq\operatorname{im}(T_i h)
 \subseteq\operatorname{im}T_i.
\]

Passing to the fixed quotient `C` gives (LHS.10). For any nested subspaces `P subseteq Q subseteq R`,
the inclusion and quotient maps give

\[
 0\to Q/P\to R/P\to R/Q\to0.
\]

Apply this with `P=F_(i-1)`, `Q=G`, and `R=F_i` to obtain (LHS.11).

Apply Theorem 2.1 to the refined history at its new `W` stage. Its incoming map is `g` and its
complete future tail is `T_i h`, giving (LHS.12). Apply it at the following `V_i` stage. Its
incoming map is `h` and its future tail is `T_i`, giving (LHS.13). `square`

## 4. Split local-cancellation transgression

Let

\[
 X\xrightarrow{f}Y\xrightarrow{g}X
 \tag{LHS.15}
\]

be linear maps satisfying

\[
 g f=\operatorname{id}_X.
 \tag{LHS.16}
\]

Let `Q=Y/im f` and `K=ker g`.

### Theorem 4.1

The formula

\[
 \boxed{
 \delta:Q\longrightarrow K,
 \qquad
 \delta([y])=y-f(g y)}
 \tag{LHS.17}
\]

is a canonical linear equivalence. Its inverse is induced by the inclusion `K subseteq Y`:

\[
 \delta^{-1}(z)=[z].
 \tag{LHS.18}
\]

Consequently `coker f` and `ker g` may both be nonzero even though the total history has zero
kernel and zero cokernel because `g f=id`.

### Proof

If `y` is replaced by `y+f(x)`, then

\[
 y+f(x)-f(g(y+f(x)))
 =y+f(x)-f(g y+x)
 =y-f(g y),
\]

so (LHS.17) is well-defined. Moreover,

\[
 g(y-f(g y))=g y-g f(g y)=0,
\]

so its value lies in `K`.

For `z in K`,

\[
 \delta([z])=z-f(g z)=z.
\]

Conversely,

\[
 [\delta([y])]=[y-f(g y)]=[y]
\]

in `Q`. Thus (LHS.17)--(LHS.18) are inverse linear maps. The final assertion follows from
`g f=id`. `square`

### Sharp cell

Take `Y=X direct_sum W`,

\[
 f(x)=(x,0),\qquad g(x,w)=x.
 \tag{LHS.19}
\]

Then

\[
 \operatorname{coker}f\cong W,
 \qquad
 \ker g\cong W,
 \qquad
 g f=\operatorname{id}_X,
 \tag{LHS.20}
\]

and `delta([(x,w)])=(0,w)`. If `W` is nonzero, both local defects are nonzero while the total
defect vanishes. This is exact cancellation, not scalar compensation.

## 5. Mechanism consequences

1. **Local failure is provisional.** Nonzero stagewise defects need not survive.
2. **Future kernels are active.** They are precisely the freedom by which a local class is erased
   before the endpoint.
3. **Survival has depth.** The filtration records where a global class stops being erasable.
4. **Refactorization changes history without changing endpoint.** The total map cannot reconstruct
   its exact refinement spectrum.
5. **Cancellation is typed.** The split cell has a canonical defect-to-defect transgression.
6. **One scalar cannot encode the mechanism.** Total size, local sizes, survival depth, and
   extension data are different truncations.

## 6. Hostile boundaries

1. **No canonical direct sum.** Over a field, (LHS.11) splits abstractly, but the history supplies no
   preferred splitting. Over more general exact settings it need not split at all.
2. **No spectral-sequence universality yet.** The theorem proves the finite linear survival
   filtration and its first exact cancellation cell. A coherent stable-category page construction
   remains a separate theorem.
3. **No arbitrary filtration.** The `F_i` are generated by complete future tails. Declared target
   filtrations do not satisfy the source-normality requirement.
4. **No observer theorem yet.** Preservation under exact functors and correction terms for
   nonexact observers remain open.
5. **No infinite-history convergence.** Derived limits, completion, and transfinite stabilization
   require additional hypotheses.
6. **No RH claim.** No endpoint, source selector, or annihilation theorem is used.

## 7. Relation to certified parents

ULF-PSB-1 is the two-stage exact-sequence truncation. ULF-DKO-1 is the three-stage truncation of
Theorem 2.1. The separately formalized relative-law-fibre theorem certifies the two-stage
octahedral composition triangle and the same split inclusion--projection cancellation boundary in
the stable tangent chart. ULF-LHSM-1 supplies the general finite linear history and exact
refactorization law that those cards left open.

## 8. Lean certificate

Formal module:

`GaloisForLFunctions.HTGeometry.ConstitutiveLawHistorySpectralMechanics`.

It certifies:

1. finite future-tail image filtration, bottom/top, and monotonicity;
2. the adjacent survivor quotient identification (LHS.6);
3. exact refactorization insertion and the short exact refinement (LHS.14);
4. split transgression well-definedness, inverse, and the sharp nontrivial scalar cell;
5. unconditional capstones `finiteFiltration_closed`, `finiteHistoryStage_closed`,
   `refactorization_short_exact`, and `splitTransgression_closed`.

Foreground verification on 2026-08-10:

```text
lake env lean GaloisForLFunctions/HTGeometry/ConstitutiveLawHistorySpectralMechanics.lean
lake build GaloisForLFunctions.HTGeometry.ConstitutiveLawHistorySpectralMechanics
lake build GaloisForLFunctions.HTGeometry.UniversalLawField
```

The leaf build completed 8,700 jobs and the Universal Law Field umbrella completed 11,581 jobs.
`#print axioms` on all capstones and `splitTransgressionEquiv` reports only `propext`,
`Classical.choice`, and `Quot.sound`. The module contains no `sorry`, `admit`, project axiom,
`opaque`, `unsafe`, or computational certificate.

Repository-wide lint was clean before concurrent theorem-area edits. The final concurrent audit was
blocked only by unrelated newly owned modules not yet imported by their theorem-area umbrellas;
the LHSM module itself is imported, directly elaborated, indexed, and umbrella-built.
- 2026-08-11 -- Lean surface audited complete against the card; promoted to stage 3.
