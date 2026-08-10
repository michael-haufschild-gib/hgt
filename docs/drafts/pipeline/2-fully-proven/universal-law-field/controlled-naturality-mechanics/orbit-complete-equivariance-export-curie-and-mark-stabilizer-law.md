# Orbit-complete equivariance export, Curie inheritance, and mark-stabilizer law

- **ID:** ULF-CNM-1
- **Stage:** 2-fully-proven
- **Type:** ROUTE-INDEPENDENT MECHANISM THEOREM
- **Status:** [PAPER-PROVED] [DEPENDENCY-CLOSED] [MECHANISM NOT OBJECT]
  [SYMMETRY ALLOCATION] [LEAN-CERTIFIED] [NO PROJECT AXIOMS] [NOT RH]

## 1. Setup

Let a group `G` act on sets `X` and `Z`. Let `q:X->Q` be an old semantic reporter. Say that `q`
is **orbit-complete** when

\[
 q(x)=q(y)\quad\Longleftrightarrow\quad y\in Gx.
 \tag{CNM.1}
\]

Thus old semantic fibres are exactly symmetry orbits. Let `c:X->Z` be equivariant:

\[
 c(gx)=g c(x).
 \tag{CNM.2}
\]

As in ULF-REE-1, `c` is operationally inert when it is constant on every `q`-fibre and effective
otherwise.

## 2. Symmetry-export theorem

### Theorem 2.1

Under `(CNM.1)`--`(CNM.2)`, the following are equivalent:

1. `c` is operationally effective relative to `q`;
2. some attained response is moved by the old symmetry:

   \[
   \exists g\in G,\ x\in X:\quad g c(x)\ne c(x).
   \tag{CNM.3}
   \]

Equivalently, `c` is inert exactly when every attained response is fixed by `G`.

### Proof

If `c` is effective, choose `x,y` in one `q`-fibre with `c(x) ne c(y)`. Orbit-completeness gives
`y=gx` for some `g`. Equivariance gives `c(y)=g c(x)`, proving `(CNM.3)`.

Conversely, if `(CNM.3)` holds, `x` and `gx` lie in one orbit and hence one `q`-fibre, while
equivariance gives `c(gx)=g c(x) ne c(x)`. Thus `c` splits the fibre. QED.

### Corollary 2.2 -- invariant-output no-go

If `G` acts trivially on every attained value of `c`, then `c` is inert. In particular an invariant
scalar challenge cannot create a new distinction inside an orbit-complete semantic fibre.

This is the precise scope of the “source-native selector” obstruction. It does not apply to a
nontrivial equivariant target.

## 3. Curie inheritance

### Theorem 3.1

For every equivariant `c` and every `x`,

\[
 \operatorname{Stab}_G(x)\subseteq\operatorname{Stab}_G(c(x)).
 \tag{CNM.4}
\]

### Proof

If `gx=x`, then `g c(x)=c(gx)=c(x)`. QED.

Thus deterministic equivariance cannot reduce point symmetry. Effective equivariant genesis exports
old symmetry to motion of the response; it does not make a more asymmetric output at a
self-symmetric input.

## 4. Mark-stabilizer naturalization

Let `G` also act on a mark set `M`. Suppose

\[
 F:X\times M\longrightarrow Z
 \tag{CNM.5}
\]

is jointly equivariant:

\[
 F(gx,gm)=gF(x,m).
 \tag{CNM.6}
\]

Fix `m in M` and define `c_m(x)=F(x,m)`.

### Theorem 4.1

For every `g in Stab_G(m)`,

\[
 c_m(gx)=g c_m(x).
 \tag{CNM.7}
\]

### Proof

Since `gm=m`,

\[
 c_m(gx)=F(gx,m)=F(gx,gm)=gF(x,m)=gc_m(x).
\]

QED.

The mark converts full joint naturality into deterministic naturality under its retained stabilizer.
No claim of maximality is made without a faithfulness hypothesis on `F`.

## 5. Exact mechanism consequence

Deterministic operational birth on an orbit-complete source has two exact channels:

1. **symmetry export:** keep full equivariance and let the target response move;
2. **marked reduction:** fix an auxiliary source mark and retain at least its stabilizer.

A fully invariant scalar output uses neither channel and is inert. Distribution-valued birth is a
third possible channel, but lies outside this set theorem.

## 6. Sharp boundaries

1. Without orbit-completeness, the converse direction fails: equal `q` values can join distinct
   orbits, and a trivial-action reporter may separate them.
2. Nontrivial target action is not sufficient unless an attained value is actually moved.
3. A mark can have a small stabilizer while `F(-,m)` remains inert; marking is not sufficient for
   genesis.
4. The stabilizer of `m` need not be the maximal equivariance subgroup of `F(-,m)`.
5. Cumulative fixed marks yield subgroup intersection and no intrinsic order dependence.
6. The theorem constructs no recursive reporter generator, cost, topology, probability law,
   hypertranscendence statement, recurrence theorem, RH criterion, or route endpoint.

## 7. Parent boundary

Theorems 2.1 and 3.1 are orbit theory and Curie's principle. Theorem 4.1 is the elementary law behind
positional encodings and framed constructions. The package is therefore a `[BRIDGE]`. Its field
leverage is the allocation law: “native” must be typed as invariant, equivariant, marked, or
distributional before any genesis claim is meaningful.

## 8. Lean target

Formalization must certify orbit-complete semantics, symmetry export iff operational effectivity,
invariant-output inertness, Curie stabilizer inheritance, fixed-mark equivariance, sharp
countermodels for missing orbit-completeness and marking insufficiency, and one closed capstone.

Lean module `GaloisForLFunctions.HTGeometry.ConstitutiveControlledNaturalityMechanics` certifies all
listed clauses. Direct elaboration passes. The leaf build completes 8,665 jobs and the Universal Law
Field umbrella build completes 11,583 jobs. Axiom prints report only `propext`,
`Classical.choice`, and `Quot.sound`; two central equivalences need fewer or no axioms. No
computation certificate, `sorry`, `admit`, project axiom, `opaque`, or `unsafe` declaration occurs.
