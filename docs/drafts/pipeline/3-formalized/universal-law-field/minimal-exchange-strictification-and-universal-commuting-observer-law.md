# Minimal exchange strictification and universal commuting-observer law

- **ID:** ULF-OPM-2
- **Stage:** 3-formalized
- **Type:** MECHANISM THEOREM / STRICT OBSTRUCTION PROMOTION
- **Statement:** Failure of two unary laws to exchange promotes canonically to the least congruence
  making both laws executable and commuting; every commuting observer factors uniquely through the
  resulting quotient.
- **Status:** [PAPER-PROVED] [LEAN-CERTIFIED] [DEPENDENCY-CLOSED] [MECHANISM NOT ROUTE]
  [STRICT-PROMOTION BASELINE] [NOT RH]

## 1. Setup

Let `X` be a set and let

\[
  f,g:X\longrightarrow X
\]

be two unary laws. Their raw exchange residual is the family of critical pairs

\[
  E_{f,g}
  =\{(f(gx),g(fx)):x\in X\}.
  \tag{ES.1}
\]

Let `R_(f,g)` be the intersection of all equivalence relations `R` on `X` such that

1. `E_(f,g) subset R`;
2. `R(x,y)` implies `R(fx,fy)`;
3. `R(x,y)` implies `R(gx,gy)`.

Equivalently,

\[
 R_{f,g}=\operatorname{Cg}_{\{f,g\}}(E_{f,g})
 \tag{ES.2}
\]

is the unary-law closure from ULF-LSM-2 applied to the exchange residual.

## 2. Minimal strictification theorem

### Theorem 2.1

The relation `R_(f,g)` has the following exact properties.

1. It is an equivalence relation.
2. Both `f` and `g` preserve it.
3. Every raw exchange pair lies in it:

   \[
     R_{f,g}(f(gx),g(fx))
     \qquad(x\in X).
     \tag{ES.3}
   \]

4. It is least with these properties. If `S` is any equivalence relation preserved by `f` and `g`
   and containing `(ES.1)`, then

   \[
     R_{f,g}\subseteq S.
     \tag{ES.4}
   \]

### Proof

By definition `R_(f,g)` is the intersection of all equivalence relations satisfying the three
declared conditions. Intersections preserve reflexivity, symmetry, and transitivity. Membership of
`f` and `g` in the generating unary-law family gives preservation, and the closure contains its seed
relation. Since every competitor `S` appears among the relations being intersected, the intersection
is contained in `S`. QED.

## 3. Universal commuting quotient

Let

\[
  \pi:X\longrightarrow Q_{f,g}:=X/R_{f,g}
  \tag{ES.5}
\]

be the quotient map.

### Theorem 3.1

There are unique induced laws

\[
  \bar f,\bar g:Q_{f,g}\longrightarrow Q_{f,g}
  \tag{ES.6}
\]

satisfying

\[
  \pi f=\bar f\pi,
  \qquad
  \pi g=\bar g\pi.
  \tag{ES.7}
\]

They commute:

\[
  \boxed{\bar f\bar g=\bar g\bar f.}
  \tag{ES.8}
\]

### Proof

Preservation of `R_(f,g)` by `f` and `g` gives the quotient maps `(ES.6)` and their uniqueness.
For every `x`,

\[
 \bar f\bar g(\pi x)
 =\pi(f(gx))
 =\pi(g(fx))
 =\bar g\bar f(\pi x)
\]

by `(ES.3)`. Surjectivity of `pi` proves `(ES.8)`. QED.

### Theorem 3.2 -- universal factorization

Let `q:X->Y` be any observer. Suppose there are unary laws `F,G:Y->Y` such that

\[
 qf=Fq,
 \qquad
 qg=Gq,
 \qquad
 FG=GF.
 \tag{ES.9}
\]

Then there is a unique map

\[
 \widetilde q:Q_{f,g}\longrightarrow Y
 \tag{ES.10}
\]

with

\[
 q=\widetilde q\pi.
 \tag{ES.11}
\]

If `q` is surjective, `widetilde q` also intertwines the induced laws with `F,G` on all of `Y`.

### Proof

The observer kernel `ker q` is an equivalence relation. Equations `(ES.9)` show that it is preserved
by `f` and `g`. Moreover,

\[
\begin{aligned}
q(f(gx))
 &=F(G(qx))\\
 &=G(F(qx))\\
 &=q(g(fx)),
\end{aligned}
\]

so `ker q` contains every exchange pair. Minimality `(ES.4)` gives

\[
 R_{f,g}\subseteq\ker q.
 \tag{ES.12}
\]

Therefore `q` is constant on quotient classes and descends uniquely to `(ES.10)`. Intertwining
follows from `(ES.7)`, `(ES.9)`, and surjectivity. QED.

## 4. Sharp no-go and positive survivor

### Corollary 4.1

Let `S` be an equivalence relation strictly smaller than `R_(f,g)`. Then the quotient `X/S` cannot
simultaneously have all three properties:

1. `f` descends;
2. `g` descends;
3. the descended laws commute.

Thus strict exchange failure has exactly two mechanism-level responses:

- retain the critical-pair history as higher or extension-valued law;
- erase at least `R_(f,g)` distinctions to obtain a strict commuting quotient.

There is no smaller strict quotient repair.

### Proof

If all three properties held, `S` would be an equivalence relation preserved by both laws and would
contain every exchange pair. Theorem 2.1 would force `R_(f,g) subseteq S`, contradicting strict
smallness. QED.

This is the positive survivor of the no-go: failure of exchange canonically **produces** a universal
new law, namely the minimal strictifying congruence.

## 5. Nontrivial finite/infinite calibration

Take `X=N`,

\[
 f(n)=n+1,
 \qquad
 g(n)=2n.
 \tag{ES.13}
\]

Then the raw critical pairs are `(2n+1,2n+2)`. Preservation under `f` adds the bridges
`(2n+2,2n+3)`, so every positive integer becomes equivalent. Zero remains separate because the
two-class relation

\[
 x\sim y
 \quad\Longleftrightarrow\quad
 (x=0\Longleftrightarrow y=0)
 \tag{ES.14}
\]

contains every critical pair and is preserved by both laws. Hence `Q_(f,g)` has exactly two classes:
zero and positive. The quotient is nontrivial, both laws descend, and they commute. Strictification
need not collapse the entire source.

## 6. Mechanism interpretation

The theorem is not a search for a hidden carrier. It is one exact law of law genesis:

\[
 \text{failed exchange}
 \longmapsto
 \text{least promoted congruence}
 \longmapsto
 \text{universal commuting execution}.
 \tag{ES.15}
\]

It supplies a falsifiable prediction. Any observer claiming to retain both source laws as commuting
operations must erase every pair in `R_(f,g)`. Measuring less loss is impossible.

The theorem also exposes its own ceiling. Quotient strictification deletes ordered history. A field
that must retain carry, phase, extension, or higher interaction needs a non-strict promotion rather
than a smaller quotient. The next research question is therefore to classify the universal
alternatives to `(ES.2)`, not to search for another route object.

## 7. Parent boundary and scope

The construction is standard universal algebra: it is the least congruence forcing two unary
operations to commute, equivalently a coequalizing quotient in the category of unary algebras. Its
field role is foundational, not a novelty claim.

It proves no canonical higher cell, no cost, no topology, no convergence, no physical law, and no
RH consequence. It is the strict Class-A baseline for Obstruction--Promotion Mechanics. Class-B
homotopy promotion and Class-C singular promotion remain independent until comparison theorems are
proved.

## Lean certification

Module:
`GaloisForLFunctions.HTGeometry.ConstitutiveExchangeStrictification`.

Lean closes without project axioms:

1. exchange seed and least exchange congruence;
2. equivalence, preservation, containment, and leastness;
3. quotient operations, their uniqueness, and exact commutation;
4. universal factorization and intertwining for every commuting observer;
5. sharp no-smaller-strictification corollary;
6. the successor/doubling calibration: the least exchange congruence is exactly the zero/positive
   partition, so the quotient has exactly two classes;
7. bundled mechanism theorem.

Direct elaboration and the targeted module build pass. Axiom audit reports only `propext` and
`Quot.sound`.

## Log

- 2026-08-09 -- paper theorem closed as first explicit obstruction-to-law promotion rule.
- 2026-08-09 -- full significant theorem closed in Lean and wired into the dedicated universal-law
  umbrella.
- 2026-08-11 -- uniqueness of the induced quotient laws and the successor/doubling two-class calibration certified; card promoted to stage 3.
