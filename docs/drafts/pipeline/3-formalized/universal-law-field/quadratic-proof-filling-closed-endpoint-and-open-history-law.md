# Quadratic proof filling, closed endpoint, and open history law

- **ID:** ULF-FILL-1
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean-certified)
- **Lean module:** `GaloisForLFunctions.HTGeometry.ConstitutiveQuadraticFilling`
- **Status:** [LEAN-CERTIFIED] [UNIVERSAL-LAW FIELD]
  [FILLING-GEOMETRY FORK] [ENDPOINT BLINDNESS]
  [QUADRATIC HISTORY COST] [ORIENTATION QUOTIENT] [NOT RH] [NO PROJECT AXIOMS]

## 1. Setup

Use the finite presentation

\[
 \mathbb Z^2=\langle a,b\mid aba^{-1}b^{-1}\rangle.
\tag{PF.1}
\]

For \(n\geq1\), define the null word

\[
 w_n=a^n b^n a^{-n}b^{-n}.
\tag{PF.2}
\]

Let \(\operatorname{Area}(w)\) be the minimum number of conjugates of the relator
\([a,b]^{\pm1}\) needed to express a null word \(w\), equivalently the minimum number of two-cells
in a van Kampen filling.

## 2. Exact filling theorem

### Theorem 2.1 — endpoint return with quadratic minimal proof history

For every \(n\geq1\):

\[
 [w_n]_{\mathbb Z^2}=1,
 \qquad |w_n|=4n,
 \qquad \boxed{\operatorname{Area}(w_n)=n^2}.
\tag{PF.3}
\]

Thus the endpoint observer is constantly the identity, while the shortest two-dimensional proof
history diverges quadratically.

### Corollary 2.2 — positive filling cost forgets orientation

The inverse word \(w_n^{-1}\) has the opposite oriented lattice area but the same minimum filling
cost:

\[
 \operatorname{Area}(w_n^{-1})=\operatorname{Area}(w_n)=n^2.
\tag{PF.4}
\]

Hence unsigned proof cost is a positive quotient of an oriented filling law.

## 3. Proof

Commutativity gives \([w_n]=1\), and the displayed word has length \(4n\).

For the upper bound, commute each of the \(n\) copies of \(a\) across each of the \(n\) copies of
\(b\). This gives an \(n\times n\) grid filling with \(n^2\) relator cells.

For the lower bound, read any word in \(a^{\pm1},b^{\pm1}\) as a closed lattice path in
\(\mathbb Z^2\) and let \(\mathcal A(w)\in\mathbb Z\) be its signed lattice area. Inserting or
deleting a conjugate of \([a,b]^{\pm1}\) changes \(\mathcal A\) by exactly \(\pm1\). The path
\(w_n\) is the boundary of an \(n\times n\) square, so

\[
 \mathcal A(w_n)=n^2.
\tag{PF.5}
\]

Every filling therefore uses at least \(n^2\) relator cells. The grid upper bound is sharp.
Reversing orientation negates \(\mathcal A\) but does not change its absolute minimum, proving
(PF.4).

## 4. Field interpretation

This model suggests **law filling geometry** rather than law curvature:

- a theorem endpoint is a boundary word;
- a proof is a filling object;
- proof equivalence is a move between fillings;
- no-go means a boundary is not fillable in the admitted law complex;
- complexity is minimal filling volume, not path length;
- recurrence is repeated return of the boundary observer;
- open history is divergence of filling volume despite endpoint return;
- positivity is passage from oriented filling current to unsigned volume.

The primitive is intrinsically two-dimensional. It is not recoverable from endpoint state space or
one-dimensional orbit geometry.

## 5. Fatal boundaries

1. Exact area depends on the chosen presentation. A universal field must use presentation-stable
   filling functions, simple-homotopy data, or a source-selected presentation; otherwise this is
   theatre.
2. Endpoint recurrence alone does not determine filling cost. The relation cells are constitutive
   data.
3. Quadratic growth is model-specific. Other law complexes can have linear, polynomial,
   exponential, nonrecursive, or infinite filling functions.
4. The theorem does not produce positivity of operators, hypertranscendence, observer matching, or
   physical complexity.
5. A one-dimensional proof calculus with canonical normal forms may have no meaningful higher
   filling geometry; such a corpus would kill this fork.

## 6. Distinguishing prediction

If law filling geometry is fundamental, proof routes with identical endpoints should be separated
by stable higher-dimensional filling invariants, and some apparent source-selection no-gos should
become non-fillability or superlinear filling lower bounds. Unlike polyscopic geometry, this predicts
large history even when total reconstruction is unique.
