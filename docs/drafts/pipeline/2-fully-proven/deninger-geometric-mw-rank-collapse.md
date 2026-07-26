# Geometric Milnor--Witt rank collapse

- **ID:** `deninger-geometric-mw-rank-collapse`
- **Stage:** 2-fully-proven
- **Type:** SOURCE THEOREM
- **Labels:** `DAC_GEOMETRIC_MW_RANK_COLLAPSE`
- **Parent:** `deninger-derived-mw-rational-witt-coefficient`

## Statement

Let \(F\) be an algebraically closed field of characteristic \(0\).  For every
\(n\geq 0\), the forgetful morphism
\[
 F_n:K_n^{MW}(F)\longrightarrow K_n^M(F)
 \tag{1}
\]
is an isomorphism.  More explicitly,
\[
 K_n^{MW}(F)\cong
 \begin{cases}
 \mathbb Z,&n=0,\\
 K_n^M(F),&n>0,
 \end{cases}
 \tag{2}
\]
and under \(K_0^M(F)=\mathbb Z\), \(F_0\) is the rank isomorphism.

Consequently:

1. `(1)` remains an isomorphism after quotienting by torsion or tensoring with
   \(\mathbb R\);
2. any map of connective spectra
   \[
   \mathcal K_F^{MW}\longrightarrow\mathcal K_F^M
   \]
   realizing `(1)` on all homotopy groups is an equivalence;
3. base change along any \(E_\infty\)-algebra map
   \(\mathcal P_F\to\mathcal C_F\) gives an equivalence
   \[
   \mathcal C_F\otimes_{\mathcal P_F}^{\mathbb L}\mathcal K_F^{MW}
   \xrightarrow{\;\sim\;}
   \mathcal C_F\otimes_{\mathcal P_F}^{\mathbb L}\mathcal K_F^M;
   \tag{3}
   \]
4. the connective fiber and derived rank quotient of `(3)` are trivial:
   \[
   \operatorname{Fib}(3)\simeq0,\qquad
   \left(\mathcal C_F\otimes_{\mathcal P_F}^{\mathbb L}\mathcal K_F^{MW}\right)
   \otimes_{\operatorname{Free}_{E_\infty}^{+}(0)}^{\mathbb L}\mathbbm1
   \simeq
   \mathcal C_F\otimes_{\mathcal P_F}^{\mathbb L}\mathcal K_F^M.
   \tag{4}
   \]

The conclusion concerns the untwisted nonnegative diagonal coefficient on a
geometric chart.  It does **not** trivialize twisted Milnor--Witt residues over
non-algebraically-closed arithmetic residue fields.

## Proof

Because \(F\) is algebraically closed, every element of \(F^\times\) has a
square root.  Déglise, Example 2.1.13, proves that for any field \(K\), the
following are equivalent:

- every unit of \(K\) is a square;
- the parity-rank morphism \(W(K)\to\mathbb Z/2\) is an isomorphism.

Thus the fundamental ideal \(I(F)\), the kernel of parity rank, vanishes.

Déglise, Corollary 2.3.7, identifies the Milnor--Witt ring as the cartesian
square
\[
\begin{CD}
K_*^{MW}(F) @>>> K_*^M(F)\\
@VVV              @VVV\\
I^*(F) @>>> \bar I^*(F).
\end{CD}
\tag{5}
\]
Equivalently, Example 2.3.11 specializes this square directly: whenever every
unit is a square,
\[
K_n^{MW}(F)=
\begin{cases}
\mathbb Z,&n=0,\\
\mathbb Z/2,&n<0,\\
K_n^M(F),&n>0.
\end{cases}
\tag{6}
\]
The map in positive degrees in `(6)` is the forgetful map.  In degree zero,
\(K_0^{MW}(F)=GW(F)\); since all one-dimensional forms are isometric and
hyperbolic cancellation leaves rank as the only Grothendieck--Witt invariant,
the forgetful map is \(GW(F)\xrightarrow{\sim}\mathbb Z=K_0^M(F)\).
This proves `(1)` and `(2)`.

Torsion quotient and realification preserve isomorphisms, proving consequence
1.  A map between connective spectra that is an isomorphism on every homotopy
group is an equivalence, proving consequence 2.  Derived base change preserves
equivalences, proving `(3)`.  Its fiber is therefore contractible.  The free
unital \(E_\infty\)-algebra on the zero object is the unit, so `(4)` follows.

## Arithmetic consequence

The local geometric character chart has no nonnegative Milnor--Witt rank
kernel and no degree-one Tor obstruction.  Hence local coefficient construction
must use the ordinary unit-amalgamated algebra
\[
\mathcal C_F^M
=
\mathcal C_F\otimes_{\mathcal P_F}^{\mathbb L}\mathcal K_F^M.
\]

Quadratic orientation data can only survive in parts not covered by the
untwisted geometric calculation:

1. twisted Rost--Schmid residue terms \(K_n^{MW}(\kappa(v),\omega_v)\);
2. Galois descent before passage to algebraic closure;
3. real/archimedean boundary terms.

Therefore a construction that inserts a nontrivial rank quotient separately on
every algebraically closed chart is redundant.  The correct next problem is to
construct a homotopy-coherent global residue/Galois descent system whose
geometric stalk is \(\mathcal C_F^M\) and whose arithmetic specialization maps
retain the Milnor--Witt twists.

## Boundary

This theorem does not prove:

- existence of the global Rost--Schmid descent object;
- compatibility of power maps with twisted residues and transfers;
- the three-term global cohomology calculation;
- Poincaré duality, Lefschetz trace, determinant realization, or positivity.

It removes only the local geometric rank-kernel gate.

## References

- Frédéric Déglise, *Notes on Milnor--Witt K-theory*, Example 2.1.13,
  Corollary 2.3.7, and Example 2.3.11:
  https://arxiv.org/abs/2305.18609
- Fabien Morel, *\(\mathbb A^1\)-Algebraic Topology over a Field*,
  Milnor--Witt \(K\)-theory and the fundamental square.

## Novelty audit

The algebraic identity `(1)` is standard.  The new deduction for this program
is architectural: on Deninger's algebraically closed geometric character
charts, Milnor--Witt refinement and the local derived rank quotient cannot
carry extra nonnegative information.  Quadratic data must be placed in
twisted arithmetic descent rather than in the local geometric stalk.

**Verdict:** `FULLY PROVEN ON PAPER`.
