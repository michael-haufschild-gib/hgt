# Prime-sieve Boolean first-trace connection curvature

- **ID:** `prime-sieve-boolean-first-trace-connection-curvature`
- **Stage:** 2-fully-proven
- **Type:** EXACT SOURCE RENORMALIZATION / TWO-PRIME CURVATURE LAW
- **Scientific status:** `[PAPER-PROVED] [BRIDGE] [NOVELTY UNVERIFIED] [NOT RH]`
- **Parents:**
  - `../2-fully-proven/not_new_scientific_knowledge/finite-boolean-hochschild-diagonal-cofinal-fracture.md`;
  - `../2-fully-proven/prime-sieve-wold-gamma-bv-relative-character.md`;
  - `../3-formalized/new_scientific_knowledge/prime-first-trace-essential-normal-bockstein.md`.

## Exact frontier

For a finite prime packet \(P\), let
\[
 A_P=C(\{\pm1\}^P),\qquad
 D_P=\sum_{\omega\in\{\pm1\}^P}\delta_\omega\otimes\delta_\omega,
 \qquad
 a_P=\prod_{r\in P}(1-r^{-1}).
\]
All finite-packet tensor products are embedded by unit extension into a common larger packet; the
embeddings are isometric for the projective tensor norm because they have contractive conditional
expectation retractions.

The Boolean diagonal has \(\|D_P\|_\pi=1\) and
\[
 D_{P\cup\{p\}}=D_PD_p,\qquad
 a_{P\cup\{p\}}=a_P(1-p^{-1}).
\tag{1}
\]
The uncorrected weighted diagonal \(a_PD_P\) still changes by order \(a_P\), not by the summable
first-trace loss \(a_P/p\).  Define the source face counterterm
\[
 C_{P,p}=a_PD_P(1-D_p)
\tag{2}
\]
and the corrected edge
\[
 \nabla_{P,p}
 =
 a_{P\cup\{p\}}D_{P\cup\{p\}}-a_PD_P+C_{P,p}.
\tag{3}
\]

## Theorem

`[PAPER-PROVED] [BOOLEAN_FIRST_TRACE_CONNECTION_CURVATURE]`

For every finite \(P\) and distinct primes \(p,q\notin P\):

1. the corrected edge is exactly the singular first-trace increment
   \[
   \boxed{\qquad
   \nabla_{P,p}=-{a_P\over p}D_{P\cup\{p\}};
   \qquad}
   \tag{4}
   \]
2. its projective norm is
   \[
   \boxed{\qquad
   \|\nabla_{P,p}\|_\pi={a_P\over p};
   \qquad}
   \tag{5}
   \]
3. along every enumeration \(p_1,p_2,\ldots\) of the primes, with
   \(P_n=\{p_1,\ldots,p_n\}\),
   \[
   \sum_{n\ge1}\|\nabla_{P_{n-1},p_n}\|_\pi=1;
   \tag{6}
   \]
4. the two-prime path curvature
   \[
   \Omega_{P;p,q}
   =
   \nabla_{P,p}+\nabla_{P\cup\{p\},q}
   -\nabla_{P,q}-\nabla_{P\cup\{q\},p}
   \tag{7}
   \]
   has the exact factorizations
   \[
   \boxed{
   \begin{aligned}
   \Omega_{P;p,q}
   &=
   a_P\left(
    -{D_{P\cup\{p\}}\over p}
    +{D_{P\cup\{q\}}\over q}
    +\left({1\over p}-{1\over q}\right)D_{P\cup\{p,q\}}
   \right)\\
   &=
   a_PD_P\left(
    {1\over q}D_q(1-D_p)
    -{1\over p}D_p(1-D_q)
   \right);
   \end{aligned}}
   \tag{8}
   \]
5. \(\Omega_{P;p,q}\) lies in the two-face defect ideal
   \[
   (1-D_p,1-D_q)
   \tag{9}
   \]
   and is killed by every character taking \(D_p,D_q\) to \(1\);
6. \(\Omega_{P;p,q}\neq0\).  More precisely, evaluation on a pair of Boolean points agreeing on
   \(P\cup\{p\}\) and disagreeing at \(q\) gives
   \[
   -{a_P\over p}.
   \tag{10}
   \]

Thus first-trace renormalization converts the norm-one cofinal diagonal jump into an absolutely
summable edge, but not into a presentation-independent one-cocycle.  Its obstruction is a
nonzero, explicitly factorized two-prime curvature.

## Proof

Using `(1)` in `(3)` gives
\[
\begin{aligned}
 \nabla_{P,p}
 &=
 a_P(1-p^{-1})D_PD_p-a_PD_P+a_PD_P(1-D_p)\\
 &=
 -a_Pp^{-1}D_PD_p,
\end{aligned}
\]
which is `(4)`.  Since \(a_P/p>0\) and \(\|D_{P\cup\{p\}}\|_\pi=1\), equation `(5)` follows.
Equation `(6)` is the exact sieve telescope
\[
 \sum_{n\ge1}{a_{P_{n-1}}\over p_n}
 =
 \sum_{n\ge1}(a_{P_{n-1}}-a_{P_n})
 =a_\varnothing-\lim_na_{P_n}=1.
\]

Substitute `(4)` four times in `(7)` and use
\[
 a_{P\cup\{p\}}=a_P(1-p^{-1}),\qquad
 D_{P\cup\{p,q\}}=D_PD_pD_q.
\]
This gives the first line of `(8)`.  Expanding
\[
 {1\over q}D_q(1-D_p)-{1\over p}D_p(1-D_q)
\]
gives the second line.  That line proves `(9)` and the character-vanishing assertion.

For `(10)`, realize each \(D_r\) as the indicator that the two Boolean \(r\)-coordinates agree.
Choose two points agreeing on every coordinate in \(P\cup\{p\}\) and disagreeing at \(q\).  Then
\[
 D_P=D_p=1,\qquad D_q=0,
\]
and the second line of `(8)` evaluates to \(-a_P/p\neq0\).  This proves all clauses.

## Exact BV scale bridge

Let \(J\) be the pole-cancelled BV/co-Poisson principal-normal class.  The proved sieve law gives
\[
 J(E_Pp_a)=a_PJ(p_a),\qquad
 J(E_{P\cup\{p\}}p_a)=a_P(1-p^{-1})J(p_a).
\]
Therefore
\[
 \boxed{\qquad
 p\,a_P^{-1}
 \left(J(E_Pp_a)-J(E_{P\cup\{p\}}p_a)\right)
 =J(p_a).
 \qquad}
\tag{11}
\]
The reciprocal-prime normalization in `(11)` is exactly the normalization in the Lean-proved
vector boundary
\[
 p\,\Pi_1^\perp Y_p\longrightarrow e_2.
\tag{12}
\]
This fixes the scale of a possible comparison; it does not construct that comparison.

## Hostile audit

1. **Scalar agreement is not a morphism.**  Equation `(11)` does not identify \(e_2\) with
   \(J(p_a)\) inside one source category.
2. **Summable edges are not descent.**  Equation `(6)` gives convergence along each ordered prime
   exhaustion, but `(10)` proves path dependence.
3. **Finite Boolean filling is insufficient.**  The curvature lies in the finite face-defect
   ideal and finite Boolean Hochschild homology is contractible, but canonical finite primitives
   need not converge cofinally.
4. **No zero occurs.**  Character vanishing in Clause 5 is a finite Boolean constraint, not the
   Xi co-Poisson ideal landing required for RH.
5. **No positivity is used.**  The result cannot select the critical line.
6. **No novelty claim.**  Algebraic connection curvature, separability diagonals, and sieve
   telescoping are parent mechanisms.  Targeted corpus and literature searches found no exact
   arithmetic conjunction `(4)`--`(12)`, but this theorem is classified only as a bridge.

## Positive survivor and corrected open core

The killed conjecture was that the scalar first-trace counterterm might directly turn finite
Boolean diagonals into one cofinal source object.  Equation `(10)` shows why it cannot: the
renormalized one-connection has nonzero two-curvature.

`[OPEN CORE] [XI_SOURCE_TWO_CURVATURE_EXTENSION_LANDING]`

Construct, before divisor specialization, a coherent two-cell in the restricted
Wold/Gamma/BV determinant extension whose finite Boolean boundary is `(8)`, whose differentiated
Meyer/Contou--Carrère image is the relative logarithmic residue cocycle, and whose literal
Gamma/co-Poisson/Sonin boundary lies in
\[
 (\Lambda_j,\Lambda_{j+1},\overline{\Lambda_j},
   \overline{\Lambda_{j+1}}).
\tag{13}
\]
The two-cell must be compatible on every three-prime face and its cofinal primitive must converge
in the source-normal topology.  Finite Boolean contractibility supplies local fillers; it does
not supply these two global properties.

This is stronger and better typed than asking for an essentially singular sewing operator.  The
essential datum is the cofinal trivialization of a nonzero source two-curvature.  The determinant
central extension is no longer an analogy: it is the categorical degree forced by `(10)`.

## Lean certificate for the algebraic core

The exact edge identity, square-curvature factorization, face-defect ideal landing, and universal
character vanishing are formalized in

```text
formal/GaloisForLFunctions/RHTower/PrimeSieveBooleanFirstTraceConnection.lean
```

with declarations:

```text
firstTraceCorrectedEdge_eq
firstTraceCorrectedSquareCurvature_eq
firstTraceCorrectedSquareCurvature_mem_faceDefectIdeal
map_firstTraceCorrectedSquareCurvature_eq_zero
```

The projective-norm statements `(5)`--`(6)` and concrete Boolean nonvanishing evaluation `(10)`
remain paper-proved; the formal module deliberately claims only its exact algebraic theorem.

## Gates

- [x] exact first-trace corrected edge
- [x] exact projective norm
- [x] cofinal total variation
- [x] exact two-prime curvature
- [x] face-defect ideal landing
- [x] explicit nonvanishing evaluation
- [x] BV reciprocal-prime scale bridge
- [x] hostile audit
- [x] Lean formalization of algebraic edge, curvature, and ideal landing
- [ ] restricted Wold/Gamma/BV two-cell
- [ ] three-prime coherence
- [ ] cofinal primitive convergence
- [ ] literal co-Poisson/Sonin ideal landing
- [ ] RH
