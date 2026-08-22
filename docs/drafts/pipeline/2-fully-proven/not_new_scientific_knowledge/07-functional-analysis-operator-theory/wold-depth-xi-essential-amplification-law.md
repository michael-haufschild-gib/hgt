# Wold-depth--Xi essential amplification law

- **ID:** `wold-depth-xi-essential-amplification-law`
- **Stage:** 2-fully-proven / not new scientific knowledge
- **Type:** EXACT SOURCE-REPORTER LOWER BOUND / IRREGULAR-SCALE IDENTIFICATION
- **Scientific status:** `[PAPER-PROVED] [CORPUS-NEW SYNTHESIS] [NOT RH]`
  `[NO EXTERNAL NOVELTY CLAIM]`
- **Parents:**
  - `../../1-in-progress/adjoint-duality-cauchy-nerve-purity-law.md`,
    Sections 30 and 32;
  - `../bounded-exponent-poisson-strictness-emergence.md`;
  - `wold-boolean-diagonal-renormalization-mismatch.md`;
  - `../new_scientific_knowledge/gamma-copoisson-sonin-independent-quadrant-boundary-transgression.md`;
  - `../../3-formalized/prime-valuation-reflection-type-conservation-law.md`.

## Frontier correction

The all-orders-flat radical proves that no fixed finite-Rees operator can sew the reflected
irregular Wold sector to the vacuum half-density sector.  That statement identifies the kind of
singularity required but not its scale.

The literal bounded-exponent source fixes the scale.  Adding exponent depth \(M+1\) adds one
orthogonal maximum-valuation shell of Wold norm
\[
 \asymp 2^{-(M+2)/2},
\]
while the completed reporter changes by
\[
 {1\over M+1}\left(-u{\Xi'(u)\over\Xi(u)}+o(1)\right).
\]
Therefore every linear source-to-reporter realization of this same depth successor has norm at
least
\[
 \asymp {2^{(M+2)/2}\over M+1}.
\]
The exact irregular action in the normal coordinate
\(\varepsilon=(M+1)^{-1}\) is
\[
 \boxed{\mathcal A_2={\log2\over2}.}
\]
Thus “we need infinity” sharpens first to “we need an essential singularity” and now to “the
literal source forces a level-one essential extraction with action \((\log2)/2\).”

This is a necessity theorem.  It does not construct the source-canonical comparison and does not
locate a zero.

## 1. Orthogonal Wold maximum shells

Let \(K_p\) be independent with critical Wold valuation law
\[
 \mathbb P(K_p=k)=(1-p^{-1})p^{-k},
 \qquad k\in\mathbb N_0,
\tag{1}
\]
and let
\[
 {\cal M}=\sup_pK_p.
\tag{2}
\]
The corpus proves
\[
 h_m:=\mathbb P({\cal M}=m)
 ={1\over\zeta(m+1)}-{1\over\zeta(m)}
 \sim 2^{-(m+1)}.
\tag{3}
\]

Let \(\Omega^{\rm W}\) be the canonical product Wold purification and let \(Q_m\) be the spectral
projection of the maximum statistic onto \(\{{\cal M}=m\}\).  Put
\[
 \delta_m:=Q_m\Omega^{\rm W}.
\tag{4}
\]
The vectors \(\delta_m\) are pairwise orthogonal and
\[
 \|\delta_m\|^2=h_m,
 \qquad
 \|\delta_m\|\sim2^{-(m+1)/2}.
\tag{5}
\]

Nothing about \(\Xi\) is used in `(1)`--`(5)`.  The exponential half-density is fixed by the
ordinary-prime source before divisor specialization.

## 2. The same depth successor generates the Xi connection

Let
\[
 X_M(s)={\Xi(s)\over\Xi((M+1)s)},
 \qquad
 \varepsilon_M={1\over M+1},
\tag{6}
\]
and define
\[
 R_M(u)
 :=
 {X_{M+1}(\varepsilon_Mu)\over X_M(\varepsilon_Mu)}-1
 =
 {\Xi(u)\over\Xi((1+\varepsilon_M)u)}-1.
\tag{7}
\]
On every compact set \(K\) avoiding the Xi divisor,
\[
 {R_M\over\varepsilon_M}
 \longrightarrow
 L_\Xi,
 \qquad
 L_\Xi(u):=-u{\Xi'(u)\over\Xi(u)},
\tag{8}
\]
uniformly on \(K\).

Choose a compact \(K\) for which
\[
 c_K:=\|L_\Xi\|_{C(K)}>0.
\tag{9}
\]
Uniform convergence in `(8)` gives
\[
 \|R_M\|_{C(K)}
 ={c_K+o(1)\over M+1}.
\tag{10}
\]

The step \(M\mapsto M+1\) in `(6)` is the reporter image of adjoining valuation shell
\({\cal M}=M+1\).  Equations `(5)` and `(10)` compare the producer and reporter scales of one
literal source-depth operation.

## 3. Sharp essential-amplification theorem

`[PAPER-PROVED] [WOLD_XI_DEPTH_SUCCESSOR_ESSENTIAL_AMPLIFICATION]`

Let \({\cal H}_{\rm W}\) be the Wold standard-form Hilbert carrier.  Suppose bounded linear maps
\[
 T_M:{\cal H}_{\rm W}\longrightarrow C(K)
\tag{11}
\]
realize the depth successor on the corresponding shell:
\[
 T_M\delta_{M+1}=R_M.
\tag{12}
\]
Then
\[
 \boxed{\quad
 \|T_M\|
 \geq
 {c_K+o(1)\over M+1}\,2^{(M+2)/2}.
 \quad}
\tag{13}
\]
Equivalently,
\[
 \boxed{\quad
 \liminf_{M\to\infty}
 \varepsilon_M\log\|T_M\|
 \geq{\log2\over2}.
 \quad}
\tag{14}
\]
In particular, for every fixed \(N\),
\[
 \varepsilon_M^N\|T_M\|\longrightarrow\infty.
\tag{15}
\]
No finite-Rees family in the exponent normal coordinate can realize `(12)`.

### Proof

The operator norm inequality and `(12)` give
\[
 \|T_M\|
 \geq
 {\|R_M\|_{C(K)}\over\|\delta_{M+1}\|}.
\tag{16}
\]
Equations `(3)`, `(5)`, and `(10)` imply
\[
 \|\delta_{M+1}\|
 =\sqrt{h_{M+1}}
 =2^{-(M+2)/2}(1+o(1)),
\tag{17}
\]
and substitution proves `(13)`.  Taking logarithms, multiplying by
\(\varepsilon_M=(M+1)^{-1}\), and using
\[
 {\log(M+1)\over M+1}\longrightarrow0
\]
proves `(14)`.  Exponential growth in \(M\) implies `(15)`. `QED`

The bound is sharp in the unconstrained linear category.  The fitted rank-one map
\[
 T_M^{\rm fit}v
 =
 {\langle\delta_{M+1},v\rangle\over h_{M+1}}\,R_M
\tag{18}
\]
has
\[
 \|T_M^{\rm fit}\|
 ={\|R_M\|_{C(K)}\over\sqrt{h_{M+1}}}.
\tag{19}
\]
Thus the theorem computes the exact minimal amplification but does not turn arbitrary
essential growth into an RH selector.

## 4. Meaning: a source-fixed alien scale, not yet alien calculus

With \(\varepsilon=\varepsilon_M\), equation `(17)` is
\[
 \|\delta_{M+1}\|
 =
 2^{-1/2}
 \exp\!\left(-{\log2\over2\varepsilon}\right)(1+o(1)).
\tag{20}
\]
The Xi logarithmic connection in `(8)` is therefore a finite reporter extracted from a source
sector exponentially flat with action \(\mathcal A_2=(\log2)/2\).

This is exactly the scale pattern for which Stokes or alien operators are designed: ordinary
power-series/Rees operations annihilate the flat sector, while an irregular transition records
its exponentially small coefficient.  But the corpus has not constructed a Borel plane,
resurgent germ, alien derivative, or Stokes automorphism whose action is `(12)`.  “Alien
derivative” is currently the category suggested by `(14)`, not a proved identification.

The action is not fitted to a zero.  It comes from the least integer in the maximum-exponent
shell, \(2^{M+1}\), and agrees with the source-normal half-density scale already present in
\[
 {H_m(s)\over\sqrt{h_m}}
 \sim
 \sqrt2(1-2^{-s})\,2^{-m(s-1/2)}.
\tag{21}
\]
At Sonin ratio \(r=2\), the same exponential is the boundary character
\[
 \lambda_2(s)=2^{s-1/2}.
\tag{22}
\]
Hence Wold shell half-density, positive-shell conormal order, and the Sonin quadrant character
share one source-fixed irregular action.

## 5. Exact frontier after the theorem

The missing object is not an arbitrary essential multiplier.  Equation `(18)` shows that such a
multiplier can always be fitted and carries no arithmetic force.

The RH-bearing construction must instead be one source-global irregular connection
\[
 {\boldsymbol\Delta}_{\rm W\to\Xi}
\tag{23}
\]
with all of the following properties:

1. its associated Stokes grade has the forced action \((\log2)/2\);
2. its depth-\(M\) symbol sends the actual Wold maximum shell to the actual completed quotient
   successor, not to an independently chosen scalar;
3. it is compatible under every depth transition and prime cofinalization;
4. its Gamma/co-Poisson/Sonin boundary values are the already constructed independent-quadrant
   section;
5. its dagger/reflection structure is defined before choosing a zero; and
6. its Xi top-conormal boundary descent is closed, source-linear, and faithful.

Items 1 and the scalar target in item 2 are now forced.  Items 2--6 are unconstructed.  If they
produce a subexponential section on both independent Sonin faces, the exact quadrant escape law
forces
\[
 \Re\rho={1\over2}
\]
for every nontrivial zero.

## 6. Hostile audit

1. **Not RH.**  No map satisfying `(12)` source-globally is constructed.
2. **The lower bound is elementary once the two corpus asymptotics are known.**  Scientific value
   is their literal source-depth identification, not the norm inequality.
3. **Essentiality is not selectivity.**  The fitted maps `(18)` exist for every reporter and are
   maximally noncanonical.
4. **The scale depends on the chosen normal coordinate.**  It is essential relative to
   \(\varepsilon_M=(M+1)^{-1}\), but only half-order relative to the shell probability
   \(h_{M+1}\).  Both coordinates must be stated.
5. **No resurgent theorem is claimed.**  A genuine alien operator needs analytic continuation in
   a Borel or enhanced irregular category and compatibility across all depths.
6. **No positivity inference.**  Wold shell probabilities calibrate the source norm; they do not
   make the continued Xi connection positive.
7. **No finite-rank attack.**  Rank one already attains the sharp lower bound.  Dimension is
   irrelevant.

## 7. Literature boundary

Écalle alien calculus and level-one irregular Riemann--Hilbert theory are parent frameworks for
extracting exponentially flat sectors and encoding Stokes actions.  Burnol's co-Poisson/Sonine
work is the parent for the literal completed Mellin boundary.  Targeted searches found general
resurgence treatments that include zeta among rescaled meromorphic transforms, but no theorem
identifying the Wold maximum-exponent shell action \((\log2)/2\) with the bounded-exponent Xi
successor \(-u\Xi'/\Xi\).

Parent references:

- D. Dorigoni, *An Introduction to Resurgence, Trans-Series and Alien Calculus*,
  <https://arxiv.org/abs/1411.3585>.
- M. Loday-Richaud and P. Remy, *Resurgence, Stokes phenomenon and alien derivatives for
  level-one linear differential systems*, <https://arxiv.org/abs/1006.2613>.
- J. E. Andersen, *Resurgence Analysis of Meromorphic Transforms*,
  <https://arxiv.org/abs/2011.01110>.
- J.-F. Burnol, *Entrelacement de co-Poisson*,
  <https://doi.org/10.5802/aif.2268>.

No external priority claim is made without a deeper collision audit.  Current status is
corpus-new synthesis of already proved source laws.

## Lean decision

The formal tree contains the abstract all-orders-flat/finite-Rees operator theorem, but not the
infinite Wold maximum statistic, its standard-form shell projections, uniform compact
Xi-successor convergence, or the literal Gamma/co-Poisson/Sonin carrier.  Formalizing only
\(\|T v\|\leq\|T\|\|v\|\) would be theatre.  No Lean wrapper is added.

## Gates

- [x] Wold maximum-shell probability and half-density inherited
- [x] bounded-exponent Xi depth-successor connection inherited
- [x] exact minimal source-to-reporter amplification proved
- [x] exponent-normal irregular action \((\log2)/2\) identified
- [x] fitted rank-one falsifier and coordinate dependence audited
- [x] preliminary literature noncollision
- [ ] construct source-global irregular connection
- [ ] prove compatibility with prime cofinalization and depth cocycle
- [ ] identify literal Gamma/co-Poisson/Sonin boundary value
- [ ] prove independent-quadrant subexponential control
- [ ] formalize analytic interfaces in Lean
- [ ] RH
