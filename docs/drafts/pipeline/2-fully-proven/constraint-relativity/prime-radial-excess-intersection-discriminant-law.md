# Prime-radial excess intersection and normalized discriminant law

- **ID:** `prime-radial-excess-intersection-discriminant-law`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) / DERIVED PRIME-HORIZON MODEL / CROSS-FACE BRIDGE
- **Status:** `[PAPER PROOF COMPLETE] [UNCONDITIONAL] [CORPUS-NEW INSTANTIATION]`
  `[GENERIC KOSZUL ALGEBRA PREEXISTING] [NO RH CLAIM] [NO LEAN WRITTEN]`
- **Parent:** `../positive-shell-koszul-cartier-obstruction-reciprocity.md`.
- **Statement:** finite prime radial holonomy defects have one underived horizon port, full
  type-`A_(N-1)` excess conormal in degree one, exterior higher coherences, and cutoff-normalized
  discriminant divisor equal to same horizon.

## Setup

Let

\[
 R=\mathbb C[[a]]
 \tag{1}
\]

and fix `M>0`. For nonempty finite set `F` of distinct primes, `N=|F|`, put

\[
 f_p(a)=p^{Ma}-1=\exp(Ma\log p)-1=a\,u_p(a),
 \tag{2}
\]

where

\[
 u_p(0)=M\log p\ne0.
 \tag{3}
\]

Thus every `u_p` is unit in `R`. Define split surjection

\[
 h_F:R^F\longrightarrow R,
 \qquad
 h_F(e_p)=u_p,
 \qquad
 E_F=\ker h_F.
 \tag{4}
\]

Let `K_F=K((f_p)_(p in F))` be Koszul differential graded algebra.

## Theorem 1: exact excess-intersection homology

There is graded-commutative algebra isomorphism

\[
 \boxed{
 H_\bullet(K_F)
 \cong
 R/(a)\otimes_R\bigwedge\nolimits^\bullet E_F.}
 \tag{5}
\]

In particular,

\[
 H_j(K_F)
 \cong
 \bigwedge\nolimits^j_{R/(a)}(E_F/aE_F),
 \qquad
 \dim_\mathbb C H_j(K_F)=\binom{N-1}{j}
 \tag{6}
\]

for `0<=j<=N-1`, and higher homology vanishes.

### Proof

Since one `u_p` is unit, `h_F` is split surjective and `E_F` is free rank `N-1`. Choose
`v in R^F` with `h_F(v)=1`; then

\[
 R^F=Rv\oplus E_F.
 \tag{7}
\]

Koszul differential is contraction by covector

\[
 (f_p)_{p\in F}=a\,h_F.
 \tag{8}
\]

Under exterior decomposition induced by `(7)`,

\[
 K_F
 \cong
 K(a)\otimes_R(\bigwedge\nolimits^\bullet E_F,0).
 \tag{9}
\]

Element `a` is nonzerodivisor in `R`, so `K(a)` has homology `R/(a)` only in degree zero.
Taking homology in `(9)` proves `(5)`--`(6)`. QED.

## Corollary 2: literal weighted root conormal

At horizon `a=0`,

\[
 E_F/aE_F
 =\left\{(c_p)_{p\in F}:
 \sum_{p\in F}c_p\log p=0\right\}.
 \tag{10}
\]

Diagonal map

\[
 (c_p)\longmapsto(c_p\log p)
 \tag{11}
\]

is isomorphism onto mean-zero hyperplane

\[
 \mathcal A_F
 =\left\{(d_p)_{p\in F}:\sum_{p\in F}d_p=0\right\},
 \tag{12}
\]

the complex type-`A_(N-1)` root space. Thus

\[
 H_0(K_F)\cong\mathbb C
 \tag{13}
\]

is one common radial horizon port, while

\[
 H_1(K_F)\cong\mathcal A_F
 \tag{14}
\]

retains all prime-relative excess directions. Higher `H_j` are their exterior coherences.

### Proof

Reduce `(4)` modulo `a` and use `(3)`. Common scalar `M` is nonzero. Every `log p` is nonzero, so
diagonal map `(11)` is invertible and takes weighted equation `(10)` to ordinary mean-zero equation.
Equations `(13)`--`(14)` follow from `(6)`. QED.

No relation `U_p=U_q` is imposed. Root conormal arises as syzygy among distinct prime holonomy
functions sharing one simple radial factor.

## Theorem 3: normalized discriminant is cutoff-independent horizon

Assume `N>=2` and define monic observer polynomial

\[
 P_F(T,a)=\prod_{p\in F}(T-f_p(a)).
 \tag{15}
\]

For distinct primes `p,q`,

\[
 f_q(a)-f_p(a)=a\,v_{pq}(a),
 \qquad
 v_{pq}(0)=M(\log q-\log p)\ne0,
 \tag{16}
\]

so every `v_pq` is unit. Therefore

\[
 \boxed{
 \operatorname{Disc}_T(P_F)
 =a^{N(N-1)}U_F(a),
 \qquad U_F\in R^\times.}
 \tag{17}
\]

Equivalently,

\[
 \operatorname{div}\operatorname{Disc}_T(P_F)
 =N(N-1)[a=0],
 \tag{18}
\]

and normalized rational divisor

\[
 \boxed{
 \frac1{N(N-1)}
 \operatorname{div}\operatorname{Disc}_T(P_F)
 =[a=0]}
 \tag{19}
\]

is independent of prime cutoff.

### Proof

Equation `(16)` follows by dividing difference of exponentials by `a`; constant term is nonzero
because primes are distinct. Root formula gives

\[
 \operatorname{Disc}_T(P_F)
 =\prod_{p<q}(f_q-f_p)^2
 =a^{2\binom N2}\prod_{p<q}v_{pq}(a)^2.
\]

Second factor is unit and `2 binom(N,2)=N(N-1)`, proving `(17)`--`(19)`. QED.

With source ordering of primes, Vandermonde orientation is

\[
 \Delta_F(a)
 =a^{N(N-1)/2}\prod_{p<q}v_{pq}(a).
 \tag{20}
\]

Its norm-square/discriminant forgets orientation exactly as finite monogenic theorem predicts.

## Theorem 4: exact observer Smith/Bockstein staircase

Order `F={p_1,...,p_N}` and let

\[
 \mathscr A_F=R[T]/(P_F).
 \tag{20a}
\]

Evaluation observer

\[
 J_F:\mathscr A_F\longrightarrow R^N,
 \qquad
 g(T)\longmapsto(g(f_1),\ldots,g(f_N))
 \tag{20b}
\]

is injective and has exact Smith form

\[
 \boxed{
 J_F\sim\operatorname{diag}(1,a,a^2,\ldots,a^{N-1}).}
 \tag{20c}
\]

Consequently

\[
 \boxed{
 0\longrightarrow\mathscr A_F\xrightarrow{J_F}R^N
 \longrightarrow\bigoplus_{j=1}^{N-1}R/(a^j)
 \longrightarrow0.}
 \tag{20d}
\]

Observer defect has length

\[
 \sum_{j=1}^{N-1}j=\binom N2,
 \tag{20e}
\]

and its `a`-adic associated-grade dimensions are

\[
 N-1,N-2,\ldots,1.
 \tag{20f}
\]

This sequence equals height distribution of positive roots of type `A_(N-1)`: there are `N-h`
positive roots of height `h`, for `1<=h<=N-1`.

### Proof

In monomial basis `1,T,...,T^(N-1)`, observer matrix is

\[
 J_F
 =(u_i(a)^{j-1})_{i,j}
 \operatorname{diag}(1,a,\ldots,a^{N-1})
 =V_uD_a.
 \tag{20g}
\]

Reduction of `V_u` modulo `a` is Vandermonde matrix on distinct numbers
`M log p_1,...,M log p_N`; determinant is nonzero. Hence `V_u in GL_N(R)`. Left multiplication
by invertible matrix does not change Smith form, proving `(20c)`. Since `R` is domain, determinant
is nonzero and observer is injective. Cokernel of diagonal map is direct sum in `(20d)`. Length is
`(20e)`. In grade `k`, exactly summands with `j>k` survive, giving dimensions
`N-1-k`, `0<=k<=N-2`, which is `(20f)`. Positive roots of `A_(N-1)` are intervals of simple roots;
exactly `N-h` intervals have length/height `h`. QED.

For complex `a` sufficiently near zero and fixed `F`, equip monomial and coordinate bases with
Euclidean norms. Since `V_u(a)` and inverse stay bounded, descending singular values satisfy

\[
 c_F|a|^{j-1}
 \le\sigma_j(J_F)\le
 C_F|a|^{j-1}
 \qquad(1\le j\le N),
 \tag{20h}
\]

for constants `c_F,C_F>0`. Thus

\[
 \|J_F^{-1}\|\asymp_F|a|^{-(N-1)}.
 \tag{20i}
\]

Raw prime-relative rank is transmuted into normal jet-depth staircase at horizon. Statement is
fixed-cutoff asymptotic; no uniform-in-`F` analytic constant is claimed.

Write `C_F=coker J_F` and `m=binom(N,2)`. Smith form and monogenic theorem give exact square law

\[
 \boxed{
 \operatorname{Fitt}_0(C_F)=(a^m)=(\Delta_F),
 \qquad
 \operatorname{Fitt}_0(\Omega_{\mathscr A_F/R})
 =(a^{2m})=(\operatorname{Disc}P_F)
 =\operatorname{Fitt}_0(C_F)^2.}
 \tag{20j}
\]

Thus framed observer orientation ideal squares to relative-law discriminant/Fitting ideal. If one
new prime is adjoined, Smith classification yields abstract module isomorphism

\[
 C_{N+1}\cong C_N\oplus R/(a^N).
 \tag{20k}
\]

New persistence bar of length `N` contributes one class in every normal grade `0,...,N-1`, exactly
`N` new positive roots involving new simple root. Isomorphism is not claimed canonical across
unordered cutoffs.

## Theorem 5: compatible infinite excess, no stable top determinant

For inclusions `F subset F'`, zero extension sends `E_F` into `E_(F')` and induces compatible
maps on Koszul homology. Filtered colimit gives

\[
 \boxed{
 H_\bullet(K_\infty)
 \cong
 \mathbb C\otimes\bigwedge\nolimits^\bullet E_\infty,
 \qquad
 E_\infty=\varinjlim_FE_F.}
 \tag{21}
\]

Degree zero stabilizes as one port, degree one grows to weighted `A_infinity` conormal, and every
fixed degree is born at finite cutoff. There is no largest nonzero degree. Finite top lines

\[
 \det(E_F)=\bigwedge^{N-1}E_F
 \tag{22}
\]

do not themselves form degree-preserving stable top homology: after adjoining prime, old top lies
one degree below new top. Producing one infinite determinant/Stokes phase therefore requires extra
semi-infinite/Tate polarization or determinant-gerbe datum, with source-defined transition
trivializations.

### Proof

Zero extension preserves equation `sum u_pc_p=0`, so maps `E_F->E_(F')` and exterior algebras.
Filtered colimits of vector spaces are exact and commute with each fixed exterior power, yielding
`(21)`. Since ranks `|F|-1` are unbounded, no top exterior degree exists in colimit. Statement
about `(22)` is degree count. QED.

## Theorem 6: phase-torus non-Abelian conormal curvature

Decorate finite prime defects by independent phases

\[
 f_p(a,\theta)
 =e^{i\theta_p}(p^{Ma}-1)
 =a\,u_p(a,\theta),
 \qquad
 u_p(0,\theta)=M\log p\,e^{i\theta_p}.
 \tag{22a}
\]

Koszul, Smith, and discriminant-order theorems remain valid at every phase. At horizon define
rank-`N-1` excess bundle over phase torus

\[
 E_\theta
 =\ker\left[
 \mathbb C^F\to\mathbb C,
 (c_p)\mapsto\sum_p(M\log p)e^{i\theta_p}c_p
 \right].
 \tag{22b}
\]

Bundle is smoothly trivial via diagonal unitary
`U_theta=diag(e^(-i theta_p))`, which maps `E_0` to `E_theta`. Equip ambient prime-coordinate space
with standard Hermitian metric and let `P_theta` be orthogonal projection to `E_theta`. Grassmann
connection `nabla=P_theta d` has, in global `E_0` frame, connection and curvature

\[
 A=-i\sum_pQ_p\,d\theta_p,
 \qquad
 Q_p=P_0E_{pp}P_0,
 \tag{22c}
\]

\[
 \boxed{
 F_A=-\sum_{p<q}[Q_p,Q_q]\,
 d\theta_p\wedge d\theta_q.}
 \tag{22d}
\]

For `N=2`, curvature is zero. For `N>=3`, every pair commutator `[Q_p,Q_q]` is nonzero. Yet

\[
 \boxed{\operatorname{tr}F_A=0.}
 \tag{22e}
\]

Hence determinant-line/first-Chern curvature is flat while excess bundle carries traceless
non-Abelian phase curvature beginning at three primes.

### Proof

Phase multiplication changes each `u_p` by unit, so previous decompositions and valuations
persist. Relation `E_theta=U_theta E_0` proves triviality. Pulling Grassmann connection to `E_0`
gives

\[
 U_\theta^*P_\theta dU_\theta
 =P_0U_\theta^*dU_\theta P_0
 =-i\sum_pP_0E_{pp}P_0d\theta_p,
\]

which is `(22c)`. Coefficients are constant, so `dA=0`; wedge square gives `(22d)`.

Write normalized positive vector `w` spanning `E_0^perp`. Then `Q_p` is rank-one operator
`|P_0e_p><P_0e_p|`. For `p!=q`, inner product

\[
 \langle P_0e_p,P_0e_q\rangle
 =-\overline w_pw_q
\]

is nonzero. If `N>=3`, vectors `P_0e_p,P_0e_q` are not collinear because a third nonzero coordinate
separates them. Nonorthogonal, noncollinear rank-one Hermitian operators do not commute, proving
pair claim. For `N=2`, `E_0` is one-dimensional and all endomorphisms commute. Trace of every
commutator is zero, proving `(22e)`. QED.

Any one-dimensional time path pulls curvature two-form back to zero, though its path-ordered
connection holonomy may remain nontrivial. Detecting local curvature requires at least two phase
directions. The connection is not intrinsic to algebraic bundle: bundle is trivial and another
connection may be flat. Arithmetic/physical use requires source derivation of prime-coordinate
Hermitian metric/projection; otherwise this is observer model, not selector.

## Theorem 7: canonical root frame and forced half-density connection

Put

\[
 s_p=u_p(a)^{-1}e_p.
 \tag{22f}
\]

Then `h_F(s_p)=1`, and ordered differences

\[
 \eta_{pq}=s_p-s_q
 \tag{22g}
\]

give canonical type-`A` root frame over entire formal radial disk:

\[
 \boxed{
 E_F\cong
 \left\{(b_p)\in R^F:\sum_pb_p=0\right\},
 \qquad
 (b_p)\mapsto\sum_pb_ps_p.}
 \tag{22h}
\]

In particular `eta_pq+eta_qr=eta_pr`, and roots `eta_(p p0)` for fixed base prime generate `E_F`.

Logarithmic radial connection of normalized legs is

\[
 A_p(a)=\partial_a\log u_p(a).
 \tag{22i}
\]

Every relative coefficient has regular horizon limit

\[
 \boxed{
 A_p(0)-A_q(0)
 =\frac M2(\log p-\log q).}
 \tag{22j}
\]

Thus half-density factor `1/2` is forced by exponential holonomy and canonical unit normalization,
not chosen by symmetric two-prime ansatz.

There is equivalent Bernoulli--Todd regulator. For log covector `L(e_p)=log p`,

\[
 L(\eta_{pq})
 =\frac1M\left[
 \operatorname{Td}^{-1}(Ma\log p)
 -\operatorname{Td}^{-1}(Ma\log q)
 \right],
 \quad
 \operatorname{Td}^{-1}(x)=\frac{x}{e^x-1},
 \tag{22k}
\]

and

\[
 \boxed{
 \lim_{a\to0}\frac{L(\eta_{pq})}{a}
 =\frac{\log q-\log p}{2}.}
 \tag{22l}
\]

### Proof

Units `u_p` make `(s_p)` basis of `R^F`; `h_F(s_p)=1`, so kernel is exactly coefficient
augmentation kernel, proving `(22h)` and root relations. Series

\[
 u_p(a)
 =M\log p+\frac{M^2(\log p)^2}{2}a+O(a^2)
\]

gives `A_p(0)=M log p/2`, proving `(22j)`. Also

\[
 \frac{\log p}{u_p(a)}
 =\frac1M\frac{Ma\log p}{e^{Ma\log p}-1},
\]

which proves `(22k)`. Expansion `x/(e^x-1)=1-x/2+O(x^2)` cancels constant in difference and gives
`(22l)`. QED.

Identity character `a=0` supplies canonical radial frame in this formal family. Theorem does not
prove physical Xi divisor uses that frame; shifting desired conclusion into identification
`a=Re(rho)-1/2` remains forbidden as selector. Literal Route-L comparison must derive same
half-density connection and then prove source curvature flatness.

## Exact four-face synthesis

One literal prime-radial family now has:

\[
 \begin{array}{c|c}
 \text{face}&\text{exact object}\\ \hline
 \text{underived/horizon}&H_0=\mathbb C\\
 \text{restrictive excess}&H_1\cong\mathcal A_F\\
 \text{higher coherence}&H_j\cong\bigwedge^j\mathcal A_F\\
 \text{observer branch}&\operatorname{divDisc}=N(N-1)[a=0]\\
 \text{observer thickness}&\operatorname{coker}J_F=\bigoplus_{j=1}^{N-1}R/(a^j)
 \\
 \text{phase geometry}&F_A=-\sum_{p<q}[Q_p,Q_q]d\theta_p\wedge d\theta_q,
 \quad\operatorname{tr}F_A=0
 \\
 \text{radial connection}&A_p(0)-A_q(0)=\frac M2(\log p-\log q)
 \end{array}
 \tag{23}
\]

This replaces vague “singular collapse from `A_infinity` to one port.” One port and full root
conormal coexist in different derived degrees of same excess intersection; observer converts
relative rank into full positive-root normal-depth staircase. What remains singular is infinite
determinant/phase and source topology, not production of degree-zero port.

## Corollary: radical saturation and derived-only growth

For every nonempty finite prime set,

\[
 (f_p:p\in F)=(a).
 \tag{23a}
\]

Indeed one `f_p=a u_p` with unit `u_p` already generates `(a)`. Therefore adding primes never
strengthens underived ideal, radical, or common zero locus. It adds only derived syzygies,
observer persistence bars, and discriminant multiplicity. All-prime ideal/radical methods cannot
produce stronger radial selection than one prime; genuine new leverage must use derived excess,
source chronology/topology, or coefficient-faithful comparison.

## RH boundary

Taking

\[
 a=\operatorname{Re}\rho-\frac12
 \tag{24}
\]

formally recovers physical prime holonomy factors up to harmless sign/power calibration. Theorem
does **not** prove actual Xi divisor maps to `a=0`. Same construction works for any distinct
positive generalized-prime weights `lambda_i` with
`f_i(a)=exp(M lambda_i a)-1`. Thus derived intersection and normalized discriminant organize
radial horizon but do not select it.

RH leverage is exact architecture:

1. raw `A_infinity` and one port need not be connected by rank-collapsing map;
2. they are `H_1` and `H_0` of one prime-radial Koszul object;
3. normalized discriminant already stabilizes at every cutoff;
4. observer Smith form predicts exact normal jet multiplicities and maximal inverse exponent;
5. underived ideal saturates at one prime, closing “more prime equations strengthen wall” route;
6. missing source theorem is coefficient-faithful comparison of this pre-divisor object with
   actual rational-Witt/Milnor/Gamma boundary, followed by literal flatness/annihilation.

## Hostile audit

1. Generic excess Koszul formula is already proved in parent positive-shell card and classical.
2. New corpus delta is literal prime-holonomy instantiation, weighted-root identification,
   normalized discriminant coupling, Smith staircase, forced half-density connection, phase
   model, and infinite determinant obstruction.
3. Variable `a` is universal radial deformation coordinate, not arithmetic selector.
4. `H_0`/`H_1` interpretation is theorem for this Koszul model only; it does not restore false
   generic SEG identification of homological degrees with creative/restrictive cells.
5. No physical Stokes-line comparison, Route-L curvature flatness, source-nullhomology, or RH is
   claimed.
6. Infinite determinant suggestion is open and must collide with Tate determinants,
   determinant gerbes, semi-infinite wedge, and restricted Grassmannian literature.
7. Phase curvature depends on standard prime-coordinate Hermitian observer; source has not yet
   forced that metric. Determinant curvature vanishes, but flat determinant holonomy is not ruled
   out.

## Lean-return note

No Lean work authorized. Later files should reuse generic Koszul/exterior algebra corpus theorem;
new formal targets would be formal-exponential factorization, weighted root-space isomorphism, and
discriminant valuation. Verify current mathlib before any plan.

## Gates

- [x] dependency-closed finite/infinite paper proof
- [x] generic internal parent identified
- [x] generalized-prime falsifier recorded
- [ ] external novelty audit
- [ ] coefficient-faithful literal Route-L comparison
- [ ] Lean formalization

## Log

- 2026-08-08 — proved prime radial excess homology, weighted `A_(N-1)` conormal, and normalized
  discriminant stability.

## Lean build progress

Formalization in progress in
`formal/GaloisForLFunctions/HTGeometry/ConstraintRelativity/PrimeRadialExcessDiscriminant.lean`
(wired into `GaloisForLFunctions.HTGeometry`).  Built and green so far:

- `vandermondeProd_contactSheets` — **card `(20)`**: the orientation of `f_p = a·u_p` is
  `a^{N(N−1)/2}` times the residue orientation;
- `addVal_pow`, `addVal_sheetDiscriminant_contact` — **cards `(17)`, `(18)`, `(19)` boxed**: the
  discriminant has order exactly `N(N−1)` in the horizon parameter, so the normalised divisor is
  cutoff-independent;
- `primeRadial_cokernel_equiv` — **cards `(20c)`, `(20d)` boxed**: the exact Smith staircase
  `diag(1, a, …, a^{N−1})` and the barcode `⊕_j R/(a^j)`;
- `primeRadial_detIdeal` — every determinantal ideal of the observer;
- `primeRadial_fitting_square` — **card `(20j)` boxed**: the orientation ideal squares to the
  cotangent Fitting ideal, at every height;
- `primeRadial_grade_card`, `primeRadial_grade_eq_rootCount` — **card `(20f)`**: the `a`-adic
  grade dimensions are `N−1, N−2, …, 1`, matching the type `A_{N−1}` positive-root height
  distribution `N − h`.

Reused, not rebuilt: `contactSheets`, `contact_cokernel_equiv`, `detIdeal_contact`,
`detIdeal_contactScale_eq_sq`, `isUnit_det_vandermonde_of_separated`, `phaseSubdiscriminant`,
`residueMult`, `contactScale` from
`phase-subdiscriminant-kahler-smith-stratification-law-formalized.md`; `sheetDiscriminant`,
`vandermondeProd`, `addVal_of_isUnit` from
`ultrametric-horizon-energy-smith-correspondence-formalized.md` and the DVR layer.

- `weightedSum`, `meanSum`, `weightDiag`, `weightDiag_map_ker`, `weightedSum_surjective`,
  `finrank_ker_weightedSum` — **Corollary 2, cards `(10)`–`(14)` boxed**: the weighted diagonal
  `(c_p) ↦ (c_p log p)` is a linear isomorphism carrying the weighted syzygy hyperplane
  `{∑ c_p log p = 0}` onto the mean-zero type `A_{N−1}` root space `{∑ d_p = 0}`; the syzygy
  functional is surjective, so the underived horizon port is one-dimensional `(13)` and the excess
  conormal has rank `N − 1` `(14)`.

- `splitKoszulHomology`, `splitKoszulHomologyEquiv` — **Theorem 1, cards `(5)`, `(9)` boxed**:
  in split coordinates the Koszul homology of a common-factor family is
  `H_{p+1}(K) ≅ (⋀^{p+1}E) ⧸ z·(⋀^{p+1}E)`, i.e. `R/(a) ⊗ ⋀^• E_F`.

**mathlib has no Koszul complexes at all** (no `Mathlib/**/Koszul*` file), but the corpus does:
`HTGeometry/CommonFactorKoszulHomology.lean` already owns the whole split-coordinate layer —
`unitWeightedAugmentation` (the card's `h_F`), `unitWeightedSplitEquiv` (the splitting `(7)`),
`unitWeightedRelationsBasis` and `card_unitWeightedAway` (`E_F` free of rank `N−1`),
`splitCommonFactorCyclesEquiv` (cycles `≅ ⋀^{p+1}E`) and
`map_scalarRange_splitCommonFactorCyclesEquiv_eq_boundaries` (boundaries `= z·⋀^{p+1}E`).  The card's
Theorem 1 is those two facts glued by `Submodule.Quotient.equiv`.  One practical note: forming the
nested quotient `↥(cycles) ⧸ boundaries` needs `set_option maxSynthPendingDepth 4`, otherwise
instance search fails to find `HasQuotient` even though every ingredient is present.

- `finrank_exteriorPower_ker_weightedSum` — **card `(6)` boxed**: the Koszul homology dimensions
  are `C(N−1, j)`;
- `rootFrame_normalised`, `rootDifference_mem_relations` — **Theorem 7, cards `(22f)`, `(22g)`**:
  the canonical root frame `s_p = u_p⁻¹e_p` is normalised and its ordered differences are excess
  syzygies (reusing the corpus `unitWeightedSection` and `unitWeightedAugmentation_section`);
- `trace_commutator_eq_zero` — **card `(22e)` boxed**: the determinant-line curvature is flat;
- `commutator_eq_zero_of_finrank_one` — **card `(22d)` at `N = 2`**: a one-dimensional excess
  bundle has vanishing phase curvature;
- `exists_cutoff_exteriorPower_ne_zero` — **cards `(21)`, `(22)`**: every fixed exterior degree is
  born at a finite cutoff, so there is no largest nonzero degree and no stable top determinant.

- `rankOneOp`, `rankOneOp_not_commute` — **card `(22d)`, the `N ≥ 3` mechanism**: non-orthogonal,
  non-collinear rank-one Hermitian operators do not commute.  This is exactly the step the card's
  proof invokes for the pair claim.

- `orthoProj`, `inner_orthoProj_orthoProj`, `orthoProj_not_collinear`,
  `phaseCurvature_commutator_ne_zero` — **card `(22d)` boxed, `N ≥ 3`**: orthogonal unit vectors
  project to non-orthogonal ones (`⟪P₀a, P₀b⟫ = −⟪a,w⟫⟪w,b⟫ ≠ 0`), a third direction meeting the
  weight vector separates them, and hence every pair commutator of the phase curvature is nonzero.
  Stated over an arbitrary complex inner-product space rather than in prime coordinates, so no
  `EuclideanSpace` bookkeeping is needed.

Remaining: the filtered-colimit form of `(21)`, i.e. `H_•(K_∞) ≅ ℂ ⊗ ⋀^• E_∞` for
`E_∞ = colim_F E_F`.  The degree-count half of `(21)`/`(22)` — every fixed degree is born at a
finite cutoff and there is no stable top — is already proved as
`exists_cutoff_exteriorPower_ne_zero`; what is left is the interchange
`⋀^j (colim E) ≅ colim (⋀^j E)`, for which mathlib has `Module.DirectLimit` but no exterior-power
commutation lemma.
