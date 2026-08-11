# Route E two-sided column-load gradient and pair-switch law

- **ID:** `ROUTE-E-TWO-SIDED-LOAD-GRADIENT-PAIRSWITCH-001`
- **Stage:** 3-formalized
- **Type:** `[THEOREM (paper)]` / `[FRONTIER REDUCTION]` / `[SHARP FIREWALL]`
- **Source:** Route E direct recurrence-weighted conductance lane; read-only reuse of
  `RHTower/RouteEDegreeNormalizedGibbsBoundaryVariation.lean`,
  `HTGeometry/RecurrenceSwapInteractionReconstructionLaw.lean`, and
  `HTGeometry/ComponentReplicaCollisionLaw.lean`
- **Statement:** For a full-row two-sided parity recurrence, inverse-load Dirichlet energy is at
  most four times ordinary column-load edge energy; sectorwise hydrodynamic column profiles cost
  only second order at strict-half displacement, while component pair switches preserving product
  distort physical Gibbs pair weight only by `O(H^2/X^2)`.

## Goal

Reduce the genuinely non-circular Route E producer after the recurrence-weighted conductance
theorem.  Global column balance is stronger than needed, while retaining the sign of the complete
inverse-load edge flux is exactly circular.  The surviving object should be an arithmetic
roughness/collision invariant which can be attacked by the explicit entropy-complement
convolution and by componentwise pair switching.

## Gates

- [x] 0 → 1 in-progress: source-pure finite objects and hostile tests stated
- [x] 1 → 2 fully-proven: Theorems A--E below have complete finite proofs
- [x] 2 → 3 formalized: exact finite laws are closed in umbrella-wired Lean
- [ ] 3 → 4 publication-ready: requires arithmetic pair-switch admissibility theorem

## 1. Finite setup

Let `V` be a finite linearly ordered physical aperture.  Write `y_i` for its strictly increasing
physical coordinate, `s_i in {+1,-1}` for Möbius sign, and

\[
 w_i=e^{-x y_i},\qquad Z=\sum_iw_i,\qquad J=\sum_i s_iw_i .
\tag{1}
\]

Let `b_ij=b_ji>=0`, with `b_ii=0`, and assume `b_ij>0` only when
`s_j=-s_i` and `|y_i-y_j|<=H`.  Put

\[
 d_i=\sum_jb_{ij},\qquad
 q_i=\begin{cases}d_i^{-1},&d_i>0,\\0,&d_i=0,\end{cases}
\qquad
 I_i=\mathbf 1_{d_i=0}w_i .
\tag{2}
\]

All unordered edge sums below use orientation `i<j`, hence `y_i<y_j` and `w_j<=w_i`.

## 2. Signed edge flux is exact but circular

### Theorem A — exact signed inverse-load flux

Define

\[
 J_{\rm iso}=\sum_i s_iI_i,
\tag{3}
\]

\[
 C_x=\sum_{i<j}b_{ij}s_i(w_i-w_j)q_i,
\qquad
 L_x=\sum_{i<j}b_{ij}s_iw_j(q_i-q_j).
\tag{4}
\]

Then

\[
 \boxed{J=J_{\rm iso}+C_x+L_x.}
\tag{5}
\]

Moreover,

\[
 |C_x|\le xHZ.
\tag{6}
\]

#### Proof

Identity `w_i=I_i+d_iw_iq_i` gives

\[
 J=J_{\rm iso}+\sum_{i,j}s_i b_{ij}w_iq_i.
\]

Pair `(i,j)` with `(j,i)`.  Symmetry of `b` and sign reversal on every live edge give

\[
 b_{ij}(s_iw_iq_i+s_jw_jq_j)
 =b_{ij}s_i(w_iq_i-w_jq_j).
\]

Finally

\[
 w_iq_i-w_jq_j=(w_i-w_j)q_i+w_j(q_i-q_j),
\]

which proves `(5)`.  Taking absolute values only in `C_x`, using
`0<=w_i-w_j<=x(y_j-y_i)w_i<=xHw_i`, and summing incidence against `q_i=d_i^{-1}` proves `(6)`.
∎

### Corollary A.1 — exact circularity firewall

For every `eta>=0`,

\[
 |L_x|\le\eta
 \quad\Longleftrightarrow\quad
 |J-J_{\rm iso}-C_x|\le\eta .
\tag{7}
\]

At `x=0`, `C_0=0` and `L_0=J-J_iso` exactly.  Thus a theorem which merely “retains all alternating
signs” in the complete edge flux `L_x` has not produced cancellation; it has renamed the current.
The positive Dirichlet relaxation below is non-circular precisely because it loses this exact
identity.

## 3. Full two-sided rows remove inverse-load denominators

Let `P_ij>=0` be a source-predeclared recurrence kernel on the same aperture, supported on the
same parity-reversing `H`-local relation.  Assume every row is complete:

\[
 \sum_jP_{ij}=1.
\tag{8}
\]

Define incoming column load and symmetric base

\[
 \ell_i=\sum_jP_{ji},\qquad b_{ij}={P_{ij}+P_{ji}\over2}.
\tag{9}
\]

The symmetric degree and reciprocal degree are

\[
 d_i={1+\ell_i\over2},\qquad q_i={2\over1+\ell_i}.
\tag{10}
\]

In particular there are no isolated vertices.

Define

\[
 \mathcal E_q=
 \sum_{i<j}b_{ij}w_j(q_i-q_j)^2,
\qquad
 \mathcal E_\ell=
 \sum_{i<j}b_{ij}w_j(\ell_i-\ell_j)^2.
\tag{11}
\]

### Theorem B — ordinary column-load gradient reduction

One has the exact edge identity

\[
 q_i-q_j=
 {2(\ell_j-\ell_i)\over(1+\ell_i)(1+\ell_j)}
\tag{12}
\]

and hence

\[
 \boxed{\mathcal E_q\le4\mathcal E_\ell.}
\tag{13}
\]

Consequently the existing recurrence-weighted conductance theorem sharpens to

\[
 \boxed{
 |J|\le xHZ+
 \sqrt{(1+e^{xH})Z\,\mathcal E_\ell}.}
\tag{14}
\]

#### Proof

Equation `(10)` gives `(12)` by one subtraction.  Since every column load is nonnegative,
`(1+ell_i)(1+ell_j)>=1`; squaring `(12)`, multiplying by the nonnegative edge weight, and summing
proves `(13)`.  The recurrence-weighted bridge is

\[
 |J|\le xHZ+{1\over2}\sqrt{(1+e^{xH})Z\mathcal E_q}.
\]

Insert `(13)`. ∎

At `x=X^{-1}`, `H=X^{1/2+o(1)}`, and `Z=X^{1+o(1)}`, the new sufficient arithmetic producer is

\[
 \boxed{\mathcal E_\ell\le X^{o(1)}.}
\tag{15}
\]

It asks for edge regularity of the ordinary rough-convolution column load, not global
`ell_i=1+o(1)`, weighted Hall, or inverse-load control near empty columns.  Full outgoing rows on
both signs are essential: in the one-sign specialization the row term in `(10)` disappears and
the energy reverts to reverse Pearson chi-square.

## 4. Sectorwise hydrodynamic profile theorem

Fix `X>0`.  Let `sigma_i` be a finite source-declared sector label, including reciprocal marker and
zero/one-large-prime seam labels.  Split `(11)` into same-sector and cross-sector edge energies.
Suppose, for each sector `a`,

\[
 \ell_i=\Lambda_a(y_i/X)+\eta_i\qquad(\sigma_i=a),
\tag{16}
\]

where every `Lambda_a` is `L`-Lipschitz.  Put

\[
 \begin{aligned}
 \mathcal R_{\rm same}
 &=\sum_{i<j:\,\sigma_i=\sigma_j}
   b_{ij}w_j(\eta_i-\eta_j)^2,\\
 \mathcal E_{\rm cross}
 &=\sum_{i<j:\,\sigma_i\ne\sigma_j}
   b_{ij}w_j(\ell_i-\ell_j)^2.
 \end{aligned}
\tag{17}
\]

### Theorem C — hydrodynamic load modes are power-free

\[
 \boxed{
 \mathcal E_\ell
 \le 2\mathcal R_{\rm same}+\mathcal E_{\rm cross}
 +{L^2H^2\over2X^2}(1+e^{xH})Z .}
\tag{18}
\]

#### Proof

On a same-sector edge,

\[
 |\Lambda_a(y_i/X)-\Lambda_a(y_j/X)|\le LH/X.
\]

Apply `(u+v)^2<=2u^2+2v^2` to `(16)`, multiply by `b_ijw_j`, and sum.  The symmetric edge-mass
budget from the recurrence kernel is

\[
 \sum_{i<j}b_{ij}w_j\le{1\over4}(1+e^{xH})Z.
\]

Adding the untouched cross-sector energy proves `(18)`. ∎

Thus `(15)` follows from the strictly weaker, structured target

\[
 L=X^{o(1)},\qquad
 \mathcal R_{\rm same}\le X^{o(1)},\qquad
 \mathcal E_{\rm cross}\le X^{o(1)}.
\tag{19}
\]

The macroscopic profile may vary by order one.  Only its microscopic edge roughness and literal
seam jumps cost energy.  This is the precise point where entropy-complement rough convolution and
normalized seam recurrence must enter.

## 5. Sharp firewall: two-sidedness and alternating global signs do not imply `(15)`

### Theorem D — complete-bipartite row-kernel energy

Let one block have `a` positive and `b` negative vertices.  Send each positive row uniformly to
all negative vertices and each negative row uniformly to all positive vertices:

\[
 P_{LR}=1/b,\qquad P_{RL}=1/a.
\tag{20}
\]

Then all rows have mass one, forward and reverse supports agree, and

\[
 \ell_L={b\over a},\qquad \ell_R={a\over b},\qquad
 q_L={2a\over a+b},\qquad q_R={2b\over a+b}.
\tag{21}
\]

At unit Gibbs weight,

\[
 \boxed{\mathcal E_q={2(a-b)^2\over a+b}.}
\tag{22}
\]

#### Proof

Every edge has symmetric weight `(a+b)/(2ab)`, and there are `ab` edges.  Substitute the
difference `2(a-b)/(a+b)` from `(21)`. ∎

For `a=2h`, `b=h`, energy is `2h/3`, while every subset has opposite neighborhood at least half
its cardinality.  Alternate blocks `(2h,h)` and `(h,2h)`.  Pair their physical coordinate lists by
a translation of size `O(H)`, matching every positive slot in one block with a negative slot in
the other and conversely.  For matched coordinates `y,y+Delta`,
`|e^{-xy}-e^{-x(y+Delta)}|<=x|Delta|e^{-x min(y,y+Delta)}`.  Hence paired signed currents cost at
most `O(xH)` times paired Gibbs mass.  At `x=X^{-1}` and
\(h\asymp H=X^{1/2}\), summing \(\asymp X/H\) paired blocks gives current
`O(X^{1/2})`; `(22)` and comparability of all Gibbs weights on the physical shell give
\(\mathcal E_q\asymp X\).

Therefore full two-sided rows, reverse support, constant-factor near-Hall, no isolated mass, and
alternating finite-volume cancellation still do not force the positive energy producer.  Any use
of `(15)` must prove actual entropy-complement load smoothness; degree exponents and global signed
cancellation cannot substitute for it.

## 6. Component recombination is Gibbs-compatible at second order

The grown HTGeometry corpus proves two exact facts:

1. universal pairwise partial-swap recurrence is equivalent to additive separation across the
   swapped coordinate cut;
2. for an additive component spectrum, two-history equal-energy partners are exactly independent
   component recombinations, with Boolean orbit size `2^d` at component Hamming distance `d`.

For Route E, logarithm of a squarefree block product is additive.  Hence a component recombination
of two physical histories preserves their pair product.  Physical Gibbs weight is not logarithmic,
so compatibility requires a separate estimate.

### Theorem E — pair-product Gibbs curvature

Let `X>0`, `0<=H<X`, and

\[
 a,b,c,d\in[X-H,X+H],\qquad ab=cd.
\tag{23}
\]

Then

\[
 \boxed{
 |e^{-a/X}+e^{-b/X}-e^{-c/X}-e^{-d/X}|
 \le 2\bigl(e^{-1}+e^{-1+H/X}\bigr){H^2\over X^2}.}
\tag{24}
\]

#### Proof

Write `a=X+A`, ..., `d=X+D`, with every capital letter of modulus at most `H`.  Product equality
gives

\[
 X(A+B-C-D)=CD-AB,
\]

and therefore

\[
 |A+B-C-D|\le {2H^2\over X}.
\tag{25}
\]

For `f(t)=e^{-t/X}`,

\[
 f'(X)=-e^{-1}/X,
 \qquad
 \sup_{[X-H,X+H]}|f''|\le e^{-1+H/X}/X^2.
\]

Taylor's theorem at `X` bounds each quadratic remainder by
`e^{-1+H/X}H^2/(2X^2)`.  The four remainders contribute at most
`2e^{-1+H/X}H^2/X^2`; the linear term is bounded by `(25)` times `e^{-1}/X`.
This is `(24)`. ∎

If a source-defined pair-switching construction has total absolute history weight
`X^{1+o(1)}`, then `(24)` costs only

\[
 X^{1+o(1)}{H^2\over X^2}=X^{o(1)}
\tag{26}
\]

at strict-half displacement.  Thus product-coordinate versus physical-Gibbs mismatch is not the
obstruction to using component recombination.  Remaining obstruction is arithmetic closure and
dispersion of recombined entropy-complement histories.

### Corollary E.1 — Boolean switching cardinality alone is rate-insufficient

Current entropy-complement histories have only `O(log log X)` prime/block components.  The
HTGeometry Boolean recombination orbit therefore has cardinality at most

\[
 2^{O(\log\log X)}=X^{o(1)}.
\tag{27}
\]

Orbit size alone cannot turn an `X^{1+o(1)}` raw collision budget into the required `X^{o(1)}`
centered budget.  A successful switching proof must exploit the square-root family of actual
structured-token choices or prove cancellation of the centered collision weights; relabeling the
Boolean cube as power-scale entropy would be false.

## 7. Heavy conjecture → proof/failure loop

### Loop A — use the new all-order Wold prime-clock profile as Route E dissipation

`[FAILED PRODUCER TEST]`  `SourceHorizontalWoldPrimeClockProfile.lean` now gives a complete
nonlinear profile, reflection oddness, strict sign away from zero, and unique zero.  It is genuine
source-horizontal knowledge, but it is a one-prime ordered-moment law.  No theorem maps it to the
ordinary-integer entropy-complement column load, collision quotient, or moving seam.  Using its
critical-line zero classification would insert an RH-equivalent receiver, not prove Route E.

### Loop B — keep signs in the inverse-load edge sum

`[FAILED EXACTLY AS THEATRE]`  Theorem A and Corollary A.1.  Complete signed flux reconstructs the
endpoint current.

### Loop C — complete outgoing rows on both parities and remove inverse denominators

`[PROVED SURVIVOR]`  Theorem B.  The live positive producer becomes ordinary column-load gradient
energy `(15)`.

### Loop D — infer `(15)` from row degree, co-degree, near-Hall, and alternating blocks

`[FAILED SHARPLY]`  Theorem D.  Those properties coexist with linear energy, even when paired
block orientations already give a square-root signed endpoint.

### Loop E — permit a source-derived macroscopic load profile

`[PROVED SURVIVOR]`  Theorem C.  Order-one hydrodynamic modes cost only `X^{o(1)}`; exact remaining
terms are within-sector microscopic roughness and cross-seam load energy.

### Loop F — use HTGeometry component recombination to close physical collision

`[PARTIAL SURVIVOR / CARDINALITY FAILURE]`  Theorem E closes physical Gibbs compatibility at
second order.  Corollary E.1 shows Boolean switch count alone is subpower and cannot supply the
missing power.  Sequential structured-token admissibility and weighted collision dispersion remain
the hard arithmetic work.

## 8. Revised Route E producer

Construct one canonical parity-agnostic entropy-complement row kernel on a common aperture, with
full rows outside an explicit `X^{1/2+o(1)}` Gibbs boundary budget.  Its remaining sufficient
producer is

\[
 \boxed{
 \mathcal E_{\ell,X}=
 \sum_{n<m}{P_X(n,m)+P_X(m,n)\over2}
 e^{-m/X}(\ell_X(n)-\ell_X(m))^2
 \le X^{o(1)}.}
\tag{28}
\]

Theorem C refines this to three arithmetic obligations:

1. source-derived sectorwise hydrodynamic column profiles with `X^{o(1)}` Lipschitz norm;
2. subpolynomial within-sector rough-convolution gradient after subtracting those profiles;
3. subpolynomial cross-edge load energy for the same zero/one-large-prime seam used by signed
   recurrence.

The new pair-switch route attacks item 2: pair incoming histories, recombine their independent
block/token coordinates, use `(24)` for Gibbs stability, and prove that non-admissible switches plus
weighted recombination collisions have total `X^{o(1)}` energy.  Item 3 cannot be optimized away;
it remains coupled to normalized signed seam flux.

## 9. Honest status

Theorems A--E are dependency-closed finite paper mathematics.  They create missing Route E
knowledge:

- exact signed inverse-load flux is classified as circular;
- full two-sided rows reduce inverse-load energy to ordinary column-load gradient energy;
- slow sectorwise load profiles are harmless at strict-half displacement;
- existing degree/near-Hall/alternating-sign data do not imply the gradient estimate;
- component pair switching preserves physical Gibbs pair mass to second order; and
- its Boolean orbit cardinality is insufficient without arithmetic token dispersion.

Route E and RH remain open.  No common-aperture full-row kernel, estimate `(28)`, recombination
admissibility/dispersion theorem, normalized seam accumulation, endpoint bound, or RH proof is
claimed.

## Log

- 2026-08-11 — paper proofs completed after read-only audit of grown HTGeometry/RHTower corpus.
- 2026-08-11 — formalized in `RouteESignedInverseLoadFlux.lean`,
  `RouteETwoSidedColumnLoadGradient.lean`, and `RouteEGibbsProductStability.lean`; targeted builds
  pass.  Axiom audit reports only `propext`, `Classical.choice`, and `Quot.sound`.  No umbrella or
  full build was run.
