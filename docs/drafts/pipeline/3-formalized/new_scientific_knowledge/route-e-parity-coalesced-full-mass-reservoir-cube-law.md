# Route E parity-coalesced full-mass reservoir cube law

- **ID:** `ROUTE-E-PARITY-COALESCED-FULL-MASS-CUBE-001`
- **Stage:** 3-formalized
- **Type:** `[THEOREM (paper)]` / `[NEW SOURCE RELATION]` / `[OPPOSITE-SIGN FULL-MASS NEAR-HALL]`
- **Parent:** `route-e-grade-recurrent-sparse-reservoir-cube-admission.md`
- **Source:** `OPEN-SOURCE-001`
- **RH used:** no
- **Computation used:** no
- **Lean status:** formalized. `RHTower/MobiusParityCoalescedFullMassCube.lean` has the exact
  finite parity-coalescence and two-sided Wold-drift core: explicit odd/even packets, both `+1` and
  `-1` drift for odd arity and even arity at least four, exact arity-two downward boundary, sign
  reversal, and subset grade control. `RHTower/MobiusParityCoalescedProductLaws.lean` adds the
  robust token range `(15)`/`(17)`, the mixed Gibbs cost `(30)`, the row supply `(32)`, the physical
  co-degree `(37)`, and the seam law `(40)`. Sparse-forbidden token supply is a cited input; the
  unit Carleson load and normalized seam flux `(43)` are the card's own open core.

## 1. Result

The grade-recurrent relation previously obtained opposite parity by selecting a maximal odd
subset of active coordinates.  If the number of active blocks was even, this deleted one active
block.  Its selected source mass could then be only (X^{1/2-o(1)}), so the guaranteed
opposite-sign row degree fell to (X^{1/4-o(1)}).  Scale-weighted co-degree recovered near-Hall,
but left an artificial row-dependent half-density.

That loss is unnecessary.  When active block count is even, coalesce two active blocks into one
replacement coordinate.  Coordinate count becomes odd, while source product carried by all
coordinates is unchanged.  Coalesced coordinate receives grade shift (-1); its more economical
reservoir breadth makes its structured (E_3) argument at least (Y^2), so existing
sparse-forbidden-support theorem applies with room to spare.

The resulting source-predeclared relation has following properties uniformly for every central
squarefree anchor (n\in[X,2X]):

1. every coordinate reverses Möbius parity;
2. number of coordinates is odd, hence full terminal has sign (-\mu(n));
3. full terminal changes Wold breadth by exactly (+1) or (-1);
4. all active source mass (n/a=X^{1-o(1)}) participates;
5. every row has (X^{1/2-o(1)}) distinct opposite-sign full terminals;
6. every physical terminal has at most (X^{1/2+o(1)}) incoming anchors;
7. full-terminal relation is automatically compatible with moving (1\to0) seam; and
8. full mixed Gibbs cost remains (X^{-1/2+o(1)}) per anchored cube.

Consequently every anchor family (A) has

\[
 \#N_{\rm coal}(A)\ge \#A\,X^{-o(1)}                                      \tag{1}
\]

distinct ordinary opposite-sign neighbors, with no maximal-odd-subset weight (U_n^{-1/2}).
Remaining fixed-relation theorem is now unweighted subpower-to-unit interval Carleson plus
normalized co-moving flux.

## 2. Input relation and notation

Use notation and paper theorems from
`route-e-grade-recurrent-sparse-reservoir-cube-admission.md`.  Thus

\[
 L=\log\log X,\qquad k=\lfloor\sqrt L\rfloor,
 \qquad Y=\exp((\log X)^{1/3}),                           \tag{2}
\]

and a central squarefree anchor is partitioned into ordered blocks

\[
 n=a\prod_{i\in I}u_i,qquad k_i=\omega(u_i),qquad
 \frac{k}{2}\le k_i\le k,\qquad |I|\le3\sqrt L.          \tag{3}
\]

Inactive product satisfies

\[
 a=X^{o(1)},                                               \tag{4}
\]

while every active block obeys

\[
 u_i\ge YZ^{k_i-2},\qquad
 Z=\exp\!\left(\frac{\log X}{L^2}\right).                \tag{5}
\]

Reservoir pool is

\[
 \mathcal P_X=\{p:\ W<p\le Z\},\qquad
 W=\exp(\exp\sqrt L).                                    \tag{6}
\]

It contains enough primes for every allocation below, and every product of at most (2L)
reservoir primes is (X^{o(1)}).

## 3. Source-defined parity coalescence

Write active indices in increasing order as

\[
 I=\{i_1<\cdots<i_d\}.                                    \tag{7}
\]

Define a partition \(\mathcal G(n)\) of (I) as follows.

- If (d) is odd, every group is a singleton.
- If (d) is even, first group is (G_0=\{i_1,i_2\}), and every remaining group is a
  singleton.

Put (g=\#\mathcal G(n)).  Since (d\ge1),

\[
 g=\begin{cases}d,&d\text{ odd},\\ d-1,&d\text{ even},\end{cases}
 \qquad g\text{ is odd}.                                 \tag{8}
\]

For (G\in\mathcal G(n)), set

\[
 U_G=\prod_{i\in G}u_i,qquad K_G=\sum_{i\in G}k_i.      \tag{9}
\]

Choose source-defined shifts \(\varepsilon_G\in\{+1,-1\}\) with following rules.

- For odd (d), alternate (+1,-1,+1,\ldots,+1), so
  \(\sum_G\varepsilon_G=+1\).
- For even (d), give coalesced group (G_0) shift (-1), and assign equal numbers of
  (+1) and (-1) to remaining even number of singleton groups, so
  \(\sum_G\varepsilon_G=-1\).

Define reservoir breadth

\[
 b_G=K_G-3+\varepsilon_G
 =\begin{cases}K_G-2,&\varepsilon_G=+1,\\
                 K_G-4,&\varepsilon_G=-1.
   \end{cases}                                           \tag{10}
\]

All (b_G) are positive for large (X).  Their total is at most (2L):

\[
 B:=\sum_Gb_G
 =\sum_{i\in I}k_i-3g+\sum_G\varepsilon_G
 \le\omega(n)\le2L.                                     \tag{11}
\]

Choose every ordered family of pairwise-disjoint reservoir sets

\[
 R_G\subseteq\mathcal P_X\setminus\{p:p\mid n\},qquad
 \#R_G=b_G,                                               \tag{12}
\]

and put

\[
 t_G=\prod_{p\in R_G}p,qquad T=\prod_Gt_G=X^{o(1)}.      \tag{13}
\]

This is fixed from (n,X), ordinary prime order, and all admissible allocations.  It inspects no
Möbius imbalance, exceptional set, partial sum, or divisor observation.

## 4. Coalesced coordinate remains in robust (E_3) range

Put

\[
 y_G=\frac{U_G}{t_G}.                                     \tag{14}
\]

For singleton (G=\{i\}), equations `(5)` and `(10)` give

\[
 y_G\ge
 \begin{cases}
 Y,&\varepsilon_G=+1,\\
 YZ^2,&\varepsilon_G=-1.
 \end{cases}                                             \tag{15}
\]

If (d) is even, coalesced group has shift (-1).  Therefore

\[
 U_{G_0}=u_{i_1}u_{i_2}
 \ge Y^2Z^{k_{i_1}+k_{i_2}-4}
 =Y^2Z^{K_{G_0}-4},                                      \tag{16}
\]

and (t_{G_0}\le Z^{K_{G_0}-4}), so

\[
 \boxed{y_{G_0}\ge Y^2.}                                \tag{17}
\]

This is key robustness gain.  Coalescing does not push structured token below known all-interval
range; it improves lower scale.

Process groups in source order.  At each stage forbid prime support of (n), all reservoirs, and
all earlier tokens.  Forbidden set has (O(L)) elements, while `(15)`--`(17)` give
\(\log\log y_G\ge(1/3+o(1))L\).  Sparse-forbidden (E_3) theorem therefore supplies a squarefree
three-prime token (m_G), pairwise coprime across groups and coprime to (a,n,T), with

\[
 y_G<m_G\le y_G+\sqrt{y_G}(\log y_G)^{1.55}.              \tag{18}
\]

Define

\[
 q_G=t_Gm_G.                                              \tag{19}
\]

Then

\[
 \omega(q_G)=b_G+3=K_G+\varepsilon_G,qquad
 \mu(q_G)=-\mu(U_G),                                     \tag{20}
\]

and

\[
 0<q_G-U_G\le\sqrt{U_Gt_G}(\log U_G)^{1.55}.             \tag{21}
\]

## 5. Odd full-mass cube

For (S\subseteq\mathcal G(n)), define

\[
 v_S=a\prod_{G\in S}q_G\prod_{G\notin S}U_G.            \tag{22}
\]

All factors in every corner are pairwise coprime.  Hence

\[
 \mu(v_S)=(-1)^{|S|}\mu(n),                              \tag{23}
\]

and

\[
 \omega(v_S)=\omega(n)+\sum_{G\in S}\varepsilon_G.      \tag{24}
\]

Because (g) is odd, full terminal (v_{\mathcal G(n)}) satisfies

\[
 \boxed{\mu(v_{\mathcal G(n)})=-\mu(n).}                 \tag{25}
\]

By construction of shifts,

\[
 \boxed{\omega(v_{\mathcal G(n)})-\omega(n)
   =\begin{cases}+1,&d\text{ odd},\\-1,&d\text{ even}.
     \end{cases}}                                        \tag{26}
\]

Every partial corner changes breadth by at most (g=O(\sqrt L)=o(L)), so all corners remain in
same central Wold sector.

Every coordinate obeys

\[
 \frac{q_G-U_G}{U_G}
 \le Y^{-1/2}(\log X)^{1.55}.                            \tag{27}
\]

Since (g=O(\sqrt L)),

\[
 \max_{S\subseteq\mathcal G(n)}\frac{v_S}{n}=1+o(1).     \tag{28}
\]

Thus relation stays in one co-moving multiplicative shell.

## 6. Mixed Gibbs cost is unchanged

Apply existing (g)-fold exponential mixed-difference bound to cube `(22)`.  With
(x\asymp X^{-1}), its absolute packet cost is at most

\[
 xg^ga\prod_G|q_G-U_G|.                                  \tag{29}
\]

By `(21)`, \(\prod_GU_G=n/a\), and `(13)`,

\[
 xg^ga\prod_G|q_G-U_G|
 \le xg^g\sqrt{anT}(\log X)^{1.55g}
 =X^{-1/2+o(1)}.                                         \tag{30}
\]

Coalescing two factors replaces
\(\sqrt{u_{i_1}t_{i_1}}\sqrt{u_{i_2}t_{i_2}}\) by
\(\sqrt{u_{i_1}u_{i_2}t_{G_0}}\).  Both have same square-root source exponent and subpower
reservoir factor.  No analytic exponent is spent to repair parity.

## 7. Full half-density row supply

Fix one admissible reservoir allocation.  At every group, sparse-forbidden theorem gives

\[
 \gg \frac{\sqrt{y_G}}
 {(\log y_G)^{0.45}\log\log y_G}                    \tag{31}
\]

admissible sequential tokens.  Therefore number of labeled full terminals is at least

\[
 X^{-o(1)}\sqrt{\prod_Gy_G}
 =X^{-o(1)}\sqrt{\frac{n}{aT}}
 =X^{1/2-o(1)}.                                          \tag{32}
\]

A physical terminal has (O(L)) prime factors.  Assigning them to (a) and at most
(3\sqrt L) terminal groups, then choosing reservoir divisors, costs

\[
 (3\sqrt L+1)^{O(L)}2^{O(L)}=X^{o(1)}.                  \tag{33}
\]

For coalesced group one must additionally split one recovered source product into two ordered
source blocks.  Number of such splittings is at most number of its divisors, hence at most
\(2^{O(L)}=X^{o(1)}\), already absorbed in `(33)`.  Thus every anchor has

\[
 \boxed{D_{\rm coal}(n)\ge X^{1/2-o(1)}}                \tag{34}
\]

distinct ordinary opposite-sign full terminals.

The trivial integer count inside each token interval also gives matching upper exponent

\[
 D_{\rm coal}(n)\le X^{1/2+o(1)}.                        \tag{35}
\]

So every row now lives at same physical half-density exponent; no selected-mass parameter (U_n)
remains.

## 8. Physical co-degree and opposite-sign near-Hall

Fix physical full terminal (v).  After structural assignment `(33)` and reservoir divisors are
fixed, each source group product (U_G) lies in inverse interval from `(21)` and has at most

\[
 O\!\left(\sqrt{q_Gt_G}(\log X)^{1.55}+1\right)          \tag{36}
\]

possible integer values.  Multiplying over groups and using \(\prod_Gq_G=v/a\),
\(T=X^{o(1)}\), and (v\asymp X), gives

\[
 \boxed{\#\{n:n\to v\}\le X^{1/2+o(1)}.}              \tag{37}
\]

Again coalesced source split contributes only (X^{o(1)}).  Counting anchor--terminal incidences
between arbitrary anchor family (A) and its physical terminal union gives from `(34)` and `(37)`

\[
 \boxed{\#N_{\rm coal}(A)\ge\#A\,X^{-o(1)}.}            \tag{38}
\]

Every target in `(38)` has opposite Möbius sign by `(25)`.  By `(28)`, same statement holds on
physical intervals after only co-moving boundary enlargement.

## 9. Moving seam is automatic at full terminal

Let (z=z(X)) satisfy

\[
 z/\sqrt X\to\infty,qquad
 \log z=(1/2+o(1))\log X.                                \tag{39}
\]

Existing seam theorem proves block containing unique prime (p>z) is active.  It belongs to
exactly one group of \(\mathcal G(n)\), possibly coalesced group.  Full terminal replaces every
group, so seam group cannot be omitted for parity reasons.

Every reservoir prime is at most (Z=o(\sqrt X)).  Every structured small factor is (X^{o(1)}),
and every balanced (E_3) factor is at most (\sqrt{2X}).  Hence every prime factor of every
replacement (q_G) is below (z) for large (X).  Therefore, on a one-large-prime anchor,

\[
 \boxed{
 \ell_z(n)=1,qquad
 \ell_z(v_{\mathcal G(n)})=0,qquad
 \mu(v_{\mathcal G(n)})=-\mu(n).}                       \tag{40}
\]

This closes simultaneous seam inclusion and opposite parity at full row degree.  Remaining seam
problem is normalized weight/endpoint flux, not admission and not selection of seam coordinate.

## 10. Conjecture--proof--failure loop

### Loop A: even active dimension forces deletion

`[CONJECTURE]` An opposite-sign target must omit one active coordinate whenever (d) is even.

`[FALSIFIED]` Coalescing two source blocks reduces coordinate count from (d) to (d-1), which is
odd, while full source product remains \(\prod_{i\in I}u_i\).  Equation `(25)` gives opposite sign
without deleting active mass.

### Loop B: coalescence leaves robust token range

`[CONJECTURE]` A merged coordinate requires too many reservoir primes and drives its (E_3)
argument below (Y).

`[FALSIFIED]` Give merged coordinate shift (-1), hence reservoir breadth (K_G-4).  Product of
two active lower bounds is (Y^2Z^{K_G-4}), proving exact margin `(17)`.

### Loop C: parity repair costs analytic exponent

`[CONJECTURE]` Replacing two square-root gaps by one merged gap loses strict-half mixed scale.

`[FALSIFIED]` Square-root products associate exactly; reservoir products differ only by
(X^{o(1)}).  Equation `(30)` is unchanged.

### Loop D: maximal-odd scale weight is intrinsic

`[CONJECTURE]` Opposite-sign co-degree must retain (U_n^{-1/2}).

`[FALSIFIED]` All active mass participates in odd coalesced cube, so row scale is uniformly
(X^{1/2-o(1)}).  Equations `(34)`--`(38)` prove unweighted opposite-sign near-Hall.

### Loop E: unweighted near-Hall is unit Carleson

`[CONJECTURE]` Uniform half-density exponents imply canonical row weights have column load
(1+o(1)).

`[FAILED]` Exponent comparison gives only

\[
 \sup_v\sum_{n\to v}\frac1{D_{\rm coal}(n)}\le X^{o(1)}. \tag{41}
\]

Subpower factor cannot be renamed unit.  Coalescence removes parity/scale artefact but does not
prove fine collision conditioning.

## 11. Exact revised frontier

For coalesced relation, define canonical row kernel

\[
 P_X(n,v)=\frac{\mathbf1_{n\to v}}{D_{\rm coal}(n)}.      \tag{42}
\]

Rows sum exactly one; support is ordinary, opposite-sign, co-moving, and seam-compatible.  It now
suffices to prove

\[
 \boxed{
 \sup_{v\text{ in every extended physical interval}}
 \sum_nP_X(n,v)\le1+o(1)}                                \tag{43}
\]

outside (X^{1/2+o(1)}) Gibbs budget, together with normalized (1\to0) endpoint flux of same
kernel.  This premise is

`FULL-MASS-ODD-CUBE-UNIT-CARLESON-AND-COMOVING-FLUX`.

Compared with predecessor, following are no longer open:

- parity correction;
- row-dependent selected mass (U_n);
- loss of one active coordinate;
- inclusion of forced seam block; and
- power-scale row/co-degree balance.

What remains is fine (1+o(1)) collision law and normalized sector flux.  Route E and RH are not
claimed complete.

## 12. Scientific and formal status

`[PAPER-PROVED] [NOVELTY UNVERIFIED]` for construction and equations `(8)`--`(40)`.
Proof uses existing sparse-forbidden (E_3) theorem, reservoir-pool laws, mixed derivative bound,
and physical inverse-interval count.  New content is parity coalescence and its exact consequence:
full-mass, unweighted, seam-compatible opposite-sign near-Hall.

No external literature search was performed under current instruction.  No Lean was written or
built while corpus refactor is active.

## 13. Two-sided full-mass Wold drift

The shift choice in §3 was canonical but unnecessarily one-sided.  Same coalesced relation admits
both terminal drifts on every anchor except exact two-active-block case.

### Proposition `[PAPER-PROVED]`

If active count \(d\) is odd, assign singleton shifts so their sum is either \(+1\) or \(-1\).
Both choices are admissible: a singleton with shift \(+1\) has \(y_G\ge Y\), while one with shift
\(-1\) has \(y_G\ge YZ^2\).

If \(d\ge4\) is even, keep coalesced group shift equal to \(-1\).  There are \(d-2\ge2\) remaining
singleton groups.  Their even count permits either total shift \(0\), giving full drift \(-1\), or
total shift \(2\), giving full drift \(+1\).  Every singleton remains in range by `(15)`, and
coalesced group remains in stronger range `(17)`.

Thus, for \(d\) odd or \(d\ge4\) even, relation contains two source-predeclared full-mass terminal
families

\[
 \omega(v_+)-\omega(n)=+1,
 \qquad
 \omega(v_-)-\omega(n)=-1,                              \tag{44}
\]

both of opposite Möbius sign, both with row degree \(X^{1/2-o(1)}\), co-degree
\(X^{1/2+o(1)}\), mixed cost \(X^{-1/2+o(1)}\), and same seam law `(40)`.  Proofs of §§4--9 use
only individual bounds for shifts and are unchanged.

When \(d=2\), sole coalesced group has robust shift \(-1\).  Assigning it \(+1\) would only give

\[
 y_{G_0}\ge Y^2/Z^2,                                   \tag{45}
\]

which does not reach known all-interval \(E_3\) range.  Therefore current source theorem proves
only downward full-mass drift in this exact case.  No upward claim is made.

This removes one-sided Wold orientation as a capacity obstruction on every multi-group anchor.
Fine physical column load and normalized seam flux remain open.

## 14. Reciprocal-allocation successor

Uniform row kernel (42) is no longer strongest normalization.  Successor theorem
route-e-reciprocal-allocation-square-root-jacobian-carleson-reduction.md assigns allocation
mass proportional to \(1/T\), then distributes it uniformly over distinct terminals of that
allocation.  Per-edge weight is \(T^{-1/2}\) up to explicit
\(\exp(O(L^{3/2}))\) factors, while inverse physical interval has Jacobian \(T^{1/2}\).
These cancel exactly.

Resulting row-stochastic kernel \(P_X^{\rm har}\) satisfies

\[
 \sup_v\sum_nP_X^{\rm har}(n,v)
 \le\exp(O(L^{3/2})),                                   \tag{46}
\]

with no residual \(X^{O(1/L)}\) dependence on reservoir product.  Reciprocal allocation exponent
is unique exponent with this cancellation.  Therefore premise in §11 is sharpened to

HARMONIC-SQUARE-ROOT-UNIT-CARLESON-AND-COMOVING-FLUX.

Unit \(1+o(1)\) and normalized seam flux remain open.

## Lean status (final)

Every proved statement of this card is formal and axiom-clean
(`[propext, Classical.choice, Quot.sound]`).  The cited inputs — the sparse-forbidden `E_3`
theorem `(18)`/`(31)`, the reservoir-pool laws, the `g`-fold mixed derivative bound `(29)`, and the
physical inverse-interval count `(36)` — enter as hypotheses; they are not content of this card.

    RHTower/MobiusParityCoalescedFullMassCube.lean    (axiom-clean, wired, built)
      oddUpShiftPacket, oddDownShiftPacket,
        evenCoalescedDownShiftPacket,
        evenCoalescedUpShiftPacket                    **(8)/(10)** the source-defined shift packets
      *_length, *_sum, *_values, *_head              their arity, total drift, admissible values,
                                                      and the coalesced head shift `-1`
      exists_twoSided_fullMass_shiftPackets_of_odd,
        exists_twoSided_fullMass_shiftPackets_of_even **(44)** both `+1` and `-1` full-mass terminal
                                                      drift for odd arity and for even arity at
                                                      least four
      two_activeBlocks_coalesce_to_downward_singleton **(45)** the exact arity-two boundary: only
                                                      downward drift is claimed
      prod_coordinateReversals_eq_neg_of_odd          **(23)/(25)** an odd packet of coordinate
                                                      reversals reverses the product sign
      abs_subset_sum_le_card_of_unitShifts            **(24)/(26)** every corner stays within the
                                                      coordinate count of the source breadth

    RHTower/MobiusParityCoalescedProductLaws.lean     (axiom-clean, wired, built)
      prod_sqrt_mul                                   the single identity behind every product law:
                                                      `prod sqrt(f g) = sqrt(prod f * prod g)`
      token_range_ge                                  **(15)/(17)** the robust token range; the
                                                      three cases are `M = Y`, `M = YZ²`,
                                                      `M = Y²` with `E = Z^{b_G}`
      mixed_gibbs_cost_le                             **(30)** `a * prod (q_G - U_G)
                                                       <= sqrt(a n T) * Lambda^g`: the per-group
                                                      square-root gaps associate exactly and the
                                                      reservoir product enters only through
                                                      `sqrt(T)`
      row_supply_ge                                   **(32)** `prod N_G >= sqrt(n/(aT))/prod c_G`,
                                                      the half-density row degree
      codegree_le                                     **(37)** `prod (sqrt(q_G t_G) Lambda + 1)
                                                       <= (2 Lambda)^g sqrt(v T/a)`, the matching
                                                      half-density column bound
      seamCount, seamCount_eq_zero_iff,
        seamCount_mul_eq_zero,
        seamCount_prod_eq_zero,
        seamCount_fullTerminal_eq_zero                **(40)** every replacement coordinate and the
                                                      inactive product have all prime factors below
                                                      the seam, so the full terminal carries no
                                                      prime above it; combined with `(25)` this is
                                                      the simultaneous seam-inclusion and
                                                      opposite-parity statement

Sections 10--11 are the falsification record and the card's declared open core `(43)`
(`FULL-MASS-ODD-CUBE-UNIT-CARLESON-AND-COMOVING-FLUX`); section 14 records that the successor
card sharpens it to the harmonic form, which is itself now formal.
