# Renormalized formation work, divisor charge, and divisible-lift selection law

- **ID:** ULF-DFPM-1
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) / EXACT RH EQUIVALENCE / SELECTION MECHANISM
- **Status:** [PAPER-PROVED] [DEPENDENCY-CLOSED] [UNCONDITIONAL EQUIVALENCE] [INTEGER-CHARGE CONSERVATION] [DIVISIBLE-LIFT SELECTION] [SOURCE ROOT GENESIS OPEN] [NO LEAN IN THIS PASS]

## 1. Setup

Fix integers (m\ge12) and (r\ge2).  Let

\[
 S_j(s)=\sum_{n\in A_j}n^{-s}=\zeta(s)H_j(s).
 \tag{DWP.1}
\]

The high-exponent shell theorem gives a holomorphic zero-free function (H_j) on

\[
 \mathbb H_{1/2}=\{s\in\mathbb C:\Re s>1/2\}.
 \tag{DWP.2}
\]

On the positive convergence ray (\sigma>1), define the inherited formation survival

\[
 A_{m,r}(\sigma)=\frac{S_m(r\sigma)}{S_{rm}(\sigma)}\in(0,1)
 \tag{DWP.3}
\]

and formation work

\[
 W_{m,r}(\sigma)=-\log A_{m,r}(\sigma).
 \tag{DWP.4}
\]

The source normalization pole forces (A_{m,r}(\sigma)\to0) as (\sigma\downarrow1).  Remove that
universal zero and define the meromorphic survival transfer

\[
 \boxed{
 R_{m,r}(s)=\frac{S_m(rs)}{(s-1)S_{rm}(s)}.}
 \tag{DWP.5}
\]

## 2. Divisor theorem

### Theorem 2.1 -- exact strict-right divisor

The transfer (R_{m,r}) is meromorphic on (\mathbb H_{1/2}), extends holomorphically and
nonvanishingly across (s=1), has no zeros in (\mathbb H_{1/2}), and has a pole of order (q) at
(\rho\in\mathbb H_{1/2}) exactly when (\zeta) has a zero of order (q) at (\rho).

Its value at the normalization point is

\[
 \boxed{
 R_{m,r}(1)=\frac{S_m(r)}{H_{rm}(1)}>0.}
 \tag{DWP.6}
\]

#### Proof

Using (DWP.1),

\[
 R_{m,r}(s)
 =\frac{\zeta(rs)H_m(rs)}{(s-1)\zeta(s)H_{rm}(s)}.
 \tag{DWP.7}
\]

If (\Re s>1/2) and (r\ge2), then (\Re(rs)>1).  Therefore (\zeta(rs)) is holomorphic and
zero-free there.  Both shell units in (DWP.7) are holomorphic and zero-free by hypothesis.

The function

\[
 G(s)=(s-1)\zeta(s)
 \]

extends holomorphically through (s=1) with (G(1)=1).  Away from (1), its zeros in
(\mathbb H_{1/2}) are exactly the nontrivial zeta zeros, with their multiplicities.  Thus every
factor in the numerator of (DWP.7) is holomorphic and nonzero, while the denominator can vanish
only through (G).  This proves the zero and pole statements.  Substitution at (s=1) gives
(DWP.6). ∎

### Corollary 2.2 -- renormalized real work

For real (\sigma>1),

\[
 \boxed{
 \widetilde W_{m,r}(\sigma)
 :=W_{m,r}(\sigma)+\log(\sigma-1)
 =-\log R_{m,r}(\sigma).}
 \tag{DWP.8}
\]

It extends real-analytically across (\sigma=1) with

\[
 \boxed{
 \widetilde W_{m,r}(1)
 =\log\frac{H_{rm}(1)}{S_m(r)}.}
 \tag{DWP.9}
\]

Thus raw proper-work divergence is exactly the universal normalization term
(-\log(\sigma-1)); the finite remainder carries the continued divisor.

## 3. Branch-free work form and integer charge

Define the meromorphic one-form

\[
 \boxed{
 \omega_{m,r}
 =-d\log R_{m,r}
 =-\frac{R_{m,r}'(s)}{R_{m,r}(s)}\,ds.}
 \tag{DWP.10}
\]

### Theorem 3.1 -- charge formula

The form (\omega_{m,r}) is holomorphic at (s=1).  At every strict-right zeta zero (\rho) of
multiplicity (q),

\[
 \boxed{\operatorname{Res}_{s=\rho}\omega_{m,r}=q.}
 \tag{DWP.11}
\]

For any positively oriented piecewise smooth contour (\Gamma\subset\mathbb H_{1/2}) avoiding
zeros and enclosing only finitely many of them,

\[
 \boxed{
 \frac1{2\pi i}\int_\Gamma\omega_{m,r}
 =\sum_{\rho\ \mathrm{inside}\ \Gamma}\operatorname{ord}_\rho\zeta.}
 \tag{DWP.12}
\]

#### Proof

At (s=1), (R) is holomorphic and nonzero by Theorem 2.1, so its logarithmic derivative is
holomorphic.  If (R) has a pole of order (q) at (\rho), write

\[
 R(s)=(s-\rho)^{-q}u(s),
 \qquad u(\rho)\ne0.
\]

Then

\[
 -\frac{R'}R=\frac q{s-\rho}-\frac{u'}u,
\]

which proves (DWP.11).  The residue theorem gives (DWP.12). ∎

The integer in (DWP.12) is a formation-work charge.  It is independent of logarithm branch and of
the positive real gauge.

### Corollary 3.2 -- spectral cumulant shadow

Let (E_{rm,\sigma}[\log N]) and (\operatorname{Var}_{rm,\sigma}(\log N)) denote target Gibbs
moments, and let inherited target energy be (r\log k) under (P_{m,r\sigma}).  Then

\[
 \boxed{
 \widetilde W_{m,r}'(\sigma)
 =\mathbb E_{m,r\sigma}[r\log k]
 -\mathbb E_{rm,\sigma}[\log N]
 +\frac1{\sigma-1},}
 \tag{DWP.13}
\]

\[
 \boxed{
 \widetilde W_{m,r}''(\sigma)
 =\operatorname{Var}_{rm,\sigma}(\log N)
 -\operatorname{Var}_{m,r\sigma}(r\log k)
 -\frac1{(\sigma-1)^2}.}
 \tag{DWP.14}
\]

#### Proof

For any positive Dirichlet partition (Z(\sigma)),

\[
 (\log Z)'=-\mathbb E(\log n),
 \qquad
 (\log Z)''=\operatorname{Var}(\log n).
\]

Apply these identities to
(\widetilde W=\log S_{rm}-\log S_m(r\sigma)+\log(\sigma-1)), using the chain rule. ∎

Thus positive GNS clock cumulants are the real-axis shadow of the same branch-free form whose
complex residues count the divisor.

## 4. Holomorphic-potential selection equivalence

### Theorem 4.1 -- exact formation-potential criterion for RH

The following are equivalent:

1. the Riemann hypothesis;
2. (R_{m,r}) is holomorphic on (\mathbb H_{1/2});
3. (R_{m,r}) is holomorphic and nowhere zero on (\mathbb H_{1/2});
4. (\omega_{m,r}) is holomorphic on (\mathbb H_{1/2});
5. there exists a holomorphic (\Phi_{m,r}:\mathbb H_{1/2}\to\mathbb C) such that

\[
 \boxed{R_{m,r}=e^{-\Phi_{m,r}}.}
 \tag{DWP.15}
\]

The potential may be normalized uniquely by requiring

\[
 \Phi_{m,r}(1)=\log\frac{H_{rm}(1)}{S_m(r)}.
 \tag{DWP.16}
\]

#### Proof

By the zeta functional equation and conjugation symmetry, RH is equivalent to absence of nontrivial
zeros in (\Re s>1/2).  Theorem 2.1 makes this equivalent to holomorphy of (R), proving
((1)\Leftrightarrow(2)).  The same theorem says (R) has no zeros wherever it is holomorphic, so
((2)\Leftrightarrow(3)).  The charge formula gives
((2)\Leftrightarrow(4)).

The half-plane (\mathbb H_{1/2}) is simply connected.  A holomorphic nowhere-zero function on a
simply connected domain has a holomorphic logarithm, proving ((3)\Rightarrow(5)).  An exponential
is holomorphic and nowhere zero, proving the reverse implication.  The positive value (DWP.6)
fixes the additive (2\pi i\mathbb Z) ambiguity as in (DWP.16). ∎

This is not an RH proof.  It identifies the missing law as global exactness of renormalized
formation work.

## 5. Divisible-lift selection

### Lemma 5.1 -- unbounded root divisibility annihilates a meromorphic divisor

Let (D\subset\mathbb C) be connected and let (R\) be a nonzero meromorphic function on (D).
Suppose there is an unbounded set (\mathcal N\subset\mathbb N_{\ge2}) such that for every
(n\in\mathcal N) there is a meromorphic (G_n) on (D) with

\[
 G_n^n=R.
 \tag{DWP.17}
\]

Then (R) is holomorphic and nowhere zero on (D).

#### Proof

At any point (x\in D), meromorphic orders are integers and

\[
 \operatorname{ord}_xR=n\operatorname{ord}_xG_n
 \]

for every (n\in\mathcal N).  Hence the fixed integer (\operatorname{ord}_xR) is divisible by an
unbounded set of positive integers.  It must be zero.  Thus (R) has neither a zero nor a pole at
any point. ∎

### Theorem 5.2 -- divisible formation selection law

For the Euler-shell transfer (R_{m,r}), the following are equivalent:

1. RH;
2. for every (n\ge2), there is a holomorphic (G_n\) on (\mathbb H_{1/2}) with
   (G_n^n=R_{m,r});
3. there is an unbounded set (\mathcal N\subset\mathbb N_{\ge2}) and meromorphic roots (G_n)
   satisfying (DWP.17) on (\mathbb H_{1/2});
4. (R_{m,r}) has a coherent rational-power lift

\[
 G_{ab}^a=G_b,
 \qquad G_1=R_{m,r},
 \tag{DWP.18}
\]

for all positive integers (a,b).

#### Proof

If RH holds, Theorem 4.1 gives (R=e^{-\Phi}).  Put

\[
 G_n=e^{-\Phi/n}.
\]

These roots are holomorphic and satisfy the coherence (DWP.18), proving
\((1)\Rightarrow(4)\Rightarrow(2)\Rightarrow(3)\).  Lemma 5.1 and Theorem 4.1 prove
\((3)\Rightarrow(1)\). ∎

### Corollary 5.3 -- charge-divisibility conservation

Whenever (G_n^n=R_{m,r}),

\[
 \omega_{m,r}=n\left(-d\log G_n\right).
 \tag{DWP.19}
\]

Every contour charge (DWP.12) is therefore divisible by (n).  A tower of unbounded depths forces
every charge to vanish.

This is the exact selection mechanism: not positivity, recurrence, or reflection, but unbounded
source divisibility of an integer-valued obstruction.

### Theorem 5.4 -- integral formation-root rigidity

Let

\[
 F(t)=1+\sum_{j\ge1}a_jt^j\in1+t\mathbb Z[[t]].
 \tag{DWP.20}
\]

Suppose that for an unbounded set (\mathcal N\subset\mathbb N_{\ge2}), each (n\in\mathcal N)
admits

\[
 G_n(t)=1+\sum_{j\ge1}b_{n,j}t^j\in1+t\mathbb Z[[t]]
 \]

with (G_n(t)^n=F(t)).  Then

\[
 \boxed{F(t)=1.}
 \tag{DWP.21}
\]

#### Proof

Assume (F\ne1), and let (k\ge1) be the least index with (a_k\ne0).  Fix
(n\in\mathcal N).  Inductively for (j<k), the coefficient of (t^j) in (G_n^n) is
(n b_{n,j}) plus a polynomial in the earlier coefficients (b_{n,1},\ldots,b_{n,j-1}).  Since
the target coefficients and the earlier source coefficients vanish, (n b_{n,j}=0), hence
(b_{n,j}=0).

At degree (k), all nonlinear contributions again vanish, so

\[
 a_k=n b_{n,k}.
\]

Thus the fixed nonzero integer (a_k) is divisible by every (n\in\mathcal N), impossible for an
unbounded set.  Hence (F=1). ∎

### Corollary 5.5 -- same-doctrine root no-go

No nontrivial integral counting-valued formation series can generate the unbounded root tower of
Theorem 5.2 inside its original coefficient ring.  A successful source construction must pass to a
genuine rational, stacky, derived, or otherwise enlarged doctrine and then prove that its analytic
realization satisfies (DWP.17).

In particular, existing Witt Adams operations do not close the gate: they raise individual modes
and subsample ghost coordinates, while (DWP.17) is a multiplicative root equation for the complete
formation transfer.

### Theorem 5.6 -- local Kummer descent and open root history

Let (R) be nonzero meromorphic near (z=0), with

\[
 R(z)=z^q u(z),
 \qquad q\in\mathbb Z,
 \qquad u(0)\ne0.
 \tag{DWP.22}
\]

Fix (n\ge2).  On a sufficiently small punctured disk, choose one holomorphic branch of
(u^{1/n}) on the universal cover.  Then an (n)-th root of (R) on that cover is

\[
 \widetilde G_n(z)=z^{q/n}u(z)^{1/n}.
 \tag{DWP.23}
\]

One positive loop around (0) multiplies it by

\[
 \boxed{\exp(2\pi i q/n).}
 \tag{DWP.24}
\]

Consequently the following are equivalent:

1. the root history (DWP.23) has trivial deck holonomy;
2. it descends to a single-valued meromorphic (n)-th root of (R) on the base disk;
3. (n\mid q).

#### Proof

The unit (u) has a holomorphic logarithm on a sufficiently small disk and therefore a
single-valued holomorphic (n)-th root.  Only (z^{q/n}) has monodromy.  Increasing the argument of
(z) by (2\pi) multiplies that factor by (DWP.24).  The multiplier is one exactly when
(q/n\in\mathbb Z), equivalently (n\mid q).  In that case (z^{q/n}u^{1/n}) is meromorphic on the
disk; otherwise no single-valued meromorphic root can exist because meromorphic order would be
(q/n\notin\mathbb Z). ∎

### Corollary 5.7 -- effective pro-Kummer selection

Root existence on ramified covers or root stacks does not constrain (q): the cover
(z=w^n) always creates a tautological root.  If, however, the roots descend to the common base with
trivial holonomy for an unbounded set of depths (n), then (q=0).

Applied pointwise to (R_{m,r}), effective unbounded root descent is equivalent to annihilation of
all strict-right zeta-zero charges and hence to RH.

## 6. Functional-equation scope

The zeta functional equation transports a zero \(\rho\) to \(1-\rho\) with the same multiplicity.
Thus it transports the corresponding divisor charge; it does not annihilate it.  Independently,
the previously proved functional-equation action on split packet formation is information-neutral.
No comparison theorem currently identifies that packet isometry with the divisor transfer
\(R_{m,r}\), so information neutrality supplies no charge-annihilation mechanism here.

The functional equation is used in Theorem 4.1 only to turn “no zero in the strict-right
half-plane” into RH.  Construction of the roots in Theorem 5.2 must come from additional source
formation, not from reflection or common recovery alone.

## 7. Sharp countermodels and boundaries

1. **Positive real work is insufficient.**  The positive packet (1+2\,2^{-s}) has zeros on
   (\Re s=1).
2. **One fixed root depth is insufficient.**  A divisor whose orders are multiples of (n) admits
   local (n)-th roots while remaining nontrivial.
3. **Roots only on (\sigma>1) are insufficient.**  Every positive function has local real roots
   there; selection requires the full strict-right complex domain.
4. **Formal roots after adjoining the divisor are circular.**  Roots must be produced by pre-target
   source operations.
5. **Coherence is stronger than selection needs.**  Lemma 5.1 needs only unbounded root depths;
   a field realization should nevertheless supply (DWP.18).
6. **This theorem does not construct a root.**  It converts a precise source-genesis problem into
   RH and rules out weaker positivity/reflection substitutes.
7. **Integral Witt formation automatically supplies the roots.**  Failed by Theorem 5.4 and by the
   Adams/root type mismatch.  **Survivor:** the required extension must retain the resulting
   integrality defect rather than erase it.
8. **Infinite root stacks automatically select zero-freeness.**  Failed: they create roots after a
   ramified base change and retain the divisor as isotropy.  **Survivor:** require effective descent
   to the original formation base, measured by Theorem 5.6.

## 8. Parent mathematics and research content

Logarithmic derivatives, the argument principle, meromorphic root divisibility, and holomorphic
logarithms are classical.  Infinite divisibility and root gerbes are established neighbouring
languages.  No novelty claim attaches to Lemma 5.1.

Connes--Consani's *The scaling Hamiltonian* (arXiv:1910.14368) already shows that holomorphy and
inner/Hardy behaviour of ratios of local factors are load-bearing in an RH operator model.  Infinite
root-stack machinery is also established; a current structural parent is Binda--Lundemo--Merici--Park,
*Logarithmic TC via the Infinite Root Stack and the Beilinson Fiber Square* (arXiv:2408.15627).
Neither source constructs roots of the Euler-shell formation transfer (DWP.5).  The present theorem
therefore supplies an exact target for such machinery, not a priority claim for inner functions or
root stacks.

The corpus-level advance is their exact fusion with:

- literal ramification survival;
- Mellin--GNS formation work;
- universal pole subtraction;
- high-shell zero-free units;
- functional-equation charge transport; and
- a necessary-and-sufficient source-root selection gate.

## 9. Formalization status

No Lean was written or built in this research pass.  Exact shell factorization, zero-free shell
units, ramification excess, and the source GNS parents already exist in the corpus.  A later Lean
pass must formalize only after independent paper audit, and must not encode RH as an assumption;
the acceptable target is the unconditional equivalence and the abstract divisor-divisibility
lemma.
