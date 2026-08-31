# Observer-jet formation decomposition, clock-order properness, and RH source reduction

- **ID:** ULF-TAFM-23
- **Stage:** 2-fully-proven
- **Type:** universal mechanism / exact formation law / arithmetic source reduction
- **Parents:** ULF-TAFM-10, ULF-TAFM-15, ULF-TAFM-19
- **Status:** `[PROVED HERE]` dependency-closed paper proof; Lean formalisation pending

## 1. What changes

Law XXIV proved that the harmonic-to-square-root relative clock rate is unbounded and therefore
cannot act boundedly on all neutral fixed-mass charges.  That statement does not classify its
source-generated domains.  Unboundedness is order-sensitive.

This card constructs the missing object.  Every finite path charge has canonical coordinates

\[
  \text{mass}\ \oplus\ \text{drift}\ \oplus\ \text{second-boundary history}.
\]

Every observer clock has the exactly dual coordinates

\[
  \text{value}\ \oplus\ \text{slope}\ \oplus\ \text{curvature}.
\]

Their pairing is conserved.  This is coordinate-free before choosing an anchor: second-boundary
charges are the annihilator of affine observer gauges, and observer curvature is the quotient by
affine gauges.  The anchor `{0,1}` supplies a concrete chart.

The literal harmonic-to-square-root clock has unbounded value and slope but bounded, decaying
curvature.  Its minimal additive formation order is therefore two.  RH selection is reduced from
vague exceptional-domain regularity to a signed second-formation-action estimate on the literal
completed source.

## 2. Canonical second formation jet

Fix `N >= 1` and a real charge `q_0,...,q_N`.  Put

\[
 m_0=\sum_{k=0}^{N}q_k,
 \qquad
 m_1=\sum_{k=0}^{N}kq_k.                              \tag{OJ.1}
\]

Define the anchored affine part and moment-free residual by

\[
 b=(m_0-m_1)\delta_0+m_1\delta_1,
 \qquad r=q-b.                                         \tag{OJ.2}
\]

Then

\[
 \sum r_k=0,
 \qquad \sum kr_k=0.                                  \tag{OJ.3}
\]

For `j >= 0`, define the double prefix

\[
 A_j=\sum_{k=0}^{\min(j,N)}(j+1-k)r_k,                \tag{OJ.4}
\]

and put `A_{-1}=A_{-2}=0`.

### Theorem 2.1 -- exact reconstruction and terminal closure

For `0 <= k <= N`,

\[
 q_k=(m_0-m_1)1_{k=0}+m_1 1_{k=1}
     +A_k-2A_{k-1}+A_{k-2}.                            \tag{OJ.5}
\]

Moreover,

\[
 A_{N-1}=A_N=0.                                       \tag{OJ.6}
\]

Consequently `A` is a finite history supported in `{0,...,N-2}`, and the coordinates

\[
 J_2(q)=(m_0,m_1,A)                                   \tag{OJ.7}
\]

determine `q` uniquely.

#### Proof

Let

\[
 R_j=\sum_{k=0}^{\min(j,N)}r_k.
\]

Direct subtraction in `(OJ.4)` gives

\[
 A_j-A_{j-1}=R_j.
\]

A second subtraction gives

\[
 A_j-2A_{j-1}+A_{j-2}=R_j-R_{j-1}=r_j.
\]

Adding the affine part `(OJ.2)` proves `(OJ.5)`.

Because the coefficient of `r_N` is zero, `(OJ.3)` gives

\[
 A_{N-1}=\sum_{k=0}^{N}(N-k)r_k
 =N\sum r_k-\sum kr_k=0.
\]

Similarly,

\[
 A_N=\sum_{k=0}^{N}(N+1-k)r_k
 =(N+1)\sum r_k-\sum kr_k=0.
\]

The moments force `m_0,m_1`; two prefix sums then force `A`.  Hence reconstruction is unique.
QED.

## 3. Observer-jet Green identity

For a real observer rate `lambda`, write

\[
 \Delta\lambda_j=\lambda_{j+1}-\lambda_j,
 \qquad
 \Delta^2\lambda_j=\lambda_{j+2}-2\lambda_{j+1}+\lambda_j. \tag{OJ.8}
\]

### Theorem 3.1 -- value--slope--curvature conservation

Every finite charge satisfies

\[
 \boxed{
 \sum_{k=0}^{N}q_k\lambda_k
 =m_0\lambda_0+m_1\Delta\lambda_0
  +\sum_{j=0}^{N-2}A_j\Delta^2\lambda_j.}
                                                               \tag{OJ.9}
\]

#### Proof

The affine part pairs as

\[
 (m_0-m_1)\lambda_0+m_1\lambda_1
 =m_0\lambda_0+m_1\Delta\lambda_0.
\]

Insert `(OJ.5)` for the residual.  Since `A` is finitely supported and
`A_{-1}=A_{-2}=0`, finite reindexing gives

\[
 \sum_k(A_k-2A_{k-1}+A_{k-2})\lambda_k
 =\sum_j A_j(\lambda_j-2\lambda_{j+1}+\lambda_{j+2}).
\]

This is the last term of `(OJ.9)`.  Terminal closure `(OJ.6)` removes every boundary debt. QED.

### Corollary 3.2 -- affine gauge law

For `p_k=a+bk`,

\[
 \sum q_k(\lambda_k+p_k)-\sum q_k\lambda_k=am_0+bm_1, \tag{OJ.10}
\]

and

\[
 \Delta^2(\lambda+p)=\Delta^2\lambda.                 \tag{OJ.11}
\]

On the moment-free sector, response depends only on the observer class modulo affine functions.
Thus curvature is not a metaphor: it is the complete observer invariant dual to second-boundary
formation.

## 4. Sharp clock-order properness

Let `c_00` denote finite real sequences.  The reconstruction theorem gives a linear isomorphism

\[
 J_2:c_{00}\longrightarrow \mathbb R^2\oplus c_{00}. \tag{OJ.12}
\]

Give the source its second-formation action

\[
 \|q\|_{F^2}=|m_0|+|m_1|+\sum_j|A_j|.                \tag{OJ.13}
\]

Its completion is therefore canonically `R^2 direct-sum ell^1`.

### Theorem 4.1 -- second-order properness classification

The response functional

\[
 L_\lambda(q)=\sum q_k\lambda_k
\]

extends continuously to the `F^2` completion if and only if

\[
 \sup_j|\Delta^2\lambda_j|<\infty.                    \tag{OJ.14}
\]

Its norm is

\[
 \|L_\lambda\|=
 \max\left\{|\lambda_0|,|\Delta\lambda_0|,
                  \sup_j|\Delta^2\lambda_j|\right\}. \tag{OJ.15}
\]

#### Proof

In `J_2` coordinates, `(OJ.9)` says that `L_lambda` has coefficient vector

\[
 (\lambda_0,\Delta\lambda_0,(\Delta^2\lambda_j)_j).
\]

The dual of the sum norm on `R^2 direct-sum ell^1` is the maximum norm on
`R^2 direct-sum ell^infinity`.  This proves sufficiency and `(OJ.15)`.

For necessity, take the unit quadrupole

\[
 Q^{(j)}=\delta_j-2\delta_{j+1}+\delta_{j+2}.          \tag{OJ.16}
\]

It has mass zero, first moment zero, ordinary `l1` mass four, one unit second-history
coordinate, and `F^2` action one.  Its response is exactly

\[
 L_\lambda(Q^{(j)})=\Delta^2\lambda_j.                \tag{OJ.17}
\]

A bounded functional must therefore bound all second differences. QED.

This is the higher-order replacement for Law XXIV's dipole theorem.  A rate can be nonproper on
neutral measures and proper on the source-generated second-formation completion.

## 5. Literal harmonic--Riesz clock has order two

The literal relative rate is

\[
 \lambda_k=
 \frac{\sqrt{k+2}-\sqrt{k+1}}
      {1/(k+1)-1/(k+2)}
 =\frac{(k+1)(k+2)}{\sqrt{k+2}+\sqrt{k+1}}.            \tag{OJ.18}
\]

Put, for `x >= 1`,

\[
 f(x)=\frac{x(x+1)}{\sqrt{x+1}+\sqrt x},
 \qquad \lambda_k=f(k+1).                             \tag{OJ.19}
\]

### Theorem 5.1 -- minimal additive clock order

The following hold unconditionally:

1. `lambda_k` is unbounded;
2. `Delta lambda_k` is unbounded;
3. for every `k >= 0`,

\[
 |\Delta^2\lambda_k|
 \le \frac{13}{4\sqrt{k+1}}
 \le \frac{13}{4}.                                    \tag{OJ.20}
\]

Hence the harmonic-to-square-root transmutation has minimal additive formation order two.

#### Proof

Let

\[
 h(x)=\sqrt{x+1}-\sqrt x
     =\frac1{\sqrt{x+1}+\sqrt x}.
\]

Then `f(x)=x(x+1)h(x)`.  Since the denominator in `(OJ.19)` is at most
`2 sqrt(x+1)`,

\[
 f(x)\ge \frac{x\sqrt{x+1}}2,
\]

which proves unboundedness.

The same upper and lower denominator bounds give

\[
 \begin{aligned}
 f(x+1)-f(x)
 &\ge \frac{(x+1)\sqrt{x+2}}2
      -\frac{(x+1)\sqrt x}2\\
 &=\frac{x+1}{\sqrt{x+2}+\sqrt x}.                    \tag{OJ.21}
 \end{aligned}
\]

At `x=n^2`, `sqrt(x+2)<=n+1`, so the right side is at least
`n^2/(2n+1)>=n/3`.  First differences are therefore unbounded.

It remains to bound curvature.  Direct differentiation gives

\[
 h'(x)=\frac12\left(\frac1{\sqrt{x+1}}-\frac1{\sqrt x}\right),
\]

\[
 h''(x)=\frac14\left(
   \frac1{x\sqrt x}-\frac1{(x+1)\sqrt{x+1}}\right),    \tag{OJ.22}
\]

and

\[
 f''(x)=2h(x)+2(2x+1)h'(x)+x(x+1)h''(x).              \tag{OJ.23}
\]

For `x>=1`, rationalization yields

\[
 0<h(x)\le\frac1{2\sqrt x},
 \qquad
 |h'(x)|=\frac{h(x)}{2\sqrt x\sqrt{x+1}}
          \le\frac1{4x\sqrt x}.                       \tag{OJ.24}
\]

For the second derivative, split the positive difference in `(OJ.22)` as

\[
 \frac1{x\sqrt x}-\frac1{(x+1)\sqrt{x+1}}
 =\frac1{x(x+1)\sqrt x}
  +\frac{h(x)}{(x+1)\sqrt x\sqrt{x+1}}.
\]

Using `(OJ.24)` and `x+1>=x` gives

\[
 0\le h''(x)\le\frac3{8x^2\sqrt x}.                   \tag{OJ.25}
\]

Because `2x+1<=3x` and `x+1<=2x`, `(OJ.23)`--`(OJ.25)` imply

\[
 |f''(x)|
 \le \frac1{\sqrt x}+\frac3{2\sqrt x}+\frac3{4\sqrt x}
 =\frac{13}{4\sqrt x}.                                \tag{OJ.26}
\]

Let `g(x)=f(x+1)-f(x)`.  The mean-value theorem applied first to `f'` on
`[x,x+1]` and then to `g` on `[x,x+1]`, together with the monotonicity of
`x |-> 1/sqrt x`, gives

\[
 |g(x+1)-g(x)|\le\frac{13}{4\sqrt x}.
\]

Taking `x=k+1` is exactly `(OJ.20)`. QED.

## 6. Literal completed-source reduction

For `M>=3`, let

\[
 q^{(M)}_k=
 \operatorname{completedPrimePolarGammaHarmonicCharge}(k),
 \qquad 0\le k\le M-2.                                \tag{OJ.27}
\]

Let `(m_0^{(M)},m_1^{(M)},A^{(M)})=J_2(q^{(M)})`.  Existing exact clock
transmutation identifies

\[
 \mathcal R_M=
 \operatorname{mobiusDivisorSquareRootAbelMoment}(M)
 =\sum_{k=0}^{M-2}q^{(M)}_k\lambda_k.                 \tag{OJ.28}
\]

### Theorem 6.1 -- exact second-jet landing

For every `M>=3`,

\[
 \boxed{
 \mathcal R_M=
 m_0^{(M)}\lambda_0+m_1^{(M)}\Delta\lambda_0
 +\sum_{j=0}^{M-4}A_j^{(M)}\Delta^2\lambda_j.}        \tag{OJ.29}
\]

Moreover,

\[
 \frac{|\mathcal R_M|}{M}
 \le \frac{|\lambda_0||m_0^{(M)}|
       +|\Delta\lambda_0||m_1^{(M)}|
       +\frac{13}{4}\sum_{j=0}^{M-4}
           |A_j^{(M)}|/\sqrt{j+1}}{M}.                \tag{OJ.30}
\]

#### Proof

Equation `(OJ.29)` is Theorem 3.1 applied to `(OJ.28)`.  Apply the triangle inequality and
`(OJ.20)` to obtain `(OJ.30)`. QED.

The zeroth jets `m_0^{(M)}` converge to zero unconditionally by the already-proved completed
harmonic cancellation law.  In particular they are uniformly bounded.

### Corollary 6.2 -- new unconditional proof architecture

It is sufficient for RH to prove the source-native linear action estimate

\[
 |m_1^{(M)}|+
 \sum_{j=0}^{M-4}\frac{|A_j^{(M)}|}{\sqrt{j+1}}
 =O(M).                                                \tag{OJ.31}
\]

#### Proof

The convergent zeroth jets and `(OJ.30)` make `|mathcal R_M/M|` uniformly bounded.  Existing theorem
`riemannHypothesis_iff_mobiusDivisorSquareRootAbelBounded` identifies that normalized bound with
RH. QED.

This is not an RH proof: `(OJ.31)` remains open.  It is a new, strictly typed producer target.
Unlike the scalar Riesz criterion, it separates affine boundary drift from curvature-coupled bulk
formation and supplies a localizable positive source action.  Unlike universal compactness, it is
compatible with the proved unbounded raw clock.

## 7. Cross-organ fusion and prediction

One mechanism now acts in five different organs.

1. **Formation Stokes:** second-boundary history is the next exact path-chain layer after ordinary
   divergence.
2. **Clock transmutation:** value--slope--curvature conservation lifts the first-order
   boundary-storage/acceleration identity.
3. **Positivity:** the action in `(OJ.31)` is phase-blind only after oriented jet coefficients have
   been formed; local signs remain in `(OJ.29)`.
4. **Recurrence:** zeroth charge can close while drift and second-boundary history remain open.
5. **Möbius/divisor organ:** the existing dilation-channel telescope is predicted to construct or
   control `A^(M)`, rather than provide an unrelated endpoint.

The theorem also corrects the field interpretation of noncompactness.  A clock is not simply
proper or nonproper.  It has a **formation order spectrum**: the least boundary depth at which its
observer coboundary is bounded.  Hypertranscendental sources may require an unbounded tower of such
orders, but that statement remains conjectural until a literal differential-algebraic comparison
is built.

## 8. Hostile audit

1. **Not Abel summation renamed.**  Abel summation is the `r=1` pairing.  The new theorem proves
   canonical source reconstruction, affine-gauge quotient, an induced Banach completion, sharp
   properness classification, and literal minimal order two.
2. **Not a fitted norm.**  `F^2` is the transported `l1` norm under the canonical boundary-complex
   isomorphism `J_2`; quadrupoles prove sharpness.
3. **Not generic compactness.**  Value and slope remain unbounded.  Only curvature acts boundedly
   on second-formation histories.
4. **Not an RH premise.**  The literal curvature bound `(OJ.20)` is elementary and unconditional.
   RH enters only as the open source action `(OJ.31)`.
5. **Not determinant or Waldhausen repackaging.**  Determinant history records multiplicative
   orientation.  Observer jets classify additive formation depth and dual clock regularity.
6. **Known-idea collision accepted, not hidden.**  Discrete Green identities, moment cancellation,
   Sobolev/Besov duality, and distributional transport are established parents.  New value lies in
   their exact source/observer interpretation and literal harmonic--Riesz minimal-order theorem.

Relevant primary comparisons are Bouchitte--Buttazzo--De Pascale on transport of distributional
dipoles (arXiv:1312.5453), Connes--Consani on a second-order scaling Hamiltonian whose image carries
two vanishing constraints (arXiv:1910.14368), and Meyer on bornological analytic completion and
excision (arXiv:math/9906205).  None supplies `(OJ.29)` or `(OJ.31)` for the arithmetic source.

## Gates

- [x] exact reconstruction and terminal closure
- [x] exact observer-jet Green identity
- [x] affine gauge classification
- [x] sharp second-order formation properness
- [x] literal rate unbounded at orders zero and one
- [x] literal weighted second-curvature bound
- [x] exact completed-source second-jet landing
- [x] new sufficient source law for RH
- [ ] Lean formalisation
- [ ] identify Möbius--divisor dilation history with canonical second primitive
- [ ] prove linear source action `(OJ.31)`
- [ ] RH selection consequence

## Log

- 2026-08-31 -- promoted from Stage 1 after complete reconstruction, properness, literal clock-order,
  and arithmetic landing proofs.  Determinant and first-order completion candidates were retired as
  already occupied corpus shadows; observer-jet formation order is the positive survivor.
