# Valuated Plücker--Gram capacity exchange law

- **ID:** `cfr-valuated-plucker-gram-capacity-exchange`
- **Stage:** 3 — formalized in Lean 4
- **Type:** THEOREM (paper) / ROUTE-INDEPENDENT FINITE FRAME LAW
- **Status:** `[PAPER-PROVED] [DEPENDENCY-CLOSED] [NO RH] [LEAN COMPLETE]`
- **Statement:** A finite Puiseux constraint frame has one exact support--valuation--positive-capacity law: maximal-minor valuations form a valuated matroid, the Gram determinant has twice the minimal Fitting depth, and its leading coefficient is the positive square-sum of the minimal Plücker packet; positive Gram data determine filling energy but erase Plücker phase, while event depth and cofinal strictness are independent.

## Goal

Isolate a theorem that genuinely crosses several HGT organs without asserting a universal route
carrier. The result must simultaneously retain:

1. finite dependence and basis exchange;
2. event/contact valuation;
3. Fitting/discriminant depth;
4. positive Gram capacity;
5. orientation/phase loss;
6. cofinal strictness.

It must also prove where this finite skeleton stops: neither hypertranscendence nor recurrence is a
consequence of a Gram matrix or a valuated matroid.

## 1. Setup

Let `1<=r<=n` and let

\[
 \mathcal O=\mathbb C\{t^{1/q}\}
\]

be a convergent Puiseux discrete valuation ring for a fixed positive integer `q`, with fraction
field `K`, valuation `nu(t)=1`, and coefficient conjugation fixing `t`. Let

\[
 T\in\mathcal O^{r\times n},\qquad n\ge r,
\]

have rank `r` over `K`. For every `r`-subset `B` of `[n]`, put

\[
 p_B=\det T_B,qquad
 \omega(B)=\nu(p_B)\in \tfrac1q\mathbb Z_{\ge0}\cup\{\infty\}.
\tag{1}
\]

Let

\[
 d=\min_{|B|=r}\omega(B),qquad G=TT^*.
\tag{2}
\]

For a Puiseux germ `p`, write `|p|^2=p\bar p`; at positive real `t` this is the ordinary modulus
square.

For nonzero `p_B`, write

\[
 p_B=t^{\omega(B)}(c_B+o(1)),\qquad c_B\in\mathbb C^\times.
\tag{3}
\]

## 2. The theorem

### Theorem 2.1 — support, valuation, Fitting depth, and positive capacity

Under the setup above:

1. The subsets `B` with `p_B != 0` are the bases of the column matroid of `T` over `K`.
2. `omega` is a valuated matroid in the minimum-valuation convention. Explicitly, for bases
   `B,C` and `e in B\C`, some `f in C\B` satisfies

   \[
    \omega(B)+\omega(C)
    \ge
    \omega(B-e+f)+\omega(C-f+e).
   \tag{4}
   \]

   Equivalently, every tropical Grassmann--Plücker minimum is attained at least twice.
3. The minimal-depth bases

   \[
    \mathcal B_{\min}=\{B:\omega(B)=d\}
   \tag{5}
   \]

   form the bases of the initial matroid at the event normal.
4. For `C=coker(T:\mathcal O^n -> \mathcal O^r)`, one has

   \[
    \operatorname{Fitt}_0(C)=I_r(T)=(p_B:|B|=r),
    \qquad
    \nu\operatorname{Fitt}_0(C)=d.
   \tag{6}
   \]
5. Cauchy--Binet and positivity give

   \[
    \det G=\sum_{|B|=r}p_B\bar p_B,
   \tag{7}
   \]

   and therefore the exact square law

   \[
    \boxed{\nu(\det G)=2d
    =2\nu\operatorname{Fitt}_0(C).}
   \tag{8}
   \]

   More precisely,

   \[
    \boxed{
    \operatorname{lc}\bigl(t^{-2d}\det G\bigr)
    =\sum_{B\in\mathcal B_{\min}}|c_B|^2>0.}
   \tag{9}
   \]
6. Let `tau>0` be sufficiently small and suppose the complex matrix `T_tau` obtained by evaluating
   `t=tau` is onto. For `y in C^r`, the exact minimum filling energy is

   \[
    \mathcal E_\tau(y)
    =\inf_{T_\tau x=y}\|x\|^2
    =y^*G_\tau^{-1}y,
   \tag{10}
   \]

   with unique minimum-norm filler

   \[
    x_{\min}=T_\tau^*G_\tau^{-1}y.
   \tag{11}
   \]

   Hence

   \[
    \sup_{\|y\|=1}\mathcal E_\tau(y)
    =\lambda_{\min}(G_\tau)^{-1}
    =s_{\min}(T_\tau)^{-2}.
   \tag{12}
   \]
7. If `||G_tau|| <= M`, then

   \[
    \lambda_{\min}(G_\tau)
    \ge {\det G_\tau\over M^{r-1}}.
   \tag{13}
   \]

   This is the precise finite-dimensional hypothesis under which determinant magnitude controls
   strict filling capacity. Valuation depth alone gives no fixed-`tau` numerical bound without
   lower control of the leading coefficient and remainder.

### Proof

Item 1 is the maximal-minor criterion for a represented column matroid.

For item 2, the ordinary Grassmann--Plücker relation gives, for `e in B\C`,

\[
 p_Bp_C
 =\sum_{f\in C\setminus B}\epsilon_f
   p_{B-e+f}p_{C-f+e},
\tag{14}
\]

with signs `epsilon_f in {+1,-1}`. A nonarchimedean valuation satisfies

\[
 \nu(p_Bp_C)
 \ge
 \min_f\nu(p_{B-e+f}p_{C-f+e}).
\tag{15}
\]

Choose a minimizing `f`; this is `(4)`. The same argument applied to every Plücker relation says
its minimum is attained at least twice, since a unique lowest-order term could not cancel. The
standard initial-matroid theorem, or directly `(4)` restricted to minimum-weight bases, proves
item 3.

The presentation `O^n -> O^r -> C -> 0` makes `Fitt_0(C)` the ideal of maximal minors. In a DVR,
the valuation of a finitely generated nonzero ideal is the minimum valuation of its generators.
This proves `(6)`.

Cauchy--Binet gives `(7)`. Every term has valuation `2 omega(B)`. The terms of least valuation
cannot cancel because their leading coefficients are the positive real numbers `|c_B|^2`.
Factoring `t^(2d)` proves `(8)` and `(9)`.

For item 6, the normal equations for minimizing `||x||^2` under `T_tau x=y` give
`x=T_tau^*z` and `G_tau z=y`. Since `T_tau` is onto, `G_tau` is positive definite, hence
`z=G_tau^-1 y`. This proves `(10)` and `(11)`. Maximizing the Rayleigh quotient of `G_tau^-1`
gives `(12)`.

Finally, if the eigenvalues of `G_tau` are
`0<lambda_1<=...<=lambda_r<=M`, then

\[
 \det G_\tau=\lambda_1\cdots\lambda_r
 \le\lambda_1M^{r-1}.
\]

Rearrangement proves `(13)`. `[PROVED HERE]`

## 3. Exact phase/orientation uncertainty

### Theorem 3.1 — positive capacity is an unsquared-phase quotient

Let

\[
 S=\operatorname{diag}(u_1,\ldots,u_n),\qquad |u_j|=1.
\]

Then

\[
 (TS)(TS)^*=TT^*,
\tag{16}
\]

while

\[
 p_B(TS)=\left(\prod_{j\in B}u_j\right)p_B(T).
\tag{17}
\]

Consequently the full Gram matrix, every filling energy in `(10)`, every singular value, and the
positive leading packet in `(9)` are invariant under column rephasing, whereas the oriented or
phased Plücker packet is not. In the real case, `u_j in {+1,-1}` realizes column reorientation. In
the square case, rephasing one column changes determinant phase arbitrarily while leaving `G`
fixed.

Therefore no gauge-invariant map can recover the original phased or oriented Plücker packet from
unmarked Gram data.

### Proof

Since `SS*=I`, equation `(16)` is immediate. Determinants are alternating multilinear in columns,
which gives `(17)`. Choosing one nontrivial `u_j` changes every basis phase containing `j` while
leaving `(16)` fixed. Such a nonloop column exists because `r>=1` and `T` has rank `r`.
`[PROVED HERE]`

This theorem is the exact, limited meaning of the corpus phrase “positivity squares away
orientation.” Positivity in general is not a phase quotient; this statement applies to the
specified Gram/polar reduction.

## 4. Cofinal strictness

Let `T_N:X_N->Y_N` be finite-dimensional surjective Hilbert-space maps in a compatible aperture
system. Put

\[
 \sigma_\infty=\inf_N s_{\min}(T_N).
\tag{18}
\]

### Theorem 4.1 — uniform filling is the cofinal strictness coordinate

One has

\[
 \sigma_\infty>0
 \iff
 \sup_N\sup_{\|y\|=1}\inf_{T_Nx=y}\|x\|^2<\infty.
\tag{19}
\]

For a bounded diagonal operator `D e_j=lambda_j e_j` on `ell^2`, with every `lambda_j != 0` and
`sup_j|lambda_j|<infinity`, all finite
restrictions are onto and have free column matroid. The infinite range is closed exactly when

\[
 \inf_j|\lambda_j|>0.
\tag{20}
\]

### Proof

Equation `(12)` at each aperture says the right side of `(19)` equals
`sup_N s_min(T_N)^(-2)`, proving `(19)`. For the diagonal operator, bounded below is equivalent to
`inf_j |lambda_j|>0`. A bounded operator between Hilbert spaces with trivial kernel has closed
range exactly when it is bounded below. If the infimum is zero, unit vectors `e_j` along a
vanishing subsequence satisfy `||De_j||->0`, so the range is not closed. `[PROVED HERE]`

## 5. Two-axis independence

### Theorem 5.1 — event valuation and cofinal strictness do not determine one another

Fix `tau in (0,1)`. The normal/event depth `d_N` and cofinal strictness `sigma_infty` do not
determine one another.

1. Let `A_N(t)=t I_N`. Then `d_N=N` and

   \[
    \inf_Ns_{\min}(A_N(\tau))=\tau>0.
   \]

2. Let `lambda_j>0` tend to zero and put

   \[
    B_N(t)=t\operatorname{diag}(\lambda_1,\ldots,\lambda_N).
   \]

   Both `A_N` and `B_N` have depth `N`, while

   \[
    \inf_Ns_{\min}(B_N(\tau))=\tau\inf_j\lambda_j=0.
   \]

3. The constant family `C_N(t)=tau I_N` has the same strictness `tau` as `A_N(t)` at `t=tau`, but
   depth zero rather than `N`.

Thus none of determinant valuation, discriminant valuation, or Fitting depth alone determines both
axes. A valid field needs an event-normal valuation filtration and a separately declared
aperture/topological strictness filtration.

### Proof

All calculations are immediate from the displayed diagonal matrices. `[PROVED HERE]`

## 6. Stronger false conjectures and survivors

1. **Gram determines orientation.** False by Theorem 3.1. Survivor: exact doubled Fitting depth
   and squared minimal Plücker packet.
2. **Nonzero finite determinant implies cofinal strictness.** False for
   `diag(epsilon,epsilon^-1)`, whose Gram determinant is one while its least singular value tends
   to zero. Survivor: Theorem 4.1 and bound `(13)` with operator-norm control.
3. **Maximal-minor valuation determines full persistence spectrum.** False: `d` is only the sum of
   Smith exponents. Survivor: the full family of determinantal divisors or singular values is
   needed.
4. **Recurrence follows from the finite frame.** False: the same `T` admits no declared flow or
   arbitrarily chosen unitary flows. A source character lattice, transport, and admitted
   completion are additional data.
5. **Hypertranscendence is unbounded Fitting depth.** False: a free differential-clock tower can
   have every finite minor nonzero of valuation zero. HT appears as persistent prolongation-rank
   growth, not event depth.
6. **The full Stokes form is positive Gram.** False: the published Stokes Cartan form subtracts
   one physical-rank square. The theorem applies to its positive multi-Rees/coarea sector, not to
   the negative port or inertia by itself.

## 7. Literal corpus instantiations

The theorem has four structurally distinct corpus specializations; no pairwise matroid
nonisomorphism is claimed.

1. **Ultrametric Vandermonde/Smith collision.** After base change to the stated complex convergent
   Puiseux DVR, maximal minors are alternants and determinantal valuations are collision energies.
   Gram passage squares the leading Vandermonde orientation. No positive-Gram assertion is made
   for a general `p`-adic DVR.
2. **Positive multi-Rees Stokes cut sector.** Along a chosen one-parameter Puiseux specialization,
   the frame is `[I | sqrt(ell_e t_e)u_e]_e` and its Gram is
   `I+sum_e ell_e t_e u_eu_e*`. The represented matroid is the augmented frame matroid, not simply
   the cut matroid. A genuinely multiparameter Rees valuation lies outside the rank-one value group
   of Theorem 2.1. The separate negative physical port is not included.
3. **Prime Gamma--Bockstein/Rees normal.** The literal diagonal comparison has

   \[
    L_p={4p^3(\log p)^2\over(p+1)^2(p-1)(2p-1)}\longrightarrow0.
   \]

   Every finite `t`-valuation is zero, yet the all-prime diagonal map has no bounded inverse and
   nonclosed range in `ell^2` and `c_0`. This realizes Theorem 5.1(2).
4. **Weighted prime port.** A rank-one row `T_F=(a_p/sqrt(w_p))` has
   `TT*=sum_F |a_p|^2/w_p`; `(10)` is exactly the prime-port minimum-energy law. Recurrence exists
   only after the separate phase action and capacity-admission hypotheses of the parent theorem.

Finite source-Grushin and Helson/Fredholm matrices along a real-analytic one-parameter transverse
arc supply further square-event instances: Gram determinant doubles wall order and loses crossing
orientation, while Moore--Penrose cost blows up at a simple rank loss. No arithmetic wall selector
follows.

## 8. Significance and field boundary

This theorem proves one common finite skeleton. It does **not** prove that every RH route is a
valuated matroid, that all route transitions are deletion/contraction, or that recurrence and HT
are consequences of minors. Its load-bearing conclusion is two-dimensional:

\[
 \boxed{
 \text{event-normal valued Plücker geometry}
 \quad\perp\quad
 \text{cofinal Archimedean strictness geometry}.}
\]

Positive Gram capacity is a nonconservative realization between them: it retains squared depth
and filling cost but loses unsquared phase/orientation. This finite law is the first exact metric
calibration for Constraint-Frame Relativity; it is not the complete field.

## Lean-return notes

Formalized: see `valuated-plucker-gram-capacity-exchange-law-formalized.md` in this directory for
the declaration-by-declaration map.  Likely later reuse:

- `formal/GaloisForLFunctions/HilbertMetric/GradedPartition.lean`;
- `formal/GaloisForLFunctions/RHTower/GammaSewnFourRatePluckerConnector.lean`;
- `formal/GaloisForLFunctions/RHTower/XiPrimeSeamPairVariance.lean`;
- existing Smith/Fitting and finite minimum-energy modules cited by parent cards.

## Gates

- [x] complete paper proof
- [x] orientation-loss countermodel
- [x] cofinal strictness theorem
- [x] event/strictness independence
- [x] four literal corpus instantiations scoped
- [x] HT/recurrence overclaim rejected
- [x] independent hostile audit
- [x] Lean formalization
- [ ] external paper integration

## Log

- 2026-08-09 — theorem originated from whole-corpus search for a non-scalar finite constraint-frame law; recurrence and HT clauses were rejected under hostile review.
