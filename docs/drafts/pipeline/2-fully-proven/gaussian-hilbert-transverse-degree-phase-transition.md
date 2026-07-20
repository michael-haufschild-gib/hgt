# Gaussian Hilbert transverse-degree phase transition

- **ID:** gaussian-hilbert-transverse-degree-phase-transition
- **Stage:** 2-fully-proven
- **Type:** FAILURE-DRIVEN UNIVERSAL LAW / GAUSSIAN COUNTEREXAMPLE
- **Novelty:** `[NOVELTY UNVERIFIED]`; exact searches have not located an equivalent result
- **Parent card:** `gaussian-hilbert-fano-curvature`

## Exact theorem

Let `M >= 2`, let `E` be a finite-dimensional real Hilbert space, and let
`0 != T subset Sym^M(E)`.  Put `k=dim T`.  For `0 <= n < M`, let `R_n(T)` be the span of
all `(M-n)`-fold annihilation contractions of vectors in `T`, and define the **lowering charge**

\[
 B_T=\sum_{n=0}^{M-1}n\dim R_n(T).                       \tag{LC}
\]

Let `W` be an isometric copy of `T`, with isometry `U : T -> W`.  In symmetric Fock space over
`E direct-sum W`, define

\[
 S_{T,\lambda}
 =\bigoplus_{n=0}^{M-1}R_n(T)
  \;\oplus\;
  \{q+\lambda Uq:q\in T\},
 \qquad \lambda>0.                                      \tag{TGC}
\]

Then:

1. `S_(T,lambda)` is finite-dimensional and invariant under every annihilation operator.
2. If homogeneous Fock degree `n` is scaled by `t^(n/2)`, its determinant-line partition is

   \[
    Z_{T,\lambda}(t)
      =t^{B_T}(t^M+\lambda^2t)^k
      =t^{B_T+k}(t^{M-1}+\lambda^2)^k.                   \tag{PF}
   \]

3. Put

   \[
     p(t)=\frac{t^{M-1}}{t^{M-1}+\lambda^2}.
   \]

   The induced total-degree variable has the exact law

   \[
     D\;\overset{\rm law}=B_T+k+(M-1)X,
     \qquad X\sim\operatorname{Binomial}(k,p(t)),         \tag{DL}
   \]

   and hence the exact Fano margin is

   \[
   \begin{aligned}
    \mathbb E_tD-\operatorname{Var}_t(D)
      &=B_T+k+(M-1)kp(t)\\
      &\quad -(M-1)^2kp(t)(1-p(t)).                       \tag{FM}
   \end{aligned}
   \]

4. As the scale ratio ranges over `(0,infinity)`, the infimum of the margin per top direction is

   \[
    \frac1k\inf_t\bigl(\mathbb E_tD-\operatorname{Var}_t(D)\bigr)
      =\frac{B_T}{k}-\frac{M(M-4)}4.                      \tag{PT}
   \]

   For `M>2` the infimum is attained when

   \[
     p=\frac{M-2}{2(M-1)}.
   \]

   Consequently this invariant Fock family is super-Poisson at some scale exactly when

   \[
     \frac{B_T}{k}<\frac{M(M-4)}4.                       \tag{TH}
   \]

The isometric completion is the sharp equal-channel specialization of a more general universal
law.  For an arbitrary linear map `L:T -> W`, let `mu_1,...,mu_k` be the eigenvalues of
`L^*L` and put

\[
 p_j(t)=\frac{t^{M-1}}{t^{M-1}+\mu_j}.
\]

Then

\[
 Z_L(t)=t^{B_T+k}\det(t^{M-1}I+L^*L),                   \tag{AG}
\]

and the exact **channel-square law** is

\[
 \mathbb E_tD-\operatorname{Var}_t(D)
 =B_T-\frac{kM(M-4)}4
   +\sum_{j=1}^k
    \left((M-1)p_j(t)-\frac{M-2}{2}\right)^2.             \tag{CS}
\]

If `r=rank L`, the `k-r` zero eigenvalues have `p_j=1`, while each of the other square terms is
nonnegative.  Therefore

\[
 \mathbb E_tD-\operatorname{Var}_t(D)
 \ge B_T+(k-r)M-\frac{rM(M-4)}4.                         \tag{RB}
\]

The rank-budget bound is sharp over completion maps and scales: take all nonzero singular values
equal and choose the balancing probability above.  Equations (CS)--(RB), rather than the
equal-channel example alone, are the universal transverse-degree law.

There is also a sharp low-ambient consequence for this entire single-top class.  Every nonzero
top symbol has a nonzero contraction in every lower degree, so

\[
 B_T\ge\sum_{n=1}^{M-1}n=\frac{M(M-1)}2.                \tag{MC}
\]

If the ambient one-particle Hilbert space has dimension at most three, then either there is no
transverse direction, or `rank L <= 1`; when one transverse direction exists, the base symbol
space has dimension at most two.  Substituting `r<=1`, `k>=r`, and (MC) into (RB) gives

\[
 \mathbb E_tD-\operatorname{Var}_t(D)
 \ge \frac{M(M+2)}4>0.                                  \tag{LA3}
\]

Thus every single-top transverse completion in ambient dimension at most three is strictly
sub-Poisson.  This does not yet prove the low-ambient conjecture for arbitrary multi-level
filtered inverse systems or non-colliding coherent spans.

For the full top space `T=Sym^M(E)`, with `d=dim E`, one has

\[
 h_n=\binom{d+n-1}{n},\qquad k=h_M,\qquad
 B_T=\sum_{n=0}^{M-1}n h_n,\qquad
 \frac{B_T}{k}=\frac{M(M-1)}{d+1}.                       \tag{FS}
\]

Thus the full-top family is super-Poisson at some scale exactly when

\[
 (d+1)(M-4)>4(M-1).                                      \tag{FTH}
\]

5. Every full-top space `S_(Sym^M(E),lambda)` is a collision limit of spans of finitely many
   **distinct** real coherent vectors.  Therefore strict super-Poissonity in (FTH) persists for
   an actual finite family of
   distinct points in a real Hilbert space.  For the Gaussian matrix

   \[
     K_X(t)_{ij}=\exp(-t\lVert x_i-x_j\rVert^2),
   \]

   there are configurations `X` for which

   \[
     \left.\frac{d^2}{dt^2}\log\det K_X(t)\right|_{t=1}>0. \tag{GCX}
   \]

The first degree at which this full-top mechanism can cross the Poisson boundary is `M=5`.  Taking
`M=5`, `d=16`, `lambda^2=5/3`, and `t=1` gives

\[
 p=\frac38,\qquad
 \mathbb E D-\operatorname{Var}(D)=-\frac5{68}k<0,        \tag{E16}
\]

where `k=binom(20,5)`.  No decimal or numerical search enters the construction.

## Dependency-closed proof

### 1. Annihilation invariance

By construction, an annihilator in a direction of `E` maps `R_n(T)` into `R_(n-1)(T)`.  On a graph vector
it gives

\[
 a_e(q+\lambda Uq)=a_eq\in R_{M-1}(T),
\]

because `Uq` is a one-particle vector orthogonal to `E`.  An annihilator in a direction of `W`
kills `q` and maps `lambda Uq` to a scalar multiple of the vacuum.  Thus every annihilator
preserves (TGC).

### 2. Exact determinant partition

Choose orthonormal bases in every `R_n(T)` and an orthonormal basis `q_1,...,q_k` of
`T`.  All lower homogeneous blocks are mutually orthogonal.  Each graph vector
`q_j+lambda Uq_j` is orthogonal to all lower blocks and to the other graph vectors.  Degree
dilation sends it to

\[
 t^{M/2}q_j+\lambda t^{1/2}Uq_j,
\]

whose squared norm is `t^M+lambda^2 t`.  The lower blocks contribute
`product_(n<M) t^(n dim R_n(T))=t^(B_T)`; multiplying the orthogonal Gram blocks proves (PF).  Expanding
the `k` identical factors gives (DL), and the binomial mean and variance give (FM).

For a general map `L`, the graph Gram operator is

\[
 t^MI+tL^*L=t(t^{M-1}I+L^*L),
\]

which proves (AG).  Diagonalising the positive operator `L^*L` gives independent weighted
Bernoulli jumps with probabilities `p_j(t)`.  Completing the square channel by channel gives

\[
 1+(M-1)p-(M-1)^2p(1-p)
 =-\frac{M(M-4)}4+
   \left((M-1)p-\frac{M-2}{2}\right)^2,
\]

and summation proves (CS).  A zero eigenvalue has `p=1`, for which the whole left side of the
one-channel identity equals `M`.  Dropping the nonnegative squares of the `r` active channels
proves (RB), including its equality statement.

To prove (MC), choose `0 != q in T`.  Its symmetric polar form is nonzero, so there are
directions `e_1,...,e_M` whose full contraction with `q` is nonzero.  For every `0<=n<M`, the
partial contraction by `e_1,...,e_(M-n)` cannot vanish, because contracting it by the remaining
`n` directions gives that same nonzero scalar.  Hence `dim R_n(T)>=1`.  Summing the degrees
proves (MC).  In ambient dimension at most
three, the orthogonal decomposition into base and transverse one-particle directions gives the
rank alternatives stated above.  The weakest case of (RB) is `r=k=1`, and

\[
 \frac{M(M-1)}2-\frac{M(M-4)}4=\frac{M(M+2)}4,
\]

which proves (LA3).

### 3. Sharp phase threshold

Write `g=M-1`.  Apart from the deterministic term `B_T+k`, the margin per graph direction is

\[
 gp-g^2p(1-p).
\]

For `g>=1` its infimum on `[0,1]` is `-(g-1)^2/4`; for `g>1` it is attained at
`p=(g-1)/(2g)`.  This immediately gives

\[
 \frac1k\inf(\mathbb ED-\operatorname{Var}D)
 =\frac{B_T}{k}+1-\frac{(M-2)^2}{4}
 =\frac{B_T}{k}-\frac{M(M-4)}4,
\]

proving the universal law (PT) and threshold (TH).

For the full top space, `R_n(T)=Sym^n(E)`.  The elementary binomial identities

\[
 n\binom{d+n-1}{n}=d\binom{d+n-1}{n-1},
 \qquad
 \sum_{r=0}^{M-2}\binom{d+r}{r}=\binom{d+M-1}{M-2}
\]

give (FS):

\[
 B_T=d\binom{d+M-1}{M-2},\qquad
 \frac {B_T}k=\frac{M(M-1)}{d+1}.
\]

Substitution into (TH) proves (FTH).  At `M=5,d=16`, the normalized margin is

\[
 \frac{20}{17}-\frac54=-\frac5{68}.
\]

Choosing `lambda^2=M/(M-2)` at `t=1` gives the minimizing probability, proving (E16).

### 4. Collision by unisolvent coherent nodes

Let

\[
 N=\dim\bigoplus_{n=0}^M\operatorname{Sym}^n(E)=\binom{d+M}{M}.
\]

Choose `N` distinct nodes `u_1,...,u_N in E` unisolvent for polynomials of total degree at
most `M`.  Such nodes exist explicitly: in coordinates, take all nonnegative integer
multi-indices of total degree at most `M`.  The multivariate falling-factorial polynomials are
triangular with diagonal one on these nodes.

Let

\[
 v_i=\bigoplus_{n=0}^M\frac{u_i^{\odot n}}{\sqrt{n!}}.
\]

Unisolvency says that `v_1,...,v_N` form a basis of the truncated Fock space.  Define a linear
map `F` on that space to be zero in degrees below `M` and `lambda U` in degree `M`, and set

\[
 w_i=F(v_i)\in W,\qquad z_i(\varepsilon)=\varepsilon u_i+\varepsilon^M w_i.
\]

The points `z_i(epsilon)` are distinct for every positive `epsilon`, because their `E`
projections are the distinct points `epsilon u_i`.

For a homogeneous vector `q` of degree `n<=M`, write uniquely

\[
 q=\sum_i c_i(q)v_i
\]

and form the invertible recombination of exponential vectors

\[
 f_{q,\varepsilon}
   =\varepsilon^{-n}\sum_i c_i(q)\,\exp_{\!Fock}(z_i(\varepsilon)). \tag{CB}
\]

The pure-`E` Taylor terms of orders at most `M` cancel except for `q`.  If `n<M`, every term
containing `w_i` has an additional factor at least `epsilon^(M-n)` and vanishes.  If `n=M`,
the unique surviving transverse term is

\[
 \sum_i c_i(q)w_i=F(q)=\lambda Uq.
\]

All higher Taylor terms vanish after the displayed rescaling.  Hence, in Fock norm and in the
graph norms of the first two powers of the number operator,

\[
 f_{q,\varepsilon}\longrightarrow
 \begin{cases}
 q,&n<M,\\
 q+\lambda Uq,&n=M.
 \end{cases}                                             \tag{CL}
\]

The coefficient change in (CB) is invertible for every positive `epsilon`, so these vectors
are a basis of the coherent span.  Equation (CL) proves convergence of the coherent spans to
(TGC).  Graph-norm convergence makes the first two scale derivatives of their Gram
determinants converge locally uniformly.  Strict positivity of the limiting second logarithmic
derivative therefore persists for all sufficiently small positive `epsilon`.

Finally, put `x_i(epsilon)=z_i(epsilon)/sqrt 2`.  The coherent Gram matrix is

\[
 G(t)_{ij}=\exp(2t\langle x_i,x_j\rangle),
\]

whereas

\[
 K_X(t)=D(t)G(t)D(t),\qquad
 D(t)_{ii}=\exp(-t\lVert x_i\rVert^2).
\]

Thus `log det K_X(t)` and `log det G(t)` differ by a function affine in `t`; their second
derivatives agree.  Since (E16) says

\[
 (\log Z)''(1)=\operatorname{Var}(D)-\mathbb ED=\frac5{68}k>0,
\]

continuity proves (GCX) for actual distinct Gaussian points.

## Anti-theatre and literature audit

- `[LITERATURE]` Symmetric Fock exponential vectors and their Gram formula are standard parent
  theory; Marwah--Lutkenhaus characterize multimode coherent Gram matrices
  (`arXiv:1809.05187`).
- `[LITERATURE]` De Boor--Ron least interpolation owns the use of least homogeneous terms of
  spans of exponentials and the resulting `D`-invariant interpolation spaces.  The proof above
  uses that viewpoint but needs only the displayed unisolvent-basis argument
  (`Math. Z. 210 (1992), DOI 10.1007/BF02571803`).
- `[LITERATURE]` Flat Gaussian-kernel determinant asymptotics own the leading polynomial-rank
  order in collision limits (Barthelme--Usevich, `arXiv:1910.14067`).
- `[LITERATURE]` Schoenberg and Horn own the Hilbert-distance positive-definite semigroup and
  infinitely divisible matrix framework (`Trans. AMS 44 (1938)` and `136 (1969)`).
- Exact searches across Gaussian-kernel log determinants, Hadamard-power determinant
  inequalities, least interpolation, coherent-state photon statistics, and annihilation-
  invariant Fock subspaces did not locate (PF)--(TH), the super-Poisson collision construction,
  or the consequence (GCX).  This is a search boundary, not proof of global priority.
- The routine ingredients are not the scientific claim.  The candidate new content is the
  exact **transverse-degree channel-square/rank-budget law** (CS)--(RB), its sharp phase
  specialization (PT)--(TH), and its transfer to a counterexample to Gaussian log-determinant
  concavity.
- The theorem is significant independently of the HGT programme: it decides a universal
  metric-determinant curvature question by an exact finite Hilbert-space construction.

## Lean ownership

The exact theorem should be formalised in four connected layers:

1. the arbitrary degree-`M` graph Gram determinant `t^(B+k) det(t^(M-1) I + L^T L)`;
2. the finite-family weighted-Bernoulli channel-square law and its rank-budget corollary;
3. the binomial-dimension identity `B/k=M(M-1)/(d+1)` and the exact `M=5,d=16` sign;
4. the finite coherent-collision connector, including convergence of two scale derivatives.

`[LEAN-PROVED]` All four layers now compile.  Layers 1--3 are owned by
`TransverseDegreePhase` and `TransverseDegreeCurvature`.  The analytic and determinant
connectors are owned by `CoherentCollisionJet`, `GramCurvaturePersistence`, and
`DeterminantCurvatureJet`.  The former open collision layer is closed by
`UnisolventEvaluation`, `PolynomialMomentCancellation`, `PolynomialFockKernel`,
`PolynomialFockRecombination`, `TransverseCollisionGraph`, `DegreeFiveCollisionGraphJet`, and
`DegreeFiveGaussianCurvature`.

The first exact Lean lemma in layer 4 is now isolated.  For fixed real `a,b`, put
`y_epsilon=epsilon^2 a+epsilon^10 b`.  For `q=0,1,2`, one needs the three simultaneous limits

\[
 y_\varepsilon^q e^{y_\varepsilon}
 =\sum_{\ell=q}^{5}
    \frac{\varepsilon^{2\ell}a^\ell}{(\ell-q)!}
  +\mathbf 1_{q\le1}\varepsilon^{10}b
  +o(\varepsilon^{10}).                                \tag{CJ}
\]

These are respectively the value and first two scale derivatives of one coherent Gram entry.
`[LEAN-PROVED]` All three limits in (CJ) compile unconditionally.  Lean also constructs an
injective unisolvent node family, derives the inverse evaluation coefficients and every required
polynomial moment cancellation, assembles the normalized matrix 2-jet, proves eventual strict
positive curvature and determinant nonvanishing at a nonzero collision scale, and connects the
algebraic curvature to the literal second derivative of `log det`.  Finally it proves that the
diagonal exponential gauge changes `log det` only by an affine function and rescales the points
by `sqrt 2` to the conventional kernel `exp(-t ||x_i-x_j||^2)`.

The unconditional endpoint is

```lean
exists_finiteGaussianDistanceGram_positiveLogDetCurvature
```

which asserts an injective finite Euclidean configuration with positive literal Gaussian
`log det` curvature at `t=1`.  There is no remaining Lean open core for (GCX); the scientific
open core is the low-ambient boundary conjecture on the parent in-progress card.

## Log

- 2026-07-19 -- the arbitrary commuting-tuple counterexample forced the missing transverse
  channels into the model; extending those channels to arbitrary top degree exposed (PF).
- 2026-07-19 -- completed the exact phase minimisation and found the first strict crossing at
  `M=5,d=16`.
- 2026-07-19 -- proved by unisolvent coherent collision that the Fock counterexample persists
  for finite Gaussian point configurations, refuting universal scale log-concavity on paper.
- 2026-07-19 -- formalized the arbitrary higher-degree graph determinant, the finite-family
  channel-square law, its universal lower bound, the exact symmetric-power lowering-charge
  ratio, and the degree-five negative crossing; the coherent-collision connector was then the
  remaining Lean checkpoint and was closed later the same day.
- 2026-07-19 -- formalized the exact identity `(log Z)''(1)=-B+5k/4` for the literal balanced
  graph determinant and the full-top value `5k/68>0`; persistence under coherent collision is
  now the sole formal gap to the distinct-point Gaussian counterexample.
- 2026-07-19 -- formalized the exact order-ten coherent-collision jets for the Gram entry and
  its first two scale derivatives; only finite unisolvent matrix assembly and strict-curvature
  persistence remain in the collision layer.
- 2026-07-19 -- formalized continuity and strict-sign persistence of the Gram log-curvature
  matrix 2-jet at every invertible limit; the sole collision-layer gap is now unisolvent
  recombination proving the required matrix convergence.
- 2026-07-19 -- formalized arbitrary finite linear assembly of the three collision-jet
  remainders; the exact remaining gap is the unisolvent-node and polynomial
  moment-cancellation construction identifying the limiting graph 2-jet.
- 2026-07-19 -- formalized determinant first/second jets from entrywise derivatives and the
  literal second-derivative identity for `log det`; this removes determinant differentiation
  from the collision gap.
- 2026-07-19 -- formalized the unisolvent construction, moment cancellation, full collision
  matrix 2-jet, eventual invertibility and strict curvature, and the diagonal metric gauge.
  The literal distinct-point Gaussian counterexample now compiles unconditionally.
