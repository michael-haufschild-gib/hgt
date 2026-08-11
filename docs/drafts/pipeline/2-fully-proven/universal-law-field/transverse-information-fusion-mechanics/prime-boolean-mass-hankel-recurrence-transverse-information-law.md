# Prime Boolean--Mass--Hankel fusion and recurrent transverse-information law

- **ID:** ULF-TIFM-1
- **Stage:** 2-fully-proven
- **Type:** LITERAL CROSS-ORGAN FUSION / CONSERVATION / FOURTH-ORGAN PREDICTION
- **Source:** high-exponent Euler shell on its ramification diagonal
- **Status:** [PAPER-PROVED] [DEPENDENCY-CLOSED] [LITERAL ROUTE-E ORGAN]
  [MASS HALF-DENSITY ORGAN] [POSITIVE HANKEL ORGAN] [QUANTUM-RECURRENCE PREDICTION]
  [EXACT CONSERVATION] [FINITE JOINT RECONSTRUCTION] [RH SELECTOR NO-GO]

## 1. Why this is a field theorem rather than another route calculation

The input is one literal source event.  On the perfect-power ramification diagonal the
high-exponent Euler shell becomes the squarefree Boolean source

\[
 \widetilde a_m(k^m)=\mu(k)^2.
 \tag{TIF.1}
\]

The theorem does not add four independently chosen structures to this source.  It applies four
executors to the same Boolean configurations:

1. parity versus logarithmic clock gives the finite Route-E Schur capacity;
2. the clock-gradient column gives a Gibbs-damped version of the primitive-prime Mass current;
3. the first moment/Hankel block gives the positive spectral organ;
4. coherent phase execution gives a recurrent pure-state orbit and its transverse quantum Fisher
   information.

The fourth value is not fitted.  It is forced by the first three through one conservation identity.
This is the strict version of the full-frontier intervention grammar: one source formation, one
intervention family, several nonisomorphic executors, and one equation that makes their outputs
jointly accountable.

## 2. Literal finite source

Let \(F\) be a finite set of distinct primes with \(|F|=d\ge2\).  Fix \(\sigma>0\), and write

\[
 \lambda_p=\log p,
 \qquad
 q_p={p^{-\sigma}\over 1+p^{-\sigma}}={1\over1+p^\sigma},
 \qquad
 w_p=q_p(1-q_p)={p^\sigma\over(1+p^\sigma)^2}.
 \tag{TIF.2}
\]

On the Boolean configurations \(S\subseteq F\), put

\[
 \mathbb P_\sigma(S)
 =\prod_{p\in S}q_p\prod_{p\notin S}(1-q_p),
 \quad
 N(S)=|S|,
 \quad
 E(S)=\sum_{p\in S}\lambda_p.
 \tag{TIF.3}
\]

This is not an auxiliary probability model.  Taking the raw shell weight \((k^m)^{-\tau}\) on
the active diagonal \(k\mid\prod_{p\in F}p\) gives `(TIF.3)` with \(\sigma=m\tau\).

Define

\[
 A=\operatorname{Var}N=\sum_pw_p,
 \quad
 B=\operatorname{Cov}(N,E)=\sum_pw_p\lambda_p,
 \quad
 C=\operatorname{Var}E=\sum_pw_p\lambda_p^2.
 \tag{TIF.4}
\]

Let

\[
 D=\inf_{t\in\mathbb R}\operatorname{Var}(\pi N-tE)
 =\pi^2\left(A-{B^2\over C}\right).
 \tag{TIF.5}
\]

The equality and strict positivity of \(D\) are the already-proved finite Route-E Schur law.  The
present theorem identifies what that capacity measures in three other organs.

## 3. Three source-generated organs

### 3.1 Route-E Boolean capacity

The first organ is `(TIF.5)`.  Its minimizing clock correction is

\[
 t_*=\pi {B\over C}.
 \tag{TIF.6}
\]

If

\[
 R=(N-\mathbb EN)-{B\over C}(E-\mathbb EE),
 \tag{TIF.7}
\]

then \(D=\pi^2\mathbb E(R^2)\).

### 3.2 Mass half-density current

Define the prime-clock current

\[
 j_{\sigma,p}=\sqrt{w_p}\,\lambda_p
 ={p^{-\sigma/2}\log p\over1+p^{-\sigma}}.
 \tag{TIF.8}
\]

Then

\[
 \boxed{\|j_\sigma\|_2^2=C.}
 \tag{TIF.9}
\]

At the physical half-density value \(\sigma=1\), the primitive-prime Mass coefficient is

\[
 t_p={\log p\over\sqrt p},
\]

and `(TIF.8)` becomes

\[
 \boxed{j_{1,p}={p\over p+1}t_p.}
 \tag{TIF.10}
\]

The diagonal multiplier \(p/(p+1)\) and its inverse are uniformly bounded on the primes.  Thus
the current is not an analogy to the Mass current: it is its exact source-Gibbs damping, with the
same finite and \(\ell^2\)-admission class whenever either class is defined.

### 3.3 Positive Hankel/spectral block

Let

\[
 \nu_\sigma=\sum_{p\in F}w_p\,\delta_{\lambda_p},
 \qquad
 M_k=\int x^k\,d\nu_\sigma(x)=\sum_pw_p\lambda_p^k.
 \tag{TIF.11}
\]

Its first nontrivial Hankel block is

\[
 H_1=
 \begin{pmatrix}M_0&M_1\\M_1&M_2\end{pmatrix}
 =\begin{pmatrix}A&B\\B&C\end{pmatrix}.
 \tag{TIF.12}
\]

Cauchy--Binet gives

\[
 \Delta:=\det H_1=AC-B^2
 =\sum_{p<q}w_pw_q(\lambda_p-\lambda_q)^2>0.
 \tag{TIF.13}
\]

This is a genuine positive moment/Hankel executor.  It is not asserted to be the completed
shifted-Xi Hankel tower of Route U; it is the literal arithmetic finite source packet on which a
fourth-organ prediction can be tested without importing the Route-U sign.

## 4. Master conservation and reconstruction theorem

### Theorem 4.1 — three-organ transverse-volume conservation

For every finite prime aperture \(F\) with \(|F|\ge2\) and every \(\sigma>0\),

\[
 \boxed{D\,\|j_\sigma\|_2^2=\pi^2\det H_1.}
 \tag{TIF.14}
\]

Equivalently,

\[
 \boxed{
 \pi^2\sum_{p<q}w_pw_q(\log p-\log q)^2
 =D\sum_pw_p(\log p)^2.}
 \tag{TIF.15}
\]

The equality conserves the same two-dimensional source volume across three unlike organs:

- Boolean quotient capacity \(D\);
- squared Mass-current scale \(\|j_\sigma\|^2\);
- positive Hankel determinant \(\det H_1\).

#### Proof

By `(TIF.5)`, `(TIF.9)`, and `(TIF.13)`,

\[
 D\|j_\sigma\|^2
 =\pi^2\left(A-{B^2\over C}\right)C
 =\pi^2(AC-B^2)
 =\pi^2\det H_1.
\]

No limit, zero specialization, or positivity conjecture enters.  ∎

### Theorem 4.2 — finite joint reconstruction

The moment packet

\[
 (M_0,M_1,\ldots,M_{2d-1})
 \tag{TIF.16}
\]

determines the unordered pairs \(\{(\lambda_p,w_p):p\in F\}\), hence determines the prime
aperture, the Gibbs law, the Mass current `(TIF.8)`, every finite Hankel block, and the capacity
`(TIF.5)`.

#### Proof

Let

\[
 Q(T)=\prod_{p\in F}(T-\lambda_p)
 =T^d+c_{d-1}T^{d-1}+\cdots+c_0.
\]

The moments obey

\[
 M_{n+d}+c_{d-1}M_{n+d-1}+\cdots+c_0M_n=0
 \qquad(0\le n<d).
 \tag{TIF.17}
\]

The coefficient matrix is the \(d\times d\) Hankel matrix
\((M_{i+j})_{0\le i,j<d}=V\operatorname{diag}(w_p)V^{\mathsf T}\).  Distinct prime logs make the
Vandermonde matrix \(V\) invertible, and every \(w_p\) is positive.  The Hankel matrix is therefore
positive definite and `(TIF.17)` uniquely determines \(Q\).  Its roots recover the \(\lambda_p\).
The first \(d\) moments then recover the \(w_p\) through the square Vandermonde system.

Since \(p=e^{\lambda_p}\), the labels are recovered.  Moreover \(0<q_p<1/2\) and
\(w_p=q_p(1-q_p)\), so the smaller root of \(q(1-q)=w_p\) recovers \(q_p\).  Equation `(TIF.2)`
then recovers the common \(\sigma\).  All stated organs are explicit functions of these data. ∎

## 5. Predicted fourth organ: recurrent quantum information

Let \(\mathcal H_F=\ell^2(\mathcal P(F))\), with orthonormal basis \(|S\rangle\).  Define the
normalized source vector and its parity/clock orbit

\[
 |\psi_{\alpha,t}\rangle
 =\sum_{S\subseteq F}\sqrt{\mathbb P_\sigma(S)}
   e^{\,i(\pi\alpha N(S)-tE(S))}|S\rangle.
 \tag{TIF.18}
\]

For a tangent \((a,b)\in\mathbb R^2\), the conventional pure-state quantum Fisher value is

\[
 \mathcal I(a,b)
 =4\operatorname{Var}(\pi aN-bE)
 =4(\pi^2Aa^2-2\pi Bab+C b^2).
 \tag{TIF.19}
\]

This follows directly from the Fubini--Study formula: the derivative is
\(i(\pi aN-bE)\psi\), and projectivization subtracts its expectation.

### Theorem 5.1 — recurrence with strict transverse parity information

The pure clock orbit \(t\mapsto\psi_{0,t}\) is recurrent.  More precisely, there are arbitrarily
large \(t_j\) for which \(\psi_{0,t_j}\to\psi_{0,0}\), while the parity direction has exact QFI
normal to all clock reparameterizations

\[
 \boxed{
 \mathcal I_\perp
 :=\inf_{b\in\mathbb R}\mathcal I(1,b)
 =4D>0.}
 \tag{TIF.20}
\]

Combining `(TIF.14)` and `(TIF.20)` yields the four-organ conservation law

\[
 \boxed{
 \mathcal I_\perp\,\|j_\sigma\|_2^2
 =4\pi^2\det H_1.}
 \tag{TIF.21}
\]

#### Proof

Rational independence of the finite set \(\{\log p:p\in F\}\) follows from unique
factorization.  Continuous Kronecker recurrence supplies arbitrarily large times for which every
phase \(e^{-it_j\log p}\) tends to one.  Every configuration phase in `(TIF.18)` is a product of
those prime phases, hence the finite state vector returns in norm.

Minimizing `(TIF.19)` at \(a=1\) gives \(b=\pi B/C\) and value \(4D\).  Strict positivity follows
from `(TIF.13)`.  Equation `(TIF.21)` is `(TIF.14)` multiplied by four. ∎

The prediction is substantive: recurrent observation does not make every generated direction a
clock gauge.  The exact obstruction is neither a new scalar nor declared curvature; it is the
Route-E capacity itself, now identified as transverse projective information.

### Theorem 5.2 — intervention response in the fourth organ

Tilt the finite source by a real score \(r\):

\[
 \mathbb P_{\epsilon}(S)
 ={\mathbb P_\sigma(S)(1+\epsilon r(S))
   \over1+\epsilon\mathbb E r},
\]

for sufficiently small \(\epsilon\).  With \(R\) from `(TIF.7)`,

\[
 \boxed{
 {d\over d\epsilon}\bigg|_{0}\mathcal I_{\perp,\epsilon}
 =4\pi^2\operatorname{Cov}(r,R^2).}
 \tag{TIF.22}
\]

#### Proof

The finite tilt identity gives

\[
 {d\over d\epsilon}\bigg|_0
 \operatorname{Cov}_\epsilon(X,Y)
 =\operatorname{Cov}
   \bigl(r,(X-\mathbb EX)(Y-\mathbb EY)\bigr).
\]

Differentiating the Schur minimum gives
\(D'=\pi^2\operatorname{Cov}(r,R^2)\).  Equation `(TIF.20)` gives
\(\mathcal I_\perp'=4D'\). ∎

Equation `(TIF.22)` was not used to define the comparison.  It is a response theorem in the
quantum-recurrence organ predicted from the Boolean/Hankel intervention law.

## 6. Hostile audit

1. **One prime.**  If \(|F|=1\), then \(N=E/\log p\), so \(D=\Delta=\mathcal I_\perp=0\).
   Two distinct clocks are load-bearing.
2. **Not the full Route-E endpoint.**  The theorem uses the source-derived Boolean Schur capacity.
   It does not construct Hall allocation, directed seam, or cofinal physical normalization.
3. **Not the full Route-U tower.**  The positive measure `(TIF.11)` gives an exact Hankel organ,
   not the adaptive shifted-Xi hyperedges.  A future field functor must transport `(TIF.21)` to
   that tower before any U-orientation claim.
4. **Mass relation is exact, not identical normalization.**  At \(\sigma=1\) the current is the
   bounded invertible Gibbs damping `(TIF.10)` of the primitive Mass current.  Erasing the damping
   would break `(TIF.14)`.
5. **Recurrence is finite-aperture.**  Cofinal recurrence requires a declared topology and
   admission law.  The theorem does not infer one from finite Kronecker recurrence.
6. **QFI convention.**  Quantum Fisher information is four times the Fubini--Study metric.  Using
   the metric itself removes every factor four but changes no conservation statement.
7. **No novelty claim.**  Bernoulli covariance, Schur complements, finite moments, and pure-state
   QFI are classical.  Field content is their forced coupling by one literal arithmetic source.

## 7. RH selection audit

Only after proving `(TIF.21)` may one ask whether it selects the critical line.  It does not.

At the physical half-density source \(\sigma=1\), every finite aperture with at least two primes
has

\[
 D>0,
 \qquad
 \det H_1>0,
 \qquad
 \mathcal I_\perp>0.
 \tag{TIF.23}
\]

Therefore the candidate rule

\[
 \text{criticality}=\text{vanishing transverse QFI}
\]

is false on the literal critical source.  This closes a tempting but wrong selector.

The exact positive survivor is a design constraint:

> Any RH selection law using this fusion cell must compare two nonzero conserved transverse
> volumes, or produce a singular cofinal renormalized balance.  It cannot set the finite Boolean,
> Mass, Hankel, or QFI factor to zero.

The next admissible RH question is therefore not whether one of the four shadows vanishes.  It is
whether source reflection supplies a second independently generated transverse packet whose
four-organ volume is forced to equal the forward packet before divisor specialization.  That is a
new conservation problem; imposing the equality only at Xi zeros would be circular.

## 8. Parent mathematics and corpus dependencies

- finite Boolean Gibbs covariance and the Route-E Schur response:
  `constraint-frame-relativity/ramification-diagonal-boolean-descent-route-e-schur-response-law.md`;
- primitive-prime Mass coefficients and prime-log phase:
  `critical-euler-mass-weil-stokes-shadow-law.md`;
- finite prime-log recurrence:
  `constraint-frame-relativity/ramification-power-phase-history-time-dilation-law.md`;
- pure-state Fubini--Study/QFI normalization: Provost--Vallee, Anandan--Aharonov, and
  Braunstein--Caves; multiparameter nuisance elimination uses the same Schur-complement mechanism.

No external theorem supplies the arithmetic identification `(TIF.10)` or the conservation law
`(TIF.21)` as one source statement.

## 9. Lean certification

The unconditional finite theorem is formalized in
`GaloisForLFunctions.HTGeometry.PrimeBooleanMassHankelQuantumFusion`:

- Mass norm equals the clock variance `C`;
- Hankel determinant equals `AC-B^2`;
- transverse QFI equals four times Schur capacity;
- four-organ conservation `(TIF.21)`;
- strict positivity under positive weights and two distinct clocks;
- finite-tilt QFI response `(TIF.22)` by reuse of the existing Boolean response theorem;
- prime-log large-return recurrence by reuse of the existing phase-history theorem.

The module directly elaborates and its foreground leaf build completes 8,675 jobs.  It is wired
into `HTGeometry.UniversalLawField`; that foreground umbrella build completes 11,659 jobs.  Axiom
prints for the pure-state QFI identity, four-organ conservation, positivity, Mass damping, tilt
response, reconstruction, and recurrence capstones report only `propext`, `Classical.choice`, and
`Quot.sound`.  Repository formal lint and the target forbidden-declaration scan pass.

No RH statement or cofinal source completion is asserted in Lean.

## Gates

- [x] common literal source identified before Xi specialization
- [x] three structurally different organs generated from that source
- [x] exact cross-organ conservation proved
- [x] finite joint reconstruction proved
- [x] fourth-organ recurrence/QFI theorem predicted and proved
- [x] direct zero-QFI RH selector refuted with positive survivor
- [x] Lean formalization and umbrella wiring
- [ ] reflected second-packet conservation theorem
