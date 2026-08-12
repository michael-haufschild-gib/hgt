# Mixed spectral formation, atomic retention, continuous escape, and closed-range law

- **ID:** ULF-OISM-6
- **Stage:** 2-fully-proven
- **Type:** COMPLETE SPECTRAL-TYPE / OPERATOR-IDEAL FORMATION CLASSIFICATION
- **Parents:** ULF-OISM-4 and ULF-OISM-5
- **Statement:** For every separable unitary phase representation, Hilbert--Schmidt Cesaro formation
  retains exactly the equal-eigenvalue atomic blocks and erases every mixed or continuous block.
  For a positive trace-class packet, trace-norm formation converges exactly when the packet has zero
  continuous spectral mass; otherwise the continuous mass is an exact lower bound for the missing
  trace-norm convergence.  The conjugation transgression has closed Hilbert--Schmidt range exactly
  when the unitary has finite spectrum.
- **Status:** [PAPER-PROVED] [DEPENDENCY-CLOSED] [ROUTE-INDEPENDENT]
  [COMPLETE MIXED-SPECTRUM CLASSIFICATION] [ATOMIC RETENTION]
  [CONTINUOUS TRACE ESCAPE] [CLOSED-RANGE IFF FINITE SPECTRUM]
  [FUNCTIONAL-EQUATION NEUTRAL] [LEAN-PENDING] [NOT RH]

## 1. Purpose

ULF-OISM-4 proves the pure-point resonance law.  ULF-OISM-5 proves the atomless escape law.  A
source representation need not be purely one or the other.  The correct invariant is the atomic
and continuous spectral decomposition of the unitary phase action.

This card closes that dichotomy.  It gives one complete formation law for arbitrary spectral type
and identifies the escaped trace exactly.

## 2. Spectral decomposition

Let `H` be a separable complex Hilbert space and let `U:H->H` be unitary.  For each unit-circle
eigenvalue `lambda`, let

```text
H_lambda=ker(U-lambda),
P_lambda=orthogonal projection onto H_lambda.
```

Separability makes the set `A(U)` of eigenvalues countable.  Define

```text
H_at = orthogonal direct sum_(lambda in A(U)) H_lambda,
P_at = sum_lambda P_lambda,
H_c  = H_at^perp,
P_c  = 1-P_at.
```

The restriction of `U` to `H_c` has no eigenvectors.

On the Hilbert space `S_2(H)` define

```text
alpha(T)=U* T U,
delta(T)=T-alpha(T).
```

Define the atomic pinching

\[
 \boxed{
 \Pi_{\rm at}(T)=\sum_{\lambda\in A(U)}P_\lambda T P_\lambda.}
\tag{MSF.1}
\]

For `T in S_2`, the sum converges in Hilbert--Schmidt norm because its terms are orthogonal
compressions.  For positive trace-class `T`, it also converges in trace norm.

## 3. Fixed Hilbert--Schmidt geometry

### Lemma 3.1 -- a compact commuting operator vanishes on the continuous subspace

If a compact operator `K:H_c->H_c` commutes with `U|H_c`, then `K=0`.

#### Proof

Commutation with the normal operator `U` implies commutation with its adjoint.  Hence `K*K` is a
positive compact operator commuting with `U|H_c`.  If `K!=0`, then `K*K` has a positive eigenvalue
whose eigenspace `E` is nonzero and finite dimensional.  Commutation makes `E` invariant under
`U`.  A unitary on a nonzero finite-dimensional complex space has an eigenvector.  This would give
an eigenvector of `U` in `H_c`, contradicting the definition of the continuous subspace. QED.

### Theorem 3.2 -- fixed ideal equals atomic equal-phase blocks

\[
 \boxed{
 \ker\delta
  =\left\{\bigoplus_{\lambda\in A(U)}T_\lambda:
        T_\lambda\in S_2(H_\lambda),\ 
        \sum_\lambda\|T_\lambda\|_2^2<\infty\right\}.}
\tag{MSF.2}
\]

The orthogonal projection of `S_2(H)` onto this fixed space is exactly `Pi_at`.

#### Proof

If `T` commutes with `U`, then it commutes with every spectral projection of `U`.  Thus it preserves
`H_at`, `H_c`, and every eigenspace `H_lambda`; all cross blocks vanish.  Its restriction to `H_c`
is Hilbert--Schmidt, hence compact, and Lemma 3.1 makes it zero.  The remaining restrictions are the
equal-eigenvalue blocks displayed in `(MSF.2)`.

Conversely, every such block sum commutes with `U`.  Orthogonality of the blocks gives the stated
Hilbert--Schmidt summability and identifies `(MSF.1)` as the orthogonal projection. QED.

### Corollary 3.3 -- complete Hilbert--Schmidt formation law

For

\[
 M_N(T)=\frac1N\sum_{n=0}^{N-1}U^{-n}TU^n,
\tag{MSF.3}
\]

the mean ergodic theorem and Theorem 3.2 give

\[
 \boxed{
 M_N(T)\longrightarrow\Pi_{\rm at}(T)
 \quad\text{in }S_2.}
\tag{MSF.4}
\]

The pure-point theorem ULF-OISM-4 is the case `P_at=1`.  The atomless theorem ULF-OISM-5 is the
case `P_at=0`.

## 4. Exact escaped trace mass

Let `T>=0` be trace class.  Define its atomic and continuous masses

\[
 m_{\rm at}(T)=\operatorname{tr}(TP_{\rm at}),
 \qquad
 m_c(T)=\operatorname{tr}(TP_c).
\tag{MSF.5}
\]

They are nonnegative and add to `tr(T)`.

### Theorem 4.1 -- atomic trace retained by the Hilbert--Schmidt limit

\[
 \boxed{
 \operatorname{tr}\Pi_{\rm at}(T)=m_{\rm at}(T),
 \qquad
 \operatorname{tr}M_N(T)=\operatorname{tr}T.}
\tag{MSF.6}
\]

Therefore

\[
 \boxed{
 \operatorname{tr}\bigl(M_N(T)-\Pi_{\rm at}(T)\bigr)=m_c(T).}
\tag{MSF.7}
\]

#### Proof

The positive blocks `P_lambda T P_lambda` have total trace at most `tr(T)`, so their sum converges
in trace class.  Countable trace additivity gives

\[
 \operatorname{tr}\Pi_{\rm at}(T)
 =\sum_\lambda\operatorname{tr}(P_\lambda T P_\lambda)
 =\operatorname{tr}(TP_{\rm at}).
\]

Unitary conjugation preserves trace, hence so does its Cesaro average.  Subtraction proves
`(MSF.7)`. QED.

### Corollary 4.2 -- quantitative ideal mismatch

For every `N`,

\[
 \boxed{
 \|M_N(T)-\Pi_{\rm at}(T)\|_1\ge m_c(T).}
\tag{MSF.8}
\]

Indeed, the trace norm dominates the absolute value of the trace.  Thus continuous spectral mass
is not merely “lost” in the Hilbert--Schmidt limit; it is the exact conserved charge obstructing
trace-norm convergence.

## 5. Trace-norm convergence classification

### Theorem 5.1 -- trace formation converges if and only if continuous mass vanishes

For positive trace-class `T`,

\[
 \boxed{
 M_N(T)\longrightarrow\Pi_{\rm at}(T)\text{ in }S_1
 \iff m_c(T)=0.}
\tag{MSF.9}
\]

#### Proof: necessity

If `M_N(T)` converges in trace norm, then it converges in Hilbert--Schmidt norm to the same limit.
Equation `(MSF.4)` makes that limit `Pi_at(T)`.  Trace continuity and `(MSF.6)` then give

```text
tr(T)=tr(Pi_at(T))=m_at(T),
```

so `m_c(T)=0`.  Equivalently, `(MSF.8)` already forbids convergence when `m_c(T)>0`.

#### Proof: sufficiency

If `m_c(T)=0`, then

\[
 \|T^{1/2}P_c\|_2^2=\operatorname{tr}(P_cTP_c)=0.
\]

Hence `T^(1/2)P_c=0`, and positivity gives

```text
T=P_at T P_at.
```

Choose finite subsets `F` of `A(U)` increasing to all eigenvalues and put

```text
P_F=sum_(lambda in F)P_lambda,
T_F=P_F T P_F.
```

Strong convergence `P_F->P_at` and trace-class compactness give `||T-T_F||_1->0`.  For fixed
finite `F`, only finitely many phase ratios occur, so geometric averaging gives

\[
 M_N(T_F)\longrightarrow\sum_{\lambda\in F}P_\lambda T_FP_\lambda
 \quad\text{in }S_1.
\]

Both Cesaro averaging and atomic pinching are trace-norm contractions.  Approximate `T` by `T_F`,
apply the finite result, and let `F` increase.  This proves `(MSF.9)`. QED.

### Corollary 5.2 -- spectral type is operationally recoverable from ideal convergence

For positive packets, the scalar

```text
m_c(T)
```

is exactly the obstruction to promoting Hilbert--Schmidt formation convergence to trace-norm
formation convergence.  It can be recovered as

\[
 \boxed{
 m_c(T)=\operatorname{tr}T-\operatorname{tr}\Pi_{\rm at}(T).}
\tag{MSF.10}
\]

Thus the ideal mismatch carries spectral-type information erased by the `S_2` limit itself.

## 6. Closed-range classification for arbitrary unitary spectrum

### Theorem 6.1 -- global transgression is proper exactly for finite spectrum

\[
 \boxed{
 \operatorname{ran}(1-\operatorname{Ad}_U)\text{ is closed on }S_2(H)
 \iff \sigma(U)\text{ is finite}.}
\tag{MSF.11}
\]

#### Proof: finite spectrum

If

```text
sigma(U)={lambda_1,...,lambda_r},
```

then

```text
S_2(H)=orthogonal direct sum_(i,j) P_i S_2(H) P_j.
```

On the `(i,j)` block, `delta` is scalar multiplication by

```text
1-conj(lambda_i)lambda_j.
```

It vanishes on equal phases and is bounded below on all other blocks by the minimum of a finite
nonempty set of positive numbers.  Hence it has closed range.

#### Proof: infinite spectrum

An infinite compact subset of the unit circle contains distinct pairs

```text
lambda_n,mu_n in sigma(U),      |lambda_n-mu_n|->0.
```

Choose disjoint spectral arcs `A_n,B_n` around these points, with diameters tending to zero and
nonzero spectral projections.  Take unit vectors

```text
x_n in E_U(A_n)H,      y_n in E_U(B_n)H,
```

and let `R_n=|x_n><y_n|`.  Then `||R_n||_2=1`.  Since the arcs are disjoint, `R_n` is orthogonal to
the fixed Hilbert--Schmidt space: a commuting operator has no block from `B_n` to `A_n`.

Spectral localization gives

```text
||U x_n-lambda_n x_n|| -> 0,
||U y_n-mu_n y_n||     -> 0.
```

The rank-one norm identity then yields

```text
||delta(R_n)||_2
 <= |1-conj(lambda_n)mu_n| + o(1) -> 0.
```

Thus `delta` has no positive lower bound on the orthogonal complement of its kernel.  The Hilbert
closed-range theorem implies that its range is not closed. QED.

### Corollary 6.2 -- spectral richness forces global ill-conditioning

Every finite spectral aperture has a bounded inverse on its off-resonant blocks.  If the full
spectrum is infinite, the best inverse norms over increasing apertures diverge.  This holds for
pure point, singular continuous, absolutely continuous, and mixed spectrum alike.

Hence closed-range failure is caused by infinite spectral richness, not specifically by
atomlessness.  Atomlessness decides the survivor and trace escape; infinitude decides global
transgression properness.

## 7. Functional-equation neutrality

Replacing `U` by `U*` conjugates every spectral value and leaves every spectral projection
unchanged.  Therefore it preserves:

1. `H_at`, `H_c`, `P_at`, and `P_c`;
2. the pinching `Pi_at`;
3. atomic and continuous trace masses;
4. the trace-norm convergence criterion `(MSF.9)`;
5. finiteness of the spectrum;
6. closedness of the transgression range.

The functional equation is again information-neutral: it reverses phase orientation without
changing the mixed-spectral formation geometry.  A common exact-recovery lift preserves the same
information distinctions.

## 8. Field laws and leverage

The mixed theorem yields a complete spectral formation table.

| source spectral feature | formed `S_2` law | formed `S_1` law |
|---|---|---|
| finite atomic spectrum | closed transgression; atomic pinching | trace-norm convergence |
| infinite pure point | nonclosed transgression; atomic pinching | trace-norm convergence |
| atomless continuous | dense nonclosed transgression; zero limit | no convergence for nonzero state |
| mixed atomic/continuous | nonclosed transgression; atomic pinching | convergence iff continuous mass zero |

This separates three quantities that the corpus often merges:

1. **phase cardinality** controls transgression properness;
2. **spectral type** controls the surviving fixed ideal;
3. **packet spectral mass** controls trace-class convergence.

The theorem provides unconditional leverage on any route obstruction realized by a unitary phase
packet: once its source spectral type and packet mass are known, all three global questions are
settled without further route-specific estimates.

## 9. Hostile boundaries

1. **No RH conclusion.** The source still must construct its unitary phase representation before
   zero specialization.
2. **Positive packets only in Theorem 5.1.** For general trace-class operators, zero continuous
   diagonal trace does not control cross blocks.
3. **Separability matters.** It makes the point spectrum countable and the block sum manageable.
4. **`S_2` is load-bearing.** Conjugation is unitary there, enabling exact mean-ergodic projection.
5. **Classical ingredients.** Spectral decomposition, compact commutant arguments, mean ergodicity,
   and trace ideals are classical.  The field contribution is their exact formation classification
   and use as a universal source test.
6. **Finite spectrum is stronger than pure point.** Infinite pure point retains all trace mass but
   still has nonclosed transgression.
7. **No claim that spectral type causes HT.** A separate source theorem must connect differential
   independence to spectral richness.

Corpus search found recurrence theorems for countable pure-point packets, spectral-type moment
fibers, finite pinching, and route-specific dephasing.  None found states `(MSF.2)`, `(MSF.9)`, and
`(MSF.11)` as one mixed-spectrum formation classification.

## 10. Lean status

The paper proof is dependency-closed.  The active formal audit is read-only, so no Lean file is
created or built.  Existing infrastructure covers Hilbert--Schmidt kernels, compactness, closed
range, trace norms, trace-class completeness, rank-one operators, and finite pinching.

Missing formal infrastructure:

1. atomic/continuous spectral subspaces for an arbitrary unitary;
2. compact-commutant vanishing on the continuous subspace;
3. countable atomic pinching in `S_2` and `S_1`;
4. the spectral-localization approximate rank-one construction for `(MSF.11)`;
5. the mean-ergodic Cesaro theorem on the project Hilbert--Schmidt carrier.

Status remains `[LEAN-PENDING]`.
