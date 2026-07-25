# Quaternionic Real Morita descent shifts even parity to odd parity

- **Status:** Formalized in Lean; novelty needs audit
- **Claim type:** THEOREM
- **Date:** 2026-07-25
- **Role:** Non-doubling parity mechanism for the rational CCM Real-Brauer lift

## Statement

Let \(A,E,M\) be complex vector spaces. Suppose:

1. \(\alpha:A\to A\) is conjugate-linear and \(\alpha^2=1\);
2. \(J:E\to E\) is conjugate-linear and \(J^2=-1\);
3. \(\sigma:M\to M\) is conjugate-linear and \(\sigma^2=1\);
4. \(s:A\to\operatorname{End}_{\mathbb C}(E)\) and
   \(r:A\to\operatorname{End}_{\mathbb C}(M)\) are actions satisfying
   \[
     (-J)(s(a)e)=s(\alpha(a))(-Je),
     \qquad
     \sigma\!\left(r(\alpha(a))m\right)=r(a)\sigma(m)
     \tag{R}
   \]
   for every \(a,e,m\).

Define the complex vector space of Morita intertwiners
\[
  \operatorname{Mor}_{s,r}(E,M)=
  \left\{F:E\to_{\mathbb C}M:
    F(s(a)e)=r(a)F(e)\text{ for all }a,e\right\}.
\]
Then
\[
  (\tau F)(e)=\sigma\!\left(F(-Je)\right)
  \tag{1}
\]
defines a conjugate-linear endomorphism of
\(\operatorname{Mor}_{s,r}(E,M)\) satisfying
\[
  \tau^2=-1.
\]

Thus Morita descent through a quaternionic Real-Brauer fiber turns an even Real module into
an odd \(K_{\mathbb R}\)-object without replacing the descended complex multiplicity space by
a direct sum of two copies.

## Proof

### 1. Endomorphism-algebra specialization

For \(A=\operatorname{End}_{\mathbb C}(E)\), \(s(T)=T\), the required even
Real structure is forced by \(J\). Since \(J^{-1}=-J\), set
\[
  \alpha(T)=JTJ^{-1}=-JTJ.
\]
It is conjugate-linear as a function of \(T\), preserves composition and the identity, and
\(\alpha^2=1\).

Its source compatibility is
\[
  (-J)(Te)=\alpha(T)(-Je).
  \tag{2}
\]
Indeed,
\[
  \alpha(T)(-Je)=(-JTJ)(-Je)=-JT(e).
\]

### 2. \(\tau F\) is complex-linear in \(e\)

Both \(e\mapsto -Je\) and \(\sigma\) are conjugate-linear, while \(F\) is complex-linear.
Their composite is complex-linear. Explicitly, for \(z\in\mathbb C\),
\[
\begin{aligned}
  (\tau F)(ze)
    &=\sigma\!\left(F(-J(ze))\right)\\
    &=\sigma\!\left(F(\overline z(-Je))\right)\\
    &=\sigma\!\left(\overline z F(-Je)\right)
     =z(\tau F)(e).
\end{aligned}
\]

### 3. \(\tau F\) remains a Morita intertwiner

Using the source part of (R), the defining equivariance of \(F\), and the target part of (R),
\[
\begin{aligned}
  (\tau F)(s(a)e)
    &=\sigma\!\left(F((-J)(s(a)e))\right)\\
    &=\sigma\!\left(F(s(\alpha(a))(-Je))\right)\\
    &=\sigma\!\left(r(\alpha(a))F(-Je)\right)\\
    &=r(a)\sigma\!\left(F(-Je)\right)
     =r(a)(\tau F)(e).
\end{aligned}
\]
Hence \(\tau\) restricts to \(\operatorname{Mor}_{s,r}(E,M)\).

### 4. \(\tau\) is conjugate-linear in \(F\)

For \(z\in\mathbb C\),
\[
  \tau(zF)(e)=\sigma(zF(-Je))
             =\overline z\,\tau(F)(e).
\]
Additivity follows from additivity of \(F\) and \(\sigma\).

### 5. Square

Since \(J\) is additive and \(J^2=-1\),
\[
  (-J)(-Je)=J^2e=-e.
\]
Consequently,
\[
\begin{aligned}
  (\tau^2F)(e)
    &=\sigma\!\left((\tau F)(-Je)\right)\\
    &=\sigma^2\!\left(F((-J)(-Je))\right)\\
    &=F(-e)=-F(e).
\end{aligned}
\]
Thus \(\tau^2=-1\).

## Hostile checks

- **No hidden doubling:** carrier is the actual intertwiner subspace of
  \(\operatorname{Hom}_{\mathbb C}(E,M)\); theorem introduces no product or direct sum.
- **Parity is not inserted by decree:** minus sign is forced by \(J^{-2}=-1\).
- **No finite-dimensional assumption:** proof is algebraic and applies to infinite-dimensional
  modules; analytic continuity is a separate application obligation.
- **No trace or RH premise:** no spectrum, positivity, zero set, or explicit-formula assumption
  occurs.
- **Compatibility is necessary:** without (R), formula (1) need not preserve Morita
  intertwiners.

## Application boundary

For rational CCM, take \(E=\ell^2(\mathbb Q^\times)\) with
\[
  (Jf)(q)=\operatorname{sgn}(q)\overline{f(-q)}
\]
and \(\alpha(T)=-JTJ\). The theorem proves the exact parity shift once the analytic CCM closed
cyclic cokernel is exhibited as an even Real module for the operator field and its Morita
intertwiner realization is identified with the single complex CCM realization.

Those two identifications remain application-specific `[OPEN CORE]`; this theorem does not
assert them.

## Evidence and novelty

This is the elementary algebraic mechanism behind the degree-four Real Brauer shift. Moutuou's
classification supplies the established Real-Brauer context. The explicit formulation as the
non-doubling parity bridge required by the CCM/Deninger construction is new synthesis pending
expert review.

## Lean formalization

Module:

- `GaloisForLFunctions.RHTower.KRealMoritaParityShift`

Formal capstones:

- `kRealOddEndomorphismRealStructure_sq`;
- `kRealOddInverseSigma_endomorphism`;
- `kRealMoritaReflection_mem`;
- `kRealMoritaDescentSigma_sq`;
- `kRealMoritaParityShift`;
- `kRealMoritaActionReflection_mem`;
- `kRealMoritaActionDescentSigma_sq`;
- `kRealMoritaActionParityShift`.

## Gates

- [x] Dependency-closed paper proof
- [x] Hostile no-doubling and circularity audit
- [x] Formalized in Lean; minimal leaf build and axiom audit passed
- [ ] Applied to completed CCM cyclic cokernel

## Sources

- El-kaïoum M. Moutuou, *Graded Brauer groups of a groupoid with involution*,
  arXiv:1202.2057.
- Dmitry Kaledin, *Cyclic homology with coefficients*, arXiv:math/0702068.
- Emanuele Dotto, *Stable Real K-theory and Real topological Hochschild homology*,
  arXiv:1212.4310.

## Log

- 2026-07-25 — theorem isolated from Real-Brauer attack on rational CCM target. Paper proof
  completed without numerical evidence or RH assumptions.
- 2026-07-25 — formalized in `KRealMoritaParityShift.lean`. Minimal Lean check and cached leaf
  build passed. Capstone axiom audit contains only `propext`, `Classical.choice`, and
  `Quot.sound`.
- 2026-07-25 — generalized from the full algebraic endomorphism ring to an arbitrary represented
  Real operator algebra, covering the bounded-operator form required by analytic CCM. Cached
  leaf build and axiom audit passed unchanged.
