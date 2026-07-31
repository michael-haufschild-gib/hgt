# Prime-tail reflection-folded second-order resolvent

- **ID:** `prime-tail-reflection-folded-second-order-resolvent`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) / SOURCE--DIVISOR BRIDGE
- **Scientific status:** `[PROVED HERE] [CORPUS-NEW EXACT BRIDGE]`
  `[EXTERNAL NOVELTY PROVISIONAL] [NOT RH]`
- **Parents:**
  - `critical-half-density-prime-tail-resolvent-law.md`;
  - `../not_new_scientific_knowledge/prime-tail-copoisson-essential-boundary-bockstein.md`.

## Result

The first-order prime-tail equation can be folded across the functional equation before any zero
is selected. The fold has four properties that the separate reflected modes did not have
simultaneously:

1. its forcing is the literal ordinary-integer prime-power measure and is independent of the
   spectral parameter;
2. functional-equation reflection is internal because the folded parameter is
   \(\mu=(s-\frac12)^2\);
3. every Xi zero produces a single nonzero global homogeneous mode with source-fixed Cauchy data;
4. multiplicity is the exact monodromy coefficient.

Thus functional-equation cross-landing is no longer the open core. The remaining RH-bearing
statement is sharper: prove that these source-created global modes are **spectral rather than
resonant** for one source-defined self-adjoint, resolvent-stable completion. That theorem would
force every \(\mu\) to be real; the known absence of real nontrivial zeta zeros would then give RH.

## 1. Completed prime-tail branch

Put
\[
 a_n=\frac{\Lambda(n)}{\log n}\quad(n\ge2),\qquad
 \Pi_0=\sum_{n\ge2}\frac{\Lambda(n)}{\sqrt n\,\log n}\,\delta_{\log n}.
\tag{1}
\]
Let
\[
 \Xi_C(\lambda)=\Xi\!\left(\frac12+\lambda\right).
\tag{2}
\]
It is even and entire. On a simply connected zero-free open set choose a branch
\[
 P(\lambda)=\log\Xi_C(\lambda)
\tag{3}
\]
compatible with \(P(-\lambda)=P(\lambda)\).

For \(L>0\), away from the prime jump points, define the completed tail branch
\[
 \mathcal H_\lambda(L)
 =
 e^{\lambda L}
 \left(
   P(\lambda)
   -
   \sum_{\log n<L}a_n n^{-1/2-\lambda}
 \right).
\tag{4}
\]
On \(\operatorname{Re}\lambda>\frac12\), this is the earlier literal prime-tail source plus the
homogeneous polynomial--Gamma completion term. Equation `(4)` then continues that source branch
without choosing a zero.

At \(L=\log n\), the jump of `(4)` is
\[
 -e^{\lambda\log n}a_nn^{-1/2-\lambda}
 =-\frac{\Lambda(n)}{\sqrt n\,\log n}.
\tag{5}
\]
Consequently, in distributions on \((0,\infty)\),
\[
 \boxed{\qquad
 (\partial_L-\lambda)\mathcal H_\lambda=-\Pi_0.
 \qquad}
\tag{6}
\]
The Gamma and polynomial completion changes only the homogeneous boundary datum \(P(\lambda)\);
it does not change the ordinary-prime forcing.

## 2. Reflection fold

For \(\lambda\ne0\), define
\[
 \mathcal C_\lambda
 =\frac{\mathcal H_\lambda+\mathcal H_{-\lambda}}2,
 \qquad
 \mathcal S_\lambda
 =\frac{\mathcal H_\lambda-\mathcal H_{-\lambda}}{2\lambda}.
\tag{7}
\]
The second expression has a removable value at \(\lambda=0\). Both are even in \(\lambda\), hence
depend on the single parameter
\[
 \mu=\lambda^2.
\tag{8}
\]

### Theorem 1: parameter-independent second-order forcing

\[
 \boxed{
 \begin{aligned}
  (\partial_L^2-\lambda^2)\mathcal S_\lambda&=-\Pi_0,\\
  (\partial_L^2-\lambda^2)\mathcal C_\lambda&=-\partial_L\Pi_0.
 \end{aligned}}
\tag{9}
\]

#### Proof

Apply \(\partial_L+\lambda\) to `(6)`:
\[
 (\partial_L^2-\lambda^2)\mathcal H_\lambda
 =-\partial_L\Pi_0-\lambda\Pi_0.
\tag{10}
\]
Replacing \(\lambda\) by \(-\lambda\) gives
\[
 (\partial_L^2-\lambda^2)\mathcal H_{-\lambda}
 =-\partial_L\Pi_0+\lambda\Pi_0.
\tag{11}
\]
The difference divided by \(2\lambda\) and the half-sum give `(9)`.

This is an actual reflection fold, not a relabeling: the two first-order branches have disjoint
absolute Euler half-planes. Their common object exists only after completed analytic continuation.

### Theorem 2: the completed Xi source is the Cauchy datum

Because there is no prime atom in \(0<L<\log2\),
\[
 \mathcal H_\lambda(0)=P(\lambda),\qquad
 \partial_L\mathcal H_\lambda(0)=\lambda P(\lambda).
\tag{12}
\]
Therefore
\[
 \boxed{
 \begin{aligned}
  \mathcal C_\lambda(0)&=P(\lambda),&
  \partial_L\mathcal C_\lambda(0)&=0,\\
  \mathcal S_\lambda(0)&=0,&
  \partial_L\mathcal S_\lambda(0)&=P(\lambda).
 \end{aligned}}
\tag{13}
\]
Thus \(\log\Xi_C\) is simultaneously the Dirichlet datum of the even fold and the Neumann datum
of the odd fold. The source point \(L=0\) is fixed before divisor localization.

## 3. Every Xi conormal becomes one source-pointed global mode

Let
\[
 \rho=\frac12+\lambda_\rho
\tag{14}
\]
be a nontrivial Xi zero of multiplicity \(m_\rho\). Positive monodromy of `(3)` around
\(\lambda_\rho\) is
\[
 \Delta_\rho P=2\pi i\,m_\rho.
\tag{15}
\]
All finite prime sums in `(4)` are single-valued. Evenness of \(\Xi_C\) makes the two folded
branches carry the same monodromy orientation in the \(\lambda\)-coordinate. Hence
\[
 \Delta_\rho\mathcal H_\lambda
 =2\pi i\,m_\rho e^{\lambda_\rho L},
\qquad
 \Delta_\rho\mathcal H_{-\lambda}
 =2\pi i\,m_\rho e^{-\lambda_\rho L}.
\tag{16}
\]

### Theorem 3: reflection-internal global conormal modes

\[
 \boxed{
 \begin{aligned}
  \Delta_\rho\mathcal C
  &=2\pi i\,m_\rho\cosh(\lambda_\rho L),\\
  \Delta_\rho\mathcal S
  &=2\pi i\,m_\rho
    \frac{\sinh(\lambda_\rho L)}{\lambda_\rho}.
 \end{aligned}}
\tag{17}
\]
At \(\lambda_\rho=0\), the second mode has the removable value \(2\pi i\,m_\rho L\).

Both functions are entire in \(L\), nonzero, and satisfy the homogeneous equation
\[
 (\partial_L^2-\mu_\rho)u=0,
 \qquad
 \mu_\rho=(\rho-\tfrac12)^2.
\tag{18}
\]
Their Cauchy data are source-fixed:
\[
 \begin{array}{c|cc}
 &u(0)&u'(0)\\ \hline
 \Delta_\rho\mathcal C&2\pi i\,m_\rho&0\\
 \Delta_\rho\mathcal S&0&2\pi i\,m_\rho.
 \end{array}
\tag{19}
\]
The coefficient retains multiplicity exactly. Parameter derivatives retain the full polynomial
Jordan-jet tower. Functional-equation partners \(\lambda_\rho\) and \(-\lambda_\rho\) give the
same \(\mu_\rho\)-mode, so reflection is internal before Hilbert adjunction is discussed.

## 4. Exact RH consumer: spectral, not resonant

Complex conjugation sends
\[
 \mu_\rho\longmapsto\overline{\mu_\rho}.
\tag{20}
\]
Suppose a source-defined rigging
\[
 \Phi_{\rm src}\subset\mathcal H_{\rm src}\subset\Phi_{\rm src}'
\tag{21}
\]
and a self-adjoint realization \(A\) of the folded second-order operator satisfy:

1. every mode in `(17)` is a nonzero element of \(\Phi_{\rm src}'\);
2. it is a transpose eigenfunctional of \(A\) with eigenvalue \(\mu_\rho\);
3. for every \(z\notin\mathbb R\), the Hilbert resolvent
   \((A-z)^{-1}\) maps \(\Phi_{\rm src}\) onto itself.

Then every \(\mu_\rho\) is real. Indeed, if \(\mu_\rho\notin\mathbb R\), resolvent surjectivity
would make the transpose kernel of \(A-\mu_\rho\) zero, contradicting clause 1.

If \(\mu_\rho=(a+ib)^2\) is real, then \(2ab=0\). A nontrivial zeta zero is not real in
\(0<\operatorname{Re}s<1\), so \(b\ne0\), hence \(a=0\). Therefore
\[
 \operatorname{Re}\rho=\frac12.
\tag{22}
\]

This is the short RH consumer. The unproved content is the source-derived resolvent-stable landing,
not the reality argument.

## 5. What changed

The former open core asked for two first-order reflected conormals to become one class. Equation
`(17)` performs the functional-equation part unconditionally:

```text
literal prime/Gamma completed tail
  -> reflection divided difference before zero specialization
  -> one mu-dependent second-order forced equation
  -> every reflection-paired Xi conormal becomes a nonzero global Cauchy mode.
```

What remains is no longer “make reflection internal.” It is:

`[OPEN CORE] [XI_PRIME_TAIL_FOLDED_LIMITING_ABSORPTION]`

> Construct the essential-singular continuation of `(7)` as a common, Hausdorff,
> resolvent-stable rigging of one self-adjoint folded operator. Prove that monodromy commutes with
> the limiting-absorption boundary map, so every mode `(17)` lands nontrivially in the transpose
> spectral space rather than only in a larger resonance/hyperfunction space.

This wording is falsifiable. A completion accepting every entire exponential as a compact-support
distribution is too large: it turns all complex resonances into “modes.” A scalar \(L^2\)
completion is too small: it loses continuous-spectrum fibres. The required object must retain
the source monodromy while remaining invariant under the nonreal resolvent.

## 6. Critical source carrier correction

The first Wold normal jet does not disappear at the critical half-density. On
\(\ell^2(\mathbb N_{>0})\), its diagonal coefficient is
\[
 b_\sigma(n)=\Lambda(n)n^{-\sigma}.
\tag{23}
\]
For every \(\sigma>0\), \(b_\sigma(n)\to0\), so the diagonal operator is compact. For the initial
prime exhaustion \(P_y=\{p:p\le y\}\), the finite Wold derivative multiplied by \(n^{-\sigma}\)
converges to `(23)` in operator norm. Once \(y\) is large in terms of \(\sigma\), the error is
bounded by
\[
 \left\|\mathcal E'_{P_y}(0)Q^\sigma-L_\sigma\right\|
 \le \frac{\log y}{y^\sigma}.
\tag{24}
\]

To see this, prime powers with base \(p>y\) contribute at most
\(\sup_{p>y}\log p/p^\sigma\). A non-prime-power error can occur only when exactly one of its
prime divisors \(p\) lies in \(P_y\); choosing another divisor \(q>y\) gives
\[
 \frac{\log p}{(pq)^\sigma}
 \le
 \left(\sup_{t\ge2}\frac{\log t}{t^\sigma}\right)y^{-\sigma}.
\tag{25}
\]
Both bounds are at most `(24)` for sufficiently large \(y\).

At \(\sigma=\frac12\), this critical source operator is compact although it is not
Hilbert--Schmidt. More precisely, on the prime-power incidence space with coordinates \((p,k)\),
\[
 A e_{p,k}=\frac1{k p^{k/2}}e_{p,k},
\qquad
 DA e_{p,k}=\frac{\log p}{p^{k/2}}e_{p,k},
\tag{26}
\]
and
\[
 A,DA\in\mathcal S_q\quad\Longleftrightarrow\quad q>2.
\tag{27}
\]
The forward implication follows by comparison with
\(\sum_n(\log n)^q n^{-q/2}\); the reverse implication follows already from the prime,
\(k=1\), subseries and Euler's divergence of \(\sum_p1/p\).

Consequently the critical carrier is the concrete Hausdorff Fréchet ideal
\[
 \mathcal S_{2+}:=\bigcap_{q>2}\mathcal S_q,
\tag{28}
\]
not an absent operator. Essential singularity enters when one tries to take the noncontinuous
trace/limiting-absorption boundary which creates the divisor monodromy. This corrects the earlier
statement that a new completion is needed merely to retain
\(\Lambda(n)/\sqrt n\): ordinary operator norm already retains it.

## Hostile audit

1. **Not RH.** Modes `(17)` exist for a hypothetical off-line zero. Off-line modes are
   resonances: they are entire functions and compact-support distributions, but not tempered
   translation eigenmodes.
2. **Not Hilbert--Pólya by notation.** Calling \(\mu_\rho\) an eigenvalue without constructing
   `(21)` and resolvent-stable landing is forbidden.
3. **Not positivity.** Positive forcing \(\Pi_0\) does not make the boundary response a Herglotz
   function. It is a source-to-boundary matrix element, not a positive diagonal resolvent
   coefficient.
4. **Generalized-prime falsifier remains.** An off-line generalized-prime system has the same
   formal fold. It fails precisely at spectral rather than resonant landing.
5. **Compactness is not traceability.** Equation `(24)` does not continue the trace. The
   critical operator lies outside \(\mathcal S_2\), and its raw prime trace diverges.
6. **No simplicity claim.** The monodromy coefficient retains \(m_\rho\); self-adjoint spectral
   landing of the order-zero mode would prove RH but does not by itself turn the analytic jet
   tower into a semisimple eigenspace.
7. **No common absolute Euler domain.** The two terms in `(7)` cannot be joined by termwise
   summation. Completed analytic continuation before folding is load-bearing and is exactly where
   essential singularity enters.

## Literature boundary

Hedenmalm's 2026 theta paper constructs a second-order differential boundary problem whose
nontrivial solutions are indexed by Xi zeros and identifies a positive self-adjoint operator-pair
form as the missing RH theorem:

- H. Hedenmalm, *Spectral interpretation of Riemann zeta zeros*,
  <https://arxiv.org/abs/2606.17494>.

Therefore no novelty is claimed for “a second-order Xi eigenproblem” or for the self-adjoint
consumer. Sierra's \(xp\) model and Connes--Consani's scaling Hamiltonian likewise establish the
spectrum-versus-resonance and absorption-spectrum background.

The provisional corpus-new delta is the exact conjunction `(4)`--`(19)`: the literal
ordinary-prime tail measure is the parameter-independent forcing, the completed
functional-equation branches are folded by a resolvent divided difference, and every divisor
monodromy becomes a single global \(\mu\)-mode with fixed Cauchy data and exact multiplicity.
A targeted primary-literature search found close second-order, Jost, and scaling constructions,
but not this exact prime-tail forced-resolvent fold. This is noncollision evidence, not a priority
claim.

## Gates

- [x] literal completed prime-tail branch fixed before zero specialization
- [x] first-order jump equation proved
- [x] reflection fold and parameter-independent second-order forcing proved
- [x] source Cauchy data proved
- [x] every Xi conormal and multiplicity landed in a nonzero global mode
- [x] functional-equation reflection internalized through \(\mu=\lambda^2\)
- [x] spectral-versus-resonant RH consumer isolated
- [x] critical Wold operator-norm/compact-ideal correction proved on paper
- [ ] construct source-defined folded limiting-absorption rigging
- [ ] prove nonzero resolvent-stable monodromy landing
- [ ] formalize the literal distributional source theorem
- [ ] RH
