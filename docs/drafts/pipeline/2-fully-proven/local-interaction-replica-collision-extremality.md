# Local interaction attains the all-order quantum-return collision floor

- **ID:** `local-interaction-replica-collision-extremality`
- **Stage:** 2-fully-proven
- **Type:** DEPENDENCY-CLOSED PAPER PROOF / REPLICA MOMENTS /
  SPECTRAL-FORM-FACTOR LIMIT
- **Parent:**
  `../3-formalized/nearest-neighbor-qudit-projective-spectral-maximality.md`
- **Master candidate:**
  `../1-in-progress/universal-replica-collision-law-of-quantum-return.md`
- **Scientific status:** `[PAPER-PROVED]`
  `[ABSTRACT MOMENT LAW NOT NEW]`
  `[LOCAL PREMISE DISCHARGE CANDIDATE NEW]`
  `[PRIORITY PROVISIONALLY CLEARED] [SPECIALIST AUDIT OPEN]`
  `[LEAN PROOF OPEN]`

## Theorem A — exact finite collision expansion

Let
\[
 \mu=\sum_{j=1}^{D}p_j\delta_{E_j},
 \qquad p_j>0,\quad \sum_{j=1}^{D}p_j=1,
\]
and let
\[
 F_\mu(t)=\left|\sum_{j=1}^{D}p_je^{-itE_j}\right|^2.
\]
For \(m\geq1\), let
\[
 M_m(\mu)
 =
 \lim_{T\to\infty}\frac1{2T}
 \int_{-T}^{T}F_\mu(t)^m\,dt.
\]
Then
\[
 \boxed{
 M_m(\mu)
 =
 \sum_{\substack{k,\ell\in\mathbb N^D\\
                   |k|=|\ell|=m\\
                   \sum_jk_jE_j=\sum_j\ell_jE_j}}
 {m\choose k}{m\choose\ell}
 \prod_{j=1}^{D}p_j^{k_j+\ell_j}.
 }
                                                        \tag{1}
\]

### Proof

The all-order recurrence theorem gives
\[
 M_m(\mu)
 =
 \mathbb P(E_1+\cdots+E_m=E'_1+\cdots+E'_m)
                                                        \tag{2}
\]
for two independent \(m\)-samples from \(\mu\). The multiplicity vector
\(k\) of the first sample has probability
\[
 {m\choose k}\prod_jp_j^{k_j},
                                                        \tag{3}
\]
and the second sample has the analogous probability for \(\ell\).
Summing `(3)` over exactly the pairs with equal total energy proves `(1)`.
\(\square\)

## Theorem B — universal collision floor and equality classification

For every finite spectrum with fixed positive weight vector \(p\),
\[
 \boxed{
 M_m(\mu)\geq
 B_m(p):=
 \sum_{\substack{k\in\mathbb N^D\\|k|=m}}
 {m\choose k}^{\!2}\prod_{j=1}^{D}p_j^{2k_j}.
 }
                                                        \tag{4}
\]
Equality holds for every \(m\geq1\) simultaneously if and only if
\[
 \sum_jc_jE_j=0,\quad \sum_jc_j=0,\quad c\in\mathbb Z^D
 \quad\Longrightarrow\quad c=0.                       \tag{5}
\]
Equivalently, the projective rational spectral rank is \(D-1\).

### Proof

Every diagonal pair \(k=\ell\) occurs in `(1)`, giving `(4)`.

If `(5)` holds and a pair in `(1)` has equal total energy, then
\(c=k-\ell\) has zero coordinate sum and zero energy sum. Hence \(c=0\),
so \(k=\ell\). Thus `(4)` is equality for every \(m\).

Conversely, suppose `(5)` fails. Write a nonzero relation as
\[
 c=c^+-c^-,
 \qquad c^\pm_j=\max(\pm c_j,0).
\]
The zero coordinate sum gives
\[
 |c^+|=|c^-|=:m.
\]
The zero energy sum gives
\[
 \sum_jc^+_jE_j=\sum_jc^-_jE_j.
\]
Because \(c\neq0\), the multiplicity vectors \(c^+\) and \(c^-\) are
distinct. Their term in `(1)` is strictly positive because every \(p_j>0\).
Therefore
\[
 M_m(\mu)>B_m(p)
\]
at this finite replica order. This proves the equivalence. \(\square\)

### Interpretation

The floor is absolute only after spectral weights are fixed. A state
supported on one eigenvalue has fidelity one forever and is not compared to
a fully supported state. At fixed positive weights, every nontrivial
equal-cardinality energy-sum resonance raises at least one return moment;
maximal projective rank removes all such excess simultaneously.

## Theorem C — generic local collision extremality

Let \(n,q\geq2\), \(D=q^n\), and let
\(\mathcal L_{P_n,q}\) be the real vector space of arbitrary one-site and
nearest-neighbour two-site Hermitian Hamiltonians on the open \(q\)-level
path. For Lebesgue-almost every \(H\in\mathcal L_{P_n,q}\), for every
probability vector \(p\) on its simple energy spectrum and every \(m\geq1\),
\[
 \boxed{
 M_m(H,p)=B_m(p).
 }
                                                        \tag{6}
\]

### Proof

The parent theorem proves that almost every such \(H\) has maximal
projective rational rank \(D-1\). Theorem B then applies simultaneously to
every \(m\) and every positive \(p\). If some weights vanish, restrict to
their support; projective independence passes to every subset. \(\square\)

Thus one static, bounded-degree, finite-range Hamiltonian attains the
smallest possible long-time survival-return moment at every order for every
state after conditioning on its spectral weights.

## Theorem C2 — one-knob activation of the full collision hierarchy

Use the Hilbert--Schmidt orthogonal decomposition
\[
 \mathcal L_{P_n,q}
 =
 \mathcal A_{n,q}\oplus\mathcal V_{n,q},              \tag{7a}
\]
where \(\mathcal A_{n,q}\) contains the traceless one-site Hamiltonians and
\(\mathcal V_{n,q}\) contains the nearest-neighbour correlation terms whose
partial traces on both endpoints vanish. Thus every local Hamiltonian has a
unique form
\[
 H(g)=A+gV,\qquad
 A\in\mathcal A_{n,q},\quad V\in\mathcal V_{n,q}.     \tag{7b}
\]

For Lebesgue-almost every pair \((A,V)\), there is a countable exceptional
set \(C_{A,V}\subset\mathbb R\), containing \(0\), such that
\[
 \boxed{
  \rho(A+gV)=q^n-1
  \quad\text{for every }g\notin C_{A,V}.
 }
                                                               \tag{7c}
\]
Consequently every punctured interval around zero contains all but
countably many coupling strengths for which every nontrivial replica
collision has disappeared. At the uncoupled point,
\[
 \rho(A)\leq n(q-1)<q^n-1.                            \tag{7d}
\]
One scalar interaction knob therefore activates the full exponential
projective rank and the collision floor at every order simultaneously.

### Proof

The parent theorem constructs a countable family
\(\{P_r\}_{r\in\mathbb N}\) of nonzero real polynomials on
\(\mathcal L_{P_n,q}\): one discriminant polynomial and one symmetric
relation polynomial for each nonconstant rational zero-sum coefficient
vector. A Hamiltonian has simple spectrum and maximal projective rank
exactly when every \(P_r\) is nonzero.

For fixed \(r\), define
\[
 Q_{r,A,V}(g)=P_r(A+gV).                              \tag{7e}
\]
Its coefficients as a polynomial in \(g\) are polynomial functions of
\((A,V)\). The set of pairs for which \(Q_{r,A,V}\) is identically zero is
therefore algebraic. It is proper: because \(P_r\) is nonzero, choose
\(H_r\) with \(P_r(H_r)\neq0\), decompose \(H_r=A_r+V_r\) by `(7a)`, and
observe that \(Q_{r,A_r,V_r}(1)\neq0\). Hence this identity locus has
Lebesgue measure zero.

Remove the countable union of these null identity loci over \(r\). For
every remaining pair \((A,V)\), each polynomial \(Q_{r,A,V}\) is nonzero
and therefore has finitely many real roots. The union of those root sets
over \(r\) is countable; outside it all obstruction polynomials are nonzero,
which proves `(7c)`.

Finally, the eigenvalues of an onsite Hamiltonian are sums of \(n\) local
eigenvalues. Relative to one reference level per site, every energy
difference lies in the rational span of at most \(n(q-1)\) local gaps.
Therefore \(\rho(A)\leq n(q-1)\). The strict inequality in `(7d)` follows
from \(q^n>1+n(q-1)\) for \(n,q\geq2\), so \(0\in C_{A,V}\). \(\square\)

The exceptional coupling strengths are not uniformly controlled and can
accumulate at zero because \(C_{A,V}\) is only countable. The theorem is an
exact infinite-time arithmetic transition, not a lower bound on the finite
time required to resolve the newly created frequencies.

## Theorem D — exact independent-phase time law

For every \(H\) in the full-measure set of Theorem C and every continuous
\(h:[0,1]\to\mathbb R\),
\[
 \boxed{
 \lim_{T\to\infty}\frac1{2T}
 \int_{-T}^{T}
 h\!\left(\left|\sum_{j=1}^{D}p_je^{-itE_j}\right|^2\right)dt
 =
 \int_{\mathbb T^D}
 h\!\left(\left|\sum_{j=1}^{D}p_jz_j\right|^2\right)dm(z).
 }
                                                        \tag{7}
\]
Here \(m\) is normalized Haar measure.

### Proof

Maximal projective rank makes the relative phase orbit uniquely
equidistributed on \(\mathbb T^{D-1}\). The integrand is invariant under one
common phase, so Haar integration on \(\mathbb T^{D-1}\) equals Haar
integration on \(\mathbb T^D\). Apply Kronecker--Weyl to the continuous
function in `(7)`. \(\square\)

Equation `(7)` is exact at finite size. It identifies deterministic
long-time sampling of one Hamiltonian with an independent-phase ensemble;
it does not identify a finite mixing time.

## Theorem E — exact spectral-form-factor moments

Define
\[
 X_D(t)
 =
 \frac1D\left|\sum_{j=1}^{D}e^{-itE_j}\right|^2.
                                                        \tag{8}
\]
For every \(m\geq1\),
\[
 \boxed{
 \lim_{T\to\infty}\frac1{2T}\int_{-T}^{T}X_D(t)^m\,dt
 =
 a_{D,m}:=
 \frac1{D^m}
 \sum_{\substack{k\in\mathbb N^D\\|k|=m}}
 {m\choose k}^{\!2}.
 }
                                                        \tag{9}
\]

### Proof

Take \(p_j=1/D\) in `(6)`. Since
\[
 X_D=D\left|\frac1D\sum_je^{-itE_j}\right|^2,
\]
the \(m\)-th moment gains a factor \(D^m\), giving `(9)`. Equivalently,
`(7)` identifies it with the \(m\)-th moment of
\[
 \left|\frac1{\sqrt D}\sum_{j=1}^{D}U_j\right|^2
\]
for independent Haar phases \(U_j\). \(\square\)

## Theorem F — unconditional iterated exponential limit

Let \(H_n\) be any choice from the full-measure local set at size \(n\), and
put \(D_n=q^n\). First take the long-time law of \(X_{D_n}\), then let
\(n\to\infty\). The resulting probability measures converge weakly to the
unit-mean exponential law:
\[
 \boxed{
 \lim_{n\to\infty}\lim_{T\to\infty}
 \operatorname{Law}_{t\in[-T,T]}X_{D_n}(t)
 =
 \operatorname{Exp}(1).
 }
                                                        \tag{10}
\]

### Moment proof

Fix \(m\). In `(9)`, the multiplicity vectors with \(m\) distinct occupied
indices have \(k_j\in\{0,1\}\). Their contribution is
\[
 \frac{\binom Dm(m!)^2}{D^m}
 \longrightarrow m!.                                  \tag{11}
\]

Every remaining vector has support size \(s\leq m-1\). For each fixed
\(s\), there are
\[
 \binom Ds\binom{m-1}{s-1}
\]
choices of support and positive multiplicities, and
\({m\choose k}^2\leq(m!)^2\). Hence the total repeated-index contribution
is bounded by a constant depending only on \(m\) times
\[
 \frac{D^{m-1}}{D^m},
\]
which tends to zero. Therefore
\[
 a_{D,m}\longrightarrow m!.                           \tag{12}
\]

The first moment is identically one, so the finite-\(D\) laws are tight.
Convergence of the \((m+1)\)-st moments supplies uniform integrability for
the \(m\)-th powers. Every subsequential weak limit therefore has all
moments \(m!\). The unit-mean exponential law has these moments and is
moment-determinate, for example by Carleman's criterion. Every
subsequential limit is consequently \(\operatorname{Exp}(1)\), proving
`(10)`. \(\square\)

## Direct literature relation

Riddell--Bertini prove rational independence of only the one-particle
energies in free fermion models. Their many-body energies retain many
replica collisions, so higher spectral-form-factor moments exceed the
Poisson prediction. They explicitly identify the interplay between rational
independence and interacting perturbations as future research.

The parent local theorem supplies the missing interacting statement:
generic nearest-neighbour interaction lifts the projective rank from
\(O(n)\) to \(q^n-1\). Theorems C--F then prove the exact all-order
independent-phase plateau and its exponential limit.

Vallejo-Fabila--Torres-Herrera derive exponential late-time return and
spectral-form-factor distributions under a central-limit condition. Theorem
F reaches the same limiting shape from exact finite-size moment identities,
with no central-limit premise and no Hamiltonian ensemble.

Campos Venuti--Odavić--Hamma (2026) is a direct collision with the abstract
content of Theorems D--F. It identifies the SFF with a planar random walk,
proves exact arbitrary moments under finite-order nondegeneracy, proves that
all-order nondegeneracy is equivalent to rational independence, and obtains
the Gaussian/exponential thermodynamic law under a Lyapunov weight
condition. Therefore Theorems D--F are not new as abstract spectral
probability statements.

The surviving candidate contribution is sharply delimited:

> almost every bounded-degree static nearest-neighbour qudit Hamiltonian
> satisfies the rational-independence premise that the 2026 paper treats as
> difficult and tests numerically for nonintegrable models.

Theorems C--F remain valuable corollaries because they translate that new
local generator into established SFF language, but priority must be claimed
only for the premise discharge and its tensor-local origin.

## Scope and attack points

1. The result is a symmetric infinite-time average, not a finite laboratory
   equilibration time.
2. The ordered limit \(T\to\infty\) before \(n\to\infty\) is essential.
3. The theorem concerns the full inhomogeneous local coupling space.
   Translation-invariant fixed-parameter subfamilies remain open.
4. The independent-phase plateau is not a claim of Wigner--Dyson statistics
   at finite time or local energy scales.
5. Theorem C inherits every open specialist and priority issue of the
   parent maximal-rank proof.
6. Equations `(1)`--`(12)` require unconditional Lean formalization before
   entering the manuscript.
7. Theorems D--F and the abstract combinatorics behind Theorems A--B must be
   cited as prior or elementary background, not presented as standalone
   novelty.
8. Theorem C2 removes the need to tune every local coefficient after a
   generic onsite background and interaction profile have been fixed, but it
   does not cover a prescribed laboratory Hamiltonian or a
   translation-invariant profile.

## Promotion gate

- [x] dependency-closed paper proof
- [x] no numerical computation
- [x] exact fixed-weight qualification
- [x] ordered-limit qualification
- [x] direct 2026 SFF-moment collision identified
- [x] dependency-closed one-knob activation proof
- [x] abstract one-knob polynomial avoidance formalized
- [ ] independent combinatorics/probability audit
- [x] exact-object priority provisionally cleared
- [ ] local generator formalization
- [ ] collision-floor and equality formalization
- [ ] finite-size SFF moment formalization
- [ ] exponential-limit formalization
