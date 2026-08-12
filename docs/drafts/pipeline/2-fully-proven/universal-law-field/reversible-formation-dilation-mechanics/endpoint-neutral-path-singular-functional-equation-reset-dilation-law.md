# Endpoint-neutral functional-equation packets, path-singular finite lifts, and reversible reset dilation

- **ID:** ULF-RFDM-1
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Source:** packet-formation-mechanics/functional-equation-split-formation-lift-information-isometry-and-work-no-go.md
- **Statement:** A non-Dirac common recovery kernel is information-neutral at packet endpoints but forbids every finite-order deterministic execution of its fresh-reset path law; the exact two-step obstruction is collision deficit in total variation, Shannon entropy in forward KL, and infinite reverse KL, while a bilateral Bernoulli history supplies an invertible infinite-order dilation.
- **Status:** [PAPER-PROVED] [DEPENDENCY-CLOSED] [ROUTE-INDEPENDENT] [FUNCTIONAL-EQUATION CALIBRATED] [THREE-ORGAN LAW FUSION] [WITHHELD KMS PATH PREDICTION] [GENERIC DILATION MACHINERY OCCUPIED] [LEAN OPEN] [NOT RH]

## 1. Why the preceding packet theorem is not yet dynamics

Let \(X\) be a standard Borel observer space, let \(R:X\to X\) be a Borel involution, and let

\[
 \kappa_x=(\kappa_x(n))_{n\in\mathbb N}
 \tag{RFDM.1}
\]

be a measurable family of probability vectors. The split packet formation of an observer law
\(\mu\) is

\[
 \mathsf E_\kappa(\mu)(dx,n)=\mu(dx)\kappa_x(n).
 \tag{RFDM.2}
\]

The functional-equation packet theorem constructs the reset lift

\[
 \mathsf L((x,n),dy,m)=\delta_{Rx}(dy)\kappa_{Rx}(m).
 \tag{RFDM.3}
\]

It discards \(n\), applies \(R\), and samples a fresh recovery coordinate. On formed laws,

\[
 \mathsf L_*\mathsf E_\kappa(\mu)=\mathsf E_\kappa(R_*\mu),
 \qquad
 \mathsf L_*^2\mathsf E_\kappa(\mu)=\mathsf E_\kappa(\mu).
 \tag{RFDM.4}
\]

This is an involution of **laws**. It is not an invertible execution on individual packet histories.
The distinction is invisible to all one-time marginals and to endpoint KL isometry.

## 2. Stochastic isomorphisms cannot hide refreshment

### Lemma 2.1 -- a Markov isomorphism is a permutation

Let \(K,L\) be Markov kernels on a countable set \(H\), represented by row-stochastic matrices, and
suppose

\[
 KL=LK=I.
 \tag{RFDM.5}
\]

Then there is a bijection \(\phi:H\to H\) such that

\[
 K(i,j)=\mathbf 1_{j=\phi(i)},
 \qquad
 L(j,i)=\mathbf 1_{i=\phi^{-1}(j)}.
 \tag{RFDM.6}
\]

#### Proof

For \(i\ne j\), nonnegativity and \((KL)(i,j)=0\) give

\[
 K(i,h)>0\quad\Longrightarrow\quad L(h,j)=0.
\]

Hence every \(h\) in the support of row \(i\) of \(K\) satisfies \(L(h,i)=1\). If the same \(h\)
occurred in rows \(i\ne i'\), its row in \(L\) would contain two entries equal to one, impossible.
Fix \(h\) in the support of row \(i\). Since \(L(h,i)=1\),

\[
 (LK)(h,h')=K(i,h')=\mathbf 1_{h=h'}.
\]

Thus row \(i\) of \(K\) is the point mass at \(h\). Every row is deterministic; disjointness gives
injectivity and \(LK=I\) gives surjectivity. The formula for \(L\) follows. ∎

### Corollary 2.2 -- reset is not a stochastic involution on a reflection orbit

Fix one orbit \(O_x=\{x,Rx\}\). Its restricted packet space \(O_x\times\mathbb N\) is countable.
If either recovery law on this orbit has at least two positive atoms, then the restriction of
\(\mathsf L\) to \(O_x\times\mathbb N\) is not a Markov isomorphism. In particular, equation
\((\mathrm{RFDM}.4)\) cannot be strengthened on that orbit from formed-law involutivity to

\[
 \mathsf L\circ\mathsf L=I
 \tag{RFDM.7}
\]

as kernels.

#### Proof

The restricted reset never leaves \(O_x\times\mathbb N\). Every row above \((y,n)\), for
\(y\in O_x\), has history marginal \(\kappa_{Ry}\). A non-Dirac row contradicts Lemma 2.1. ∎

## 3. Exact endpoint/path defect

Let \(p=(p_i)_{i\in H}\) be a probability vector on a countable set. Define its diagonal coupling
and independent coupling by

\[
 \Delta_p(i,j)=p_i\mathbf 1_{i=j},
 \qquad
 (p\otimes p)(i,j)=p_ip_j.
 \tag{RFDM.8}
\]

Use

\[
 \operatorname{TV}(P,Q)=\frac12\sum_z|P(z)-Q(z)|.
\]

### Theorem 3.1 -- diagonal/refresh separation

For every countable probability vector \(p\),

\[
 \boxed{
 \operatorname{TV}(\Delta_p,p\otimes p)
 =1-\sum_i p_i^2.}
 \tag{RFDM.9}
\]

In extended relative entropy,

\[
 \boxed{
 D(\Delta_p\Vert p\otimes p)
 =H(p):=-\sum_i p_i\log p_i,}
 \tag{RFDM.10}
\]

with \(+\infty\) allowed. If \(p\) has at least two positive atoms, then

\[
 \boxed{
 D(p\otimes p\Vert\Delta_p)=+\infty.}
 \tag{RFDM.11}
\]

All three defects vanish simultaneously exactly when \(p\) is Dirac.

#### Proof

On the diagonal,

\[
 \sum_i|p_i-p_i^2|=1-\sum_i p_i^2.
\]

Off the diagonal,

\[
 \sum_{i\ne j}|0-p_ip_j|
 =\sum_{i\ne j}p_ip_j
 =1-\sum_i p_i^2.
\]

Dividing their sum by two proves \((\mathrm{RFDM}.9)\). On every diagonal atom with \(p_i>0\),
the likelihood ratio is \(p_i/p_i^2=1/p_i\). Therefore

\[
 D(\Delta_p\Vert p\otimes p)
 =\sum_i p_i\log(1/p_i)=H(p),
\]

which proves \((\mathrm{RFDM}.10)\). If \(p_i,p_j>0\) for \(i\ne j\), then \(p\otimes p\) assigns
positive mass to \((i,j)\), while \(\Delta_p\) assigns zero mass there. Absolute continuity fails,
so the reverse divergence is infinite. Finally, \(\sum_i p_i^2=1\) holds for a probability vector
exactly when one atom has mass one. ∎

The collision probability \(\sum_i p_i^2\) is exactly the fraction of the fresh-reset endpoint law
that happens to look deterministic. Its complement is the total-variation cost of pretending that
the two-step reset closes pointwise. Shannon entropy is the directed information cost of replacing
fresh reset by deterministic return. Reverse replacement is singular.

## 4. Finite observer order forces infinite source order

Let \(Z\) be a measurable source-history space, let \(T:Z\to Z\) be a measurable bijection, and let

\[
 \Pi:Z\longrightarrow X\times H
 \tag{RFDM.12}
\]

be a packet factor. Say that \((Z,T,\Pi)\) **executes the reset process** if, for every initial
observer law, the finite-dimensional distributions of

\[
 \Pi(z),\Pi(Tz),\Pi(T^2z),\ldots
 \tag{RFDM.13}
\]

are those of the Markov kernel \(\mathsf L\).

### Theorem 4.1 -- no finite-order execution of non-Dirac reset

Assume that \(\kappa_x\) is non-Dirac on a set of positive initial observer measure. No deterministic
reset execution can satisfy \(T^N=I\) for any finite \(N>0\).

More locally, if \(R^N x=x\) and \(T^N=I\), then execution of the reset process at \(x\) forces
\(\kappa_x\) to be Dirac.

#### Proof

If \(T^N=I\), process factorization first forces \(R^N x=x\) for almost every initial \(x\): the
observer coordinate of \(\Pi(T^Nz)\) equals both \(R^Nx\) by execution and \(x\) by periodicity.
Fix such an \(x\), and start from the packet conditional law above it. Because every
reset discards the old history, the reset process has

\[
 (H_0,H_N)\sim\kappa_x\otimes\kappa_x.
 \tag{RFDM.14}
\]

If \(T^N=I\), then \(\Pi(T^Nz)=\Pi(z)\) pointwise, so

\[
 (H_0,H_N)\sim\Delta_{\kappa_x}.
 \tag{RFDM.15}
\]

Equality of \((\mathrm{RFDM}.14)\) and \((\mathrm{RFDM}.15)\) forces
\(1-\sum_n\kappa_x(n)^2=0\) by Theorem 3.1, hence \(\kappa_x\) is Dirac. This contradicts the
non-Dirac hypothesis on a positive-measure set. ∎

### Corollary 4.2 -- functional-equation closure is only an observer quotient

For an involution \(R\), the packet law may close after two steps as in
\((\mathrm{RFDM}.4)\), but every deterministic execution of the full non-Dirac reset process has
infinite order. Thus

\[
 \boxed{
 \text{finite observer symmetry}
 \quad\not\Rightarrow\quad
 \text{finite source-history symmetry}.}
 \tag{RFDM.16}
\]

The obstruction is the exact coupling discrepancy
\((\mathrm{RFDM}.9)\)--\((\mathrm{RFDM}.11)\), not a topological metaphor.

## 5. Why one-time marginals do not suffice

Put

\[
 \widetilde H=H\times H,
 \qquad
 \widetilde\kappa_x=\kappa_x\otimes\kappa_{Rx},
\]

and define

\[
 \Phi(x,h_0,h_1)=(Rx,h_1,h_0).
 \tag{RFDM.17}
\]

Then

\[
 \Phi^2=I,
 \qquad
 \Phi_*\widetilde\kappa_x=\widetilde\kappa_{Rx}.
 \tag{RFDM.18}
\]

If only the first history coordinate is observed, every one-time packet conditional is correct.
After two steps, however, the first coordinate is the original \(h_0\), not a fresh sample.
Therefore endpoint marginals admit a finite involutive enlargement, while the full fresh-reset path
law does not. Infinite history is forced by **process execution**, not packet formation alone.

## 6. Positive survivor: bilateral reversible reset dilation

Let

\[
 \Omega=[0,1)^{\mathbb Z}
\]

with product Lebesgue law \(\lambda^{\mathbb Z}\), and let \(S\) be the bilateral left shift,
\((S\omega)_j=\omega_{j+1}\). For \(c_{-1}(x)=0\) and

\[
 c_n(x)=\sum_{j=0}^n\kappa_x(j),
\]

define the inverse-transform sampler

\[
 G(x,u)=n
 \quad\Longleftrightarrow\quad
 c_{n-1}(x)\le u<c_n(x).
 \tag{RFDM.19}
\]

Every \(c_n\) is measurable, so \(G\) is measurable, and

\[
 \lambda\{u:G(x,u)=n\}=\kappa_x(n).
 \tag{RFDM.20}
\]

Define

\[
 \mathcal T(x,\omega)=(Rx,S\omega),
 \qquad
 \Pi(x,\omega)=(x,G(x,\omega_0)).
 \tag{RFDM.21}
\]

### Theorem 6.1 -- reversible natural extension

The transformation \(\mathcal T\) is a measurable bijection with

\[
 \mathcal T^{-1}(x,\omega)=(Rx,S^{-1}\omega).
 \tag{RFDM.22}
\]

For every observer law \(\mu\), under \(\mu\otimes\lambda^{\mathbb Z}\) the factor process
\(\Pi,\Pi\mathcal T,\Pi\mathcal T^2,\ldots\) is exactly the reset Markov process. Conditional on
\(X_0=x\),

\[
 \Pr(H_0=n_0,\ldots,H_k=n_k\mid X_0=x)
 =\prod_{j=0}^k\kappa_{R^jx}(n_j).
 \tag{RFDM.23}
\]

Moreover,

\[
 \mathcal T^2(x,\omega)=(x,S^2\omega).
 \tag{RFDM.24}
\]

Hence the observer returns after two steps, while marked history advances by two independent seed
coordinates. The dilation has infinite order, and almost every seed history is nonperiodic.

#### Proof

Equation \((\mathrm{RFDM}.22)\) follows from \(R^2=I\) and invertibility of the bilateral shift.
At time \(j\), the observer is \(R^jx\), and the sampler reads \(\omega_j\). Product Lebesgue
measure makes \(\omega_0,\ldots,\omega_k\) independent uniforms. Applying
\((\mathrm{RFDM}.20)\) coordinatewise gives \((\mathrm{RFDM}.23)\). Equation
\((\mathrm{RFDM}.24)\) is immediate. For every \(N>0\), the event \(S^N\omega=\omega\) is
contained in \(\{\omega_0=\omega_N\}\), which has product-Lebesgue measure zero. Thus almost every
orbit is nonperiodic and \(\mathcal T\) cannot have finite order. ∎

### Theorem 6.2 -- endpoint information neutrality survives dilation

For finite observer laws \(\mu,\nu\), extended KL divergence obeys

\[
 D(\mu\otimes\lambda^{\mathbb Z}
   \Vert\nu\otimes\lambda^{\mathbb Z})
 =D(\mu\Vert\nu),
 \tag{RFDM.25}
\]

\[
 D(\mathcal T_*(\mu\otimes\lambda^{\mathbb Z})
   \Vert\mathcal T_*(\nu\otimes\lambda^{\mathbb Z}))
 =D(\mu\Vert\nu),
 \tag{RFDM.26}
\]

and

\[
 D(\Pi_*(\mu\otimes\lambda^{\mathbb Z})
   \Vert\Pi_*(\nu\otimes\lambda^{\mathbb Z}))
 =D(\mu\Vert\nu).
 \tag{RFDM.27}
\]

#### Proof

Equation \((\mathrm{RFDM}.25)\) is the common-product-kernel chain rule. A measurable bijection with
measurable inverse preserves extended KL in both directions by data processing, proving
\((\mathrm{RFDM}.26)\). By construction,
\(\Pi_*(\mu\otimes\lambda^{\mathbb Z})=\mathsf E_\kappa(\mu)\), so
\((\mathrm{RFDM}.27)\) is the split-formation information law. ∎

Thus one common seed history supports

\[
 \boxed{
 \text{exact endpoint information neutrality}
 \quad+\quad
 \text{infinite-order reversible execution}.}
 \tag{RFDM.28}
\]

## 7. Hasse recovery and functional-equation specialization

For \(t>0\), put

\[
 r(t)=\frac{1-e^{-t}}2,
 \qquad
 \kappa_t(n)=(1-r(t))r(t)^n.
 \tag{RFDM.29}
\]

Then \(0<r(t)<1/2\), so every Hasse recovery law is non-Dirac. Reflection acts by
\(R(t)=t^{-1}\), or in logarithmic scale \(x=\log t\), by \(R(x)=-x\).

### Theorem 7.1 -- exact Hasse execution defect

For every \(t>0\),

\[
 \boxed{
 \operatorname{TV}(\Delta_{\kappa_t},\kappa_t\otimes\kappa_t)
 =\frac{2r(t)}{1+r(t)}.}
 \tag{RFDM.30}
\]

Its forward relative entropy is

\[
 \boxed{
 D(\Delta_{\kappa_t}\Vert\kappa_t\otimes\kappa_t)
 =-\log(1-r(t))-\frac{r(t)}{1-r(t)}\log r(t),}
 \tag{RFDM.31}
\]

and its reverse relative entropy is \(+\infty\).

#### Proof

The geometric series gives

\[
 \sum_{n\ge0}\kappa_t(n)^2
 =(1-r)^2\sum_{n\ge0}r^{2n}
 =\frac{1-r}{1+r}.
\]

Substitution into \((\mathrm{RFDM}.9)\) gives \((\mathrm{RFDM}.30)\). Also
\(\sum_{n\ge0}n(1-r)r^n=r/(1-r)\). Expanding
\(-\sum_n\kappa_t(n)\log\kappa_t(n)\) gives \((\mathrm{RFDM}.31)\). Reverse divergence is
infinite because every geometric law has at least two positive atoms. ∎

### Corollary 7.2 -- exact balance locus

Both finite defect functions

\[
 V(t)=\frac{2r(t)}{1+r(t)},
 \qquad
 J(t)=-\log(1-r(t))-\frac{r(t)}{1-r(t)}\log r(t)
\]

are strictly increasing in \(t\). Therefore

\[
 V(t)=V(1/t)\iff t=1,
 \qquad
 J(t)=J(1/t)\iff t=1.
 \tag{RFDM.32}
\]

#### Proof

Since \(r'(t)=e^{-t}/2>0\), differentiate with respect to \(r\):

\[
 \frac d{dr}\frac{2r}{1+r}=\frac2{(1+r)^2}>0,
 \qquad
 \frac{dJ}{dr}=-\frac{\log r}{(1-r)^2}>0.
\]

Strict monotonicity and \(t=1/t\iff t=1\) prove the claim. ∎

This is an exact formation-balance selector for the scale fixed point. It is **not** an RH selector:
the corpus has not proved that the arithmetic source imposes equality of the two path defects, and
\(t\) is packet scale rather than the real part of a zero.

### Corollary 7.3 -- theta/Hasse natural extension

Let \(\nu_a\) be the theta-carrier scale law from the parent packet card, with
\(R_*\nu_a=\nu_{-a}\), and put

\[
 \overline Q_a=\nu_a\otimes\lambda^{\mathbb Z}.
\]

Then

\[
 \mathcal T_*\overline Q_a=\overline Q_{-a},
 \qquad
 \mathcal T_*^2\overline Q_a=\overline Q_a,
 \qquad
 \Pi_*\overline Q_a=\widehat Q_a.
 \tag{RFDM.33}
\]

The law closes after two steps because product seed measure is shift-invariant. Almost every marked
seed history remains open because the bilateral shift is nonperiodic. This is the precise meaning
of recurrent observation with open lifted history in this packet model.

## 8. Exact cross-organ prediction: Toeplitz--KMS reversibilization trilemma

The existing corpus theorem

invariant-positivity-reversibility-wall-and-kms-irreversibility-measure-law.md

starts from an operator-algebraic system rather than a packet kernel. For a marked isometry at
positive inverse temperature, it proves that orthogonal history layers have masses

\[
 p_q(n)=(1-q)q^n,
 \qquad 0<q<1.
 \tag{RFDM.34}
\]

This is exactly the same geometric law as Hasse recovery after the identification \(q=r(t)\). The
identification is at the level of the entire probability vector, not only its first moment.

### Theorem 8.1 -- canonical Hasse-to-KMS modular parameter transport

The Hasse packet itself reconstructs the KMS modular product:

\[
\boxed{
q(t)=\frac{\kappa_t(n+1)}{\kappa_t(n)}=r(t)
\quad(n\ge0),}
\tag{RFDM.34a}
\]

\[
\boxed{
\beta E=\log\frac{\kappa_t(n)}{\kappa_t(n+1)}
=-\log r(t).}
\tag{RFDM.34b}
\]

The expression is independent of \(n\), so no selected history layer is involved. Conversely, for
every \(q\in(0,1/2)\),

\[
\boxed{
t(q)=-\log(1-2q)}
\tag{RFDM.34c}
\]

is the unique Hasse scale whose recovery law is \(p_q\).

Functional-equation reflection transports to the involution

\[
\Theta(q)
=r\!\left(\frac1{-\log(1-2q)}\right)
\qquad(0<q<1/2).
\tag{RFDM.34d}
\]

It satisfies

\[
\Theta^2=I,
\qquad
\Theta(q)=q
\iff
q=q_*:=\frac{1-e^{-1}}2.
\tag{RFDM.34e}
\]

#### Proof

Equation \((\mathrm{RFDM}.34a)\) follows immediately from
\(\kappa_t(n)=(1-r(t))r(t)^n\). Taking the negative logarithm gives
\((\mathrm{RFDM}.34b)\). Since \(q=(1-e^{-t})/2\), solving for \(t\) gives
\((\mathrm{RFDM}.34c)\). By definition,

\[
\Theta=r\circ(t\mapsto t^{-1})\circ r^{-1},
\]

so it is an involution. Its fixed points correspond exactly to positive fixed points of
\(t\mapsto t^{-1}\), hence to \(t=1\), which gives \(q_*=r(1)\). ∎

Thus the Hasse packet canonically determines the **product** \(\beta E\) appearing in the KMS layer
law. It does not separately determine inverse temperature and energy; their rescaling remains a
clock gauge.

### Theorem 8.2 -- exact KMS layer-execution defect

If one KMS history cycle is observed only through its returned endpoint, deterministic return has
coupling \(\Delta_{p_q}\), while a fresh KMS-layer reset has coupling \(p_q\otimes p_q\). Their
exact separation is

\[
\boxed{
\operatorname{TV}(\Delta_{p_q},p_q\otimes p_q)
=\frac{2q}{1+q},}
\tag{RFDM.35}
\]

\[
\boxed{
D(\Delta_{p_q}\Vert p_q\otimes p_q)
=-\log(1-q)-\frac q{1-q}\log q,}
\tag{RFDM.36}
\]

and

\[
\boxed{
D(p_q\otimes p_q\Vert\Delta_{p_q})=+\infty.}
\tag{RFDM.37}
\]

#### Proof

Apply Theorem 3.1 to the layer distribution \((\mathrm{RFDM}.34)\). The same geometric-series
calculation as Theorem 7.1 gives \((\mathrm{RFDM}.35)\)--\((\mathrm{RFDM}.36)\); full support and
two distinct atoms give \((\mathrm{RFDM}.37)\). ∎

### Theorem 8.3 -- execution entropy equals KMS state entropy

Let

\[
\rho_q=(1-q)q^N
\tag{RFDM.38a}
\]

be the Toeplitz Gibbs density operator from the existing KMS theorem. Its eigenvalues in the depth
basis are precisely \(p_q(n)\). Therefore

\[
\boxed{
\operatorname{Tr}(\rho_q^2)
=\frac{1-q}{1+q},}
\tag{RFDM.38b}
\]

\[
\boxed{
1-\operatorname{Tr}(\rho_q^2)
=\operatorname{TV}(\Delta_{p_q},p_q\otimes p_q),}
\tag{RFDM.38c}
\]

and

\[
\boxed{
S_{\mathrm{vN}}(\rho_q)
:=-\operatorname{Tr}(\rho_q\log\rho_q)
=D(\Delta_{p_q}\Vert p_q\otimes p_q).}
\tag{RFDM.38d}
\]

Thus state mixedness and failure of finite path closure are the same two scalar laws:

- linear entropy equals total-variation execution defect;
- von Neumann entropy equals directed-KL execution defect.

#### Proof

Diagonalization in the depth basis gives

\[
\operatorname{Tr}(\rho_q^2)
=\sum_{n\ge0}(1-q)^2q^{2n}
=\frac{1-q}{1+q}.
\]

Theorem 8.2 identifies the complement with the TV defect, proving
\((\mathrm{RFDM}.38c)\). Functional calculus for the positive diagonal trace-class operator gives

\[
S_{\mathrm{vN}}(\rho_q)
=-\sum_{n\ge0}p_q(n)\log p_q(n)
=H(p_q).
\]

Theorem 3.1 identifies \(H(p_q)\) with the directed path divergence, proving
\((\mathrm{RFDM}.38d)\). ∎

This is the exact cross-organ conservation identity: positive thermal mixedness is neither an
extra analogy nor a separately fitted cost. It is exactly the information required to distinguish
fresh history production from false deterministic return.

### Corollary 8.4 -- quotient, finite lift, or infinite dilation

At every \(0<q<1\), the following reversibilization trilemma holds.

1. **Reversible quotient:** making the Toeplitz isometry unitary is incompatible with the
   positive-temperature KMS state; the existing KMS exchange theorem forces \(q=1\).
2. **Finite-order deterministic lift:** retaining fresh geometric layer reset is impossible by
   Theorem 4.1; its attempted closure has the exact defect
   \((\mathrm{RFDM}.35)\)--\((\mathrm{RFDM}.37)\).
3. **Infinite-order reversible dilation:** the bilateral construction of Theorem 6.1 realizes the
   full geometric reset process, preserves endpoint KL, and stores the missing execution in shift
   history.

Thus reversibilization has two mathematically different operations:

\[
\boxed{
\text{quotient reversibilization erases the positive state,}
\qquad
\text{dilation reversibilization retains it by creating open history}.}
\tag{RFDM.39}
\]

This prediction was not present in the KMS card. It is derived without using Toeplitz matrix
formulas beyond the already-proved layer law. It fuses three structurally different organs:

- Hasse packet recovery (probability/disintegration);
- Toeplitz KMS layers (operator-algebraic positivity and completion);
- recurrent observer/open history (invertible dynamical dilation).

The fusion is canonical at the level of depth labels, geometric ratio, and modular product
\(\beta E\). It is not yet a source-derived choice separating physical inverse temperature from
energy, nor a construction of one arithmetic operator algebra before packet formation.

## 9. Conjecture -> proof/failure loops

### Loop A -- law involution is a reversible packet map

- **Conjecture:** \(\mathsf L_*^2E=E\) comes from a Markov-kernel involution.
- **Failure:** Lemma 2.1; any Markov isomorphism is deterministic, while reset rows are non-Dirac.
- **Positive survivor:** law involution is a split/recovery phenomenon, not a path inverse.

### Loop B -- non-Dirac packets alone force open history

- **Conjecture:** correct one-time packet marginals forbid finite-order lifts.
- **Failure:** the two-coordinate swap \((\mathrm{RFDM}.17)\) is involutive and has every one-time
  marginal correct.
- **Positive survivor:** full fresh-reset finite-dimensional distributions, not marginals, force
  infinite-order history.

### Loop C -- finite observer order lifts with the same order

- **Conjecture:** an observer involution should have an involutive deterministic dilation.
- **Failure:** Theorem 4.1 and the exact diagonal/independent defect.
- **Positive survivor:** a reversible dilation exists, but its source transformation has infinite
  order and uses bilateral fresh-seed history.

### Loop D -- endpoint information neutrality means path neutrality

- **Conjecture:** KL isometry at formed endpoints removes dynamical information production.
- **Failure:** endpoint KL is unchanged while false finite-order execution has positive TV, forward
  KL \(H(p)\), and infinite reverse KL relative to reset.
- **Positive survivor:** endpoint information and execution information are independent grades.

### Loop E -- Hasse path balance proves RH

- **Conjecture:** reciprocal equality \((\mathrm{RFDM}.32)\) is already the critical-line selector.
- **Failure:** it selects packet scale \(t=1\); no source theorem identifies this equality with
  source nullhomology or a zero's real part.
- **Positive survivor:** exact non-RH fixed-point calibration and a new source gate: derive
  path-defect balance before divisor specialization.

## 10. Literature and collision boundary

Abstract dilation machinery is occupied:

- Gregoratti, [A universal dilation of discrete Markov evolutions](https://arxiv.org/abs/math/0512393),
  constructs deterministic invertible environment dilations of discrete Markov evolutions.
- Gregoratti, [Classical dilations à la Quantum Probability of Markov evolutions in discrete time](https://arxiv.org/abs/math/0702690),
  develops the classical/quantum comparison.
- Perrone, [Markov Categories and Entropy](https://arxiv.org/abs/2212.11719), identifies entropy as
  a measure of nondeterminism in enriched Markov categories.
- Dahya, [Dilations of non-Markovian dynamical systems on graphs](https://arxiv.org/abs/2508.07511),
  supplies current divisible/invertible dilation machinery for graph-indexed systems.

No claim is made that bilateral Markov dilation, entropy, collision probability, or KL divergence
is new in isolation. Exact corpus leverage is their forced coupling to:

1. the already-certified functional-equation split packet;
2. the common Hasse geometric recovery kernel;
3. the exact classification of the finite-order execution obstruction;
4. the TV/KL path defect hidden by endpoint information isometry; and
5. the reciprocal Hasse balance law.

Internal audit found many open-history theorems and the endpoint packet isometry, but no existing
diagonal-versus-refresh path theorem or Hasse defect formula.

## 11. Exact scope and next gate

Proved here:

- endpoint information isometry does not imply path reversibility;
- non-Dirac fresh reset forbids every finite-order deterministic execution;
- exact path discrepancy is collision deficit / Shannon entropy / singular reverse KL;
- a bilateral seed shift gives an invertible full reset execution;
- Hasse recovery gives closed formulas and a unique reciprocal balance point.
- Toeplitz KMS geometric layers obey the same exact path-defect law, yielding the
  quotient/finite-lift/infinite-dilation trilemma.
- Hasse adjacent-depth ratios canonically transport functional reflection to the KMS modular
  product, while leaving the temperature/energy split as an explicit clock gauge.

Not proved here:

- uniqueness or minimality of the bilateral dilation;
- a physical clock, action, or complexity;
- a source theorem imposing Hasse path-defect balance;
- a comparison to source Cartier/Bockstein nullhomology;
- RH.

Next load-bearing question:

> Does the pre-zero arithmetic source canonically compare the reciprocal reset executions so their
> path defects must balance, or does every such comparison require an externally chosen
> clock/history gauge?

Only the first outcome could move formation mechanics toward selection.

## Gates

- [x] 0 -> 1: well-posed, source connection explicit, hostile countermodel supplied
- [x] 1 -> 2: dependency-closed paper proof, exact boundary and positive survivor
- [ ] 2 -> 3: Lean formalization not attempted in this read-only Lean audit pass
- [ ] 3 -> 4: publication packaging and independent hostile audit

## Log

- 2026-08-11 -- separated formed-law involution from path execution.
- 2026-08-11 -- proved Markov-isomorphism rigidity, exact diagonal/refresh TV-KL laws, finite-order
  execution no-go, bilateral natural extension, and Hasse formulas.
- 2026-08-11 -- hostile review killed marginal-only openness and RH-selection overclaims; retained
  full-process infinite-history theorem and reciprocal balance gate.
