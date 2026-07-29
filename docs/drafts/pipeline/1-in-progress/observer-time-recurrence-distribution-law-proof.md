# Paper proof — observer-time recurrence distribution law

- **Dependency:** `observer-time-recurrence-distribution-law.md`
- **Status:** `[DEPENDENCY-CLOSED PAPER PROOF V1; SPECIALIST AUDIT OPEN]`
- **Scope:** normalized symmetric positive spectral measures on
  \(\mathbb R\), followed by pure-state and finite observer reductions

## 1. Canonical spectral split

Let \(\nu\) be a finite Borel measure on \(\mathbb R\), and set
\[
 S=\{\omega:\nu\{\omega\}>0\}.
\]
For every \(n\geq1\), the set
\[
 S_n=\{\omega:\nu\{\omega\}\geq 1/n\}
\]
is finite because its cardinality is at most \(n\nu(\mathbb R)\). Hence
\(S=\bigcup_nS_n\) is countable and Borel. Define
\[
 \nu_{\mathrm{pp}}=\nu|_S,\qquad
 \nu_{\mathrm c}=\nu|_{S^{\mathrm c}},\qquad
 b=\nu_{\mathrm{pp}}(\mathbb R).
\]
Restriction to a measurable set and its complement gives
\(\nu=\nu_{\mathrm{pp}}+\nu_{\mathrm c}\). For every \(x\), either
\(x\in S\), in which case \(\nu_{\mathrm c}\{x\}=0\), or \(x\notin S\),
in which case \(\nu\{x\}=0\). Thus \(\nu_{\mathrm c}\) is atomless.

Write
\[
 C(t)=\widehat\nu(t),\qquad
 P(t)=\widehat{\nu_{\mathrm{pp}}}(t),\qquad
 R(t)=\widehat{\nu_{\mathrm c}}(t).
\]
Then \(C=P+R\), \(|P|\leq b\), and \(|R|\leq1-b\).

## 2. The continuous remainder vanishes in time density

Wiener's theorem for finite measures on \(\mathbb R\) gives
\[
 \lim_{T\to\infty}\frac1{2T}\int_{-T}^{T}|R(t)|^2\,dt
 =\sum_x\nu_{\mathrm c}\{x\}^2=0.                 \tag{1}
\]
For every \(\delta>0\), Markov's inequality therefore yields
\[
 \lim_{T\to\infty}\frac1{2T}
   |\{t\in[-T,T]:|R(t)|\geq\delta\}|=0.           \tag{2}
\]

Let \(g\) be bounded and continuous on the closed unit disk. It is uniformly
continuous. Given \(\varepsilon>0\), choose \(\delta>0\) such that
\[
 |z-w|<\delta\Longrightarrow |g(z)-g(w)|<\varepsilon.
\]
On \(\{|R|<\delta\}\), the integrand
\(|g(C)-g(P)|\) is below \(\varepsilon\); on its complement it is at most
\(2\|g\|_\infty\). Equation (2) gives
\[
 \lim_{T\to\infty}\frac1{2T}\int_{-T}^{T}
   |g(C(t))-g(P(t))|\,dt=0.                       \tag{3}
\]
Thus every limiting continuous statistic of the full record equals that of
the atomic record.

## 3. Compact phase hull and its Haar law

Enumerate the countable atom set as \(S=\{\omega_j\}_{j\in J}\), with
weights \(q_j=\nu\{\omega_j\}>0\). Let
\[
 \Phi(t)=(e^{it\omega_j})_{j\in J}\in\mathbb T^J,
\qquad
 K=\overline{\Phi(\mathbb R)}.
\]
The product is compact; countability makes it metrizable. Since \(\Phi\) is
a continuous homomorphism, \(K\) is a compact abelian group. Define
\[
 \mathcal P(z)=\sum_{j\in J}q_jz_j .
\]
The series converges uniformly on \(\mathbb T^J\) because
\(\sum_jq_j=b<\infty\). Hence \(\mathcal P\) is continuous and
\[
 P(t)=\mathcal P(\Phi(t)).                         \tag{4}
\]

The flow \(\Phi(\mathbb R)\) is dense in \(K\) by definition. For every
nontrivial character \(\chi\) of \(K\),
\[
 \chi(\Phi(t))=e^{i\lambda_\chi t}
\]
with \(\lambda_\chi\neq0\); otherwise \(\chi\) would equal one on a dense
subgroup and hence on \(K\). Direct integration gives
\[
 \lim_{T\to\infty}\frac1{2T}\int_{-T}^{T}
   \chi(\Phi(t))\,dt=0.                            \tag{5}
\]
Finite character sums are uniformly dense in \(C(K)\) by
Stone--Weierstrass. Equation (5), uniform approximation, and the character
orthogonality formula for normalized Haar measure \(m_K\) imply
\[
 \lim_{T\to\infty}\frac1{2T}\int_{-T}^{T}
   h(\Phi(t))\,dt
 =\int_Kh\,dm_K                                   \tag{6}
\]
for every continuous \(h\) on \(K\).

Apply (6) to \(h=g\circ\mathcal P\), and combine with (3):
\[
 \lim_{T\to\infty}\frac1{2T}\int_{-T}^{T}g(C(t))\,dt
 =\int_Kg(\mathcal P(z))\,dm_K(z).                 \tag{7}
\]
This proves the complete recurrence-distribution law.

## 4. Sharp positive-density boundary

Assume now that \(\nu\) is symmetric, so \(C\) is real. Symmetry also makes
\(\mathcal P\) real on the dense orbit \(\Phi(\mathbb R)\), hence on \(K\).
At the identity \(e\in K\),
\[
 \mathcal P(e)=b,
\]
and everywhere \(\mathcal P\leq|\mathcal P|\leq b\).

Fix \(\eta<b\). By continuity, the open set
\[
 V_\eta=\{z\in K:\mathcal P(z)>\eta\}
\]
contains \(e\). Every nonempty open subset of a compact group has positive
Haar measure. Weak convergence in (7) and the Portmanteau lower bound give
\[
 \liminf_{T\to\infty}\frac1{2T}
 |\{t\in[-T,T]:C(t)>\eta\}|
 \geq m_K(V_\eta)>0.                               \tag{8}
\]

Fix instead \(\eta>b\). If \(C(t)>\eta\), then
\[
 |R(t)|\geq C(t)-|P(t)|>\eta-b.
\]
Equation (2) gives
\[
 \lim_{T\to\infty}\frac1{2T}
 |\{t\in[-T,T]:C(t)>\eta\}|=0.                     \tag{9}
\]
Equations (8)--(9) prove the sharp boundary. Taking the supremum of all
positive-lower-density thresholds gives the recurrence-tomography formula.

No universal statement is possible at \(\eta=b\). For example, when the
atomic part is a single atom, \(|P|\equiv b\), and an arbitrarily small
continuous remainder can cross the boundary with a sign pattern having
nonzero density even though it vanishes in density in magnitude.

## 5. Bounded-gap, density-arrow and escape phases

If \(\nu\) is pure point, \(C=P\) is a uniform limit of finite
trigonometric polynomials and therefore Bohr almost periodic. For every
\(\eta<1=C(0)\), sufficiently accurate almost periods \(\tau\) satisfy
\(C(\tau)>\eta\). Almost periods are relatively dense, so the return set has
bounded gaps.

Conversely, suppose every subunit return set has bounded gaps and \(b<1\).
Choose
\[
 b<\eta_1<\eta_2<1.
\]
The set \(\{C>\eta_2\}\) is relatively dense. Uniform continuity supplies one
radius \(r>0\) such that every \(r\)-neighbourhood of a point in that set
lies in \(\{C>\eta_1\}\). Selecting one return in each sufficiently separated
bounded-gap block produces disjoint intervals of length \(2r\), and hence
strictly positive lower density for \(\{C>\eta_1\}\). This contradicts
(9). Therefore \(b=1\), so \(\nu\) is pure point.

Equations (8)--(9) also show
\[
 b=0
 \quad\Longleftrightarrow\quad
 \text{every positive-threshold return set has density zero}. \tag{10}
\]
Finally,
\[
 |C(t)|\longrightarrow0
\quad\Longleftrightarrow\quad
\nu\text{ is Rajchman}                              \tag{11}
\]
is the definition of a Rajchman measure. This is exactly permanent escape
below every fixed positive absolute-return threshold. Absolute continuity is
sufficient by the Riemann--Lebesgue lemma but not necessary.

## 6. Finite observer dimension is the density exponent

Assume the atomic support is finite and its nonzero frequency group has
rational rank \(d>0\). The identity component of \(K\) is a \(d\)-torus,
possibly accompanied by finitely many components. Choose local angular
coordinates \(y\in\mathbb R^d\) at the identity. Every atomic character has
the form
\[
 z_j(y)=e^{i m_j\cdot y},\qquad m_j\in\mathbb Z^d,
\]
and the vectors \(m_j\) span \(\mathbb R^d\). Symmetry gives
\[
 b-\mathcal P(y)
 =\sum_jq_j\bigl(1-\cos(m_j\cdot y)\bigr).          \tag{12}
\]
The quadratic form
\[
 Q(y)=\frac12\sum_jq_j(m_j\cdot y)^2                \tag{13}
\]
is positive definite because the \(m_j\) span. Taylor's theorem and compactness
therefore give constants \(c,C,\varepsilon_0>0\) such that, throughout the
small target,
\[
 c\|y\|^2\leq b-\mathcal P(y)\leq C\|y\|^2.         \tag{14}
\]
Away from a sufficiently small identity neighbourhood the deficit has a
positive minimum. Normalized Haar measure is a constant multiple of
Lebesgue measure in the local chart, so (14) sandwiches the target between
two \(d\)-balls of radii proportional to \(\sqrt\varepsilon\):
\[
 c_1\varepsilon^{d/2}
 \leq
 m_K\{\mathcal P>b-\varepsilon\}
 \leq
 c_2\varepsilon^{d/2}.                              \tag{15}
\]
The nonconstant real-analytic function
\(\mathcal P-(b-\varepsilon)\) has a Haar-null zero set. Equation (7)
therefore makes the time density exist and equal the Haar target volume.
Taking logarithms in (15) proves
\[
 \lim_{\varepsilon\downarrow0}
 \frac{\log\operatorname{dens}
   \{t:C(t)>b-\varepsilon\}}
      {\log\varepsilon}
 =\frac d2.                                         \tag{16}
\]

For a finite coherence graph, \(d\) is the rational rank of its visible
energy gaps. The independent phase capacity is \(|V|-c(G)\); the physical
time orbit may explore a lower-dimensional subtorus. This is the exact
capacity-versus-exploration split.

## 7. Pure-state gap law

Let \(\mu\) be the energy probability measure of a unit vector, let
\(\widetilde\mu(B)=\mu(-B)\), and define
\[
 \Delta\mu=\mu*\widetilde\mu.
\]
Characteristic functions turn convolution into multiplication:
\[
 \widehat{\Delta\mu}(t)
 =\widehat\mu(t)\overline{\widehat\mu(t)}
 =|\widehat\mu(t)|^2.                               \tag{17}
\]

Write \(\mu=\mu_{\mathrm{pp}}+\mu_{\mathrm c}\) and
\(a=\mu_{\mathrm{pp}}(\mathbb R)\). Expanding the convolution gives four
terms. The atomic--atomic term is pure point and has total mass \(a^2\).
Convolution with an atomless measure is atomless, because for every \(x\)
\[
 (\sigma*\tau)\{x\}
 =\int \sigma\{x-y\}\,d\tau(y)=0
\]
whenever \(\sigma\) is atomless. Hence the other three terms are atomless.
Therefore
\[
 (\Delta\mu)_{\mathrm{pp}}(\mathbb R)=a^2.          \tag{18}
\]
Applying Sections 3--5 to \(\Delta\mu\) proves the pure-state fidelity law,
including the exact threshold \(a^2\).

## 8. Mixed states and observer families

Let
\[
 H=\sum_vE_vP_v
\]
on a finite Hilbert space and let \(\rho\neq0\) be positive. Orthogonality of
spectral blocks in Hilbert--Schmidt inner product gives
\[
 \operatorname{Tr}(\rho^2)
 =\sum_{u,v}\|P_u\rho P_v\|_{\mathrm{HS}}^2.         \tag{19}
\]
Define the probability gap measure
\[
 \nu_\rho
 =\frac1{\operatorname{Tr}(\rho^2)}
   \sum_{u,v}\|P_u\rho P_v\|_{\mathrm{HS}}^2
      \delta_{E_u-E_v}.                              \tag{20}
\]
It is symmetric because the \((u,v)\) and \((v,u)\) block norms agree.
Expanding the evolved blocks yields
\[
 \widehat{\nu_\rho}(t)
 =\frac{\operatorname{Tr}(\rho\,e^{-itH}\rho e^{itH})}
        {\operatorname{Tr}(\rho^2)}.                 \tag{21}
\]
The numerator is nonnegative because it is the trace of the product of two
positive operators.

For a finite nonnegatively weighted reporter family, take the direct sum of
the corresponding Hilbert--Schmidt spaces and repeat (19)--(21). The
resulting weights are exactly the observer-union coherence-block weights.
The support graph therefore has phase capacity \(|V|-c(G)\), while the orbit
hull has dimension equal to the rational rank of the supported gaps.

Existing block orthogonality, graph recurrence, graph sharpness, operational
norm conversion, local-spin transfer and device-window theorems supply the
finite implementation. Existing summable pure-point block identities supply
the countably infinite discrete sector.

## 9. Lossy finite sector

For a finite Hilbert contraction, the peripheral projection of the initial
state has squared norm \(p\). Existing contraction theorems prove that every
late overlap threshold below \(p\) recurs and every threshold above \(p\)
eventually fails. Restricting the dynamics to the peripheral unitary sector
produces its stationary visible-gap measure. Sections 3--8 determine the
frequency and dimension of the surviving returns.

Thus loss ceiling and recurrence geometry are sequential invariants of one
record:
\[
 \text{loss fixes how much can return};
 \qquad
 \text{visible-gap geometry fixes how it returns}.

## 10. Claims not proved by this theorem

The theorem does not determine the spectral measure of a particular black
hole, de Sitter patch, quantum field or laboratory device. It does not turn a
finite-entropy gravitational algebra into a finite matrix algebra. It does
not identify observer temporal dimension with spacetime dimension. It does
not give a system-independent convergence rate in the presence of an
arbitrary continuous spectral component.
