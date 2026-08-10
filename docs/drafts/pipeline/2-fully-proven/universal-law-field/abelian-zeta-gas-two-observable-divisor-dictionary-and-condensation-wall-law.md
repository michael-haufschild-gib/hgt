# Abelian zeta gas, two-observable divisor dictionary, and condensation-wall law

- **ID:** ULF-GAS-1
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) / PRD-E ARITHMETIC SOURCE TEST
- **Source:** structural audit of ULF-EQG-1 against the PRD charter gates
- **Statement:** The Euler q-Gamma source of ULF-EQG-1 is the zeta-Gibbs measure
  \(\mathbb P_\sigma(A)=C_\sigma|A|^{-\sigma}\) on finite abelian groups, equivalently the unique
  KMS\(_\sigma\) state of one free prime-power Toeplitz gas; its two canonical integers — the order
  \(|A|\) and the socle order \(|\operatorname{soc}A|\) — carry two nonisomorphic complete
  zeta-divisor calculi (dilation and translation), its walls \(\sigma=1/g\) are exact
  depth-\(g\) condensation transitions with the critical abscissa \(\tfrac12\) as the squarefull
  wall, the depth-dilation semigroup is an exact renormalization action, and the symmetrized
  information cost of the canonical tilt equals the von Mangoldt mass
  \(\sigma\sum_n\Lambda(n)n^{-\sigma}\).
- **Status:** [PAPER-PROVED] [DEPENDENCY-CLOSED] [PRE-ZERO SOURCE] [THREE OBSERVER ORGANS]
  [WITHHELD SECOND-ORGAN RESPONSE] [KMS-UNIQUE FOR ALL POSITIVE TEMPERATURE]
  [CLASSICAL COMPONENT PARENTS DISCLAIMED] [NOT RH] [THEOREM 2.1 LEAN CERTIFIED]

## 1. Source, modes, and the depth fan

Let \(\mathbb M=\{(p,j):p\text{ prime},\ j\ge1\}\) be the set of nontrivial cyclic prime-power
groups \(\mathbb Z/p^j\). A **configuration** is a finitely supported
\(g:\mathbb M\to\mathbb N\); by the structure theorem for finite abelian groups, configurations
biject with isomorphism classes via

\[
A(g)=\bigoplus_{(p,j)}(\mathbb Z/p^j)^{g(p,j)} .
\tag{GAS.1}
\]

Fix two real parameters and give mode \((p,j)\) the geometric occupation ratio

\[
\tilde q_{p,j}=p^{-j\sigma-\tau}\in(0,1)
\qquad(\sigma>0,\ \tau\ge0).
\tag{GAS.2}
\]

The **depth fan** is the arrangement of lines \(\{j\sigma+\tau=c\}\) in the \((\sigma,\tau)\)
parameter plane. The same fan will reappear below as the wall arrangement, as the divisor-line
arrangement of the grand response, and as the orbit structure of the renormalization action. The
two observables of the title are

\[
|A|=\prod_{(p,j)}p^{\,j\,g(p,j)},
\qquad
|\operatorname{soc}A|=\prod_p p^{\,N_p},
\quad
N_p=\sum_j g(p,j),
\tag{GAS.3}
\]

the second because the socle \(\operatorname{soc}A=\bigoplus_pA[p]\) has
\(|A[p]|=p^{\#\{\text{cyclic }p\text{-factors}\}}\).

## 2. The zeta measure on finite abelian groups

Let \((G_{p,j})\) be independent with \(\mathbb P(G_{p,j}=n)=(1-\tilde q_{p,j})\tilde q_{p,j}^{\,n}\).

### Theorem 2.1 — zeta-Gibbs law and Erdős–Szekeres normalization

If \(\sigma+\tau>1\), then almost surely only finitely many \(G_{p,j}\) are nonzero, so
\(A=A(G)\) is a finite abelian group, and

\[
\boxed{
\mathbb P_{\sigma,\tau}(A)
=C_{\sigma,\tau}\,|A|^{-\sigma}\,|\operatorname{soc}A|^{-\tau},
\qquad
C_{\sigma,\tau}^{-1}
=Z(\sigma,\tau)
=\prod_{j\ge1}\zeta(j\sigma+\tau).}
\tag{GAS.4}
\]

For \(\tau=0\) this is \(\mathbb P_\sigma(A)=C_\sigma|A|^{-\sigma}\) with
\(Z(\sigma,0)=\prod_{j\ge1}\zeta(j\sigma)=\sum_{n\ge1}a(n)n^{-\sigma}\), where \(a(n)\) is the
number of abelian groups of order \(n\) (Erdős–Szekeres).

#### Proof

\(\sum_{(p,j)}\tilde q_{p,j}=\sum_{j\ge1}\sum_p p^{-j\sigma-\tau}\le\sum_{j\ge1}P(j\sigma+\tau)\),
where \(P\) is the prime zeta function; each term is finite because \(j\sigma+\tau\ge\sigma+\tau>1\),
and the terms decay geometrically in \(j\), so the sum converges. Borel–Cantelli I gives finite
activity. The product mass of a configuration is

\[
\prod_{(p,j)}(1-\tilde q_{p,j})\tilde q_{p,j}^{\,g(p,j)}
=C_{\sigma,\tau}\prod_{(p,j)}\bigl(p^{-j\sigma-\tau}\bigr)^{g(p,j)}
=C_{\sigma,\tau}\,|A|^{-\sigma}|\operatorname{soc}A|^{-\tau},
\]

using (GAS.3). The constant rearranges by absolute convergence of
\(\sum_{(p,j)}|\log(1-p^{-j\sigma-\tau})|\le2\sum p^{-j\sigma-\tau}<\infty\):

\[
C_{\sigma,\tau}
=\prod_{j\ge1}\prod_p(1-p^{-j\sigma-\tau})
=\prod_{j\ge1}\zeta(j\sigma+\tau)^{-1}.
\]

Total mass one then re-proves \(\sum_A|A|^{-\sigma}|\operatorname{soc}A|^{-\tau}=Z(\sigma,\tau)\);
at \(\tau=0\), grouping by \(|A|=n\) gives the Erdős–Szekeres identity. QED.

## 3. Socle bridge: ULF-EQG-1 is the socle observer of this gas

### Theorem 3.1 — Euler's identity is the mode bridge

Under \(\mathbb P_{\sigma,0}\), the variables \(N_p=\sum_jG_{p,j}\) are independent with

\[
\mathbb P(N_p=n)=w_{q_p,n}
=(q_p;q_p)_\infty\frac{q_p^{\,n}}{(q_p;q_p)_n},
\qquad q_p=p^{-\sigma}.
\tag{GAS.5}
\]

Hence \(M:=|\operatorname{soc}A|=\prod_pp^{N_p}\) has exactly the law (EQG.4)–(EQG.6) of
ULF-EQG-1, and the entire global structure of that card — the random-integer law, the q-Gamma
response, the translation equation, and the Cartier-divisor landing — is the socle-observer shadow
of the abelian zeta gas.

#### Proof

Independence across \(p\) is clear. Fix \(p\), write \(q=q_p\). The probability generating
function of \(N_p\) is

\[
\prod_{j\ge1}\frac{1-q^j}{1-uq^j}
=\frac{(q;q)_\infty}{(uq;q)_\infty}.
\]

Euler's \(q\)-binomial identity
\(\sum_{n\ge0}u^nq^n/(q;q)_n=1/(uq;q)_\infty\) for \(|u|<1/q\) gives

\[
\sum_{n\ge0}w_{q,n}u^n=\frac{(q;q)_\infty}{(uq;q)_\infty},
\]

the same analytic function on \(|u|<1\). Equality of generating functions of nonnegative laws
forces (GAS.5). QED.

The corpus's local Euler weights are therefore not primitive: they are the shadow of independent
geometric prime-power modes, and the \(q\)-binomial theorem is precisely the change of observer.

### Corollary 3.2 — depth-ladder responses and one-line translation law

On the exact absolute-convergence chamber

\[
\operatorname{Re}(\sigma+u)>0,
\qquad
\operatorname{Re}(\sigma+u+v)>1,
\]

with normal convergence,

\[
\boxed{
\mathfrak F_\sigma(u,v)
:=\mathbb E_\sigma\!\left[|A|^{-u}\,|\operatorname{soc}A|^{-v}\right]
=\frac{Z(\sigma+u,\;v)}{Z(\sigma,\;0)}
=\prod_{j\ge1}\frac{\zeta\bigl(j(\sigma+u)+v\bigr)}{\zeta(j\sigma)} .}
\tag{GAS.6}
\]

In particular the socle axis telescopes:

\[
\frac{\mathfrak F_\sigma(0,v+\sigma)}{\mathfrak F_\sigma(0,v)}
=\prod_{j\ge1}\frac{\zeta((j+1)\sigma+v)}{\zeta(j\sigma+v)}
=\frac1{\zeta(\sigma+v)},
\tag{GAS.7}
\]

which is (EQG.13) after the substitution \(v=\sigma s\) and multiplication by the elementary factor
\(\zeta(\sigma)^s\).

#### Proof

Per mode, \(\mathbb E[x^{G_{p,j}}]=(1-q)/(1-xq)\) with \(q=p^{-j\sigma}\) and
\(x=p^{-ju-v}\). Put \(a=\operatorname{Re}(\sigma+u)\). The two chamber inequalities say
\(a>0\) and \(a+\operatorname{Re}v>1\), hence

\[
\operatorname{Re}\bigl(j(\sigma+u)+v\bigr)
=(a+\operatorname{Re}v)+(j-1)a>1
\qquad(j\ge1).
\]

Thus every local geometric moment exists and
\(\sum_{(p,j)}|{\textstyle\frac{1-q}{1-xq}}-1|\) converges normally on compact subsets.
Conversely, failure of either chamber inequality makes the depth exponents fail to stay in the
prime-Euler absolute-convergence half-plane: at depth one if
\(\operatorname{Re}(\sigma+u+v)\le1\), and at large depth if
\(\operatorname{Re}(\sigma+u)\le0\). This proves exactness of the chamber.
Multiplying over modes and rearranging as in Theorem 2.1 gives (GAS.6). Equation (GAS.7) is
literal telescoping of the depth ladder: shifting \(v\) by \(\sigma\) moves depth \(j\) to depth
\(j+1\). QED.

The corpus's translation-divisor law is thus the telescoping of the depth fan, and its
normalized tilt \((\)EQG.15\()\) is the \(\tau\)-shift \(\tau\mapsto\tau+\sigma\) inside the
exactly solvable family (GAS.4); the tilted state is
\(\mathbb P_{\sigma,\sigma}\), which lies outside the one-parameter family
\(\{\mathbb P_{\sigma'}\}\): the socle tilt is transverse to the temperature axis.

## 4. KMS realization: unique equilibrium at every positive temperature

Let \(\mathfrak A=\bigotimes_{(p,j)\in\mathbb M}\mathcal T\) be the C\(^*\)-inductive limit of
finite minimal tensor products of Toeplitz algebras (\(\mathcal T\) is nuclear, so the tensor
product is unambiguous), with generators \(V_{p,j}\), and gauge dynamics

\[
\alpha_t(V_{p,j})=e^{\,it\,j\log p}\,V_{p,j};
\tag{GAS.8}
\]

the mode energy is \(\varepsilon_{p,j}=j\log p=\log|\mathbb Z/p^j|\), so the second-quantized
Hamiltonian is \(H=\log|A|\): **energy is the logarithm of the order**.

### Theorem 4.1 — existence and uniqueness

For every \(\sigma>0\) there is exactly one KMS\(_\sigma\) state \(\varphi_\sigma\) on
\((\mathfrak A,\alpha)\). It is the product over modes of the geometric states with weights
\((1-q)q^n\), \(q=p^{-j\sigma}\), and its restriction to the diagonal masa is the mode-occupation
law of Section 2 (at \(\tau=0\)).

#### Proof

**Existence.** Each factor carries the state \(\varphi^{(p,j)}\) of ULF-IPKMS-1 §3 with
\(E=j\log p\), which is KMS\(_\sigma\) for its gauge flow. On the dense union of finite tensor
products, the product state is well defined, and the KMS identity for elementary tensors of
analytic elements factorizes into the per-mode identities. Continuity extends both the state and
the KMS identity to \(\mathfrak A\).

**Uniqueness.** Let \(\varphi\) be any KMS\(_\sigma\) state. The linear span of finite elementary
tensors of monomials \(V^m(V^*)^n\) is dense in \(\mathfrak A\) (in \(\mathcal T\), the span of
\(V^m(V^*)^n\) contains \(e_{jk}=V^j(1-VV^*)V^{*k}\), hence all compacts, and is classically dense).
So it suffices to compute \(\varphi\) on a monomial
\(a=\prod_{i\in F}V_i^{m_i}(V_i^*)^{n_i}\) with \(F\subset\mathbb M\) finite.

*Step 1: nonzero total energy.* Each monomial is an eigenvector:
\(\alpha_t(a)=e^{itE(a)}a\) with \(E(a)=\sum_i(m_i-n_i)\varepsilon_i\). The KMS identity with
\(b=1\) gives \(\varphi(a)=\varphi(\alpha_{i\sigma}(a))=e^{-\sigma E(a)}\varphi(a)\), so
\(\varphi(a)=0\) whenever \(E(a)\ne0\).

*Step 2: resonant off-diagonal monomials.* Suppose \(E(a)=0\) but \(k_{i_0}:=m_{i_0}-n_{i_0}\ne0\)
for some \(i_0\); after replacing \(a\) by \(a^*\) if necessary, \(k_{i_0}\ge1\). Apply the KMS
identity with \(c=V_{i_0}\), \(d\) the remaining product: since
\(\alpha_{i\sigma}(V_{i_0})=q_{i_0}V_{i_0}\) with \(q_{i_0}=p^{-j\sigma}\in(0,1)\),

\[
\varphi(V_{i_0}\,d)=q_{i_0}\,\varphi(d\,V_{i_0}),
\]

and inside factor \(i_0\) one contraction \((V^*)^nV=(V^*)^{n-1}\) shortens the word while
preserving \(k_{i_0}\). Iterating \(n_{i_0}\) times reduces to a monomial whose \(i_0\)-part is the
pure power \(V_{i_0}^{k_{i_0}}\), which commutes with every other factor. One further application
with \(c=V_{i_0}^{k_{i_0}}\), \(d\) the rest, gives

\[
\varphi(cd)=q_{i_0}^{k_{i_0}}\varphi(dc)=q_{i_0}^{k_{i_0}}\varphi(cd),
\]

hence \(\varphi(a)=0\) because \(0<q_{i_0}^{k_{i_0}}<1\).

*Step 3: diagonal monomials.* If \(k_i=0\) for all \(i\), then
\(a=\prod_iV_i^{n_i}V_i^{*n_i}\). Splitting off \(c=V_{i_0}^{n_{i_0}}\) and using commutation of
distinct factors,

\[
\varphi\Bigl(V_{i_0}^{n_{i_0}}V_{i_0}^{*n_{i_0}}R\Bigr)
=q_{i_0}^{\,n_{i_0}}\varphi\bigl(V_{i_0}^{*n_{i_0}}V_{i_0}^{n_{i_0}}R\bigr)
=q_{i_0}^{\,n_{i_0}}\varphi(R),
\]

since \(V^*V=1\). Induction over \(|F|\) forces
\(\varphi(a)=\prod_iq_i^{\,n_i}\), the product-state value. QED.

### Corollary 4.2 — two kinds of arithmetic phase transition

The abelian zeta gas has **no KMS-simplex transition**: the equilibrium state is unique at every
\(\sigma>0\). All its arithmetic walls (Section 5) are transitions in the *realization of
observables* under the unique state — condensation of activity sectors — not in the multiplicity
of equilibria. This is the exact structural opposite of the Bost–Connes system, whose wall at
\(\beta=1\) is a transition in the extremal KMS simplex driven by the Hecke/Galois symmetry that
this gas does not carry. The polarized-realization dictionary is: symmetry-rich sources store
their walls in state multiplicity; the bare directed source stores them in observable
condensation.

Under the unique state, positivity is the KMS state on the directed Toeplitz history, phase is the
gauge flow, and their pairing is the KMS boundary condition itself — a derived pairing, exactly as
PRD-B requires, not an additive weight (which the certified polarization theorem forbids).

## 5. Condensation stratification: the walls are the depth fan

Call mode \((p,j)\) **active** when \(G_{p,j}>0\), and let depth-\(g\) refer to modes with
\(j\ge g\). Work at \(\tau=0\); the statement for general \(\tau\) shifts the fan by \(\tau\).

### Theorem 5.1 — sharp depth-\(g\) condensation walls

Fix \(g\ge1\).

1. If \(\sigma>1/g\), then almost surely only finitely many modes of depth \(\ge g\) are active.
2. If \(0<\sigma\le1/g\), then almost surely infinitely many modes of depth exactly \(g\) are
   active.

Consequently: the finite-integer wall of ULF-EQG-1 (\(\sigma=1\)) is the depth-one condensation
wall, and its divergence half — asserted without proof in that card's failure loop 2 — holds;
the **squarefull sector** (groups with no cyclic factor of prime order) remains an honest
almost-surely-finite random abelian group for all \(\sigma>\tfrac12\), with law
\(\propto|B|^{-\sigma}\) on that sector and partition function \(\prod_{j\ge2}\zeta(j\sigma)\); and
the genus-\(g\) renormalization chamber \(\sigma>1/(g+1)\) of ULF-EQG-1 §9 is exactly the
non-condensation chamber of depth \(g+1\).

#### Proof

The events \(\{G_{p,j}>0\}\) are independent with probabilities \(\tilde q_{p,j}=p^{-j\sigma}\).
For (1): \(\sum_{j\ge g}\sum_pp^{-j\sigma}=\sum_{j\ge g}P(j\sigma)\) converges because
\(j\sigma>1\) for all \(j\ge g\) and the terms decay geometrically; Borel–Cantelli I applies.
For (2): already the depth-exactly-\(g\) slice gives
\(\sum_pp^{-g\sigma}\ge\sum_pp^{-1}=\infty\), and the events are independent, so Borel–Cantelli II
gives infinitely many active modes almost surely. QED.

Thus the critical abscissa \(\tfrac12\) enters the field **as the condensation threshold of the
squarefull stratum of a pre-zero source**, not through the zeros of \(\zeta\): below
\(\sigma=1\) the divisor-carrying depth-one stratum has already condensed, while the unit-carrying
strata survive chamber by chamber down the fan \(\{1/g\}\), which accumulates at the natural
boundary \(\sigma=0\).

## 6. Two-observable divisor dictionary

### Theorem 6.1 — grand response, two calculi, line-arrangement divisor

The function \(\mathfrak F_\sigma(u,v)\) of (GAS.6) continues meromorphically to
\(\{\operatorname{Re}(\sigma+u)>0\}\times\mathbb C\), and:

1. **Dilation (temperature) organ.** \(u\mapsto\mathfrak F_\sigma(u,0)=Z(\sigma+u)/Z(\sigma)\)
   is the response to the temperature deformation \(\sigma\mapsto\sigma+u\). Its divisor at
   \(u_0\) is the finite sum

   \[
   \operatorname{ord}_{u_0}
   =\sum_{j\ge1}\operatorname{ord}_{\,j(\sigma+u_0)}\zeta ,
   \tag{GAS.9}
   \]

   with \(\operatorname{ord}_1\zeta=-1\); every nontrivial zero \(\rho\) lands at every depth as
   \(u=\rho/j-\sigma\), every pole at \(u=1/j-\sigma\), and both families accumulate only at
   \(\operatorname{Re}u=-\sigma\), which is a natural boundary.

2. **Translation (fugacity) organ.** \(v\mapsto\mathfrak F_\sigma(0,v)\) is the response to the
   socle-fugacity deformation \(\tau\mapsto\tau+v\); it telescopes by (GAS.7), reproducing the
   translation-divisor law and clean landing (EQG.16)–(EQG.18) of ULF-EQG-1.

3. **Joint divisor is a line arrangement.** In \((u,v)\in\mathbb C^2\) the singular set of
   \(\mathfrak F_\sigma\) is carried by the affine lines

   \[
   \ell_{j,w}:\quad j\,u+v=w-j\sigma,
   \qquad j\ge1,\ w\in\{1\}\cup\{\text{zeros of }\zeta\},
   \tag{GAS.10}
   \]

   with depth \(j\) as slope. The Riemann hypothesis is the statement that the intercepts of the
   zero-lines have real part \(j(\tfrac12/j - \sigma)\)… i.e., that all zero-lines meet the real
   \((u,v)\)-plane in the single translated fan
   \(\{ju+v=\tfrac12-j\sigma\}\); no such localization is proved or claimed here.

#### Proof

For \(u\) in a compact subset of \(\operatorname{Re}(\sigma+u)>0\) and \(v\) in a compact subset of
\(\mathbb C\), all but finitely many \(j\) put \(j(\sigma+u)+v\) in a fixed half-plane
\(\operatorname{Re}>2\), where \(\log\zeta\) is bounded by \(2^{1-\operatorname{Re}}\) up to a
constant; the tail therefore converges normally to a nonvanishing holomorphic function, and the
finitely many remaining factors are meromorphic. This proves the continuation and (GAS.9), since
affine pullback preserves local order and the sum is finite on any compact. The accumulation claim:
poles \(1/j-\sigma\to-\sigma\); zero-copies \(\rho/j-\sigma\) have real parts in
\((-\sigma,-\sigma+1/j)\to-\sigma\), and by the Riemann–von Mangoldt count the ordinates
\(\gamma/j\) are dense in \(\mathbb R\), so every point of \(\operatorname{Re}u=-\sigma\) is a
limit of singularities; distinct sources contribute nonnegative zero-orders and the isolated poles
\(1/j-\sigma\) (a zero \(\rho/j=1/j'\) would force \(\rho\) real, which is false), so no
cancellation occurs and the line is a natural boundary. Item 2 is Corollary 3.2 plus ULF-EQG-1 §6.
Item 3 is (GAS.6) read as a function of \((u,v)\). QED.

The two single-variable organs are genuinely nonisomorphic as divisor calculi: the translation
organ's singular set is a discrete union of translated copies of \(\operatorname{div}\zeta\) with
no finite accumulation, while the dilation organ's singular set accumulates on a natural boundary
at finite distance. One source, two inequivalent meromorphic observers.

## 7. Renormalization self-similarity: the source acts on itself

### Theorem 7.1 — depth dilation is an exact RG semigroup

For \(d\ge1\) let \(\delta_d:\mathbb M\to\mathbb M\), \((p,j)\mapsto(p,dj)\). The induced unital
\(*\)-embedding \(\iota_d:\mathfrak A\to\mathfrak A\) onto the depth-\(d\mathbb N\) tensor
subfactor satisfies

\[
\iota_d\circ\iota_e=\iota_{de},
\qquad
\alpha_t\circ\iota_d=\iota_d\circ\alpha_{dt},
\qquad
\varphi_\sigma\circ\iota_d=\varphi_{d\sigma}.
\tag{GAS.11}
\]

Hence \(Z\) restricted to depth-\(d\mathbb N\) modes at temperature \(1/\sigma\) equals
\(Z\) at temperature \(1/(d\sigma)\); the wall ladder \(\{1/g\}\) of Theorem 5.1 is the
\(\delta\)-orbit of the depth-one wall \(\sigma=1\); and the dilation organ of Theorem 6.1 is the
observer of the RG orbit.

#### Proof

\(\delta_d\) is injective with image the depth-multiples-of-\(d\) modes, and multiplies each mode
energy by \(d\): \(\varepsilon_{p,dj}=d\,\varepsilon_{p,j}\). The first relation is
\(\delta_d\circ\delta_e=\delta_{de}\). The second is the energy rescaling read through (GAS.8).
For the third, the per-mode state pulled back along \(\iota_d\) has ratio
\(p^{-(dj)\sigma}=p^{-j(d\sigma)}\), which is the \((p,j)\)-ratio of \(\varphi_{d\sigma}\); product
states match factorwise. QED.

The renormalization semigroup is \((\mathbb N_{\ge1},\times)\) — the same directed monoid that
generates the source. The arithmetic gas is renormalized by its own history monoid.

## 8. Information cost of the canonical tilt

### Theorem 8.1 — entropy equals von Mangoldt mass

Fix \(\sigma>1\) and let \(\mathbb P^*=\mathbb P_{\sigma,\sigma}\) be the canonical unit tilt of
ULF-EQG-1 (density \(\zeta(\sigma)|\operatorname{soc}A|^{-\sigma}\)). Then both relative entropies
are finite and

\[
\boxed{
D(\mathbb P^*\Vert\mathbb P_\sigma)+D(\mathbb P_\sigma\Vert\mathbb P^*)
=\sigma\!\left(-\frac{\zeta'}{\zeta}\right)\!(\sigma)
=\sigma\sum_{n\ge2}\Lambda(n)\,n^{-\sigma}.}
\tag{GAS.12}
\]

Moreover the two observables have the exact depth-ladder means

\[
\mathbb E_\sigma\bigl[\log|\operatorname{soc}A|\bigr]
=\sum_{j\ge1}\left(-\frac{\zeta'}{\zeta}\right)\!(j\sigma),
\qquad
\mathbb E_\sigma\bigl[\log|A|\bigr]
=\sum_{j\ge1}j\left(-\frac{\zeta'}{\zeta}\right)\!(j\sigma),
\tag{GAS.13}
\]

and for the temperature deformation \(u>0\),

\[
D(\mathbb P_{\sigma+u}\Vert\mathbb P_\sigma)+D(\mathbb P_\sigma\Vert\mathbb P_{\sigma+u})
=u\sum_{j\ge1}j\left[\left(-\frac{\zeta'}{\zeta}\right)\!(j\sigma)
-\left(-\frac{\zeta'}{\zeta}\right)\!(j(\sigma+u))\right]\;\ge0.
\tag{GAS.14}
\]

#### Proof

The tilt density is \(e^{X}\) with \(X=\log\zeta(\sigma)-\sigma\log|\operatorname{soc}A|\), so

\[
D(\mathbb P^*\Vert\mathbb P)+D(\mathbb P\Vert\mathbb P^*)
=\mathbb E^*[X]-\mathbb E[X]
=\sigma\bigl(\mathbb E[\log M]-\mathbb E^*[\log M]\bigr),
\qquad M=|\operatorname{soc}A|.
\]

Under \(\mathbb P_{\sigma,\tau}\), independence and the geometric mean
\(\mathbb E[G_{p,j}]=\tilde q/(1-\tilde q)=\sum_{r\ge1}p^{-r(j\sigma+\tau)}\) give

\[
\mathbb E_{\sigma,\tau}[\log M]
=\sum_p\log p\sum_{j\ge1}\sum_{r\ge1}p^{-r(j\sigma+\tau)}
=\sum_{j\ge1}\left(-\frac{\zeta'}{\zeta}\right)(j\sigma+\tau),
\]

since \((-\zeta'/\zeta)(w)=\sum_p\sum_r\log p\,p^{-rw}\); all sums converge absolutely because
every argument exceeds \(1\). At \(\tau=0\) and \(\tau=\sigma\) the two ladders differ by exactly
the \(j=1\) term, which proves (GAS.12); finiteness of each entropy separately follows from the
finiteness of \(\mathbb E[|X|]\) and \(\mathbb E^*[|X|]\), both dominated by the convergent ladders.
The first half of (GAS.13) is the case \(\tau=0\); the second half is the same computation with the
extra weight \(j\) from \(\log|A|=\sum j\,G_{p,j}\log p\). For (GAS.14),
\(\log(d\mathbb P_{\sigma+u}/d\mathbb P_\sigma)=\log(Z(\sigma)/Z(\sigma+u))-u\log|A|\), so the
symmetrized entropy telescopes to
\(u(\mathbb E_\sigma-\mathbb E_{\sigma+u})[\log|A|]\), and monotonicity of each ladder term in the
argument gives nonnegativity. QED.

The symmetrized information cost of the corpus's canonical tilt is exactly the depth-one
(prime-layer) energy density — the same layer that carries the divisor (ULF-EQG-1 §9.2) and the
same layer whose condensation forms the \(\sigma=1\) wall. Divisor carrier, entropy carrier, and
first condensation stratum coincide.

## 9. PRD-E gate assessment

The PRD charter demanded: one pre-zero arithmetic process, at least three nonisomorphic observer
localizations, one shared unitization class, and a withheld consequence.

- **One source:** the mode gas (GAS.1)–(GAS.4); pre-zero (no zero of \(\zeta\) enters any
  construction; zeros appear only in forced responses).
- **Three organs:** (O1) the positive/probability organ (zeta-Gibbs measure, Theorem 2.1); (O2)
  the modular/phase organ (unique KMS state and gauge flow, Theorem 4.1; recurrence with open lift
  by ULF-EQG-1 §8); (O3) the meromorphic organ, which is itself doubled into two nonisomorphic
  divisor calculi (Theorem 6.1). O1 is commutative-probabilistic, O2 is operator-dynamical, O3 is
  function-theoretic; no pair is isomorphic as an observer structure.
- **Shared class:** the canonical tilt — the \(\tau\)-shift by \(\sigma\) — is one source history
  class whose three shadows are: a normalized probability intervention (O1, EQG.15), the KMS
  boundary/cocycle datum with information cost (GAS.12) (O2), and the translation-divisor
  transgression (O3, EQG.16).
- **Withheld response:** given only what ULF-EQG-1 recorded (O1 + the translation half of O3),
  the mode identification predicts the entire second meromorphic organ — the dilation ladder
  \(Z(\sigma+u)/Z(\sigma)\), its Erdős–Szekeres coefficients, its pole set \(\{1/j-\sigma\}\), and
  its natural boundary — before that observer is consulted; the classical literature then confirms
  the prediction independently (Erdős–Szekeres; Kendall; Ivić; Estermann-type natural boundaries).
  Component novelty is disclaimed; the point is that the source forces the organ.

The gate is passed at paper level. It remains open at Lean level, and the gate's spirit — a
withheld consequence in a *fourth, non-classical* organ — is a standing demand; see §10.

## 10. Conjecture, attack, and failure loops

1. **The gas should have a Bost–Connes-type KMS transition at \(\sigma=1\).** False — Theorem 4.1
   proves uniqueness at every \(\sigma>0\). The wall at \(\sigma=1\) is observable condensation,
   not equilibrium multiplicity. Positive survivor: Corollary 4.2's dichotomy of arithmetic wall
   types.
2. **Per-depth clean landing should hold for the dilation organ as it does for translation
   (EQG.18).** Not provable unconditionally: the order formula (GAS.9) at \(u=\rho/j-\sigma\)
   involves \(\zeta(j'\rho/j)\) at other depths, and no unconditional result forbids, e.g.,
   \(\rho\) and \(2\rho\) both being zeros. The translation organ's clean landing survives because
   its ladder moves *right* into the zero-free half-plane; the dilation ladder moves *both ways*.
   Exact asymmetry between the two calculi; recorded as a structural difference, not a defect.
3. **The socle tilt should be a temperature shift.** False: \(\mathbb P_{\sigma,\sigma}\) is not
   \(\mathbb P_{\sigma'}\) for any \(\sigma'\). The two deformation axes are transverse; this is
   what makes the grand response two-dimensional and its divisor a line arrangement rather than a
   curve family.
4. **Condensation at \(\sigma=1/2\) should yield horizontal information about zeros.** Not
   established, and three corpus no-gos (reciprocity character-blindness; density envelopes;
   modulus-first cap) warn that activity/size observables alone are divisor-blind. The wall is a
   wall of the *source*; nothing here localizes \(\operatorname{Re}\rho\). Any claim that the
   depth fan "sees" the critical line is, at this stage, theatre and is not made.
5. **The positivity locus of the grand response should characterize the divisor lines.**
   Open; extracted to the stage-1 card
   `../1-in-progress/universal-law-field/grand-response-positivity-locus-conjecture.md`
   with the known no-go filters attached.
6. **The two independent bounds \(\operatorname{Re}u>1-\sigma\) and
   \(\operatorname{Re}v>1-\sigma\) should suffice for (GAS.6).** False: at
   \(\sigma=2\), \(\operatorname{Re}u=\operatorname{Re}v=-0.9\), both bounds hold while the
   depth-one exponent has real part \(0.2\), so the prime Euler product diverges. The killing
   mechanism is coupling of the two observables on each mode. The positive survivor is the exact
   coupled chamber
   \(\operatorname{Re}(\sigma+u)>0\),
   \(\operatorname{Re}(\sigma+u+v)>1\), proved in Corollary 3.2; it is stronger as a boundary
   classification and is not killed by the counterexample.

## 11. Corpus and literature collision audit

Internal parents: ULF-EQG-1 (all translation-organ content; cited, not re-claimed), ULF-IPKMS-1
(single-mode Toeplitz KMS layer; its Theorem 2.1/§3 is the per-mode engine of Theorem 4.1),
ULF-QGPRH-1 (single-\(q\) process chart), the certified polarization and unitization theorems
(`ConstitutiveHistoryPolarization`, `ConstitutiveObserverUnitization`).

External parents and disclaimed components:

- B. Julia, *Statistical theory of numbers*, in Number Theory and Physics (1990) — the primon gas
  with \(Z=\zeta(\beta)\); our gas differs by having a mode at every prime **power**, which is what
  replaces \(\zeta(\sigma)\) by \(\prod_j\zeta(j\sigma)\) and creates the depth fan.
- J.-B. Bost, A. Connes, *Hecke algebras, type III factors and phase transitions...*, Selecta Math.
  1 (1995) — arithmetic KMS with symmetry-driven phase transition; our Corollary 4.2 is the
  contrast, not a rediscovery.
- P. Erdős, G. Szekeres (1934); D. G. Kendall, R. A. Rankin; A. Ivić — the identity
  \(\sum a(n)n^{-s}=\prod_k\zeta(ks)\) and its analytic theory, including the pole ladder
  \(x,x^{1/2},x^{1/3}\); classical, used as confirmation of the withheld organ.
- T. Estermann (1928); N. Kurokawa; G. Bhowmik, D. Essouabri — natural boundaries of Euler
  products, including products of the type \(\prod_k\zeta(ks)\) and multivariable variants; the
  natural-boundary mechanism in Theorem 6.1 is theirs.
- B. Fristedt, *The structure of random partitions of large integers*, TAMS 337 (1993) — the
  independent-geometric mode measure at a single \(q\); our local measure is Fristedt's at
  \(q=p^{-\sigma}\), globalized over primes.
- N. Chair, *The Euler–Riemann gases, and partition identities*, arXiv:1306.5415 — mode-frequency
  multiplication identities adjacent to Theorem 7.1's self-similarity; single-\(q\) setting.
- M. Marcolli, Z. Ren, *q-Deformations of statistical mechanical systems...*, arXiv:1704.06367 —
  q-deformed BC via Witt/Habiro constructions; different deformation mechanism, cited as the
  nearest q-BC neighbor.
- H. Cohen, H. W. Lenstra — the \(1/|\mathrm{Aut}|\) measure on abelian groups; our measure is the
  \(|A|^{-\sigma}\) zeta measure, a different (and much simpler) ensemble; no collision found for
  the assembled object.

Broad searches (arXiv + web, 2026-08) found no source assembling: the \(|A|^{-\sigma}\) zeta
measure as a KMS state of the prime-power Toeplitz gas, the socle/order two-observable divisor
dictionary, the sharp depth-condensation fan with \(\tfrac12\) as squarefull wall, or the entropy =
von Mangoldt mass identity. Priority is claimed only for the assembled coupling, per field policy.

## 12. Scope

- All statements are unconditional; \(\sigma>1\) where a probability law on finite groups is used,
  \(\sigma>0\) for the KMS theorem, \(\sigma>1/g\) chamber by chamber for Theorem 5.1.
- Nothing here proves RH, localizes any zero horizontally, or claims leverage beyond structure:
  the contribution is that one pre-zero source now provably carries the corpus's translation
  calculus, the classical dilation calculus, a unique-KMS phase organ, an exact RG action, sharp
  condensation walls at \(\{1/g\}\), and exact information costs, as one typed object.
- No Lean in this session by session directive; the card stays in Stage 2 under the certification
  boundary. Natural certification targets: Theorem 2.1, Theorem 3.1, Theorem 5.1, and (GAS.12)
  (finite/elementary layers first; the KMS theorem needs operator-algebra infrastructure the corpus
  already partially owns via ULF-IPKMS-1).

## Log

- 2026-08-09 — created: mode identification found while auditing ULF-EQG-1 against the PRD-E gate;
  socle bridge, KMS uniqueness, condensation fan, two-organ dictionary, RG action, and entropy
  identities proved; withheld dilation organ confirmed against classical literature; PRD-E passed
  at paper level.
- 2026-08-09 — hostile Lean-entry audit falsified the printed independent half-planes for (GAS.6);
  replaced them by the exact coupled absolute-convergence chamber and recorded the counterexample
  and positive survivor in failure loop 6.

## 13. Lean certification status

### Theorem 2.1 (GAS.4) — CERTIFIED

The `[NO LEAN]` tag in the header was stale.  Modules

```
GaloisForLFunctions.HTGeometry.AbelianZetaGas.Core
GaloisForLFunctions.HTGeometry.AbelianZetaGas.GibbsLaw
GaloisForLFunctions.HTGeometry.AbelianZetaGas.Normalization
```

(all wired into `GaloisForLFunctions.HTGeometry`) carry the mode space, the geometric mode laws,
the product gas measure, the finite-occupancy theorem, the group-class observables, and the
normalization identity:

| Clause | Lean |
|---|---|
| modes, depth fan, occupation ratios | `AbelianZetaMode`, `depth`, `AbelianZetaParameters`, `exponent`, `ratio`, `ratio_lt_one` |
| geometric mode law and the product gas | `modeLaw`, `modeLaw_singleton`, `gasMeasure` |
| Borel–Cantelli finite activity | `summable_ratio`, `AbelianZetaConvergentParameters.measure_finite_occupancy_eq_one`, `measure_existsUnique_groupClass_eq_one` |
| the two observables (GAS.3) | `AbelianZetaGroupClass.order`, `AbelianZetaGroupClass.socleOrder`, `order_eq_mode_product`, `socleOrder_eq_mode_product` |
| the Gibbs weight (GAS.4) | `abelianZetaModeWeight_eq_twoObservableWeight`, `abelianZetaClassMass`, `classMass_eq_ennNormalizer_mul_twoObservableWeight` |
| total mass one | `tsum_classMass_eq_one`, `tsum_twoObservableWeight_eq_ennNormalizer_inv` |
| the partition function `Z = ∏_j ζ(jσ+τ)` | `zetaPartition`, `complexNormalizer`, `complexNormalizer_eq_zetaPartition_inv`, `zetaPartition_eq_complexNormalizer_inv`, `complexNormalizer_ne_zero` |
| depth-tail machinery for the walls | `abelianZetaTailRatio`, `summable_abelianZetaTailRatio`, `abelianZetaTailModeEquiv`, `not_summable_prime_rpow_of_exponent_le_one`, `depthTailEvent` |

`#print axioms` on `tsum_classMass_eq_one`,
`classMass_eq_ennNormalizer_mul_twoObservableWeight`,
`complexNormalizer_eq_zetaPartition_inv`, `zetaPartition_eq_complexNormalizer_inv` and
`measure_existsUnique_groupClass_eq_one` reports only `propext`, `Classical.choice`, `Quot.sound`.

### Remaining certification targets, in attack order

1. **Theorem 3.1 (GAS.5), the socle bridge.**  The marginal of `N_p = ∑_j G_{p,j}` is the Euler
   weight `w_{q,n} = (q;q)_∞ q^n/(q;q)_n`.  The corpus already owns the two halves that meet here:
   `GaloisForLFunctions.HTGeometry.QBinomialTheorem` (Euler's `q`-binomial identity) and
   `EulerQGammaGlobalLaw` (`eqgWeight`, `eqgWeight_prime_pow`).  The formal content is the
   coefficient identity `[uⁿ] ∏_{j≥1}(1−u qʲ)⁻¹ = qⁿ/(q;q)_n`, i.e. Euler's identity read as a
   power series in `u`, together with the partition-counting rewrite
   `P(N_p = n) = (q;q)_∞ · ∑_{g : ∑_j g_j = n} q^{∑_j j g_j}`.
2. **Corollary 3.2, (GAS.7) — CERTIFIED; (GAS.6) remains.**

   `formal/GaloisForLFunctions/HTGeometry/AbelianZetaGas/DepthLadder.lean` (wired into
   `GaloisForLFunctions.HTGeometry`).  The socle tilt `τ ↦ τ + σ` moves depth `j` to depth `j + 1`,
   so the complete zeta ladder telescopes and the partition function loses exactly one factor.

   | Clause | Lean |
   |---|---|
   | the zeta ladder converges (exposed from the normalization proof) | `AbelianZetaConvergentParameters.hasProd_zetaLadder`, `…hasProd_zetaLadder_zetaPartition` |
   | the socle tilt inside the convergence chamber | `AbelianZetaConvergentParameters.depthShift` |
   | `ℕ` enumerates the nonzero naturals | `natComplZeroEquiv` |
   | **(GAS.7): `Z(σ,τ) = ζ(σ+τ)·Z(σ,τ+σ)`** | **`zetaPartition_depthShift`** |

   The proof is a head/tail split of the ladder (`HasProd.mul_compl` on `{0}` and its complement),
   which works in a commutative *monoid* and so applies to `ℂ` directly — the group-based
   `Multipliable.tprod_eq_zero_mul` does not.  Axiom prints: `propext`, `Classical.choice`,
   `Quot.sound` only; module green at 3 284 jobs.

   **(GAS.6) is now certified too**, in
   `formal/GaloisForLFunctions/HTGeometry/AbelianZetaGas/Response.lean`.  Tilting the zeta-Gibbs law
   by `|A|^{−(σ′−σ)}·|soc A|^{−(τ′−τ)}` moves the parameters from `θ` to `θ′`, so the expectation of
   the tilt is the ratio of the two zero-occupation constants, equivalently of the two zeta
   partition functions.  The card's coupled chamber `Re(σ+u) > 0`, `Re(σ+u+v) > 1` is exactly the
   requirement that *both* parameter points lie in the convergence chamber — it is carried by the
   types, not by a side hypothesis.

   | Clause | Lean |
   |---|---|
   | the tilt observable | `gasTilt`, `gasTilt_nonneg`, `twoObservableWeight_nonneg` |
   | the tilt moves the parameters | `twoObservableWeight_mul_gasTilt` |
   | the response | `gasResponse` |
   | **(GAS.6): `𝔉 = C_θ · C_{θ′}⁻¹`** | **`gasResponse_eq`** |
   | cleared form, no inverses | `gasResponse_mul_ennNormalizer`, `ennNormalizer_ne_zero`, `gasResponse_ne_top` |
   | **(GAS.6), zeta form: `𝔉 · Z(θ) = Z(θ′)`** | **`gasResponse_toReal_mul_zetaPartition`** |

   Axiom prints: `propext`, `Classical.choice`, `Quot.sound` only; module green at 3 285 jobs.
   Corollary 3.2 is therefore closed: (GAS.6) by `gasResponse_toReal_mul_zetaPartition` and (GAS.7)
   by `zetaPartition_depthShift`.
3. **Theorem 5.1, the depth-`g` condensation walls — ALREADY CERTIFIED.**  Audited in
   `Core.lean`: both halves are closed unconditionally, at `τ = 0` and in the general two-parameter
   chamber.

   | Clause | Lean |
   |---|---|
   | mode events | `depthTailEvent`, `exactDepthEvent`, `modeLaw_depthTailEvent`, `modeLaw_exactDepthEvent` |
   | convergent side of the wall | `tsum_depthTailEvent_ne_top`, `AbelianZetaParameters.measure_finite_depthTail_eq_one` |
   | divergent side of the wall | `tsum_exactDepthEvent_eq_top`, `AbelianZetaParameters.measure_infinite_exactDepth_eq_one` |
   | **5.1(1): `σ > 1/g` ⇒ finitely many active modes of depth `≥ g`** | **`AbelianZetaParameters.temperature_finite_depthTail_eq_one`** |
   | **5.1(2): `0 < σ ≤ 1/g` ⇒ infinitely many active modes of depth exactly `g`** | **`AbelianZetaParameters.temperature_infinite_exactDepth_eq_one`** |

   Axiom prints on all four capstones: `propext`, `Classical.choice`, `Quot.sound` only.  In
   particular the divergence half of ULF-EQG-1's failure loop 2, asserted there without proof, is
   machine-checked here as the depth-one case `g = 1`.
4. **(GAS.12) and Theorem 8.1**, the entropy/von Mangoldt identity — elementary once the response
   layer of target 2 is in place.
5. **Theorem 4.1 (KMS)** last: it needs C\*-inductive-limit and KMS-state infrastructure that
   mathlib does not have and that the corpus owns only partially through ULF-IPKMS-1.

### Target 1, step 1 — the partition generating-function layer

`formal/GaloisForLFunctions/HTGeometry/PartitionGeneratingFunction.lean` (wired into
`GaloisForLFunctions.HTGeometry`).

Neither mathlib nor the corpus owned partition generating functions (mathlib's Euler
odd-versus-distinct proof lives in `Archive`, which is not importable), so the layer is built here.
A partition is recorded by its occupation numbers `g : ℕ →₀ ℕ`, with `g j` the number of parts
equal to `j + 1`; `partCount` is the number of parts and `partSize` the size.  Everything rests on
one bijection — remove one from every part — used twice.

| Declaration | Statement |
|---|---|
| `PartConfig`, `partCount`, `partSize` | occupation-number model of a partition |
| `unshift`, `partCount_unshift`, `partSize_unshift` | raise every part by one and adjoin `a` ones |
| `shift`, `shift_apply`, `unshift_shift`, `shift_unshift` | lower every part by one |
| `partCount_eq`, `partSize_eq`, `partCount_shift_le` | the count and size split off the parts equal to one |
| **`partSize_eq_add_partSize_shift`** | the size drops by exactly the number of parts |
| **`shiftEquiv`** | partitions with exactly `n` parts ≃ partitions with at most `n` parts |
| `exactGF`, `atMostGF` | the two generating functions, as `ℝ≥0∞`-valued unconditional sums |
| **`exactGF_eq_mul`** | `S_n(q) = qⁿ · T_n(q)` — Euler's shift |
| `partCount_eq_zero_iff`, `atMostGF_zero` | `T_0 = 1` |
| `atMostGF_succ` | `T_{n+1} = T_n + S_{n+1}` |
| **`atMostGF_succ_self`** | **the Euler recursion `T_{n+1} = T_n + q^{n+1} T_{n+1}`** |

The sums are taken in `ℝ≥0∞`, so every identity above is unconditional — no summability side
condition appears anywhere.  Axiom audit: `propext`, `Classical.choice`, `Quot.sound` only; the
module builds green (8 655 jobs).

### Target 1, step 2 — Euler's generating function, closed form (DONE)

The finiteness input was obtained without any sorted-parts injection.  Truncating by *size* rather
than by support makes the shift bijection strictly decrease the size budget, so the Euler recursion
becomes an induction that terminates:

`T_n^{[N]} ≤ T_{n−1}^{[N]} + q^n · T_n^{[N−n]}`,  and  `N − n < N` for `n ≥ 1`.

Bounding by the geometric majorant `G = (1−q)⁻¹`, which satisfies `1 + qG = G`, gives
`T_n^{[N]} ≤ Gⁿ` uniformly in `N`, and then `T_n ≤ Gⁿ < ∞` by exhausting the index set with finite
subsets.  With finiteness the recursion inverts.

| Declaration | Statement |
|---|---|
| `atMostGFTrunc` | the size-truncated generating function |
| `partSize_eq_zero_iff`, `atMostGFTrunc_size_zero`, `atMostGFTrunc_count_zero` | the two base cases |
| `eq_unshift_of_partCount` | a configuration is recovered from its shift and its part count |
| `atMostGFTrunc_succ_le` | the truncated Euler step, with the size budget dropping by `n+1` |
| `geomBound`, `one_add_mul_geomBound`, `one_le_geomBound`, `geomBound_ne_top` | the majorant `G = (1−q)⁻¹` and `1 + qG = G` |
| `atMostGFTrunc_le_geomBound` | `T_n^{[N]} ≤ Gⁿ`, by induction on `n` and strong induction on `N` |
| `atMostGF_le_geomBound`, **`atMostGF_ne_top`** | **`T_n ≤ Gⁿ < ∞`** |
| `atMostGF_mul_one_sub` | `T_{n+1}(1 − q^{n+1}) = T_n` |
| **`atMostGF_mul_prod`** | **`T_n · ∏_{i<n}(1 − q^{i+1}) = 1`** |
| **`exactGF_mul_prod`** | **`S_n · ∏_{i<n}(1 − q^{i+1}) = qⁿ`** — Euler's identity for partitions with exactly `n` parts |

Stating the closed forms multiplicatively keeps the whole layer free of `ℝ≥0∞` division.  Axiom
audit: `propext`, `Classical.choice`, `Quot.sound` only; module green at 8 655 jobs.

### Target 1, step 3 — Euler's identity in q-Pochhammer form, and the local socle mass (DONE)

`formal/GaloisForLFunctions/HTGeometry/PartitionQPochhammerBridge.lean` (wired into
`GaloisForLFunctions.HTGeometry`).

`∏_{i<n}(1 − q^{i+1})` is literally the corpus's `realQFactorial q n`, so transporting
`exactGF_mul_prod` from `ℝ≥0∞` to `ℝ` identifies the partition generating function with the
q-geometric coefficient of the q-Pochhammer layer.

| Declaration | Statement |
|---|---|
| `exactGFReal`, `ofReal_nome_lt_one`, `exactGF_ne_top` | the real-valued exact generating function and its finiteness |
| `prod_ofReal_eq` | `∏_{i<n}(1 − q^{i+1})` in `ℝ≥0∞` is `ofReal (realQFactorial q n)` |
| **`exactGFReal_eq_qGeometricCoefficient`** | **`S_n(q) = qⁿ/(q;q)ₙ`** — Euler's identity in corpus form |
| `localSocleMass`, `localSocleMass_ne_top` | the `p`-local mass of the configurations with exactly `n` cyclic factors |
| **`localSocleMass_toReal`**, `localSocleMass_eq_ofReal` | **(GAS.5), local form: that mass is the Euler weight `w_{q,n} = (q;q)_∞·qⁿ/(q;q)ₙ`** |

Axiom audit: `propext`, `Classical.choice`, `Quot.sound` only; module green at 8 658 jobs.

### Target 1, step 4 — Theorem 3.1 (GAS.5), local form (DONE)

`formal/GaloisForLFunctions/HTGeometry/AbelianZetaGas/SocleBridge.lean` (wired into
`GaloisForLFunctions.HTGeometry`).

The two models line up exactly: the gas mode ratio at depth `j` and prime `p` is
`p^{−(j+1)σ} = q^{j+1}` for the nome `q = p^{−σ}`, so the local configuration mass
`∏_j (ratio)^{g_j}(1 − ratio)` is `(q;q)_∞ · q^{partSize g}` verbatim.

| Declaration | Statement |
|---|---|
| `tprod_occupation_pow`, `multipliable_occupation_pow` | `∏_j (q^{j+1})^{g_j} = q^{size g}`, a finite product |
| **`tprod_localModeMass`** | **the mass of one local configuration is `(q;q)_∞ · q^{size g}`** |
| **`tsum_localModeMass_eq_localSocleMass`**, `tsum_localModeMass_toReal` | summing over the configurations with exactly `n` cyclic factors gives the local socle mass, whose value is the Euler weight |
| `eqgNome_pow_succ` | the depth-`j` gas ratio at `p` is the `(j+1)`-st power of the nome `eqgNome σ p` |
| **`gas_socleMarginal_eq_eulerWeight`** | **(GAS.5): the local socle marginal of the gas at `p` is `(q;q)_∞ · eqgWeight σ (pⁿ)`, the Euler weight of the random-integer law of ULF-EQG-1** |

Axiom audit: `propext`, `Classical.choice`, `Quot.sound` only; module green at 8 660 jobs.

**Scope of what is certified.**  The statement is the *local* form of (GAS.5): it is about the
product of the geometric depth modes at one prime, which is exactly the object the card's proof
computes with.  The step from this to the marginal of the full `gasMeasure` — factoring the
countable product over `Nat.Primes × ℕ` into its prime blocks — is measure-theoretic bookkeeping
that remains; it needs a product-index splitting for `∏'` in `ℝ≥0∞`, which mathlib does not
currently carry.

### Theorem 7.1 (GAS.11) — depth dilation, measure-theoretic clauses (DONE)

`formal/GaloisForLFunctions/HTGeometry/AbelianZetaGas/DepthDilation.lean` (wired into
`GaloisForLFunctions.HTGeometry`).

| Clause | Lean |
|---|---|
| the dilation `δ_d : (p,j) ↦ (p,d·j)` | `depthDilation`, `depthDilation_fst`, `depth_depthDilation` |
| `δ_d` is injective onto the depth-`dℕ` modes | `depthDilation_injective` |
| **`δ_d ∘ δ_e = δ_{de}`: the renormalisation semigroup `(ℕ_{≥1}, ×)`** | **`depthDilation_comp`** |
| the dilated parameter point `σ ↦ d·σ` | `AbelianZetaParameters.depthDilate`, `AbelianZetaConvergentParameters.depthDilate` |
| **`φ_σ ∘ ι_d = φ_{dσ}`: pullback along `δ_d` is temperature dilation** | **`AbelianZetaParameters.ratio_depthDilation`** |
| **`Z` on the depth-`dℕ` modes at `σ` is `Z` at `d·σ`** | **`AbelianZetaConvergentParameters.zetaPartition_depthDilate`** |

The corpus indexes modes by `(p, k)` with `depth = k + 1`, so the card's `δ_d` is
`(p, k) ↦ (p, d(k+1) − 1)`; `depth_depthDilation` records that this multiplies the depth by `d`
exactly, and every later clause is stated in terms of the depth.

Axiom prints: `propext`, `Classical.choice`, `Quot.sound` only; module green at 3 286 jobs.

**What is not covered.**  The operator-algebraic clause of (GAS.11) — that `δ_d` induces a unital
`*`-embedding `ι_d` of the mode algebra intertwining the modular flows, `α_t ∘ ι_d = ι_d ∘ α_{dt}` —
waits on the KMS layer of Theorem 4.1.  The state and partition clauses above are the content that
the rest of the card actually uses: the wall ladder `{1/g}` of Theorem 5.1 is the `δ`-orbit of the
depth-one wall `σ = 1`, which is now `depthDilation_comp` together with
`AbelianZetaParameters.temperature_finite_depthTail_eq_one`.

### Theorem 8.1 (GAS.12) — the mode-mean ladder telescopes to the von Mangoldt mass

`formal/GaloisForLFunctions/HTGeometry/AbelianZetaGas/ModeMean.lean` (wired into
`GaloisForLFunctions.HTGeometry`).

The card's identity does not need any differentiation of `Z`.  Writing the symmetrised cost as
`σ·(E_{P_σ}[log|soc A|] − E_{P*}[log|soc A|])` and expanding `log|soc A| = ∑_{(p,j)} A(p,j)·log p`,
each mode contributes its geometric mean `r/(1−r)`; the unit tilt shifts the depth by one, so per
prime the two ladders differ by exactly their depth-one term, which is the local von Mangoldt
factor.

| Clause | Lean |
|---|---|
| the geometric mode mean | `modeMean`, `modeMean_nonneg`, `modeMean_le`, `summable_modeMean` |
| **the ladder telescopes** | **`tsum_modeMean_sub_shift`** |
| the depth-one residue is `∑_{a≥1} qᵃ` | `modeMean_zero_eq_tsum` |
| `(p^{−σ})^{a+1} = p^{−(a+1)σ}` | `eqgQ_pow_succ` |
| **(GAS.12), local form: the per-prime difference is `∑_{a≥1} p^{−aσ}`** | **`tsum_modeMean_sub_shift_prime`** |

Axiom prints: `propext`, `Classical.choice`, `Quot.sound` only; module green at 8 665 jobs.

**What remains for (GAS.12).**  Two independent pieces, neither of them the identity above:

1. *The gas-expectation layer*: that `E[log|soc A|] = ∑_{(p,j)} E[G_{p,j}]·log p` for the product of
   the geometric mode laws, and that the two relative entropies are finite.  This is the same
   product-measure bookkeeping that the global form of (GAS.5) needs.
2. *The prime-power reindexing* — **DONE**, in
   `formal/GaloisForLFunctions/HTGeometry/AbelianZetaGas/VonMangoldtEuler.lean`.

   | Clause | Lean |
   |---|---|
   | `Λ(p^{a+1}) = log p` | `vonMangoldt_primePow` |
   | `(p^{a+1})^{−σ} = p^{−(a+1)σ}` | `rpow_primePow` |
   | `Λ` is supported on the prime powers | `support_vonMangoldt_rpow_subset` |
   | **Euler form: `∑_n Λ(n)n^{−σ} = ∑_p log p · ∑_{a≥1} p^{−aσ}`** | **`tsum_vonMangoldt_eq_tsum_primes`** |
   | **the mode-mean residues sum to the von Mangoldt mass** | **`tsum_primes_modeMean_residue`** |
   | **and that mass is `−ζ′(σ)/ζ(σ)`** | **`ofReal_tsum_primes_modeMean_residue`** |

   The reindexing runs through mathlib's `Nat.Primes.prodNatEquiv : Nat.Primes × ℕ ≃ {n // IsPrimePow n}`
   and the corpus's `summable_vonMangoldt_rpow`; the `−ζ′/ζ` identification is the corpus's
   `ofReal_tsum_vonMangoldt_eq`.  Axiom prints: `propext`, `Classical.choice`, `Quot.sound` only;
   module green at 8 675 jobs.

   **What is left of (GAS.12)** is therefore only item 1, the gas-expectation layer: that
   `E[log|soc A|] = ∑_{(p,j)} E[G_{p,j}]·log p` under the product of the geometric mode laws, and
   that both relative entropies are finite.  The entire arithmetic side of the boxed identity —
   from the depth-one residue of the mode-mean ladder to `σ·(−ζ′/ζ)(σ)` — is now machine-checked.

### Theorem 6.1 — the dilation organ's divisor, finite-depth form (DONE)

`formal/GaloisForLFunctions/HTGeometry/AbelianZetaGas/DilationDivisor.lean` (wired into
`GaloisForLFunctions.HTGeometry`).

The depth-`j` factor `ζ(j(σ+u)+v)` is an affine pullback of `ζ` in the dilation variable with slope
exactly `j`, so its order is the order of `ζ` at the pulled-back point and orders add over any
depth truncation.

| Clause | Lean |
|---|---|
| the depth-`j` factor and its affine form | `depthFactor`, `depthFactor_eq_affine` |
| **(GAS.10): the depth-`j` factor meets `w` on the line `j·u + v = w − j·σ`** | **`depthFactor_arg_eq_iff`** |
| the factor is meromorphic in `u` | `meromorphicAt_depthFactor` |
| **(GAS.9), one depth** | **`meromorphicOrderAt_depthFactor`** |
| the depth-truncated response | `depthProduct` |
| **(GAS.9): `ord_u ∏_{j<J} = ∑_{j<J} ord_{j(σ+u)+v} ζ`** | **`meromorphicOrderAt_depthProduct`** |

The proof reuses ULF-EQG-1's certified affine-pullback machinery (`meromorphicAt_comp_affine`,
`meromorphicOrderAt_comp_affine`) verbatim — depth enters only as the nonzero slope `j`.  Axiom
prints: `propext`, `Classical.choice`, `Quot.sound` only; module green at 8 858 jobs.

### Theorem 6.1 — the depth tail converges and is zero-free (DONE)

`formal/GaloisForLFunctions/HTGeometry/AbelianZetaGas/DepthTail.lean` (wired into
`GaloisForLFunctions.HTGeometry`).

| Clause | Lean |
|---|---|
| the depth-`j` argument and its real part | `depthArg`, `re_depthArg` |
| the depth beyond which `Re ≥ 2` | `depthThreshold`, `two_le_re_depthArg` |
| the majorant is geometric in the depth | `rpow_two_depthArg`, `geomRatio_lt_one` |
| **normal convergence: `∑_j ‖ζ(j(σ+u)+v) − 1‖ < ∞`** | **`summable_norm_zeta_depth_sub_one`** |
| **the depth factors are multipliable** | **`multipliable_zeta_depth`** |
| **the tail beyond the threshold is zero-free** | **`tprod_zeta_depth_tail_ne_zero`** |

The convergence input is the corpus's own `norm_riemannZeta_sub_one_le_rpow`
(`‖ζ(s) − 1‖ ≤ 4·2^{−Re s}` for `Re s ≥ 2`): since `Re(j(σ+u)+v) = j·a + Re v` with
`a = σ + Re u > 0`, that bound is geometric with ratio `2^{−a} < 1`, so no compactness in `v` is
needed — the statement holds pointwise on the whole chamber `Re(σ+u) > 0`.  Axiom prints:
`propext`, `Classical.choice`, `Quot.sound` only; module green at 8 883 jobs.

The uniformity and holomorphy are certified as well:

| Clause | Lean |
|---|---|
| the uniform depth threshold on `a₀ ≤ σ + Re u` | `depthTailThreshold`, `two_le_re_depthArg_of_ge` |
| the uniform geometric bound | `norm_zeta_depthArg_sub_one_le` |
| each tail factor is holomorphic | `differentiableAt_zeta_depthArg` |
| **uniform convergence on every compact of the half-plane** | **`hasProdUniformlyOn_zeta_depthTail`** |
| **the tail product is holomorphic on `a₀ < σ + Re u`** | **`differentiableOn_tprod_zeta_depthTail`** |

### Theorem 6.1 — the grand response splits at any depth (DONE)

`formal/GaloisForLFunctions/HTGeometry/AbelianZetaGas/GrandResponse.lean` (wired into
`GaloisForLFunctions.HTGeometry`).

| Clause | Lean |
|---|---|
| `ℕ` enumerates the naturals beyond `J` | `natComplRangeEquiv` |
| **splitting a multipliable family at a finite depth, in a commutative monoid** | **`tprod_split_nat`** |
| the depth factors are multipliable after any shift | `multipliable_depthFactor_shift`, `multipliable_depthFactor_succ` |
| the grand response | `grandResponse`, `depthFactor_eq_zeta_depthArg` |
| **`F = (truncation at J) · (tail beyond J)`** | **`grandResponse_split`** |

`tprod_split_nat` is stated for an arbitrary multipliable family in a commutative *monoid*: mathlib's
`Multipliable.prod_mul_tprod_nat_add` needs a commutative group, and `ℂ` is not one under
multiplication.  The proof is again the `HasProd.mul_compl` head/tail split, this time on
`Finset.range J` and its complement — the same device that made `zetaPartition_depthShift` work.
Axiom prints: `propext`, `Classical.choice`, `Quot.sound` only; module green at 8 884 jobs.

The contraction is closed as well:

| Clause | Lean |
|---|---|
| the tail beyond any admissible depth is zero-free | `tprod_depthFactor_tail_ne_zero` |
| and holomorphic at every point of the chamber | `analyticAt_tprod_depthFactor_tail` |
| **(GAS.9), full form: `ord_u F = ∑_{j<J} ord_{j(σ+u)+v} ζ`** | **`meromorphicOrderAt_grandResponse`** |

The tail lemmas of `DepthTail.lean` were generalised from the canonical threshold to an arbitrary
admissible depth `J ≥ depthTailThreshold v a₀`, which is what lets the response be split at the same
depth at which its divisor is read.  Axiom prints: `propext`, `Classical.choice`, `Quot.sound` only;
module green at 8 884 jobs.

### Theorem 6.1 — the natural boundary (DONE)

`formal/GaloisForLFunctions/HTGeometry/AbelianZetaGas/NaturalBoundary.lean` (wired into
`GaloisForLFunctions.HTGeometry`).

The accumulation claim needs far less than the Riemann–von Mangoldt count: it needs only that the
completed zeta has zeros of arbitrarily large ordinate, because the *depths* supply the density.
For a single zero `ρ` of large ordinate `γ` and the depth `j = ⌊γ/t⌋`, the quotient `ρ/j` already
sits within `(1+|t|)/j` of `it` — one zero, one well-chosen depth, and the whole line is reached in
the limit.  The zero supply is the corpus's own `xiDivisorSupport_infinite`, upgraded to
unboundedness by the fact that a closed discrete subset of the plane inside a ball is finite.

| Clause | Lean |
|---|---|
| the `Ξ` divisor support is unbounded | `exists_xi_divisor_norm_gt` |
| **nontrivial zeta zeros of arbitrarily large ordinate** | **`exists_zetaZero_abs_im_gt`** |
| the ordinate sign can be prescribed (conjugate pairing) | `exists_zetaZero_im_div_gt` |
| the landing estimate `‖ρ/j − it‖ ≤ (|Re ρ| + |Im ρ − jt|)/j` | `norm_div_natCast_sub_mul_I_le` |
| **`ρ/j` comes arbitrarily close to every purely imaginary number** | **`exists_zetaZero_depth_near`** |

The landings themselves and their consequences:

| Clause | Lean |
|---|---|
| the landing point `u = ρ/j − σ` | `landing`, `re_landing` |
| **the landing has real part in `(−σ, −σ + 1/j)`** | **`re_landing_mem`** |
| **the response vanishes at every landing** | **`grandResponse_landing_eq_zero`** |
| **every point of `Re u = −σ` is a limit of zeros of the organ** | **`exists_grandResponse_zero_near`** |
| only finitely many zeta zeros meet a compact affine segment or disc | `finite_zetaZero_segment`, `finite_zetaZero_ball` |
| **the organ is nonzero somewhere in every disc of the chamber** | **`exists_grandResponse_ne_zero_near`** |
| **the zeros accumulate only on the line** | **`finite_grandResponse_zeros`** |
| **the line is a natural boundary** | **`no_analytic_extension`** |

`no_analytic_extension` is the sharp form: *no* function analytic at a point `p` of the line can
agree with `u ↦ 𝔉_σ(u,0)` on the chamber side of any neighbourhood of `p`.  The mechanism is the
identity theorem applied to the putative extension, not to the response itself: zeros of the
response accumulate at `p`, so the extension would vanish identically near `p`, while
`exists_grandResponse_ne_zero_near` produces a nonvanishing point of the response in every disc of
the chamber.  That non-degeneracy is itself unconditional: on a compact piece of the chamber the
response is a finite product of pulled-back zeta factors times a zero-free tail, and mathlib's
`IsCompact.inter_riemannZetaZeros_finite` makes each factor's zero set finite there.

`finite_grandResponse_zeros` is the converse half — *only* the line carries the accumulation:
within any closed ball and at any positive distance from the line there are finitely many zeros.

Axiom prints for every declaration above: `propext`, `Classical.choice`, `Quot.sound` only; the
module builds green (8 917 jobs).  **Theorem 6.1 is closed**: continuation, (GAS.9), (GAS.10),
item 2 (Corollary 3.2 plus the certified translation-divisor layer of ULF-EQG-1) and now item 1's
accumulation and natural-boundary claims.

### Theorem 4.1 (KMS) — the monomial monoid and the exchange identity

The card's proof of Theorem 4.1 never leaves the dense monomial `*`-algebra: existence is a product
of per-mode geometric states on elementary tensors, and uniqueness is a three-step computation on
monomials `∏_i V_i^{m_i}(V_i^*)^{n_i}`.  That algebra has an exact algebraic model — no C\*-norm, no
completion, no analytic continuation of the flow: it is the monoid algebra of the restricted direct
sum of bicyclic monoids, and the imaginary-time flow `α_{iσ}` is the algebra automorphism scaling
each generator by its weight.  Formalising Theorem 4.1 in that model is what the two modules below
begin.

#### The monomial monoid

`formal/GaloisForLFunctions/HTGeometry/AbelianZetaGas/GasWord.lean` (wired into
`GaloisForLFunctions.HTGeometry`).

A monomial is a pair of finitely supported exponent families, and multiplying two of them contracts
the inner block through `(V^*)^b V^{b'} = (V^*)^{b - b'} V^{b' - b}` — the bicyclic law, applied
mode by mode.  Every identity below is proved pointwise, where `omega` decides the truncated
subtraction.

| Clause | Lean |
|---|---|
| the monomial `∏_i V_i^{raise i}(V_i^*)^{lower i}` | `GasWord` |
| **the contraction law is a monoid** | **`GasWord.instMonoid`** |
| the generators and their powers | `gen`, `cogen`, `gen_pow`, `cogen_pow` |
| **the isometry relation `V_i^* V_i = 1`** | **`cogen_mul_gen`** |
| the one-mode block and its factorisation | `block`, `block_eq`, `mk_eq_mul` |
| **words on disjoint mode sets commute** | **`mul_comm_of_disjoint`** |
| **peeling one mode off a word** | **`eq_block_mul_erase`**, `disjoint_block_erase` |
| the charge `raise − lower` in `ℤ` | `charge`, `charge_apply` |
| **the charge is additive** | **`charge_mul`**, `charge_one` |
| a word is diagonal exactly when its charge vanishes | `charge_eq_zero_iff` |

#### The exchange identity

`formal/GaloisForLFunctions/HTGeometry/AbelianZetaGas/KMSExchange.lean` (wired into
`GaloisForLFunctions.HTGeometry`).

The KMS boundary condition enters only as the algebraic exchange identity
`φ(ab) = φ(b·σ(a))` of `ULF-IPKMS-1` (Theorem 2.1 there), which the corpus already carries for a
single mode.  Its two multi-mode consequences — exactly the two steps of the card's uniqueness
argument — are:

| Clause | Lean |
|---|---|
| **step 2: a mode with nonzero net charge kills the monomial** | **`kms_eq_zero_of_commuting`**, `kms_pow_eq_zero_of_commuting` |
| **step 3: a diagonal block peels off with the factor `qⁿ`** | **`kms_diagonal_step`** |

Both are stated for an arbitrary `ℂ`-algebra with an algebra endomorphism `σ` scaling the isometry,
so they apply verbatim to the monoid algebra of `GasWord` once the twist is built.  Axiom prints:
`propext`, `Classical.choice`, `Quot.sound` only; both modules build green (8 658 jobs).

**What remains of Theorem 4.1.**  In order:

1. *The twist.*  The character `χ(x) = ∏_i q_i^{charge x i}` is a monoid homomorphism
   `GasWord M → ℂˣ` (this is `charge_mul` plus `zpow`), so `MonoidAlgebra.lift` turns it into the
   algebra automorphism `σ` with `σ(V_i) = q_i · V_i`.
2. *The Gibbs functional.*  `φ = Finsupp.linearCombination ℂ ω` with
   `ω x = if x.raise = x.lower then ∏_i q_i^{x.raise i} else 0`.  The exchange identity
   `φ(xy) = φ(y σ(x))` is then a purely combinatorial check on pairs of words: both sides vanish
   unless the total charge is zero, and when it is, the identity reduces to
   `n' + (n − m')⁺ = m + (n' − m)⁺`, which follows from `m + m' = n + n'` — `omega` territory.
   This is the **existence** half, and it holds for every `σ > 0`: no convergence enters, because
   the monomial algebra is the algebraic (not the C\*) tensor product.
3. *Uniqueness.*  Induct on `x.raise.support ∪ x.lower.support` with `eq_block_mul_erase`: at each
   step either the peeled block is off-diagonal, and `kms_eq_zero_of_commuting` kills the word, or
   it is diagonal, and `kms_diagonal_step` extracts `q_i^{n_i}`.  `mul_comm_of_disjoint` supplies
   the commutation hypothesis both lemmas need.
4. *Scope.*  What this certifies is Theorem 4.1 on the dense monomial `*`-algebra — which is where
   the card's proof lives.  Extending it to the C\*-completion is a separate analytic wrapper
   (continuity of the state and density of the monomials), and the operator-algebraic clause of
   (GAS.11) — that `δ_d` induces `ι_d` with `α_t ∘ ι_d = ι_d ∘ α_{dt}` — is immediate on the
   monomial algebra once step 1 is in place, since `δ_d` is already certified as an injective
   depth map.

### The gas-expectation layer — the single-mode atom (DONE)

`formal/GaloisForLFunctions/HTGeometry/AbelianZetaGas/ModeExpectation.lean` (wired into
`GaloisForLFunctions.HTGeometry`).

| Clause | Lean |
|---|---|
| `∑_n n·rⁿ(1−r) = r/(1−r)` and its summability | `AbelianZetaParameters.tsum_natCast_mul_geometric`, `…summable_natCast_mul_geometric` |
| **the mean occupation of one mode** | **`AbelianZetaParameters.lintegral_modeLaw`** |

Stated as a lower Lebesgue integral the mean is unconditional — no integrability hypothesis appears
— and it is finite because the ratio is `< 1`.  This is the atom the socle expectation is assembled
from: `log|soc A| = ∑_{(p,j)} A(p,j)·log p` is mode-additive, so `E[log|soc A|]` is
`∑_{(p,j)} log p · (mean of mode (p,j))`, and each factor is now computed.

Axiom prints: `propext`, `Classical.choice`, `Quot.sound` only; module green at 8 666 jobs.

### The gas-expectation layer — COMPLETE

Both remaining steps turned out to be available: mathlib carries
`MeasureTheory.Measure.infinitePi_map_eval`, the coordinate marginal of an infinite product measure,
and `lintegral_tsum` for the exchange.

| Clause | Lean |
|---|---|
| **the mean occupation of a mode under the gas** | **`AbelianZetaParameters.lintegral_gasMeasure_eval`** |
| **the expectation of any nonnegative mode-additive observable** | **`AbelianZetaParameters.lintegral_gasMeasure_tsum`** |

`lintegral_gasMeasure_tsum` says exactly that `E[∑_m c_m·A(m)] = ∑_m c_m·(mean of mode m)` for every
nonnegative coefficient family — which with `c_{(p,j)} = log p` is `E[log|soc A|]`, the observable of
(GAS.12), and with the class-mass decomposition is the missing exchange for the global form of
(GAS.5).  Stated in `ℝ≥0∞` it carries no integrability hypothesis at all.

Axiom prints: `propext`, `Classical.choice`, `Quot.sound` only; module green at 8 666 jobs.

### (GAS.12), expectation side — the socle expectation (DONE)

Added to `formal/GaloisForLFunctions/HTGeometry/AbelianZetaGas/ModeExpectation.lean`.

| Clause | Lean |
|---|---|
| the socle observable's expectation | `AbelianZetaParameters.socleExpectation` |
| **it groups by prime into the mode-mean ladders** | **`AbelianZetaParameters.socleExpectation_eq`** |
| at `τ = 0` the mode mean is exactly `modeMean` | `ratio_div_one_sub_eq_modeMean` |
| **(GAS.12), expectation side** | **`socleExpectation_temperature`** |

`socleExpectation_temperature` says `E_σ[log|soc A|] = ∑_p log p · ∑_j modeMean(p^{−σ}, j)`.  With
`tsum_modeMean_sub_shift_prime` (the depth shift removes exactly the depth-one term) and
`tsum_primes_modeMean_residue` (those residues sum to the von Mangoldt mass), the symmetrised
information cost of the canonical unit tilt is `σ·∑_n Λ(n)n^{−σ} = σ·(−ζ′/ζ)(σ)`, which is the
boxed identity of Theorem 8.1.

Every ingredient of (GAS.12) is now certified.  What is not formalised is the *definition* of the
two relative entropies as such: the card writes the cost as `D(P*‖P_σ) + D(P_σ‖P*)`, and the Lean
development computes the equivalent quantity `σ·(E_{P_σ}[log|soc|] − E_{P*}[log|soc|])` directly
from the mode structure.  Introducing `MeasureTheory.klDiv` for the two laws and proving it equals
that difference is the remaining bookkeeping; the analytic content is closed.

Axiom prints: `propext`, `Classical.choice`, `Quot.sound` only; module green at 8 666 jobs.

### (GAS.12) — the tilted expectation (DONE)

| Clause | Lean |
|---|---|
| the canonical unit tilt `P_{σ,σ}` | `tiltParameters` |
| the tilt shifts the mode mean by one depth | `ratio_div_one_sub_eq_modeMean_tilt` |
| **the tilted socle expectation** | **`socleExpectation_tilt`** |

Both sides of the boxed identity are now expressions in the same object:

```text
socleExpectation_temperature :  E_σ [log|soc A|] = ∑_p log p · ∑_j modeMean(p^{-σ}, j)
socleExpectation_tilt        :  E_{σ,σ}[log|soc A|] = ∑_p log p · ∑_j modeMean(p^{-σ}, j+1)
tsum_modeMean_sub_shift_prime:  their per-prime difference is ∑_{a≥1} p^{-aσ}
tsum_primes_modeMean_residue :  summed against log p that is ∑_n Λ(n)n^{-σ}
ofReal_tsum_primes_modeMean_residue : which is −ζ′(σ)/ζ(σ)
```

so `σ·(E_σ − E_{σ,σ}) = σ·(−ζ′/ζ)(σ)` is a chain of certified identities.  Contracting it into one
Lean statement needs only the finiteness of the two expectations — both are bounded by the von
Mangoldt mass, which `tsum_vonMangoldt_rpow_pos` and `summable_vonMangoldt_rpow` already certify as
finite — since `ℝ≥0∞` subtraction is truncated.

Axiom prints: `propext`, `Classical.choice`, `Quot.sound` only; module green at 8 666 jobs.

### (GAS.12) — the contraction, in additive form (DONE)

| Clause | Lean |
|---|---|
| the `ℝ≥0∞` transport of the ladder and its shift | `tsum_ofReal_modeMean_eq`, `tsum_ofReal_modeMean_shift_eq` |
| **the ladder splits off its depth-one term** | **`tsum_ofReal_modeMean_split`** |
| **(GAS.12): `E_σ[log\|soc\|] = E_{σ,σ}[log\|soc\|] + (von Mangoldt mass)`** | **`socleExpectation_eq_tilt_add_residue`** |

Stating the contraction *additively* removes the last obstruction: `ℝ≥0∞` subtraction is truncated,
so the difference form would have needed finiteness of both expectations, whereas
`E_σ = E_{σ,σ} + residue` needs nothing at all.  The residue is
`∑_p log p · modeMean(p^{−σ}, 0)`, which `modeMean_zero_eq_tsum`, `eqgQ_pow_succ`,
`tsum_primes_modeMean_residue` and `ofReal_tsum_primes_modeMean_residue` identify with
`∑_n Λ(n)n^{−σ} = −ζ′(σ)/ζ(σ)`.

Theorem 8.1's analytic content is therefore closed end to end and unconditionally.  What is left is
purely definitional: exhibiting the card's `D(P*‖P_σ) + D(P_σ‖P*)` as `σ` times the difference of
these two expectations, i.e. introducing `MeasureTheory.klDiv` for the two laws and computing its
log-density.

Axiom prints: `propext`, `Classical.choice`, `Quot.sound` only; module green at 8 666 jobs.

### (GAS.12) — the residue is the von Mangoldt mass (DONE)

| Clause | Lean |
|---|---|
| **`∑_p log p · modeMean(p^{−σ},0) = ∑_n Λ(n)n^{−σ}`** | **`tsum_primes_modeMean_zero`** |
| **and that is `−ζ′(σ)/ζ(σ)`** | **`ofReal_tsum_primes_modeMean_zero`** |

The residue appearing in `socleExpectation_eq_tilt_add_residue` is therefore *literally* the von
Mangoldt mass, so (GAS.12) now reads, as a chain of certified Lean statements,

```text
E_σ[log|soc A|]  =  E_{σ,σ}[log|soc A|]  +  ∑_n Λ(n) n^{−σ}      (additive, unconditional)
                                            ∑_n Λ(n) n^{−σ}  =  −ζ′(σ)/ζ(σ)
```

which is the boxed identity of Theorem 8.1 after multiplying by `σ`.

### (GAS.5), global form — the prime fibre marginal (DONE)

| Clause | Lean |
|---|---|
| the modes above a fixed prime | `primeFiber` |
| depths enumerate that fibre | `primeFiberEquiv` |
| **the prime fibre marginal of the gas is the product of its depth modes** | **`gasMeasure_map_restrict_primeFiber`** |

This is the factorisation the global form of (GAS.5) needs: the law of the socle exponent at `p`
depends only on the depth modes above `p`.  It comes straight from mathlib's
`Measure.infinitePi_map_restrict'` once the gas is recognised as `Measure.infinitePi θ.modeLaw` —
no product-measure construction had to be built.

The transport to depth indexing is certified too:

| Clause | Lean |
|---|---|
| **the depth-indexed prime fibre marginal** | **`gasMeasure_map_primeFiber_depths`** |

`gasMeasure_map_primeFiber_depths` says `gasMeasure.map (fun k ↦ fun j ↦ k (p,j))` is exactly
`infinitePi (fun j ↦ modeLaw (p,j))`: reading the fibre by depth, the marginal of the gas above `p`
is the product of the depth mode laws at `p`.  It composes `infinitePi_map_restrict'` with
`infinitePi_map_piCongrLeft` along `primeFiberEquiv`.

The atom masses are certified as well:

| Clause | Lean |
|---|---|
| **a depth configuration's atom mass is the product of its mode masses** | **`infinitePi_depthModes_singleton`** |
| the same in mode-ratio form | `infinitePi_depthModes_singleton_ratio` |

`infinitePi_depthModes_singleton_ratio` gives the atom mass as
`∏'_j ofReal(ratio(p,j)^{g j}·(1 − ratio(p,j)))`, which is exactly the family that
`tsum_localModeMass_eq_localSocleMass` sums over the configurations with `n` parts.

**What is left of the global (GAS.5).**  Two bookkeeping steps.

1. *`ℝ≥0∞` transport of the atom mass* — **DONE**: `hasProd_ofReal` and `tprod_ofReal` transport a
   convergent product of nonnegative reals into `ℝ≥0∞`, so `tprod_localModeMass` now applies to
   `infinitePi_depthModes_singleton_ratio`.  The route is the corpus's own device from
   `Normalization.lean`: pass through `ℝ≥0` by `Topology.IsInducing.hasProd_iff` along the closed
   embedding `ℝ≥0 → ℝ`, then push forward with `ENNReal.ofNNRealHom`.  Note for future work that
   `Topology.IsInducing.multipliable_iff` does *not* exist — only the `hasProd_iff` form does, which
   is why the lemma is stated for `HasProd` and the `tprod` version derived from it.
2. *The atoms exhaust the event* — **DONE**.

| Clause | Lean |
|---|---|
| the exact-parts event as a union of configuration atoms | `exactPartsEvent` |
| **its mass is the sum of the atom masses** | **`measure_exactPartsEvent`** |
| **(GAS.5), global form at a prime: that mass is the local socle mass, hence the Euler weight** | **`measure_exactPartsEvent_eq_localSocleMass`** |

**Theorem 3.1 (GAS.5) is therefore closed in its global form.**  Chaining
`gasMeasure_map_primeFiber_depths` (the fibre marginal is the depth product),
`measure_exactPartsEvent_eq_localSocleMass` (its exact-parts mass is `localSocleMass`) and
`localSocleMass_toReal` (that is the Euler weight `w_{q,n}`) gives exactly (GAS.5): under the gas
the socle exponent at `p` has the Euler law of `ULF-EQG-1`.

Then `localSocleMass_toReal` identifies the total with the Euler weight and the global (GAS.5)
closes.

### (GAS.5) — the capstone

| Clause | Lean |
|---|---|
| **(GAS.5) as the card states it** | **`gas_socle_law`** |

`gas_socle_law` reads: under the abelian zeta gas at temperature `σ`, the probability that the socle
exponent at `p` is exactly `n` equals `(q;q)_∞ · eqgWeight σ (pⁿ)` — the Euler weight of the
random-integer law of `ULF-EQG-1`.  Theorem 3.1 is closed.

### Note for the remaining work

`klDiv` **does** exist in mathlib, in `Mathlib/InformationTheory/KullbackLeibler/Basic.lean` (not in
the `MeasureTheory` namespace), so no entropy theory has to be built.  But an audit of its API
corrects an earlier note on this card: `klDiv_of_ac_of_integrable` evaluates the divergence only
under `μ ≪ ν` **and** `Integrable (llr μ ν) μ`.  The integrability hypothesis is exactly the
finiteness of the socle expectations that the additive formulation of (GAS.12) was able to avoid.
So the last step of Theorem 8.1 is *not* purely definitional; it needs, in this order:

1. finiteness of `E_σ[log|soc A|]` — **DONE**.

   | Clause | Lean |
   |---|---|
   | `∑_j q^{j+1} = q/(1−q)` | `tsum_pow_succ` |
   | **the ladder is bounded: `∑_j modeMean(q,j) ≤ q/(1−q)²`** | **`tsum_modeMean_le`** |
   | `q/(1−q)² ≤ 4q` on the half interval | `div_one_sub_sq_le` |
   | the von Mangoldt family restricted to the primes is summable | `summable_primes_vonMangoldt` |
   | **the log-weighted ladder bound is summable over the primes** | **`summable_primes_log_mul_ladderBound`** |

   The prime sum did not need the `(1 − 2^{−σ})^{−1}` constant after all: since `q_p ≤ 1/2` for
   every prime, `q/(1−q)² ≤ 4q` outright, so the bound is `4·Λ(p)·p^{−σ}` termwise and summability
   is a subfamily comparison against `summable_vonMangoldt_rpow`;
2. mutual absolute continuity of `P_σ` and `P_{σ,σ}` with the density `ζ(σ)|soc A|^{−σ}`.  The
   *constant* in that density is already certified: `temperatureConv` places the untilted gas in the
   convergence chamber and **`zetaPartition_temperatureConv`** is (GAS.7) at `τ = 0`, namely
   `Z(σ,0) = ζ(σ)·Z(σ,σ)` — which is exactly the ratio of normalisers appearing in the
   Radon–Nikodym derivative, and the *atomwise* factor is certified too:
   **`twoObservableWeight_tiltParameters`** says the unit tilt multiplies the Gibbs weight by exactly
   `|soc A|^{−σ}`.  With `classMass_eq_ennNormalizer_mul_twoObservableWeight` the full density
   `ζ(σ)·|soc A|^{−σ}` is therefore assembled from certified parts.

   The carrier is built too, in
   `formal/GaloisForLFunctions/HTGeometry/AbelianZetaGas/ClassLaw.lean`:

   | Clause | Lean |
   |---|---|
   | the discrete measurable structure on the class space | `instance : MeasurableSpace AbelianZetaGroupClass`, `instance : MeasurableSingletonClass …` |
   | the zeta-Gibbs law as an atomic measure | `classLaw` |
   | **its atom masses are the class masses** | **`classLaw_singleton`** |
   | **it is a probability measure in the convergence chamber** | **`classLaw_univ`** |

   `AbelianZetaGroupClass` had no `MeasurableSpace` instance in the tree — the gas measure lives on
   the configuration space and the class space was only ever an index for atoms — so the discrete
   structure is introduced here.  What remains of step 2 is the absolute continuity itself, which is
   now immediate from `classLaw_singleton` and the positivity of every class mass;
3. `klDiv_of_ac_of_integrable` twice, and the log-density computation
   `llr = log ζ(σ) − σ·log|soc A|`.

Steps 1 and 2 are closed, and step 3 has its atomwise input:

| Clause | Lean |
|---|---|
| the canonical unit tilt in the convergence chamber | `tiltConv` |
| **the atomwise mass of the tilt** | **`classMass_tiltConv`** |

`classMass_tiltConv` reads: the class mass of `P_{σ,σ}` is its normaliser times the untilted Gibbs
weight times `|soc A|^{−σ}`.  With `classLaw_singleton` this is the atomwise Radon–Nikodym ratio, and
with `zetaPartition_temperatureConv` its constant is `ζ(σ)`.

The density presentation is certified as well:

| Clause | Lean |
|---|---|
| the atom mass of a `withDensity` | `withDensity_singleton` |
| the density constant | `densityConst` |
| **the canonical tilt is a density against the untilted law** | **`classLaw_tiltConv_eq_withDensity`** |

`classLaw_tiltConv_eq_withDensity` exhibits `P_{σ,σ}` as
`P_σ.withDensity (fun A ↦ densityConst σ · |soc A|^{−σ})`, proved atomwise through
`Measure.ext_of_singleton` on the countable class space.

The Radon–Nikodym derivative is certified too:

| Clause | Lean |
|---|---|
| the class law is a probability measure | `isProbabilityMeasure_classLaw` |
| **the Radon–Nikodym derivative of the canonical tilt** | **`rnDeriv_classLaw_tiltConv`** |

The log-density is certified as well:

| Clause | Lean |
|---|---|
| the density constant is finite and positive | `ennNormalizer_ne_top`, `densityConst_ne_zero`, `densityConst_ne_top`, `densityConst_toReal_pos` |
| **the log-density of the canonical tilt** | **`llr_classLaw_tiltConv`** |

`llr_classLaw_tiltConv` is exactly the card's `log ζ(σ) − σ·log|soc A|`, once `densityConst σ` is
identified with `ζ(σ)` through `zetaPartition_temperatureConv`.

### Theorem 8.1 is fully certified

`formal/GaloisForLFunctions/HTGeometry/AbelianZetaGas/RelativeEntropy.lean` (wired into
`GaloisForLFunctions.HTGeometry`).

**Finiteness of the two means.**  The socle and order expectations are finite at every `σ > 1`;
this is the only analytic input the Kullback–Leibler evaluation needs, and it is obtained from the
prime ladder bounds alone.

| Clause | Lean |
|---|---|
| `∑_j m_j(q) ≤ q/(1−q)²` summed over primes | `summable_primes_log_mul_tsum_modeMean` |
| **the socle mean in real form** | **`socleExpectation_temperature_eq_ofReal`** |
| socle mean of the gas and of the tilt are finite | `socleExpectation_temperature_ne_top`, `socleExpectation_tilt_ne_top` |
| `∑_j (j+1)·m_j(q) ≤ q/(1−q)³` | `summable_depthMean`, **`tsum_depthMean_le`** |
| `q/(1−q)³ ≤ 8q` and its prime sum | `div_one_sub_cube_le`, `summable_primes_log_mul_depthLadderBound` |
| **the order mean in real form, and its finiteness** | **`orderExpectation_temperature_eq_ofReal`**, `orderExpectation_temperature_ne_top` |
| the von Mangoldt residue in `ℝ≥0∞` form | `residue_eq_ofReal_vonMangoldt` |

**The two observables on the class space.**  Both are mode-additive, so both transport along the
class map with no integrability side condition — the Bochner integral is evaluated through
`integral_eq_lintegral_of_nonneg_ae`, which needs only nonnegativity.

| Clause | Lean |
|---|---|
| `log|A| = ∑ (depth m)·A(m)·log p` | `log_order`, `log_order_classOf`, `ofReal_logOrder_eq_tsum` |
| the order expectation as a mode-additive integral | `orderExpectation`, **`orderExpectation_eq`** |
| **`∫⁻ log|soc A| = socleExpectation`, `∫⁻ log|A| = orderExpectation`** | **`lintegral_classLaw_logSocle`**, **`lintegral_classLaw_logOrder`** |
| the Bochner means | `integral_classLaw_logSocle`, `integral_classLaw_logOrder` |
| integrability from finiteness | `integrable_classLaw_logSocle`, `integrable_classLaw_logOrder` |

**(GAS.12).**  The reverse density is built exactly like the forward one, so both `llr`'s are
available and both divergences are finite.

| Clause | Lean |
|---|---|
| the untilted law as a density against the tilt | `classLaw_temperatureConv_eq_withDensity`, `rnDeriv_classLaw_temperatureConv` |
| the reverse log-density `−log C + σ·log|soc A|` | `llr_classLaw_temperatureConv` |
| mutual absolute continuity | `ac_tilt_temperature`, `ac_temperature_tilt` |
| integrability of both log-densities | `integrable_llr_tilt`, `integrable_llr_temperature` |
| the two mean log-densities | `integral_llr_tilt`, `integral_llr_temperature` |
| the two divergences, and their finiteness | `klDiv_tilt`, `klDiv_temperature`, `klDiv_tilt_ne_top`, `klDiv_temperature_ne_top` |
| the two socle means differ by the von Mangoldt mass | **`socleExpectation_toReal_sub`** |
| **`D(P*‖P) + D(P‖P*) = σ·∑ Λ(n)n^{−σ}`** | **`klDiv_symmetrised_eq_vonMangoldt`** |
| the same in real and in zeta form | `klDiv_symmetrised_toReal`, **`klDiv_symmetrised_eq_zeta`** |

`klDiv_symmetrised_eq_zeta` is the boxed identity of the card:
`D(P*‖P) + D(P‖P*) = σ·(−ζ′/ζ)(σ)`.  Nonnegativity of each summand is taken from mathlib's
`integral_llr_add_sub_measure_univ_nonneg`, which is what makes the `ℝ≥0∞` addition split.

**(GAS.13).**  Both ladders are obtained from one observation: raising the depth by `j` is the same
as raising the temperature to `(j+1)σ`, so every depth level is a *shifted copy of the same
residue*.

| Clause | Lean |
|---|---|
| the temperature at depth `j` | `depthSigma` |
| `m_j(p^{−σ}) = m_0(p^{−(j+1)σ})` | **`modeMean_eqgQ_depth`** |
| **`E_σ[log|soc A|] = ∑_{j≥1} (−ζ′/ζ)(jσ)`** | **`socleExpectation_temperature_depthLadder`** |
| **`E_σ[log|A|] = ∑_{j≥1} j·(−ζ′/ζ)(jσ)`** | **`orderExpectation_temperature_depthLadder`** |

**(GAS.14).**  The temperature deformation multiplies the Gibbs weight by `|A|^{−u}`, so the whole
(GAS.12) argument runs again with the order observable in place of the socle observable.

| Clause | Lean |
|---|---|
| the deformed temperature and its weight | `sigmaShift`, **`twoObservableWeight_shift`** |
| the deformation as a density, both ways | `classLaw_shift_eq_withDensity`, `classLaw_temperatureConv_eq_withDensity_shift` |
| the two Radon–Nikodym derivatives and log-densities | `rnDeriv_classLaw_shift`, `rnDeriv_classLaw_temperatureConv_shift`, `llr_classLaw_shift`, `llr_classLaw_temperatureConv_shift` |
| integrability and the two mean log-densities | `integrable_llr_shift`, `integrable_llr_temperature_shift`, `integral_llr_shift`, `integral_llr_temperature_shift` |
| the two divergences | `klDiv_shift`, `klDiv_temperature_shift` |
| **the deformation lowers the order mean** | **`orderExpectation_shift_le`** |
| **`D(P_{σ+u}‖P_σ) + D(P_σ‖P_{σ+u}) = u·(E_σ[log|A|] − E_{σ+u}[log|A|]) ≥ 0`** | **`klDiv_symmetrised_temperature_shift`** |

Combining `klDiv_symmetrised_temperature_shift` with
`orderExpectation_temperature_depthLadder` at `σ` and at `σ+u` gives the card's
`u·∑_{j≥1} j[(−ζ′/ζ)(jσ) − (−ζ′/ζ)(j(σ+u))] ≥ 0`.

Axiom audit for every declaration above: `propext`, `Classical.choice`, `Quot.sound` only; the
module builds green (8 682 jobs).  **Theorem 8.1, and with it (GAS.12), (GAS.13) and (GAS.14), is
closed.**
