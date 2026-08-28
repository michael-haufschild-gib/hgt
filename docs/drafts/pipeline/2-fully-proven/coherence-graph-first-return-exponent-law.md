# Static-local all-observer first-return law

- **ID:** coherence-graph-first-return-exponent-law
- **Stage:** 2-fully-proven
- **Type:** THEOREM / MIXED-STATE RECURRENCE / STATIC LOCAL MANY-BODY SYSTEMS
- **Date:** 2026-08-28
- **Status:** [PAPER-PROVED] [NOVELTY UNVERIFIED]

## Public sentence

One fixed one-dimensional quantum system can make every state and every finite collection of
probes recur at a power determined only by which energy coherences those probes connect.

## Frontier

### [LITERATURE]

1. Gimeno--Sotoca, *J. Phys. A* **50** (2017) 185302, prove mixed-state recurrence upper bounds
   for discrete spectra. They do not prove an exact first-return exponent, observer graph law, or
   local-Hamiltonian realization.
2. Kotowski--Oszmaniec, *Phys. Rev. Lett.* **137** (2026) 060402, prove deterministic pure-state
   recurrence upper bounds and generic random-Hamiltonian lower bounds. Their conclusion asks for
   extensions to mixed states, expectation values, and physical local noncommuting Hamiltonians.
3. Karimi--Wu--Cleland--Pekola, *Phys. Rev. Research* **8** (2026) L012062, give a multiqubit
   experimental blueprint and size scaling, not exact coherence-graph first-return law.
4. Shrinking-target and hitting-time exponents for torus translations are classical. Diophantine
   first-return mechanism below is therefore [BRIDGE], not novelty claim.
5. Targeted primary-source searches through 28 August 2026 found no theorem with simultaneous
   quantifiers and physical locality conclusion frozen below. Priority remains provisional
   pending independent expert review.

### [CORPUS]

1. FiniteQuantumObserverCoherenceLaw.lean: exact Hilbert--Schmidt displacement identity, zero law,
   and graph capacity \(D-c(G)\).
2. FiniteQuantumObserverGraphRecurrenceBound.lean: graph-rank Dirichlet upper deadline.
3. ObserverTemporalDimensionLaw.lean: visible-gap module equals component-relative-energy module.
4. ObserverReturnTemporalMetricLaw.lean and ObserverReturnTemporalCoercivityLaw.lean: local
   quadratic comparison for observer return metrics.
5. KleinbockMargulis/FirstReturnExponent.lean: non-VWA continuous first-return lower law.
6. NearestNeighborPathSpectrumRealRelationEscape.lean: full nearest-neighbour path family escapes
   every balanced real spectral relation.
7. AllStateSpectralSupportRecurrenceLaw.lean: one local Hamiltonian classifies all pure states by
   spectral support. It does not cover arbitrary mixed-state coherence graphs or observer unions.
8. No declaration found that proves exact all-observer physical exponent or unconditional
   static-local capstone.

## Failure-driven conjecture loop

### [FALSIFIED] C1: graph capacity controls every fixed spectrum

Claim that every observer has exponent \((D-c(G)-1)/2\) is false without arithmetic control.
If visible gaps have rational rank smaller than \(D-c(G)\), orbit explores a lower-dimensional
subtorus and recurs faster; rational rank one is exactly periodic regardless of graph capacity.

### [BRIDGE] C1 survivor: two ranks

For an arbitrary fixed system,

\[
 r_{\rm cap}=D-c(G),\qquad
 s_{\rm dyn}=\dim_{\mathbb Q}\operatorname{span}_{\mathbb Q}
 \{E_i-E_j:\{i,j\}\in E(G)\}
\]

are different. First is observable phase capacity; second is actual temporal rank. Universal
upper power in Hilbert--Schmidt radius is \(\max\{s_{\rm dyn}-1,0\}\). A non-VWA packet attains
that power. This is a quantum instantiation of classical torus recurrence and is not by itself
new scientific knowledge.

### [PAPER-PROVED] C2: static-local simultaneous saturation

For every \(N,Q\in\mathbb N\), put \(n=N+2\), \(q=Q+2\), and \(D=q^n\). There exists one
time-independent Hermitian Hamiltonian \(H\) in full onsite-plus-nearest-neighbour path family on
\((\mathbb C^q)^{\otimes n}\) such that:

1. \(H\) has simple spectrum \(E_1<\cdots<E_D\);
2. \(H\) has an onsite-plus-edge decomposition containing two local summands with nonzero
   commutator;
3. for every finite matrix family \((B_a)\), every nonnegative weight family \((\lambda_a)\), and
   every \(t_0>0\), define in energy basis

   \[
    w_{ij}=\sum_a\lambda_a |(B_a)_{ij}|^2,
   \]

   let \(G\) have edge \(\{i,j\}\) iff \(w_{ij}+w_{ji}>0\), and set

   \[
    \mathcal D_{H,B}(t)=
    \sum_a\lambda_a\|e^{-itH}B_ae^{itH}-B_a\|_{\rm HS}^2,
   \]

   \[
    T_{H,B}(\delta;t_0)
    =\inf\{t\ge t_0:\mathcal D_{H,B}(t)<\delta\}.
   \]

   Then

   \[
    \boxed{
    \lim_{\delta\downarrow0}
    \frac{\log T_{H,B}(\delta;t_0)}{\log(1/\delta)}
    =\frac{\max\{D-c(G)-1,0\}}2.}
   \]

Hamiltonian is chosen before observer family, weights, state, and cutoff. Constants and onset may
depend on observer; exponent does not.

For every density matrix \(\rho\), use \(B=\rho\). Hilbert--Schmidt and trace norms are equivalent
in fixed dimension, so first return in trace-distance radius \(\epsilon\) has power
\(\max\{D-c(G_\rho)-1,0\}\). For pure projector, \(G_\rho\) is complete on exact spectral
support and isolated elsewhere, recovering existing support law.

## Why C2 is stronger than killed claim

C2 does not patch rational dependence with a hypothesis. It proves existence of one physical
local Hamiltonian for which every one of finitely many labelled coherence graphs has maximal
rational rank and non-VWA projective packet simultaneously. Arithmetic premise is a conclusion
about selected Hamiltonian, while observers remain universally quantified.

## Dependency-closed paper proof

### Lemma 1: exact observer phase energy

Diagonal conjugation multiplies matrix entry \((i,j)\) by
\(\exp[-it(E_i-E_j)]\). Orthogonality of matrix units in Hilbert--Schmidt inner product gives

\[
 \mathcal D_{H,B}(t)
 =\sum_{i,j}w_{ij}|e^{-it(E_i-E_j)}-1|^2.                 \tag{1}
\]

Diagonal terms vanish. Equation (1) is zero exactly when endpoint phases agree on every edge,
hence exactly when phase is constant on every connected component of \(G\).

### Lemma 2: graph capacity and quadratic target equivalence

Choose one root in each component and a spanning forest. There are

\[
 r=D-c(G)                                                     \tag{2}
\]

nonroot vertices. For each nonroot \(v\), set

\[
 \omega_v=E_v-E_{\operatorname{root}(v)}.                    \tag{3}
\]

Choose, on each forest edge, one directed orientation having positive aggregate weight and let
\(m>0\) be minimum of those finitely many weights. Let \(W=\sum_{ij}w_{ij}\).

If every root-relative phase chord is at most \(R\), every visible edge chord is at most \(2R\),
so

\[
 \mathcal D_{H,B}(t)\le 4WR^2.                              \tag{4}
\]

Conversely, if \(\mathcal D(t)<\delta\), every forest-edge chord is below
\(\sqrt{\delta/m}\). Telescoping along a forest path of length at most \(D-1\) makes every
root-relative chord below \((D-1)\sqrt{\delta/m}\). Since for
\(\|x\|_{\mathbb Z}\le1/2\),

\[
 4\|x\|_{\mathbb Z}\le |e^{2\pi i x}-1|
 \le2\pi\|x\|_{\mathbb Z},                                \tag{5}
\]

there are fixed constants \(a,b>0\) such that, for all small \(\delta\),

\[
 \max_v\left\|\frac{t\omega_v}{2\pi}\right\|_{\mathbb Z}
 <a\sqrt\delta
 \Longrightarrow \mathcal D_{H,B}(t)<\delta
 \Longrightarrow
 \max_v\left\|\frac{t\omega_v}{2\pi}\right\|_{\mathbb Z}
 <b\sqrt\delta.                                           \tag{6}
\]

Thus weights change only constants, whereas graph connectivity determines target codimension.

### Lemma 3: sharp physical first-return exponent

Assume \(r\ge2\) and projective packet obtained by choosing one nonzero \(\omega_0\),

\[
 \beta=(\omega_v/\omega_0)_{v\ne0}\in\mathbb R^{r-1},       \tag{7}
\]

is not very well approximable. Dirichlet simultaneous approximation gives, for every large \(Q\),
some \(1\le k\le Q^{r-1}\) with
\(\max_v\|k\beta_v\|_{\mathbb Z}\le1/Q\). At
\(t=2\pi k/|\omega_0|\), clock phase is exact, so (6) gives upper return power \(r-1\) in radius
\(\epsilon=\sqrt\delta\).

For lower bound, sufficiently small return forces clock phase within \(O(\epsilon)\) of integer
\(k\); (6) and triangle inequality then force

\[
 \max_v\|k\beta_v\|_{\mathbb Z}\le C\epsilon.              \tag{8}
\]

Non-VWA says that for every \(\eta>0\), all sufficiently large \(k\) obey

\[
 \max_v\|k\beta_v\|_{\mathbb Z}
 \ge k^{-1/(r-1)-\eta}.                                    \tag{9}
\]

Packet is rationally independent, so it has no positive exact return. Continuity on every compact
interval \([t_0,M]\) therefore gives positive minimum defect; return times tend to infinity as
\(\epsilon\) tends to zero and integer \(k\) in (8) is eventually positive and comparable to
physical time. Equations (8)--(9) yield lower power at least
\((r-1)/(1+(r-1)\eta)\). Letting \(\eta\) decrease to zero and combining with Dirichlet proves
power \(r-1\) in \(\epsilon\), hence \((r-1)/2\) in squared defect \(\delta\).

If \(r=0\), graph has no visible edge and (1) vanishes identically. If \(r=1\), graph has exactly
one two-vertex nontrivial component; every term in (1) has one energy gap, so displacement is
exactly periodic. Both boundary exponents are zero.

### Lemma 4: every graph packet is nondegenerate on a local spectral chart

Fix labelled graph \(G\) and component roots. For its nonroot vertices define incidence vectors

\[
 b_v=e_v-e_{\operatorname{root}(v)}\in\mathbb R^D.          \tag{10}
\]

Vectors \((b_v)\) are linearly independent: at coordinate of nonroot vertex \(v\), only \(b_v\)
has coefficient \(+1\), because roots are excluded from nonroot list.

On connected simple-spectrum analytic chart of full path family, write ordered eigenvalue map as
\(E(x)\). Existing path spectral-escape theorem states that for every nonzero balanced
\(c\in\mathbb R^D\), function \(c\cdot E(x)\) is not identically zero.

For \(r\ge2\), choose \(b_0\) and form analytic ratio map

\[
 f_G(x)=\left(
 \frac{b_v\cdot E(x)}{b_0\cdot E(x)}
 \right)_{v\ne0}.                                         \tag{11}
\]

Denominator never vanishes on simple-spectrum chart. If a nonzero affine functional of \(f_G\)
were constant, clearing denominator would produce identically zero balanced spectral relation
whose coefficient vector is a nontrivial real combination of independent \((b_v)\), contradicting
spectral escape. Thus \(1\) and coordinates of \(f_G\) are linearly independent as analytic
functions. Kleinbock--Margulis analytic extremality implies preimage of VWA set is null.

There are finitely many labelled simple graphs on \(D\) vertices. Intersect their full-measure
non-VWA sets. Result remains conull and gives one Hamiltonian satisfying Lemma 3 for every graph
simultaneously. This converts uncountable observer-family quantifier into finite graph
intersection; weights never enter arithmetic event.

### Lemma 5: chart can be chosen genuinely noncommuting

Let \(Z=\operatorname{diag}(0,1,\ldots,q-1)\) on one qudit and let
\(X=|0\rangle\langle1|+|1\rangle\langle0|\). Digit Hamiltonian

\[
 H_{\rm dig}=\sum_{j=1}^{n}q^{j-1}Z_j                    \tag{12}
\]

has distinct product-basis eigenvalues \(0,1,\ldots,q^n-1\). Add edge term

\[
 V_\varepsilon=\varepsilon X_1\otimes X_2.                \tag{13}
\]

For sufficiently small nonzero \(\varepsilon\), simple spectrum persists by operator-norm
eigenvalue perturbation bound. Moreover

\[
 [Z_1,V_\varepsilon]\ne0.                                  \tag{14}
\]

Both simplicity and nonzero commutator persist on nonempty open coefficient neighborhood.
Choose connected ball inside it. Conull simultaneous event from Lemma 4 meets this ball, so
select \(H\) there. It is static, one-dimensional, nearest-neighbour, bounded degree, simple, and
has noncommuting local summands.

### Capstone

Select \(H\) as in Lemma 5. Lemma 4 discharges non-VWA simultaneously for every coherence graph.
For arbitrary observer family, Lemmas 1--3 give exactly C2. Selection occurred before observer,
weights, density matrix, and cutoff, so all universal quantifiers are preserved.

For density matrix, (1) is exact conjugation displacement. In dimension \(D\),

\[
 \|A\|_{\rm HS}\le\|A\|_1\le\sqrt D\|A\|_{\rm HS},        \tag{15}
\]

so fixed norm factors do not change logarithmic first-return exponent. For
\(\rho=|\psi\rangle\langle\psi|\), graph is complete on exact energy support of \(\psi\), plus
isolated vertices, and

\[
 \|e^{-itH}\rho e^{itH}-\rho\|_{\rm HS}^2
 =2(1-|\langle\psi,e^{-itH}\psi\rangle|^2),               \tag{16}
\]

recovering pure-state support law.

## Hostile audit

1. **Graph-only universality repaired.** Exceptional rational rank killed C1; C2 proves one local
   Hamiltonian where every graph saturates capacity instead of assuming saturation.
2. **Classical mechanism not claimed new.** Torus shrinking-target exponent is [BRIDGE].
3. **Mixed-state claim exact.** Result concerns ordinary unmeasured unitary conjugation, not
   monitored recurrence or channel iteration.
4. **Observer claim properly scoped.** It gives operator-family return and therefore uniform
   expectation-value return over input states; one scalar expectation can return faster by
   cancellation and is not assigned this exponent.
5. **No uniform onset over observers.** Tiny positive weights change coercivity constants and may
   postpone asymptotic regime; theorem claims only common exponent.
6. **No hidden locality premise.** Site count and local dimension are shifted by two; path locality,
   simple spectrum, chart existence, noncommutation and arithmetic genericity are conclusions.
7. **No thermodynamic claim.** This is all-finite-size theorem. It strengthens physical model class
   without asserting infinite-volume recurrence exponent.
8. **Priority scope.** Candidate novelty is exact simultaneous all-observer law for one static
   one-dimensional local noncommuting Hamiltonian, not graph rank, Diophantine approximation, or
   existence of mixed-state recurrence separately.

## [FORMAL OPEN CORE]

Paper proof is dependency-closed. Remaining gate is exact Lean formalization of Lemmas 3--5 and
closed shifted capstone; no mathematical hypothesis may survive in final theorem.

## Paper-integration decision

This theorem is not a replacement paper.  By itself it is narrower than the existing four-law
recurrence synthesis.  Its role is to close the strongest missing arrow inside Law III:

\[
\text{observer coherence graph}
\longrightarrow
\text{exact physical first-return exponent}
\]

on the same static local Hamiltonian for every finite observer family.  The unified paper retains
carrier selection, arbitrary spectral type, action--constraint conservation, scalar/resolved
information separation, finite-horizon non-identifiability, thermodynamic completion, circuit
occupation and return reflection.  C2 upgrades the observer theorem from a capacity identity and
Dirichlet deadline to an exact asymptotic physical law.  It therefore strengthens the common
principle---persistent carrier, phase action, target quotient, record boundary---without replacing
that principle by a mixed-state-only story.
