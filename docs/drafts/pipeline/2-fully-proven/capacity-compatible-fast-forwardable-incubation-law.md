# Capacity-compatible fast-forwardable strata create complexity incubation tails

- **ID:** capacity-compatible-fast-forwardable-incubation-law
- **Stage:** 2 -- fully proved on paper
- **Type:** theorem / static-local complexity onset / fast-forwarding singularity
- **Parents:** ../3-formalized/fast-forwardable-stratum-codimension-obstruction.md,
  ../3-formalized/weak-interaction-recurrence-singularity-law.md,
  cubic-phase-seeded-static-local-full-scale-plateau-law.md
- **Status:** [PAPER-PROVED] [FRONTIER ADVANCE] [NOVELTY UNVERIFIED] [LEAN DEFERRED]
- **Date:** 2026-08-09

## Public sentence

A local quantum system can already possess maximal eventual complexity, maximal spectral
independence, and strong coupling across every spatial cut while remaining efficiently reproducible
for as long as desired. Every suitably visible fast-forwardable model contributes a
delayed-but-eventually-complex lower tail whose forced power is its codimension.

## 1. Abstract incubation theorem

Let \(X=S^{m-1}\) be a unit coefficient shell with normalized surface measure \(\sigma\), and let

\[
 H:\mathbb R^m\longrightarrow\operatorname{Herm}(\mathcal H_D)
 \tag{1}
\]

be real-linear with

\[
 \|H(x)-H(y)\|_{\rm op}\le L_H\|x-y\|_2.                       \tag{2}
\]

Let \(F\le\mathbb R^m\) have dimension \(f\), put \(d=m-f\), and let
\(P\subset F\cap X\) be a positive-measure compact patch. Denote by
\(\mathcal N_r(P)\) its Euclidean \(r\)-neighbourhood in \(X\).

Fix a finite seed family \(\mathcal Q\), circuit errors

\[
 0\le\eta<\epsilon_-<\epsilon_+<1,                              \tag{3}
\]

and a finite gate alphabet. Suppose the following independently checkable certificates are given.

1. **Uniform carrier compiler.** There is \(B<\infty\) such that for every
   \(y\in P\), every \(\chi\in\mathcal Q\), and every real \(t\),
   \[
    C_\eta(e^{-itH(y)}\chi)\le B.                               \tag{4}
   \]
2. **Basis-uniform capacity seeds.** For every orthonormal basis \(e\) of
   \(\mathcal H_D\), at least a fraction \(1-\beta\) of the seeds obey
   \[
    \sum_{j=1}^D|\langle e_j,\chi\rangle|^4\le {c_0\over D}.    \tag{5}
   \]
3. **Generic physical completion.** A conull subset \(G\subset X\) has simple spectrum,
   maximal projective rational rank, and cyclicity for every seed in \(\mathcal Q\). The fixed
   local two-query non-Haar separator applies to every \(H(x)\) in the family.
4. **Completed-phase capacity.** The existing collision-to-capacity theorem at errors
   \((\epsilon_-,\epsilon_+)\) turns (5) into depth
   \[
    s_D\ge c_1D/\log M_n                                      \tag{6}
   \]
   on a continuous block of length at least \(\exp(c_2D)\), followed by projective recurrence.

Items 1--4 are certificate data, not conclusions disguised as assumptions. Item 1 is a concrete
compiler on a named carrier, item 2 is a finite moment statement, and items 3--4 are already proved
generic spectral and completed-phase laws.

### Theorem A -- codimension incubation law

For every \(L>0\), put

\[
 r_L=\min\left\{r_0,\ {\epsilon_- -\eta\over2L_HL}\right\},     \tag{7}
\]

where \(r_0>0\) is any radius on which nearest-point directions into \(P\) remain inside the
chosen patch. Then one seed \(\chi_L\in\mathcal Q\) satisfies

\[
\begin{aligned}
\sigma\Bigl\{x\in\mathcal N_{r_L}(P):\;&
 C_{\epsilon_-}(e^{-itH(x)}\chi_L)\le B\quad(0\le t\le L),\\
&H(x)\text{ later has the plateau (6) for }\exp(c_2D)\text{ time},\\
&H(x)\text{ later recurs and is locally non-Haar for every time}
\Bigr\}\\
&\ge (1-\beta)\,\sigma(\mathcal N_{r_L}(P)).                   \tag{8}
\end{aligned}
\]

Moreover there are \(a_P>0\) and \(r_P>0\), depending only on the finite-dimensional patch, such
that

\[
 \boxed{
 \sigma(\mathcal N_r(P))\ge a_Pr^d\qquad(0<r\le r_P).}         \tag{9}
\]

Consequently, for all sufficiently large \(L\),

\[
 \boxed{
 \Pr\{\text{easy through }L\text{ but later full plateau and recurrence}\}
 \ge A_P(1-\beta)L^{-d}.}                                      \tag{10}
\]

The guaranteed contribution has transverse-codimension exponent \(d=m-f\). No claim is made that
this is the complete delay distribution or its sharp exponent after all delayed sectors are united.

### Proof

Fix \(x\in\mathcal N_{r_L}(P)\) and choose \(y\in P\) with
\(\|x-y\|_2\le2r_L\). Duhamel's formula gives, uniformly for \(0\le t\le L\),

\[
\begin{aligned}
\|e^{-itH(x)}-e^{-itH(y)}\|_{\rm op}
&\le t\|H(x)-H(y)\|_{\rm op}\\
&\le 2LL_Hr_L\le\epsilon_- -\eta.                              \tag{11}
\end{aligned}
\]

The carrier circuit (4), applied to the same seed, therefore prepares
\(e^{-itH(x)}\chi\) to error \(\epsilon_-\) with at most \(B\) gates. This proves the first line
inside (8) for every seed.

For each \(x\), apply (5) to an eigenbasis of \(H(x)\). Average its indicator first over
the finite seed family and then over \(x\in\mathcal N_{r_L}(P)\). Fubini gives one fixed seed
\(\chi_L\) for which the collision-good Hamiltonian subset has relative measure at least
\(1-\beta\). Removing \(X\setminus G\) changes no measure. On the remainder, maximal
projective rank and cyclicity give completed phase equidistribution and recurrence; item 4 gives
the continuous full plateau, and the local separator is time-uniform. This proves (8).

For (9), decompose a uniform shell point into \(F\oplus F^\perp\). The squared norm \(U\) of its
transverse projection has law

\[
 U\sim\operatorname{Beta}(d/2,f/2).                            \tag{12}
\]

Conditional on \(U\), the direction of the \(F\)-projection is uniform on \(F\cap X\).
Restrict that direction to a compact positive-measure subset of the interior of \(P\), and
restrict \(U\le r^2/4\). The beta density is bounded below by a positive multiple of
\(u^{d/2-1}\) on a sufficiently short interval. Integration gives \(a_Pr^d\). Combining with
(7)--(8) proves (10).

No inverse theorem is claimed: other delayed sectors may exist. Equation (10) is the universal
forced contribution of every independently certified capacity-compatible fast-forwardable patch.

## 2. Ordinary nearest-neighbour instantiation

Put \(D=2^n\) and use the full one-site plus nearest-neighbour two-site Pauli shell

\[
 m=3n+9(n-1)=12n-9.                                            \tag{13}
\]

Let \(F_{\rm diag}\) be the diagonal path subspace

\[
 H_0(a,b)=\sum_{i=1}^n a_iZ_i+\sum_{i=1}^{n-1}b_iZ_iZ_{i+1}.   \tag{14}
\]

It has dimension

\[
 f=2n-1,\qquad d=m-f=10n-8.                                   \tag{15}
\]

Choose a compact positive-measure patch \(P_n\subset F_{\rm diag}\cap S^{m-1}\) on which

\[
 |b_i|\ge {b_0\over\sqrt n}\qquad(1\le i<n)                   \tag{16}
\]

for a numerical \(b_0>0\). Concretely, take a spherical ball of Euclidean radius
\(\rho/\sqrt n\), for fixed sufficiently small \(\rho>0\), around the normalized all-positive
coefficient vector. Then (16) holds and its normalized \((f-1)\)-sphere measure is at least
\(\exp[-O(n\log n)]\).

Take the complete cubic-phase family

\[
 \chi_h=D^{-1/2}\sum_{z\in\{0,1\}^n}\exp(2\pi ih(z)/8)|z\rangle. \tag{17}
\]

Every seed has exact preparation cost \(O(n^3)\). Since all terms in (14) commute,
\(e^{-itH_0(a,b)}\chi_h\) is prepared by that seed circuit followed by \(n\) one-qubit
\(Z\)-rotations and \(n-1\) two-qubit \(ZZ\)-rotations. Uniform finite-alphabet compilation gives

\[
 B_n(\eta)=O\!\left(n^3+n\log^c(n/\eta)\right)                 \tag{18}
\]

for a gate-set constant \(c\), independently of \(t,a,b\). Thus (4) is a literal compiler, not
membership in an easy set.

The cubic-phase collision theorem gives, for every possibly entangled eigenbasis,

\[
 \Pr_h\left\{
 \sum_j|\langle e_j,\chi_h\rangle|^4>{2+\kappa\over D}
 \right\}
 \le {96\over\kappa^2D}.                                      \tag{19}
\]

Hence \(\beta=96/(\kappa^2D)\). Generic maximal projective rank and simultaneous cyclicity are
conull in the path-local shell. All abstract certificates are therefore present.

### Theorem B -- fully coupled sleeping-chaos family

For fixed errors and every sufficiently large \(n\), every sufficiently large prescribed delay
\(L\) admits one fixed cubic-phase seed \(\chi_{n,L}\) and a shell subset
\(\mathcal I_{n,L}\) satisfying

\[
 \boxed{
 \sigma(\mathcal I_{n,L})
 \ge A_n\left(1-{96\over\kappa^2D}\right)L^{-(10n-8)}.}        \tag{20}
\]

Every \(H\in\mathcal I_{n,L}\) simultaneously obeys:

1. \(C_{\epsilon_-}(e^{-itH}\chi_{n,L})\le B_n(\eta)\) for every \(0\le t\le L\);
2. its projective spectral rank is \(D-1\);
3. its seed collision is at most \((2+\kappa)/D\);
4. its later complexity exceeds \(cD/\log M_n\) continuously for \(\exp(cD)\) time;
5. it later recurs to the easy seed;
6. the fixed local two-query protocol separates its propagator from Haar randomness for every
   real time;
7. every spatial edge remains quantitatively coupled:
   \[
    \boxed{
    \min_{1\le i<n}\|V_i(H)\|_{\rm op}\ge {b_0\over2\sqrt n}.}  \tag{21}
   \]

### Proof

Apply Theorem A to \(F_{\rm diag}\) and \(P_n\). The operator Lipschitz bound

\[
 \|H(x)-H(y)\|_{\rm op}\le\|x-y\|_1\le\sqrt m\,\|x-y\|_2       \tag{22}
\]

allows \(L_H=\sqrt m\). For large \(L\), the radius (7) also obeys
\(3r_L\le b_0/(2\sqrt n)\). On edge \(i\), the diagonal centre has interaction
\(b_iZ_iZ_{i+1}\), while the complete nine-coefficient perturbation has operator norm at most
three times its Euclidean norm. The reverse triangle inequality and (16) prove (21).
Equations (15) and (19) turn (10) into (20). The remaining items are precisely the
generic-completion conclusions already assembled in Theorem A.

The dimension dependence hidden in \(A_n\) is controlled. The radius-\(\rho/\sqrt n\) spherical
patch above has measure at least \(\exp[-O(n\log n)]\). In the beta integral (12), both parameters
are linear in \(n\), so its normalization contributes \(\exp[O(n)]\); replacing \(r\) by
\((2L_HL)^{-1}(\epsilon_- -\eta)\), with \(L_H=\sqrt m\), costs a further
\(m^{-d/2}=\exp[-O(n\log n)]\). Hence, for fixed errors,

\[
 A_n\ge \exp[-O(n\log n)].                                    \tag{23}
\]

At Brown delay \(L=D/\operatorname{poly}(n)\), equation (20) has logarithm

\[
 -(10\log2)n^2+O(n\log n),                                    \tag{24}
\]

so this conductance-good incubation sector has probability \(\exp(-\Theta(n^2))\). It is smaller
than the weak-cut \(L^{-9}\) sector but survives after weak cuts are excluded.

## 3. Exact frontier correction

The following successively stronger onset conjectures are now false.

### C0 -- spatial conductance is sufficient

[FALSIFIED]. The Lean-proved gapped-eigenstate box retains nonzero path interactions while the
chosen eigenstate has zero-gate complexity for every time.

### C1 -- conductance plus optimal collision is sufficient

[FALSIFIED]. The diagonal carrier (14) has strong coupling on every edge and every cubic seed has
computational-basis collision exactly \(1/D\), yet its whole orbit has the compiler (18).

### C2 -- conductance, optimal collision, and maximal projective rank are sufficient

[FALSIFIED]. Every Hamiltonian in \(\mathcal I_{n,L}\) has all three properties and still has
arbitrarily prescribed polynomial-complexity incubation.

### C3 -- any qualitative chaos checklist fixes onset

[FALSIFIED AS A REPRESENTATION]. Dense or conull exact properties hold arbitrarily close to the
certified carrier. Duhamel continuity preserves the carrier's finite-time compiler while those
properties can change discontinuously. No finite list of such qualitative labels can supply a
dimension-uniform onset deadline.

### Positive survivor

For each independently certified fast-forwardable patch \(P\) compatible with the seed's full
spectral capacity, there is a load-bearing quantitative distance. Define the non-circular patch
condition number

\[
 \tau_P(H)
 ={1\over L_H\,\operatorname{dist}(H,P)}.                     \tag{25}
\]

It uses a separately supplied compiler on \(P\), never the unknown minimal circuit of \(H\).
Theorem A proves that \(\tau_P\) lower-bounds onset up to the fixed error margin, and (10) proves
that this patch contributes the carrier-codimension power to the delay tail.

This condition is not claimed sufficient. Nor is a union over “all carriers” defined: doing so
would reproduce the circular inverse-classification problem already retired. The exact consequence
for the Brown programme is narrower and testable. Any proposed shell theorem must name its
exceptional sets and pay, at minimum, both the weak-cut tube and the diagonal-carrier tube at their
proved codimension scales before attacking geometric-skeleton Bellman escape on the complement.
That target is strictly sharper than conductance conditioning and is not killed by the diagonal
family, but it is not yet a sufficiency theorem.

## 4. Relation to prior work and novelty boundary

- [LOCAL-RESEARCH] [LEAN-PROVED]
  fast-forwardable-stratum-codimension-obstruction proves that an \(f\)-dimensional uniformly
  synthesizable coefficient stratum forces an \(L^{-(m-f)}\) shortcut floor. Theorem A does not
  reclaim that Duhamel/codimension mechanism. Its candidate new content is that, when the same
  carrier is capacity-compatible, almost the entire generic transverse tube consists of systems
  that are easy through \(L\) **and later attain the full plateau, recurrence, and non-Haar
  locality simultaneously**.
- [LOCAL-RESEARCH] [LEAN-PROVED]
  weak-interaction-recurrence-singularity-law proves that arbitrarily weak interactions can
  change completed recurrence while bounded-time observables remain close. The present theorem
  upgrades the completed side to near-maximal circuit complexity and gives the codimension tail.
- [LITERATURE] Atia and Aharonov prove that commuting local and quadratic fermionic Hamiltonians
  can be fast-forwarded and connect fast-forwarding to precise energy measurement. The carrier
  compiler itself is therefore known, not novel.
- [LITERATURE] Gu, Somma and Sahinoglu enlarge the positive fast-forwarding classes. Their results
  do not state a delayed-yet-full-complexity transverse-tube law.
- [LITERATURE] Balasubramanian, DeCross, Kar and Parrikar give an eigenstate-complexity condition
  ensuring local minimality of a Nielsen geodesic for exponential time. They do not prove the
  fixed-resolution, nonuniform state-circuit law (8)--(10).

No located primary source states the conjunction (20)--(21). Search absence is not proof of
priority; the result remains [NOVELTY UNVERIFIED] pending specialist review.

Primary sources:

- Y. Atia and D. Aharonov, *Fast-forwarding of Hamiltonians and exponentially precise
  measurements*, [arXiv:1610.09619](https://arxiv.org/abs/1610.09619).
- S. Gu, R. D. Somma and B. Sahinoglu, *Fast-forwarding quantum evolution*,
  [arXiv:2105.07304](https://arxiv.org/abs/2105.07304).
- V. Balasubramanian, M. DeCross, A. Kar and O. Parrikar, *Quantum complexity of time evolution
  with chaotic Hamiltonians*, [arXiv:1905.05765](https://arxiv.org/abs/1905.05765).

## 5. Hostile audit

1. The theorem proves a lower tail of delayed onset, not the Brown upper escape bound.
2. The diagonal carrier is integrable and the transverse tube is fine-tuned. Equation (20)
   quantifies that tuning rather than hiding it.
3. The fixed seed may depend on \(n,L\). It is not resampled in time, but no single explicit seed
   is claimed uniformly over all delays.
4. Exact maximal projective rank is a fragile arithmetic property, not conventional many-body
   chaos. The theorem's point is precisely that qualitative completed-time properties cannot set
   a finite-time clock.
5. The abstract law is one-sided. It does not classify every fast-forwardable or delayed family,
   and it avoids the circular inverse theorem already retired in
   autonomous-shortcut-free-energy-law.md.
6. Scientific novelty lies only in the capacity-compatible composition and its ordinary-local
   instantiation. Duhamel continuity, commuting compilation, beta tubes, and fast-forwarding are
   established mechanisms.
7. No final-paper claim is authorized before exact Lean formalization and axiom audit.

## 6. Lean realization after corpus refactor

Reuse rather than rebuild:

1. HTGeometry/FastForwardableStratumCodimension.lean for Duhamel tube transport;
2. cubic-phase collision modules once their parent card reaches Stage 3;
3. path-local maximal-projective-rank and cyclicity modules;
4. completed phase plateau, recurrence, and local-separator modules;
5. add only finite Fubini seed selection, shell beta-tube specialization, diagonal compiler
   certificate, and final conjunction.

No Lean source or process was touched during the active refactor.
