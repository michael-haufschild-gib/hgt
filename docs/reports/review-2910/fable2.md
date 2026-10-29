# Fable 2 — consolidated big-picture report on the RH programme (revised)

Status: 29 October 2026, revised after comparison with the OpenAI report `astra.md`. Inputs: the frontier map, the killed-routes ledger, the route-unification ledger, the route-obstacles report, the walls ledger, the 47 programme READMEs listed in `docs/reports/research-programmes.md` (read oldest to newest), targeted searches of the Lean corpus with `scripts/formal_tools.py research`, and, for every number quoted in this revision, the Lean statement itself. No builds, no web, no audits of other agents' work. Evidence labels **[L]** (Lean statement read), **[S]** (README or ledger claim not re-read in Lean), **[E]** (external), **(inference)** (a conclusion of this report that is not a corpus theorem). Working log: `logs/fable2-research-2026-10-29.md`.

## 0. Answers at a glance

1. **Circumvent or destroy a wall.** The walls cannot be circumvented: the deciding-input theorem forces every RH proof to contain a parity-breaking, square-root-precise, aperture-unbounded statement about $\Lambda$. They can be destroyed from two sides. The nearest concrete mechanism is a complete operator estimate at one fixed macroscopic overlap ($c=3/2$ or $c=2$) built from the exact successor shells and the conductor-uniform cyclotomic curvature floor, with the Schur cost of the paid block retained. The deeper one is a point-side producer of a one-sided count. Neither is proved; both have first lemmas that are finite problems.
2. **Wildly different route.** None with an independently justified producer. Theta/signature forcing and reflection positivity of the Cayley–Li ladder on $\mathbb N\rtimes\mathbb N^\times$ are the two directions that would supply the input through structure rather than estimate; both reduce to an arithmetic Herglotz theorem. Lee–Yang, transfer operators, Gowers norms, finite-support computation and typicality are either already obstructed by theorem or reduce to a known wall.
3. **Quasi-RH beyond $(1/8,7/8)$.** No fixed strip is proved in the corpus; $7/8$ is an external claim whose local intake has no capstone. The corpus gives exact targets: strip $[1-\theta,\theta]$ is equivalent to a Cesàro energy bound $\mathcal E(N)\ll N^{2\theta+\varepsilon}$ and to a one-dyadic-multiplier escaped-Möbius saving; the detector budget of the external method admits $5/6$ only if both nonunit Gram terms improve ($\nu\le1/15$, $\kappa+4\nu\le4/3$) and never reaches $3/4$ (floor $29/36$). The first strip, not its value, is the problem.
4. **$75\%$ on the line.** The best receiver is the bandwidth-$4/3$ certificate $N_0^{\rm s}\ge(29/36-o(1))N-S$: a surplus $S\le bN$ buys $29/36-b$, so $b\le1/18$ gives $3/4$ (and $b\le19/180$ gives $70\%$). The surplus is an exact Ramanujan model plus a centred discrepancy; if the model's limit is the Hardy–Littlewood value $-1/144$, the discrepancy may be as large as $N/16$. The required arithmetic is the signed, parity-retained prime-pair correlation at shifts $h\asymp n/T$ up to $T^{1/3}$, which is pair correlation of zeros beyond $\alpha=1$ in prime language. No present input establishes it.
5. **Three questions.** (i) Complete positivity at one macroscopic overlap, with the cyclotomic/affine shell calculus and the remote flip $\omega_p$ as diagnostic. (ii) The signed coalescent discrepancy within the $1/16$ allowance. (iii) A producer of a one-sided count at some power precision $\theta<1$ from the factorial identity and the Nair lattice, i.e. the first fixed strip.
6. **The field.** An effective index theory of Hermitian kernels on $\mathbb Q_{>0}$ with precision classes: the index of the Weil kernel computed from local constituents and one produced count, with a signed symbol calculus for the finite-horizon operators, constrained inversion for the count, and index-carrying exhaustion for the limit.

---

## 1. Where the research stands

### 1.1 What is proven

| Area | Established | Grade |
|---|---|---|
| Census | Simple critical zeros: $N_{0,\rm simple}(0,T)\ge(0.67250071-\varepsilon)N(0,T)$ eventually, the rational just above $H_D(1)=0.6725007036\ldots$ (symbolically $H_D(1)+10^{-8}$). Zero copies within $4/\log T$ of the line: $\ge\tfrac34N(T,2T)$. Ordinates in $(T,2T]$ carrying a critical zero: $\ge(\tfrac45-\varepsilon)$ of all zero ordinates. Dichotomy: either $N_0(T,2T)\ge\tfrac34N(T,2T)$ or at least $(H_D(1)-\tfrac12-\tfrac1A-\varepsilon)N(T,2T)$ simple off-line zeros lie within $A/\log T$ of the line. | [L] on the imported `Zeta23` (Alpöge–Furman) |
| Complete Weil positivity at fixed overlap | For the plateau profile `transMetzlerProfile` and every fixed overlap ratio $c\in(0,1+\delta)$ with $\delta<\delta_*=1/107520002048050000$, the complete Weil matrix (primes, Gamma, both poles) on the atomic family of width $c/N$ at $\log n$, $n\le N$, is eventually positive definite; the certified asymptotic floor is $\tfrac1{25}-2000\delta\,K$, $K=1+1024000(2100000+\tfrac1{25})$, and $\delta_*$ is the boundary of this certificate, not a spectral transition. Beyond $c=1$ no unimodular gauge makes the atomic Markov block Metzler. The Liouville twin $\lambda\Lambda$ fails eventual nonnegativity at every fixed $c\ge\tfrac12$ (both conventions $w=c/N$ and $w=c\cdot\mathrm{atomSpacing}(N)$) and survives for $0<c\le$ `fixedWidthRatio`. | [L] |
| RH-complete receivers | RH $\iff$ eventual nonnegativity of the atomic family of one profile at overlap $c_N=N/\kappa_N\to\infty$, with the admissible growth depending on regularity: $C^2$ profiles need $c_N^{-2}\log N\to0$; second-order synthesis $c_N^{-4}\log N\to0$; $C^\infty$ profiles $c_N^{-q}\log N\to0$ for a $q$ of their choice; Gevrey-$s$ profiles $c_N/(\log\log N)^s\to\infty$; the Steklov–Denjoy–Carleman profile `steklovDCProfile` at $c_N=(\log\log N)(\log\log\log N)^\beta$, $\beta>2$. | [L] |
| Index theory | The Weil kernel $K_\zeta$ on $\mathbb Q_{>0}$ has negative index $\kappa=\#\{\rho:\operatorname{Re}\rho>\tfrac12\}$, an even number, and the restriction to the lattice of any two primes has the same index (because that lattice contains fine towers; the consecutive-integer towers $\langle(n+2)/(n+1)\rangle$ decide every tempered orbit kernel). Index zero $\iff\psi(x)-x\le C\sqrt x\log^2x$ eventually (one side) $\iff$ the upper count of the odd Liouville class $O(t)\le\tfrac12(H(t)+Ct^{1/2-\varepsilon})$. Finite index $\iff$ finitely many off-line zeros $\iff$ bounded heat counts $\iff$ all zeros above some height critical; finite index implies the Lindelöf hypothesis and a fixed zero-free half-plane. Heat-collision mass $=2(\kappa+\text{multiplicity excess})$. A positive part never pays a hyperbolic pair; bounded index is closed under pointwise kernel limits. | [L] (first three rows), [S] (last two) |
| Precision | $\mathrm{Count}(a)\iff a-1\in\mathcal Q=\{\delta:\sum_{n\le x}\delta(n)=O(\sqrt x\log^2x)\}$. The sign gauge flipping a prime set $F$ satisfies the count iff RH and $\theta_F(x)=O(\sqrt x\log^2x)$: finite flip sets pass, the set of all primes does not. Tower positivity along one prime $p$ for all $C^2$ generators holds for $\Lambda+\delta$ iff RH and $\delta=0$ on $n\ge2$; $\Lambda+1/n$ has the count iff RH and is never tower positive. Any property implying the count rejects the Liouville twin, never holds for both $a$ and $a+\varepsilon n^{-\eta}$ ($\eta<\tfrac12$), and is not finitely determined. Integrality: $\min\{\int_0^1P>0:P\in\mathbb Z[x],\deg P\le n\}=\mathrm{lcm}(1..n+1)^{-1}=e^{-\psi(n+1)}$; the Siegel and Liouville halves at scale $x^\theta$ hold for $\theta>\Theta$ and fail for $\theta<\Theta$; $\Theta<1\iff$ Siegel half at some $\theta<1$. RH $\iff$ monotone errors bounded by $1$ invert to $O(x^{1/2+\delta})$ for every $\delta>0$. | [L] |
| Selection | Harmonic-hyperplane margin exactly $2\log2$; single flips $\omega_p$ attain it exactly from $p=11$ and still fail complete Weil positivity (full-cone uniqueness); cofinite flips have gap $0$; a bounded weight $|\lambda|\le\Lambda$ eventually positive on atomic families of growing overlap is $\Lambda$; locality is twin-blind. | [L]/[S] |
| Analytic inputs | Guth–Maynard $N(\sigma,T)\ll T^{(30/13)(1-\sigma)+\varepsilon}$ on $[\tfrac12,\tfrac56]$; density hypothesis on $\sigma\ge\tfrac56$; Vinogradov–Korobov; $\mu(11/18)\le1/9$; Montgomery's $F(T^\alpha,T)/((T/2\pi)\alpha\log T)\to1$ for $0<\alpha<1$, all zeros of $\xi$ with multiplicity, no hypothesis on real parts; Newman's conjecture $\Lambda_{\rm dBN}\ge0$ (every $H_t$, $t<0$, has a non-real zero); for $0<t\le\tfrac18$ the zeros of $H_t$ with $|\operatorname{Re}z|\ge\max(X_0,2\pi e^{(2/3+\varepsilon)/t})$ are real and simple; effective Baker–Matveev $|\sum\nu_i\log p_i|\ge c(2+|\nu|_1)^{-C}$; Siegel zero-freeness for quadratic characters with an existential constant; $\zeta(\tfrac12+it)\ll|t|^{3/8}$. | [L] |
| Countermodels | Over-regular Beurling systems with regular integer counts and an off-line zero; the golden datum $1-5X+5X^2$ (index one, integral counts, functional equation); the complex fake $q=16$; a tempered single-pair configuration whose atomic form is negative at every overlap $c>0$ and every $N\ge2$ on one two-atom test; the ferromagnetic measure with $Z(t)=1+\tfrac34\cos t$ (GHS and Lebowitz hold, Lee–Yang fails). | [L] |

No fixed zero-free strip $\Theta<1$ is proven for $\zeta$ in the corpus. The Chen–Gupta–Li intake (279 modules, 1863 declarations) has detector, density and tail components and no zero-free capstone [frontier map].

A convention that matters at touching: in the Lean statements the overlap ratio is $c=Nw$ (width $w=c/N$), while the exact spacing of the lattice $\{\log n\}$ at $N$ is $\log(1+1/N)\in[\tfrac1{N+1},\tfrac1N]$. The two agree to first order; the Liouville-twin theorem is proved in both conventions.

### 1.2 Three walls, one input, two precisions

The walls ledger keeps three families (selective critical sign; transfer and exhaustion; realization and forcing). The theorems proved around them say they are one obligation seen from three sides:

1. **Transfer is solved where it can be.** Bounded index passes to pointwise limits of kernels; fine towers and two-prime lattices carry the full index; what remains of Wall 3 is overlap growth, which is Wall 1 content: the point where the separated prime error enters as the overlap grows.
2. **Realization is located.** Compressions by spectral-side auxiliaries are receivers: over $\mathbb F_q$ the characteristic polynomial annihilates the trace kernel and certifies nothing, and over $\mathbb Z$ Euler-factor compressors are index-neutral. A producer must vanish at the primes (point side). Wall 14 is a request for one object: a point-side producer of the odd class's upper count.
3. **The deciding input is a theorem.** Any property implying the count rejects the Liouville twin, is not finitely determined, and separates $a$ from $a+\varepsilon n^{-\eta}$ for every $\eta<\tfrac12$.

So every RH proof contains a parity-breaking, square-root-precise, aperture-unbounded inequality about $\Lambda$; the corpus has written this input in every currency:

| Currency | The one input | Programme |
|---|---|---|
| Count | $\psi(x)-x\le C\sqrt x\log^2x$ eventually (one side) | HKT, ASRP |
| Parity | $O(t)\le\tfrac12\big(H(t)+Ct^{1/2-\varepsilon}\big)$ for the odd Liouville class | AKL |
| Index | $\kappa(K_\zeta)=0$ | HKT |
| Positivity | atomic positivity at overlap $c_N\to\infty$ at a profile-dependent rate | SSHA, TM |
| Integrality | the Siegel half or the Liouville half at scale $\sqrt x$ | ASRP |
| Inversion | uniform monotone Möbius inversion at every exponent $\tfrac12+\delta$ | ASRP |
| Heat | collision mass $<2$ | HKT, WD |
| Escape | every escape state has positive gauge mass | ACG |
| Effectivity | $\log|\mathbb Z/\mathrm{lcm}(1..N)|=\chi(\sqrt N A)+O(\sqrt N\log^2N)$ | AET |

**The two precisions.** All rows are equivalent at $\Lambda$; as properties of weights they are not. The count sees $\Lambda$ only modulo $\mathcal Q$: finite flips, $\Lambda+1/n$ and every Euler-factor deletion of square-root mass are in its stabilizer. Tower positivity for all generators along one prime sees every coefficient. Two consequences, the first of which the earlier version of this report got wrong:

- A count route works modulo $\mathcal Q$. It need not reject a finite flip, and demanding that it do so poses a harder problem than its endpoint requires. Only a positivity claim for the perturbed weight must see the flip.
- "Two primes" is sufficiency, not necessity: the index is carried by any two primes because their lattice contains fine towers, and positivity for all generators on one prime tower already decides RH. What is necessary is unbounded aperture, not a second prime.

### 1.3 A dictionary the ledgers imply but do not state (inference)

An atomic test $f_x=\sum_{n\le N}x_n\,\varphi((u-\log n)/w)$ with $w=c/N$ has Fourier side $\hat\varphi(ct/N)\,D_x(\tfrac12+it)$ with $D_x$ a Dirichlet polynomial of length $N$; the window $\hat\varphi(ct/N)$ cuts the height at $T\asymp N/c$. Hence overlap ratio $c$ at horizon $N$ is Dirichlet-polynomial length $N$ at height $T=N/c$, bandwidth $\lambda=\log N/\log T=1+\log c/\log T$. In these terms:

- the proved positivity ($c<1+\delta_*$) is positivity of the complete Weil form at length $N<(1+\delta_*)T$: the square-root threshold $X=T$ with a certified excess of $\delta_*T$;
- the RH-complete Steklov receiver is positivity at length $N=T\,c_N$, i.e. $N/T=(\log\log N)(\log\log\log N)^\beta$;
- the census needs bandwidth $4/3$, length $T^{4/3}$, but only for a proportion.

SSHA states the Nyquist half of this ("the spacing is the Nyquist scale of the atomic family"). The square-root threshold is the one wall in every coordinate the corpus uses: Montgomery–Vaughan's diagonal, the density-hypothesis threshold, the Metzler threshold $c=1$, the aperture $a=L/2$ of SRT, the first prime-pair coalescence of TTPC. RH is the sliver between length $T$ and length $T(\log\log T)(\log\log\log T)^{2+}$.

The structure of the atomic form at overlap $c$ (inference from TM, CACT, SSHA). Per unit mass the diagonal has an $O(1)$ margin: the archimedean self-energy $\log(N/c)$ and the prime counterterm $\log N$ match with constant one. Against it stand two families of off-diagonal terms with nonnegative entries and row sums $\asymp c$ on disjoint supports: the archimedean overlaps of additive neighbours $m=n\pm j$, $j<cn/N$ (positive), and the prime successor shells $m=kn\pm r$, $k\ge2$, $r<ckn/N$ (negative). At $c<1$ no shell is present and the form is Metzler; at $c=1$ only the boundary star $(N,N+1)$ enters; at $c=3/2$ the shells $r=1$ with $kn\in(2N/3,N]$ enter; at $c=2$ the shells $r=1$ with $kn\in(N/2,N]$ plus boundary terms. Neither family can be paid in operator norm, so positivity at macroscopic $c$ is a Schur-complement balance $A-BD^{-1}B^*\ge0$ between the paid additive block $D$ and the shell block, and the $c\to\infty$ limit of the family is Weil positivity on smooth tests. The trans-Metzler proof pays the $c\le1+\delta_*$ shells from a fixed reserve ($\tfrac1{25}$ mass floor plus the strict-variance prime-defect coercivity $E\ge-2100000M+D/1024000$), which is why its range is perturbative.

---

## 2. Question 1 — a mechanism that circumvents or destroys a wall

By §1.2 "circumvent" is excluded by theorem. "Destroy" means produce the input. Six mechanisms are live; I rank them by how much of the problem they remove if they work and by how finite their first lemma is. Each is checked against the proved constraints: selectivity beyond the $2\log2$ margin, precision, non-locality, unbounded aperture, point side, no positive majorant, finite index is Lindelöf-deep.

### 2.1 M-1. Complete positivity at one macroscopic overlap from the exact shells

**What is proved.** Three CACT ingredients and the TM base case now coexist.

- *A conductor-uniform positive quantity.* For $m>1$ let $P_m(k)=\sum_{\zeta\ \text{primitive}}|\sum_{j<k}\zeta^j|^2$ and $A_m(t)=\sum_{d\mid m}\mu(m/d)d^2\{t/d\}(1-\{t/d\})$. Then $A_m(k+u)=(1-u)P_m(k)+uP_m(k+1)$ for $0\le u<1$, and $A_m(t)/\varphi(m)\ge\{t\}(1-\{t\})$ on $t\ge0$. The input is that a nonvanishing geometric prefix $\sum_{j<k}\zeta^j$ is a nonzero cyclotomic integer, so the product of its conjugates has modulus $\ge1$ and the arithmetic–geometric mean gives $P_m(k)\ge\varphi(m)$ whenever $m\nmid k$. The floor is uniform in the conductor.
- *Affine prime windows realize the unit average.* For fixed $q>0$, $n,h$, $0<A\le B$: $\sum_{AN<k\le BN}\Lambda(k)c_q(kn+h)/k\to(\log B-\log A)\,c_q(n)c_q(h)/\varphi(q)$, a source theorem with no correlation model. It gives the arithmetic eigenvalue of an affine successor average; it does not give a norm estimate when conductor, lag and coefficients move together.
- *Annular frames.* On $(A,2A]$ with $A\ge4Q(Q-1)$ the packets $F_a(n)=\sum_{m\le Q}a_m c_m(n)/\sqrt{\varphi(m)n}$ have square mass in $[\tfrac14,\tfrac54]\sum a_m^2$, and the literal prime kernel compressed to one annulus is zero (no two distinct integers there divide one another): the arithmetic transport lives between annuli. The downward prime row is an exact logarithmic divisor jet, $\sum_{a\mid n}\Lambda(a)c_m(n/a)=\log n\,c_m(n)-J_m(n)$.
- *Non-ratio lags.* At width $c/N$ the prime side of an atomic test is a sum over pairs $(n,kn\pm r)$ with $r<ckn/N$, written as a lag form (SSHA, `primeSum_atomicTest_eq_lags`, `exists_nonRatio_pair`); at $c=1$ only the boundary star enters, and it vanishes after normalization (CACT).

**The mechanism.** (1) Organize the non-ratio terms by shell $r=kn-j$ with sign, boundary terms and the actual overlap Gram retained; at bounded $c$ finitely many shells occur. (2) Compute their action on growing Ramanujan packets through the affine unit averages and the divisor jet, and combine prime, Robin, Gamma and both poles before estimating any remainder. (3) Decide whether the completed shell symbol contains $\int A_m(t)/\varphi(m)\,d\nu(t)$ with $\nu\ge0$; this identification is the open theorem, not a consequence of the scalar floor. (4) Treat cross-conductor and cross-annulus interactions as one operator: if the additive block $D$ is paid, what remains is $A-BD^{-1}B^*$, and a scalar positive symbol cannot pay an uncontrolled Schur subtraction. (5) Prove the complement estimate and a norm residual on the actual source uniformly over the packets needed at that overlap, then a full-matrix lower bound.

**Endpoints.** One explicit fixed full-support profile at $c=3/2$ (shells $r=1$ on $kn\in(2N/3,N]$) or $c=2$ (shells $r=1$ on $kn\in(N/2,N]$), with all coefficient vectors controlled. A profile whose effective width shrinks while its nominal support grows does not answer the question. A diagnostic cheaper than the Liouville test: the remote flip $\omega_p$, $p\ge11$, which has the same maximal hyperplane gap $2\log2$ as $\zeta$ and fails complete positivity; the overlap at which the complete form first separates $\omega_p$ from $\Lambda$ measures what information the fixed-ratio form carries. The corpus has no module evaluating flips on the atomic complete form (wall 1.38).

**Why it respects the constraints and why it may fail.** The sign would come from an integer norm and exact algebraic cancellation, not from an entrywise Metzler gauge (impossible beyond $c=1$) or absolute payment of every prime edge. It may fail because the cyclotomic quantity describes only a diagonal compression, or because the complement cost consumes the reserve; either failure should produce an explicit residual operator or a sharp obstruction.

**What it is not.** Fixed-$c$ positivity for every $c$ does not by itself give positivity along a prescribed $c_N\to\infty$: the horizon $N_0(c)$ may grow too fast, and bounded-overlap completeness (that *every* schedule $c_N\to\infty$ is RH-complete) is not established. The companion problem is therefore approximation theory on the lattice $\{\log n\}$: the slowest overlap at which integer-centred atoms synthesize every compact test in the Weil-continuity norm. The present synthesis (Riemann sums of one dilated profile, Lévy energy (amplitude)$^2\log N$, alias ripple $\exp(-c\varrho^{1/s})$ for a Gevrey-$s$ profile) explains the ladder of §1.1 and why the quasi-analytic boundary $s=1$ limits it; $\beta\in(1,2]$ is open. A proposal that lowers the obligation without supplying positivity: a profile with summable radii $a_m\asymp1/(m\log m(\log\log m)^{1+\eta})$ should have $\|\varphi^{(q)}\|_1\le C^{q+1}q!(\log q)^q(\log\log q)^{(1+\eta)q}$ and synthesis decay $\exp[-cR/(\log R(\log\log R)^{1+\eta})]$, pointing to schedules $c_N=L\log L(\log\log L)^\beta$, $L=\log\log N$, $\beta>1+\eta$ (proposal from `astra.md`; derivative bounds, remainder and continuity in the complete Weil norm all unproved). Two obligations attach to any schedule work: the positivity theorems are for the plateau, the sharp receiver for the Steklov profile, so either a compatible profile or a signed transfer between profiles is needed; and a schedule improvement supplies no positivity.

**Assessment.** The closest opportunity to convert established tools into a new positivity mechanism, with a measurable first theorem. If the companion completeness problem is false (a tempered finite-support model is negative at every fixed $c$, so fixed-ratio positivity cannot follow from the zero side without $\zeta$'s density), the fixed-$c$ theorem survives as a standalone result and the RH-complete axis stays at the super-Gevrey schedule.

### 2.2 M-2. A point-side producer

**Where the corpus has put the problem.** RH is the upper count of the odd Liouville class alone (one class suffices because $\zeta$ has no real zero in $(\tfrac12,1)$); over $\mathbb F_q$ that count is produced by Stepanov's auxiliary polynomial vanishing to high order at the points of a parity class, with $x^q=x$ making vanishing cheap and the twist tower completing the lower count. Over $\mathbb Z$ the identity side is built: the integrality lattice $\{\int_0^1P\}=\mathrm{lcm}(1..n+1)^{-1}\mathbb Z$ with least positive value $e^{-\psi(n+1)}$ attained; integer Dirichlet polynomials have the sharp Liouville inequality $|D(m)|\ge\mathrm{lcm}(1..N)^{-m}$ at $s=m\ge1$, integer values at $s\le0$, fewer real zeros than nonzero coefficients, and Siegel's lemma for vanishing at $0,-1,\ldots,-(M-1)$; the integrality exponent is the zero width in each half; a strip is a Siegel half at a power $\theta<1$. Precision is lost in two places only: the ceiling (an analytic certificate that a nonzero integral is small) and Möbius inversion. For inversion the corpus is sharp: the operator $I_x(E)=\sum_{k\le x}\mu(k)E(x/k)$ is unbounded on every size class, monotone errors invert at exactly Mertens precision, and $\psi(n)=I_n(F)+I_n(G)+I_n(h)$ with $F=y\log y-y$, $G$ a monotone Stirling remainder and $h=F(\lfloor y\rfloor)-F(y)$ a sawtooth of amplitude $\log y$. Sup-norm ceilings at precision $\theta<1$ must vanish at $0,\tfrac12,1$ (Stepanov-like), and the integer Chebyshev constant blocks sup-norm auxiliaries below linear precision.

**The mechanism, in two realizations.** (a) *Constrained inversion.* Generic size control on $E$ does not survive inversion with sublinear precision and monotone control gives Mertens precision; the new theorem must use the joint constraints among $F,G,h$ (they sum to $\log\lfloor y\rfloor!$ exactly) before separating them into absolute bounds. First milestone: the precision at which the sawtooth $h$ cancels against $\mu$ below linear size (ASRP's open problem). (b) *Arithmetic Stepanov.* An auxiliary in $\mathbb Z[\mathbb Q_{>0}]$ with $p$-adic multiplicity $\ge2$ on a positive proportion of counted primes above $\sqrt x$ and size $\log|A|=O(x)$, certified by an identity rather than a sup norm; the Bézout ledger $\sum_pm_p\log p\le\log A$ is proved, binomial auxiliaries are capped at multiplicity one above $\sqrt N$ by $p^m\mid\binom Nk\Rightarrow p^m\le N$. Missing: the zero estimate (a nonzero integer Dirichlet polynomial of length $N$ and height $H$ cannot have $p$-adic multiplicity $\ge m$ at more than $O(\log(NH)/(m\log p))$ primes) and the flatness identity playing $x^q=x$; Fermat and Kummer–Legendre are the candidates the ledger uses implicitly (inference).

**Why it respects the constraints.** It acts at the ring level (only the ring level excludes the golden datum and Beurling systems); it is parity-visible because the twin's horizon value is a reciprocal group order $e^{A_\lambda(n)}=1/r_n$, $r_n=d_n/d_{\lfloor\sqrt n\rfloor}^2\in\mathbb N$; its aperture is the degree; it is a count, hence a producer.

**Target.** Any one-sided $\psi(x)-x\le Cx^\theta$ or $\ge-Cx^\theta$ with $\theta<1$ without assuming a Mertens bound, an RH-equivalent sign or a small integral. By the dictionaries it is a strip; its square-root version is RH. A count route works modulo $\mathcal Q$ (§1.2), which is the correct, weaker quotient.

**Assessment.** The only mechanism attacking the wall where the corpus proved it must be attacked, and the hardest: its first rung (beat the sieve parity constant $2$ in intervals of length $x^\varepsilon$, or any fixed $\theta<1$) is a classical open problem.

### 2.3 M-3. The characteristic circle: a covariant regulator with a null cone

AIT shows that on $\mu_\infty$ with power maps as correspondences Weil's ingredients are integral: intersection numbers are log-orders of finite rings, the projection formula holds, the self-intersection of $O_n$ is the discriminant of $\mathbb Q(\zeta_n)$. The diagonal exists only after a regularization that is not Hecke-covariant (cocycle $\beta(n,t)=\log t-\sum_{p\mid t,p\nmid n}\log p/(p-1)$). RAPT shows the horizon regulator is covariant with scalar counterterm $\log N+O(1)$, constant one, and that torsion renormalization costs $\varphi\log N$; RBG shows positivity passes a scale limit exactly on the null cone of the counterterm, with the archimedean germ surviving on the polar hyperplane and the torsion germ nowhere. The mechanism is a Hecke-covariant regulator with a nontrivial null cone (AIT open 1) plus an arithmetic Riemann–Roch on torsion orbits with defect $\tfrac12\log|d|$ (AIT open 3); AES states the target as a Hodge index theorem with adjunction (equilibrium computed, stability is the sign). It is the one place where integers enter as intersection numbers. Its weakness: rotations localize in the additive dual $\mathbb Q/\mathbb Z$ while zeros live in the multiplicative dual and enter only through the hyperbolic Hecke maps.

### 2.4 M-4. A prime-side ceiling for the Hecke defect at $L\asymp\log T$

The collided form $D(f)=\sum m_\rho|\hat f(\rho)|^2$ is positive by construction and computed from arithmetic in the limit by theta-prefix source currents; its second difference $D(T_Lf)+D(T_{-L}f)-2D(f)=\sum m_\rho(2\cosh(2\delta_\rho L)-2)|\hat f(\rho)|^2$ is a positive measure of off-line depth and at $L\asymp\log T$ a weighted zero-density statistic (CDG). The open input is a prime-side upper bound. It touches three strata at once: the census dichotomy puts every failure of $3/4$ into $\ge(H_D(1)-\tfrac12-\tfrac1A)N$ simple off-line zeros within $A/\log T$, a configuration with defect $\asymp A^2N$ per unit mass at $L=\log T$; finite support is a uniform bound on the defect's growth; RH is its vanishing (inference). Its prime side reads primes up to $T$: the square-root threshold again.

### 2.5 M-5. Compatibility at relative precision $1/T$

ACCE shows that admission of the damped Möbius receiver below damping $\tfrac12$ is prime-pair cancellation at relative precision $1/T$, that both ends of the damping range are paid and escape is an interior bump at $n\gtrsim2^{1/\varepsilon}$, and that after the square-root head the whole obligation is the long-modulus Möbius quadrature. ACCC proposes the compatibility of the prime-dilation and Möbius-dilation descriptions of one tangent as a constraint. A legitimate estimate-hunting ground that supplies no parity breaking by itself; it must be combined with gauge-charged inputs (successor, cells).

### 2.6 M-6. The polar divisor of positive-genus affine Eisenstein series

Over $y^2=x^3-x$ / $\mathbb F_3$ the affine $A_1$ Gindikin–Karpelevich coefficients have poles at the Frobenius zeros with full multiplicity, the poles survive the regularized Weyl sum, and pole detection is exact even for impure data; the golden datum has an off-line pole with the same calculus (ISC-polar). The missing confinement principle would be an arithmetic constraint on the polar divisor from the infinitely many functional equations of a Kac–Moody Eisenstein series. The only live idea using an infinite symmetry group; the golden counterexample says the constraint must be arithmetic, not formal. Exploratory.

### 2.7 Verdict, and what would not break the wall

No mechanism circumvents the walls. M-1 and M-2 would destroy the wall from the two sides the corpus has shown are the only ones (positivity language for selection, count language for production); M-1 has the finite first lemma. M-3 is the deepest structural direction, M-4 the cleanest one-sided census target, M-5 and M-6 are supporting.

Theorems that filter new proposals: every approach reading prime information through interval statistics with $o(1)$ relative error; every positive majorant (a positive part never pays a pair); every local tower statement (twin-blind); every multiplicative-only construction (Beurling systems satisfy every multiplicative identity); every tensor or family amplification over $\mathbb Z$ (depth-homogeneous); every finite-aperture certificate (width limit $\tfrac12$). Also not a wall-breaker on its own: a better scalar overlap constant; another width/index equivalence; retaining almost all Gamma after a fixed detail head (the full nonfirst source does, without paying the complete first-prime source); and "finite complete index", which is RH above a height plus Lindelöf and so a major theorem rather than a bridge.

---

## 3. Question 2 — approaches wildly different from everything so far

A proof cannot avoid the deciding input. An approach can differ in where it gets it. The corpus's own classification is sharp: estimates lose precision; structure (an identity, a count, a positivity by construction) is the only known way precision has been kept, over $\mathbb F_q$ and on $\operatorname{Re}s=1$.

**W-a. Theta series of the intersection lattice and signature from a transformation law.** The Weil form on $\mathbb Z[\mathbb Q_{>0}]$ (integer Dirichlet polynomials) under RH has exactly one positive square in the intersection convention (ACS signature law: positive squares $=1+$ negative squares). For integral lattices the signature mod $8$ is a finite Gauss sum (Milgram) and indefinite theta series of signature $(1,n)$ have a transformation law once a positive cone vector is chosen (Siegel, Zwegers). The approach: a theta series $\sum_Pe^{-\pi W(Pf,Pf)}$ over a growing horizon whose Poisson law comes from the prime side (the explicit formula is itself a Poisson pair, APD), with the rank of the positive part read from the law. *Obstruction to evade:* the form is neither integral nor of finite rank and $\kappa$ is even, so a mod-$8$ invariant cannot pin $\kappa=0$; the full modular weight at each height truncation would be needed. *Merit:* positivity as a consequence of a self-duality, the one forcing pattern the corpus has seen work (APD: positivity plus exact self-dual identity plus an integer gives rigidity).

**W-b. Reflection positivity of the Cayley–Li ladder by construction.** RH is reflection positivity of the Cayley ladder, equivalently the Metzler sign of the Li ladder (ALG). Osterwalder–Schrader positivity holds by construction from a positive transfer operator or Markov semigroup; ALG names the carrier (KMS states of $\mathbb N\rtimes\mathbb N^\times$ with the reflection $\beta\mapsto3-\beta$), APD has the Bost–Connes temperature as the Hecke exponent and affine positivity induced from dilations. *Obstruction to evade:* the identification of the constructed functional with the actual Li ladder must not use the zeros, or it is a receiver. The content is an arithmetic Herglotz theorem: a positive measure on the circle built from primes and the successor whose moments are explicit-formula values (ACountP open). The most concrete wild idea: Hilbert–Pólya in Cayley coordinates with a noncommutative, additive carrier.

**W-c. Transfer operators (inference from classical facts).** Mayer writes the Selberg zeta function of the modular surface as $\det(1-L_s)\det(1+L_s)$ for the Gauss-map transfer operator, and the zeros of $\zeta(2s)$ appear through the scattering determinant at $s=\rho/2$. Dolgopyat-type arguments give resonance-free strips near the pressure line $\operatorname{Re}s=1$, i.e. $\operatorname{Re}\rho=2$: the dynamical gap reproduces the Euler-product region and nothing else. A dynamical system whose pressure line is the critical line is not known. Recorded so the route is not reopened.

**W-d. Fourier quasicrystals and Lee–Yang.** The corpus has the receiver (phase-normalized Ising limits to Riemann's law force RH; the centering law forces total field $\Lambda_n\to\infty$ with $\Lambda_n-2\beta_n$ convergent) and three no-gos: constant-normalized ferromagnetic Ising partition functions cannot converge locally uniformly to a zero-free entire factor times $\Xi$; the ferromagnetic inequalities (GHS concavity of the magnetization, negative fourth cumulant) hold for Riemann's measure unconditionally and do not imply Lee–Yang (the measure $\delta_0+\tfrac38(\delta_1+\delta_{-1})$, $Z(t)=1+\tfrac34\cos t$, satisfies both and has $Z(\pi+iy)=0$ at $\cosh y=4/3$, with Gaussian smoothing preserving the zero); local factors are Lorentzian only at the Weil bound, never at a prime (ALG). A producer must be a stable polynomial on the Bohr torus that does not factor over primes; the Euler product is the wrong start, and the natural object is W-b's carrier seen as a polynomial.

**W-e. Arithmetic topology.** Primes as knots, $\operatorname{Spec}\mathbb Z$ as a 3-manifold, log-torsions as Reidemeister torsion; AET already reads $\psi(N)=\log|\mathbb Z/\mathrm{lcm}(1..N)|$ as a log-torsion. A 3-manifold has no Hodge index theorem; the needed object is a surface with a quadratic Euler characteristic, and AET shows the base theta $h^0$ never extends (the box class $\sqrt NA$ has $\chi=N$, the dimension of Dirichlet polynomials of length $N$). Alive only as M-3/AET.

**W-f. Higher-order Fourier analysis.** Gowers norms, nilsequence orthogonality, Matomäki–Radziwiłł-type short-interval results and every almost-all statement are precision-blind by theorem: stable under $\Lambda\to\Lambda+\varepsilon n^{-\eta}$. They cannot decide.

**W-g. Typicality of the arithmetic gauge point.** Square-root cancellation holds Haar-almost everywhere on the gauge torus, fails at the Liouville twin, is RH at the arithmetic point; the exceptional set is null and comeager (ACG). A typicality proof must use a gauge-charged (additive) relation that no finite-precision information about prime phases contains. No mechanism places a specific point outside a comeager null set except an identity it satisfies.

**W-h. Computation plus an effective finite-support theorem.** Finite support with an effective height below the verified height would give RH, and verified-height amplifiers exist (`RHVerifiedThrough`). But finite support is RH above a height and implies Lindelöf: RH-hard exactly where verification stops.

**Summary.** W-a and W-b deserve cards; both reduce to an arithmetic Herglotz theorem, the structural form of the deciding input. A new idea earns a route when it supplies a source-built inequality with a proved transfer, a new invariant computed from arithmetic that forces the sign, or a faithful approximation by independently signed objects with complete-form convergence proved. A novel object with its deciding property assumed is a candidate, not a mechanism.

---

## 4. Question 3 — quasi-RH beyond $\tfrac18<\operatorname{Re}\rho<\tfrac78$

**Status.** No fixed strip is proven in the corpus. The $7/8$ claim is external [E]; its intake has detector, density and tail components and no capstone, and the frontier records its detector floor $288$ against the collision quantum $2$ as blocking an RH endpoint but not the $7/8$ claim. Unconditional strip-type facts: Vinogradov–Korobov, the density hypothesis on $\sigma\ge5/6$, Guth–Maynard $30/13$, $\mu(11/18)\le1/9$, Siegel zero-freeness for quadratic characters, $\Lambda_{\rm dBN}\ge0$, and heated-zero reality above $2\pi e^{(2/3+\varepsilon)/t}$. The density-envelope theorem: no bound $N(\sigma,T)\ll T^{\theta(1-\sigma)}(\log T)^A$ forces a zero-free region, at $30/13$ as at $8/3$.

**Exact targets.** With $\Theta=\sup\operatorname{Re}\rho$, $S(M)=\sum_{2\le n<M}(\psi(n)-n)/\sqrt n$ and $\mathcal E(N)=\sum_{2\le M\le N}(S(M)/M)^2$, the infimum of admissible energy exponents is exactly $2\Theta$:

| Closed strip | Sufficient one-sided bound | Energy target ($\forall\varepsilon$) | Escaped-Möbius saving |
|---|---|---|---|
| $[\tfrac18,\tfrac78]$ | $S(M)/M\ll1+M^{3/8}$ | $\mathcal E(N)\ll N^{7/4+\varepsilon}$ | $\theta=\tfrac18$ |
| $[\tfrac16,\tfrac56]$ | $S(M)/M\ll1+M^{1/3}$ | $\mathcal E(N)\ll N^{5/3+\varepsilon}$ | $\theta=\tfrac16$ |
| $[\tfrac14,\tfrac34]$ | $S(M)/M\ll1+M^{1/4}$ | $\mathcal E(N)\ll N^{3/2+\varepsilon}$ | $\theta=\tfrac14$ |
| critical line | — | $\mathcal E(N)\ll N^{1+\varepsilon}$ | $\theta=\tfrac12$ |

The $5/6$ and $3/4$ one-sided bounds may be sampled on any power mesh $M=j^m$ (still all-scale estimates). For $0<\theta\le\tfrac12$ the following are equivalent: the growing-endpoint escaped-Möbius law at $\theta$ (uniform $O_\varepsilon(((N-b)/a)^{-\theta+\varepsilon})$ over all multipliers), the single dyadic law ($a=2$, $b=0$), receiver damping rate $\le\tfrac12-\theta$, and $\Theta\le1-\theta$; uniform decay measured in $N$ over every multiplier is false, the escaped endpoint is the right scale. The seven-way theorem unites the first power-saving rung across five programmes (escaped Möbius, centred prime band, short-window prime and Möbius mean squares, damping below $\tfrac12$, $\Theta<1$). One exponent identity links this question to the census: the coalescent resonance exponent $\theta(\lambda)=(\lambda-1)/(2\lambda)$ is the strip exponent at which off-critical contributions $x^{\beta_0}$ stay below the square-root coalescent barrier at bandwidth $\lambda$ ($\beta_0\le(1+1/\lambda)/2$); $\theta(4/3)=1/8$ and $\theta(5/4)=1/10$. The $7/8$ of the external claim and the $4/3$ of the census are the same exponent relation.

**The detector budget.** The external method's exponent budget is formalized as identities on an upper-bound model (not lower bounds on energy, not zero-free theorems). With Gram profile $1+P^\nu+P^\kappa/Y$, $X=Z^x$, $Y=Z^{1-s-x}$, $P=Y/X$, $s$ the total slot length, the boundary after principal normalization and the reflected allowance is
$$B(x,s;\nu,\kappa)=\tfrac56+\tfrac{x-s}6+\tfrac12\max\big(0,\ \nu(1-s-2x),\ (\kappa-1)(1-s)-(2\kappa-1)x\big)+\tfrac12\max\big(0,\tfrac{6s-1}5\big).$$

| Change | Exact conclusion |
|---|---|
| retune scales and slot length, keep the losses | minimum stays $7/8$, uniquely at $s=1/6$; longer slots are paid back by a reflected face |
| save $\sigma$ in the exceptional Gram exponent at the original scales | boundary $7/8-\sigma/16$ |
| remove the exceptional term, keep $P^2/Y$ | optimum $23/27\approx0.852$, at $x=5/18$, $s=1/6$: still above $5/6$ |
| improve both nonunit terms | $B\le5/6$ feasible iff $\nu\le1/15$ and $\kappa+4\nu\le4/3$; witness $\nu=1/30$, $\kappa=6/5$, $x=5/48$, $s=1/6$, $Y=Z^{35/48}$ |
| remove both nonunit terms | floor $29/36>3/4$ at $x=0$, $s=1/6$ |

The published normalization is $B(17/48,1/6;1/6,2)=7/8$. A fourth-moment bound for arbitrary sets of the detector's cardinality is false (sextic characters and shift sets exceed $C|K||S|^2$ by an unbounded factor); any new bound must use the structure of the actual sets.

**What this says about "improve $7/8$".** All strips $0<\theta\le\tfrac12$ are equivalent to a power saving of the same type; the corpus lacks any producer of any power saving. Two consequences. If the external mechanism is sound, $5/6$ is a defined optimization problem (both Gram terms must improve; the exceptional term alone cannot reach it) and $3/4$ is out of reach of that mechanism (the $29/36$ floor), so $3/4$ must come from a different source bound such as the Cesàro energy. If it is not sound, the value is irrelevant. Either way the next step is the one the unification ledger lists (W10): extract the vanishing mechanism, formalize the capstone or refute it; if it holds, seven dictionaries fire at $\theta=1/8$.

**What a producer must contain (inference).** The density-envelope theorem shows a strip needs a pointwise vanishing step, not a count of large values. The mean square of $\psi(x)-x$ is dominated by its diagonal over zeros, so it tracks $\Theta$ exactly and buys nothing; the energy targets above are the receiver, not the producer. The currency in which a strip is a one-sided statement about an arithmetic object with no hidden zero sum is the escaped-Möbius law: Möbius in intervals $[x-b,x]$ with a power saving uniformly in $x$; almost-all results exist, the all-$x$ version is the strip.

**Heat flow is not a route to a strip (inference).** $\Lambda_{\rm dBN}\ge0$ is formalized, and an isolated off-line zero of depth $b$ forces $\Lambda_{\rm dBN}>t$ for $2t<b^2$ under local non-interaction; the converse fails without isolation, which is why an upper bound on $\Lambda_{\rm dBN}$ gives no strip.

**Answer.** No opportunity to prove a strip narrower than $7/8$ by a new idea is visible; the opportunity is to make the first strip real. Independent targets with the right shape: the escaped-Möbius one-sided law at some $\theta>0$, the Siegel-half ceiling at some precision $\theta<1$ (the quasi-RH form of M-2), and, inside the external method, the five-sixths Gram pair.

---

## 5. Question 4 — at least $75\%$ of zeros on the critical line

**What is established.** The census facts of §1.1. Statistics not to conflate with $75\%$ on the line: "simple or critical", ordinates carrying a critical zero ($\ge4/5$), copies within $4/\log T$ ($\ge3/4$). The dichotomy does not eliminate the near-line population; it locates it: every failure of $3/4$ is a near-line conspiracy of simple off-line zeros at depth $O(1/\log T)$ with density $\ge(H_D(1)-\tfrac12-\tfrac1A-\varepsilon)$.

**Receivers and their exact budgets.**

1. *Bandwidth $4/3$.* The diagonal, archimedean and pole constant is $\kappa(\lambda)=1/\lambda+\lambda/3$, equal to $43/36$ at $\lambda=4/3$ (minimum $4/3$ at $\lambda=1$, giving $2/3$). The smooth-window certificate is, for every admissible profile $u$ (collar $\varepsilon_1$), $\eta>0$, $\varepsilon>0$, eventually
$$N_{0,\rm simple}(T,2T)\ge\big(\tfrac{29}{36}-32\pi\varepsilon_1-\varepsilon\big)N(T,2T)-S_{u,\eta}(T)+M_{\rm off,multiple}(T,2T),$$
with the last term nonnegative. So a surplus bound $S\le bN+o(N)$ buys $29/36-b$: $b<5/36$ beats $2/3$; $b\le577/4500$ beats $H_D(1)$ (through $254/375$); $b\le19/180$ gives $70\%$; $b\le1/18$ gives $3/4$; the Hardy–Littlewood value $b=-1/144$ would give $13/16$. The surplus reduces to odd primes at even shifts within relative distance $T^{-1+\eta}$; prime powers cost $O(T^{-1/3+\eta})N$. Quantifiers are part of the target: the same window, collar and all large heights.
2. *Narrow strip $\lambda=1+\delta$.* With $E(\delta)$ the narrow-strip Cesàro energy, the proportion exceeds $2/3$ by $\delta(2-(3E-4)\delta)/(3(1+\delta)^2)$, so it beats $2/3$ iff $E(\delta)<2/(3\delta)+4/3$, and beats $H_D(1)$ (through $254/375$) iff $375\delta^2E(\delta)\le242\delta+496\delta^2-4$ (e.g. $E(0.05)\le9.96$). Under $E\le B$, $B>1$, the gain is at least $1/(3(3B-2))$ at $\delta^*=1/(3(B-1))$: $E(1/9)\le4$ gives exactly $70\%$. Under a quadratic surplus $\beta\le B\delta^2/(1+\delta)^2$ the gain is $\delta(2+(1-3B)\delta-\delta^2)/(3(1+\delta)^2)$ ($0.072$ at $B=1$, $\delta=1/5$), with a collar-preserved share. The two receivers ($4/3$ with $b\le19/180$; narrow strip with $E(1/9)\le4$) are different functionals and must be compared by arithmetic difficulty, not by coefficient size.
3. *Reflection accounting and shallow energy.* Off-line zero copies come in reflected pairs, so $N=N_0+2(R_{\rm sh}+R_{\rm deep})$ and $R_{\rm sh}+R_{\rm deep}\le N/8$ gives $75\%$. The unconditional shallow Cauchy bound is $hE_h\le C\max(\kappa_2,2h\log T)T\log T$ uniformly in $0<h\le1/64$ with $\kappa_2\ge120000$, hence $(1/\log T)E_{1/\log T}\le C'N(T,2T)$ and, for every $\varepsilon$, a depth multiplier $\alpha\ge4$ with deep fraction $\le\varepsilon N$ and $(\alpha/\log T)E_{\alpha/\log T}+R_{\rm deep}\le BN$. It controls multiplicity and clustering (sum of squared multiplicities $\le CT\log T$, close pairs within $K/\log T$ weighted $\le(C/8)(16+K^2)T\log T$) but its constant is many orders of magnitude above the $3/20$ that $70\%$ needs in this currency; the majorant counts every zero in the window.
4. *Zero-side slack.* Refuted for every bandwidth below $3/4$; displaced pairs at $\kappa=4/3$ give slack $N/12$ only for displacement $\ge1/6$; value moments cannot separate reflected pairs from two critical zeros; the pinching slack of IGP ($10^{-8}$) is structural and says nothing about off-line zeros, though better packing may enlarge it and a combined receiver carrying pinching credit into the trans-threshold certificate would relax the surplus budget (that combination must be proved).

**The arithmetic target.** The surplus is an exact finite identity $S_{\rm prime}=S_{\rm model,Q}+D_Q$: the parity-locked $Q$-modulus Ramanujan stabilizer model on coalescent odd pairs plus a centred discrepancy, parity retained in both. Calibration at $\lambda=4/3$ of the affine family $F_{\beta,\gamma}(\alpha)=\beta+\gamma(\alpha-1)$, surplus $((\lambda-1)^2/\lambda^2)(\beta-1)+((\lambda-1)^3/(3\lambda^2))(\gamma-1)$:

| Model | Surplus | Against the $1/18$ budget |
|---|---|---|
| Hardy–Littlewood / function field / GUE ($\beta=1,\gamma=0$) | $-1/144$ | slack $1/16$ |
| uncorrelated / diagonal only ($\beta=1,\gamma=1$) | $0$ | slack $1/18$ (a different normalization, not Poisson) |
| Poisson off-diagonal without repulsion ($\beta=2,\gamma=1$) | $+1/16$ | fails by $1/144$ |
| spectral sieve ($\beta=\Upsilon,\gamma=0$) | $(9\Upsilon-10)/144$ | passes iff $\Upsilon\le2$ (the parity threshold) |
| unsigned additive sieve ($\beta=1+\Upsilon,\gamma=1$) | $\Upsilon/16$ | passes iff $\Upsilon\le8/9<1$: impossible for any upper-bound sieve |

So the budget sits one tenth of the way from Poisson to Hardy–Littlewood, and no unsigned majorant can reach it (positive spectral majorants give $8/27$ against the needed $1/9$ for the trans-threshold integral). If the selected model's limit is proved to be $-1/144$, it suffices that $D_Q/N\le1/16+o(1)$; a full $o(N)$ discrepancy is unnecessary. The Hardy–Littlewood logarithmic deficit integrates to $-(\lambda-1)^3/(3\lambda^2)<0$ against the trans-threshold weight before any error term is estimated (Frullani cancellation of the Poisson main term).

**What the discrepancy is (inference, normalizations not audited in Lean).** The off-diagonal of the second moment of the prime Dirichlet polynomial of length $X=T^\lambda$ against a smooth window on $[T,2T]$ is $\sum_{T<p\le X}\Lambda(p)\,(T/p)\sum_h\hat w(Th/p)(\Lambda(p+h)-1)$ with the Poisson term killed by $w(0)=0$: the centred, smoothed prime count in a window of length $H_p=p/T\le T^{\lambda-1}$ after each prime $p$, averaged over primes. The trivial sieve bound gives $O(X)$ against a diagonal $T\log^2T$ (Montgomery–Vaughan's loss). A gain needs this centred count to be unbiased on average to within a secondary term of size $\log H$, i.e. a fixed fraction of the $-\tfrac12\log H$ repulsion in $\sum_{h\le H}\mathfrak S(h)$; the dangerous shifts are $h\asymp H_p$, between $T^\delta$ and $T^{1/3}$. Almost-all short-interval theorems (from length $x^{2/15+\varepsilon}$) give the main term with an error far larger than the secondary term. By the explicit-formula bridge this is the pair correlation of zeros beyond $\alpha=1$ in prime language, open even under RH.

**Answer.** No opportunity to reach $75\%$ with current tools. The leading target is the signed, parity-retained coalescent discrepancy within the $1/16$ allowance (a $70\%$ checkpoint at $19/180$, or $E(1/9)\le4$ in the narrow strip). Structural slack and shallow energy are complementary; the one depth-sensitive quantity computable from arithmetic is the Hecke defect at $L\asymp\log T$ (M-4), whose prime side is the same coalescent sum. The corpus has shown every known collective statistic (density, value moments, shallow energy, pair correlation at $\alpha\le1$) blind at depth $1/\log T$.

---

## 6. Question 5 — the three open questions to focus on

Ranked by expected progress per unit of success, with first lemmas and success criteria.

### Q5.1 Complete positivity at one macroscopic overlap (M-1)

*Statement.* For one fixed, quantitatively nondegenerate profile, eventual positive definiteness of `completeWeilMatrix φ c N` at $c=3/2$ or $c=2$, with usable dependence on ratio, conductor and horizon so that an exhausting schedule is a subsequent question and not a hidden quantifier exchange.

*First lemmas.* The completed shell symbol on Ramanujan packets (affine unit averages plus the divisor jet, all terms combined before estimation) and its cross-mode residual; whether the cyclotomic floor $A_m/\varphi(m)$ enters with nonnegative weight; the Schur cost of the paid additive block; the $c$-dependence of the TM floor beyond $\delta_*$ by the same scheme (the route report calls this "just work"); the flip diagnostic $\omega_p$, $p\in\{11,13,101\}$, at $c\in\{c_0,2,4\}$.

*Success.* Positivity at $c=3/2$ or $c=2$; or a sharp negative symbol or unavoidable cross-mode term identifying what the Ramanujan description loses (a theorem controlling only selected diagonal entries does not answer the question). Walls addressed: 3.26, 3.28, 3.42 and the first-prime/polar faces of Wall 1; the impossible atomic Metzler repair is avoided.

### Q5.2 The signed coalescent discrepancy at bandwidth $4/3$

*Statement.* For the exact admissible windows, $S_{\rm prime}(T)\le(1/18+o(1))N(T,2T)$; equivalently, evaluate the selected stabilizer model (proving its limit) and bound $D_Q/N\le1/16+o(1)$.

*First lemmas.* Any constant saving in the same functional that improves $0.67250071$ (the $577/4500$ threshold beats $H_D(1)$); the $19/180$ checkpoint ($70\%$); the model's limiting value with the chosen cutoff; a characterization of which signed dispersion estimates collapse to a parity-blind majorant (the unsigned additive sieve cannot pass at any $\Upsilon\ge1$).

*Success.* $75\%$ simple critical zeros; or a classification of the signed estimates that survive beyond the square-root threshold. Walls addressed: 1.27, 1.30, 1.31, 1.33. No claim that the estimate transfers to RH without a separate source theorem.

### Q5.3 A producer of a one-sided count at some power precision (M-2)

*Statement.* $\psi(x)-x\le Cx^\theta$ or $\ge-Cx^\theta$ for some $\theta<1$, from exact identities (the factorial identity with its Stirling split, the Nair lattice, integer Dirichlet polynomials with Siegel's lemma) without a Mertens bound, an RH-equivalent sign or a small integral assumed.

*First lemmas.* The joint inversion of $(F,G,h)$ more accurately than the sum of separate bounds; the precision at which the sawtooth cancels against $\mu$; a ceiling certifying a Siegel-half auxiliary at any $\theta<1$; an integer auxiliary of size $O(x)$ with multiplicity $\ge2$ on a positive proportion of primes above $\sqrt x$; beating the parity constant $2$ in intervals of length $x^\varepsilon$.

*Success.* A first fixed strip, of any width, which fires the seven dictionaries. Walls addressed: 1.34–1.37 and the producer faces of Wall 14. Its receiver-side companions are the extraction or refutation of the external capstone (W10) and the five-sixths Gram pair.

*Honourable mentions.* The prime-side ceiling for the Hecke defect at $L\asymp\log T$; the converse Krein–Langer theorem on $\mathbb Q_{>0}$ (a common invariant negative subspace for all prime translations), which would make the finite-support stratum a structure theorem; the slower synthesis schedule with a signed profile transfer; infinite-symmetry polar confinement as exploratory foundational work.

---

## 7. Question 6 — the field that would supply the missing tools

### 7.1 The walls as questions

- **W1.** Which property of $\Lambda$, absent from every bounded twin and from every weight in $\Lambda+\mathcal Q$ other than at square-root gauge distance, bounds a signed arithmetic form at square-root precision on an unbounded family?
- **W3.** In which topology does a sign or an index survive overlap growth, aperture growth and conductor growth, and which exhaustion carries the arithmetic point with it?
- **W14.** Which independently built structure produces a one-sided count, as Riemann–Roch plus Stepanov produce it over $\mathbb F_q$?

Analytic number theory answers these at $o(1)$ relative precision, which the corpus proves is not enough; algebraic geometry answers them over $\mathbb F_q$ with a surface, a Frobenius and sections; Krein–Langer theory answers W3 on $\mathbb Z$ and $\mathbb R$ but not on $\mathbb Q_{>0}$ with its towers; transcendence theory makes auxiliary functions with multiplicity but has never produced a prime count. The field is where these four meet.

### 7.2 Name and point of view

**Effective arithmetic Hodge theory of $\mathbb Q_{>0}$**, with two engines: an index calculus (HKT, AKL are its first chapters) and a precision calculus (ASRP), and with the finite-horizon correlation calculus of CACT as its computational tool. The name is a specification of missing theorems, not a discovered subject.

Point of view: RH is the Hodge index theorem of an arithmetic surface whose points are the primes with residue size $\log p$, whose Frobenius is the Hecke ring of $\mathbb Q_{>0}$ together with the successor $n\mapsto n+1$, whose cohomology is measured by log-volumes and log-orders rather than dimensions, whose genus is infinite, and whose boundary is the archimedean place. The index is a global invariant; positivity is its last step; the order of work is index, then count, then sign. Every theorem is stated at finite height with its precision class, and passes to the limit in an index-carrying topology.

Central question: which exact compatibility laws of arithmetic (divisibility, affine successor shifts, residue stabilizers, logarithmic weights, the archimedean completion) force cancellation or positivity beyond what follows from size, symmetry, local spectra and marginal distributions?

### 7.3 Objects

| Object | Role | Already built |
|---|---|---|
| Hermitian kernels on $\Gamma=\mathbb Q_{>0}\cong\oplus_p\mathbb Z$, Hecke-covariant, with towers $\langle p\rangle$, fine towers $\langle(n+2)/(n+1)\rangle$ and the archimedean completion | the Weil kernel and its truncations; the index | HKT, AKL |
| precision spaces $\mathcal Q_{\theta,k}=\{\delta:\sum_{n\le x}\delta(n)=O(x^\theta\log^kx)\}$, the square-root class $\mathcal Q$, stabilizers of each observable | which operations keep precision and which lose it | ASRP |
| the prime torus and the gauge torus; the arithmetic point | spectral side; where selectivity lives | APD, ACG |
| the scaling surface (pole plane plus tests), its height truncations, the signature law | the surface whose Hodge index is RH | ACS, AOG |
| the characteristic circle $\mu_\infty$ with power maps; torsion orbits; log-orders as intersection numbers | the only integral intersection theory over $\mathbb Z$ | AIT, AES, RAPT |
| the group ring $\mathbb Z[\Gamma]$: integer Dirichlet polynomials, the integrality lattice, the box class $\sqrt NA$ with $\chi=N$ | sections and auxiliaries | ASRP, AET |
| complete forms with designated reserves: coefficient space, profile, Gram, Gamma, both poles, interaction blocks; a reserve is a proved lower bound in a named norm and a transfer records what it spends | the finite sections of the kernel | TM, CACT, SSHA, AID |
| signed correlation functionals (the coalescent surplus with its centring and parity; the completed successor-shell operator) | the objects the census and the overlap problem actually read | TTPC, CACT |
| regulators, counterterms, anomalies, null cones | renormalization of the divergent diagonal | RAPT, RBG, AIT |

### 7.4 Language

Negative index and hyperbolic pairs; Krein–Langer class; aliasing and Nyquist windows of a tower; index-carrying completion; selective versus twin-blind; precision class and stabilizer; point side versus zero side; producer versus receiver; reserve, transfer, Schur cost; regulator, counterterm, anomaly, null cone; log-torsion and log-volume; overlap ratio as bandwidth excess; the structure ladder (sign, support, normalization, ring). Every statement names its source, its height, aperture or overlap, conductor, profile class and norm, its simultaneous parameter range, and what it gives on the golden datum, the Liouville twin, a remote flip, and over $\mathbb F_q$.

### 7.5 Foundational principles

1. **Irreducibility.** Any sufficient input is parity-breaking, square-root-precise and of unbounded aperture, and acts at the ring level. A statement that survives a battery move is a dictionary entry.
2. **Target-dependent precision.** A count theorem works modulo $\mathcal Q$; a complete positivity theorem must see every coefficient; a census theorem pays an aggregate exceptional budget. The theory exploits these differences and never imports one tolerance into another without a proved bridge.
3. **Structure, not estimate.** Precision is kept by identities, counts and self-dualities; it is lost by extraction (inversion, ceilings, majorants). A positive part never pays a hyperbolic pair.
4. **Completion before sign extraction; visible cancellation.** The decisive estimate retains the terms that can change sign (both poles, mixed blocks, centring, parity) until their cancellation has been used; triangle inequalities come after the signed combination is identified.
5. **Index first.** Compute or bound the index from local constituents and one global law; positivity follows. Finite index is Lindelöf-deep, so every claimed ceiling must imply LH.
6. **Point side.** Producers vanish at the primes, not at the zeros; zero-side annihilation certifies nothing.
7. **Uniformity as content; graded coercivity.** Fixed-conductor, finite-dimensional and fixed-overlap theorems are distinct from exhaustive ones; a reserve may decay with overlap, conductor or resolution, and the goal is a lower bound sufficient for the actual residual, not one floor at every scale.
8. **Renormalization carries its anomaly.** Positivity passes a scale limit exactly on the null cone of the counterterm; covariance is proved, not assumed.
9. **Calibration and positive salvage.** Reproduce Weil over $\mathbb F_q$ by counting; fail on the golden datum, the complex fake and over-regular Beurling systems; recover PNT, Vinogradov–Korobov and Guth–Maynard in the field's coordinates; every failed theorem exposes the lost information and the strongest surviving bound.
10. **Formal closure.** Unconditional statements with every input discharged.

### 7.6 Criteria a theorem of the field must fulfil

Independence from zero-indexed objects; fidelity (Gamma, both poles, every prime power, multiplicities, mixed entries); the battery, with the remote flip added to the Liouville twin where the claimed range already separates it; the precision class named and respected (rejecting every $\mathcal Q$-perturbation is not a criterion for a count theorem); exhaustion in a named index-carrying topology with uniformity in the growing parameters; calibration over $\mathbb F_q$ and on fakes; a new inequality, count, index ceiling or structure theorem rather than another equivalence; LH implied whenever finite index is claimed.

| Proposed conclusion | Required calibration |
|---|---|
| full Weil positivity for the prime source | separate the Liouville twin and, if the family is exhaustive, every finite flip |
| square-root count precision | respect $\mathcal Q$; a count cannot and need not see a finite flip |
| a $75\%$ census | same windows and normalization as the receiver; retain the Poisson/singular-series difference |
| an improved detector estimate | survive the structured-set geometry while respecting the arbitrary-set fourth-moment counterexample |
| spectral or polar purity from a realization | supply an input absent from the impure data that already satisfy realization and continuation |
| a limit theorem | track escaping mass and the decisive cross terms in the receiver's topology |

### 7.7 The tools to build and the first decade's topics

1. **A signed arithmetic symbol calculus** for operators mixing multiplicative scales and additive successor shifts: the completed action on growing Ramanujan packets, the exact divisor jet, composition and elimination rules that preserve the full Schur cost. First theorem: the symbol at one macroscopic overlap and whether the cyclotomic floor pays its residual.
2. **Dispersion for centred arithmetic functionals** using parity, singular series and signed windows jointly, with the census benchmark (model evaluation plus discrepancy within $1/16$) and a theory of structured exceptional sets.
3. **Constrained inversion.** The joint inversion of the correlated tuple $(F,G,h)$ of the factorial identity; a cancellation theorem in which precision follows from the relations among errors rather than from a norm bound on each; first success a fixed sublinear one-sided count.
4. **Arithmetic Stepanov.** Auxiliaries in $\mathbb Z[\Gamma]$ with $p$-adic multiplicity; the zero estimate for integer Dirichlet polynomials (a Dyson lemma over $\operatorname{Spec}\mathbb Z$, with Baker separation available on two-prime supports); the flatness identity playing $x^q=x$; the odd-class upper count at a power precision.
5. **Converse Krein–Langer on $\Gamma$.** A common invariant negative subspace for all prime translations of the Pontryagin space of a finite-index kernel; the covariant classification beyond finite spectral support.
6. **Quantitative exhaustion.** Profile regularity, aperture, conductor and height tracked together in the complete form; the slowest RH-complete overlap; arithmetic synthesis (Möbius or Ramanujan cell weights) below the quasi-analytic rate; the alias fraction at bounded overlap; signed transfers between profiles.
7. **Selection and invisible perturbations.** What each observable determines (count: modulo $\mathcal Q$; tower positivity: everything; fixed-ratio complete forms: to be measured by the flip threshold), and which coupling supplies the rest.
8. **Quadratic Riemann–Roch on the scaling surface and covariant regulators on the characteristic circle.** A section count $h^0$ of box-class size $N$ defined without the sign; a regulator with nontrivial null cone; Riemann–Roch on torsion orbits with defect $\tfrac12\log|d|$; the Hodge index with adjunction.
9. **Arithmetic Herglotz theory.** Positive measures on the circle or the prime torus built from primes and the successor whose moments are explicit-formula values; reflection-positive states on $\mathbb N\rtimes\mathbb N^\times$; non-factorizable stable polynomials on the Bohr torus.
10. **Depth-sensitive census.** Observables sensitive to displacement at depth $1/\log T$ with prime-side upper bounds; the Hecke defect at $L\asymp\log T$; two-sided coalescent pair theory; local-to-global with heights (one explicit prime certifying all zeros below $T$).

First theorems in order of accessibility: the flip threshold at fixed ratio; the completed shell symbol at $c=3/2$ or $2$; a constant saving in the signed coalescent functional; a Hasse principle with heights; the covariant converse Krein–Langer theorem for orbit kernels with infinite spectral support; an arithmetic synthesis theorem below the quasi-analytic rate; a zero estimate for integer Dirichlet polynomials on two-prime supports; and, as the field's signature result, a one-sided count at some power precision for one parity class.

### 7.8 What the field is not

Not a new set of RH equivalences (complete and E-trivial); not a positive-majorant theory; not a theory of local tower data (twin-blind); not a theory of interval statistics (precision-blind); not finite-field geometry imported by analogy (curves reproduce the prime support, not the archimedean continuum); not a foundational "positivity principle" that restates RH. It is the theory in which the index of one Hermitian kernel on $\mathbb Q_{>0}$ is computed from local constituents and one produced count, at a named precision.

---

## 8. Lean anchors (statements read for this revision)

Positivity and overlap: `TransMetzlerWeilPositivity.eventually_completeWeilMatrix_posDef_of_mem_Ioc`, `OptimizedTransMetzlerFloor.eventually_completeWeilMatrix_posDef_certified`, `certifiedOverlapIncrement_eq`, `certifiedOverlapFloor`, `LiouvilleTwinSelectivity.eventually_liouville_weilQuadTw_neg_transMetzlerProfile`, `liouville_weilQuadTw_nonneg_of_le_fixedWidthRatio`, `ArithmeticLorentzianGeometry.metzlerThreshold_overlapRatio`, `SuperGevreyCriticalGrowth.riemannHypothesis_iff_steklovDCProfile_nonneg_superGevrey`, `superGevreyRatio`, `OverlapGrowthSuperGevrey`; `SpacingScaleHarmonicAnalysis.riemannHypothesis_iff_atomicFamilies_nonneg_of_growth` (`OverlapGrowth`), `_of_growthTwo`, `_of_growthPow`, `_of_gevrey`, `_log` ($\alpha>1/2$), `_log_quarter`; `ZeroSideStratum.hermNegIndex_atomicShiftWeilGram_le_of_finiteOffLine`, `isolatedPairConfig_atomic_negative_every_ratio`.
CACT ingredients: `CyclotomicNormGivesAConductorUniformCurvatureFloor.fract_quadratic_le_normalized_arithmeticOverlapCurvature`, `one_le_prod_primitive_prefix_norm`, `ActualPrimeWindowsDiagonalizeAffineRamanujanModes.tendsto_affineRamanujanPrimeWindow`; modules `AnnularRamanujanFamiliesHaveTwoSidedFrames`, `OneHorizonMakesTheCompleteWeilMatrixPositiveThroughTouching`, `OnlyTheBoundaryStarEntersAtTouching`, `TheBoundaryPrimeStarVanishesAfterNormalization`; `SpacingScaleHarmonicAnalysis.TheGaugeEntersThroughNonRatioLags` (`primeSum_atomicTest_eq_lags`, `exists_nonRatio_pair`).
Index and strata: `HeckeKreinToeplitz.negIndex_zetaKernel`, `negIndex_zetaKernel_twoPrime`, `negIndex_zetaKernel_eq_two_mul`, `zetaKernel_finiteIndex_tfae`, `lindelof_of_negIndex_zetaKernel_lt_top`, `quasiRH_of_negIndex_zetaKernel_lt_top`, `negIndex_zetaKernel_eq_zero_iff_count`, `forall_negIndex_towerKernel_eq_zero_iff`; `ArithmeticKreinLangerTheory.riemannHypothesis_iff_oddClass_upper`, `riemannHypothesis_iff_zetaKernel_consecutive`, `negIndex_zetaKernel_eq_iSup_consecutive`; modules `LocalityIsTwinBlind`, `CompressionsAreReceivers`, `TheTwistTowerCompletesTheUpperCount`.
Precision: `ArithmeticOfSquareRootPrecision.deciding_input_necessary_properties`, `towerIndexZero_necessary_properties`, `count_and_not_towerIndexZero_add_inv`, `count_signGauge_iff`, `count_signGauge_of_finite`, `riemannHypothesis_iff_monotone_inversion`, `isLeast_positive_nairIntegral`, `riemannHypothesis_iff_siegelHalf_sqrtScale`, `zeroReSup_lt_one_iff_siegelHalf`, `exists_intDirichlet_vanishing_on_trivial_lattice`; modules `TheStirlingErrorSplits`, `IntegerDirichletPolynomialsAtArithmeticPoints`.
Selection: `ArithmeticCountingPositivity.primeFlip_hasHyperplaneGap_two_mul_log_two_iff`, `primeFlip_exists_negative_complete_test`, `primeFlip_not_weilPositiveFull`; modules `CofinitePrimeFlipsHaveZeroGap`, `SelectiveMultiscaleArithmeticPositivity.PositivityAtEveryRootSelectsTheVonMangoldtWeight`.
Census: `IncommensurableGaborPinching.simple_critical_proportion_ge_67250071`, `RHTower.three_quarters_or_simple_offLine_near_line`, `three_quarters_within_four_div_log`, `four_fifths_critical_ordinates`; `TransThresholdPairCorrelation.zeta_coalescent_certificate_four_thirds_simple_and_offLineMultiple`, `oddEvenShiftPrimeCoalSum_eq_stabilizerModel_add_discrepancy`, `calibration_five_models_four_thirds`, `generalPrimeSurplusRatio_affineTransModel`, `narrowStrip_proportion_gain_eq`, `narrowStrip_beats_two_thirds_iff`, `constrainedStrip_optimal_exchange_rate`, `narrowStrip_coalescent_proportion_gain_eq`; `ArithmeticCastelnuovoSeveri.coalescent_budget_thresholds_for_two_thirds_HD_one_and_three_quarters`, `narrowStrip_HD_one_and_twoAdic_parity_collar`; `RHTower.ZetaThreeQuartersReduction.FrobeniusFourThirds`, `PairCorrelationFourThirds`, `frobenius_target_gue`; `ShallowCauchyPrimeEnergy.exists_uniform_xiShallowCauchyEnergy_le`, `exists_arbitrary_deepFraction_with_linear_shallowEnergy_budget`, `exists_shallow_zetaZeros_sq_multiplicity_and_closePairs_le`; module `RHTower.ValueMomentsCannotSeparateReflectedPairs`.
Quasi-RH: `BezoutValuationIncidence.quasiRH_crossRoute_seven_way_tfae`, `escapedMoebius_receiver_abscissa_tfae`, `coalescentResonanceExponent_properties`; `SelectivePositivityAndThresholdLaws.growingEndpointEscapedMoebiusLaw_tfae`; `RHTower.three_quarters_strip_iff_chebyshevNormalizedCesaroMeanSquareEnergy_subpower`, `five_sixths_strip_iff_...`, `two_mul_zetaZeroAbscissa_eq_sInf_chebyshevNormalizedCesaroMeanSquareEnergy_exponents`, `five_sixths_strip_of_chebyshevNormalizedCesaroSum_pow_le_one_third`, `three_quarters_strip_of_chebyshevNormalizedCesaroSum_pow_le_one_quarter`; `RHTower.QuasiRHDetectorScaleBudget.retunedBoundary_sharp_minimum`, `gram_power_saving_boundary`, `ordinaryGramBoundary_sharp_minimum`, `unitGramBoundary_sharp_minimum`, `gramProfile_five_sixths_feasible_iff`, `gramProfile_five_sixths_witness`, `gramProfile_published_boundary`; modules `QuasiRHSubfieldMoment`, `DensityEnvelopeNoGo`, `ReflectiveDirichletPolynomialS2.moebius_and_prime_powerWindowSaving_iff_quasiRH`.
Analytic inputs: `RHTower.tendsto_montgomeryForm_div_leadingOrder`, `RHTower.DeBruijn.not_real_rooted_of_neg`, `riemannHeat_neg_nonreal_zeros_infinite`, `riemannHeat_zeros_real_simple_twoThirds`, `RHTower.Matveev.effectiveBakerBound_holds`, `RHTower.siegel_zero_free`, `SignedArithmeticEnergyIncidence.exists_norm_zeta_half_le`; modules `RHTower.Sieve.GuthMaynardTheoremOneOne`, `GuthMaynardCorollariesUnconditional`, `ZetaZeroDensityHypothesisFiveSixths`, `Sieve.VinogradovKorobovZeroFree`, `ZetaElevenEighteenthsLineBound`.
Countermodels and no-gos: `RHTower.FerroBlind.ferromagnetic_inequalities_leeYang_blind`, `RHTower.not_tendstoLocallyUniformly_isingGraph_const_mul_XiC` (module `IsingGraphCenteringLaw`), `RHTower.overRegular_integers_do_not_constrain_zeros`; modules `ArithmeticCastelnuovoSeveri` (golden datum), `ArithmeticCorrespondencePositivity` (complex fake), `ArithmeticIndexDescent.exists_fullPolarNonfirst_completeGamma_reserve`.
Characteristic circle, effectivity, Hecke defect: `ArithmeticEffectivityTheory.riemannHypothesis_iff_logTorsion_sub_eulerChar`, `RenormalizedArithmeticPotentialTheory.renormalizedPrimeForm_covariant_iff`, `torsionCounterterm_golden`, `ConjugateDiagonalGeometry.heckeDefect_eq_second_difference`; module `ArithmeticIntersectionTheory`.

## 9. Corrections relative to the first version of this report

- Overlap convention: $c=Nw$ in Lean; the exact spacing is $\log(1+1/N)$. Shell radius at ratio $c$ is $r<ckn/N$, not $2ckn/N$.
- Certified range: $c<1+\delta_*$, $\delta_*=1/107520002048050000$, with the explicit floor; $\delta_*$ is a certificate boundary.
- The RH-complete receiver ladder is profile-dependent; the sharp one is $(\log\log N)(\log\log\log N)^\beta$, $\beta>2$, for the Steklov profile, and the positivity theorems are for the plateau.
- The count's stabilizer contains finite flips; a count route need not reject them; "two primes" is sufficiency; one prime tower with all generators decides RH.
- $75\%$: exact hierarchy $29/36-b$ ($5/36$, $577/4500$, $19/180$, $1/18$), the five-model calibration, the $1/16$ discrepancy allowance, the narrow-strip gain formula with $E(1/9)\le4$, the reflection accounting, and the shallow-energy constant stated as proved.
- Quasi-RH: exact energy targets, the escaped-Möbius dictionary, the detector budget with the five-sixths feasibility region and the $29/36$ floor, the $\theta(\lambda)$ identity, the subfield fourth-moment warning.
- Lee–Yang: the centering no-go and the ferromagnetic-inequality no-go stated explicitly.
- Three questions re-ranked: macroscopic overlap, signed census discrepancy, one-sided producer; extraction of the external capstone demoted to the receiver-side companion of the third.
