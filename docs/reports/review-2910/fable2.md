# Fable 2 — consolidated big-picture report on the RH programme

Status: 29 October 2026. Inputs: the frontier map, the killed-routes ledger, the route-unification ledger, the route-obstacles report, the walls ledger, the 47 programme READMEs in `docs/reports/research-programmes.md` (read oldest to newest), and targeted searches of the Lean corpus with `scripts/formal_tools.py research`. No builds, no web, no audits of other agents' work. Evidence labels **[L]/[S]/[K]/[P]/[E]** are inherited from the frontier map; **(inference)** marks a conclusion of this report that is not a corpus theorem. Working log: `logs/fable2-research-2026-10-29.md`.

The six questions are answered in §§2–7. §1 fixes the picture they rest on.

---

## 1. Where the research stands

### 1.1 What is proven

| Area | Established (corpus) | Grade |
|---|---|---|
| Census | Simple critical zeros \(\ge 0.67250071-\varepsilon\) of \(N(T,2T)\); zero copies within \(4/\log T\) of the line \(\ge 3/4\); distinct ordinates carrying a critical zero \(\ge 4/5\); dichotomy: either \(N_0\ge\tfrac34 N\) or \(\ge(H_D(1)-\tfrac12-\tfrac1A-\varepsilon)N\) simple off-line zeros lie within \(A/\log T\) of the line. | [L] on an imported `Zeta23` (Alpöge–Furman) |
| Complete Weil positivity | For the plateau profile and every fixed overlap ratio \(c\in(0,1+10^{-18}]\) the complete Weil matrix (primes, Gamma, both poles) on atomic families at \(\log n\), \(n\le N\), is eventually positive definite, including where no unimodular gauge is Metzler; the Liouville twin is negative there from \(c\ge\tfrac12\). | [L]/[S] |
| RH-complete receiver | RH \(\iff\) eventual positivity of one Steklov–Denjoy–Carleman profile at overlap \(c_N=(\log\log N)(\log\log\log N)^\beta\), any \(\beta>2\). | [L] |
| Index theory | The Weil kernel on \(\mathbb Q_{>0}\) has negative index \(=\) number of distinct right zeros; two primes carry it; bounded index is closed under pointwise kernel limits; a positive part never pays a hyperbolic pair; index zero \(\iff\) one-sided count \(\psi(x)-x\le C\sqrt x\log^2x\) \(\iff\) upper count of the odd Liouville class; heat-collision mass \(=2(\kappa+\text{multiplicity excess})\). | [L]/[S] |
| Strata | Finite off-line support \(\iff\) finite index \(\iff\) bounded heat counts \(\iff\) finite critical energy \(\iff\) all zeros above some height critical; it implies LH and a fixed zero-free strip. | [L]/[S] |
| Precision | The count's stabilizer among weights is exactly the square-root class; tower positivity's stabilizer is trivial; PNT, Guth–Maynard and every error law weaker than square root are satisfied by \(\Lambda+\varepsilon n^{-\eta}\), \(\eta<\tfrac12\), which fails the count (deciding-input theorem). | [L]/[S] |
| Selection | A bounded weight positive on atomic families of growing overlap is \(\Lambda\); the harmonic-hyperplane margin is exactly \(2\log 2\); single flips \(\omega_p\), \(p\ge 11\), attain it and still fail complete positivity; cofinite flips have gap \(0\); locality is twin-blind. | [L]/[S] |
| Analytic inputs | Guth–Maynard large values: \(N(\sigma,T)\ll T^{(30/13)(1-\sigma)+\varepsilon}\) on \([\tfrac12,\tfrac56]\); density hypothesis on \(\sigma\ge 5/6\); Vinogradov–Korobov; primes in \((x,x+x^{17/30+\varepsilon}]\); almost all intervals \(x^\theta\), \(\theta>2/15\); \(\mu(11/18)\le 1/9\); Ingham's fourth moment; Montgomery pair correlation at leading order for \(\alpha<1\); de Bruijn–Newman \(\Lambda\ge 0\) (nonreal zeros at every negative heat time) and reality of heated zeros beyond \(2\pi e^{(2/3+\varepsilon)/t}\); effective Baker–Matveev bound \(|\sum\nu_i\log p_i|\ge c(2+|\nu|_1)^{-C}\); Siegel zero-freeness for quadratic characters. | [L] |
| Countermodels | Over-regular Beurling systems with regular integer counts and an off-line zero; the golden curve datum \(1-5X+5X^2\) with integral counts, functional equation, Witt integrality and index one; the complex fake \(q=16\); tempered single-pair configurations negative at every fixed overlap. | [L]/[S] |

No fixed zero-free strip \(\Theta<1\) is proven. The Chen–Gupta–Li intake (279 modules, 1863 declarations) has detector, density and tail components and no zero-free capstone.

### 1.2 The walls after this review: three names, one input

The walls ledger keeps three families (selective critical sign, transfer and exhaustion, realization and forcing). The theorems proved around them say more: they are one obligation seen from three sides.

1. **Transfer is solved where it can be.** Bounded index is closed under pointwise convergence of kernels (HKT). Height truncations and integer atomic families carry the index to the limit. What remains of Wall 3 is overlap growth, which is Wall 1 content: the point where the separated prime error enters as the overlap grows.
2. **Realization is located.** Zero-side certificates (compressions, characteristic polynomials, calibrated vanishing laws) are receivers; a producer must vanish at the primes, on the point side, at the ring level (AKL). Wall 14 is now a request for one object: a point-side producer of one parity class's upper count.
3. **The deciding input is a theorem.** Any property implying the count rejects the Liouville twin, fails for \(\Lambda+\varepsilon n^{-\eta}\), is not finitely determined, and has stabilizer inside the square-root class (ASRP). Any RH proof contains such a statement.

So the walls cannot be circumvented: whatever route is taken, somewhere inside it one proves a parity-breaking, square-root-precise, aperture-unbounded inequality about \(\Lambda\). The corpus's achievement is to have shown that this is **irreducible** and to have written the same input in every currency.

| Currency | The one input in that currency | Where it lives |
|---|---|---|
| Count | \(\psi(x)-x\le C\sqrt x\log^2 x\) eventually (one side suffices) | ASRP, HKT |
| Parity | \(\sum_{\lambda(n)=-1}e^{-nt}/n\le\tfrac12\big(\sum_n e^{-nt}/n+Ct^{1/2-\varepsilon}\big)\) | AKL |
| Index | \(\kappa(K_\zeta)=0\) | HKT |
| Positivity | atomic positivity at overlap \(c_N\to\infty\) (super-Gevrey rate) | TM, SSHA |
| Integrality | Siegel half or Liouville half of \(\{\int_0^1P\}=\mathrm{lcm}(1..n+1)^{-1}\mathbb Z\) at square-root scale | ASRP |
| Inversion | uniform monotone Möbius inversion at every exponent \(\tfrac12+\delta\) | ASRP |
| Energy | \(\mathcal E_{\rm crit}\) within one quantum; annular increment \(\le 39/50\) at every \(R\ge 4\) | AID, CACT |
| Heat | collision mass \(<2\); horizontal collision charge \(\le 1\) | HKT, WD |
| Escape | every escape state has positive gauge mass | ACG, PM |
| Effectivity | \(\log|\mathbb Z/\mathrm{lcm}(1..N)|=\chi(\sqrt N A)+O(\sqrt N\log^2N)\) | AET |

All rows are E-equivalent at \(\Lambda\). As properties of weights they are not: counts see the square-root class, positivity sees every coefficient (ASRP). This is why selection must be proved in positivity language and a producer is most naturally built in count language.

### 1.3 A dictionary the ledgers imply but do not state (inference)

An atomic test \(f_x=\sum_{n\le N}x_n\,g\big((u-\log n)/w\big)\) with \(w=c/N\) has Fourier side \(\hat g(ct/N)\,D_x(\tfrac12+it)\), where \(D_x\) is a Dirichlet polynomial of length \(N\). The window \(\hat g(ct/N)\) cuts the height at \(T\asymp N/c\). Hence:

- **overlap ratio \(c\) at horizon \(N\) is Dirichlet-polynomial length \(N\) at height \(T=N/c\)**, i.e. bandwidth \(\lambda=\log N/\log T=1+\log c/\log T\);
- the proven positivity (\(c\le 1+10^{-18}\)) is positivity of the complete Weil form at length \(N\le(1+10^{-18})\,T\): exactly the square-root threshold \(X=T\);
- the RH-complete receiver (\(c_N=(\log\log N)^{1+\varepsilon}\)) is positivity at length \(N=T(\log\log T)^{1+\varepsilon}\): a factor \((\log\log T)^{1+\varepsilon}\) beyond the threshold;
- the census needs \(\lambda=4/3\), i.e. length \(T^{4/3}\), but only for a proportion.

SSHA states the Nyquist half of this ("the spacing scale is the Nyquist scale of the atomic family"). The consequence is that the square-root threshold is the one wall in every coordinate the corpus uses: Montgomery–Vaughan's diagonal, the density-hypothesis threshold, the Metzler threshold \(c=1\), the aperture \(a=L/2\) of SRT, and the first prime–pair coalescence of TTPC are all \(X=T\). RH is the sliver between length \(T\) and length \(T(\log\log T)^{1+\varepsilon}\).

Per unit mass the atomic Weil form at overlap \(c\) has an \(O(1)\) margin (the archimedean self-energy \(\log(N/c)\) and the prime counterterm \(\log N\) match with constant one), against two \(O(c)\) families of off-diagonal terms on disjoint supports: the archimedean overlaps of additive neighbours \(m=n\pm j\), \(j\le cn/N\) (positive), and the prime successor shells \(m=kn\pm r\), \(k\ge 2\), \(r\le 2ckn/N\) (negative). Both have nonnegative entries and row sums \(\asymp c\), so neither can be paid by cancellation in operator norm; positivity for large \(c\) is a Schur-complement balance between them, and the \(c\to\infty\) limit of the family is Weil positivity on smooth tests. The trans-Metzler theorem is the statement that at \(c\le 1+10^{-18}\) the shells reduce to the pairs \((kn,kn\pm1)\) with \(kn>N/3\) and are paid by a fixed reserve (inference from TM, CACT, SSHA).

---

## 2. Question 1 — a mechanism that circumvents or destroys a wall

By §1.2 "circumvent" is excluded by theorem. "Destroy" means produce the input. Below are the six mechanisms I consider live, each checked against the eight constraints the corpus has proved (selectivity, beyond the margin, precision, non-locality, unbounded aperture on two primes, point side, no positive majorant, finite index is LH-deep). I rank them by how much of the problem they would remove if they work and by how finite their first milestone is.

### 2.1 M-A. A point-side producer: arithmetic Stepanov

**What it is.** Over \(\mathbb F_q\) the one-sided count is produced by an auxiliary polynomial vanishing to order \(m\approx\sqrt q\) at every point of a parity class, with the identity \(x^q=x\) making the vanishing conditions cheap and Euler's criterion making the parity class algebraic (AKL). Over \(\mathbb Z\) the corpus has reduced RH to the upper count of the odd Liouville class (one class suffices because \(\zeta\) has no real zero in \((\tfrac12,1)\)), has shown that integrality is exact (\(\{\int_0^1P\}=\mathrm{lcm}(1..n+1)^{-1}\mathbb Z\), least positive value \(e^{-\psi(n+1)}\)), that the integrality exponent is the zero width in each half, that a zero-free strip is a Siegel half at a power precision \(\theta<1\), and that precision is lost not in the identity or the floor but in the **ceiling** (the analytic bound certifying a small integral) and in **Möbius inversion** (ASRP). It has also shown that sup-norm ceilings at precision \(\theta<1\) must vanish at \(0,\tfrac12,1\), i.e. are Stepanov-like, and that the integer Chebyshev constant blocks sup-norm ceilings below linear precision.

**The mechanism.** Build an auxiliary object \(A\) on the point side (an integer polynomial, an integer Dirichlet polynomial, or an element of \(\mathbb Z[\mathbb Q_{>0}]\)) whose \(p\)-adic multiplicities grow on a positive proportion of the counted primes while its size \(\log|A|\) stays \(O(x)\), and certify the size by an identity rather than by a sup norm. The Bézout ledger \(\sum_p m_p\log p\le\log A\) is proved in both rings; the binomial cap \(p^m\mid\binom Nk\Rightarrow p^m\le N\) shows binomial auxiliaries have multiplicity one above \(\sqrt N\), so the multiplicity must come from somewhere else (AKL).

**Why it respects the constraints.** It acts at the ring level (coefficients add, valuations multiply); it is parity-visible because the Liouville twin's horizon value is a reciprocal group order \(e^{A_\lambda(n)}=1/r_n\), \(r_n=d_n/d_{\lfloor\sqrt n\rfloor}^2\in\mathbb N\) (ASRP); its aperture is the degree; it is a count, so it is a producer and not a receiver.

**First milestones.** (i) Beat the sieve parity constant \(2\) for primes in intervals of length \(x^\varepsilon\) (AKL's first rung). (ii) A ceiling certifying a Siegel-half auxiliary at any precision \(\theta<1\), which is a fixed zero-free strip by the integrality exponent. (iii) The inversion of the sawtooth \(h(y)=F(\lfloor y\rfloor)-F(y)\) against \(\mu\) below linear size (ASRP open 4).

**What the Dyson-lemma analogue would be (inference).** Stepanov needs two things: existence of the auxiliary with many vanishing conditions (linear algebra, cheap because of flatness) and a zero estimate (\(N\cdot m\le\deg\)). Over \(\mathbb Z\) existence is Siegel's lemma on integer Dirichlet polynomials (built in ASRP); the missing lemma is the arithmetic zero estimate: a nonzero integer Dirichlet polynomial of length \(N\) and height \(H\) cannot have \(p\)-adic multiplicity \(\ge m\) at more than \((\log(NH))/(m\log p)\)-type many primes unless it vanishes identically. The flatness identity over \(\mathbb Z\) is the open input; Fermat \(a^p\equiv a\ (p)\) and Kummer–Legendre \(v_p(n!)=(n-s_p(n))/(p-1)\) are the two candidates the corpus's ledger already uses implicitly, and neither has been turned into a multiplicity amplifier.

**Assessment.** This is the only mechanism that attacks the wall at the place the corpus has proven it must be attacked. It is also the hardest: its first rung is a classical open problem. It belongs in the top three (§6).

### 2.2 M-B. Overlap growth by diagonalization

**What it is.** The receiver chain gives RH from positivity at \(c_N=(\log\log N)(\log\log\log N)^\beta\). The proven positivity is at fixed \(c\le 1+10^{-18}\) by a perturbation around touching whose margin does not scale with \(N\). Two separate problems make up the gap:

1. **Fixed macroscopic overlap.** Positivity for every fixed \(c\ge 2\) with an explicit horizon \(N_0(c)\). By §1.3 this is a finite arithmetic problem about the shells \((kn,kn\pm r)\), \(r\le 2ck n/N\), balanced against the additive overlaps \(m=n\pm j\) through the diagonal and the pole reserve. TM lists it as its first open problem.
2. **Any-schedule completeness.** Whether positivity along *every* schedule \(c_N\to\infty\) is RH-complete. The super-Gevrey rate comes from synthesizing a fixed smooth witness by Riemann sums of a dilated profile; the alias ripple has amplitude \(\exp(-c\,\varrho^{1/s})\) for a Gevrey-\(s\) profile and Lévy energy (amplitude)\(^2\log N\), which is why \(\varrho\gtrsim(\log\log N)^{s}\), \(s>1\), is needed and why the quasi-analytic boundary \(s=1\) is the limit of *this* synthesis (HKT, SSHA).

If both hold, RH follows by diagonalization: define \(c_N=\max\{c:N_0(c)\le N\}\). With a tower-type \(N_0(c)\) this \(c_N\) grows like an iterated logarithm, far below every explicit threshold; so (2) must be proved for arbitrary slow growth, or (1) with \(N_0(c)\le\exp\exp(O(c))\).

**Why it is attractive.** Problem (1) is unconditional, finite at each \(c\), and progress is measurable (\(c=2\) would already be new). Problem (2) is approximation theory on the lattice \(\{\log n\}\): the slowest overlap at which integer-centred atoms synthesize every compact test in the Weil-continuity norm. The corpus's Euler–Maclaurin/Denjoy–Carleman synthesis is one method; a synthesis that uses the arithmetic of the lattice (Möbius or Ramanujan weights on cells, as in the complete-cell transfer, rather than Riemann sums of one profile) is the natural replacement, and HKT already shows that *some* shrinking schedule carries the whole index.

**Assessment.** The most measurable programme on the RH-complete axis. Its risk is that (2) is false (a tempered finite-support model is negative at every fixed \(c\), so fixed-ratio positivity cannot follow from the zero side without \(\zeta\)'s density), in which case (1) alone gives a new unconditional theorem and no RH.

### 2.3 M-C. The characteristic circle: a covariant regulator with a null cone

**What it is.** AIT shows that on the torsion \(\mu_\infty\) with power maps as correspondences, Weil's ingredients (i)–(iii) exist and are *integral*: intersection numbers of torsion orbits are log-orders of finite rings, the projection formula holds, the self-intersection of \(O_n\) is the discriminant of \(\mathbb Q(\zeta_n)\). What fails is the diagonal: it exists only after a regularization, and the regularization is not covariant (the Hecke cocycle \(\beta(n,t)=\log t-\sum_{p\mid t,p\nmid n}\log p/(p-1)\)). RAPT shows the horizon regulator is covariant with scalar counterterm \(\log N+O(1)\), constant one, and that torsion renormalization costs \(\varphi\log N\) with \(\varphi\) the golden ratio. RBG shows positivity passes a scale limit exactly on the null cone of the counterterm, and that the archimedean germ's cone is the polar hyperplane while the torsion germ's cone is \(\{0\}\).

**The mechanism.** A regulator of the diagonal that is Hecke-covariant *and* has a nontrivial null cone (AIT open 1), with an arithmetic Riemann–Roch on torsion orbits whose defect is \(\tfrac12\log|d|\) (AIT open 3). AES states the target as a Hodge index theorem with adjunction: equilibrium is computed (virial laws, the field at a zero is the residue of \((\zeta'/\zeta)^2\)), stability is the sign.

**Why it respects the constraints.** It is the one place in the corpus where integers enter as intersection numbers; integrality is local (log-orders at each \(p\)) and the global sign is RH, which is the correct shape for a producer that acts at the ring level.

**Assessment.** The deepest structural direction already in the corpus; it is where a "Frobenius for \(\mathbb Z\)" has concrete form (power maps \(z\mapsto z^t\) on \(\mu_\infty\)). Its weakness is that rotations (the elliptic correspondences) localize in the additive dual \(\mathbb Q/\mathbb Z\) while zeros live in the multiplicative dual; the zeros enter only through the hyperbolic Hecke maps.

### 2.4 M-D. A prime-side ceiling for the Hecke defect at translation \(L\asymp\log T\)

**What it is.** The collided form \(D(f)=\sum m_\rho|\hat f(\rho)|^2\) is positive by construction, coercive, and computed from arithmetic in the limit by theta-prefix source currents (CDG). Its second difference under Hecke translation, \(D(T_Lf)+D(T_{-L}f)-2D(f)=\sum m_\rho(2\cosh(2\delta_\rho L)-2)|\hat f(\rho)|^2\), is a positive measure of off-line depth and at \(L\asymp\log T\) a weighted zero-density statistic. CDG names the open input: a prime-side *upper* bound for it.

**Why it matters (inference).** It touches three strata at once. The census dichotomy puts every failure of \(3/4\) into \(\ge 0.17N\) simple off-line zeros within \(A/\log T\); such a configuration has Hecke defect \(\asymp A^2N\) per unit mass at \(L=\log T\), a macroscopic amount. Finite support is a uniform bound on the defect's growth. RH is its vanishing. A prime-side ceiling at any strength therefore lands in a named stratum.

**Assessment.** The prime side of \(W(T_Lf)\) at \(L=\log T\) reads primes up to \(T\): the square-root threshold again. This is the cleanest *one-sided* target among the depth-sensitive statistics the census lacks, but it is not easier than the others.

### 2.5 M-E. Compatibility of two exact descriptions at relative precision \(1/T\)

ACCE shows admission of the damped Möbius receiver at a damping below one half is equivalent to prime-pair cancellation at relative precision \(1/T\), that both ends of the damping range are paid and escape is an interior bump at \(n\gtrsim 2^{1/\varepsilon}\), and that after the square-root head the whole obligation is the long-modulus Möbius quadrature. ACCC proposes using the compatibility of the prime-dilation and Möbius-dilation forms of the same tangent as a constraint. This is a legitimate estimate-hunting ground, with the structural hint that the two descriptions must agree exactly. It does not by itself supply parity breaking; it must be combined with the gauge-charged inputs (successor, cells) of ACG and BGG.

### 2.6 M-F. The polar divisor of positive-genus affine Eisenstein series

Over \(y^2=x^3-x\) / \(\mathbb F_3\) the affine \(A_1\) Gindikin–Karpelevich coefficients have poles at the Frobenius zeros with full multiplicity, and the poles survive the complete regularized Weyl sum; for strip data, unitarity is eventual holomorphy off \(\operatorname{Re}s=-\tfrac12\) in the left band; the golden datum has an off-line pole despite the same calculus (ISC-polar). The mechanism would be an arithmetic constraint on the polar divisor coming from the infinitely many functional equations of a Kac–Moody Eisenstein series, which no finite-dimensional group supplies. It is the only live idea that uses an *infinite* symmetry group. The golden counterexample says the constraint must be arithmetic (actual curve, then actual \(\zeta\) via Garland over \(\mathbb Q\)), not formal.

### 2.7 Verdict on Question 1

No mechanism circumvents the walls; the deciding-input theorem forbids it. Two mechanisms would destroy the wall if they work: M-A (point-side producer) and M-C (covariant regulator with Riemann–Roch on the characteristic circle). One mechanism converts the wall into two measurable sub-problems without presupposing the answer: M-B (fixed macroscopic overlap plus any-schedule completeness). M-D and M-F are the strongest single targets inside the census and the geometric branches respectively.

A remark on what has quietly been shown impossible: every approach that reads prime information through interval statistics with \(o(1)\) relative error, every positive majorant, every local tower statement, every multiplicative-only construction, every tensor or family amplification over \(\mathbb Z\), and every finite-aperture certificate. These are theorems, not opinions, and they should be applied as filters before any new route is built.

---

## 3. Question 2 — approaches wildly different from everything so far

A proof cannot avoid the deciding input (§1.2). An *approach* can be different in where it gets the input from. The corpus's own classification is sharp: estimates lose precision; **structure** (an identity, a count, a positivity by construction) is the only known way precision has ever been kept, over \(\mathbb F_q\) and on the boundary \(\operatorname{Re}s=1\). The following are the approaches I consider genuinely different in kind. For each I give the mechanism, the corpus theorem it must evade, and an assessment.

**W-a. Theta series of the intersection lattice and the signature from a transformation law.** Weil's intersection form on \(C\times C\) is integral; the Weil form of \(\zeta\) on the group ring \(\mathbb Z[\mathbb Q_{>0}]\) (integer Dirichlet polynomials) is a real quadratic form that under RH has exactly one positive square in the intersection convention (ACS). For integral lattices the signature mod 8 is read off a finite Gauss sum (Milgram), and the theta series of an indefinite lattice of signature \((1,n)\) has a transformation law once a positive cone vector is chosen (Siegel, Zwegers). The approach: build the theta series \(\sum_{P\in\mathbb Z[\Gamma]}e^{-\pi W(P f,P f)}\) over a growing horizon, prove its Poisson/transformation law from the prime side (the explicit formula is itself a Poisson summation, APD), and read the number of positive squares from the law. *Obstruction to evade:* the form is not integral and has infinite rank, and \(\kappa\) is even, so a mod-8 invariant cannot pin \(\kappa=0\). What would be needed is the full modular weight, i.e. the rank of the positive part, at each height truncation. *Assessment:* speculative; its merit is that positivity would appear as a consequence of a self-duality rather than an estimate, the only forcing pattern the corpus has ever seen work (APD: positivity + exact self-dual identity + integer ⇒ rigidity).

**W-b. Reflection positivity of the Cayley–Li ladder by construction.** RH is reflection positivity of the Cayley ladder, equivalently the Metzler sign of the Li ladder (ALG). Osterwalder–Schrader positivity is the kind of positivity that holds *by construction* in Euclidean field theories, from a positive transfer operator or a Markov semigroup. ALG names the candidate carrier: KMS states of the \(ax+b\) semigroup \(\mathbb N\rtimes\mathbb N^\times\) with the reflection \(\beta\mapsto 3-\beta\); APD has the Bost–Connes temperature as the Hecke exponent and shows affine positivity is induced from dilations. *Obstruction to evade:* a functional whose reflection positivity is proved from a transfer matrix must be identified with the actual Li ladder, whose coefficients are explicit-formula values; if the identification uses the zeros it is a receiver. The whole content is an "arithmetic Herglotz theorem": a positive measure on the circle, built from primes and the successor, whose Fourier coefficients are the Cayley–Li sums. ACountP lists arithmetic Herglotz theory as open. *Assessment:* the most concrete of the wild ideas; it is the Hilbert–Pólya problem in Cayley coordinates, with the specific advantage that the carrier is noncommutative and additive (the successor acts).

**W-c. Transfer operators and dynamical spectral gaps.** Mayer's theorem writes the Selberg zeta function of the modular surface as \(\det(1-L_s)\det(1+L_s)\) for the Gauss-map transfer operator, and the zeros of \(\zeta(2s)\) are eigenvalue \(\pm1\) points of \(L_s\) at \(s=\rho/2\). Dolgopyat-type arguments give resonance-free strips near the *pressure* line, which for the Gauss map is \(\operatorname{Re}s=1\), i.e. \(\operatorname{Re}\rho=2\); the resonances sit left of the continuous spectrum at \(\operatorname{Re}s\le\tfrac12\). *Assessment (inference):* for finite-area surfaces the dynamical gap reproduces the Euler-product region and nothing else; a dynamical system whose pressure line is the critical line would be needed, and none is known. This is a wall of a different kind, worth recording so the route is not reopened.

**W-d. Fourier quasicrystals and Lee–Yang polynomials in infinitely many variables.** Kurasov–Sarnak construct crystalline measures from stable polynomials restricted to a line; Dyson's suggestion is that the zero measure is a quasicrystal. The corpus has the receiver (W1C: Ising/Lee–Yang limits to Riemann's law force RH; the centred limit law) and two obstructions: uncentred constant normalization fails, and local factors are Lorentzian only at the Weil bound, never at a prime (ALG: Ramanujan and Lorentzian meet only at the Weil bound). *Assessment:* a producer must be a stable polynomial on the Bohr torus that does **not** factor over primes; the Euler product is the wrong starting point. The natural object is a stable polynomial in the variables \(p^{-s}\) coupling different primes through the successor, which is exactly W-b's carrier seen as a polynomial.

**W-e. Arithmetic topology and dynamical cohomology.** Primes as knots, Spec \(\mathbb Z\) as a 3-manifold, log-torsions as Reidemeister torsion. The corpus's AET already reads integers over \(\mathbb Z\) as log-torsions and its Deninger modules build the dynamical \(H^1\) with the flow. *Assessment:* a 3-manifold has no Hodge index theorem; the needed object is a surface with a quadratic Euler characteristic, and AET shows the base theta \(h^0\) never extends. The direction is alive only as M-C/AET (a surface \(h^0\) of box-class size \(N\), the dimension of Dirichlet polynomials of length \(N\)).

**W-f. Higher-order Fourier analysis of \(\Lambda\) and \(\mu\).** Gowers norms and nilsequence orthogonality are precision-blind by theorem: they are stable under \(\Lambda\to\Lambda+\varepsilon n^{-\eta}\). They cannot decide. The same applies to all Matomäki–Radziwiłł-type short-interval results and to every almost-all statement.

**W-g. Typicality of the arithmetic gauge point.** ACG shows square-root cancellation holds at Haar-almost every point of the gauge torus, fails at the Liouville twin, and is RH at the arithmetic point; the exceptional set is null and comeager. A proof of typicality must use a gauge-charged property (an additive relation) that no finite-precision information about prime phases contains. This reframes RH as a measure-versus-category statement about one point; no mechanism is known that places a specific point outside a comeager null set except an identity it satisfies.

**W-h. Computation plus an effective finite-support theorem.** Finite support with an effective \(T_0\) below the verified height would give RH, and the corpus has the verified-height amplifiers. But finite support is RH above a height and implies LH; it is RH-hard at exactly the heights where verification stops.

**Summary for Question 2.** The two wild directions worth a card are W-a (self-duality forcing signature) and W-b (reflection positivity by construction on the \(ax+b\) semigroup). Both reduce to an arithmetic Herglotz theorem, which is the structural form of the deciding input. Everything else either reduces to a known wall or is excluded by a proved precision or locality theorem.

---

## 4. Question 3 — quasi-RH beyond \(\tfrac18<\operatorname{Re}\rho<\tfrac78\)

I read the question as: all nontrivial zeros lie in the strip \(\tfrac18<\sigma<\tfrac78\), and whether a narrower strip is in reach.

**What is known.** No fixed strip is proven in the corpus for \(\zeta\). The Chen–Gupta–Li manuscript claims \(7/8\) externally [E]; its intake has detector, density (a \(7/3\) envelope) and tail components and no capstone; the frontier records that its detector floor \(288\) against the collision quantum \(2\) blocks an RH endpoint but not the \(7/8\) claim. The unconditional strip-type facts are the Vinogradov–Korobov region, the density hypothesis on \(\sigma\ge 5/6\), Guth–Maynard's \(30/13\), \(\mu(11/18)\le 1/9\), Siegel zero-freeness for quadratic characters, and \(\Lambda\ge 0\) for the de Bruijn–Newman constant.

**The dictionaries.** A strip \(\Theta\le 1-\theta\) is proved equivalent to each of: an escaped-Möbius growing-endpoint saving at \(\theta\); a uniform Vaughan power saving; a Hecke-defect strip cap; Carathéodory positivity of \(\operatorname{Re}\xi'/\xi\) on \(\operatorname{Re}s>1-\theta\); a balanced-regime short-window Möbius or prime power saving; a Siegel half of integer-polynomial integrality at precision \(1-\theta\); for \([\tfrac14,\tfrac34]\), the Chebyshev Cesàro mean-square energy \(\ll N^{3/2+\varepsilon}\); and the seven-way cross-route equivalence (BVI, SPTL, RDPS2, ASRP). The density-envelope theorem says no bound \(N(\sigma,T)\ll T^{\theta(1-\sigma)}(\log T)^A\) forces a zero-free region, at \(30/13\) as at \(8/3\).

**Why "improve \(7/8\)" is not a constant problem.** All strips \(0<\theta\le\tfrac12\) are equivalent to a power saving of the same *type*; what the corpus lacks is any producer of any power saving. The difficulty is the first rung, not its value. Two consequences:

1. If the Chen–Gupta–Li mechanism is sound, its exponent \(\theta=1/8\) is a tradeoff inside a specific argument (a detector order against a density exponent, by the shape of its intake), and improving it is an optimization problem one can only pose after reconstructing the capstone. Until then "\(3/4\)" has no more meaning than "\(7/8\)".
2. If it is not sound, the value is irrelevant.

Either way the correct next step is the one the unification ledger already lists (W10): extract the vanishing mechanism, formalize the capstone or refute it. If it holds, the whole dictionary fires at \(\theta=1/8\): escaped Möbius saving, Vaughan power saving, the Siegel-half ceiling at precision \(7/8\), the balanced short-window saving. That is a structural gain far larger than the number.

**What a producer must contain (inference).** The density-envelope theorem shows a strip needs a *pointwise* vanishing step, not a count of large values. In the mean-square currency the strip \([\tfrac14,\tfrac34]\) looks like a second moment, but the mean square of \(\psi(x)-x\) is dominated by its diagonal over zeros (no cancellation between zeros is needed to evaluate it), so it tracks \(\Theta\) exactly and buys nothing; the ledger is honest on this point. The one currency in which a strip is a *one-sided* statement about an arithmetic object with no hidden zero sum is the escaped-Möbius law: Möbius in intervals \([x-b,x]\) with a power saving uniformly in \(x\). Almost-all results exist; the all-\(x\) one-sided version is the strip.

**Heat flow is not a route to a strip (inference).** \(\Lambda\ge 0\) is formalized, and an isolated off-line zero of depth \(b\) forces \(\Lambda>t\) for \(2t<b^2\) under a local non-interaction condition. The converse (a heat-time bound implies a depth bound) fails without isolation, which is why Polymath's \(\Lambda\le 0.22\) gives no strip.

**Answer.** No opportunity is visible to prove a strip narrower than \(7/8\) by a new idea; the opportunity is to make the first strip real (reconstruct or refute Chen–Gupta–Li) and then read its exponent off the mechanism. The best-shaped independent targets are the escaped-Möbius one-sided law at some \(\theta>0\) and the Siegel-half ceiling at some precision \(\theta<1\), the latter being the quasi-RH form of M-A.

---

## 5. Question 4 — at least \(75\%\) of zeros on the critical line

**What is known.** Simple critical zeros \(\ge 0.67250071-\varepsilon\) (Montgomery–Taylor's constant \(H_D(1)\) made unconditional by the imported Alpöge–Furman theorem plus the pinching slack \(10^{-8}\)); copies within \(4/\log T\) of the line \(\ge 3/4\); distinct ordinates carrying a critical zero \(\ge 4/5\); the dichotomy: \(N_0\ge\tfrac34N\) or at least \((H_D(1)-\tfrac12-\tfrac1A-\varepsilon)N\approx(0.17-\tfrac1A)N\) simple off-line zeros within \(A/\log T\). Every failure of \(3/4\) is a **near-line conspiracy**: a positive proportion of zeros off the line at depth \(O(1/\log T)\).

**The three levers and their distances.**

1. *Trans-threshold prime surplus at bandwidth \(4/3\).* Unconditionally the diagonal, archimedean and pole constant is \(43/36=\tfrac54-\tfrac1{18}\); \(3/4\) follows if the signed coalescent prime-pair surplus is \(\le(\tfrac1{18}+o(1))N(T,2T)\); after prime-power elimination and parity this is a sum over odd primes at even shifts within \(T^{-1+\eta}\), equal to its Ramanujan stabilizer model plus a centred discrepancy. Calibration: Hardy–Littlewood/GUE gives \(-1/144\), the Poisson model without repulsion gives \(+1/16\) (fails), positive spectral majorants give \(8/27\) against the needed \(1/9\). So the budget sits about ten percent of the way from Poisson to Hardy–Littlewood: a fixed fraction of the prime repulsion at shift scale \(h\asymp n/T\asymp x^{1/4}\) must be proved (inference from the calibration numbers). Beyond \(\alpha=1\) the pair correlation of zeros is open even under RH, and the explicit-formula bridge makes the prime-pair statement equivalent to it.

2. *Narrow strip \(\lambda=1+\delta\).* Gain over \(2/3\) iff \(E(\delta)<2/(3\delta)+4/3\); a quadratic bound \(\beta\le B\delta^2/(1+\delta)^2\) on the signed coalescent surplus gives a fixed gain \((3B^2+7B+3)/(9(B+1)^2(3B+2))\) at \(\delta^*=1/(3B+2)\) (e.g. \(0.072\) at \(B=1\), \(0.011\) at \(B=10\)), half kept after the collar. To beat \(H_D(1)\) one needs \(375\delta^2E(\delta)\le 242\delta+496\delta^2-4\), e.g. \(E(0.05)\le 9.96\). Here is what the signed surplus is at bandwidth \(1+\delta\) (inference, normalizations not audited in Lean): the off-diagonal of the second moment of the prime Dirichlet polynomial of length \(X=T^{1+\delta}\) against a smooth window on \([T,2T]\) equals
   \[
   \sum_{T<p\le X}\Lambda(p)\,\frac{T}{p}\sum_{h}\hat w\!\Big(\frac{Th}{p}\Big)\big(\Lambda(p+h)-1\big),
   \]
   the Poisson term having been killed by \(w(0)=0\). The windows have length \(H_p=p/T\le T^\delta\), and the trivial sieve bound gives \(O(X)\) against a diagonal \(T\log^2T\), which is Montgomery–Vaughan's loss. A gain needs the centred, smoothed prime count in a window of length \(T^\delta\) *after a prime* to be unbiased on average over primes to within a secondary term of size \(\log H\), i.e. a fixed fraction of the \(-\tfrac12\log H\) repulsion in \(\sum_{h\le H}\mathfrak S(h)\). For bounded shifts (\(\delta\to0\)) this is twin-prime territory, where the sieve upper bound with constant \(4\) already makes the terms negligible; the dangerous shifts are \(h\asymp T^\delta\). Almost-all short-interval theorems (available from length \(x^{2/15+\varepsilon}\)) give the main term only with an error far larger than the secondary term. So even the narrow strip needs Hardy–Littlewood on average over shifts up to \(x^{\delta'}\) with a secondary-term-precise error, which is not available.

3. *Zero-side slack.* Refuted for every bandwidth below \(3/4\); displaced pairs at \(\kappa=4/3\) reach slack \(N/12\) only for displacement \(\eta\ge 1/6\); value moments cannot separate reflected pairs from two critical zeros; the shallow Cauchy energy at depth \(1/\log T\) is \(O(N)\) with a majorant that counts all zeros of the window and constants (\(\kappa_2\ge 120000\)) five orders of magnitude from the \(3/20\) that \(70\%\) would need. The pinching slack of IGP is structural (\(10^{-8}\)) and says nothing about off-line zeros.

**Answer.** I see no opportunity to reach \(75\%\) with current tools. The identified levers all reduce to one object: signed prime-pair correlations at shifts between \(T^{\delta}\) and \(T^{1/3}\), controlled to a secondary term, which is the pair correlation of zeros beyond \(\alpha=1\) in prime language. The structural fact worth keeping is the dichotomy: \(75\%\) is equivalent to refuting a near-line conspiracy of positive density at depth \(1/\log T\), and the corpus has shown that every known collective statistic (density, value moments, shallow energy, pair correlation at \(\alpha\le 1\)) is blind at exactly that depth. The one depth-sensitive quantity that is computable from arithmetic is the Hecke defect at \(L\asymp\log T\) (M-D), whose prime side is the same coalescent sum.

---

## 6. Question 5 — the three open questions to focus on

Ranked by expected progress toward RH per unit of success, with first milestones and success criteria.

### Q5.1 Fixed macroscopic overlap with explicit horizon, and any-schedule completeness

*Statement.* (a) For every fixed \(c\ge 2\) and one smooth plateau, the complete Weil matrix on atomic families at width \(c/N\) is eventually positive definite, with an explicit \(N_0(c)\). (b) Every schedule \(c_N\to\infty\) is RH-complete, or the explicit \(N_0(c)\) grows slowly enough that the diagonal schedule reaches the super-Gevrey rate.

*Why.* It is the RH-complete axis; (a) is finite at each \(c\) and its content is the successor-shell balance of §1.3, where the arithmetic is bounded-shift prime pairs \((kn,kn\pm r)\), \(r\le 2c\), against archimedean additive overlaps; (b) is approximation theory on \(\{\log n\}\). Together they are RH; separately each is a theorem.

*First milestones.* \(c=2\) (shells \(r\le 2\) over the top half); the \(c\)-dependence of the TM floor beyond \(1+10^{-18}\) by the same scheme (the route report lists this as "just work"); an arithmetic synthesis (Ramanujan or Möbius cell weights) whose alias energy at overlap \(\varrho\) is \(o(1/\log N)\) below the quasi-analytic rate; the flip selectivity test at fixed ratio (\(\omega_p\), \(p\ge 11\)), which decides whether fixed-ratio positivity sees every prime's sign or only parity.

*Success.* Positivity at \(c=2\); or a schedule strictly below \((\log\log N)(\log\log\log N)^2\); or a proof that bounded-overlap completeness fails, which would retire (b) and promote (a) to a standalone theorem family.

### Q5.2 The point-side producer at its first rung

*Statement.* An auxiliary object over \(\mathbb Z\) with controlled size and growing \(p\)-adic multiplicity on a positive proportion of counted primes, certified without a sup norm; equivalently an upper count for the odd Liouville class at any precision better than linear.

*Why.* It is the one input every route needs, in the only form the corpus has shown can carry precision (an identity plus a count). Over \(\mathbb F_q\) it is Stepanov; over \(\mathbb Z\) the ledger, Siegel's lemma, the integrality lattice and the sawtooth split are built; the zero estimate and the flatness identity are missing.

*First milestones.* Beat the Brun–Titchmarsh constant \(2\) in intervals of length \(x^\varepsilon\); a Siegel-half ceiling at any precision \(\theta<1\) (a strip); the precision at which \(\mu\) cancels against the sawtooth \(h(n/k)\); an integer auxiliary of size \(O(x)\) with multiplicity \(\ge 2\) on a positive proportion of primes above \(\sqrt x\) (binomials are capped at one).

*Success.* Any one-sided count with a power saving on one parity class; by the dictionaries it is a strip, and by the parity form of the global law its square-root version is RH.

### Q5.3 The first fixed strip: extract or refute the Chen–Gupta–Li vanishing mechanism

*Statement.* Reconstruct the zero-free capstone of the external \(7/8\) claim from its formalized components, or locate the step that fails.

*Why.* It is the only place where a producer of any power saving is claimed to exist. If it holds, seven dictionaries become unconditional theorems at \(\theta=1/8\) and the "improve \(7/8\)" question becomes a defined optimization. If it fails, the failure will be a theorem about which pointwise vanishing mechanisms cannot exist, sharpening the density-envelope no-go. Either outcome moves the quasi-RH frontier, which has not moved since Vinogradov–Korobov.

*First milestones.* The continuation/contour step the frontier lists as open; the relation of the detector floor \(288\) to the collision quantum \(2\); the exponent as a function of the detector order.

*Success.* A formalized strip, of any width.

*Honourable mentions.* The prime-side ceiling for the Hecke defect at \(L\asymp\log T\) (ties the census dichotomy, finite support and RH); the converse Krein–Langer theorem on \(\Gamma\) (a common invariant negative subspace for all prime translations), which would make the finite-support stratum a structure theorem; the flip test at fixed ratio, cheap and decisive for the selectivity theory.

---

## 7. Question 6 — the field that would supply the missing tools

### 7.1 The walls as questions

Reading the three walls as questions no existing field answers:

- **W1.** Which property of \(\Lambda\), absent from every bounded twin, bounds a signed arithmetic form at square-root precision on an unbounded family?
- **W3.** In which topology does a sign or an index survive overlap growth, aperture growth and conductor growth, and which exhaustion carries the arithmetic point with it?
- **W14.** Which independently built structure *produces* a one-sided count, as Riemann–Roch plus Stepanov produce it over \(\mathbb F_q\)?

Existing fields answer the shadows of these questions: analytic number theory answers them with \(o(1)\) relative precision (and the corpus proves that is not enough); algebraic geometry answers them over \(\mathbb F_q\) with a surface, a Frobenius and sections; Krein–Langer theory answers W3 on \(\mathbb Z\) and \(\mathbb R\) but not on \(\mathbb Q_{>0}\) with its towers; transcendence theory produces auxiliary functions with multiplicity but has never produced a prime count. The field would be the one in which these four meet.

### 7.2 Name and point of view

**Effective arithmetic Hodge theory of the multiplicative group of \(\mathbb Q\)** (working name; the corpus's HKT and AKL are its first two chapters).

Point of view: RH is the Hodge index theorem of an arithmetic surface whose points are the primes with residue size \(\log p\), whose Frobenius is the Hecke ring of \(\mathbb Q_{>0}\) together with the successor \(n\mapsto n+1\), whose cohomology is measured by log-volumes and log-orders of finite groups rather than dimensions, whose genus is infinite, and whose boundary is the archimedean place. The index is a global invariant; positivity is its last step; the order of work is index, then count, then sign. Every theorem is stated at finite height and passes to the limit in an index-carrying topology.

### 7.3 Objects

| Object | Role | Already built |
|---|---|---|
| Hermitian kernels on \(\Gamma=\mathbb Q_{>0}\cong\oplus_p\mathbb Z\), Hecke-covariant, with towers \(\langle p\rangle\) and the archimedean completion | the Weil kernel and its truncations | HKT, AKL |
| the prime torus \(\mathbb T^{P}\) and the gauge torus; the arithmetic point \(x=0\) | spectral side; where selectivity lives | APD, ACG |
| the scaling surface (pole plane plus tests) and its height truncations | the surface whose Hodge index is RH | ACS, AOG |
| the characteristic circle \(\mu_\infty\) with power maps; torsion orbits; log-orders as intersection numbers | the only integral intersection theory over \(\mathbb Z\) | AIT, AES, RAPT |
| the group ring \(\mathbb Z[\Gamma]\): integer Dirichlet polynomials, the integrality lattice \(\mathrm{lcm}(1..N)^{-1}\mathbb Z\), the box class \(\sqrt N\cdot A\) with \(\chi=N\) | sections | ASRP, AET |
| regulators, counterterms, anomalies, survival cones | how a divergent diagonal is renormalized | RAPT, RBG, AIT |
| precision classes of weights; the square-root class \(\mathcal Q\); the battery | the admissibility calculus | ASRP, SSIC, AOT |
| atomic families at overlap \(c\); complete cells; Ramanujan quasimodes | the finite sections of the kernel | SSHA, CACT, SAHT |

### 7.4 Language

Negative index and hyperbolic pairs; Krein–Langer class; aliasing and Nyquist windows of a tower; index-carrying completion; selective versus twin-blind; precision class and stabilizer; point side versus zero side; producer versus receiver; regulator, counterterm, anomaly, null cone; log-torsion and log-volume; quadratic Euler characteristic; overlap ratio as bandwidth excess; the structure ladder (sign, support, normalization, ring). Every statement names height, aperture or overlap, conductor, the profile class, the norm, and what it gives on the golden datum, the Liouville twin and over \(\mathbb F_q\).

### 7.5 Foundational principles

1. **Irreducibility.** Any sufficient input is parity-breaking, square-root-precise, aperture-unbounded on two primes, and acts at the ring level. A statement that survives a battery move is a dictionary entry, not a theorem.
2. **Structure, not estimate.** Precision is kept by identities, counts and self-dualities; it is lost by extraction (inversion, ceilings, majorants). A positive part never pays a hyperbolic pair.
3. **Index first.** Compute or bound the index from local constituents and one global law; positivity follows. Finite index is Lindelöf-deep, so every claimed ceiling must imply LH.
4. **Point side.** Producers vanish at the primes (rational points), not at the zeros; zero-side annihilation certifies nothing.
5. **Calibration.** Reproduce Weil over \(\mathbb F_q\) by counting; fail on the golden datum, the complex fake and over-regular Beurling systems; recover PNT, Vinogradov–Korobov and Guth–Maynard in the field's own coordinates.
6. **Renormalization carries its anomaly.** Positivity passes a scale limit exactly on the null cone of the counterterm; covariance is a constraint to be proved, not assumed.
7. **One arithmetic point.** Multiplicative data see a gauge orbit; the arithmetic point is distinguished only by additive relations (successor, Bézout, cells).
8. **Formal closure.** Unconditional statements with every input discharged.

### 7.6 Criteria a theorem of the field must fulfil

Independence from zero-indexed objects; fidelity (Gamma, both poles, every prime power, multiplicities, mixed entries); the battery; parity and precision inputs visibly used; exhaustion in a named index-carrying topology with uniformity in the growing parameters; calibration over \(\mathbb F_q\) and on fakes; a new inequality, count, index ceiling or structure theorem rather than another equivalence; LH implied whenever finite index is claimed.

### 7.7 Research topics (the field's first decade)

1. **Converse Krein–Langer on \(\Gamma\).** A common invariant negative subspace for all prime translations of the Pontryagin space of a finite-index kernel; the covariant classification beyond finite spectral support and Bohr series.
2. **Arithmetic Stepanov.** Auxiliaries in \(\mathbb Z[\Gamma]\) with \(p\)-adic multiplicity; the arithmetic zero estimate (a Dyson lemma over Spec \(\mathbb Z\)); the flatness identity playing \(x^q=x\); the odd-class upper count at a power precision.
3. **Quadratic Riemann–Roch on the scaling surface.** A section count \(h^0\) of box-class size \(N\) defined without the sign, with Riemann inequality and subquadratic degree-zero growth; the theta surface's soft polarization replaced by a selective one at torsion characteristics.
4. **Covariant regulators on the characteristic circle.** A regulator of the diagonal with nontrivial null cone; Riemann–Roch on torsion orbits with defect \(\tfrac12\log|d|\); the Hodge index with adjunction (equilibrium computed, stability proved).
5. **Index-carrying completion with explicit schedules.** The slowest RH-complete overlap; arithmetic synthesis below the quasi-analytic rate; the alias fraction at bounded overlap.
6. **Local-to-global with heights.** An explicit prime certifying all zeros of height \(\le T\) (a Diophantine problem on \(\log p\), where the effective Baker bound is now available); prime-tower locality when the depth supremum is not attained.
7. **Geometry of the parity twin over \(\mathbb Z\).** Over \(\mathbb F_q\) the quadratic twist of base changes is a vertical shift and the twist tower completes the upper count; over \(\mathbb Z\) the Liouville twist acts on prime constituents. What is the object whose "base changes" produce the Liouville twist?
8. **Arithmetic Herglotz theory.** Positive measures on the circle or the prime torus constructed from primes and the successor whose moments are explicit-formula values; reflection-positive states on \(\mathbb N\rtimes\mathbb N^\times\); non-factorizable stable polynomials on the Bohr torus.
9. **Infinite symmetry.** Polar divisors of positive-genus affine Eisenstein series; an arithmetic constraint that rejects the golden datum.
10. **Depth-sensitive census.** Observables sensitive to displacement at depth \(1/\log T\) with prime-side upper bounds; the Hecke defect at \(L\asymp\log T\); two-sided coalescent pair theory.

### 7.8 First theorems the field should prove

In order of accessibility: the flip test at fixed ratio; positivity at overlap \(c=2\); a Hasse-principle-with-heights theorem (one prime certifies all zeros below \(T\), with an explicit \(p(T)\)); the covariant converse Krein–Langer theorem for orbit kernels with infinite spectral support; an arithmetic synthesis theorem below the quasi-analytic rate; a zero estimate for integer Dirichlet polynomials on two-prime supports using the Baker separation; and, as the field's signature result, a one-sided count at some power precision for one parity class.

### 7.9 What the field is not

It is not a new set of RH equivalences (the corpus has shown those are complete and E-trivial); not a positive-majorant theory (a positive part never pays a pair); not a theory of local tower data (twin-blind); not a theory of interval statistics (precision-blind); not finite-field geometry imported by analogy (curves reproduce the prime support, not the archimedean continuum). It is the theory in which the index of one Hermitian kernel on \(\mathbb Q_{>0}\) is computed from local constituents and one produced count.

---

## 8. Lean anchors for the facts cited

Census: `RHTower.three_quarters_or_simple_offLine_near_line`, `RHTower.three_quarters_within_four_div_log`, `RHTower.four_fifths_critical_ordinates`, `IncommensurableGaborPinching.simple_critical_proportion_ge_67250071`, `RHTower.ZetaThreeQuartersReduction.*` (`FrobeniusFourThirds`, `PairCorrelationFourThirds`, `frobenius_target_gue`), `ArithmeticCastelnuovoSeveri.narrowStrip_HD_one_and_twoAdic_parity_collar`.
Positivity and overlap: `TransMetzlerWeilPositivity.TransMetzlerPositivity`, `LiouvilleTwinSelectivity`, `ZeroSideStratum`, `SuperGevreyCriticalGrowth`; `CriticalArithmeticCorrelationTheory.OneHorizonMakesTheCompleteWeilMatrixPositiveThroughTouching`, `AnnularRamanujanFamiliesHaveTwoSidedFrames`.
Index and strata: `HeckeKreinToeplitz.TheGlobalLawIsTheOneSidedSquareRootCount`, `TheFiniteIndexStratumOfZetaIsLindelofDeep`, `IndexIsEnergy`, `HeatCollisionsCountTheIndex`; `ArithmeticKreinLangerTheory.TheParityFormOfTheGlobalLaw`, `LocalityIsTwinBlind`, `CompressionsAreReceivers`, `TheTwistTowerCompletesTheUpperCount`, `FineTowersDecideEveryOrbitKernel`.
Precision and integrality: `ArithmeticOfSquareRootPrecision.TheDecidingInputTheorem`, `TheGaugeStabilizerOfTheCount`, `TowerPositivityIsPrecisionExact`, `TheIntegralityExponentIsTheZeroWidth`, `IntegerDirichletPolynomialsAtArithmeticPoints`, `TheStirlingErrorSplits`, `MonotoneErrorsInvertAtMertensPrecision`.
Selection: `SelectiveMultiscaleArithmeticPositivity.PositivityAtEveryRootSelectsTheVonMangoldtWeight`, `ArithmeticCountingPositivity.LargePrimeFlipsAttainTheMaximalGap`, `CofinitePrimeFlipsHaveZeroGap`.
Quasi-RH dictionaries: `BezoutValuationIncidence.quasiRH_crossRoute_seven_way_tfae`, `ReflectiveDirichletPolynomialS2.moebius_and_prime_powerWindowSaving_iff_quasiRH`, `RHTower.three_quarters_strip_iff_chebyshevNormalizedCesaroMeanSquareEnergy_subpower`, `RHTower.DensityEnvelopeNoGo`, `RHTower.quasiRH_of_zerosApproachLine`.
Analytic inputs: `RHTower.Sieve.GuthMaynardTheoremOneOne`, `RHTower.GuthMaynardCorollariesUnconditional`, `RHTower.ZetaZeroDensityHypothesisFiveSixths`, `RHTower.Sieve.VinogradovKorobovZeroFree`, `RHTower.riemannZeta_ne_zero_of_one_sub_lt_re`, `RHTower.ZetaElevenEighteenthsLineBound`, `RHTower.DeBruijn.not_real_rooted_of_neg`, `RHTower.KiKimLeeTwoThirdsHorizon`, `RHTower.Matveev.effectiveBakerBound_holds`, `RHTower.siegel_zero_free`, `RHTower.tendsto_montgomeryForm_div_leadingOrder`.
Countermodels: `RHTower.BeurlingOverRegularIntegers.overRegular_integers_do_not_constrain_zeros`, `ArithmeticCastelnuovoSeveri.goldenDatum_*`, `ArithmeticCorrespondencePositivity.complexFake_*`.
Characteristic circle and effectivity: `ArithmeticIntersectionTheory.*` (projection formula, anomaly, local Hodge index), `ArithmeticEffectivityTheory.riemannHypothesis_iff_logTorsion_sub_eulerChar`, `RenormalizedArithmeticPotentialTheory.renormalizedPrimeForm_covariant_iff`, `torsionCounterterm_golden`.
Hecke defect and census blindness: `ConjugateDiagonalGeometry.heckeDefect_eq_second_difference`, `RHTower.ValueMomentsCannotSeparateReflectedPairs`, `ShallowCauchyPrimeEnergy.exists_uniform_xiShallowCauchyEnergy_le`.

Research log with all facts and inferences: `logs/fable2-research-2026-10-29.md`.
