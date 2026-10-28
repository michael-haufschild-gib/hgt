# Arithmetic Lorentzian Geometry (ALG)

Namespace `GaloisForLFunctions.ArithmeticLorentzianGeometry`; umbrella `ArithmeticLorentzianGeometry.lean`.

**Question.** How do arithmetic constructions produce a quadratic form with at most one positive square, and how does that
signature survive composition, restriction and passage to a limit? Target: the intersection form of the scaling surface
(infinite place, pole plane, diagonal), whose Hodge index is RH. A construction must explain the *origin* of the sign, not
restate it.

ALG owns **signature certificates**: elementary objects with proved signature, operations preserving it, and exact costs of
combining them. Over $\mathbb F_q$ Weil's theorem has this shape: Bézout makes the Frobenius Gram **Metzler**, Frobenius acts
**conformally** with factor $q$, and the Hodge index is a **trickle-down inequality** on one Frobenius ladder. Over $\mathbb Z$ the
Metzler sign is present (Euler gauge, below the spacing), local forms exist at every prime and the infinite place, and the
conformal symmetry is absent. Which arithmetic structure replaces it?

**Three problems kept separate:** construction (a form with proved signature), identification (equality/domination with the
actual intersection form incl. Γ-term, pole moments, diagonal), exhaustion (every required signed test in a topology
controlling the pairing).

**Central conjecture.** On atomic families $f_x=\sum_{n\le N}x_ng(\cdot-\log n)$ with overlap ratio $K=w/\delta_N$: $\zeta$'s Euler-gauge atomic
intersection form satisfies trickle-down at every fixed $K$, uniformly in $N$; uniformity in $K$ is RH. Small overlap is the
**stability regime** (ends at the Robin–Euler threshold $\exp(2\theta'(0)+\kappa_L(\varphi)+\gamma)$ below the spacing); the rest of bounded overlap is the
**trickle-down regime**; beyond $K=1$ no gauge of the atoms is Metzler.

---

## 1. Place in the research

| Programme | Interface |
|---|---|
| ArithmeticCastelnuovoSeveri | Scaling surface, pole plane, Hodge target, curve calibrations |
| SpacingScaleHarmonicAnalysis | Separated-regime stability, universality, diamagnetism, non-ratio lags, fixed-width RH criterion |
| RenormalizedArithmeticPotentialTheory, RenormalizedBiarithmeticGeometry | Counterterm rank, horizon counterterms, finite parts |
| ArithmeticIntersectionTheory | Prime ladders, tower forms |
| ArithmeticElectrostatics, ArithmeticIndexDescent | Transverse energy, quantization, index bounds |
| BiarithmeticGaugeGeometry, ArithmeticCorrelationGeometry | Gauge torus, successor connection |
| ArithmeticPolarization, ConjugateDiagonalGeometry | Reflected pairing, even–odd splitting |
| ArithmeticEffectivityTheory, ArithmeticOrientationGeometry | Counting, Weil planes, Rosati signs |
| IncommensurableGaborPinching | Structural Gram slack discarded by scalar estimates |
| `HTGeometry`, `RHTower` (Li criterion) | Inertia, Schur complements; Cayley images of zeros |

---

## 2. Objects and language

`IsHyperbolic Q`: reverse Cauchy–Schwarz $Q[x]Q[y]\le B_Q(x,y)^2$ when $Q[x]>0$ (⇔ at most one positive square). `IsLorentzian Q`: plus entrywise
nonnegativity; `IsMetzler Q`: nonnegative off-diagonal. Both depend on coordinates. *Hyperbolic* describes a form, not real-rootedness.

| Object | Role |
|---|---|
| Pole plane $\langle H,V\rangle$, $H^2=V^2=0$, $H\cdot V=1$ | Positive direction; global degree data |
| Anchor $e$, polar row, Schur reserve $R_Q(x)=B_Q(e,x)^2/Q[e]-Q[x]$ | Primitive hyperplane; negative energy left |
| Polar dispersion $V_e$, $C_e$ | Exact incompatibility of local polar rows |
| Row sums $D=Q\mathbb 1$, weights $\pi$ | Stability regime $Q\pi\le0$ vs trickle-down regime $Q\pi>0$ |
| Links $T_i$, $\sum T_i=Q$ | Local pieces whose signature yields the global one |
| Trickle-down defect $QD^{-1}Q-Q$ | The PSD quantity that *adds* (unlike hyperbolicity) |
| Hodge completion; half-defect correction | Transfer a repair preserving the pole plane; rank cost |
| Isometric / conformal ladders $(\lambda^{\min(i,j)}a_{|i-j|})$ | Where the positive square can live |
| Lorentzian polynomials, mixed Hessians | Higher-degree certificates and their closure |
| Overlap ratio $K$; ratio / non-ratio lags | Where a form first reads the gauge |
| Cayley points $w_\rho=1-1/\rho$, Li couplings, Cayley ladder | FE as reflection $w\mapsto1/\bar w$; RH as reflection positivity |
| Window tests $\sum_nG_n(\cdot-\log n)$ | Arbitrary $C^2$ profiles near the logarithms |

---

## 3. Principles

Fix the pairing (name the full form and test space). Prove local signature from the source (no link carrying the desired
inequality as a field). Measure compatibility (local signatures need not add; pole budgets cannot be spent twice). Separate
gauge selection from sign production. Demand selectivity (coefficient-size estimates hold for every bounded twist and stop at
a finite overlap). Keep global resources global. Treat the limit as mathematics. State the scope of an obstruction.

---

## 4. Mechanisms

1. **Degree-two calculus**: hyperbolicity ⇔ nonpositivity on a hyperplane; preserved by pullback and domination, *not* by sums
   (two Lorentzian rank-ones add to the identity); conditionally negative definite forms are the sum-closed class.
2. **Arithmetic bridge**: RH ⇔ every finite Hermitian Gram of the scaling surface is hyperbolic; a nef shift makes any form with a
   hyperbolic plane entrywise nonnegative without changing inertia — nonnegativity informs only in a fixed basis.
3. **Metzler trickle-down**: for connected Metzler $Q$ with positive row sums, one positive square ⇔ $Q[v]\le\sum(Qv)_i^2/D_i$ ⇔ hyperbolic links
   (rank one + NSD); quantitative version gives $Q\le\mu_-(\varepsilon)D$ on the primitive hyperplane.
4. **Metzler dichotomy**: $Q\pi\le0$ for some $\pi>0$ ⇒ $Q\le0$ (stability); otherwise hyperbolicity ⇔ weighted trickle-down $(TD_\pi)$. Every unconditional
   positivity of Weil's form on atomic families has the stability shape.
5. **Finite-field calibration**: Frobenius Gram is Metzler iff counts nonnegative (Bézout); Hodge index ⇔ $(TD_\pi)$; golden datum is
   Metzler, connected, violates $(TD_\pi)$. $(TD_\pi)$ on every ladder ⇔ $|\beta_i|=1$ ⇔ one-sided square-root count; hyperelliptic curves satisfy it
   via Stepanov; a finite piece of the ladder decides; Kloosterman factors trickle down by Weil's bound.
6. **Ramanujan vs Lorentzian**: a local factor is Lorentzian only at the Weil bound (log-concavity forces $a_1\ge d\sqrt q$), hence never at a prime.
7. **Atomic family below the spacing**: the Markov pairing makes the Gram of $H,V,g_1..g_N$ Metzler and connected; Weil positivity ⇔ $(TD_\pi)$.
8. **Stability at a fixed fraction**: tilted per-atom margins $\mu_m\ge1+(m/8N)\log m$ pay the pole term $2AB$ (weighted Cauchy–Schwarz) ⇒ Weil's
   form nonnegative on every signed atomic test at $w\le c_\star\delta_N$ — twist-blind.
9. **Uniform margin stops at $K\sqrt{\log N}$** (rank-two model); the pole is paid by growth of the margin along $n^{1/2}$.
10. **Overlap law and Metzler threshold**: overlapping atoms meet positively (overlap × self-energy, constant one), separated ones strictly
    negatively; an odd triangle frustrates every unimodular gauge ⇒ Metzler threshold of the overlap ratio is exactly $K=1$.
11. **Metzler sign is selective**: a twin flipping a prime $\le N$ has no Metzler gauge below the spacing.
12. **Pole defect pays the pole**: multiplicative Hardy inequality $(\sum\sqrt nx_n)^2\le C_H(N^2/\log N)(D_N+|x|^2)$ with the pole defect $D_N$; positivity at an
    explicit fraction $K_\star$ eventually; on **window tests** (any $C^2$ profile near the logarithms) at $K_\star^\infty$, hence on every $C^2$ test supported within
    $K^\infty_\star\delta_N$ right of $\log n$; sharp constants reach $\approx K_{RE}/4$ for plateau profiles; absolute payment of the pole stops near $K_{RE}/2$.
13. **End of stability**: beyond the Robin–Euler threshold the atom block has a positive square along the pole vector.
14. **Rank-two reduction**: $Q+2AB\ge0$ ⇔ $Q\ge0$ on $\ker A$ and $Q+2B\ge0$ on $\{A=1\}$; for atomic tests $A$ is the pole functional at every width.
15. **Conformal symmetry**: Frobenius is conformal ($T^\top G_{K+1}T=qG_K$); Hecke dilations are boosts (factor one); a decaying isometric ladder has
    Hodge index at every depth iff NSD — the positive square cannot live there; conformal ladders carry it iff normalized couplings
    do not decay. Along $p$-ladders the prime pairing grows like $wp^{k/2}$ (candidate conformal weight).
16. **Cayley ladder**: multiplication by $w$ preserves the reflected pairing and is conformal with factor $|w_\rho|^2$ at each zero; RH ⇔ reflection
    positivity ⇔ Metzler sign of the Li ladder (trickle-down sits inside the sign).
17. **Gauge**: modulo archimedean characters the positivity locus of the gauge torus is the Euler point; periodic successor holonomy is flat.
18. **Lorentzian polynomials**: mixed Hessians trickle down; closure under differentiation, nonnegative substitution, products; Euler
    products of Lorentzian local factors are Lorentzian — blind to the Euler point; mixed-Lorentzian supports are M-convex.
19. **Polar gluing and reflection splitting**: exact price of gluing local forms; optimal repair of the odd sector with rank cost.
20. **Turán layer**: Laguerre inequality for Jensen polynomials of $\xi$ on the half-line.

---

## 5. Pillar theorems

1. **Metzler trickle-down theorem and dichotomy** (modules `TheHodgeIndexTricklesDown`, `TheMetzlerDichotomy`).
2. **Trickle-down = square-root count over $\mathbb F_q$** (`forall_weightedTrickleDown_iff_exists_pointCount_ge`, `hyperelliptic_weightedTrickleDown`).
3. **Ramanujan–Lorentzian rigidity** (`ramanujan_lorentzian_rigid`, `not_isLorentzianPoly_at_prime`).
4. **Atomic form is Metzler below the spacing; Weil positivity ⇔ $(TD_\pi)$** (`weilQuad_finAtomicTest_nonneg_iff_weightedTrickleDown`).
5. **Hodge index at a fixed fraction of the spacing** (`weilQuad_atomicTest_nonneg`, `atomicIntersectionGram_isHyperbolic`).
6. **Metzler threshold is exactly the spacing; selectivity** (`metzlerThreshold_overlapRatio`, `not_exists_nonneg_gauge_twinAtomicIntersectionGram`).
7. **Pole defect pays the pole; positivity near the logarithms** (`sq_vRow_le`, `eventually_weilQuad_nonneg_of_support`,
   `eventually_weilQuad_windowTest_nonneg_quarter`).
8. **Rank-two reduction at every width** (`forall_weilQuad_atomicTest_nonneg_iff`).
9. **Isometric ladders carry no positive square** (`forall_isHyperbolic_toeplitzLadder_iff`, `forall_isHyperbolic_conformalLadder_iff`).
10. **RH is reflection positivity of the Cayley ladder** (module `RHIsReflectionPositivityOfTheCayleyLadder`).

---

## 6. Traps

| Tempting inference | Correction |
|---|---|
| Every prime piece positive ⇒ global Hodge index | Specify common pole allocation and dispersion payment |
| Subtracting a positive correction proves the signature | It proves it for a different form |
| Nonnegative coefficients + connectivity ⇒ Hodge index | Golden datum passes both; trickle-down is the content |
| Stability-regime positivity carries the arithmetic | Holds for every bounded twist |
| Sharper constants reach the spacing | They reach $\approx K_{RE}/4$; beyond the threshold the mechanism must change |
| Beyond the spacing a better gauge restores Metzler | Odd triangles frustrate every gauge for $K>1$ |
| A positive Euler product gives the arithmetic sign | Its Hessian is Lorentzian for every nonnegative datum; not the Weil pairing |
| Local L-factors are Lorentzian by RH over $\mathbb F_p$ | Only the ladder trickles down; the polynomial is Lorentzian only at the Weil bound |
| Li positivity is a weak sign condition | On the Cayley ladder the Metzler sign is RH |
| A Hecke dilation plays Frobenius | Dilations are isometries; decaying isometric ladders carry no positive square |
| A nef shift repairs the form | It changes coordinates |
| Positive local sections exhaust the criterion | An atomic test of ratio $K$ lives on measure $\le K$; needs a signed transfer |
| Lorentzian log-concavity ⇒ Jensen real-rootedness | Real stability is stronger |

---

## 7. Open problems

1. **Trickle-down for $\zeta$**: $(TD_\pi)$ between $c_\star$ and the spacing (Metzler structure holds there); equivalently a gap of $M$ on the pole complement plus one
   scalar condition. Beyond the Robin–Euler threshold the payment must come from cross terms.
2. **Metzler beyond atomic resolution**: a non-atomic basis (differences, wavelets, Hecke orbits) in which the overlapping form is Metzler, or a
   direct primitive gap $Q\le(1-g)D$ at fixed $K>1$.
3. **Renormalized links** from source-defined pieces (tower forms $-2\gamma_p+\log p(K_q-1)$, archimedean jump Laplacian, pole plane), with who pays $2d_p$ at
   small primes.
4. **Arithmetic polar compatibility** beyond the Robin–Euler threshold.
5. **Conformal dynamics**: a conformal correspondence with $\lambda\ne1$ (candidate weight $wp^{k/2}$), or a source-built reflection-positive functional whose
   Cayley ladder is the Li ladder (candidate: KMS states of $\mathbb N\rtimes\mathbb N^\times$, reflection $\beta\mapsto3-\beta$).
6. **Signed overlap and exhaustion**: one estimate keeping overlap Gram, lag form, archimedean cross form and both poles; transfer to exhaustive
   families (overlap growing like $\log N$, or assembly across levels).
7. **Higher-degree lifts**: a Lorentzian lift of the Weil pairing through the closure with Γ-term, pole plane, diagonal identified.
8. **Selectivity calibration** of every certificate; **exceptional extinction** combining with AES/AID energy quanta.

## 8. Tools to build

A non-atomic Metzler basis; renormalized link decompositions with controlled residual; a conformal correspondence over $\mathbb Z$;
a signed overlap transfer.

## 9. Success criteria

Unconditional theorems about explicit objects; algebraic criteria expose their structural conditions and prove them when
applied; each contribution names the producer or transfer step it improves, its behaviour on the relevant twin or fake datum,
and the positive boundary of a retired mechanism. Full success: a source-defined signature construction for the actual Weil
form on an exhaustive signed family.
