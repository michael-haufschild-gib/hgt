# Arithmetic Correspondence Positivity (ACP)

Namespace `GaloisForLFunctions.ArithmeticCorrespondencePositivity`; umbrella `ArithmeticCorrespondencePositivity.lean`.

**Question.** Over $\mathbb F_q$ one structure — the intersection theory of correspondences on $C\times C$ — supplies the sign of
the explicit formula (Rosati positivity, Hodge index), its budget ($2g$), the base and the tensor powers. Over $\mathbb Z$ the
corpus has the pairing, the Lefschetz receivers and the exhaustion of every substitute tried. What is the positivity
theory of **arithmetic correspondences** — dilations (gauge invariant), affine maps and additive relations (gauge
charged), the archimedean flow — which layers of Weil's argument exist for them, which are free, which are provably
absent, and what would a sign specific to $\zeta$ have to look like?

ACP joins ArithmeticPositiveDuality (rigidity/capacity) and ArithmeticCorrelationGeometry (gauge torus) with the object
neither has: **a ring of correspondences with graphs, degrees, a Rosati involution and a budget**. Basic object: a
*correspondence surface* (polar surface with a ring acting by similitudes). Basic invariant: the **Rosati trace**
$\tau_x(\xi)=\delta(\xi\cdot x,x)$. Basic measurement: the **local type** of a correspondence at a reflection pair $\{\rho,1-\bar\rho\}$.

---

## 1. Place in the research

The B-tier obstacles are one obstacle: *a positivity of gauge-charged correspondences with a fixed budget*. Every known
forcing mechanism has a sharp limit:

| Mechanism | Sharp limit | Owner |
|---|---|---|
| Quadratic positivity on carriers | blind, half-blind or isotropic fibres at off-line pairs | ACS, APD |
| Multiplicative positivity | boundary and capacity $\lfloor k/2\rfloor$ | MPG, SBWF |
| Linear rigidity | determines $\zeta$, never sees zeros | APD |
| Pole order | pays inserted zeros exactly, intrinsic not at all | SBWF, RHTower |
| Multiplicative data | gauge orbits only | ACG |
| Amplification over $\mathbb Z$ | loses linearly | ACG, AKT, ACP |
| Affine positivity on $\operatorname{Aff}(\mathbb Q)$ | induced from dilations | APD |
| Weil's receiver over $\mathbb Z$ | complete: one prime, one test, $|c_m|\le c_0$ ⇔ RH | ACS, AOG |

| Programme | Interface |
|---|---|
| ArithmeticOrientationGeometry | Scaling data, correspondence algebra, Rosati, Hecke graphs, spline orbit |
| ArithmeticCastelnuovoSeveri | Polar surfaces, curve data, golden datum, genus-one Hasse, maximal blind ideal |
| ArithmeticPositiveDuality, ArithmeticCorrelationGeometry | PD on $\mathbb Q_{>0}$ and $\operatorname{Aff}(\mathbb Q)$; gauge charge, escape states on the gauge torus |
| MultiplicativePositivityGeometry, StripBochnerWeilForcing | Boundary forcing, completed positive systems |
| ArithmeticKunnethTheory | Product receivers see depth only through total length |
| ArithmeticDefectRigidity | Cofactor modules, escape states, translated-zero eigenstates |
| SquareRootThreshold | Aperture-$3/10$ certificate for every prime weight |

---

## 2. Why

**Weil's proof in layers.**

| Layer | Over $\mathbb F_q$ | Over $\mathbb Z$ | Forces the sign? |
|---|---|---|---|
| L1 Identities | Lefschetz, adjunction, Rosati, $FF'=q$ | exact | no (golden datum) |
| L2 Graphs | graph map quadratic (theorem of the square) | exact for normalized graphs | no |
| L3 Budget | $\delta(\Delta,\Delta)=2g$ fixed along the orbit | $\delta(x,x)$ fixed along every Hecke orbit | no (golden budget 2) |
| L4 Kernel counts | $\deg P(F)=\prod P(\alpha_i)\ge0$; exterior counts on $\Lambda^kH^1$ | affine maps have genus zero; archimedean contractions with pole tax | $H^1$ counts see only real pairs; exterior counts force unitarity |
| L4′ Spectrum of $ff'$ | eigenvalues $P(\alpha)P(q/\alpha)\ge0$ | the critical line at one prime | yes = purity |
| L5 Rosati positivity | $\operatorname{Tr}(\xi\xi')\ge0$ from a polarization | ⇔ RH | yes |
| L6 Base | Deligne's fixed loss | a fixed loss is RH | — |

L1–L3 transfer intact and are satisfied by the golden datum: the budget is free; what $\mathbb Z$ lacks is its
**sufficiency**, on every span $\{x,Tx\}$ the positivity of the normalized graphs of $1\pm T$.

**Two kinds of effectivity.** Kernel counts $\prod P(\alpha_i)$ pair each eigenvalue with its *conjugate*; the Rosati trace
$\sum P(\alpha_i)P(q/\alpha_i)$ with its *reflection*. They coincide in genus one (Hasse) and separate from genus two: the complex
fake ($q=16$, roots $\pm8i,\pm2i$) has nonnegative point and kernel counts and violates Hasse–Weil. $\zeta$'s off-line
candidates are non-real, so $H^1$ kernel-count effectivity is blind to all of them.

**Local types.** At an off-line pair the local form $2\Re(u\bar v)$ has signature $(1,1)$:

| Type | Action on the fibre | Correspondences | Positivity forces |
|---|---|---|---|
| Hyperbolic | boost $\operatorname{diag}(\beta,\bar\beta^{-1})$, $|\beta|\ne1$ | Hecke operators, archimedean flow, all gauge twists — exactly off the line | isotropy / half-blindness |
| Elliptic | rotation or reflection swap | Hecke on the line; symmetric Hecke at a resonant prime; FE | a phase condition only |
| Unipotent | identity on the polar part | the additive successor | nothing |

**Multiplicative symmetry is hyperbolic exactly at off-line zeros** — the common origin of blindness, half-blindness and
isotropy. A non-real point resonates ($\gamma\log p\in\pi\mathbb Z$) at no more than one prime, so two primes force blindness.

**Localization and source.** Bounded-aperture carriers are positive beyond isotropy but do not localize and are
source-blind; on nonnegative tests $\zeta$ is the worst member of its sign orbit. A sign specific to $\zeta$ must localize,
have a non-hyperbolic local symmetry at off-line pairs, and live on autocorrelations changing sign at prime-power logs.

**Escape and budgets.** The cofactor Gram of the damped receiver is a translation Gram of one log profile with Laplace
symbol $G(s)=\zeta(s)(1/\zeta(s+\varepsilon)-\Re(1/\zeta(1+\varepsilon)))/s$; escape states of the deepest zeros are phase kernels of rank = number of
those zeros. Energy budgets of arithmetic rows are paid by residues of their symbols at zeros: Weil's $2g$ reappears as
Cramér's constant $\sum m_\rho^2/|\rho|^2\ge2+\gamma-\log4\pi$.

---

## 3. Objects and language

| Weil over $\mathbb F_q$ | ACP object | Lean |
|---|---|---|
| $C\times C$, NS | correspondence surface; scaling surface with Hecke algebra of $\mathbb R_{>0}$ | `ScalingDatum` (AOG), `scalingSurface` (ACS) |
| $\operatorname{End}(J)$ | correspondence ring, Rosati $\xi'(g)=\xi(-g)$ | `Correspondence`, `rosati` (AOG) |
| graph $\Gamma_f$, $\deg f$ | normalized graph $N(y)$, $\deg N(y)=\delta(y,y)/2$ | `normGraph`, `graphDegree` |
| $2g$ | budget $\delta(x,x)$ | `CurveDatum.diagonal_defect` |
| $\#\ker P(F)$; $\operatorname{Tr}(PP')$ | determinant degree; Rosati degree | `detDeg`, `rosatiDeg` |
| $\alpha\mapsto q/\alpha$ | reflection pair, local form | `localForm` |
| Frobenius eigenvalue | Hecke symbol $p^{s-1/2}$; symmetric $p^{s-1/2}+p^{1/2-s}$ | `heckeSymbol`, `symHeckeSymbol`, `symHecke` |
| — | successor defect $D_a(s)$ | `succShiftDefect` |
| fake curves | golden datum (real pair), complex fake (quartets) | `goldenDatum`, `complexFake` |
| — | sign/Liouville/flipped twins | `liouvilleTwin`, `flipTwin` |
| — | log profile, translation Gram, phase kernel, Cauchy form | `logProfile`, `escapeKernel`, `cauchyDensity` |
| — | Abel Gram, line symbol | `abelGram`, `lineSymbol` |
| — | completed systems with height coupling | `HeightCoupledSystem`, `FejerCoupledSystem` |
| — | quadratic terminal of the Xi divisor; source field | (`EveryXiZeroHasASourceField`) |

**Words.** *Sufficiency* (Weil's inequality on every span $\{x,\xi x\}$); *resonant prime*; *localizing carrier*; *dominated
source* ($w\le\Lambda$); *loss* of an amplification; *escape state*, *dominant configuration*, *escape rank*;
*subdominant remainder*; *quadratic terminal* (a zero with empty quadratic ascent cone).

---

## 4. Mechanisms

1. **Normalization of graphs**: unique modulo fibres, degree = half the defect, graph map quadratic.
2. **Similitude law**: Hecke graphs multiply degrees by $e^{s(g)}$; normalized ones keep them.
3. **Determinant vs trace**: conjugation pairs determinant factors into $|\cdot|^2$ when no eigenvalue is real.
4. **Boost lemma**: positivity of $2\Re(u\bar v)$ on a cyclic span under a boost forces $u\bar v=0$; under a rotation only $\Re(u\bar v)\ge0$.
5. **Lagrange localization** on finite spectra; **resonance arithmetic** $\Im(p^{\rho-1/2}+p^{1/2-\rho})=2\sinh((\sigma-\tfrac12)\log p)\sin(\gamma\log p)$.
6. **Unit step**: the successor shift is a holomorphic perturbation on $\Re s>0$; in the strip of size $|t|^{1-\sigma+\eta}$; a bounded Hardy perturbation.
7. **Affine source**: the Weil functional is affine in the prime weights, antitone on nonnegative atoms.
8. **Root extraction**: $|c|^k\le Ce^{Lt}$ gives width $\le L/k$.
9. **Dilation is translation** on the log scale (pronic measure = Lebesgue); **Cauchy positivity** of escape forms;
   **horizon averaging** kills cross terms at the inverse spacing; **floor error** makes power rows exponential profiles.
10. **Contractions with pole tax**: archimedean midpoint symmetric squares contract real off-critical pairs at $\Delta\kappa=0$;
    complex quartets obey a Post–Widder real-anchor law; height/Fejér coupling removes the marginal tax.
11. **Abel calculus**: energy $O(T^\kappa)$ ⇒ $L^1\cap L^2$ damped profiles with symbol $\Phi_v(s)/s$; Wiener–Khinchin; simple
    poles on the abscissa carry atoms $\pi\|r\|^2\delta_{y_0}$.
12. **Squared logarithmic derivative**: $\Lambda\star\Lambda$ has Dirichlet series $(\zeta'/\zeta)^2$; at a zero of multiplicity $m$ its simple
    Laurent coefficient is $2m\times$(regular part) = the transverse field of the other zeros + archimedean term.

---

## 5. Pillar theorems

1. **Theorem of the square is free; RH ⇔ every normalized Hecke graph of the spline has nonnegative degree**
   (`normGraph_square`, `riemannHypothesis_iff_splineCycle_graphDegree_nonneg`, `goldenDatum_normGraph_degree_neg`).
2. **Budget free, sufficiency not** (`budget_sufficient_iff_unitary`, `complexFake_budget_insufficient`).
3. **Kernel counts are blind to complex quartets** (`detDeg_nonneg_of_im_ne_zero`, `counts_do_not_force_purity`).
4. **Off-line fibres are hyperbolic; two primes force blindness; elliptic localization is resonance**
   (`mul_conj_eq_zero_of_cyclic_nonneg`, `eq_zero_of_two_prime_symCyclic_nonneg`, `separating_isometry_is_boost`,
   `eq_zero_of_archimedean_closed`).
5. **The successor is unipotent** (`norm_twisted_heckeSymbol`, `differentiableOn_succShiftDefect_vonMangoldt`).
6. **Positivity beyond isotropy does not localize; $\zeta$ is the worst twin on nonnegative tests**
   (`positivity_beyond_isotropy_at_finite_aperture`, `weilPositive_nonneg_transfers`).
7. **The base is a fixed loss; every family average loses linearly** (`riemannHypothesis_iff_fixed_tensor_loss`, `family_moment_le`).
8. **Affine correspondences of $\mathbb Z$ have genus zero** (`fixedPoints_iter_subsingleton`, `affine_graphs_meet_at_most_once`).
9. **The spectrum of symmetric squares is the sign** (`symSquare_spectrum_nonneg_iff_unitary`,
   `riemannHypothesis_iff_symSquare_heckeSymbol_nonneg`).
10. **Exterior kernel counts force unitarity; contractions and pole taxes** (`unitary_of_exteriorDetDeg_nonneg`,
    `CompletedPositiveSystem.contractRealPair`, `real_anchor_of_posDef_polarSum`, `CompletedPositiveSystem.heightCouple`).
11. **Section count and Stepanov count are the sign** (`riemannHypothesis_iff_exists_sectionCount`,
    `riemannHypothesis_iff_one_sided_count`).
12. **Escape classification**: translation Gram, Laplace symbol, escape rank = number of dominant zeros, escape alternative
    (`pronicPairing_rowDilate_eq_translationGram`, `tendsto_laplace_cofactorProfile`, `escapeForm_log_eq_zero_iff`,
    `riemannHypothesis_iff_forall_admits`).
13. **Energy budgets pay residues**: Mertens and prime-error energies have unconditional lower slopes
    $\sum\|1/(\rho\zeta'(\rho))\|^2$ and $\sum m_\rho^2/|\rho|^2\ge2+\gamma-\log4\pi$; a Mertens budget forces RH + simple zeros; over $\mathbb F_q$ a
    budget is purity with simple spectrum, slope = repulsion energy (`not_forall_primeError_energy_le_linear`,
    `not_forall_primeError_energy_le_of_lt_poleSharpConstant`, `curveMertens_budget_iff`, `tendsto_curveMertens_energy_div`).
14. **Abel–Cramér law**: RH ∧ simple zeros ⇔ Abel slope of the prime-error profile → $2+\gamma-\log4\pi$
    (`riemannHypothesis_and_simple_iff_tendsto_abelSlope`).
15. **Source field at every Xi zero**: simple Laurent coefficient of $(\zeta'/\zeta)^2$ = transverse field of the other zeros +
    archimedean term; quadratic terminals and outward rays give positive reserves (`EveryXiZeroHasASourceField`,
    `EveryRightZeroReachesAnOutwardZetaRay`).

---

## 6. Traps

| Trap | Truth |
|---|---|
| Adjunction/budget is what $\mathbb Z$ lacks | Free; sufficiency is missing |
| Kernel counts give effectivity | Blind to complex quartets; $\zeta$'s candidates are non-real |
| Symmetric Hecke positivity sees real off-line points | Real points resonate at every prime |
| More primes in a carrier help | Two already force blindness; the issue is localization without hyperbolicity |
| Bounded-aperture positivity is about $\zeta$ | Holds for every prime weight |
| Positivity on nonnegative tests transfers sign info | $\zeta$ is the worst twin there: an upper-bound statement |
| The successor is a correspondence with content | Unipotent: positivity forces nothing |
| A section count or Stepanov count is a weaker input | Each is RH |
| Escape completeness is a positivity question | It is an energy split of the profile with symbol $G$ |
| Zero-tax quartet contraction is free | Real-anchor law: a pole tax unless coupled across heights |
| Cramér's constant needs RH | Its lower bound is unconditional; the matching upper bound is RH + simplicity |
| The full source work at a zero has a sign | Only transverse pair energy is signed; the exterior interaction is kept, unsigned |

---

## 7. Open problems

1. **A localizing carrier with an elliptic local symmetry** via a non-multiplicative operation, unconditionally positive;
   separating $\zeta$ from its twins on it would be an RH-strength forcing input.
2. **The first gauge-charged window**: Liouville twin positivity on the edge-concentrated tests of $[-181/500,181/500]$.
3. **Intrinsic exterior square over $\mathbb Z$** without shifted poles: non-linear $GL(2)$ / cohomological lifts (shift-polynomial
   and unshifted-system routes are settled negative).
4. **Successor regular part**: a pointwise lower bound off the real axis.
5. **A base from a non-multiplicative structure** with loss independent of the power (would prove RH).
6. **Explicit-formula split of the cofactor profile** off RH: contour shift of $G(s)e^{su}$ past translated zeros (needs growth of
   $1/\zeta(s+\varepsilon)$ between zeros); the mass at infinite height of the damped receiver when residues are summable — a vertical
   mean square of $\zeta(s)/\zeta(s+\varepsilon)$ near the abscissa line.
7. **Sign of the source work**: control the exterior interaction term of the source-field identity at a quadratic terminal.

## 8. Tools to build

A localizing non-multiplicative carrier; a non-linear exterior lift; vertical mean-square bounds for $\zeta(s)/\zeta(s+\varepsilon)$;
a signed estimate for the exterior source interaction at quadratic terminals.

## 9. Contribution standard

Unconditional; name the Weil layer it concerns and the local type of every correspondence used; report on the battery
(curves reproduce Weil; golden datum and complex fake fail; Liouville and flipped twins; pole-order strays); separate
inserted from intrinsic charge; record the positive survivor of every no-go.
