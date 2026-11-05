# Critical Hardy Theory of the Window Cone (CHT)

Namespace `GaloisForLFunctions.CriticalHardyTheoryOfTheWindowCone`; umbrella
`CriticalHardyTheoryOfTheWindowCone.lean`; 13 modules. Every theorem here is unconditional; equivalences with RH are
labelled. CHT is the receiver programme of the Riemann Hypothesis work in this corpus: the exact theory of what a proof
must deliver on each window, at what precision, with what boundary behaviour and with what canonical-system structure.
Its partner, Arithmetic Production at Square-Root Precision (`ArithmeticProduction/README.md`), is the producer
programme: where such an input could come from.

## 1. The field

Weil's form on a window is a signed nonlocal quadratic form

$$W_\lambda(f)=H(f)-P_\lambda(f),\qquad P_\lambda(f)=\sum_{n\ge2}\lambda(n)n^{-1/2}\bigl(k_f(\log n)+k_f(-\log n)\bigr),$$

where $k_f=f\star\tilde f$ and $H$ is the archimedean–polar form: a logarithmic-order jump form with symbol
$1+\tfrac12\log(1+\xi^2)$ up to a bounded convolution, with the pole kept. The weights $\lambda(n)$ are free real
numbers. The field studies the nested convex sets

$$\mathcal A(c)=\{\lambda : W_\lambda\ge0\text{ on }[-c,c]\},$$

their best margin $\lambda^*(c)=\sup_\lambda\inf_f W_\lambda(f)/\lVert f\rVert^2$, the data (pole weight, conductor)
that define them, the edge of the window where the energy lives, and the aperture as a canonical-system parameter. The
intersection $\bigcap_c\mathcal A(c)$ is $\{\Lambda\}$ under RH and empty otherwise, while only $\Gamma$, the pole and the
positions $\log n$ enter the definition. RH is the limit statement $\lambda^*(c)\to0$. Criticality, frustration,
logarithmic boundary behaviour and de Branges structure meet on this one object; Hardy theory, Dirichlet form theory,
Wiener–Hopf theory and inverse spectral theory each cover only part of it.

The field has three theories bound by one limit theorem.

1. **Cone theory.** The shape of $\mathcal A(c)$: convexity, cylinders beyond $e^{2c}$, bounded entering coordinates,
   compact stage fibres; the pinning of every coordinate to $\Lambda(n)$ at an exponential rate in $c$; the margin law
   (doubly exponential ceiling, floors at the tower apertures); the bands of each weight; the classification of the data
   $(\beta,s)$ for which the cones are nonempty; the sign structure forced on the cone (positivity of prime-power
   weights from a finite window, frustration in every sign gauge).
2. **Edge theory.** The boundary behaviour of window energies and solutions: the Wiener–Hopf factor of the archimedean
   symbol, the positive causal kernel, the half-line Green operator, the $\sqrt{\log(1/t)}$ edge law of window
   solutions, regional–edge splitting, the absence of point traces. This theory is independent of arithmetic.
3. **Transport and canonical-system theory.** The aperture as a parameter: stage forms and fold energies at the prime
   powers, head windows under Dirichlet shifts, the de Branges chain of complete Weil spaces before contact, its
   reproducing kernels, orthogonal increments, exterior crossings, and the Hamiltonian density of the evaluation Gram,
   whose singular part is the contact.

The limit theorem binding them: positivity at a finite aperture is consistent with every zero width, and every
statement uniform in $c$ is RH or the width. CHT therefore does not aim at a sign for $\zeta$. It produces the exact
finite-level theorem a proof must meet, and it closes the alternatives: other weights, other data, other gauges, other
formats.

## 2. Objects

| Object | Meaning |
|---|---|
| Window cone $\mathcal A(c)$ | weights with $W_\lambda\ge0$ on tests supported in $[-c,c]$ (`windowCone`) |
| Band | the set of values of one weight $\lambda(n)$ over $\mathcal A(c)$ (`bandSet`) |
| Margin, best margin $\lambda^*(c)$ | `HasMargin`, `bestMargin`: the largest margin over all weights, the inradius of the cone |
| Hardy interval $\mathcal H(c)$ | $\{t : H-tP_\Lambda\ge0\text{ on }[-c,c]\}$, a closed antitone interval (`FrustratedArithmeticDirichletForms`) |
| Onset aperture $a^*$ | supremum of positive half-widths; $a^*(\zeta)=\top$ iff RH (`WindowVisibilityLaw`) |
| Blind family | positive combination of autocorrelations vanishing at every $\log n$, $n\ge2$ |
| Null family | the twisted-arc tests $F_j$, $\hat F_j=\Xi Q_j$, near null on every point of the cone |
| Gaussian test | $Y_t(v)=2e^{-3v/2}\exp(-\pi t^2e^{-2v})$ (`gaussTest`), the second slot of the atom reading |
| Hamburger series | $S(t)=\sum_{n,k}\delta(n)\,\mathrm{ker}(kn,t)$ (`readS`), and the entire function $T=\sinh^3(\pi t)\,\Delta_i^2S$ (`poleT`) |
| Datum | pole weight $\beta$ and log-conductor $s$ (`datumCone`) |
| Window equation | $E(f,u)=\langle f,g\rangle$ for finite-energy $f$ on the window, with $g$ dominated by constants and translates of $u$ |
| Edge coefficient | the limit of $u(-a+t)\sqrt{\log(1/t)}$ |
| Causal kernel, Green operator | the logarithmic Poisson factor of $1+\tfrac12\log(1+\xi^2)$ and the half-line operator $CC^*$ (`CanonicalSystemOfTheWindowTower`) |
| Stage form, fold energy, head window | the increment of the form across a prime power, its signed fold, and the length-$\log d$ window left by a Dirichlet shift (`WindowTowerOfSpecZ`, `ArithmeticHodgeTheoryOfDegenerations`) |
| Complete Weil space, Riesz vector, kernel | the de Branges space of a window before contact, its evaluation vectors $E_a(z)$ and reproducing kernel $K_a(w,z)$ (`CanonicalSystemOfTheWindowTower`) |
| Evaluation Gram and density | $G(a)=\lVert\sum_i\alpha_iE_a(z_i)\rVert^2$ and $G'$ (`evalDensity`) |
| Contact | the first aperture at which some diagonal kernel diverges; $a^*(\zeta)$ off RH |

## 3. Language

- **Critical**: no Hardy weight survives; the slack of the limit form is zero in every sense.
- **Frustrated**: not balanced in any sign gauge.
- **Pinned**: a coordinate of the cone confined to an interval around $\Lambda(n)$ whose width decays in $c$.
- **Blind**: a positive combination of autocorrelations vanishing at every $\log n$, $n\ge2$.
- **Near-null at level $c$**: a window test on which every point of $\mathcal A(c)$ has small energy.
- **Reading**: the pairing of $\lambda-\Lambda$ with $\Phi_L\star Y$ for a second test $Y$.
- **Divisor sum**: $D(N)=\sum_{d\mid N}\delta(d)$, $\delta=\lambda-\Lambda$; readings see $\delta$ only through it.
- **Datum**: the pair (pole weight, log-conductor); the datum of $\zeta$ is $(1,0)$.
- **Edge law**: the boundary asymptotics $u(-a+t)\sqrt{\log(1/t)}\to\int Kf$ of a window solution.
- **Singular part**: the gap $G(b)-G(a)-\int_a^bG'$ of the evaluation Gram; zero on every interval iff the chain is
  regular there.

## 4. Foundations

The theorems on which the field rests, each unconditional.

| Foundation | Statement | Lean |
|---|---|---|
| Cone uniqueness | $\bigcap_c\mathcal A(c)=\{\Lambda\}$ under RH, empty otherwise; only $\Gamma$, the pole and the positions $\log n$ enter | `RHTower` cone theory |
| Aperture blindness | every bounded aperture is consistent with every zero width | `SquareRootThreshold` |
| Limit law | RH $\iff\lambda^*(c)\to0$; not RH $\iff$ the cones are eventually empty | `riemannHypothesis_iff_tendsto_bestMargin`, `exists_windowCone_eq_empty_iff` |
| Hardy criticality | the multiple $1$ is the only one admissible on every window; no Hardy weight survives on odd tests; optimal Hardy term $\iff$ RH | `FrustratedArithmeticDirichletForms` |
| Onset dictionary | window positivity at half-width $a$ $\iff$ $a\le a^*(\zeta)$; `windowThreshold A = ⊤` $\iff A/2\le a^*(\zeta)$ | `WindowVisibilityLaw`, `ArithmeticHodgeTheoryOfDegenerations` |
| Floors | an infinite strictly increasing tower of apertures carries floors $(1/20000)/2^k$, on windows and reflection pairs | `ArithmeticIncidencePositivity`, `SignedWindowCriticality` |

## 5. Mechanisms

1. **Null families are universal test vectors.** The twisted-arc family is blind and $\Xi$-divisible. Truncated to a
   window it is near null for every weight in the cone, which closes the slack from other weights. Cauchy on
   $|t|=7/10$ of the generating function $(1-t)^{-1/4}\Phi(x+\frac12\log(1-t))$ gives one doubly exponential bound for
   all $F_j$.
2. **Polarization removes positivity from the dual.** Cauchy–Schwarz on the positive form reads $\lambda-\Lambda$
   against $\Phi_L\star Y$ for any $Y$. Only the first slot has to come from a positive blind family; the second slot
   carries no sign constraint.
3. **Gaussian tests read Hamburger's kernels.** The reading of $\Phi\star Y_t$ at $\log n$ is
   $\sum_k(\mathrm{ratKer}(kn,t)+\mathrm{expKer}(kn,t))$. The exponential kernel of an integer is $i$-periodic up to a
   factor linear in $t$, so the second difference at step $i$ kills it exactly. What is left has poles at $t=iL$.
4. **Three lines from a ray to the poles.** $T$ is entire, small on the real ray and bounded elsewhere. The three lines
   theorem on sectors carries the smallness to $t\pm i$, then across the imaginary axis to $iL$, where $T$ is the
   discrete Laplacian of $N\mapsto ND(N)$.
5. **Splitting the causal kernel.** The Green operator does not map $L^2$ to $L^\infty$, but the causal kernel is
   integrable and antitone: the part near $0$ has small mass and is absorbed in $L^1$ after truncating at a high level,
   and the rest is bounded. Window solutions are therefore bounded, and the half-line boundary readout applies.
6. **Orthogonal increments give a density.** Growing the window adds an orthogonal kernel increment to every Riesz
   combination, so the evaluation Gram is monotone in the aperture; its derivative exists almost everywhere and
   integrates to at most the increment. The defect is a singular measure, supported where a kernel blows up.
7. **The datum enters through the residue.** The pole weight is read from below on every nonempty datum cone, and a
   log-conductor below the critical one empties the cone: the window reads the residue and the conductor, and the
   datum $(1,0)$ of $\zeta$ is the critical point of the family.

## 6. Traps

| Trap | Truth |
|---|---|
| A finite-level theorem about $\mathcal A(c)$ moves the sign for $\zeta$ | Bounded apertures are blind to every width |
| Uniform control in $c$ is a tool | Every uniform statement is RH or the width |
| Other weights give slack | All weights share one ceiling: null families are blind; every coordinate is pinned |
| Other data give slack | Below the critical log-conductor the cones are empty; above it, at high conductor without a pole, the cone is fat and the problem is a different one |
| Single-atom readings need a positive arc measure with one moment | Polarization needs no positivity in the second slot |
| Theta smoothing cannot be undone | Hamburger's kernels undo it at the cost of a Hölder exponent |
| The resolvent bootstraps $L^2$ to $L^\infty$ | It never does; the bound comes from absorbing the small part of the kernel |
| The Weil cone at conductor one is typical | No-pole data at high conductor have a fat cone: pole and conductor one make it a point |
| A certificate format is a mechanism | Every positive form has an exact format |
| Constructing the Hamiltonian decides RH | The absolutely continuous part exists; its singular part is the contact, and "no singular part" is RH |
| A sign gauge can balance the cone | Past $\tfrac12\log2$ (odd) and $\log\rho$ (even) every point of the cone is frustrated in every gauge |

## 7. Questions and answers

| Question | Answer | Lean |
|---|---|---|
| Effective uniqueness | $\lvert\lambda(n)-\Lambda(n)\rvert\le C\exp(Kn-c/1104)$ for $c\ge2$, $\lambda\in\mathcal A(c)$, $2\le n\le e^{2c-1/6}$, with absolute $C,K$; every $n$ with $Kn\le c/2208$ pinned to $Ce^{-c/2208}$ | `exists_abs_sub_vonMangoldt_le_exp`, `exists_abs_sub_vonMangoldt_le_of_le_aperture` |
| Margin law | $\lambda^*(c)\le K\exp(\tfrac{11}{2}c-\pi e^{2(c-2)})$ for $c\ge3$, over all weights; the sharper form is $K\exp(3c-\tfrac\pi6e^{2(c-13/12)})$; $\lambda^*(a_k)\ge(1/20000)/2^k$ at the tower apertures | `exists_bestMargin_le_gaussian`, `exists_bestMargin_le`, `weilFloorTowerConst_le_bestMargin` |
| Band widths | Bands are intervals of width at least $\lambda^*(c)\sqrt n$ and at most $C\exp(Kn-c/1104)$; a perturbation of weights costs $\sum_n2\lvert v(n)\rvert/\sqrt n$ of margin | `ordConnected_bandSet`, `exists_band_width_ge`, `exists_abs_sub_le_of_mem_bandSet`, `hasMargin_add` |
| Signs on the cone | a prime-power weight is positive from a finite window on; the whole cone is frustrated past $\tfrac12\log2$ (odd) and past $\log\rho$ (even) | `exists_forall_ge_weight_pos`, `exists_odd_frustrated_on_cone`, `even_frustrated_on_cone` |
| Edge profile | Energy solutions of the window equation are bounded, and $u(-a+t)\sqrt{\log(1/t)}\to\int Kf_L$ at each end, constant one, for every aperture | `exists_ae_norm_le_of_window_equation`, `window_edge_law` |
| Datum | Conductor below one empties the cone; conductor one is RH; without a pole the threshold is exact, and the cone is fat above it; $\beta\ge1-K'\,\mathrm{ceiling}(c)$ on every nonempty datum cone | `exists_datumCone_one_eq_empty`, `riemannHypothesis_iff_forall_datumCone_one_zero_nonempty`, `forall_zero_mem_datumCone_zero_iff`, `exists_ne_mem_forall_datumCone_zero`, `exists_one_sub_le_of_datumCone`, `exists_pos_forall_lt_datumCone_zero_eq_empty` |
| Hamiltonian | In the frame of finitely many evaluation points the density $G'$ exists, with $0\le\int_a^bG'\le G(b)-G(a)$; RH or some diagonal kernel diverges at contact, the first singular length. The ordering theorem itself is not formalized | `integral_evalDensity_mem`, `riemannHypothesis_or_evalGram_tends_to_top` |
| Numerical membership of $\Lambda$ at a window | Out of scope here: a computation |

## 8. Tools

| Tool | Lean |
|---|---|
| Doubly exponential bound for all shifted-Gamma tests, from Taylor coefficients of complex translates of $\Phi$ | `abs_xiShiftedGammaTest_le` |
| Truncation calculus and near-nullity of the blind family, uniform on the cone | `exists_nullWeights_tsum_nullEnergy_le` |
| Pinning with explicit dependence on the second test | `exists_uniform_pinning` |
| Atom reading of a Gaussian test | `hasSum_atomReading` |
| Three lines theorem on a sector | `norm_le_of_sector` |
| Quantitative Hamburger uniqueness, from a small reading on a ray to each atom | `exists_abs_le_of_readS_small` |
| Causal averages and absorption in $L^1$ | `exists_ae_le_of_absorption` |
| Datum calculus, residue read from below | `exists_datum_constants`, `exists_one_sub_le_of_datumCone` |
| Evaluation Gram as a kernel form; orthogonal increments | `evalGram_eq_kernel`, `norm_evalCombination_sq` |

## 9. Pillar theorems

Cone theory.

| Theorem | Statement | Lean |
|---|---|---|
| Near-nullity | every $\lambda\in\mathcal A(c)$ has family energy at most $K\exp(3c-\tfrac\pi6e^{2(c-13/12)})$ | `exists_nullWeights_tsum_nullEnergy_le` |
| Gaussian ceiling | $\lambda^*(c)\le K\exp(\tfrac{11}{2}c-\pi e^{2(c-2)})$ | `exists_bestMargin_le_gaussian` |
| RH as a limit | RH $\iff\lambda^*(c)\to0$ | `riemannHypothesis_iff_tendsto_bestMargin` |
| Floors | the floor tower bounds $\lambda^*$ from below | `weilFloorTowerConst_le_bestMargin` |
| Collapse | every far cone lies within $\varepsilon$ of $\Lambda$ at each $n$; not RH $\iff$ the cones are eventually empty | `exists_forall_abs_sub_vonMangoldt_lt`, `exists_windowCone_eq_empty_iff` |
| Effective uniqueness | the bound of §7 | `exists_abs_sub_vonMangoldt_le_exp` |
| Range | all $n$ with $Kn\le c/2208$ are pinned to $Ce^{-c/2208}$ | `exists_abs_sub_vonMangoldt_le_of_le_aperture` |
| Bands | intervals, width between $\lambda^*(c)\sqrt n$ and $Ce^{Kn-c/1104}$; hence $\lambda^*(c)\sqrt n\le Ce^{Kn-c/1104}$ | `ordConnected_bandSet`, `exists_band_width_ge`, `exists_bestMargin_mul_sqrt_le` |
| Signs on the cone | positivity of prime-power weights from a finite window; frustration of the whole cone | `exists_forall_ge_weight_pos`, `exists_odd_frustrated_on_cone`, `even_frustrated_on_cone` |
| Residue | $\beta\ge1-K'\,\mathrm{ceiling}(c)$ on every nonempty datum cone; no pole needs positive conductor | `exists_one_sub_le_of_datumCone`, `exists_pos_forall_lt_datumCone_zero_eq_empty` |

Edge theory.

| Theorem | Statement | Lean |
|---|---|---|
| Regularity and edge | window solutions are bounded, with the exact edge law | `exists_ae_norm_le_of_window_equation`, `window_edge_law` |
| Wiener–Hopf factor, causal kernel, Green operator, interval detection | the archimedean symbol factors through a logarithmic Poisson factor with positive causal kernel; the half-line Green operator is explicit; energy per unit mass on width $h$ is $\ge\log(1/h)$ and $\le\log(1/h)+3$ is attained | `CanonicalSystemOfTheWindowTower` |
| No point traces | height-one spikes have arbitrarily small energy; Weil's form reads no point values | `FrustratedArithmeticDirichletForms` |

Transport and canonical-system theory.

| Theorem | Statement | Lean |
|---|---|---|
| Hamiltonian density | $0\le\int_a^bG'\le G(b)-G(a)$; RH or a diagonal kernel diverges at contact | `integral_evalDensity_mem`, `riemannHypothesis_or_evalGram_tends_to_top` |
| Chain before contact | complete Weil spaces, Hermite–Biehler function, unitary zero-moving, isometric inclusions, orthogonal increments, bounded exterior crossings, continuous prime and polar responses, kernel blow-up at contact | `CanonicalSystemOfTheWindowTower` |
| Stage transport | composite stages carry no fold; single-prime transport for every aperture $\iff$ RH; head windows under Dirichlet shifts, unconditional for $d=2$ | `ArithmeticHodgeTheoryOfDegenerations`, `WindowTowerOfSpecZ` |
| Exact formats for $\Lambda$ | neutral signed theta gauge and shifted ground state on every window; gauge freedom only in the pole direction; the $\{2,3,4\}$ sliver band below $\log5$ | `SignedWindowCriticality` |

## 10. Open research topics

1. **Decay law of the margin.** The pinning rate $e^{-c/1104}$ comes from the exponential tail of $Y_t$ and two uses of
   three lines, and gives $\lambda^*(c)\sqrt n\le Ce^{Kn-c/1104}$; the ceiling is doubly exponential. The true rate of
   $\lambda^*(c)$, and whether $t$-derivatives of $Y_t$ or a moment-null superposition reach the ceiling, are open.
2. **Explicit $C,K$ and uniformity in $n$.** Both constants are absolute but not numerically evaluated, and the range
   of pinned $n$ is linear in $c$, against the box $n\le e^{2c-1/6}$.
3. **The singular part.** Off RH the evaluation-Gram density has a singular part at contact. Its support, its mass and
   its relation to the contact zero are not described; the ordering theorem producing the Hamiltonian from the chain is
   not formalized. Regularity on every interval is RH.
4. **Bridge to the completed form.** The edge law is stated for the logarithmic window equation with dominated
   forcing. Identifying the extremals of $W_\lambda$ for general $\lambda$ with its solutions, in the energy completion,
   is not formalized. For $\Lambda$ before contact this is done for Riesz vectors.
5. **Nonvanishing of edge coefficients.** Whether extremals have nonzero edge coefficient.
6. **Cone language for the exact formats.** Paying the pole square and the cosh deficit with retained variance for free
   weights; proved for $\Lambda$ in the signed-window programme, open on the cone.
7. **Transport on the cone.** Stage forms, fold energies and head windows for free weights: which cone points survive a
   prime step, and what the step costs in margin.
8. **Data beyond $\zeta$.** The cones of other data $(\beta,s)$ are classified only through emptiness and the residue
   bound; their margins, bands and edges are not.

## 11. Context

| Neighbour | Interface |
|---|---|
| `RHTower` cone theory | $\mathcal A(c)$, cone uniqueness, twisted-arc family, level duality |
| `HTGeometry` Hamburger modules | the Laplace transform behind the atom reading, in its qualitative form |
| `FrustratedArithmeticDirichletForms` | Hardy interval, entry laws, frustration in sign gauges, trace theory, trivial zeros at the centre |
| `SignedWindowCriticality` | exact two-sector format, pole square, retained variance, cosh deficit, sliver band, singularity of eigenfunctions at the edge |
| `ArithmeticCriticalityTheory` | ground states, the Gaussian ceiling for $\Lambda$ |
| `CanonicalSystemOfTheWindowTower` | causal kernel, half-line Green solutions, Riesz vectors before contact, reproducing-kernel chain, exterior crossings, endpoint traces |
| `ArithmeticHodgeTheoryOfDegenerations`, `WindowTowerOfSpecZ`, `GrowingWindowsOfSpecZ` | window threshold, stage transport, head windows, lattices, Levinson recursion |
| `ArithmeticIncidencePositivity` | the floor tower of apertures |
| `WindowVisibilityLaw`, `SquareRootThreshold`, `ZeroConfigurationGeometry` | what positivity at an aperture says about the zeros: onset dictionary, exponential and cubic-logarithmic depth corridors |
| `ArithmeticProduction`, `ArithmeticOfSquareRootPrecision` | the producer side and the limit theorems bounding what CHT can deliver |

## 12. Criteria

The field meets its questions when the margin has its law, the singular part is described, the edge profile is known
on a window, the datum is classified, and the tools of §8 exist in Lean. Against its founding criteria:

1. **Thresholds.** $\tfrac12\log2$ and $\log\rho$ on the whole cone, the floors, the pinning rate, the margin ceiling
   and the bands are theorems here. The numerical table of margins is not reproduced: this programme does no computation.
2. **Pole and centre.** The pole is read from below (`exists_one_sub_le_of_datumCone`). The pole square, cosh deficit and
   trivial zeros at the centre are proved for $\Lambda$ in the signed-window programme and are open in cone language.
3. **Datum.** Pole and conductor one are distinguished from no-pole data at high conductor, whose cone contains $0$ and
   is not a point; the datum of $\zeta$ is the critical point of the family.
4. **Limits.** Every theorem states what it does not say about $\zeta$ and where it would become RH.

## 13. What counts as a contribution

A contribution must be an unconditional theorem about $\mathcal A(c)$, its data, its edge or its canonical system that:

1. reproduces a known threshold in cone language, or strictly refines it;
2. treats the weights as free, with $\Lambda$ as an output and not an input;
3. states its limit: what it does not say about $\zeta$, and where it would become RH;
4. distinguishes pole and conductor one from no-pole data at high conductor whenever it claims rigidity;
5. for a canonical-system statement, separates the absolutely continuous part from the singular part, and names which
   one it controls.
