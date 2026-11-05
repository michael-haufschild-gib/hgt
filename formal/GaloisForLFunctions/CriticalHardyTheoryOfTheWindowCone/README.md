# Critical Hardy Theory of the Window Cone (CHT)

Namespace `GaloisForLFunctions.CriticalHardyTheoryOfTheWindowCone`; umbrella
`CriticalHardyTheoryOfTheWindowCone.lean`. Every theorem here is unconditional; equivalences with RH are labelled.

## 1. Motivation

Weil's form on a window is a signed nonlocal quadratic form

$$W_\lambda(f)=H(f)-P_\lambda(f),\qquad P_\lambda(f)=\sum_{n\ge2}\lambda(n)n^{-1/2}\bigl(k_f(\log n)+k_f(-\log n)\bigr),$$

where $k_f=f\star\tilde f$ and $H$ is the archimedean–polar form: a logarithmic-order jump form with symbol
$1+\tfrac12\log(1+\xi^2)$ up to a bounded convolution, with the pole kept. The weights $\lambda(n)$ are free real
numbers. CHT studies the nested convex sets

$$\mathcal A(c)=\{\lambda : W_\lambda\ge0\text{ on }[-c,c]\}$$

as objects in their own right. Their intersection is $\{\Lambda\}$ under RH and empty otherwise, while only $\Gamma$,
the pole and the positions $\log n$ enter the definition. Criticality, frustration and logarithmic boundary behaviour
meet on this one object; Hardy theory, Dirichlet form theory and Wiener–Hopf theory each cover only part of it.

CHT is a receiver. Positivity at a finite aperture is consistent with every width, and every uniform statement in $c$
is RH or the width. So CHT does not aim at a sign for $\zeta$. It gives the exact finite-level theorem: what any proof
must deliver on each window, at what precision, and with what boundary behaviour.

## 2. Objects

| Object | Meaning |
|---|---|
| Window cone $\mathcal A(c)$ | weights with $W_\lambda\ge0$ on tests supported in $[-c,c]$ (`windowCone`) |
| Band | the set of values of one weight $\lambda(n)$ over $\mathcal A(c)$ (`bandSet`) |
| Margin, best margin $\lambda^*(c)$ | `HasMargin`, `bestMargin`: the largest margin over all weights, the inradius of the cone |
| Blind family | positive combination of autocorrelations vanishing at every $\log n$, $n\ge2$ |
| Null family | the twisted-arc tests $F_j$, $\hat F_j=\Xi Q_j$, near null on every point of the cone |
| Gaussian test | $Y_t(v)=2e^{-3v/2}\exp(-\pi t^2e^{-2v})$ (`gaussTest`), the second slot of the atom reading |
| Hamburger series | $S(t)=\sum_{n,k}\delta(n)\,\mathrm{ker}(kn,t)$ (`readS`), and the entire function $T=\sinh^3(\pi t)\,\Delta_i^2S$ (`poleT`) |
| Datum | pole weight $\beta$ and log-conductor $s$ (`datumCone`) |
| Window equation | $E(f,u)=\langle f,g\rangle$ for finite-energy $f$ on the window, with $g$ dominated by constants and translates of $u$ |
| Edge coefficient | the limit of $u(-a+t)\sqrt{\log(1/t)}$ |
| Evaluation density | $G'$, for $G(a)=\lVert\sum_i\alpha_iE_a(z_i)\rVert^2$ (`evalDensity`) |

## 3. Language

- **Critical**: no Hardy weight survives; the slack of the limit form is zero in every sense.
- **Frustrated**: not balanced in any sign gauge.
- **Blind**: a positive combination of autocorrelations vanishing at every $\log n$, $n\ge2$.
- **Near-null at level $c$**: a window test on which every point of $\mathcal A(c)$ has small energy.
- **Reading**: the pairing of $\lambda-\Lambda$ with $\Phi_L\star Y$ for a second test $Y$.
- **Divisor sum**: $D(N)=\sum_{d\mid N}\delta(d)$, $\delta=\lambda-\Lambda$; readings see $\delta$ only through it.

## 4. Mechanisms

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

## 5. Traps

| Trap | Truth |
|---|---|
| A finite-level theorem about $\mathcal A(c)$ moves the sign for $\zeta$ | Bounded apertures are blind to every width |
| Uniform control in $c$ is a tool | Every uniform statement is RH or the width |
| Other weights give slack | All weights share one ceiling: null families are blind |
| Single-atom readings need a positive arc measure with one moment | Polarization needs no positivity in the second slot |
| Theta smoothing cannot be undone | Hamburger's kernels undo it at the cost of a Hölder exponent |
| The resolvent bootstraps $L^2$ to $L^\infty$ | It never does; the bound comes from absorbing the small part of the kernel |
| The Weil cone at conductor one is typical | No-pole data at high conductor have a fat cone: pole and conductor one make it a point |
| A certificate format is a mechanism | Every positive form has an exact format |

## 6. Questions and answers

| Question | Answer | Lean |
|---|---|---|
| Effective uniqueness (B58) | $\lvert\lambda(n)-\Lambda(n)\rvert\le C\exp(Kn-c/1104)$ for $c\ge2$, $\lambda\in\mathcal A(c)$, $2\le n\le e^{2c-1/6}$, with absolute $C,K$ | `exists_abs_sub_vonMangoldt_le_exp` |
| Margin law (B59) | Yes: $\lambda^*(c)\le K\exp(\tfrac{11}{2}c-\pi e^{2(c-2)})$ for $c\ge3$, over all weights; the sharper form is $K\exp(3c-\tfrac\pi6e^{2(c-13/12)})$ | `exists_bestMargin_le_gaussian`, `exists_bestMargin_le` |
| Band widths (B59, A13) | Bands are intervals of width at least $\lambda^*(c)\sqrt n$ and at most $C\exp(Kn-c/1104)$ | `ordConnected_bandSet`, `exists_band_width_ge`, `exists_abs_sub_le_of_mem_bandSet` |
| Edge profile | Energy solutions of the window equation are bounded, and $u(-a+t)\sqrt{\log(1/t)}\to\int Kf_L$ at each end, constant one, for every aperture | `exists_ae_norm_le_of_window_equation`, `window_edge_law` |
| Datum | Conductor below one empties the cone; conductor one is RH; without a pole the threshold is exact, and the cone is fat above it | `exists_datumCone_one_eq_empty`, `riemannHypothesis_iff_forall_datumCone_one_zero_nonempty`, `forall_zero_mem_datumCone_zero_iff`, `exists_ne_mem_forall_datumCone_zero` |
| Hamiltonian (A41) | Partial: in the frame of finitely many evaluation points the density $G'$ exists, with $0\le\int_a^bG'\le G(b)-G(a)$; contact is a singular length unless RH holds. The ordering theorem itself is not formalized | `integral_evalDensity_mem`, `riemannHypothesis_or_evalGram_tends_to_top` |
| Numerical membership (A5) | Out of scope here: it is a computation | — |

## 7. Tools

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

## 8. Pillar theorems

| Theorem | Statement | Lean |
|---|---|---|
| Near-nullity | every $\lambda\in\mathcal A(c)$ has family energy at most $K\exp(3c-\tfrac\pi6e^{2(c-13/12)})$ | `exists_nullWeights_tsum_nullEnergy_le` |
| Gaussian ceiling | $\lambda^*(c)\le K\exp(\tfrac{11}{2}c-\pi e^{2(c-2)})$ | `exists_bestMargin_le_gaussian` |
| RH as a limit | RH $\iff\lambda^*(c)\to0$ | `riemannHypothesis_iff_tendsto_bestMargin` |
| Floors | the floor tower bounds $\lambda^*$ from below | `weilFloorTowerConst_le_bestMargin` |
| Collapse | every far cone lies within $\varepsilon$ of $\Lambda$ at each $n$; not RH $\iff$ the cones are eventually empty | `exists_forall_abs_sub_vonMangoldt_lt`, `exists_windowCone_eq_empty_iff` |
| Effective uniqueness | the bound of §6 | `exists_abs_sub_vonMangoldt_le_exp` |
| Range | all $n$ with $Kn\le c/2208$ are pinned to $C e^{-c/2208}$ | `exists_abs_sub_vonMangoldt_le_of_le_aperture` |
| Signs on the cone | a prime-power weight is positive from a finite window on; the whole cone is frustrated past $\tfrac12\log2$ and past $\log\rho$ | `exists_forall_ge_weight_pos`, `exists_odd_frustrated_on_cone`, `even_frustrated_on_cone` |
| Residue | $\beta\ge1-K'\,\mathrm{ceiling}(c)$ on every nonempty datum cone; no pole needs positive conductor | `exists_one_sub_le_of_datumCone`, `exists_pos_forall_lt_datumCone_zero_eq_empty` |
| Regularity and edge | window solutions are bounded, with the exact edge law | `exists_ae_norm_le_of_window_equation`, `window_edge_law` |

## 9. Open research topics

1. **Sharp rate.** The rate $e^{-c/1104}$ comes from the exponential tail of $Y_t$ and two uses of three lines. The
   ceiling suggests a doubly exponential rate. $t$-derivatives of $Y_t$ should give every exponential rate, and a
   moment-null superposition doubly exponential decay; neither is proved.
2. **Explicit $C,K$ and uniformity in $n$.** Both constants are absolute but not numerically evaluated, and the range
   of pinned $n$ is linear in $c$, against the box $n\le e^{2c-1/6}$.
3. **Lower bounds for the margin.** The true decay of $\lambda^*(c)$ below the ceiling, given RH.
4. **Bridge to the completed form.** The edge law is stated for the logarithmic window equation with dominated
   forcing. Identifying the extremals of $W_\lambda$ for general $\lambda$ with its solutions, in the energy completion,
   is not formalized. For $\Lambda$ before contact, CSTW does this for Riesz vectors.
5. **Nonvanishing of edge coefficients.** Whether extremals have nonzero edge coefficient.
6. **The ordering theorem.** The Hamiltonian $H$ of the chain. Its regularity is B51, of RH strength.
7. **Cone language for the exact formats.** Paying the pole square and the cosh deficit with retained variance for free
   weights; these are proved in SWC for $\Lambda$.

## 10. Context

CHT sits on the receiver side of the programme. Its partner, arithmetic production at square-root precision, works on
$\Lambda$ itself and may supply an input; CHT states the exact target such an input must meet.

| Neighbour | Interface |
|---|---|
| `RHTower` cone theory | $\mathcal A(c)$, cone uniqueness, twisted-arc family, level duality |
| `HTGeometry` Hamburger modules | the Laplace transform behind the atom reading, in its qualitative form |
| `FrustratedArithmeticDirichletForms` | Hardy interval, entry laws, frustration in sign gauges |
| `SignedWindowCriticality` | exact two-sector format, pole square, retained variance, cosh deficit, singularity of eigenfunctions at the edge |
| `ArithmeticCriticalityTheory` | ground states, the Gaussian ceiling for $\Lambda$ |
| `CanonicalSystemOfTheWindowTower` | causal kernel, half-line Green solutions, Riesz vectors before contact, reproducing-kernel chain |
| `ArithmeticProduction`, `ArithmeticOfSquareRootPrecision` | the input side and the limit theorems bounding what CHT can deliver |

## 11. Success criteria

The programme meets its questions when effective uniqueness and the margin law have explicit forms, the edge profile
is known on a window, the datum is classified, and the tools of §7 exist in Lean. Against the criteria of its founding
question list:

1. **Thresholds.** $\tfrac12\log2$ and $\log\rho$ on the whole cone, the floors, margins and bands are theorems here.
   The numerical table of margins is not reproduced: this programme does no computation.
2. **Pole and centre.** The pole is read from below (`exists_one_sub_le_of_datumCone`). The pole square, cosh deficit and
   trivial zeros at the centre are proved in SWC for $\Lambda$, and are open in cone language (§9).
3. **Datum.** Pole and conductor one are distinguished from no-pole data at high conductor, whose cone contains $0$ and
   is not a point.

## 12. What counts as a contribution

A contribution must be an unconditional theorem about $\mathcal A(c)$, its data, or its edge that:

1. reproduces a known threshold in cone language, or strictly refines it;
2. treats the weights as free, with $\Lambda$ as an output and not an input;
3. states its limit: what it does not say about $\zeta$, and where it would become RH;
4. distinguishes pole and conductor one from no-pole data at high conductor whenever it claims rigidity.
