# Square-Root Threshold (SRT)

**Question.** Which tests, at which aperture, lag and height, make an off-line zero visible to Weil
positivity — and which unconditional mechanism reaches that information?

Primary namespace `GaloisForLFunctions.SquareRootThreshold`; cluster-product bounds use
`SquareRootThreshold`; `SmoothWeilDetectorPolynomialAperture` and most of `EffectiveHorizons/` use `RHTower`.
Umbrella `SquareRootThreshold.lean`. 170 files. Base objects come from `Zeta23`
and `RHTower` (`ZeroConfig`, `paperFT`, `gammaOf`, `zetaZeroConfig`, explicit formula); do not redefine.

---

## 1. Motivation

- On-line zeros contribute $|h_f(\gamma)|^2\ge0$ to $W(f,f)$; a reflected off-line pair contributes an
  indefinite rank-two term. Visibility = existence of a test exposing it.
- A test on $[-a,a]$ reads lags $|v|\le2a$, primes $n\le X=e^{2a}$, ordinates to resolution $\pi/a$.
- **Threshold.** The off-line lattice $\{\tfrac12\pm\delta+2\pi ik/L\}$ hides from every test of aperture
  $\le L/2$, at every depth, and from none larger (`RHTower.offLineLattice_weil_positive_iff`).
  Ordinate spacing matched to $\zeta$ ($L\approx\log T$): threshold $X\asymp T$. Total zero density
  matched ($L=\log T/2$): threshold $X^2=T$ (`DensityMatchedLengthHeightBoundary`). Same scale as the
  diagonal threshold $2rX\le1$ of windowed Dirichlet-polynomial mean values.
- SRT classifies what hides below the threshold, what is seen early, what $\zeta$-specific structure
  positivity forces, and supplies the **common units** (zero width, aperture, lag rate, contact
  aperture, excluded depth) in which every positivity route reports progress.

---

## 2. Objects

| Object | Lean |
|---|---|
| Zero configuration, Weil form, tempered | `ZeroConfig`, `ZeroConfig.W`, `TemperedConfig` |
| Lattices, periodic profiles, patterns, runs, clusters, jitter, dilution | `onLineLatticeConfig`, `offLineLatticeConfig`, `simpleHalfLatticeConfig`, `profileConfig`, `patternConfig`, `runConfig`, `clusterConfig`, `jitterConfig`, `dilutedLatticeConfig`, `isolatedPairConfig` |
| Lag symbol $D(m)$, Toeplitz form, on-line shadow | `depthSymbol`, `patternSymbol`, `toeplitzForm`, `onLineShadow`, `shadowMoment` |
| Windowed form, height shift $S_\xi f=e^{2\pi i\xi u}f$, window slice | `windowedW`, `heightShift`, `windowSlice` |
| Lag structure $S(v)=\sum m_\rho\hat h_{k_\beta}(\gamma_\rho)e^{i\gamma_\rho v}$; coefficients $F(z),D(z)$ at $\rho=\tfrac12+z$ | `lagStructure`, `lagCoeff`, `evenCoeff` |
| Two-bump test $\beta(t+v/2)+\tau\beta(t-v/2)$; minor deficit | `twoBump`, `minorDeficit` |
| Bumps: scaled, modulated, polar-free $\kappa''-\kappa/4$, box spline $U_{w/4}^{\star4}$ | `scaledBump`, `modScaledBump`, `scaledBumpPolarFree`, `splineBump`, `splinePolarFree` |
| Lag family $f_v=\kappa_w(t+v/2)-\kappa_w(t-v/2)$; window functional $P_{w,v}$ ($\Lambda(n)$ on $|\log n-v|\le2w$) | `lagPrimeWindow`, `lagPrimePowWindow`, `lagPrimeWindowRHS` |
| Prime polynomial $\Pi_f(\xi)$, archimedean–pole part $A_f(\xi)$, prime variance $V_f$, parity/smooth/rough splits | `primePolynomial`, `archPart`, `primeVariance`, `odd/evenPrimePolynomial`, `smooth/roughPrimePolynomial` |
| Laplace / Fejér / Fejér-power / grid windows | `lapWin`, `fejerWin`, `fejerPowWin`, `geomWin` |
| Depth transforms, level weight | `depthDeficit`, `depthExcess`, `levelWeight`, `offLineMoment` |
| Explicit lags, horizons, excluded depths | `recordLag`, `oneParamLag`, `nearTopLag`, `zoneLag`, `boxHorizon`, `clusterHorizonHeight`, `zetaClusterHorizonHeight`, `nearTopExcludedDepth`, `oneParamExcludedDepth` |
| Window prime polynomial, off-line correction, $S(T)$ | `windowPrime`, `offLineCorrection`, `rvmRemainder` |
| Zero width $\sup|\Re\rho-\tfrac12|$; config width; critical depth | `zetaZeroWidth`, `configWidth`, `criticalDepth` |
| Window positivity at aperture $A$ (all / even / odd) | `ZetaWindowPositive`, `ZetaEvenWindowPositive`, `ZetaOddWindowPositive` |
| Contact aperture | `zetaContactAperture` |
| Ground energies $\mu(A)$, $\mu_0(A)$ (imported, ACT/RHTower) | `ccmRestrictedWeilGroundEnergy`, `ccmRestrictedWeilPolarGroundEnergy`, `polarGroundEnergyRate` |
| Non-clustering hypotheses | `OffLineCopiesLocallyBounded`, `OffLineDepthLocallyBounded`, `UnsignedDepthSamplingBound` |
| Function-field curve datum | `curveConfig`, `goldenDatum` |

---

## 3. Language

- **Visible at $a$**: some $C^2$ test on $[-a,a]$ has $\Re W<0$. **Hides**: not visible.
- **Shadow / mimicry**: weighted on-line periodic configuration with the same Weil form at that aperture.
- **Nyquist aperture** $P\ell/2$ for $P$ ordinates per period $2\pi/\ell$.
- **Depth** $|\Re\rho-\tfrac12|$; **width** = sup of depths; **level** = set of zeros of one real part;
  **top** = largest real part, *attained* or not; **near-top zero** = within $1/V$ (or $\mu/V$) of the top.
- **Legendre record** at lag $V$: maximiser of $|D(z)|e^{\Re z\cdot V}$; exists at every lag (summability).
  **Loud** = large $|D(z)|$; **twin** = companion zero near the record; **collapsed cluster** = $\le P$
  zeros at exponentially small geometric-mean radius.
- **Horizon** $V_0(z)$ = explicit lag at which zero $z$ is seen. **Contact aperture** = first $A$
  where $\mu(A)<0$. **Excluded depth** = inverse of an explicit lag.
- **Minor**: $|S(v)+\overline{S(-v)}|\le2\Re S(0)$ (2×2 Toeplitz minor of the lag structure).
- **TRAP**: an RH ⇔ statement (criterion), not progress.

---

## 4. Mechanisms

### A. Lattice and periodic configurations (finite Toeplitz algebra)
1. **Poisson.** Below Nyquist only the lag-zero atom of a lattice survives: doubled on-line lattice
   gives $2L\|f\|^2$; off-line lattice gives the same at every depth.
2. **Lag formula ⇒ Toeplitz law.** $W=\ell\sum_mk(m\ell)D(m)$ ⇒ hiding at $a$ ⇔ size-$\lceil2a/\ell\rceil$
   Toeplitz section of $D$ PSD (`weil_nonneg_iff_toeplitz_of_lagFormula`). Profile symbol
   $D(m)=\sum_r2\cosh(d_rmL/P)e^{2\pi irm/P}$.
3. **Hiding is mimicry.** PSD section ⇔ Carathéodory–Fejér atomic factorisation ⇔ an on-line
   configuration of the same density has the same form (`weil_nonneg_iff_onLineShadow_of_lagFormula`).
4. **Depth variation, not depth.** Constant depth has no mode below $P$ ⇒ hides to $L/2$. Below
   threshold tests read depth *jumps*: run edges seen at $a=O(1/\delta)$ independent of length and
   density; clusters invisible iff $a\cdot TV(d)\sinh(2\delta a)\le1$ (only total variation and max depth
   matter); smooth profiles hide to $\approx(1/2\delta)\log(\Lambda/\delta)$; band-limited cosine profiles
   hide to $L/4$; diluted lattices to $\approx(1/2\delta)\log(L/\ell)$.
5. **Crystal rigidity.** Newton identities: hiding near Nyquist at unboundedly many scales ⇒ uniform
   depth and offsets in one coset of $\tfrac1P\mathbb Z$. Jitter $\varepsilon$ seen once
   $\cosh(\delta L/2)|\sin(\varepsilon L/2)|>1$: relative precision $e^{-\delta L/2}=T^{-\delta/2}$ needed.
   Variational form: floor $2P\ell$ on $((P-1)\ell/2,P\ell/2]$ ⇔ crystal.
6. **Ground state** = $\ell\cdot\lambda_{\min}$(Toeplitz). Off-line lattice floor $n-U_{n-1}(\cosh\delta L)$;
   drops at every $nL/2$ (step law); $\zeta$'s $\mu(A)$ is continuous. Relaxed Hodge exponent of every
   periodic configuration $=2\cdot$max depth.
7. **Polar blindness.** On lag lattices the Hodge index (pole-killed tests) equals full positivity; it is
   blind exactly to $s=0,1$.
8. **Pinning and tomography.** $r$ ordinates/period are determined by the form beyond $r\ell/2$; depths +
   ordinates read at twice Nyquist. Sampling law: on-line shadow has an $L^2$ floor ⇔ aperture $\le$ Nyquist.
9. **Non-monotone.** Adding off-line zeros can complete a crystal and *hide* a visible set
   (`exists_offLine_superset_hiding`).

### B. Tempered configurations (two-bump minors, Laplace, Landau, Cesàro)
10. **Two-bump minor**: $W(\text{twoBump})=(1+|\tau|^2)S(0)+\tau S(v)+\bar\tau S(-v)$; minor failure ⇒
    visible at $v/2+w$. Depth $\delta$ enters as $e^{\pm\delta v}$.
    Window positivity gives `‖S(v)‖≤Re S(0)`
    (`norm_lagStructure_le_re_zero_of_weil_nonneg`). A reflected pair with complex
    amplitude `c` equals `2 exp(iγv)(Re(c) cosh(δv)+i Im(c) sinh(δv))`
    (`lagCoeff_reflected_pair_eq`); both parts of the amplitude remain visible.
11. **Logarithmic visibility.** Isolated pair in any on-line background of local mass $M$: seen at
    $\approx(1/2\delta)\log(M/|Q|)$; equal-depth clusters and finite sets: same, plus $O(n\ell)$; on $\zeta$
    background $\asymp(1/2\delta)\log\log T$.
12. **Every off-line zero is seen.** Attained top: Cesàro on a non-resonant grid. Unattained: bounded
    exponential sums have no top pole (Laplace = Mellin, identity theorem) ⇒ `offLine_visible`.
13. **Faithfulness.** The form determines the configuration (`eq_of_weil_eq`); the one-parameter lag family
    determines it up to $m(\rho)+m(\bar\rho)$ and the point $\tfrac12$. Ingham: $g$-separated on-line sets
    resolved iff $a>\pi/(2g)$, sharp.
14. **Rate = depth.** Least $\Re W$ at lag $v$ is $\ge-Ce^{Dv}$ and not $O(e^{\sigma v})$ for $\sigma<$ max depth.
15. **Parameter reduction** (all TRAPs): 3 params → even/odd 2 params → difference tests, one sign (no real
    zeros + Landau) → one parameter $v$ for generic width → **every** width with box splines
    (transform $(\sin z/z)^4$ real-rooted). Same for primitive $L(s,\chi)$ (real zeros allowed).
16. **Grids.** Geometric lag grids decide up to *chains* (depths without max): explicit chain with
    $\Re\le0$ at every integer lag but unbounded on the continuum (aliasing); continuum lag $O(\log M)$.
17. **Comb.** On the off-line lattice the lag family is silent to $v=L-2w$, negative at every tooth
    $v=nL$ ($4L\|\kappa\|^2(1-\cosh n\delta L)$), positive in gaps. Rotated patterns delay it (quarter turn:
    $3\ell/4\to2\ell$).
18. **Level transfer** $G+L+E$ conserved across levels; unattained top ⇒ subexponential excess; visibility
    recurs in every lag window of length $4\pi/g$ (Ingham).

### C. Finite lag ranges for $\zeta$ (effective Landau)
19. **Record-potential law.** Positivity of $P_v$ on $[0,V]$ + Laplace window: every exponent's
    coefficient $\le$ archimedean/pole terms + potential of the others. Fejér $\sin^2$: kernel decays
    $|z|^{-3}$ (loudness enters as $N^{1/3}$); $\sin^{2k}$: decay $2k+1$ via recursion
    $(z^2+((2k+2)\pi/V)^2)K_{k+1}=c\,K_k$. Grids replace distances by aliasing gaps.
20. **Companion law.** Local zero count ($\le40\log(180|t|)$ copies per unit window) ⇒ at every $V$:
    record quiet, or $P_v<0$ on $[0,V]$, or another zero within $r\asymp\kappa(\log\gamma)^{1/3}/V$.
    Twin radius improves to $O_w((1+\log\log\gamma_0)/V)$ uniformly in the zero.
21. **Elimination.** Combining Fejér orders kills a chosen companion exactly (`dipole_elimination`);
    iterating kills $p$ companions at cost $(8/3)^p$. Isolated twins are $e^{-cVr}$-tight unless tripled;
    coherent nearby coefficients add ⇒ **isolated twins cannot hide**. Clusters of $p$ hide only at
    geometric radius $e^{-cVr/p}$: approximate multiple zeros.
22. **Coherent cores.** Empty-annulus pigeonhole splits a cluster into core + loose members; eliminate loose,
    core adds coherently ⇒ near-top zero seen at $V_w\asymp(\log\gamma_0)^2\log\log\gamma_0/\delta_0$ (modulated
    numerator) — top need not be attained. Unmodulated family: lag $V(a,\sigma)$ from record loudness $a$
    and depth $\sigma$, $V\asymp\log^2(1/a)\log\log(1/a)/\sigma+\sqrt{\log(1/a)/a}$ (coherence drift is
    polynomial in $1/a$; `tendsto_sqrt_mul_recordLag`).
23. **Horizon law.** $P_v\ge0$ on $[0,V]$ ⇒ from every zero inside its horizon a chain of zeros, each
    $>1/V$ deeper, reaches beyond the horizon, escaping in **height and amplitude** $|h_w(\gamma-i\delta)|$
    (modulated family: height only). Wide zone: positivity keeps such zeros
    $\ge c_w(\delta_0/(V\log V))^{1/2}$ below the top.
24. **Explicit lags invert to excluded depths**: $V=\text{Numerator}/\delta_0+\text{Drift}$; all lags antitone
    in depth.

`EffectiveHorizons/` also quantifies the symmetric ξ-zero mass: with
`A(ε)=max(4,exp(20/ε),200/ε)` and `Z(ε)=max(A(ε/2)+1,6/(πε)+3,8)`,
`|M(T)−T log(T)/π|≤εT log(T)` for `T≥Z(ε)`. For Hausdorff order `k`, set
`K=10(k+1)+20` and `H=max(Z(1/500),500,42(k+1)+44K)`. Every calibrated
Hausdorff difference with shift `r≥ceil(20K)+ceil(KH²)+1` is nonnegative.

The centre Taylor sequence of ξ is **PF54**, and its first 55 reciprocal even coefficients are
nonnegative (`xi_centre_pfSeq_fiftyFour`, `evenRecipCoeff_XiC_nonneg_of_le_fiftyFour`). Retaining
the negative Gamma constant and both line-conjugate resolvent terms gives zero-depth bounds
`5/12` for `14≤|γ|≤16` and `7/16` for `14≤|γ|≤18`. Combined with the fourth-trace height floor,
these cover the order-54 cone (`EffectiveHorizons/LowHeightGammaPF54`, primary namespace).
All-order centre positivity remains open.

### D. Prime side
25. **Localized explicit formula** $W_\zeta(S_\xi f)=A_f(\xi)-\Pi_f(\xi)$; $\Pi_f$ is real; windowed mean of
    $\Pi_f$ is exactly 0 for window $2r\le\log2$ at any aperture; excursions balance exactly.
26. **Windowed variance.** Below $2rX\le1$: windowed mean square of $W-A_f$ is $\|\eta\|^2V_f$ (diagonal);
    bad heights have window weight $O((\log X/\log T)^2)$. Even (2-adic) sector diagonal at every
    bandwidth; odd sector diagonal up to $rX\le1$ (doubled threshold). Beyond: excess = prime pairs
    $|\log(m/n)|<2r$ with phase $(m/n)^{iT}$; a second window restores the diagonal.
27. **Archimedean horizon.** $\mu+P_X\ge(\log(1+|\tau|/4)-C_\varepsilon-(4+\varepsilon)\sqrt X)/2\pi$; coefficient
    4 optimal height-uniformly (`not_exists_PX_ge_of_lt_two`). Single-height positivity for
    $\sqrt X\le(\tfrac14-\varepsilon)\log T$ = localized zero-free region of depth ½.
28. **Kronecker.** $\sup_\xi\Re\Pi^{\text{prime}}_f=M_f^{\text{prime}}$ exactly; aligned heights force either
    $\Re W<0$ or exponential height escape (archPart grows like $\log$ height). Troughs: at single heights
    $\Re\Pi_f\le0$ exists, removing the $4\sqrt X$ cost there.
29. **Prime tail coupling.** The pole $s=1$ is a depth-½ pair at height 0 carrying the whole prime tail;
    for large $a$ the pole beats the archimedean part at height 0, so finite primes must cancel it.
30. **Window prime polynomial reads $S(T)$.** $\Re\Pi_\ell(T)=\int S(t)\psi_\ell'(t-T)\,dt-\text{Corr}_\ell(T)+o(1)$
    (Stieltjes); $\text{Corr}$ small outside a set of density 0 (zero density); Kronecker–Weyl on the prime
    torus gives $\Re\Pi_\ell>F_\ell(1)-\varepsilon\ge\ell\vartheta^2e^{\ell/4}$ on positive density ⇒ $S$ unbounded.
31. **Window arithmetic** ($2w<\log2$): $\le2$ consecutive powers per prime ($p\ge5$: one); divisor poset
    height $\le1$; same-side atoms only doublings/triplings; one crossing pair per $p\in\{2,3\}$, discount
    $e^{-(v-2w)}$; multiplicative relations of $\ell^1$ norm $\le2(v-2w)/\log3$ trivial; ratio 4 critical.

### E. Units: one width, one aperture
32. **Width is an exponent.** `zetaZeroWidth` = inf of admissible rates of lag family, Chebyshev deficit,
    band energies, spline windows, receiver damping; $\le\sigma$ ⇔ $P_v\ge-Ce^{\sigma v}$. Exponents are tail
    invariants ⇒ no bounded aperture decides width (lattice of width $\delta$ positive on $[-a,a]$ for every
    $a,\delta$). Amplification $|D|^k$ multiplies the exponent by $k$: returns the width it started with.
33. **One aperture.** RW ground energy, ACT shift, OWU capacity, EWU blind minimum, AIP/APT windows, SRT
    complex windows and $P_v$ are all `ZetaWindowPositive A`; $\mu(A)\ge0$ ⇔ window positive below $A$.
    Odd window = ACT variation inequality exactly (shift is a gauge) = OWU sinh capacity; EWU blind
    minimum = even polar ground energy below $\log2$; even window = polar even window + one affine slice.
34. **Ground-energy path** $A\mapsto\mu(A)$ carries three units: first sign change = contact aperture
    (positivity routes), fall rate = width (prime/zero routes), the zero forcing contact = near-top zero
    (zero-indexed routes). Zero-indexed routes are depth meters (seam charge
    $\sqrt2\log2\sinh(\log2\cdot\text{depth})$, mate gain $2\cdot\text{depth}\cdot\log n$, …).
35. **Rayleigh bridge.** $2\|\kappa_w\|^2\mu(v/2+w)\le\Re P_{w,v}$; $\mu\ge-Ce^{2\sigma A}$ ⇒ width $\le\sigma$.

### F. Floors, sampling, normalisations
36. **Sampling inequality.** $\sum_q|\Phi(z_q)|^2\le M(2a+2\pi)e^{2\pi}e^{2\sigma a}\int|f|^2$ for $\le M$ points
    per unit height, $|\Im z_q|\le\sigma$; depth-weighted version costs $\sum y_q^2$.
37. **Width → floor** needs non-clustering in $L^2$: under `OffLineDepthLocallyBounded W`,
    $\mu(A)\ge-A^2(2A+2\pi)e^{2\pi}e^{2\sigma A}W$. Unconditional depth mass per window $\le40\sigma^2\log(180T)$.
38. **Prime-side floor** (Stieltjes against normalised Chebyshev error, gauge derivative) and
    **archimedean-normalised floor** $\Re W\ge-C(a)\int|\mathcal Ff|^2\log(|y|+3)$ need no zero
    distribution; the latter has sharp rate $(2a+\varepsilon)\cdot$width.
39. **Graded incidence.** An allocation failing by $Ce^{2\sigma r}\int F^2$ still certifies $\tfrac12+\sigma$;
    a uniform constant or any subexponential loss gives RH; power saving $\theta<1$ gives width $\le\theta/2$.
40. **Certificate radius.** A radius-$R$ certificate reads only weights below $e^{2R}$; mimic weights exist
    at every radius. The $3/10$ certificate holds for every prime weight; the odd $9/25$ and $181/500$
    windows read exactly the prime 2.

### G. Calibrations
41. **Function fields.** Positivity at $a$ ⇔ Frobenius window Gram has negative index 0; silent for
    $a\le\log q/2$; window $\ge2g$ ⇒ positivity ⇔ purity; golden fake curve ($q=5$) positive exactly to
    $\log5/2$, every tooth $n\log5$ negative: threshold and comb are exact over $\mathbb F_q$.
42. **Orbits.** Unconditional local recurrence at every strip point (off zeros); head-conditioned
    decoupling; strip weight $m^{-\delta}$ damps rough variance by $y^{-2\delta}$, critical line keeps all of it.

---

## 5. Pillar theorems

| # | Statement | Lean |
|---|---|---|
| 1 | Off-line lattice hides exactly to $L/2$ | `RHTower.offLineLattice_weil_positive_iff`, `densityMatched_negative_test_iff` |
| 2 | Toeplitz law; hiding = on-line mimicry | `weil_nonneg_iff_toeplitz_of_lagFormula`, `weil_nonneg_iff_onLineShadow_of_lagFormula` |
| 3 | Crystal rigidity at the threshold | `uniform_crystal_of_hiding`, `crystal_iff_weil_floor_diagonal` |
| 4 | Relaxed Hodge exponent $=2\cdot$max depth | `offLineLattice_not_relaxedHodge_eventually_of_lt`, `profileConfig_not_relaxedHodge_eventually_of_lt` |
| 5 | Every off-line zero of a tempered configuration is visible; form is faithful | `offLine_visible`, `eq_of_weil_eq`, `eq_zetaZeroConfig_of_lag_weil_eq` |
| 6 | One parameter decides (TRAP) and measures the width | `zeta_onLine_iff_lag_primeWindow_nonneg`, `riemannHypothesis_iff_lag_splinePrimeWindow_nonneg`, `zetaZeroWidth_le_iff_lag_primeWindow_ge_neg_exp` |
| 7 | Grids decide up to chains; chains hide from grids | `zetaZeroWidth_le_iff_attainedTop_and_grid_primeWindow_ge_neg_exp`, `exists_chain_hidden_from_grid` |
| 8 | Hiding needs collapsed clusters; isolated twins cannot hide | `zeta_near_top_cluster_collapse`, `zeta_isolated_twins_cannot_hide` |
| 9 | Near-top zeros visible at explicit lag; horizon/escape law | `zeta_near_top_visible_at_polylog_lag`, `one_param_near_top_visible_at_explicit_lag`, `one_param_horizon_law_forces_height_and_amplitude_escape` |
| 10 | Unconditional lag envelopes (rate stays ½) | `zeta_lag_envelope`, `zeta_lag_envelope_vinogradovKorobov` |
| 11 | First prime paid on the lag family | `firstPrime_atom_paid_on_lagFamily_sharper` |
| 12 | $S(T)$ unbounded (unconditional) | `rvmRemainder_unbounded` |
| 13 | Width is a Landau exponent; no bounded aperture decides it | `zetaZeroWidth_exponent_law`, `configWidth_unbounded_aperture_property` |
| 14 | One aperture, one width | `theRoutesMeasureOneAperture`, `theRoutesMeasureOneZeroWidth`, `receiverDampingRate_eq_zetaZeroWidth` |
| 15 | Ground-energy abscissa law; Rayleigh bridge | `re_le_of_ccmRestrictedWeilGroundEnergy_ge_neg_exp`, `two_mul_ccmRestrictedWeilGroundEnergy_le_re_lagPrimeWindowRHS` |
| 16 | Width = $L^2$ rate unless depth mass escapes | `polarGroundEnergyRate_eq_zetaZeroWidth_or_high_depthMass_window_escape` |
| 17 | Uniform/subexponential floor ⇒ RH | `riemannHypothesis_of_odd_fullZeroForm_bddBelow`, `riemannHypothesis_of_subexponential_odd_floor` |
| 18 | Unconditional floors in energy and archimedean normalisation | `exists_fullZeroForm_ge_neg_of_zetaZeroWidth_lt`, `exists_re_W_ge_logWeighted_rate_sharp` |
| 19 | Every off-line zero has a smooth witness at aperture $\le C(4+|\Im\rho|)^2/\text{depth}^2$ | `RHTower.exists_smooth_weil_negative_quadratic_aperture` |
| 20 | Function-field calibration | `curveConfig_weil_nonneg_iff_unitary_of_card_le`, `goldenDatum_twoBump_comb_at_threshold` |
| 21 | Arbitrary clusters: `4((n+1)log(10⁶/δ)+log(A₀(|γ|+3)))≤a`. For ζ, the global count constant is `240`, giving `a≥480000 log(|γ|+3)log(10⁶/δ)` at `|γ|≥102`. Every off-line zero has a smooth detector supported in `[-(a+1),a+1]` with `a=max(exp 6,max(1/δ,48000000 log(|γ|+306))²)`. | `RHTower.not_hodgeIndex_below_nyquist_horizon`, `zeta_unit_count_le_240`, `exists_smooth_detector_at_explicit_product_aperture` |

---

## 6. Tools

**Developed (reuse, do not rebuild):**
- Lag-formula toolkit: abstract Toeplitz law, bump tests at lag points, Carathéodory–Fejér shadow,
  Newton/Lagrange power-sum lemmas, torus-compactness window lower bounds.
- Exponential-sum analysis: bounded sums have no top pole (`eq_zero_of_norm_tsum_exp_le`), growth-rate
  version, real-part Landau for separated heights, Cesàro on non-resonant grids, Abel means.
- Ingham inequality with explicit constant (`ingham_inequality`) and window lower bound.
- Finite-lag windows: `lapWin`, `fejerWin`, `fejerPowWin` (recursion, decay $2k+1$), `geomWin`;
  record-potential laws at each order; elimination sequences `elimSeq`; empty-annulus pigeonhole;
  mirror-avoiding depth choice.
- $\zeta$ inputs packaged: local zero count, Lorentzian zero mass, explicit dlVP/VK zero-free profiles on
  the lag carrier, `exists_good_width`.
- Explicit symmetric zero-mass and Hausdorff thresholds:
  `RHTower.xiSymmetricMass_close_explicit`,
  `RHTower.scaledHausdorffMomentDifference_nonneg_of_explicit_shift_le`.
- Explicit two-grid detection: `RHTower.two_three_heatGrids_explicitDetector_negative_of_offLine`
  gives a negative arithmetic-source square on `log 2` or `log 3`, after any odd offsets.
  `natDegree_xiHeatGridExplicitDetector_le` bounds its degree using finite sampled
  spectral data; separation products remain, so this is not a height/depth-only bound.
- Prime side: localized explicit formula, windowed Gram identity and diag/off-diag split, parity
  variance laws, Kronecker realisation, peak persistence, excursion balance, Stieltjes identity for
  $\Pi_\ell$ vs $S(T)$.
- Units: width dictionary (rates sets + `sInf` identities), `ZetaWindowPositive`, aperture dictionary,
  `zetaContactAperture`, sampling inequalities, three-normalisation floor bridge.
- Window arithmetic: dyadic window independence, lag-window incidence and crossing-pair payment.

**To build:**
- A signed prime-pair estimate beyond $X=T$ that keeps the height phase $(m/n)^{iT}$.
- Control of zeros beyond every finite horizon (height/amplitude escape).
- The width → $L^2$ floor arrow without local depth-mass bound.
- A positive window reaching the second prime ($v/2+w$ past $\log3/2$) on the lag family.
- An envelope $P_v\ge-Ce^{\sigma v}$ with any $\sigma<\tfrac12$.

---

## 7. Open questions and research topics

1. **Exponent below ½.** Prove $P_{w,v}\ge-Ce^{\sigma v}$ (equivalently $\mu(A)\ge-Ce^{2\sigma A}$) for some
   $\sigma<\tfrac12$; current unconditional: $e^{v/2-v^{e}}$, $e<3/5$ (VK). Any subexponential loss gives RH.
2. **Width → $L^2$ floor.** Residue of the open arrow: depth mass per window may grow like $\log T$
   (bound $40\sigma^2\log(180T)$); the arrow needs a $T$-independent bound. In the form-domain
   normalisation the rate equals the width unconditionally (ACCE `formGroundEnergyRate_eq_zetaZeroWidth`;
   polar = full $L^2$ rate: `groundEnergyRate_eq_polarGroundEnergyRate`).
3. **Beyond the square-root threshold.** Signed correlation of odd prime pairs $(m,m+2h)$, $h\ll m/T$;
   size-only bounds attain their excess, sieves lose the phase.
4. **Second prime window.** Archimedean odd ceiling $\approx0.375<\log3/2\approx0.549$; all-profile window
   between $3/10$ and $\tfrac12\log2$ (even pole direction) unpaid.
5. **Contact law.** Relate contact aperture to height and depth of the top zero.
6. **Escape.** Exclude chains of zeros escaping to large height and small amplitude beyond every horizon
   (equivalent to RH under positivity).
7. **Drift.** Remove the polynomial coherence drift $\sqrt{\log(1/a)/a}$ from record lags.
8. **Tradeoff asymmetry.** Forward exclusion below $\exp(cR/\log(C/\delta))$ at depth $\delta$, versus
   converse height reduction requiring $\exp(7000e^R)$: optimal $(\delta(n,R),T(n,R))$.
9. **Window incidence → pair payment** at the needed lag and height.
10. **Every height.** Control $\log\zeta-\sum_{p\le y}p^{-s}$ on the critical line conditioned on head returns.
11. **Zero-indexed routes.** Produce a per-zero depth meter from the prime source before the zero is known.

---

## 8. Traps

| Trap | Truth |
|---|---|
| Aperture is a height cutoff | It is a frequency resolution and a prime length $e^{2a}$ |
| Tests below threshold see depth | They see depth variation (jumps, TV); constant depth hides to $L/2$ |
| The off-line lattice is typical | Its invisibility is crystalline; everything else is seen earlier |
| More off-line zeros = more visible | Not monotone; positivity is collective |
| Finite off-line sets have a threshold | Visible at logarithmic aperture in any background |
| Polar constraint helps on dense configurations | Hodge index = full positivity on lag lattices |
| Window/height averages read depth | They are aperture-$r$ forms; off-line lattices pass every window average |
| Prime side keeps a sign on short windows | Windowed mean of $\Pi_f$ is exactly 0 |
| RH ⇔ one-parameter / spline / grid / prime-window / ground-energy statement is progress | TRAP: criteria are cheap; dozens are proved |
| Landau gives a visibility lag | Ineffective; lags need record loudness + local count |
| A lag grid decides | Chains hide from grids; continuum lags see them |
| A twin hides a record | Isolated twins add coherently; hiding needs $\ge3$ zeros in a collapsed cluster |
| "Near-top zeros are seen at polylog lag" | Only the numerator is polylog; drift $\sqrt{\log(1/a)/a}$ is polynomial in amplitude |
| dlVP/VK improve the lag rate | Envelope rate stays ½ ($e^{v/2-\sqrt v/10}$, $e^{v/2-v^{e}}$) |
| The sign is what must be proved | Any subexponential loss suffices; rate = width |
| Bounded-aperture windows bound the width | They report nothing in the width unit (Nyquist fibre has every width) |
| A certificate at radius $R$ is about $\zeta$ | It holds for every weight agreeing below $e^{2R}$ |
| One route's positivity is independent evidence | One aperture, one width, one ground-energy path |
| Amplification (Deligne-style) lowers the exponent | $|D|^k$ has exponent $k\cdot$width: no new information |
| Energy-normalised floor = $L^2$ floor | $L^2$ needs local depth-mass control |
| Weil form unbounded below | Not in its archimedean normalisation |
| `exists_gt_re_archPart_of_riemannHypothesis`, `exists_height_escape_of_riemannHypothesis`, `zeta_re_le_iff_grid_primeWindow_ge_neg_exp_of_zerosApproachLine` are results | Conditional on RH / `ZerosApproachLine` |
| Bagchi recurrence on the strip transfers to the line | Strip damps rough variance; line keeps all |

---

## 9. Place in the research

**Imports.** RHTower (89 imports: `ZeroConfig`, explicit formula, local count, zero-free regions,
Lorentzian mass, receivers); ArithmeticCriticalityTheory (12: $\mu(A)$, window gauge floors, shifted
ground states); BiScaleUncertainty (11: band/packet width laws, cubic spline probe); AIP (5: odd
windows to $181/500$, dyadic incidence); arithmetic-positivity-theory (5: tent detection, factorial
ramps); HTGeometry (4: Carathéodory–Fejér, prime-torus Kronecker, local sampling); SSHA, ACS (1 each).

**Exports** (who uses what):
| Programme | Uses |
|---|---|
| ArithmeticCastelnuovoSeveri (17 files) | Ground-state law, Hodge index on lattices, abscissa bridges, width→floor, near-top lags, contact aperture, sampling |
| ScaleSignedIncidenceCriticality (10) | Visibility laws (pairs, clusters, crystals, dilution), width as Landau exponent / aperture property, receiver damping |
| arithmetic-positivity-theory (9) | Visibility laws, prime windows, archimedean horizon, windowed variance, $S(T)$ |
| ArithmeticOrientationTheory / Geometry (5+5) | Nyquist aperture, sampling, walls = width, every-width spline criterion, heat time |
| DilutionCrystallizationPincer (4) | Crystal rigidity, dilution, relaxed Hodge exponent, non-clustering arrow |
| ArithmeticContinuationAndCriticalEnergy (3) | Contact aperture, walls, unsigned depth sampling (it closes the form-domain arrow) |
| RHTower (3), ArithmeticCompensationTheory (3) | Grid attainment, heat time, routes = width; incidence ledger, receiver damping, walls |
| AIP (2), BSU (2), TransMetzlerWeilPositivity (2) | Dyadic windows, polar bridge, ledger; amplification, walls; windowed mean value, windowed no-go |
| SelectivePositivityAndThresholdLaws, ArithmeticPolarization, ArithmeticCorrespondencePositivity, ArithmeticOfSquareRootPrecision | Window certificates and the prime weight ($3/10$, odd $181/500$) |
| ArithmeticCriticalityTheory, ArithmeticKunnethTheory, BezoutValuationIncidence, ReverseTwistedArcPoleCompression | Height-window averages and small-aperture positivity; off-diagonal beyond threshold; VK envelope; prime-tail coupling |

SRT is the **measuring instrument** of the corpus: other programmes produce positivity or floors at an
aperture; SRT converts them into the width unit and says what they can and cannot see.

---

## 10. Big picture

- Weil positivity is **faithful but blind at finite resolution**. The full form determines the zeros;
  any bounded aperture is fooled, and being fooled is exact mimicry by an on-line configuration.
- Everything measures **one number**, the zero width, as an **exponent**. Exponents are tail
  invariants: no finite window, finite prime set, finite computation or bounded aperture can bound
  them. RH ⇔ statements are abundant and worthless as progress; what is missing is an **estimate**
  with exponent $<\tfrac12$, and any subexponential estimate would already be enough.
- Unconditional prime information (PNT, dlVP, VK, Chebyshev) moves constants and sub-exponential
  factors but never the exponent; the first prime is paid, the second is not.
- For $\zeta$, positivity on a finite lag range already forces rigid structure: off-line zeros can hide
  only as approximate multiple zeros or by escaping to large height and small amplitude. The remaining
  enemy sits at the square-root threshold (pair correlation of zeros / signed prime pairs with height
  phase) and at infinity (escape beyond every horizon).
- Consequence for an RH proof: it must inject information that is uniform in height and reaches past
  $X\asymp T$ with phase — not another reformulation, not another finite certificate, and not a sign
  argument at a fixed aperture.
