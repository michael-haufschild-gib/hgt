# Arithmetic Correspondence Positivity (ACP)

Namespace `GaloisForLFunctions.ArithmeticCorrespondencePositivity`; umbrella `ArithmeticCorrespondencePositivity.lean`;
78 modules. All results unconditional; theorems carrying RH or simplicity as a hypothesis are stated implications.

## 1. Motivation

Over $\mathbb F_q$ one structure, the intersection theory of correspondences on $C\times C$, supplies the sign of the
explicit formula (Rosati positivity, Hodge index), its budget $2g$, the base and the tensor powers. ACP asks, for the
correspondences $\mathbb Z$ actually has (dilations/Hecke, affine maps, the successor, the archimedean flow): which
layers of Weil's argument exist, which are free, which are absent, and what a sign specific to $\zeta$ would have to
look like. Second question: what do energy budgets of arithmetic rows (damped Möbius receiver, Mertens, $\psi(x)-x$)
read off the zeros, and is there a $\mathbb Z$-analogue of the budget $2g$?

## 2. Objects

| Object | Lean | Meaning |
|---|---|---|
| Normalized graph | `normGraph`, `graphDegree` | unique isotropic class in $y+\langle H,V\rangle$ with $N\cdot V=1$; degree $\delta(y,y)/2$ |
| Kernel / Rosati degree | `detDeg`, `rosatiDeg`, `exteriorDetDeg` | $\prod P(\alpha_i)$; $\sum P(\alpha_i)P(q/\alpha_i)$; $\prod_{|S|=k}P(\prod_S\alpha_i)$ |
| Symmetric-square eigenvalue | `symSquareEig` | $(\alpha-c)(q/\alpha-c)$, spectrum of $(F-c)(F-c)'$ |
| Local form at a reflection pair | `localForm` | $2\Re(u\bar v)$ on $(\hat g(\rho),\hat g(1-\bar\rho))$, signature $(1,1)$ |
| Hecke symbols | `heckeSymbol`, `symHeckeSymbol`, `symHecke` | $p^{s-1/2}$; $p^{s-1/2}+p^{1/2-s}$; $g(\cdot-\log p)+g(\cdot+\log p)$ |
| Successor defect | `succShiftDefect`, `successorEnergy` | $D_a(s)=\sum a_{n+1}((n+1)^{-s}-(n+2)^{-s})$; $\sum\Lambda(n)^2/(n(n+1))$ |
| Fake data | `goldenDatum` (ACS), `complexFake`, `quartetCurveDatum` | real off-line pair; quartet $q=16$, roots $\pm8i,\pm2i$; Frobenius quartet |
| Source twins | `liouvilleTwin`, `flipTwin` | sign-twisted prime weights $w\le\Lambda$ |
| Completed systems | `CompletedPositiveSystem` (SBWF), `HeightCoupledSystem`, `FejerCoupledSystem` | entire order one, FE, PD vertical sections of $-F'/F$ |
| Contraction factors | `midpointSymSquare`, `coupledQuartetSymSquare`, `realPairPlanter` | PD multipliers moving zeros onto/off the line |
| Log profile / translation Gram | `logProfile` (ADR), `pronicPairing` (ACCE) | $g(u)=e^{-u/2}v(\lfloor e^u\rfloor)$; dilation = translation |
| Escape kernel | `escapeKernel`, `cauchyDensity` | phase kernel $\sum c_k\theta_k\psi_k(a)\overline{c_l\theta_l\psi_l(b)}/(2x+i(y_k-y_l))$ |
| Abel Gram / line symbol | `abelGram`, `lineSymbol`, `abelWeight`, `abelPairing` | $\int e^{-2cu}g(u-a)g(u-b)$; Laplace transform of damped profile |
| Damped Möbius receiver | `receiver`, `receiverLogProfile`, `centeredReceiverSymbol`, `receiverResidue` | symbol $\zeta(s)(1/\zeta(s+\varepsilon)-1/\zeta(1+\varepsilon))/s$; $r_\rho=\zeta(\rho-\varepsilon)/(\zeta'(\rho)(\rho-\varepsilon))$ |
| Pole atoms | `poleMassConstant`, `receiverPoleAtomMass`, `visibleTranslatedZetaOrder` (AOT) | $c_m=\int(1+x^2)^{-m}$; $c_m|a|^2$; $\operatorname{ord}_\rho\zeta-\operatorname{ord}_{\rho-\varepsilon}\zeta$ |
| Arithmetic rows | `mertensRow`, `primeErrorRow`, `vonMangoldtRow`, `shiftedPrimeErrorRow` | $M(n)$; $\psi(n)-n$; $\Lambda(n)$; $\psi(n+1)-n$ |
| Curve budget data | `spectrumCount`, `spectralMertensRow`, `repulsionWeight`, `chebRow`, `ellipticMertens` | $\sum_\beta\operatorname{mult}^2$; coefficients of $\prod(1-\beta_iu)^{-1}$; Lagrange weights |
| Prime-error split | `primeErrorAbelSlope`, `zeroPart`, `archRemainder`, `splitConstant`, `zeroWave` | $2c\int e^{-2cu}g^2$; $\sum'_q(-1/\rho_q)/(s-\rho_q)$ |
| Archimedean genus | `poleSharpConstant` (RHTower) | $\sum_\rho 1/(\rho(1-\rho))=2+\gamma-\log4\pi$ |
| Source field | `xiTransverseField`, `xiSourceField`, `xiRealReciprocal` | $\sum_q(\Re p-\Re q)/|p-q|^2$ |

## 3. Language

- **Weil layers.** L1 identities; L2 graphs (theorem of the square); L3 budget $\delta(x,x)$; L4 kernel counts;
  L4′ spectrum of symmetric squares; L5 Rosati positivity; L6 base (fixed loss of tensor powers).
- **Sufficiency**: Weil's inequality on every span $\{x,\xi x\}$; the budget existing is not enough.
- **Kernel vs trace effectivity**: kernel counts pair $\alpha$ with $\bar\alpha$; Rosati pairs $\alpha$ with $q/\alpha$.
- **Local type** of a correspondence at an off-line pair: hyperbolic (boost), elliptic (rotation/swap), unipotent.
- **Resonant prime** at $\rho=\sigma+i\gamma$: $\gamma\log p\in\pi\mathbb Z$.
- **Pole tax** $\Delta\kappa$: extra archimedean pole order paid by a contraction. **Real anchor**: real pole required to
  carry a non-real one in a PD polar sum.
- **Dominant zero**: rightmost visible translated zero of a row's symbol. **Escape state**: limit of normalized
  Grams. **Escape rank**: rank of the escape state on dilations. **Abel escape**: $c\downarrow0$ limit of
  $c\,A_c$. **Atom**: window mass $\pi|r|^2$ (simple pole) or $c_m|a|^2$ at scale $e^{2m-1}$.
  **Mass at infinite height**: Abel mass not carried by any compact window.
- **Budget** of a row: linear log-energy $\int_0^L g^2\le SL+B$; **slope** $S$. Mertens budget, prime-error budget.
- **Quadratic terminal**: Xi zero $p$ with empty cone $\{r:\ \operatorname{depth}(r)^2>\operatorname{depth}(p)^2+(\Delta h)^2\}$.
- **Source field**: simple Laurent coefficient of $(\zeta'/\zeta)^2$ over $2m$, plus archimedean term.

## 4. Mechanisms

**A. Correspondence algebra**
1. Normalization: $N(y)$ unique mod fibres, degree = half defect, theorem of the square is an identity on every polar
   surface.
2. Similitude law: Hecke graphs multiply degree by $e^{s(g)}$; normalized ones keep it; budget fixed along orbits.
3. Determinant pairing: without real eigenvalues $\prod P(\alpha_i)=|A|^2$; trace pairing is a Toeplitz form of power
   sums, $\ge0$ ⇔ unitary.
4. Symmetric-square core: $\alpha\alpha'=q$, all $(\alpha-c)(\alpha'-c)\ge0$ real for $c\in\mathbb R$ ⇒ $|\alpha|^2=q$.
5. Exterior collision: the max-modulus $k$-set ($k\le|\iota|/2$) collides a conjugate pair into a real off-line
   eigenvalue of $\Lambda^kH^1$.

**B. Local geometry**
6. Boost lemma: positivity of $2\Re(u\bar v)$ on a cyclic span under $|\beta|\ne1$ forces $u\bar v=0$; rotation gives
   only $\Re(u\bar v)\ge0$.
7. Resonance: $\Im(p^{\rho-1/2}+p^{1/2-\rho})=2\sinh((\sigma-\tfrac12)\log p)\sin(\gamma\log p)$; $p^a\ne q^b$ ⇒ a
   non-real point resonates at ≤ 1 prime; scale $e^{\pi/(2|\gamma|)}$ never resonates.
8. Isometries of $h$: diagonal ⇔ $a\bar b=1$ (separating ⇒ boost); antidiagonal squares are rotations.
9. Resolution = length: $|p^{i\gamma}-p^{i\gamma'}|\le\log p\,|\gamma-\gamma'|$; isolation at spacing $2\pi/\log T$ costs
   length $\asymp\log T$.

**C. Source and successor**
10. Weil functional affine in the prime weight, antitone on nonnegative atoms ⇒ $\zeta$ is the worst dominated twin on
    $f\star\tilde f$, $f\ge0$.
11. Successor: twist moduli unchanged; $D_\Lambda$ holomorphic on $\Re s>0$, $|D_\Lambda|\lesssim(|s|+1)^{1-\sigma+\eta}$,
    $D_\Lambda/s\in H^2(\Re s>\tfrac12)$ with norm$^2$ $2\pi\sum\Lambda(n)^2/(n(n+1))$.

**D. Amplification and contraction**
12. Root extraction $|c|^k\le Ce^{Lt}$ ⇒ width $\le L/k$; family Jensen $(\sum wz)^k\le\sum wz^k$, zero loss ⇔ flat.
13. Archimedean midpoint factors $M_\beta=(s-\tfrac12)^2/((s-\beta)(s-1+\beta))$: Laplace density
    $(e^{\beta t/2}-e^{(1-\beta)t/2})^2\ge0$ ⇒ PD; contracts real pairs at $\Delta\kappa=0$.
14. Post–Widder: PD polar sum ⇒ $w(t)=\sum c(z)e^{\Re z\,t}\cos(\Im z\,t)\ge0$ ⇒ real-anchor law
    $c(\sigma_{\max})\ge c(\sigma_{\max}+i\gamma_1)$ (sharp $2{:}1$ for a single ordinate).
15. Height coupling $F^2F(\cdot+i\gamma)F(\cdot-i\gamma)$ (Gram of translates; Fejér coupling with $K+1$ translates):
    phase collision $\pm i\gamma\mapsto0$ creates the exact real anchor.
16. Archimedean budget: PD at $\sigma=2$ ⇒ $\Re(-F'/F)(2)\ge0$; Hadamard pair sum bounds central and off-line orders by
    $\kappa$ and $d\log(3+|\gamma|)$.

**E. Escape geometry**
17. Dilation by $j$ = translation by $\log j$; pronic measure = Lebesgue on the log scale.
18. Horizon law $e^{-2xL}\int_0^LF(u-a)\bar F(u-b)=K_{\theta(L)}(a,b)-e^{-2xL}K_1$; Cauchy positivity
    $\sum v_k\bar v_l/(2x+i\Delta)=\int_0^\infty e^{-2xt}|\sum v_ke^{-iy_kt}|^2$; Artin/Bohr independence.
19. Horizon averages kill cross terms at window $\gg$ inverse spacing; floor error makes power rows exponential profiles
    up to $e^{(x-1)u}$.

**F. Abel calculus**
20. Wiener–Khinchin: $A_c(a,b)=e^{-c(a+b)}(2\pi)^{-1}\int|G(c+iy)|^2\cos(y(a-b))dy$; $A_c(a+t,b+t)=e^{-2ct}A_c(a,b)$.
21. Atom law: Lorentzian $2\arctan(\delta/\varepsilon)\to\pi$; order-$m$ pole: rescale $y=y_0+ex$, kernel $(1+x^2)^{-m}$.
22. Capacity: finitely many separated atoms ⇒ $e\int|S|^2\ge M$ for every $M<\pi\sum|r|^2$.
23. Abelian bound (Tonelli): $\int_0^Lf\le\Phi(L)$ ⇒ $\int e^{-su}f\le\int se^{-sL}\Phi(L)dL$; linear $\Phi$ gives
    $e\int|G|^2\le\pi S+2\pi eB$.
24. Hardy datum without energy premise: Laplace uniqueness on one absolutely convergent line identifies the $L^2$ step
    profile with the centered symbol ⇒ unconditional energy exponent at the zero abscissa.
25. Compact windows: finite zero factorization ⇒ polynomial growth $(\Re z-\Theta)^N|1/f|\le C$.

**G. Budgets**
26. Row symbol $\Phi_v(s)/s$; continuation by the identity theorem: a budget makes $\Phi_M=1/\zeta$ (resp.
    $-\zeta'/\zeta-\zeta$) holomorphic on $\Re s>\tfrac12$, forcing $\zeta\ne0$ there.
27. Residue mass ≤ slope: capacity against the Abelian bound.
28. $-\zeta'/\zeta$ has simple poles $-m_\rho$ at every zero; $1/\zeta$ has order-$m$ poles: a double zero gives window
    mass $\gtrsim e^{-2}$, outgrowing $\pi S$.
29. $\mathbb F_q$: Cesàro of unimodular $z\ne1$ vanishes; Lagrange partial fractions $h_m=\sum A_i\beta_i^m$; AM–GM
    majorant of $H(z)$ at $z=(1-\varepsilon)\bar\beta_i$ excludes collisions.

**H. Source field**
30. $(\sum m_j/(s-z_j))^2$: simple coefficient $2m_jE_j$, $E_j=\sum_{k\ne j}m_k/(z_j-z_k)$; real part $0$ on the line,
    $>0$ at the deepest off-line zero with its reflection.
31. Quadratic ascent in log windows (≤ $C\log$ zero copies) reaches a terminal; beyond a terminal every reflected pair
    contributes $\ge0$ to $\Re\xi'/\xi$.

## 5. Pillar theorems

| Theorem | Lean | Status |
|---|---|---|
| Theorem of the square is an identity; golden datum has $\deg N(2\Delta-\Gamma_F)=-1$ | `normGraph_square`, `goldenDatum_normGraph_degree_neg` | proved |
| RH ⇔ every normalized Hecke graph of the cubic spline has degree ≥ 0 | `riemannHypothesis_iff_splineCycle_graphDegree_nonneg` | proved |
| Budget fixed at every level ⇔ unitary; golden/complex fake budgets insufficient | `budget_sufficient_iff_unitary`, `complexFake_budget_insufficient` | proved |
| Rosati degree ≥ 0 on $\mathbb R[F]$ ⇔ unitary | `rosatiDeg_nonneg_iff_unitary` | proved |
| Kernel counts ≥ 0 without real eigenvalues; counts don't force purity | `detDeg_nonneg_of_im_ne_zero`, `counts_do_not_force_purity` | proved |
| Spectrum of $(F-c)(F-c)'$ ≥ 0 ∀$c$ ⇔ unitary; RH ⇔ local criterion at one prime | `symSquare_spectrum_nonneg_iff_unitary`, `riemannHypothesis_iff_symSquare_heckeSymbol_nonneg` | proved |
| Exterior kernel counts force unitarity (every genus) | `unitary_of_exteriorDetDeg_nonneg` | proved |
| Boost ⇒ half-blind; two primes ⇒ blind; archimedean-closed carrier blind | `mul_conj_eq_zero_of_cyclic_nonneg`, `eq_zero_of_two_prime_symCyclic_nonneg`, `eq_zero_of_archimedean_closed` | proved |
| Separating local isometry is a boost | `separating_isometry_is_boost` | proved |
| Successor shift has the poles of $-\zeta'/\zeta$; $D_\Lambda/s\in H^2$ | `succShift_vonMangoldt_eq`, `tendsto_integral_norm_sq_succShiftDefect` | proved |
| Affine correspondences: $\#\operatorname{Fix}(f^m)\in\{0,1\}$ constant | `fixedPoints_iter_subsingleton`, `affine_graphs_meet_at_most_once` | proved |
| Aperture $\le3/10$: coercive Weil positivity for every prime weight | `positivity_beyond_isotropy_at_finite_aperture` | proved |
| $\zeta$ worst twin on nonnegative tests | `re_weilFullFunctional_vonMangoldt_le_of_nonneg`, `weilPositive_nonneg_transfers` | proved |
| RH ⇔ one fixed loss bounds all tensor powers of the spline correlation | `riemannHypothesis_iff_fixed_tensor_loss` | proved |
| Hyperbolic exhaustion: a budget pays an off-line pair only on a finite segment | `exists_gt_abs_of_hyperbolic` | proved |
| Section count ⇔ Hodge index; over ℤ ⇔ RH | `hodgeIndex_iff_exists_sectionCount`, `riemannHypothesis_iff_exists_sectionCount` | proved |
| One-sided prime count is RH | `riemannHypothesis_iff_one_sided_count` | proved |
| Real pairs contract at $\Delta\kappa=0$; κ = 1 has no real off-critical zero | `CompletedPositiveSystem.contractRealPair`, `completedPositiveSystem_one_ne_zero_of_midpoint_contraction` | proved |
| Real-anchor law (Post–Widder) | `real_anchor_of_posDef_polarSum`, `two_mul_le_real_anchor_of_single_ordinate` | proved |
| Any complex quartet contracts at zero marginal tax after height coupling | `CompletedPositiveSystem.heightCouple`, `CompletedPositiveSystem.contractComplexQuartet_heightCoupled` | proved |
| Off-line multiplicity at one ordinate ≲ $\kappa+d\log(3+|\gamma|)$; anchored quartet ⇒ κ ≥ 3 | `CompletedPositiveSystem.ordinateQuartet_multiplicity_archimedean_bound`, `CompletedPositiveSystem.three_le_pole_of_anchored_quartet` | proved |
| Fejér coupling: central coefficient $9(K+1)/(2K)\to9/2$ | `CompletedPositiveSystem.fejerCouple`, `CompletedPositiveSystem.fejerTwo_ordinateQuartet_bound` | proved |
| Cofactor Gram = translation Gram; Laplace symbol of the cofactor profile | `pronicPairing_rowDilate_eq_translationGram`, `tendsto_laplace_cofactorProfile` | proved |
| Escape rank = number of dominant zeros, every phase | `escapeForm_log_eq_zero_iff` | proved |
| Escape completeness ⇔ dominant split + subdominant remainder | `exists_tendsto_normGram_of_dominant_split` | proved |
| RH ⇔ damped receiver admits at every ε | `riemannHypothesis_iff_forall_admits` | proved |
| Abel escape law: finite-height escape = poles on the abscissa line | `tendsto_abelGram_of_poles` | proved |
| Simple dominant zero ⇒ Abel atom $\pi|r_\rho|^2$ | `tendsto_receiver_window_atom` | proved |
| Energy $O(T^\kappa)$ ∀κ > max(0, 2Θ − 2ε − 1) | `exists_receiver_energy_le_of_zeroAbscissa` | proved |
| Order-$m$ rightmost zero ⇒ atom $c_m|a|^2$ at scale $e^{2m-1}$ | `receiver_pole_coefficient_ne_zero_and_atom` | proved |
| Compact windows at the frontier select the maximal visible order | `exists_receiver_compact_maximal_order_law` | proved |
| Bounded visible orders, or Abel escape to infinite height | `receiver_visible_order_or_infinite_height_escape` | proved |
| Endpoint law: $E\le C(T+1)^{2\theta}$ ⇒ $C\ge\sum|r_\rho|^2/(2\theta)$ | `residue_mass_le_of_energy_le_at_zeroAbscissa` | proved |
| Shadow law: $\limsup E_\varepsilon/\log T\ge\sum|\zeta(\text{shadow})/(\zeta'(\rho)\,\text{shadow})|^2$ | `not_forall_receiver_energy_le_log` | proved |
| $\limsup(\log X)^{-1}\int_1^XM^2/x^2\ge\sum|1/(\rho\zeta'(\rho))|^2$ | `not_forall_mertens_energy_le_linear` | proved |
| $\limsup(\log X)^{-1}\int_1^X(\psi-x)^2/x^2\ge\sum m_\rho^2/|\rho|^2\ge2+\gamma-\log4\pi$ | `not_forall_primeError_energy_le_linear`, `not_forall_primeError_energy_le_of_lt_poleSharpConstant` | proved |
| Mertens budget ⇒ RH + simple critical zeros + $\sum|1/(\rho\zeta'(\rho))|^2\le S$ | `mertens_budget_forces_simple_critical_spectrum` | proved |
| Prime-error budget ⇒ RH and slope ≥ archimedean genus | `riemannHypothesis_of_primeError_budget`, `poleSharpConstant_le_of_primeError_budget` | proved |
| $\mathbb F_q$: finite prime-error slope ⇔ pure; slope = $\sum\operatorname{mult}^2\ge2g$ | `unitary_of_powerSum_energy_le_linear`, `tendsto_powerSum_energy_div`, `spectrumCount_eq_card_iff` | proved |
| $\mathbb F_q$: Mertens budget ⇔ pure + simple; slope = repulsion energy; genus 1 ⇔ $a^2<4q$ | `curveMertens_budget_iff`, `tendsto_curveMertens_energy_div`, `ellipticMertens_budget_iff` | proved |
| Abel–Cramér law: RH ∧ simple ⇔ Abel slope of $\psi-x$ → $2+\gamma-\log4\pi$ | `riemannHypothesis_and_simple_iff_tendsto_abelSlope` | proved |
| Under RH + simple zeros the zero part has no mass at infinite height | `eventually_lintegral_zeroPart_le` | proved (RH hypothesis) |
| Off-line zero ⇒ nearby terminal with positive transverse field ≥ $m/(2\,\text{depth})$ | `exists_local_outward_field_witness` | proved |
| Source field = transverse field at every Xi zero; finite work identity | `xiSourceField_eq_transverseField`, `xiSourceField_finite_work` | proved |

## 6. Tools

**Developed**
- Polar-surface graph calculus: `normGraph_degree`, `normGraph_degree_heckeGraph`, `normGraph_degree_one_add_act`.
- Local-form toolkit: `localForm_boost`, `symHeckeSymbol_im`, `exists_nonresonant_scale`, `halfBlind_iff_cyclicForm_nonneg`.
- Twin comparison: `weilFullFunctional_sub_eq`, `flipTwin_lt`, `abs_atom_le_edge`.
- Contraction kit: `isEvenPosDef_midpointSymSquare`, `IsEvenPosDef.symSquareShift`, `IsEvenPosDef.fejerShift`,
  `exists_coupled_entire_contraction`, `CompletedPositiveSystem.plantRealPair`, `HeightCoupledSystem.absorbShiftedPoles`.
- Fejér–Egerváry–Szász first-harmonic bound: `fejer_egervary_szasz_first_harmonic_le`.
- Escape kit: `exp_mul_hermGram_eq`, `cauchyForm_eq_integral`, `eq_zero_of_expSeries_eq_zero`, `tendsto_avg_gram`,
  `norm_floor_cpow_sub_le`.
- Abel kit: `abelGram_spectral`, `tendsto_window_atom`, `tendsto_window_atom_of_pole_order`,
  `eventually_le_mul_integral_of_atoms`, `lintegral_exp_mul_le_of_horizon`, `mul_integral_norm_sq_lineSymbol_le_of_linear`,
  `tendsto_scaled_integral_of_finite_windows`, `exists_compact_inverse_polynomial_bound`.
- Row calculus: `integral_stepLaplaceIntegrand`, `integrable_and_memLp_dampedProfile_logProfile`,
  `lineSymbol_logProfile_eq`, `pronic_energy_eq_log_integral`, `sum_residue_le_slope`.
- Pole bounds: `exists_inv_zeta_pole_bound`, `exists_logDeriv_symbol_pole_bound`, `exists_cofactor_pole_bound`.
- Prime-error split: `primeErrorSymbol_eq_zeroPart_add`, `exists_integral_norm_sq_archRemainder_le`,
  `abel_tail_le`, `tendsto_abel_head`.
- Xi field: `xi_window_card_le_log`, `exists_xi_quadratic_terminal_near`, `xiLinePairRe_height_reserve`,
  `re_logDeriv_xi_eq_realReciprocal_tsum`, `laurentCoeff_square_of_pole_and_regular`.

**To build**
- A localizing carrier with a non-hyperbolic (elliptic) local symmetry at off-line pairs, from a non-multiplicative
  operation.
- An intrinsic exterior square over $\mathbb Z$ without shifted poles (non-linear $GL(2)$ / cohomological lift).
- Vertical mean-square bounds for $\zeta(s)/\zeta(s+\varepsilon)$ near the zero abscissa (mass at infinite height
  off RH).
- A signed estimate of the exterior interaction row in the source-field work identity.
- An unconditional upper bound for the prime-error Abel slope (it would decide RH with simple zeros).

## 7. Open questions

1. Is there an unconditionally positive carrier that localizes at off-line pairs by an elliptic symmetry and separates
   $\zeta$ from its twins?
2. First gauge-charged window $[-181/500,181/500]$: does the Liouville twin fail Weil positivity on edge-concentrated
   tests?
3. Off RH: is the Abel mass of the damped receiver at the zero abscissa carried by compact windows (no mass at infinite
   height), given only summable residues?
4. Does a Mertens or prime-error budget hold unconditionally with any slope? (Each implies RH; the Mertens one also
   simple zeros.)
5. Is $\sum_{\text{critical}}|1/(\rho\zeta'(\rho))|^2$ finite, and does it equal the Mertens slope?
6. Sign of the source work $\sum(\Re p-\tfrac12)\,\text{source}(p)$: can the exterior interaction be controlled at
   quadratic terminals?
7. A base over $\operatorname{Spec}\mathbb Z$ from a non-multiplicative structure with power-independent loss.
8. A pointwise lower bound for the successor regular part off the real axis.
9. Can height/Fejér-coupled systems be reduced below the $9/2$ central coefficient, or is $\approx(9/16)\kappa$ the
   sharp off-line multiplicity per ordinate?

## 8. Traps

| Trap | Fact |
|---|---|
| The theorem of the square / budget is what $\mathbb Z$ lacks | Both exist and are free; golden datum satisfies them. Missing: sufficiency (Rosati sign) |
| Kernel counts give effectivity | Blind to complex quartets; $\zeta$'s strip zeros are non-real |
| Symmetric Hecke positivity sees real off-line points | Real points resonate at every prime |
| More primes help localization | Two already force blindness; the obstruction is hyperbolicity |
| Bounded-aperture Weil positivity is about $\zeta$ | Holds for every prime weight; window meets no prime |
| Positivity on nonnegative tests carries sign information | $\zeta$ is the worst twin there; ζ-specific positivity needs sign-changing autocorrelations |
| The successor is a correspondence with content | Unipotent on polar fibres; a bounded Hardy perturbation; changes no slope or atom |
| A section count or Stepanov count is weaker than RH | Each is equivalent to RH |
| Bare vertical PD over $\mathbb F_q$ separates fakes | Golden datum and complex fake are vertically PD |
| CompletedPositiveSystem axioms force RH | Closed under contracting off-line zeros at pole cost; only κ = 1 excludes real zeros |
| Zero-tax quartet contraction is free | Needs a real anchor (Post–Widder); coupling across heights supplies it |
| Escape completeness is a positivity question | It is an energy split / symbol condition on $G$ |
| Escape at the abscissa needs zero-free strips or energy premises | Energy exponent, atoms and maximal-order law at Θ are unconditional |
| Cramér's constant needs RH | The lower bound is unconditional; the matching limit is RH + simplicity |
| A prime-error budget sees simplicity | It is purity only; multiplicity shows as excess slope $\sum(m^2-m)/|\rho|^2$. The Mertens budget sees it as divergence |
| The source work at a zero has a sign | Only the transverse pair energy is signed; the exterior row is not |

## 9. Context

| Uses | Modules |
|---|---|
| RHTower | 45 (Xi zero counts, Hadamard partial fractions, Plancherel, Cramér tails, convexity, genus) |
| ArithmeticCastelnuovoSeveri | 9 (polar surfaces, curve data, Frobenius-span Hodge index, scaling surface) |
| HTGeometry | 6 (Stepanov, quadratic ascent, finite factorization, Laurent translation) |
| ArithmeticDefectRigidity, ArithmeticCorrelationGeometry | 4 each (log profiles, cofactor limits; golden datum, energy growth) |
| SquareRootThreshold, MultiplicativePositivityGeometry, ArithmeticOrientationGeometry, ArithmeticContinuationAndCriticalEnergy | 2 each |
| StripBochnerWeilForcing, BiScaleUncertainty, ArithmeticOrientationTheory, ArithmeticCompensationTheory | 1 each |

| Used by | Modules |
|---|---|
| ArithmeticPolarization | 6 (height-coupled contractions, isometries, escape rank) |
| ArithmeticElectrostatics | 5 (source field, $(\zeta'/\zeta)^2$, real reciprocal field) |
| RenormalizedBiarithmeticGeometry | 4 imports in 3 modules (quadratic terminals, outward rays) |
| BiarithmeticGaugeGeometry | 2 (height-coupled systems, kernel counts) |
| ArithmeticEffectivityTheory | 2 (kernel counts, base as fixed loss) |
| SelectivePositivityAndThresholdLaws | 2 (budget sufficiency, receiver energy at Θ) |
| SelectiveMultiscaleArithmeticPositivity | 1 (worst twin) |
| MainTheorems | umbrella |

| Neighbour | Relation |
|---|---|
| ArithmeticCastelnuovoSeveri, ArithmeticOrientationGeometry | supply the scaling surface and correspondence ring; ACP measures which Weil layers they carry |
| ArithmeticPositiveDuality | rigidity/capacity on $\mathbb Q_{>0}$; ACP shows dilation-invariant PD cannot carry escape-state phases |
| ArithmeticCorrelationGeometry, ArithmeticKunnethTheory | gauge torus and products: amplification loses linearly; ACP adds family averages and the base |
| StripBochnerWeilForcing, MultiplicativePositivityGeometry | completed positive systems; ACP contracts their off-line zeros at computed pole tax |
| ArithmeticDefectRigidity, ArithmeticContinuationAndCriticalEnergy, TransHorizonIncidenceMechanics | cofactor rows and damped receiver; ACP gives their Laplace/Abel spectral theory |
| BiScaleUncertainty | RH mean-square band converts to a prime-error budget |
| ArithmeticElectrostatics, RenormalizedBiarithmeticGeometry | continue the source field and quadratic terminals |

## 10. Big picture

Weil's proof over $\mathbb F_q$ factors into layers, and ACP locates each over $\mathbb Z$. The identities, graphs and
the budget all exist and are free: fake curves satisfy them. Every correspondence $\mathbb Z$ owns has a local type at an
off-line pair: multiplicative ones are hyperbolic exactly there, so their positivity ends in blindness or isotropy;
the successor is unipotent and invisible; affine maps have genus zero. Each quantitative input that would suffice
(section counts, one-sided prime counts, a fixed tensor loss, spectral positivity of symmetric squares) turns out to
be RH itself. The sign is not hidden in a missing layer; it is the one layer, Rosati sufficiency, that no existing
correspondence carries.

The second half replaces positivity by bookkeeping of energy. Rows of arithmetic have symbols whose poles sit at the
zeros; energy budgets pay residues, and Abel escape is read pole by pole without contour shifts. This yields the
$\mathbb Z$-analogue of $2g$: the archimedean genus $2+\gamma-\log4\pi$, which the prime error's energy slope always
exceeds and equals exactly under RH with simple zeros, as a curve's slope equals $2g$ exactly for a pure simple
spectrum. The research lesson is that an RH proof along these lines needs an unconditional upper bound for a
quantity whose lower bound and conditional limit are now known; the difficulty concentrates in mass at infinite
height, not in finite windows.
