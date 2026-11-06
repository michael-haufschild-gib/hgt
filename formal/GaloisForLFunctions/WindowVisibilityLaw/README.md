# Window Visibility Law (`WindowVisibilityLaw`)

**Question.** Which off-line zeros can a window $[-a,a]$ see (`∃ f ∈ C²_c([-a,a]), \Re W_Z(f,f) < 0`), and which off-line zero configurations hide (`∀ f ∈ C²_c([-a,a]), \Re W_Z(f,f) \ge 0`)?

Primary namespace `GaloisForLFunctions.WindowVisibilityLaw`. Umbrella `WindowVisibilityLaw.lean`. 5 files.

---

## 1. Objects

| Object | Mathematical definition | Lean |
|---|---|---|
| Complex window positivity | $\forall f\in C^2_c([-a,a]),\ \Re W_Z(f,f)\ge 0$ | `WindowPositiveAt` |
| Onset aperture | $\sup\{a\in\mathbb{R} : a\ge 0 \land \mathrm{WindowPositiveAt}\ Z\ a\}\in\mathrm{EReal}$ | `onsetAperture` |
| Pair energy | $2\int_0^a \sinh^2(\delta u)\,du = \frac{\sinh(2\delta a)}{2\delta} - a$ | `pairEnergy` |
| Coherent cluster in RvM lattice | Multiplicity-$k$ off-line pair at $\tfrac12\pm\delta+i\gamma_0$ in $2\pi/L$ on-line lattice | `multiplicityPairConfig` |
| Modulated $C^2_c([-a,a])$ tilt test | $(a^2-u^2)_+^{5/2}\sinh(\delta u)e^{-i\gamma_0 u}$ | `sinhTestWeight`, `sinhTest`, `modulatedTest` |
| Finite biquadratic crystal packet | Smoothly tapered depth profile $\delta(1-(k-k_0)^2/M^2)^2$ on $\|k-k_0\|<M$ | `taperedSupport`, `biquadraticProfile` |
| Mixed $2g$-column configuration | $2g-2$ on-line columns + $2$ off-line columns at $\tfrac12\pm\delta$ of period $2\pi/\ell$ | `mixedGenusColumnConfig` |
| Single-defect off-line lattice | $2\pi/L$ off-line lattice with $k=0$ pair shifted to $\pm\delta+i\varepsilon$ | `singleDefectOffLineLattice` |
| Perturbed off-line lattice | $2\pi/L$ off-line lattice with $k$-th pair shifted by $\varepsilon_k$ ($\|\varepsilon_k\|\le \pi/(2L)$) | `perturbedOffLineLatticeConfig` |

---

## 2. Main Theorems

### A. Closed-interval onset law and $\zeta$ / `AHD` dictionary (`OnsetApertureAndPositivityDictionary.lean`)
1. **Closed-interval law.** Dilation left-continuity ($f_n(t)=f(r_n t)$, $r_n=1+1/(n+1)\downarrow 1$) closes the positive-aperture set on the right: for every tempered $Z$ and $a\ge 0$,
   - $\mathrm{WindowPositiveAt}\ Z\ a \iff (a:\mathrm{EReal})\le \mathrm{onsetAperture}\ Z$ (`windowPositiveAt_iff_le_onsetAperture`);
   - $\exists f\in C^2_c([-a,a]),\ \Re W_Z(f,f)<0 \iff \mathrm{onsetAperture}\ Z < (a:\mathrm{EReal})$ (`exists_re_W_neg_iff_onsetAperture_lt`);
   - $\mathrm{hodgeDefectAt}\ Z\ a = 0 \iff (a:\mathrm{EReal})\le \mathrm{onsetAperture}\ Z$ (`hodgeDefectAt_eq_zero_iff_le_onsetAperture`);
   - $\mathrm{onsetAperture}\ Z = \top \iff \forall \rho\in Z,\ \Re\rho=\tfrac12$ (`onsetAperture_eq_top_iff_onLine`).
2. **$\zeta$, `P1`, and `AHD` dictionary.**
   - $\mathrm{WindowPositiveAt}\ \mathrm{zetaZeroConfig}\ a \iff \mathrm{ZetaWindowPositive}\ a$ (`windowPositiveAt_zeta_iff`);
   - $\mathrm{RiemannHypothesis} \iff \mathrm{onsetAperture}\ \mathrm{zetaZeroConfig}=\top$ (`riemannHypothesis_iff_onsetAperture_zeta_eq_top`);
   - Under $\neg\mathrm{RH}$, $\mathrm{onsetAperture}\ \mathrm{zetaZeroConfig} = \mathrm{zetaContactAperture}$ and $\mathrm{ZetaWindowPositive}\ \mathrm{zetaContactAperture}$ holds at the contact endpoint (`onsetAperture_zeta_eq_contact_of_not_rh`, `zetaWindowPositive_contact_of_not_rh`);
   - Unconditionally, $\mathrm{enlargedWeilFloorAperture}\le\mathrm{onsetAperture}\ \mathrm{zetaZeroConfig}$ (`enlargedWeilFloorAperture_le_onsetAperture_zeta`);
   - For $A\ge 0$, $\mathrm{windowThreshold}\ A=\top \iff A/2\le\mathrm{onsetAperture}\ \mathrm{zetaZeroConfig}$ (`windowThreshold_eq_top_iff_le_onsetAperture`);
   - Closed-endpoint $1/R$ excluded-depth law on $\zeta$ for $R\le\mathrm{onsetAperture}\ \mathrm{zetaZeroConfig}$ (`zeta_abs_re_sub_half_lt_of_le_onsetAperture`).

### B. Coherent cluster amplification and $L^2$ tilt bounds (`CoherentClusterAndTiltAmplificationLaw.lean`)
1. **Exact criterion in $2\pi/L$ RvM background.** For $0<a\le L/2$,
   $\mathrm{WindowPositiveAt}\ (\mathrm{multiplicityPairConfig}\ k\ \dots)\ a \iff k\cdot\mathrm{pairEnergy}\ \delta\ a \le L$ (`windowPositiveAt_multiplicityPairConfig_iff`).
   - Deep logarithmic brackets: $2\delta a\le \log(4\delta L/k)\implies$ hides (`windowPositiveAt_multiplicityPairConfig_of_le_log`); $\log(4\delta(L/k+a)+2)\le 2\delta a\implies$ visible (`onsetAperture_multiplicityPairConfig_lt_of_log_le`).
   - Shallow cubic brackets: $\tfrac23 k\delta^2 a^3\cosh(2\delta a)\le L\implies$ hides (`windowPositiveAt_multiplicityPairConfig_of_cubic_le`); $L<\tfrac23 k\delta^2 a^3\implies$ visible (`onsetAperture_multiplicityPairConfig_lt_of_lt_cubic`).
2. **General unit-window RvM configurations ($N(t,t+1]\le A_0\log(|t|+3)$).**
   - Optimal $L^2$ tilt test `modulatedTest γ₀ (sinhTest a δ)` achieves $P^2/\|f\|_2^2 \ge \frac{e^{2\delta a}}{60\cdot 2^{26}\delta}$.
   - Collar-unshielded clusters of ordinate width $\le 1/(4a)$ and multiplicity sum $M_S$ satisfy exponential bounds up to doubly-exponential height (`windowPositiveAt_coherent_cluster_bound`, `windowPositiveAt_global_sea_cluster_bound`), with unconditional $\zeta$ specialization at `enlargedWeilFloorAperture` (`enlargedWeilFloor_excludes_zeta_coherent_cluster`).

### C. Shallow dichotomy and tapered crystal barrier (`ShallowClusterExclusionAndTaperedCrystalBarrier.lean`)
1. **Macroscopic log-height cancellation and `DCI`-admissible shallow visibility.**
   - Macroscopic cluster density $M_S\ge c_0\log(|\gamma_0|+3)$ cancels $\log|\gamma_0|$ completely (`macroscopic_coherent_cluster_cancels_log_height`).
   - For $L\le k\le 20L$, `multiplicityPairConfig` satisfies $2k\delta^2\le 40\delta^2 L$ globally (`DCI`-admissible), yet has $\mathrm{onsetAperture}<a$ whenever $\delta^2 a^3 > 3/2$ (`dci_admissible_coherent_cluster_visible_at_sub_depth`).
2. **Universal non-lattice shallow hiding law.** Over an $m_0$-multiplicity $2\pi/L$ on-line lattice ($0<a\le L/2$), any off-line set of depth $\le\sigma$ and unit-window depth-squared mass $\le W$ hides whenever $a^2(2a+2\pi)e^{2\pi}e^{2\sigma a}W\le m_0 L$ (`windowPositiveAt_of_onLineLattice_and_offLineDepthMass`).
3. **Single-exponential crystal barrier at $\delta=1/a$.** Smooth finite biquadratic packets of half-length $M$ satisfy $\mathrm{WindowPositiveAt}$ whenever $38 a L \delta^2 \cosh(2\delta a)\le M$ (`windowPositiveAt_biquadraticCrystal_of_le`). In particular, for $a\ge 2$ and $L\ge 4a$, a finite crystal packet shields an exact depth-$1/a$ zero at any ordinate $2\pi k_0/L$ (`exists_hidden_inv_aperture_zero_above_single_exp`).
4. **Doubly-exponential non-locality and logarithmic contact exclusion.** Fixed-aperture positivity constrains unshielded clusters to doubly-exponential height (`doubly_exponential_height_nonlocality`); logarithmic contact scaling $c\log T\le\mathrm{onsetAperture}\ \mathrm{zetaZeroConfig}$ forces power-saving cluster exclusion $M_S T^{2c(\delta-\sigma)}\lesssim \delta(\log T)^2$ (`contact_law_log_scale_cluster_bound`).

5. **Fixed depth hides at logarithmic aperture under a uniform count (`TheSineLocalizerOfATest`, `TheCutCrystalHidesFixedDepth`).** For every `0<δ≤½` and `T≥e³⁶⁰` there is a configuration with `N(t,t+1]≤2log(|t|+3)` at every height and finitely many off-line zeros, containing a zero of depth `δ` at ordinate `T`, window-positive at `a=(log T)/36` (`exists_hidden_fixed_depth_zero_at_logarithmic_aperture`). The crystal lattice is cut below height `e^L`. The floor is applied to `sinePower τ N f`, `τT=π/2`: on-line terms decrease, the zero of order `N` at height zero pays the removed points by the maximum principle (`norm_paperFT_sinePower_sq_le`), and the factor is near one on the packet.

### D. Split-column threshold and perturbed lattice fragility vs $\ell^1$ ridge (`SplitColumnThresholdAndPerturbedFragility.lean`)
1. **Split-column sign law.** One-sided right-half-plane isolation suffices (`exists_window_re_W_neg_of_one_side_isolation`), reducing each conjugate off-line column pair to one pole and yielding:
   - Sharp split-column threshold $a > \pi D_{\mathrm{on}} + \frac{\pi}{2} D_{\mathrm{off}}$ (`re_eq_half_of_re_W_nonneg_of_split_columns`);
   - Pure off-line column bound $\mathrm{onsetAperture}\le \frac{\pi}{2} D_{\mathrm{off}}$ (`onsetAperture_le_half_pi_density_of_all_offLine_columns`);
   - Improved $2g$-column curve threshold $(g-\tfrac12)\log q$ (`re_eq_half_of_re_W_nonneg_of_curve_columns_improved`);
   - Exact mixed-column onset $\mathrm{onsetAperture}(\mathrm{mixedGenusColumnConfig}\ \dots) = (g-\tfrac12)\ell > (g/2)\ell = \pi D/2$ for $g\ge 2$, refuting $\pi D/2$ for mixed columns (`onsetAperture_mixedGenusColumnConfig_eq`).
2. **Perturbed off-line column fragility vs $\ell^1$ ridge.**
   - Shifting the $k=0$ pair of `offLineLatticeConfig` by $\varepsilon\in(0,\pi/L]$ collapses $\mathrm{onsetAperture}$ below every $a\le L/2$ ($2\le\delta a$) with $960\cdot 2^{26}\delta L < \varepsilon^2 a^2 e^{2\delta a}$ (`onsetAperture_singleDefectOffLineLattice_lt`).
   - Conversely, $\ell^1$ perturbations satisfying $8 a^2 e^{2\delta a}\sum_k|\varepsilon_k|\le L$ preserve positivity at $a\le L/2$ (`windowPositiveAt_perturbedOffLineLatticeConfig`), giving exact equality $\mathrm{onsetAperture} = L/2$ on the exponentially thin ridge $2 L e^{\delta L}\sum_k|\varepsilon_k|\le 1$ (`onsetAperture_perturbedOffLineLatticeConfig_eq`).

### E. Sharp visibility constants (`TheSamplingInequalityAtAFreeWindow`, `TheUniversalVisibilityThreshold`, `TheTwoLobeTestHasAbsoluteConstants`)
1. **Universal threshold.** If the sea around an off-line site of multiplicity `k` has depth `≤σ` and at most `K` zeros per cell of length `2π/ℓ`, `ℓ>2a`, then window positivity at `a` forces `k·pairEnergy(δ,a)≤(K/2)ℓe^{2(2π/ℓ+σ)a}` (`pairEnergy_le_of_windowPositiveAt_of_cellCount`), so `e^{2δa}≤4δ(E/k+a)+1` with `E` the right side (`exp_two_mul_le_of_windowPositiveAt_of_cellCount`). At `K=2`, `ℓ=L`, `σ=0` this is the sharp `4δL/k` for every configuration as regular as a lattice.
2. **General counts.** Under `N(t,t+1]≤A₀log(|t|+3)`, a coherent cluster of depth `≥δ` in a sea of depth `≤σ≤δ` obeys `M_S e^{2(δ−σ)a}≤12000A₀log(|γ₀|+4·10⁸A₀log(|γ₀|+3)+6)` (`windowPositiveAt_cluster_absolute_bound`; for ζ, `zeta_cluster_absolute_bound`), with no dependence on `a` or `δ` on the right. The test is the pair of narrow bumps `w(u−c)−w(u+c)`, with transform `2i sin(cz)ŵ(z)`.

### F. Synthesis (`CompleteWindowVisibilitySynthesis.lean`)
Collects the complete answer in `window_visibility_closed_interval_law`, `zeta_and_ahd_onset_dictionary`, `onsetAperture_multiplicityPairConfig_mem_deep_interval`, `onsetAperture_multiplicityPairConfig_mem_cubic_interval`, `onsetAperture_perturbedOffLineLatticeConfig_eq`, `shallow_coherence_vs_nonlattice_hiding_dichotomy`, `aperture_height_duality_shielded_vs_unshielded`, `split_column_and_perturbed_lattice_dichotomy`, and `zeta_programme_consequences_of_window_visibility`.
