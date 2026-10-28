# Selective Positivity and Threshold Laws (SPTL)

Namespace `GaloisForLFunctions.SelectivePositivityAndThresholdLaws`; umbrella `SelectivePositivityAndThresholdLaws.lean`.

**Question.** What separates prime-blind positivity below the square-root and Nyquist horizons from *selective* arithmetic
positivity beyond them, and which exact obstructions govern parity-blind dispersion, unsigned torsion averaging and raw
continuum prime towers?

**The threshold picture.** Below the Nyquist threshold $\tfrac12\log2\approx0.3466$, $f\star\tilde f$ of a test in $[-A,A]$ vanishes at every
$\pm\log n$, so Weil positivity holds blindly for every weight $w$. Crossing it exposes prime atoms one at a time: on
$[-181/500,181/500]$ only $n=2$ is visible ($2\cdot181/500=0.724\in(\log2,\log3)$). At the global square-root threshold $X=T$
(large-sieve / mean-value diagonal) unsigned energies, parity-blind dispersion and unneutralized continuum towers hit sharp
obstructions. SPTL is the catalogue of exact boundary laws on six faces of this threshold, each paired with its selective
survivor.

---

## 1. Place in the research

| Programme | Interface |
|---|---|
| ArithmeticCriticalityTheory, ArithmeticIncidencePositivity | Odd window certificates to $181/500$, Schur lending; SPTL adds the even sector and selectivity |
| SquareRootThreshold | Window certificates, prime-weight blindness of radius-$R$ certificates |
| TransThresholdPairCorrelation, ArithmeticCorrelationGeometry | Coalescent surplus, Ramanujan stabilizers, gauge charge |
| BezoutValuationIncidence | Escaped Möbius pairing; cross-route quasi-RH unification |
| ArithmeticEffectivityTheory, ArithmeticCastelnuovoSeveri | Real-valued cohomology, theta log-volumes, golden datum |
| ArithmeticOrientationTheory | Continuum prime towers, tower rank-one law |
| ArithmeticCorrespondencePositivity, ArithmeticCorrelationGeometry | Escape Laplace symbol, visibility (gauge mass) |
| BiarithmeticGaugeGeometry | Catalan $\{2,3,4\}$ holonomy |

---

## 2. Objects and language

- Weighted Weil functional $\Re W_w(f\star\tilde f)$ with arbitrary prime weight $w$; battery weights: Liouville-twisted $\lambda\Lambda$,
  `flippedTwoVonMangoldt` ($w(2)=-\log2$), `shiftedPairVonMangoldt a` ($w(2)=(2^a+2^{-a})\log2$), scale twists $n^\sigma\Lambda(n)$, ordinate twists
  $\cos(\gamma\log n)\Lambda(n)$.
- `fullZeroForm`, `ccmRestrictedWeilGroundEnergy`, `liouvilleWindowGroundEigenvalue r`.
- Escaped Möbius pairing $\sum_{(N-b)/a<j\le N}\mu(j)/j$; `GrowingEndpointEscapedMoebiusLaw θ`, `DyadicEscapedMoebiusLaw θ`.
- Theta log-volumes `thetaBoxH0 w s`, `thetaBoxH1 w s`; polar-box cohomology `surfaceBoxH0`, `surfaceBoxH1`; box defect
  $E_w(s)=(e^s+s-1)-\sum_{k\le e^s}w(k)$.
- Jacobi–Hurwitz torsion packets $h_P$ with quadratic part $q_P$.
- Selberg parity weights $\Lambda\pm\lambda\Lambda$; Ramanujan stabilizer packets; escape Laplace symbol $G_\varepsilon(s)$.
- Continuum prime towers, edge bumps `edgeTowerBump A`, pole-neutralized odd subsurface.

---

## 3. Mechanisms

1. **Nyquist blindness / atom exposure**: autocorrelation support decides which prime atoms a window reads.
2. **Certified envelopes**: piecewise rational upper envelopes of the archimedean symbol + Legendre $LDL^\top$/Gershgorin
   factorization (even sector); Schur lending (odd sector).
3. **Smoothed spline witnesses** for refutation of twisted weights in the same window.
4. **Escaped pairing collapse** to a pure harmonic tail; adjacent multipliers isolate the unit cell.
5. **Real log-volumes instead of ranks** restore selectivity and Poisson–Serre duality.
6. **Jacobi–Hurwitz dichotomy**: a packet is bounded on $\ker(\cdot A)$ or inflates quadratically.
7. **Parity involution**: $\Lambda\pm\lambda\Lambda$ average to $\Lambda$ with pair correlations $0$ vs $4\log p\log p'$; a parity-blind bracket
   accumulates on the positive inner cosine lobe.
8. **Edge bumps**: continuum towers read off-lattice reflected crossings summing to $\le-c_0e^A$ (Chebyshev).

---

## 4. Pillar theorems

1. **Selective full-sector positivity past $\tfrac12\log2$**: $\Re W\ge\frac1{5000}\|f\|^2$ on $[-181/500,181/500]$ whenever $w(2)=\log2$; refuted for $w(2)=-\log2$
   (odd witness) and for shifted pairs (even witness) (`fullZeroForm_ge_of_support_le_threeHundredSixtyTwoThousandths`,
   `re_weilFullFunctional_ge_of_full_window_of_atom_two_eq`, `exists_odd_smooth_threeHundredSixtyTwoThousandths_zeta_pos_liouville_neg`,
   `threeHundredSixtyTwoThousandths_selectivity_battery`).
2. **Two-prime window $[-23/40,23/40]$**: Liouville ground eigenvalue $<-3/10$; archimedean-free Catalan separation of $\Lambda$ from scale,
   ordinate and Liouville twists (`liouvilleWindowGroundEigenvalue_twentyThreeFortieths_lt_neg_threeTenths`, `catalan_finite_gauge_separation`).
3. **Escaped Möbius boundary law**: growing-endpoint saving at $\theta\in(0,\tfrac12]$ ⇔ $\Theta\le1-\theta$ (⇔ RH at ½); impossible for $\theta>\tfrac12$; no
   uniform bound over all multipliers (`growingEndpointEscapedMoebiusLaw_tfae`, `not_dyadic_escapedPairing_rpow_of_half_lt`,
   `not_uniform_all_multipliers_escapedPairing_rpow`).
4. **Serre-dual real cohomology**: theta log-volumes satisfy RR = box defect, separate $\Lambda$ from shifted pairs; polar-box cohomology
   calibrates on curves and refutes RR on the golden datum; sub-large-sieve section growth ⇔ width $\le\sigma$; global Serre-dual
   asymptotic RR ⇔ RH (`thetaBox_riemannRoch_and_serreDuality`, `thetaBox_strict_selectivity_shiftedPair`,
   `sections_beyond_largeSieve_iff_zetaZeroWidth_le`, `serreDual_section_growth_iff_riemannHypothesis`).
5. **Jacobi–Hurwitz dichotomy and large-sieve inflation** $q_P(z)\ge\tfrac12|z\cdot z|$; short-cycle subquadratic heights exist for
   $r\le\tfrac12(\log2+1/50)$; a global bounded-below subquadratic height ⇔ RH (`jacobiHurwitzHeight_dichotomy`,
   `shortCycle_subquadratic_height_exists_primeTwo`, `riemannHypothesis_iff_exists_asymptotic_subquadratic_height`).
6. **Parity–lobe divergence**: every parity-blind dispersion bracket diverges for $\lambda>1$ and refutes the $4/3$ budget; the coalescent
   surplus decomposes over Ramanujan stabilizers (`parityBlind_dispersion_diverges_above_threshold`, `multiModulus_ramanujan_primeCoalSum_split`).
7. **Escape Laplace split**: $G_\varepsilon$ splits at simple zeros into a pole plus bounded remainder; positive gauge mass of all escape states ⇔
   RH (`escapeLaplaceSymbol_pole_and_visibility_laws`).
8. **Continuum tower obstruction vs pole-neutralized width law**: raw continuum towers diverge like $-c_0e^A$ on bounded dyadic-$H^1$
   tests; neutralizing the pole restores floor ⇔ width (`not_continuumPrimeTower_subexponential_dyadicH1`,
   `continuum_poleNeutralized_width_equivalence`).

---

## 5. Traps

| Trap | Truth |
|---|---|
| Window positivity below $\tfrac12\log2$ is about $\zeta$ | Holds for every weight: blind |
| Positivity past $\tfrac12\log2$ is selective in general | Only at the exposed atoms; it reads exactly $w(2)$ on $[-181/500,181/500]$ |
| Rank-based section counts separate weights | Ranks read support only; use log-volumes |
| A uniform escaped Möbius bound over all multipliers | False: adjacent multipliers isolate the unit cell |
| Escaped saving beyond $\theta=\tfrac12$ | Impossible |
| Parity-blind dispersion brackets reach the $4/3$ budget | Diverge on the inner lobe for every $\lambda>1$ |
| Lattice tower bounds transfer to the continuum | Edge bumps give $-c_0e^A$; the pole must be neutralized |
| Large-sieve majorants give subquadratic heights | They force quadratic inflation $\ge\tfrac12|z\cdot z|$ |

---

## 6. Open problems

1. **Windows past $\log3/2$**: selective positivity reading both $w(2)$ and $w(3)$ (beyond $23/40$ the Liouville twin already fails;
   positivity of $\zeta$ itself there is open), including the edge-concentrated tests of the $181/500$ window.
2. **Signed dispersion beyond the threshold**: a parity-sensitive bracket for the coalescent surplus (the stabilizer discrepancy).
3. **Escaped Möbius saving at some $\theta>0$** at the growing endpoint (= zero-free strip).
4. **Subquadratic heights on longer short-cycle subsurfaces** than $r\le\tfrac12(\log2+1/50)$.
5. **Pole-neutralized continuum tower bounds** below rate ½.

## 7. Tools to build

Certified envelope + factorization pipeline for longer windows; parity-sensitive dispersion brackets; selective log-volume
cohomology on the scaling surface beyond the box.

## 8. Contribution standard

Every positivity statement names the exposed atoms and the weights it holds for (blind vs selective) and is paired with
refutation witnesses on the battery ($\lambda\Lambda$, flipped-two, shifted pairs, scale/ordinate twists, golden datum). Every obstruction
states its positive survivor.
