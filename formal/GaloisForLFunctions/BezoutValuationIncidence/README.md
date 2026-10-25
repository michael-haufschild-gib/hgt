# Bézout–Valuation Incidence (BVI)

BVI studies divisor rows $c(1),\dots,c(N)$, their signals $s_{N,c}(k)=\sum_{d\le N,\,d\mid k}c(d)$
and prefix discrepancies on **polynomial-length windows**, where the period
$\operatorname{lcm}(1..N)=e^{\psi(N)}$ is unreachable. Consecutive coprimality (Bézout),
prime-power moduli (valuation) and divisibility (incidence) force signed cancellations without
period averaging. BVI isolates the single finite inequality still needed for RH. All results are
unconditional; RH appears only as the conclusion of one explicit finite inequality or in an
equivalence.

Namespace `GaloisForLFunctions.BezoutValuationIncidence`; umbrella `BezoutValuationIncidence.lean`;
flat folder.

---

## 1. Place in the research

BVI is the **finite arithmetic and pronic Gram calculus** of the RH research. Three bridges
locate the needed estimate:

- divisor rows → Selberg/Ramanujan coordinates: diagonal period forms, sharp observation horizons;
- prefix discrepancy → pronic energy: the reciprocal-cell Nyman–Beurling norm with its von
  Mangoldt readout;
- off-diagonal Gram → single-modulus residue statistics of the actual Möbius or centred prime row.

Recovery and period orthogonality never replace a signed estimate for a growing row.

| Neighbour | Interface |
|---|---|
| [TransHorizonIncidenceMechanics](../TransHorizonIncidenceMechanics/README.md) | Uses BVI window laws; classifies observers, parity pairs, receiver symmetries |
| [BiScaleUncertainty](../BiScaleUncertainty/README.md) | Full-period moment recovery; BVI supplies the window length to use it |
| [ArithmeticContinuationAndCriticalEnergy](../ArithmeticContinuationAndCriticalEnergy/README.md) | Reads BVI's damping derivative as signed work |
| [ArithmeticCompensationTheory](../ArithmeticCompensationTheory/README.md) | Boundary flux / jump-energy cancellation; Guth–Maynard window transfer |
| [SignedArithmeticEnergyIncidence](../SignedArithmeticEnergyIncidence/README.md) | Damping-chain receiver coordinates; generator; Hilbert–Schmidt bounds |
| [ArithmeticIncidencePositivity](../ArithmeticIncidencePositivity/README.md) | Continuous pair-conductance destination |
| [ArithmeticCriticalityTheory](../ArithmeticCriticalityTheory/README.md), [arithmetic-positivity-theory](../arithmetic-positivity-theory/README.md), [SquareRootThreshold](../SquareRootThreshold/README.md) | Aperture/source/lag coordinates of the destination |
| [ScaleSignedIncidenceCriticality](../ScaleSignedIncidenceCriticality/README.md) | Prices loss from period averages and magnitudes |
| [ArithmeticCastelnuovoSeveri](../ArithmeticCastelnuovoSeveri/README.md) | Whether finite arithmetic yields effectivity |
| [ArithmeticOrientationTheory](../ArithmeticOrientationTheory/README.md) | Pronic Báez–Duarte unit of the width dictionary; damping transports residue-mode signs exactly |
| [SignedSuccessorArithmetic](../SignedSuccessorArithmetic/README.md) | Successor defects recover signs that Selberg forms erase |
| [ArithmeticDefectRigidity](../ArithmeticDefectRigidity/README.md) | Cofactor identities; escape of normalized energy |
| [TransThresholdPairCorrelation](../TransThresholdPairCorrelation/README.md) | Other place where signed prime statistics beyond the large sieve are needed |

Route consumers: PM (cofactor-row damping laws), MC (fixed-modulus/window cancellation),
CTF (von Mangoldt readout, centred pronic residual).

---

## 2. Why

**Regime.** $s_{N,c}(k)=\sum_{q\le N}Y_{N,c}(q)c_q(k)$ with Selberg coordinates
$Y_{N,c}(q)=\sum_{q\mid d\le N}c(d)/d$; Ramanujan sums are orthogonal over a full period. Every
prime question instead asks about windows $M\le N^A$, where three things fail:
(1) *drift mixes with incidence*: $L_N(M,c)=-\sum_dc(d)\{M/d\}$ gets drift $-Mc(d)/d$ from every
$d>M$ before any divisibility event; (2) *shift and cutoff do not commute*; (3) *lags and depths
couple* through exact finite factorizations.

**The three words.** *Bézout*: $\gcd(n,n+1)=1$ — divisors of $n$ and $n+1$ are coprime,
$\Lambda(n(n+1))=0$, least seeds of $pa-qb=1$ govern event gaps. None of this holds in a Beurling
system, which satisfies every multiplicative identity yet may have off-line zeros: **a mechanism
that sees RH must use Bézout structure.** *Valuation*: what a lag sees of mode $q$ is decided by
$q/\operatorname{rad}q\mid h$. *Incidence*: the 0–1 matrix $\mathbf1_{d\mid n}$ and its sawtooth
geometry; every quantity is a bilinear form in the row against it.

**The receiver.** With $\tau_\varepsilon(n)=\prod_{p\mid n}(1-p^{-\varepsilon})$,
$\alpha_\varepsilon=1/\zeta(1+\varepsilon)$, $A_\varepsilon(n)=\sum_{j\le n}(\tau_\varepsilon(j)-\alpha_\varepsilon)$,
$$E_T(\varepsilon)=\sum_{n\le T}\frac{A_\varepsilon(n)^2}{n(n+1)} .$$
If $\forall\delta\,\exists\varepsilon\in(0,\delta)$ with $\sup_TE_T(\varepsilon)<\infty$, then RH. Known for
$\varepsilon\ge\tfrac12$, unknown for every $\varepsilon<\tfrac12$. An isolated admitted damping gives only
zero translation; width conclusions need accumulation of admitted dampings.

---

## 3. Objects and language

**Coordinates of a row.** Raw weights $c(d)$; responses $s_{N,c}$ (`sieveSeq`); Selberg $Y_{N,c}$
(`selbergMultiplesCoord`); spectral form $s=\sum_{\zeta\in T_N}Y(\operatorname{ord}\zeta)\zeta^k$ over
roots of unity of order $\le N$ ($1/N^2$-separated, Galois-invariant coefficients); Witt ghost
coordinates $g_w(q)$ with $\|c_w\|^2=\sum\varphi(q)g_w(q)^2$ — Frobenius $F_2$ reads $g_w(2q)$ (consumes
cutoff $2N$), Verschiebung $V_m$ dilates onto multiples of $m$. Harmonic mode $Y(1)=\mathcal H_N(c)$;
$\ker P$ = harmonic-free rows. Finite Ramanujan inversion realises any $Y$ on $[1,N]$.

**Möbius bands.** $s_{N,\mu}=\mathbf1_{k=1}$ below $N$; $-\mu(k)$ on $(N,2N]$; at most $B$ complementary
quotients on $k\le(B+1)N$. States: multiplicative $\operatorname{lcm}\{d\le N:d\mid k\}$, radical $\gcd(k,N\#)$.

**Horizons for windows** (arbitrary phase $A$): period $L_N$; cyclotomic $\Phi(N)=\sum_{q\le N}\varphi(q)$;
quadratic $N^{2\pm o(1)}$ (mean-square transfer); degree-$m$ $N^{m\pm o(1)}$.

**Sawtooth and interior.** $\tilde B_1(d,n)=\{n/d\}-\frac{d-1}{2d}$; the weighted sum $W_{N,c}$ is the
canonical primitive of the centred response. Across $n\mapsto n+1$ moduli are active at $n$,
active at $n+1$, or **interior**; by Bézout none is active at both. Interior prefix $I_\varepsilon$;
interior energy $E^{\text{int}}_T(\varepsilon)$.

**Quadratic forms** (all diagonal in Selberg coordinates, modal weight at $e\ge2$): variance
$\varphi(e)$; successor covariance $\mu(e)$; reserve $\varphi-\mu$; primitive energy $J_2(e)/12$;
lag-$h$ covariance $c_e(h)$; tuple variance = structure factor $S_e(H)$. $\mu$ separates 4 from 6
where $\varphi$ does not. Translated moments = sums over zero-product tuples of relation
coefficients $\prod Y(\operatorname{ord}\zeta_i)$.

**Pronic measure** $w(M)=1/(M(M+1))$ replaces period averaging. Ramanujan primitive $R_e(M)$;
$\sum_MR_e(M)w(M)=-\Lambda(e)$; von Mangoldt readout $\mathcal R(c)=\sum_e\Lambda(e)Y(e)$. Pronic Gram
$\mathcal G=\Lambda\Lambda^\top+\mathcal G^{\text{ec}}$ (energy-centred, PSD), mean-centred $\mathcal G^{\text{mc}}$;
cotangent–sawtooth form $C(p,q)$; Vasyunin sums $V(h,k)$; Báez–Duarte residual.

**Damped source and chain.** Row $c_\varepsilon=\mu(d)d^{-\varepsilon}$; cofactor row $w_{\varepsilon,Q}$;
stochastic Cesàro kernel $P_\eta$ with semigroup law and entrance law
$e_\eta(k)=\rho_\eta k(k^{-1-\eta}-(k+1)^{-1-\eta})$; Fermi–Nyman cells $(1/(n+1),1/n]$ carry pronic mass.

**Cross-scale objects.** Bilinear form $B(c,c')$ between small (moduli $\sim P$) and large ($\sim Q$)
rows; residue potential $\Phi_d$; Bernoulli kernel $\mathfrak B(d,n)$ and cubic kernel; kernel
statistic $\Lambda_d(c')$; dual norm $\sum_{d\in S}|\Lambda_d(c')|/d$; cross-scale exponent
$\theta=2\log P/\log Q$ (receiver at $\theta=2$). Type II: arbitrary bounded small coefficients;
Type I: flat/smooth large rows.

**Vaughan objects.** Five pieces of Vaughan's identity at cutoffs $U,V$; 25-entry pronic Gram
$G_{ij}$; diagonal $D_T$; mixed remainder $R^{\text{mix}}_T$; $E^{\text{int}}_T=D_T+R^{\text{mix}}_T$.

---

## 4. Mechanisms

1. **Bézout splitting.** Divisor pairs of $(k,k+1)$ ↔ divisors of $k(k+1)$; coprime products are
   never prime powers; pronic multiplicativity $\tau_\varepsilon(k)\tau_\varepsilon(k+1)=\tau_\varepsilon(k(k+1))$;
   2-adic ceiling $1-2^{-\varepsilon}$. Mixed differences annihilate $\log$ at two-prime nodes.
2. **Simultaneous diagonalization and finite cones.** $2\mu(e)\le\varphi(e)$ (equality only at 6) ⇒
   $-V\le C\le V/2$; feasible regions are polyhedral; for every lag horizon the covariance cone is
   finitely generated by explicit modes. Bound modal weights arithmetically, find the tight modes,
   realise them by Ramanujan inversion.
3. **Polarization and renormalization.**
   $2R_N(M)=-\sum(\Delta s)^2+s(M+1)^2-s(1)^2$; renormalization is forced (raw Möbius defect is not
   $O(N^\alpha)$, $\alpha<1$). Short windows: defect $\le0$ for all rows iff endpoint states agree.
4. **Observability.** Cyclotomic recurrence $Q_N(E)s=0$ of order $\Phi(N)$ ⇒ $\Phi(N)$ consecutive
   values determine a row at every phase; **no linear horizon** (alternating grids vanish on $mN$
   consecutive integers); window sandwich constant of exact order $N^2$ (MV constant $N(N-1)$);
   window Poincaré and long-window dissipation $2R_W\le4H^2-(K-10N^2)V$; degree-$m$ moments transfer
   at $N^{m\pm o(1)}$; lag spectrum readout from one window.
5. **Visibility and the companion.** Compressed translation has eigenvalues $\lambda_q(h)$; lags do
   not compose; sign visibility is a valuation (layer) law; relation spectra in degrees 5 and 6
   determine a row up to the half-period companion — the top dyadic layer is the whole kernel.
6. **Pronic Gram calculus.** $\mathcal G^{\text{mc}}(p,q)=C(p,q)$, a finite cotangent–sawtooth sum
   (Hecke distribution collapses it to Vasyunin sums); $\mathcal G^{\text{ec}}$ strictly PD on every
   finite modulus set; Vasyunin reciprocity with exact-order defect; prime-dilation laws;
   hypercube factorization (finite form of $\zeta(1+\varepsilon)\zeta(1+\varepsilon)^{-1}=1$, coherent
   across depths only).
7. **Reciprocity kernel = Ramanujan + Kloosterman.** $\mathfrak B(p,\cdot)-m_p$ splits into $c_p(n)$
   times a constant plus a zero-mean Kloosterman cosine series $\sum C_m(p)\cos(2\pi m\bar n/p)$ with
   Weil bound $|C_m(p)|\le\frac{\pi^2}{24}p^{3/2}$, **order-sharp** (no sub-Weil saving at one prime);
   the prime Gram is rank three + $W_K(p,q)/q$; CRT orthogonality reduces two-prime correlations to a
   terminal block; the Wiener norm of the linear spectrum is $\le\frac{\pi^2}{36}p^2$ (no $\sqrt p$ loss).
8. **Báez–Duarte in pronic coordinates.** Residual $=(1-\mathcal R)^2+Q^{\text{ec}}$; rescaling gives
   minimum $1/(1+\mathcal R^2/Q^{\text{ec}})$; unconditional floor $\kappa/\log N$ (critical zeros via
   the dual sequence). Dual residual and $E_T$ differ by $\le1$ in square root.
9. **Sawtooth martingale calculus.** Pronic Abel summation; active-deleted identity
   $E_T=D^{\text{act}}+2P^{\text{pred}}+2M^{\text{int}}$; after canonical drift compensation the first two
   are bounded: **the whole obligation is the interior martingale** (cancellation slope $\ge7/24$).
   Summation by parts gives a conservation law, never a contraction. Signed interior jump-orbit
   means collapse to Selberg coordinates on divisors of the jump modulus.
10. **Vaughan calibration.** $E^{\text{int}}=\sum G_{ij}$; diagonal sign-blind; linear pole mass
    $G_{44}/T\to\rho^2$ ⇒ $R^{\text{mix}}/D\to-1$ unconditionally; bounded energy ⇔
    $|1+R^{\text{mix}}/D|=O(1/T)$; leading matrix $\rho^2vv^\top$ uniformly over moving cutoffs; second
    scale $T^{1-2\varepsilon}$ with rank-one smooth term $ss^\top$, $s=(0,0,-1,1,0)$; every logarithmic
    saving uniform in cutoffs; amplitudes $H_U^2H_V^2$ and the normalized subcritical matrix-limit
    family are compact, countably infinite, with zero the unique accumulation point and no damping
    dependence; at positive cutoffs below half damping, the admitted coefficient space has dimension
    2 (3 iff the receiver is paid); the absolute
    remainder budget has exact power $N^{2-4\varepsilon}$; reciprocal-tail power gains = fixed strips.
    Finite harmonic nonvanishing has explicit separation $|H_N|\ge1/N!$ for $N\ge1$:
    [denominator bounds](../RHTower/FiniteMobiusHarmonicSumsHaveExplicitLowerBounds.lean).
    Every positive cutoff schedule admits divergent horizons with a nonzero rank-one
    [relative Gram limit](../../../docs/drafts/pipeline/3-formalized/vaughan-relative-gram-and-harmonic-denominators.md)
    after division by its actual harmonic amplitude; the error costs $(U!V!)^2$.
    The [complete subcritical classification](../../../docs/drafts/pipeline/3-formalized/vaughan-subcritical-gram-limit-classification.md)
    includes exact ranks, attainment, topology, and normalized damping independence.
    The [single-floor specialization](UniformLogarithmicCancellationInMobiusFloorSums.lean)
    has every logarithmic saving uniformly in its cutoff, with an exact omitted-tail identity.
    A [critical pairing bound](UniformCriticalPronicPairingsFromLogarithmicCancellation.lean)
    converts two logarithms of square-root prefix cancellation into one summable energy
    and absolute mixed-pairing envelope.
    All five [actual smooth remainders](UniformLogarithmicPrefixRemaindersInAllVaughanRows.lean)
    satisfy common logarithmic prefix bounds through half damping and a uniform linear head bound.
    At half damping, the [harmonic Gram error](UniformHarmonicVaughanGramsAtHalfDamping.lean)
    is bounded uniformly in both cutoffs and the horizon, using one summable remainder envelope.
    The [endpoint packet law](UniformHarmonicEnergyLawsForVaughanSuperpositions.lean)
    has error `C(Σ|w_i|)²`; a zero smooth coefficient gives uniform finite energy.
    [Positive floor majorants](PositiveFloorMajorantsControlPronicEnergy.lean)
    control centered prefixes; a common summable square envelope gives full pronic convergence.
    [Half-damping admission](VaughanAdmissionAtHalfDamping.lean) removes both linear
    and smooth means; positive cutoffs have admitted dimension three and quotient dimension two.
    [Above half damping](VaughanAdmissionAboveHalfDamping.lean), one bound controls
    every centered piece; admission is the linear-mean kernel, of dimension four for all cutoffs.
    [An empty cutoff](TheZeroCutoffVaughanCoefficientSpace.lean) adds an unused coordinate:
    dimension three or four according to receiver admission, and four unconditionally at half damping.
    The [extra-rank damping set](TheVaughanAdmissionRankReadsTheZeroAbscissa.lean)
    equals the receiver damping set for every cutoff pair; its lower accumulation
    boundary is exactly `zetaZeroAbscissa-1/2`. It also detects first/all damping-column summability.
    The [centered pole](TheCentredVaughanPoleHasPositiveFiniteEnergy.lean) has
    a cutoff-independent energy limit between `2^(-2ε)/32` and `1/4` for `ε≥0`;
    its normalized energy admits no eventual power exponent above `1-2ε`.
    [Two arithmetic cells](TheVaughanLimitRowsAreIndependentInTwoCells.lean)
    separate the actual prefix and pole at every positive damping, with
    determinant at least `2^(-2ε)/36`; their finite pronic Gram determinant is
    at least `2^(-4ε)/15552` for horizons containing both cells.
    [Divergent cutoffs](MovingVaughanRowsConvergeCellByCell.lean) recover
    `(A,A,-A,0,P)` cellwise in both centered and smooth-subtracted rows for every `ε>0`.
    [Dominated moving sums](../HTGeometry/MovingTruncationsPreserveDominatedLimits.lean)
    permit independently divergent horizons under a common summable envelope.
    The [uniform stretched-exponential estimate](UniformStretchedExponentialCancellationInTheVaughanConvolution.lean)
    gives a `(3q)!` logarithmic envelope with one threshold for all orders and cutoffs.
11. **Dilation profiles and the Bézout seed.** $\Phi_r(p/q)$ = pairing of jump streams of $pr,qr$;
    least seed isolated; dyadic windows reduce consecutive divisor edges to the single pair $(2,3)$.
12. **Literal Möbius on linear windows.** Uniform first-moment cancellation; finite Euler-product
    profile $P(B)$; cofinal slope $\kappa\approx0.4408$ = period variance = **one-line energy of
    $1/\zeta$**, $\kappa\ge1/288$; transfer at every superlinear horizon; primitive energy linear;
    gradient coercivity ⇒ all-prefix defect sign at large cutoffs.
13. **Cross-scale dispersion.** Rank-two law up to $P/Q$; log-free large sieve $(N+Q^2-1)$; expansion
    to every order with rising-factorial pronic weights; **Type-II barrier** $Q\ge P^{5/3}$ sharp
    (coherent near-multiples); exact loss = $\ell^1$ residue discrepancy (parity-blind); dual norm =
    one linear statistic per small modulus; Type I gains one order per smoothness order,
    $\theta=2K/(K+1)$.
14. **Actual rows.** The prime row's fixed-modulus statistic is the omitted-class sieve term
    $\asymp p/Q$; Möbius is $o(1/Q)$. Short-window mean squares (Huxley; Guth–Maynard $17/30$) beat
    Type II and the large sieve qualitatively, including balanced $Q\asymp P$. Minor arcs below the
    diagonal: power saving $Q^{-\delta/4}$; on the diagonal only subpower.
15. **Balanced statistic = quasi-RH.** For both actual rows, a power saving of the dual-norm
    statistic on any neighbourhood $Q^{1\mp\varepsilon}$ of the diagonal ⇔ $\Theta<1$ (block chaining +
    near-origin kernel + Abel summation); below the diagonal the saving is unconditional. Likewise
    short-window power savings at a fixed exponent ⇔ $\Theta<1$.
16. **Rate transfer to zero-free bands.** Any Mertens rate $|S(x)|\le Lx$ gives
    $|A(n)|\le3D^{1-\varepsilon}+\frac{13}\varepsilon LnD^{-\varepsilon}$; VK ⇒ receiver bounded on
    $\varepsilon\ge\tfrac12-\kappa\sigma(T)/(480\log T)$; pointwise transfer loses half the width
    (admits only $\varepsilon>\Theta/2$). The band separates the parity pair and is selective against
    Beurling (wider than dlVP by VK's mean value theorem).
17. **Damping chain operator calculus.** Centred operator compact on $c_0$, semigroup, spectrum
    $\{0\}\cup\{d^{-\eta}\}$, residue modes $v_d$ diagonalize; entrance tail non-square-summable for
    $\eta\le\tfrac12$ (absolute barrier only); size-bias $h$-transform makes the entrance functional
    pronic-bounded; admission ⇔ first/every column square-summable ⇔ Hilbert–Schmidt of the
    transformed chain; the residual has a linear cusp $\kappa\varepsilon$ from a critical zero.

---

## 5. Pillar theorems

1. Bézout splitting and prime-power indecomposability (module `PronicBezoutSplitAndPrimePowerIndecomposability.lean`).
2. Observability: $\Phi(N)$ at every phase, no linear horizon, sandwich order $N^2$, degree-$m$
   horizon, companion classification (`not_exists_linear_observability_horizon`,
   `windowSandwichConstant_exact_quadratic_order`, `translatedMomentTransferConstant_exact_order`,
   `sameRelationSpectrum_five_six_iff`).
3. Explicit pronic Gram (`pmRamanujanMeanCenteredGram_eq_cotangent_sawtooth`,
   `sum_sum_mul_vasyuninPrimeKernel_pos_iff`, `residueDifferenceEnergy_ge`).
4. Báez–Duarte in rows (`riemannHypothesis_iff_pronic_prefix_energy`,
   `riemannHypothesis_iff_readout_energy_ratio_unbounded`, `exists_readout_energy_uncertainty`).
5. Energy is one signed term (`exists_pmBezoutInterior_compensated_energy_bound`,
   `pmInterior_strict_contraction_iff_bounded_energy`, `mem_receiverDampings_iff_all_interior_forms`).
6. Cross-scale law, sharp Type-II barrier, exact loss (`exists_readout_free_barrier`,
   `abs_rowBilinear_add_mean_add_beta_sub_equidistributed_le`).
7. Kloosterman structure of the prime Gram (`abs_pmRamanujanEnergyCenteredGram_sub_rankThree_kloosterman_le`,
   `exists_abs_reciprocityKloostermanCoeff_ge`).
8. Balanced statistic and short windows are quasi-RH (`balancedStatisticPowerSaving_iff`,
   `centredPrimeBandPowerSaving_iff`, `moebiusPowerWindowSaving_iff`,
   `abs_kernelStatisticAll_moebius_and_centredPrime_le_rpow`).
9. Receiver on zero-free bands, selective (`exists_receiver_le_on_vinogradovKorobovBand`,
   `parityPair_separated_on_vinogradovKorobovBand`, `receiverDampingRate_sandwich`).
10. Cofinal slope = one-line energy of $1/\zeta$ (`cofinalMobiusSlope_eq_integral_eulerProduct`).
11. Vaughan leading matrix and admitted packets (`tendsto_pmPronicVaughanGram_div_moving`,
    `bounded_pmInteriorPronicEnergy_iff_reciprocal_vaughan_relative_error`, `pmPronicVaughanPacketAdmitted_iff`).
12. Damping chain (`isCompactOperator_arithmeticDampingCenteredOperator`,
    `mem_spectrum_arithmeticDampingCenteredOperator_iff`, `mem_receiverDampings_iff_hTransformed_hilbertSchmidt`,
    `exists_criticalZero_linear_dualResidual_floor`).
13. Complete-period quadratic data are exactly sign-blind (`periodCovariance_eq_iff_exists_scaledSelbergRow`).

---

## 6. Traps

| Trap | Correct statement |
|---|---|
| Pronic reach is cancellation | A modulus $d>M$ contributes only drift |
| Observability needs a period | $\Phi(N)$ values suffice at every phase; but no linear horizon exists |
| Degree-$m$ statistics transfer at $N^2$ | Horizon is $N^{m\pm o(1)}$ |
| Compressed lags form a semigroup | They do not; sub-clock lags revive modes |
| More moment degrees narrow the ambiguity | Degrees 5–6 close the hierarchy; residual = companion |
| Raw Möbius defect is small | Only the renormalized defect is bounded |
| Multiplicative identities can close it | Beurling systems satisfy them all |
| Fixed-depth cancellation | Möbius sign constant on a prime star; cancellation is cross-depth only |
| The three Grams are interchangeable | They differ by rank-one terms; PD holds for $\mathcal G^{\text{ec}}$ |
| Damped Báez–Duarte residual $o(\varepsilon)$ | Linear cusp $\kappa\varepsilon$ from a critical zero |
| Total variation controls the receiver | Entrance tail non-square-summable at $\eta\le\tfrac12$ |
| Compactness on $c_0$ bounds the energy | The receiver is pronic $\ell^2$ |
| Small readout defect or small energy alone | Coupled by the $\kappa/\log N$ floor |
| Summation by parts is an estimate | Returns $E_T$ with coefficient 1 |
| Changing the compensated kernel is harmless | It changes the target |
| Absolute values early | Signed sums over moduli must be kept |
| Far scales decouple | Only for $Q\ge P^{5/3}$ with arbitrary coefficients |
| The cross-scale form breaks parity | It sees only residue masses + two readouts |
| Flat/smooth rows model primes | Möbius and prime rows are not smooth at any order |
| A sub-Weil saving at one prime | The Weil bound on $C_m(p)$ is order-sharp |
| A power saving at the diagonal is weaker than a strip | It *is* $\Theta<1$, for both rows |
| A Mertens rate bounds the receiver at fixed $\varepsilon<\tfrac12$ | Only on a horizon-dependent band |
| Pointwise prefix bounds suffice | They lose half the width; estimate in mean square |
| Prime-row statistics are small | The omitted residue class gives $\asymp p/Q$ |
| Witt Frobenius is free at fixed horizon | It consumes cutoff $2N$ |
| Relative Vaughan cancellation is progress | $R^{\text{mix}}/D\to-1$ is unconditional; the error is $E^{\text{int}}$ itself |

---

## 7. Open problems

1. **The receiver.** One fixed $\varepsilon<\tfrac12$ with $\sup_TE_T(\varepsilon)<\infty$. Equivalent
   at fixed $\varepsilon$: bounded interior energy, bounded compensated bracket, strict interior
   contraction, square-summable chain columns, bounded dual residual. Unconditional size = zero-free
   region ($T^{1-2\varepsilon}e^{-\kappa\sigma(T)/270}$).
2. **Interior martingale contraction.** $2M^{\text{int}}+2\,\mathrm{Counterterm}\,H^{\text{comp}}\le(1-\delta)E_T+C_\varepsilon$
   at one fixed $\varepsilon<\tfrac12$; must come from the signed sum over moduli, equivalently the
   mixed Vaughan entries $G_{ij}$, $i\ne j$ (rate requirement $|1+R^{\text{mix}}/D|=O(1/T)$).
3. **Dual construction.** Rows with $\mathcal R^2/Q^{\text{ec}}\to\infty$ within the ceiling
   $(\log N-\kappa)/\kappa$; sharp attainable rate; arithmetic cofactor constructions.
4. **Balanced dispersion beyond quasi-RH.** Any power saving at the diagonal is exactly $\Theta<1$,
   and the receiver needs more than a strip. Which subpower or structured (Kloosterman-reciprocity)
   gain at $Q\asymp P$ sums into the receiver? Single-prime Weil is sharp, so gains must come from
   averaging over moduli or the CRT terminal block.
5. **Cross-depth cancellation.** Hypercube Dirichlet form uniform in $P$ for $0<\varepsilon\le\tfrac12$
   (proved for $\varepsilon>\tfrac12$); sign of the clock-successor signed complement.
6. **Damping chain.** Forward $\ell^2$ boundedness of the centred chain at one fixed $\eta<\tfrac12$
   (must read Möbius signs).
7. **Observation constants.** Exact growth of $L_{\text{obs}}(N)$ between linear and quadratic; exact
   $S_{\text{opt}}(N)/N^2$.
8. **Topics.** Single-modulus statistics at growing moduli via reciprocity without external
   averages; Bézout-selective identities for mixed Vaughan entries; additive edge reductions beyond
   dyadic windows; a finite, cutoff-quantitative statistic separating the parity pair below the band;
   whether the Witt ring structure yields a bound the Selberg coordinates do not.

---

## 8. Tools

Built: Bézout splitting; Selberg/Ramanujan diagonalization and finite cones; polarization and
renormalization; cyclotomic recurrence and log-free window laws; visibility/companion
classification; pronic Gram calculus (cotangent–sawtooth, Vasyunin reciprocity, dilation and
hypercube laws, Kloosterman decomposition); pronic Báez–Duarte dictionary; sawtooth martingale
calculus; Vaughan Gram calculus (leading matrices, second scale, admitted packets, limit-family
topology); cross-scale calculus to every order; log-free large sieve with the MV constant; rate
transfer to zero-free bands; damping chain operator calculus.

To build: signed interior contraction; a receiver-strength balanced dispersion estimate beyond
quasi-RH; dual rows with vanishing readout defect and energy; a forward $\ell^2$ chain bound below ½.

---

## 9. Working conventions

- Name coordinates (raw/response/Selberg/spectral/ghost) and regime (period, prefix, octave, band,
  arbitrary-phase window; horizon $\Phi(N)$, $N^2$, $N^m$).
- Identity before asymptotics; keep boundary terms and signed defects; cancel with the diagonal
  main term before bounding.
- Test against Beurling: the additive input must be visible ($\gcd(n,n+1)=1$, $pa-qb=h$, an omitted
  residue class, a valuation layer).
- State what a bound does not prove (first moment ≠ square root; fixed $B$ ≠ uniform;
  $\varepsilon\ge\tfrac12$ ≠ below; floor ≠ rate).
- Capstones carry only arithmetic side conditions; window statements quantify over the phase;
  module headers say what their bounds do not prove.
