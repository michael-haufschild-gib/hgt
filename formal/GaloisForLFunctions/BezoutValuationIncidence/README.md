# Bézout–Valuation Incidence (BVI)

Namespace `GaloisForLFunctions.BezoutValuationIncidence`; umbrella `BezoutValuationIncidence.lean`;
flat folder.

**Question.** Divisor rows $c(1),\dots,c(N)$, their signals $s_{N,c}(k)=\sum_{d\le N,\,d\mid k}c(d)$ and
prefix discrepancies on **polynomial-length windows**, where the period $\operatorname{lcm}(1..N)=e^{\psi(N)}$
is unreachable. Consecutive coprimality (Bézout), prime-power moduli (valuation) and divisibility
(incidence) force signed cancellations without period averaging. BVI isolates the single finite
inequality still needed for RH. RH appears only as the conclusion of an explicit inequality or in
an equivalence.

---

## 1. Place in the research

BVI is the **finite arithmetic and pronic Gram calculus** of the research. Three bridges locate
the needed estimate:

- divisor rows → Selberg/Ramanujan coordinates: diagonal period forms, sharp observation horizons;
- prefix discrepancy → pronic energy: the reciprocal-cell Nyman–Beurling norm with its von
  Mangoldt readout;
- off-diagonal Gram → single-modulus residue statistics of the actual Möbius or centred prime row.

Recovery and period orthogonality never replace a signed estimate for a growing row.

| Neighbour | Interface |
|---|---|
| TransHorizonIncidenceMechanics | Uses BVI window laws; observers, parity pairs, receiver symmetries |
| BiScaleUncertainty | Full-period moment recovery; BVI supplies the window length |
| ArithmeticContinuationAndCriticalEnergy | Reads the damping derivative as signed work |
| ArithmeticCompensationTheory | Boundary flux / jump-energy cancellation; Guth–Maynard window transfer |
| SignedArithmeticEnergyIncidence | Damping-chain receiver coordinates; Hilbert–Schmidt bounds |
| RenormalizedBiarithmeticGeometry, ConjugateDiagonalGeometry, ArithmeticElectrostatics | Theta-prefix readings, Hecke defect, escaped Möbius boundary |
| ArithmeticOrientationTheory | Pronic Báez–Duarte unit of the width dictionary |
| SignedSuccessorArithmetic | Successor defects recover signs that Selberg forms erase |
| ArithmeticDefectRigidity | Cofactor identities; escape of normalized energy |
| TransThresholdPairCorrelation | Signed prime statistics beyond the large sieve |

Route consumers: PM (cofactor-row damping laws), MC (fixed-modulus/window cancellation), CTF (von
Mangoldt readout, centred pronic residual).

---

## 2. Why

**Regime.** $s_{N,c}(k)=\sum_{q\le N}Y_{N,c}(q)c_q(k)$, Selberg coordinates $Y_{N,c}(q)=\sum_{q\mid d\le N}c(d)/d$;
Ramanujan sums are orthogonal over a full period. Prime questions ask about windows $M\le N^A$,
where (1) drift mixes with incidence ($L_N(M,c)=-\sum_dc(d)\{M/d\}$ gets drift from every $d>M$);
(2) shift and cutoff do not commute; (3) lags and depths couple through exact factorizations.

**The three words.** *Bézout*: $\gcd(n,n+1)=1$; $\Lambda(n(n+1))=0$; least seeds of $pa-qb=1$ govern
event gaps. Beurling systems satisfy every multiplicative identity yet may have off-line zeros: **a
mechanism that sees RH must use Bézout structure.** *Valuation*: a lag $h$ sees mode $q$ iff
$q/\operatorname{rad}q\mid h$. *Incidence*: the matrix $\mathbf1_{d\mid n}$ and its sawtooth geometry.

**The receiver.** $\tau_\varepsilon(n)=\prod_{p\mid n}(1-p^{-\varepsilon})$, $\alpha_\varepsilon=1/\zeta(1+\varepsilon)$,
$A_\varepsilon(n)=\sum_{j\le n}(\tau_\varepsilon(j)-\alpha_\varepsilon)$, $E_T(\varepsilon)=\sum_{n\le T}A_\varepsilon(n)^2/(n(n+1))$.
If $\forall\delta\,\exists\varepsilon\in(0,\delta)$ with $\sup_TE_T(\varepsilon)<\infty$, then RH. Known for
$\varepsilon\ge\tfrac12$, unknown for every $\varepsilon<\tfrac12$. The admitted damping set has infimum
of its derived set $=\Theta-\tfrac12$; width conclusions need accumulation of admitted dampings.

---

## 3. Objects and language

**Coordinates of a row.** Raw $c(d)$; responses $s_{N,c}$ (`sieveSeq`); Selberg $Y_{N,c}$
(`selbergMultiplesCoord`); spectral form over roots of unity of order $\le N$; Witt ghost coordinates
(Frobenius $F_2$ consumes cutoff $2N$; Verschiebung dilates). Finite Ramanujan inversion realises any
$Y$ on $[1,N]$.

**Möbius bands.** $s_{N,\mu}=\mathbf1_{k=1}$ below $N$; $-\mu(k)$ on $(N,2N]$; at most $B$ complementary
quotients on $k\le(B+1)N$.

**Window horizons** (arbitrary phase): period $L_N$; cyclotomic $\Phi(N)=\sum_{q\le N}\varphi(q)$;
quadratic $N^{2\pm o(1)}$; degree-$m$ $N^{m\pm o(1)}$.

**Sawtooth and interior.** $\tilde B_1(d,n)=\{n/d\}-\frac{d-1}{2d}$. Across $n\mapsto n+1$ moduli are
active at $n$, at $n+1$, or **interior**; by Bézout none is active at both. Interior prefix
$I_\varepsilon$, interior energy $E^{\rm int}_T$.

**Quadratic forms** (diagonal in Selberg coordinates, modal weight at $e\ge2$): variance $\varphi(e)$;
successor covariance $\mu(e)$; reserve $\varphi-\mu$; primitive energy $J_2(e)/12$; lag covariance
$c_e(h)$. $\mu$ separates 4 from 6 where $\varphi$ does not.

**Pronic measure** $w(M)=1/(M(M+1))$ replaces period averaging. $\sum_MR_e(M)w(M)=-\Lambda(e)$; von
Mangoldt readout $\mathcal R(c)=\sum_e\Lambda(e)Y(e)$. Pronic Gram $\mathcal G=\Lambda\Lambda^\top+\mathcal G^{\rm ec}$
(energy-centred, PSD), mean-centred $\mathcal G^{\rm mc}$ = cotangent–sawtooth form; Vasyunin sums;
Báez–Duarte residual.

**Damped source and chain.** $c_\varepsilon=\mu(d)d^{-\varepsilon}$; cofactor row; stochastic Cesàro kernel
$P_\eta$ with semigroup and entrance laws; Fermi–Nyman cells $(1/(n+1),1/n]$ carry pronic mass.

**Cross-scale objects.** Bilinear form between small (moduli $\sim P$) and large ($\sim Q$) rows;
Bernoulli kernel; dual norm $\sum_{d}|\Lambda_d(c')|/d$; exponent $\theta=2\log P/\log Q$. Type II:
arbitrary small coefficients; Type I: smooth large rows.

**Vaughan objects.** Five pieces of Vaughan's identity at cutoffs $U,V$; 25-entry pronic Gram $G_{ij}$;
diagonal $D_T$; mixed remainder $R^{\rm mix}_T$; $E^{\rm int}_T=D_T+R^{\rm mix}_T$; admitted coefficient
space; actual limit Gram (`pmPronicVaughanLimitGram`).

**Escaped Möbius boundary.** `escapedPairing` $=\sum_{(N-b)/a<j\le N}\mu(j)/j$ on `HorizonSpace N`;
growing-endpoint law `GrowingEndpointEscapedMoebiusLaw θ`.

---

## 4. Mechanisms

1. **Bézout splitting.** Divisor pairs of $(k,k+1)$ ↔ divisors of $k(k+1)$; coprime products are never
   prime powers; $\tau_\varepsilon(k)\tau_\varepsilon(k+1)=\tau_\varepsilon(k(k+1))$.
2. **Simultaneous diagonalization and finite cones.** $2\mu(e)\le\varphi(e)$ (equality only at 6);
   covariance cones finitely generated by explicit modes, realised by Ramanujan inversion.
3. **Polarization and renormalization.** $2R_N(M)=-\sum(\Delta s)^2+s(M+1)^2-s(1)^2$; renormalization
   is forced. Short windows: defect $\le0$ for all rows iff endpoint states agree.
4. **Observability.** Cyclotomic recurrence of order $\Phi(N)$ determines a row at every phase; **no
   linear horizon**; window sandwich constant of exact order $N^2$; degree-$m$ moments transfer at
   $N^{m\pm o(1)}$; degrees 5–6 determine a row up to the half-period companion.
5. **Pronic Gram calculus.** $\mathcal G^{\rm mc}(p,q)$ is a finite cotangent–sawtooth sum (Vasyunin);
   $\mathcal G^{\rm ec}$ strictly PD on finite modulus sets; hypercube factorization (coherent across
   depths only).
6. **Reciprocity kernel = Ramanujan + Kloosterman.** Zero-mean Kloosterman cosine series with Weil
   bound $|C_m(p)|\le\frac{\pi^2}{24}p^{3/2}$, **order-sharp**; prime Gram = rank three + Kloosterman.
7. **Báez–Duarte in pronic coordinates.** Residual $=(1-\mathcal R)^2+Q^{\rm ec}$; minimum
   $1/(1+\mathcal R^2/Q^{\rm ec})$; unconditional floor $\kappa/\log N$.
8. **Sawtooth martingale calculus.** $E_T=D^{\rm act}+2P^{\rm pred}+2M^{\rm int}$; after drift
   compensation the first two are bounded: **the whole obligation is the interior martingale**.
   Summation by parts is a conservation law, never a contraction.
9. **Vaughan calibration.** $E^{\rm int}=\sum G_{ij}$; diagonal sign-blind; $R^{\rm mix}/D\to-1$
   unconditionally; bounded energy ⇔ $|1+R^{\rm mix}/D|=O(1/T)$; leading matrix $\rho^2vv^\top$, second
   scale rank-one. The **admission rank reads the zero abscissa**: extra-rank dampings = receiver
   dampings, lower accumulation boundary $\Theta-\tfrac12$. Every uniform power gain (prefix, residual
   Gram rate, tail, factorial order one) is **exactly a fixed zero-free strip**; exact decay indices
   $1-\Theta$ (tail), $4(1-\Theta)$ (cutoff energy), $2(1-\Theta)$ (horizon energy); attained endpoint
   rates force RH and simple zeros; unconditional endpoint floors forbid little-o. For $\varepsilon\ge\tfrac12$
   the actual limit Gram is PSD of rank two (prefix/pole minor $\ge2^{-4\varepsilon}/15552$); at
   $\varepsilon=\tfrac12$ moving limits form a ray indexed by harmonic mass. Below ½ the extreme
   cutoff reads the squared Möbius harmonic sum.
10. **Dilation profiles and the Bézout seed.** Dyadic windows reduce consecutive divisor edges to the
    single pair $(2,3)$.
11. **Literal Möbius on linear windows.** Cofinal slope $\kappa\approx0.4408$ = period variance =
    one-line energy of $1/\zeta$, $\kappa\ge1/288$.
12. **Cross-scale dispersion.** Log-free large sieve; **Type-II barrier** $Q\ge P^{5/3}$ sharp
    (coherent near-multiples); exact loss = $\ell^1$ residue discrepancy (parity-blind); Type I gains
    one order per smoothness order.
13. **Actual rows.** Prime row statistic is the omitted-class term $\asymp p/Q$; Möbius $o(1/Q)$.
    Short-window mean squares (Huxley, Guth–Maynard) beat Type II qualitatively.
14. **Balanced statistic = quasi-RH.** A power saving at the diagonal $Q\asymp P$ (or short windows at a
    fixed exponent) ⇔ $\Theta<1$; below the diagonal the saving is unconditional.
15. **Rate transfer to zero-free bands.** Mertens rates transfer to the receiver on a horizon-dependent
    band ($\varepsilon\ge\tfrac12-\kappa\sigma(T)/(480\log T)$ from VK); pointwise transfer loses half the width.
16. **Escaped Möbius boundary.** Growing-endpoint power law at $\theta$ ⇔ $\Theta\le1-\theta$ ⇔ receiver
    rate $\le\tfrac12-\theta$ ⇔ Hecke-defect strip cap ⇔ Carathéodory positivity of $\Re\,\xi'/\xi$ on
    $\Re s>1-\theta$. Unconditionally the escaped pairing decays at VK rate uniformly in $N,a,b$; the
    single-scale theta-prefix reading has a VK sub-trivial ceiling.
17. **Damping chain operator calculus.** Centred operator compact on $c_0$, spectrum
    $\{0\}\cup\{d^{-\eta}\}$; admission ⇔ Hilbert–Schmidt of the size-biased chain; residual has a
    linear cusp $\kappa\varepsilon$ from a critical zero.

---

## 5. Pillar theorems

1. **Observability**: $\Phi(N)$ at every phase, no linear horizon, sandwich order $N^2$, companion
   classification (`not_exists_linear_observability_horizon`, `windowSandwichConstant_exact_quadratic_order`,
   `sameRelationSpectrum_five_six_iff`).
2. **Explicit pronic Gram** (`pmRamanujanMeanCenteredGram_eq_cotangent_sawtooth`).
3. **Báez–Duarte in rows** (`riemannHypothesis_iff_pronic_prefix_energy`, `exists_readout_energy_uncertainty`).
4. **Energy is one signed term** (`exists_pmBezoutInterior_compensated_energy_bound`,
   `pmInterior_strict_contraction_iff_bounded_energy`).
5. **Sharp Type-II barrier and exact loss** (`exists_readout_free_barrier`).
6. **Balanced statistic is quasi-RH** (`balancedStatisticPowerSaving_iff`, `moebiusPowerWindowSaving_iff`).
7. **Cofinal slope = one-line energy of $1/\zeta$** (`cofinalMobiusSlope_eq_integral_eulerProduct`).
8. **Vaughan rank reads the abscissa; uniform Vaughan power = fixed strip**
   (`pmPronicVaughanRankDampings_eq_receiverDampings`, `riemannHypothesis_iff_accPt_zero_vaughan_rank`,
   `zetaZeroAbscissa_lt_one_iff_uniform_pmUndampedVaughan_power`, `rank_pmPronicVaughanLimitGram`).
9. **Damping chain** (`mem_receiverDampings_iff_hTransformed_hilbertSchmidt`).
10. **Complete-period quadratic data are exactly sign-blind** (`periodCovariance_eq_iff_exists_scaledSelbergRow`).
11. **Escaped Möbius / quasi-RH unification** (`escapedMoebius_receiver_abscissa_tfae`,
    `quasiRH_crossRoute_seven_way_tfae`, `exists_abs_escapedPairing_moebiusSource_le_vk_rate`).

---

## 6. Traps

| Trap | Correct statement |
|---|---|
| Pronic reach is cancellation | A modulus $d>M$ contributes only drift |
| Observability needs a period | $\Phi(N)$ values suffice; but no linear horizon exists |
| Degree-$m$ statistics transfer at $N^2$ | Horizon is $N^{m\pm o(1)}$ |
| Compressed lags form a semigroup | They do not |
| Raw Möbius defect is small | Only the renormalized defect is bounded |
| Multiplicative identities can close it | Beurling systems satisfy them all |
| Fixed-depth cancellation | Cancellation is cross-depth only |
| The three Grams are interchangeable | They differ by rank-one terms; PD holds for $\mathcal G^{\rm ec}$ |
| Total variation controls the receiver | Entrance tail non-square-summable at $\eta\le\tfrac12$ |
| Summation by parts is an estimate | Returns $E_T$ with coefficient 1 |
| Far scales decouple | Only for $Q\ge P^{5/3}$ |
| The cross-scale form breaks parity | It sees residue masses + two readouts |
| Flat/smooth rows model primes | Möbius and prime rows are not smooth at any order |
| Sub-Weil saving at one prime | The Weil bound on $C_m(p)$ is order-sharp |
| A diagonal power saving is weaker than a strip | It *is* $\Theta<1$ |
| A Mertens rate bounds the receiver at fixed $\varepsilon<\tfrac12$ | Only on a horizon-dependent band |
| Pointwise prefix bounds suffice | Lose half the width; estimate in mean square |
| Relative Vaughan cancellation is progress | $R^{\rm mix}/D\to-1$ is unconditional; the error is $E^{\rm int}$ itself |
| A uniform Vaughan power gain is a new input | It is exactly a fixed strip |
| Another quasi-RH equivalence is progress | Seven are unified; none is closer to a bound |

---

## 7. Open problems

1. **The receiver.** One fixed $\varepsilon<\tfrac12$ with $\sup_TE_T(\varepsilon)<\infty$ (equivalently bounded
   interior energy, strict interior contraction, square-summable chain columns, bounded dual residual).
   Unconditional size = zero-free region.
2. **Interior martingale contraction.** $2M^{\rm int}+2\,\mathrm{Counterterm}\le(1-\delta)E_T+C_\varepsilon$ at one
   fixed $\varepsilon<\tfrac12$; must come from the mixed Vaughan entries $G_{ij}$, $i\ne j$.
3. **Dual construction.** Rows with $\mathcal R^2/Q^{\rm ec}\to\infty$ within the ceiling; sharp rate.
4. **Balanced dispersion beyond quasi-RH.** Which subpower or Kloosterman-reciprocity gain at
   $Q\asymp P$ sums into the receiver? Gains must come from averaging over moduli or the CRT block.
5. **Cross-depth cancellation.** Hypercube Dirichlet form uniform in $P$ for $0<\varepsilon\le\tfrac12$.
6. **Damping chain.** Forward $\ell^2$ boundedness at one fixed $\eta<\tfrac12$ (must read Möbius signs).
7. **Observation constants.** Exact growth of $L_{\rm obs}(N)$; exact $S_{\rm opt}(N)/N^2$.
8. **Topics.** Bézout-selective identities for mixed Vaughan entries; a finite cutoff-quantitative
   statistic separating the parity pair below the band; whether Witt structure gives a bound the
   Selberg coordinates do not.

## 8. Tools to build

Signed interior contraction; a receiver-strength balanced dispersion estimate beyond quasi-RH; dual
rows with vanishing readout defect and energy; a forward $\ell^2$ chain bound below ½.

## 9. Conventions

- Name coordinates (raw/response/Selberg/spectral/ghost) and regime (period, prefix, octave, band,
  arbitrary-phase window; horizon $\Phi(N)$, $N^2$, $N^m$).
- Identity before asymptotics; keep boundary terms and signed defects.
- Test against Beurling: the additive input must be visible ($\gcd(n,n+1)=1$, $pa-qb=h$, an omitted
  residue class, a valuation layer).
- State what a bound does not prove (first moment ≠ square root; $\varepsilon\ge\tfrac12$ ≠ below; floor ≠ rate).
