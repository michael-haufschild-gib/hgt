# Trans-Horizon Incidence Mechanics (THIM)

A divisor sieve of horizon $N$ reads $k$ through divisors $d\le N$. THIM asks what this finite
observer can recover and bound far beyond its horizon ($k\gg N$), and how its observations
transfer to RH-equivalent energies: signed sieve energies, Fermi–Nyman reciprocal-cell traces,
and odd-sector arithmetic Markov chains. *Incidence* is $d\mid k$; *mechanics* is conservation
and dissipation under succession $k\mapsto k+1$, horizon growth $N\mapsto N+1$ and prime dilation
$k\mapsto pk$; *trans-horizon* concerns omitted divisors, composite as well as prime.

Namespace `GaloisForLFunctions.TransHorizonIncidenceMechanics`; umbrella
`TransHorizonIncidenceMechanics.lean`. Sieve objects come from BVI and BSU; Markov/chain/theta/Haar
objects from `RHTower`.

---

## 1. Place in the research

THIM is the **finite-observer theory of signed arithmetic receivers**. Its central lesson:
exact recovery, good conditioning and period-variance bounds do **not** pay the centred-prefix
pronic energy $\sum_{n\le T}A_c(n)^2/(n(n+1))$. Two thresholds organise everything: sign-blind
payment needs damping $>\tfrac12$; signed horizon-limit commutation holds exactly from $\tfrac12$.
Below $\tfrac12$ an infinite source can be paid while its truncated rows are not.

| Neighbour | Interface |
|---|---|
| [BezoutValuationIncidence](../BezoutValuationIncidence/README.md) | Selberg coordinates, successor polarization, window Poincaré laws, Vaughan pronic calibration, cofinal Möbius slope |
| [BiScaleUncertainty](../BiScaleUncertainty/README.md) | Full-period observation theory, packets, Chebyshev gauge, countermodels |
| [ArithmeticContinuationAndCriticalEnergy](../ArithmeticContinuationAndCriticalEnergy/README.md) | Transports the receiver in damping/cutoff; THIM locates the boundary |
| [ArithmeticCompensationTheory](../ArithmeticCompensationTheory/README.md) | Whether signed derivative work is paid without restating admission |
| [ScaleSignedIncidenceCriticality](../ScaleSignedIncidenceCriticality/README.md) | Abstracts parity pairs into limits on what a reading can prove |
| [SignedArithmeticEnergyIncidence](../SignedArithmeticEnergyIncidence/README.md) | Keeps source and cross terms from receiver data to energy |
| [ArithmeticCriticalityTheory](../ArithmeticCriticalityTheory/README.md), [ArithmeticIncidencePositivity](../ArithmeticIncidencePositivity/README.md) | Odd-sector and crossing-pair forms of the same obstruction (nine moduli) |
| [arithmetic-positivity-theory](../arithmetic-positivity-theory/README.md), [SquareRootThreshold](../SquareRootThreshold/README.md) | Continuous receivers and zero detection |
| [ArithmeticOrientationTheory](../ArithmeticOrientationTheory/README.md) | Even flip as orientation read at the prime 2; parity barrier for readings |
| [SignedSuccessorArithmetic](../SignedSuccessorArithmetic/README.md) | Möbius orientation in successor/coprime-factor observations |
| [ArithmeticDefectRigidity](../ArithmeticDefectRigidity/README.md) | Same pronic receiver via cofactor energy $E=F+G-2Q$ |
| [TransThresholdPairCorrelation](../TransThresholdPairCorrelation/README.md) | Parity barrier at close prime pairs beyond Montgomery–Vaughan |

Routes: PM uses cofactor mean preservation, growing-cutoff transfer, Fermi traces; MC uses
oscillating probes and their anti-alignment criterion. BVI owns the Vaughan calibration and feeds
PM, MC, CTF.

---

## 2. Why: the horizon barrier and the receivers

Below the horizon ($M+1\le N$) the renormalized defect is nonpositive because the truncated
divisor sum is complete. Above it, omitted divisors at a highly composite endpoint can make
$|s_{N,c}(M+1)|>|s_{N,c}(1)|$, reversing the boundary sign in Dirichlet polarization. THIM
locates every such failure and extracts what survives.

**Three RH receivers**, each needing a horizon-uniform estimate on a literal source:

1. *Interior pronic energy.* With $c_\varepsilon(d)=\mu(d)d^{-\varepsilon}$ and Bézout interior
   prefix $I_\varepsilon$: if $\forall\delta\,\exists\varepsilon<\delta\,\sup_T\sum_{n\le T}I_\varepsilon(n)^2/(n(n+1))<\infty$
   then RH. The constant may depend on $\varepsilon$, not on $T$. Known for $\varepsilon\ge\tfrac12$.
2. *Odd-sector positivity.* RH ⇔ the arithmetic Markov resolvent (theta ground state) has no odd
   eigenvalue in $(\tfrac12,1)$ ⇔ cosh mass $\le$ archimedean Doob jump + same-side prime jumps +
   bipartite prime-power chain variances, for odd $v\in C^2_c$.
3. *Nyman–Beurling.* RH ⇔ $\mathbf1_{(0,1]}\in\overline{\operatorname{span}}\{\{1/(kx)\}\}$. Origin tail
   $\int_N^\infty|\sum a_k\{u/k\}|^2du/u^2$; a tail bound alone identifies neither weak limit nor bulk.

---

## 3. Objects and language

**Sieve.** $s_{N,c}(k)=\sum_{d\mid k,d\le N}c(d)$ (`sieveSeq`); Selberg coordinates
$Y_{N,c}(e)=\sum_{e\mid d\le N}c(d)/d$ (`selbergMultiplesCoord`). Observation state
$\gcd(k,L_N)$, $L_N=\operatorname{lcm}(1..N)$ (complete invariant); radical state $\gcd(k,N\#)$;
phase $k\bmod L_N$. $N$-rough integers (no divisor in $[2,N]$) form a monoid; rough-prime boundary
= prime $p\in(N,2N)$ with its 4-divisible neighbour.

**Weights.** $\mu$; $c_\varepsilon$ with $\tau_\varepsilon(n)=\prod_{p\mid n}(1-p^{-\varepsilon})\in[0,1]$;
Ramanujan coefficients $w_\varepsilon(e)=\rho_\varepsilon\mu(e)/D_\varepsilon(e)$,
$\rho_\varepsilon=1/\zeta(1+\varepsilon)$; PM cofactor row $c_Q$ (squarefree, support $[1,Q]$).

**Energies.** $Q_{\text{Sel}}=\sum\varphi(e)Y^2$; $Q_{\text{Bez}}$ (coprime pairs); successor reserve
$\mathcal R_N=Q_{\text{Sel}}-Q_{\text{Bez}}=\sum_{e\ge2}(\varphi-\mu)(e)Y(e)^2$; renormalized defect
$\widetilde{\mathcal D}_N(M)=\mathcal D_N(M)-M\mathcal R_N$; primitive energy
$12\mathcal E_{\text{prim}}=\sum J_2(q)Y(q)^2$; period covariance $\mathrm{Cov}_N(h)=\sum c_e(h)Y(e)^2$.
**Dirichlet polarization** (every sign statement passes through it):
$$2\widetilde{\mathcal D}_N(M)=-\sum_{k\le M}(s(k+1)-s(k))^2+s(M+1)^2-s(1)^2 .$$

**Horizon steps.** Band index $B=\lfloor M/m\rfloor$; Möbius band step $\Delta(m,B)$; Buchstab slope
$\lambda(m)$, $\lambda(p)=1-2\mathfrak m(p-1)$, $\mathfrak m(x)=\sum_{d\le x}\mu(d)/d$; smooth core
$\gcd(m,B\#)$; band average $A(B)$; profile $P(B)=\lim\mathcal E_N((B+1)N;\mu)/N$; damped crossover
$\Lambda(\varepsilon)=\log(1/2\rho_\varepsilon)/\varepsilon$.

**Scales.** $k\le N$ complete; $(N,2N]$ one omitted divisor; $(B+1)N$ at most $B$ omitted quotients
$\le B$; unit envelope for $k<5(N+1)$; radical ratio $<11$: Möbius responses $\le2$; $M\ge2N^2+2N-2$:
long-window dissipation.

**Fermi.** Cell response $F_{N,c}(n)=\sum c(d)(2\lfloor n/2d\rfloor-\lfloor n/d\rfloor)$, boundary
jumps $J$; pronic weight $1/(n(n+1))$; dyadic rays $n=2^kb$ saturating at $L=\lfloor\log_2N\rfloor$;
schedules, slots; inverse constants $K_N$ (selected), $K^{\text{all}}_N$, $K_g(N)$ (one gap).

**Clocks.** $\tau(q)=q/\operatorname{rad}q$ (`lagVisibilityClock`): $c_q(h)/\varphi(q)$ sees $q$ iff
$\tau(q)\mid h$; $\Lambda(d)=\log(d/\tau(d))$ iff $d/\tau(d)$ prime (guard: $\Lambda(6)=0$).

**Odd sector.** Riemann kernel $\Theta$; odd profile $m_a=(\Theta(\cdot-a)-\Theta(\cdot+a))/(2\sinh\frac a2)$;
source graph energy/pairing, signed radical, ground vector $\mathbf1$, resolvent; pole moment
$\langle q,\tanh_L\rangle$.

**Receiver classes.** For a weight $c$ with Ramanujan coefficients $W_c$: receiver
$E_T(c)=\sum_{n\le T}A_c(n)^2/(n(n+1))$, $A_c(n)=\sum_{j\le n}((c*1)(j)-W_c(1))$; *paid* =
`ReceiverBounded`. Damped class $\mathcal C(K,\varepsilon)$: $|c(d)|\le Kd^{-\varepsilon}$. Sign-blind
data: $|W_c|$, period statistics, pronic mode masses. Parity pair: same sign-blind data, one paid
and one not. Critical Wiener algebra: $\sum|g(q)|q^{-1/2}<\infty$; pole value $K(1-\varepsilon)$;
first pronic moment $M(c)=-\sum\Lambda(e)W_c(e)$; even flip $c^\flat$ (Fermi factor $1-2\cdot2^{-s}$).

---

## 4. Mechanisms

1. **Rough absorption.** $s_N(qr)=s_N(q)$ for rough $r$; at rough checkpoints the boundary squares
   cancel ⇒ defect $\le0$ for every weight; sharp: nonpositive for all weights iff endpoint rough.
2. **Horizon filtration.** $s_N(k)=\sum_{d\mid k}c(d)-\sum_{q\mid k,k/q>N}c(k/q)$; band normal forms;
   prime pairing puts $s_{X,\mu}(pk)$ on the top $p$-adic window; radical envelope
   $|s_{N,\mu}(r)|\le2^{\omega(r)-2}$.
3. **Envelope ladder.** $|s_N(c_\varepsilon,k)|\le1$ for $k<5(N+1)$, exact (failure $N=6p-1$,
   $k=30p$); rungs 2 below ratio 11, 3 below 13, growth $Q/\log Q$. Integer jump energy makes ratio
   11 (not 5) the Möbius sign boundary. Endpoint-square methods die at ratios $(\log N)^{O(1)}$.
4. **Global defect sign.** Polynomial windows: rough-prime boundaries dissipate $\ge4^{-\varepsilon}$
   each ⇒ $-\kappa N/\log N$ uniformly in $\varepsilon\in[0,1]$. Long windows: MV on step differences
   gives window Poincaré constant $2N(N-1)$ and slope $\ge V(c)$. Together: all prefixes nonpositive
   at large horizons; Möbius certified for $N\le12$. Receiver row: one jump of $\tau_\varepsilon$ suffices.
5. **Spike cancellation.** Extracting the last step cancels the endpoint square; a sign change
   between coprime neighbours caps the defect; path Poincaré prices spikes.
6. **Period laws.** On a common period, variance/correlation/Dirichlet $=L(Q_{\text{Sel}},Q_{\text{Bez}},2\mathcal R)$;
   torus Poincaré constant $\le1$ (Bézout coprimality kills non-coprime correlations in one step).
   Möbius observer is **white**: lag covariances → 0, variance $\to\kappa\ge1/288$ (cofinal slope).
   Reserve horizon law: $\mathcal R_p-\mathcal R_{p-1}=c(p)^2/p$ at every prime.
7. **Buchstab calculus.** Horizon step $=c(N+1)^2\lfloor M/(N+1)\rfloor+2c(N+1)\sum s_N((N+1)j)$; slope
   law; large prime horizons **inject** energy for Möbius at every $B\ge2$; smooth-core law (step
   depends only on $\gcd(m,B\#)$); band averages radical-invariant, $A(B)<0$ for $B\le9$, $A(10)>0$,
   profile nonconcave at powers of 5.
8. **Damped observer.** Freezes into $\tau_\varepsilon$ on linear windows; Parseval in $w_\varepsilon$;
   exact linear dissipation $\to-(B+1)R(\varepsilon)$, $R\sim\varepsilon/2$; second/third-order laws;
   damped prime horizons dissipate beyond $\Lambda(\varepsilon)\pm O(\varepsilon^2)$. Variance and
   damping limits **do not commute** ($0<1/288$). Primitive energy $\asymp N^{1-2\varepsilon}$ for
   $\varepsilon<\tfrac12$: below ½ only pronic weights work.
9. **Observation and recovery.** State is not dynamics beyond $N=2$; phase recovery window
   $\Phi_{\max}(N)$, error-correcting thresholds; coefficient recovery by Möbius inversion with exact
   amplification; short windows classified by endpoint states; canonical radical state maximizes the defect.
10. **Clocks and prime chains.** Three-zone filter law for prime-power modes; clock wavelets;
    squarefree rows see only $\operatorname{rad}(h)$; chain renormalization $s_H(c,pb)-s_H(c,b)=s_{H/p}(c(p\cdot),b)$.
11. **Fermi observability.** Schedule injective iff at most one of $L+2$ slots missing (dyadic and
    $p$-adic); $K_N\sim\frac4{\pi^2}(\log_2N)^2$, $K^{\text{all}}_N\sim\frac1{\pi^2}(\log_2N)^2$, one gap at
    depth $\alpha$: $\frac4{\pi^2}\max(\alpha,1-\alpha)^2$ (mixed vs Dirichlet chains). Wavelet identity
    $F=2A(\lfloor n/2\rfloor)-A(n)-(n\bmod2)m$ reduces bulk and origin-tail tightness to a subpower
    prefix bound. Antichain capacity iff $\sum_{p\in\Pi}1/p<\infty$.
12. **Odd quotient.** Exact: sourceEnergy $=$ weilForm $+2\langle q,\tanh_L\rangle^2$ on odd vectors;
    the polar shift is a gauge. Cross-lobe sandwich on odd eigenvectors; RH ⇔
    $\mathrm{weilBilin}(q^+,q^-)\le\tfrac12\langle q_1,\tanh_L\rangle^2$. Fermi curvature + Bézout
    gradient on the second octave $=-2\mu$ of the first-octave parent.
13. **Collar transport.** Parallelogram law across prime cuts; exact identity moving the
    origin-crossing collar onto a jump at distance $\ge t/2$; midpoint reflection to one-point
    diagonal potentials: atom-minus-pole excess positive on $(0,\log d)$ iff $d\in\{2,3,4,5,7\}$,
    total excess iff $d$ in the **nine moduli** $\{2,3,4,5,7,8,9,11,13\}$. **Light-cone variation:**
    adding profile variance replaces the Lévy drop by the Weil jump difference
    $\kappa(s)-\kappa(s+2y)\ge4\sinh\frac y2\sinh\frac{y+s}2$ globally, so for every $R$ and $\varepsilon>0$
    large aperture pays all prime powers $\log d\le a-R$ with an $\varepsilon$-fraction of the continuum energy.
14. **Absorption boundary.** cosh/sinh ratio $\ge\pi e^{2x-5\log2/4}>1$ for $x\ge\log2$: no fixed
    absorption coefficient; confinement law; compact primitive tests have energy $O((n+1)^{-2})$ —
    no uniform gap relative to the graph norm.
15. **Parity calculus.** Hyperbola split $A_c(n)=\sum c(d)(\lfloor n/d\rfloor-n/d)-n\sum_{d>n}c(d)/d$;
    positive weights paid iff $\sum M_k^2/2^k<\infty$ (dyadic masses); bounded partial sums pay;
    character/Liouville/Fermi parity pairs; even flip invisible to translated moments of every
    degree; logarithmic moment hierarchy $M(c\log^k)=-\sum\Lambda_{k+1}W_c$ separates every pair.
16. **Pole law and Wiener closure.** Critical Wiener convolution preserves payment; local factors with
    $|a|<\sqrt p$ preserve the class; Mellin pairing $\Phi_{k\star q}=K\Phi_q+m_q\Phi_k$; drift forces
    pole cancellation $K(1-\varepsilon)=0$; vanishing order additive (log pole moments).
17. **Mellin continuation and boundary energy.** Paid ⇒ $\zeta(s)(C(s)-m)$ holomorphic on $\Re s>\tfrac12$,
    no simple pole on the critical boundary; at ½: payment ⇔ bounded line energy of
    $\zeta(s)(C(s)-m)/s$; $|C(\sigma)-m|\le2\sqrt E(2\sigma-1)^{-1/2}$; partial pole sums decide
    $k\star d^{-\varepsilon}$ on $(0,1)$; sharp $\sqrt{\log}$ weight at ½.
18. **Horizon-limit commutation.** Uniformly paid rows ⇔ paid limit exactly for $\varepsilon\ge\tfrac12$
    on $\mathcal C$; below, lacunary dipoles break it; never on the convolution class.
19. **Multiplicative phase diagrams.** Euler product pinches $\log|F|$ to $\Re\ell_f$ beside the line.
    Quarter law (flipped density $1/4$) for constant-sign and residue flips; below ½ local exponents
    are integers (0 off the real axis); phase law reads only $\Re(ae^{i\varphi})$; prime signs and
    means do not decide; divergent-mass defects obey the **Dini law** $\int_0^1e^{-c\Lambda(\rho)}d\rho/\rho<\infty$.
20. **Probe spectroscopy.** $d^{-\varepsilon}\cos(t\log d)$ paid iff $\zeta(1-\varepsilon+it)=0$;
    log-power probes read multiplicities; half-damped probe energy $/\log T\to|\zeta(\frac12+it)|^2/(2|\frac12+it|^2)$.
21. **Actual source.** All-damping hyperbola + VK prefix bounds; power saving for $\sum(\mu\star\Lambda)$
    at $\beta$ pays Möbius/Liouville for $\varepsilon>\beta/2$; admission set infimum $=\Theta-\tfrac12$;
    long-sawtooth/tail **anti-alignment gap** ⇔ non-admission of probes.
22. **Signed interior energy.** PM cofactor row keeps the Haar mean (no dipole); interior energy =
    diagonal of a 25-entry signed Vaughan Gram + mixed remainder; diagonal sign-blind; leading matrix
    rank one $\rho^2vv^\top$; bounded energy ⇔ $|1+R^{\text{mix}}/D|=O(1/T)$.
23. **Selectivity classes.** I Beurling-universal; II sign-blind ($(\mathbb Z/2)^N$-invariant);
    III Bézout-selective ($\gcd(n,n+1)=1$, $pa-qb=1$). Only III can carry new information.

---

## 5. Pillar theorems

| Pillar | Anchor |
|---|---|
| All-prefix defect sign at large horizons, uniform in $\varepsilon\in[0,1]$; Möbius $N\le12$ | `eventually_pmPowerDamped_renormalizedDefect_nonpos_uniform`, `moebius_defect_nonpos_of_le_twelve` |
| Envelope boundary at ratio 5, rungs at 11, 13 | `sieveRenormalizedPrefixDefect_moebiusReal_five_succ_nonpos`, `sieveSeq_moebiusReal_rung_two_family` |
| White Möbius observer; variance → cofinal slope | `tendsto_periodCorrelation_moebius`, `tendsto_periodVariance_moebius`, `one_div_288_le_cofinalMobiusSlope` |
| Primitive energy diverges for $\varepsilon\le\tfrac12$ | `tendsto_sievePrimitiveEnergy_pmPowerDamped_atTop` |
| Positive weights: dyadic-mass criterion | `bounded_weightPronicEnergy_iff_summable_dyadicMass` |
| Parity barrier: amplitudes decide iff $\varepsilon>\tfrac12$ | `receiverBounded_amplitudeInvariant_iff`, `parity_barrier`, `char_parityPair` |
| Damping = zero width: $\inf$ derived admission set $=\Theta-\tfrac12$ | `receiverDampingRate_eq_zetaZeroAbscissa_sub_half`, `riemannHypothesis_iff_forall_pos_receiverBounded_moebius` |
| Wiener/pole laws; smooth-power criterion below ½ | `receiverBounded_dirichletConv`, `receiverBounded_dirichletConv_unit_iff_critical` |
| Half-damped boundary energy | `receiverBounded_iff_exists_lineEnergy_le` |
| Horizon-limit commutation exactly from ½ | `horizonLimit_commutes_with_receiver_iff` |
| Phase diagrams: quarter law, phase law, Dini law | `receiverBounded_residueFlip_half_iff_general`, `receiverBounded_phaseWeight_iff`, `receiverBounded_defectWeight_iff` |
| Integer local exponents below ½ | `exists_int_localExponent_of_receiverBounded_damped` |
| Zero-divisor spectroscopy | `receiverBounded_oscillatingSmoothPower_iff`, `receiverBounded_logPowerCosine_iff_all` |
| Fermi observability and conditioning | `fermiScheduleInjective_iff`, `fermiPhysicalInverseConstant_logb_limit` |
| Odd quotient and cross-lobe reduction | `riemannHypothesis_of_odd_eigenvector_cross_lobe_weilBilin_le_tanhL_sq` |
| Anti-alignment form of RH | `riemannHypothesis_iff_forall_ne_zero_exists_longSawtooth_tail_antiAlignment_gap` |
| Selectivity classes | `selectivity_class_III_bezout_successor_selective_laws` |

---

## 6. Traps

| Trap | Why it fails |
|---|---|
| Full period is $N!$ | Least period divides $\operatorname{lcm}(1..N)$ |
| Period diagonalization controls moving windows | Short windows are classified by endpoint states |
| Unit envelope beyond ratio 5; ratio 5 is a sign boundary | Fails at $5N+5$; sign boundary is ratio 11 |
| Endpoint-square methods reach every scale | Die at ratios $(\log N)^{O(1)}$ |
| Möbius = $\varepsilon\to0$ limit of damped | Only on bounded horizon ranges; variance, dissipation, profile limits do not commute |
| Prime horizons dissipate | Möbius large primes inject; damped dissipate only past $\Lambda(\varepsilon)$ |
| Complete-period averages bound the discrepancy below ½ | Primitive energy diverges; pronic weighting essential |
| Nyman tail with $dx/x^2$ | Correct transform is $\int_N^\infty|\cdot|^2du/u^2$ |
| $\Lambda(d)=\log(d/\tau(d))$ always | Prime guard: $\Lambda(6)=0$ |
| State equality = dynamics | Only for $N\le2$ |
| Finite observability ⇒ source estimate | Recovery says nothing about cancellation |
| Injective selected trace ⇒ uniform coercivity | Constant grows like $(4/\pi^2)(\log_2N)^2$ |
| Off-line chain excess excludes a zero | Lower bound for an inserted mode only |
| Polar shift is a parameter | It is a gauge |
| Lobe-local inequality settles the odd sector | RH is a cross-lobe statement |
| Fixed cosh/sinh absorption coefficient | Ratio grows like $\pi e^{2x}$ |
| Ramanujan amplitudes/translation statistics decide payment | Only for $\varepsilon>\tfrac12$ |
| More sign-blind observables narrow the gap | Blindness closed under post-processing; floor stays ½ |
| One admissible damping bounds the width | Width = infimum of the derived set |
| Higher-degree moments see squarefree parity | Even flip invisible at every degree |
| Separating observables bound the receiver | Separation is qualitative |
| Flipped density decides | Only on residue patterns; oscillating patterns with same signs/means split |
| Real-axis tests detect oscillating probes | Pole sits at $1-\varepsilon\pm it$ |
| Probe payment is a Möbius estimate | Möbius series $1/\zeta(s+\varepsilon)$ is the unknown |
| Absolute bounds on Vaughan pieces | Squared majorant nonsummable; content is off-diagonal signs |

---

## 7. Open problems

1. **Actual Möbius receiver at one fixed $\varepsilon<\tfrac12$.** Bound
   $\sup_T(\sum_iG_{ii}+R^{\text{mix}}_T)$ unconditionally, then cofinally as $\varepsilon\downarrow0$.
   Equivalent arithmetic target: $|\sum_{e\le N}(\mu\star\Lambda)(e)|\le CN^\beta$, $\beta<1$ (VK gives
   only subpower). Must use Class III (successor) information. Complementary coordinate: control the
   signed forcing–cofactor pairing $Q$ of ArithmeticDefectRigidity.
2. **Small horizons.** Uniform argument for the finite gap between $N\le12$ and the eventual
   regime (explicit PNT octave count).
3. **Buchstab.** Sign pattern of $A(B)$ beyond 10; a damped deformation commuting with the cofinal limit.
4. **Odd sector.** Prove $\mathrm{weilBilin}(q^+,q^-)\le\tfrac12\langle q_1,\tanh_L\rangle^2$, or pay the nine
   moduli and inner axis ends ($d\ge23$) by jump energy; the light-cone budget now discharges all
   $\log d\le a-R$ at large aperture — the residual is the low-prime/inner-end region.
5. **Fermi–Nyman.** Möbius origin-tail tightness below $\Theta/2$ without zero-free input (= problem 1);
   identify weak limits of bounded Nyman rows from Fermi data.
6. **Horizon-row gap.** For $\Theta-\tfrac12<\varepsilon\le\Theta/2$ close the row gap for Möbius or
   exhibit the dipole.
7. **Phase diagrams.** Non-monotone defects of divergent critical-line mass; sufficient conditions
   below ½ (which for Liouville is problem 1).
8. **From separation to bound.** Give an exponent to a separating observable; a non-perturbative
   index formula for "paid"; transfer the nine-moduli obstruction between sieve and pair sides;
   quantitative Class III laws controlling off-diagonal Vaughan entries.

---

## 8. Tools

Built: complementary-divisor normal forms and polarization; envelope ladder; rough-prime and
MV window dissipation; Ramanujan/Selberg period calculus; Buchstab band calculus; damped
observer asymptotics; state/phase recovery; Fermi schedule calculus and wavelet bridge; clock
filters; odd quotient, cross-lobe sandwich, collar transport, light-cone budget; parity/pole/Wiener
calculus; Mellin boundary energy; phase-diagram toolkit (Euler-log pinching, Dini law, quarter
law); probe spectroscopy; hyperbola/VK source bounds; signed Vaughan Gram; selectivity classes.

To build: a signed Möbius bound below ½; a Class III estimate for off-diagonal Vaughan entries;
the odd cross-lobe bound.

---

## 9. Working conventions

- Fix weight class, ranges of $k,M,N$, band/ratio, polynomial or long-window regime.
- Keep horizon and damping limits ordered; state nested eventual quantifiers.
- Audit signs through polarization with boundary squares; period laws through Selberg/Ramanujan.
- Transport certificates along radical fibres and positive powers; use symbolic prime-indexed
  counterexamples and proved PNT inputs ($\mathfrak m(x)\to0$, $M(x)=o(x)$, octave counts).
- Capstones take data (`c`, `N`, `M`, `ε`, `S`); no assumed positivity, cancellation or zero location.
- A failed law yields its first failure and the strongest surviving classification.
