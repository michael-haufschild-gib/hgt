# Trans-Horizon Incidence Mechanics (THIM)

Namespace `GaloisForLFunctions.TransHorizonIncidenceMechanics`; umbrella
`TransHorizonIncidenceMechanics.lean`. Sieve objects come from BVI and BSU; Markov/chain/theta/Haar
objects from `RHTower`.

**Question.** A divisor sieve of horizon $N$ reads $k$ through divisors $d\le N$. What can this
finite observer recover and bound far beyond its horizon ($k\gg N$), and how do its observations
transfer to RH-equivalent energies (signed sieve energies, Fermi–Nyman traces, odd-sector Markov
chains)? *Incidence* is $d\mid k$; *mechanics* is conservation/dissipation under $k\mapsto k+1$,
$N\mapsto N+1$, $k\mapsto pk$; *trans-horizon* concerns omitted divisors.

---

## 1. Place in the research

THIM is the **finite-observer theory of signed arithmetic receivers**. Central lesson: exact
recovery, good conditioning and period-variance bounds do **not** pay the centred-prefix pronic
energy $\sum_{n\le T}A_c(n)^2/(n(n+1))$. Two thresholds organise everything: sign-blind payment needs
damping $>\tfrac12$; signed horizon-limit commutation holds exactly from $\tfrac12$. Below $\tfrac12$
an infinite source can be paid while its truncated rows are not.

| Neighbour | Interface |
|---|---|
| BezoutValuationIncidence | Selberg coordinates, successor polarization, window Poincaré, Vaughan pronic calibration, cofinal Möbius slope |
| BiScaleUncertainty | Full-period observation theory, packets, Chebyshev gauge |
| ArithmeticContinuationAndCriticalEnergy | Transports the receiver in damping/cutoff; THIM locates the boundary |
| ArithmeticCompensationTheory | Whether signed derivative work is paid without restating admission |
| ScaleSignedIncidenceCriticality | Abstracts parity pairs into limits on what a reading can prove |
| SignedArithmeticEnergyIncidence | Keeps source and cross terms from receiver data to energy |
| ArithmeticCriticalityTheory, ArithmeticIncidencePositivity | Odd-sector and crossing-pair forms of the nine-moduli obstruction |
| ArithmeticOrientationTheory | Even flip as orientation at the prime 2; parity barrier |
| SignedSuccessorArithmetic | Möbius orientation in successor/coprime-factor observations |
| ArithmeticDefectRigidity | Same pronic receiver via cofactor energy $E=F+G-2Q$ |
| TransThresholdPairCorrelation | Parity barrier at close prime pairs |

---

## 2. Why: the horizon barrier and the receivers

Below the horizon ($M+1\le N$) the renormalized defect is nonpositive because the truncated
divisor sum is complete. Above it, omitted divisors at a highly composite endpoint can make
$|s_{N,c}(M+1)|>|s_{N,c}(1)|$, reversing the boundary sign in Dirichlet polarization. THIM locates
every such failure and extracts what survives.

**Three RH receivers**, each needing a horizon-uniform estimate on a literal source:

1. *Interior pronic energy.* $c_\varepsilon(d)=\mu(d)d^{-\varepsilon}$, Bézout interior prefix
   $I_\varepsilon$: if $\forall\delta\,\exists\varepsilon<\delta\,\sup_T\sum_{n\le T}I_\varepsilon(n)^2/(n(n+1))<\infty$ then RH.
   Known for $\varepsilon\ge\tfrac12$.
2. *Odd-sector positivity.* RH ⇔ the arithmetic Markov resolvent has no odd eigenvalue in
   $(\tfrac12,1)$ ⇔ cosh mass $\le$ archimedean Doob jump + same-side prime jumps + bipartite chain
   variances, for odd $v\in C^2_c$.
3. *Nyman–Beurling.* RH ⇔ $\mathbf1_{(0,1]}\in\overline{\operatorname{span}}\{\{1/(kx)\}\}$; origin tail
   $\int_N^\infty|\sum a_k\{u/k\}|^2du/u^2$ (a tail bound alone identifies neither weak limit nor bulk).

---

## 3. Objects and language

**Sieve.** $s_{N,c}(k)=\sum_{d\mid k,d\le N}c(d)$ (`sieveSeq`); Selberg coordinates
$Y_{N,c}(e)=\sum_{e\mid d\le N}c(d)/d$ (`selbergMultiplesCoord`). Complete invariant: $\gcd(k,L_N)$,
$L_N=\operatorname{lcm}(1..N)$; radical state $\gcd(k,N\#)$. $N$-rough integers form a monoid;
rough-prime boundary = prime $p\in(N,2N)$ with its 4-divisible neighbour.

**Weights.** $\mu$; $c_\varepsilon$ with $\tau_\varepsilon(n)=\prod_{p\mid n}(1-p^{-\varepsilon})$; Ramanujan
coefficients $w_\varepsilon(e)=\rho_\varepsilon\mu(e)/D_\varepsilon(e)$, $\rho_\varepsilon=1/\zeta(1+\varepsilon)$; PM cofactor
row $c_Q$.

**Energies.** $Q_{\rm Sel}=\sum\varphi(e)Y^2$; $Q_{\rm Bez}$ (coprime pairs); successor reserve
$\mathcal R_N=\sum_{e\ge2}(\varphi-\mu)(e)Y(e)^2$; renormalized defect $\widetilde{\mathcal D}_N(M)=\mathcal D_N(M)-M\mathcal R_N$;
primitive energy $12\mathcal E_{\rm prim}=\sum J_2(q)Y(q)^2$; period covariance $\sum c_e(h)Y(e)^2$.
**Dirichlet polarization** (every sign statement passes through it):
$2\widetilde{\mathcal D}_N(M)=-\sum_{k\le M}(s(k+1)-s(k))^2+s(M+1)^2-s(1)^2$.

**Horizon steps.** Band index $B=\lfloor M/m\rfloor$; Buchstab slope $\lambda(p)=1-2\mathfrak m(p-1)$,
$\mathfrak m(x)=\sum_{d\le x}\mu(d)/d$; smooth core $\gcd(m,B\#)$; band average $A(B)$; damped crossover
$\Lambda(\varepsilon)=\log(1/2\rho_\varepsilon)/\varepsilon$.

**Scale regimes.** $k\le N$ complete; $(N,2N]$ one omitted divisor; $(B+1)N$ at most $B$ omitted
quotients; unit envelope for $k<5(N+1)$; radical ratio $<11$: Möbius responses $\le2$;
$M\ge2N^2+2N-2$: long-window dissipation.

**Fermi.** Cell response $F_{N,c}(n)=\sum c(d)(2\lfloor n/2d\rfloor-\lfloor n/d\rfloor)$; pronic weight
$1/(n(n+1))$; dyadic rays; schedules and slots; inverse constants $K_N$, $K^{\rm all}_N$.

**Clocks.** $\tau(q)=q/\operatorname{rad}q$ (`lagVisibilityClock`): $c_q(h)/\varphi(q)$ sees $q$ iff
$\tau(q)\mid h$.

**Odd sector.** Riemann kernel $\Theta$; odd profile $m_a=(\Theta(\cdot-a)-\Theta(\cdot+a))/(2\sinh\frac a2)$;
source graph energy, ground vector, resolvent; pole moment $\langle q,\tanh_L\rangle$.

**Receiver classes.** $E_T(c)=\sum_{n\le T}A_c(n)^2/(n(n+1))$, $A_c(n)=\sum_{j\le n}((c*1)(j)-W_c(1))$;
*paid* = `ReceiverBounded`. Damped class $|c(d)|\le Kd^{-\varepsilon}$. Sign-blind data: $|W_c|$, period
statistics, pronic mode masses. Parity pair: same sign-blind data, one paid, one not. Critical
Wiener algebra $\sum|g(q)|q^{-1/2}<\infty$; first pronic moment $M(c)=-\sum\Lambda(e)W_c(e)$; even flip $c^\flat$.

**Selectivity classes.** I Beurling-universal; II sign-blind ($(\mathbb Z/2)^N$-invariant); III
Bézout-selective ($\gcd(n,n+1)=1$, $pa-qb=1$). Only III can carry new information.

---

## 4. Mechanisms

1. **Rough absorption.** $s_N(qr)=s_N(q)$ for rough $r$; at rough checkpoints boundary squares cancel
   ⇒ defect $\le0$ for every weight, sharp.
2. **Horizon filtration.** $s_N(k)=\sum_{d\mid k}c(d)-\sum_{q\mid k,k/q>N}c(k/q)$; radical envelope
   $|s_{N,\mu}(r)|\le2^{\omega(r)-2}$.
3. **Envelope ladder.** Unit envelope exact below ratio 5; rungs 2 below 11, 3 below 13. Ratio 11 is
   the Möbius sign boundary. Endpoint-square methods die at ratios $(\log N)^{O(1)}$.
4. **Global defect sign.** Polynomial windows: rough-prime boundaries dissipate $\ge4^{-\varepsilon}$
   each; long windows: MV on step differences gives Poincaré constant $2N(N-1)$. Together: all
   prefixes nonpositive at large horizons, uniformly in $\varepsilon\in[0,1]$.
5. **Period laws.** Variance/correlation/Dirichlet are linear in $(Q_{\rm Sel},Q_{\rm Bez},\mathcal R)$;
   torus Poincaré constant $\le1$. Möbius observer is **white**: lag covariances → 0, variance →
   cofinal slope $\ge1/288$.
6. **Buchstab calculus.** Horizon step formula; large prime horizons **inject** energy for Möbius;
   step depends only on the smooth core; $A(B)<0$ for $B\le9$, $A(10)>0$.
7. **Damped observer.** Freezes into $\tau_\varepsilon$; exact linear dissipation $\to-(B+1)R(\varepsilon)$;
   damped prime horizons dissipate beyond $\Lambda(\varepsilon)$. Variance and damping limits **do not
   commute**. Primitive energy $\asymp N^{1-2\varepsilon}$ below ½: only pronic weights work there.
8. **Observation and recovery.** State is not dynamics beyond $N=2$; Möbius-inversion recovery with
   exact amplification; short windows classified by endpoint states.
9. **Fermi observability.** Schedule injective iff at most one of $L+2$ slots missing;
   $K_N\sim\frac4{\pi^2}(\log_2N)^2$. Wavelet identity reduces bulk and origin-tail tightness to a
   subpower prefix bound.
10. **Odd quotient.** sourceEnergy $=$ weilForm $+2\langle q,\tanh_L\rangle^2$ on odd vectors (polar shift
    is a gauge); RH ⇔ cross-lobe bound $\mathrm{weilBilin}(q^+,q^-)\le\tfrac12\langle q_1,\tanh_L\rangle^2$.
11. **Collar transport and nine moduli.** Midpoint reflection to one-point diagonal potentials:
    atom-minus-pole total excess positive iff $d\in\{2,3,4,5,7,8,9,11,13\}$. **Light-cone variation:**
    profile variance replaces the Lévy drop by the Weil jump difference
    $\kappa(s)-\kappa(s+2y)\ge4\sinh\frac y2\sinh\frac{y+s}2$, so large aperture pays all $\log d\le a-R$
    with an $\varepsilon$-fraction of continuum energy.
12. **Absorption boundary.** cosh/sinh ratio $\ge\pi e^{2x-5\log2/4}$: no fixed absorption coefficient.
13. **Parity calculus.** Hyperbola split of $A_c$; positive weights paid iff $\sum M_k^2/2^k<\infty$;
    character/Liouville/Fermi parity pairs; even flip invisible to translated moments of every degree;
    log-moment hierarchy $M(c\log^k)=-\sum\Lambda_{k+1}W_c$ separates every pair (qualitatively).
14. **Pole law and Wiener closure.** Critical Wiener convolution preserves payment; drift forces pole
    cancellation $K(1-\varepsilon)=0$.
15. **Mellin boundary energy.** Paid ⇒ $\zeta(s)(C(s)-m)$ holomorphic on $\Re s>\tfrac12$; at ½: payment
    ⇔ bounded line energy of $\zeta(s)(C(s)-m)/s$.
16. **Horizon-limit commutation.** Uniformly paid rows ⇔ paid limit exactly for $\varepsilon\ge\tfrac12$;
    below, lacunary dipoles break it.
17. **Multiplicative phase diagrams.** Euler-log pinching; quarter law for flips; integer local
    exponents below ½; phase law reads only $\Re(ae^{i\varphi})$; Dini law for divergent-mass defects.
18. **Probe spectroscopy.** $d^{-\varepsilon}\cos(t\log d)$ paid iff $\zeta(1-\varepsilon+it)=0$; half-damped
    probe energy $/\log T\to|\zeta(\frac12+it)|^2/(2|\frac12+it|^2)$.
19. **Actual source.** Power saving for $\sum(\mu\star\Lambda)$ at $\beta$ pays Möbius for $\varepsilon>\beta/2$;
    admission infimum $=\Theta-\tfrac12$; anti-alignment gap ⇔ non-admission of probes.
20. **Signed interior energy.** Interior energy = diagonal of a 25-entry signed Vaughan Gram + mixed
    remainder; diagonal sign-blind; leading matrix rank one; bounded ⇔ $|1+R^{\rm mix}/D|=O(1/T)$.

---

## 5. Pillar theorems

1. **All-prefix defect sign at large horizons**, uniform in $\varepsilon\in[0,1]$
   (`eventually_pmPowerDamped_renormalizedDefect_nonpos_uniform`).
2. **White Möbius observer** (`tendsto_periodCorrelation_moebius`, `one_div_288_le_cofinalMobiusSlope`).
3. **Parity barrier**: sign-blind data decide payment iff $\varepsilon>\tfrac12$
   (`receiverBounded_amplitudeInvariant_iff`, `parity_barrier`).
4. **Damping = zero width** (`receiverDampingRate_eq_zetaZeroAbscissa_sub_half`,
   `riemannHypothesis_iff_forall_pos_receiverBounded_moebius`).
5. **Horizon-limit commutation exactly from ½** (`horizonLimit_commutes_with_receiver_iff`).
6. **Half-damped boundary energy** (`receiverBounded_iff_exists_lineEnergy_le`).
7. **Zero-divisor spectroscopy** (`receiverBounded_oscillatingSmoothPower_iff`).
8. **Odd quotient cross-lobe reduction** (`riemannHypothesis_of_odd_eigenvector_cross_lobe_weilBilin_le_tanhL_sq`).
9. **Selectivity classes** (`selectivity_class_III_bezout_successor_selective_laws`).

---

## 6. Traps

| Trap | Why it fails |
|---|---|
| Full period is $N!$ | Least period divides $\operatorname{lcm}(1..N)$ |
| Period diagonalization controls moving windows | Short windows are classified by endpoint states |
| Ratio 5 is a sign boundary | Unit envelope fails at $5N+5$; sign boundary is 11 |
| Endpoint-square methods reach every scale | Die at ratios $(\log N)^{O(1)}$ |
| Möbius = $\varepsilon\to0$ limit of damped | Variance, dissipation, profile limits do not commute |
| Prime horizons dissipate | Möbius large primes inject |
| Complete-period averages bound the discrepancy below ½ | Primitive energy diverges; pronic weighting essential |
| Nyman tail with $dx/x^2$ | Correct transform $\int_N^\infty|\cdot|^2du/u^2$ |
| $\Lambda(d)=\log(d/\tau(d))$ always | $\Lambda(6)=0$ |
| Finite observability ⇒ source estimate | Recovery says nothing about cancellation |
| Injective selected trace ⇒ uniform coercivity | Constant grows like $(\log_2N)^2$ |
| Polar shift is a parameter | It is a gauge |
| Lobe-local inequality settles the odd sector | RH is a cross-lobe statement |
| More sign-blind observables narrow the gap | Blindness closed under post-processing; floor stays ½ |
| One admissible damping bounds the width | Width = infimum of the derived set |
| Higher-degree moments see squarefree parity | Even flip invisible at every degree |
| Separating observables bound the receiver | Separation is qualitative |
| Probe payment is a Möbius estimate | Möbius series $1/\zeta(s+\varepsilon)$ is the unknown |
| Absolute bounds on Vaughan pieces | Squared majorant nonsummable; content is off-diagonal signs |

---

## 7. Open problems

1. **Möbius receiver at one fixed $\varepsilon<\tfrac12$.** Bound $\sup_T(\sum_iG_{ii}+R^{\rm mix}_T)$
   unconditionally, then cofinally as $\varepsilon\downarrow0$. Arithmetic form:
   $|\sum_{e\le N}(\mu\star\Lambda)(e)|\le CN^\beta$, $\beta<1$. Must use Class III information.
   Complementary coordinate: the signed forcing–cofactor pairing $Q$ of ArithmeticDefectRigidity.
2. **Small horizons.** Close the gap between $N\le12$ and the eventual regime.
3. **Buchstab.** Sign pattern of $A(B)$ beyond 10; a damped deformation commuting with the cofinal limit.
4. **Odd sector.** The cross-lobe bound, or pay the low-prime/inner-end region left after the
   light-cone budget.
5. **Fermi–Nyman.** Möbius origin-tail tightness below $\Theta/2$ without zero-free input; identify
   weak limits of bounded Nyman rows.
6. **Horizon-row gap** for $\Theta-\tfrac12<\varepsilon\le\Theta/2$.
7. **From separation to bound.** An exponent for a separating observable; quantitative Class III laws
   controlling off-diagonal Vaughan entries.

## 8. Tools to build

A signed Möbius bound below ½; a Class III estimate for off-diagonal Vaughan entries; the odd
cross-lobe bound.

## 9. Conventions

- Fix weight class, ranges of $k,M,N$, band/ratio, polynomial or long-window regime.
- Keep horizon and damping limits ordered; state nested eventual quantifiers.
- Audit signs through polarization with boundary squares; period laws through Selberg/Ramanujan.
- Capstones take data (`c`, `N`, `M`, `ε`, `S`); no assumed positivity, cancellation or zero location.
