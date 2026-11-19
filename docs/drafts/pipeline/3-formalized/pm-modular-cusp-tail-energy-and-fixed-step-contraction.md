# Modular cusp tail energy, logarithmic trapping, and fixed-step contraction

- **ID:** pm-modular-cusp-tail-energy-and-fixed-step-contraction
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** [Obstacles summary §2.7](../../../reports/review-1911/obstacles-summary.md#27-a-physical-phenomenon-and-a-way-to-test-it) · [PM](../../../reports/review-1911/route-obstacles.md#pm)
- **Statement:** On $\mathrm{PSL}_2(\mathbb{Z})\backslash\mathbb{H}$, every nonzero compact pulse $h$ has strictly positive reflected tail energy $E_h(T)=\int_T^\infty |r_h(u)|^2\,du>0$ at all $T\in\mathbb{R}$; actual compact pulse families supported in $[-S_0,S_0]$ defeat every proposed fixed-step tail-energy contraction $E_h(T+L)/E_h(T)\le\theta<1$ along every sub-logarithmic horizon $T(\Omega)=T_0+\alpha\log\Omega$ ($\alpha<1/2$), deep in the escaped tail ($0<E_h(T)\le\eta\|h\|_{L^2}^2$, uniformly in all relative phases $\phi\in\mathbb{R}$), and across arbitrarily many separated late staircase epochs; while Agmon–Sobolev regularity $|r_h(T)|^4\le 4E_h(T)E_{h'}(T)$ and horocycle zero-mode readout make zero-free strips $\operatorname{Re}\rho\le 1-2\delta$ ($0<\delta\le 1/4$, and RH at $\delta=1/4$) equivalent to asymptotic tail-energy decay $E_h(T)=O_{h,\varepsilon}(e^{-2(\delta-\varepsilon)T})$ and to pulse-uniform Sobolev-cone decay $E_h(T)\le K_{\sigma,S_0}(\|h\|_{L^2}^2+\|h^{(N_\sigma)}\|_{L^2}^2)e^{-2\sigma T}$ ($\sigma\in(0,\delta)$).

## Lean Formalization

- `GaloisForLFunctions/BlackHoleRingdown/TailEnergy/PolarizationAndPositivity.lean`:
  - `hasDerivAt_tailEnergy`, `tendsto_tailEnergy_atTop`, `tailEnergy_sub_step`, `tailCrossEnergy_sub_step`
  - `tailEnergy_linComb`, `tailEnergy_phaseMix`, `tailEnergy_phase_average`
  - `tailCrossEnergy_eq_polarization`, `stepCrossDecrement_eq_polarization`
  - `pulseAmplitude_eq_zero_of_pulseReflected_decay`, `tailEnergy_pos`, `norm_tailCrossEnergy_sq_lt_mul`
- `GaloisForLFunctions/BlackHoleRingdown/TailEnergy/RegularityAndReceiverEquivalence.lean`:
  - `hasDerivAt_pulseReflected`, `norm_pulseReflected_pow_four_le`
  - `setIntegral_pulseField_horocycle`, `pulseReflected_eq_horocycle_receiver`, `pulseReflected_eq_unit_horocycle_receiver`
  - `re_le_of_pulseReflected_decay`, `exists_sobolev_cone_tailEnergy_decay_of_zeroFree`
  - `zeroFreeStrip_tailEnergy_equivalences`, `riemannHypothesis_iff_tailEnergy_decay`, `not_riemannHypothesis_iff_exists_slower_tailEnergy`, `unconditional_sobolev_cone_tailEnergy_escape`
- `GaloisForLFunctions/BlackHoleRingdown/TailEnergy/FixedStepContractionFalsification.lean`:
  - `echoDelay_and_weight_prime_pow`, `pulseReflected_eq_finite_path_returns`, `stepDecrement_eq_finite_path_returns`
  - `norm_bounce_laplace_lineOne_le`, `exists_norm_scatteringPhase_lineOne_le`
  - `cuspTrappingPulse`, `tendsto_integral_norm_sq_cuspTrappingPulse`, `exists_radiated_energy_cuspTrappingPulse_le`
  - `tendsto_tailEnergy_ratio_sublogarithmic`, `exists_two_pulse_deep_tail_contraction_falsifier`, `exists_multi_epoch_staircase_falsifier`
  - `complete_resolution_of_physical_dephasing_test`

## Theorems and Proofs

Let $r_h=\operatorname{pulseReflected} h$, $E_h(T)=\int_T^\infty |r_h(u)|^2\,du$, $E_{g,h}(T)=\int_T^\infty r_g(u)\overline{r_h(u)}\,du$, and $D_h(T,L)=\int_T^{T+L}|r_h(u)|^2\,du=E_h(T)-E_h(T+L)$ ($L\ge 0$).

1. **Polarization and strict tail positivity (`tailCrossEnergy_eq_polarization`, `tailEnergy_pos`, `norm_tailCrossEnergy_sq_lt_mul`).** Pointwise Hermitian expansion gives $E_{g+e^{i\phi}h}(T)=E_g(T)+E_h(T)+2\operatorname{Re}(e^{-i\phi}E_{g,h}(T))$, opposite-phase averaging $\frac12(E_{g+e^{i\phi}h}(T)+E_{g+e^{i(\phi+\pi)}h}(T))=E_g(T)+E_h(T)$, and four-phase polarization
   $$
   E_{g,h}(T)=\frac14\Big(E_{g+h}(T)-E_{g-h}(T)+i\big(E_{g+ih}(T)-E_{g-ih}(T)\big)\Big).
   $$
   If $E_h(T)=0$ for $h\in C_c^\infty([-S_0,S_0])\setminus\{0\}$, continuity forces $r_h(u)=0$ on $u>T$, hence $\|r_h(u)\|\le C_0 e^{-u}$ on $u\ge 0$. Analytic continuation of $(2w-1)\xi(1+2w)\int_{-B}^\infty e^{-wu}r_h(u)\,du+2m_h\xi(1+2w)e^{(w-1/2)B}=2\pi(1+2w)a_h(-iw)\xi(2w)$ ($B=S_0+1$) to $\operatorname{Re} w>-1$ forces the nonzero exponential-type entire function $F(z)=a_h(z/2+i/4)$ to vanish at every simple critical ordinate $t>0$ of $\xi(1/2+it)=0$, contradicting Jensen's $O(1+T)$ upper bound (`exists_xiSimpleCriticalZeroCount_linear_of_cofinite_exponentialType_zeros`) against Alpöge–Furman's $\frac{1}{72\pi}T\log T$ lower bound (`eventually_superlinear_xiSimpleCriticalZeroCount`). Thus $E_h(T)>0$ at all $T\in\mathbb{R}$, and $|E_{g,h}(T)|^2<E_g(T)E_h(T)$ for every $\mathbb{C}$-linearly independent pair $(g,h)$.

2. **Local regularity, horocycle receiver, and five-way strip/RH equivalence (`norm_pulseReflected_pow_four_le`, `pulseReflected_eq_horocycle_receiver`, `zeroFreeStrip_tailEnergy_equivalences`).** Dominated differentiation gives $r_h'(T)=r_{h'}(T)$. Integrating $\partial_u|r_h(u)|^2$ on $[T,B]$, applying $2|r_h||r_{h'}|\le c|r_h|^2+c^{-1}|r_{h'}|^2$, using $\inf_{B\ge T}|r_h(B)|^2=0$, and optimizing over $c>0$ gives $|r_h(T)|^4\le 4E_h(T)E_{h'}(T)$. For $\operatorname{supp} h\subseteq[-S_0,S_0]$ and $T+2\log Y>S_0$, `setIntegral_pulsePacket` yields $r_h(T)=Y^{-1/2}\int_0^1 \mathcal{F}_h(T+\log Y,x,Y)\,dx$. Combining `pulseAmplitude_eq_zero_of_pulseReflected_decay` on `excitingPulse` with contour shifting and $(1+|\operatorname{Re} w|)^N\le 2^N(1+\|w\|^N)$ establishes, for $0<\delta\le 1/4$, the five-way equivalence between $\operatorname{Re}\rho\le 1-2\delta$ ($\operatorname{Re}\rho>0$), bulk $\mathcal{F}_h$ ringdown, pointwise $r_h$ decay, $E_h(T)=O_{h,\varepsilon}(e^{-2(\delta-\varepsilon)T})$, and pulse-uniform Sobolev-cone escape
   $$
   \forall \sigma\in(0,\delta),\ \forall S_0>0,\ \exists N\in\mathbb{N},\ \exists K>0,\ \forall h\in C_c^\infty([-S_0,S_0]),\ \forall T\ge 0,\ E_h(T)\le K\big(\|h\|_{L^2}^2+\|h^{(N)}\|_{L^2}^2\big)e^{-2\sigma T}.
   $$
   This holds unconditionally for $0<\sigma<3001/48000$ (`unconditional_sobolev_cone_tailEnergy_escape`) and is equivalent at $\delta=1/4$ to `RiemannHypothesis` (`riemannHypothesis_iff_tailEnergy_decay`, `not_riemannHypothesis_iff_exists_slower_tailEnergy`).

3. **Path-return invariance and unconditional falsification of fixed-step contraction (`echoDelay_and_weight_prime_pow`, `stepDecrement_eq_finite_path_returns`, `exists_radiated_energy_cuspTrappingPulse_le`, `exists_two_pulse_deep_tail_contraction_falsifier`, `exists_multi_epoch_staircase_falsifier`).** Every prime power $c=p^k$ ($k\ge 1$) has travel time $2k\log p$ and multiplicity-invariant weight $\varphi(p^k)/p^k=1-1/p$, and for mean-zero $h$ supported in $[-S_0,S_0]$, $D_h(T,L)$ is determined by the finite denominator sum $1\le c\le \lceil e^{(T+L+S_0)/2}\rceil$. On $\operatorname{Re} w=1$, vertical Gamma bounds give $\|\int_0^\infty e^{-(1+iy)v}(1-e^{-v})^{-1/2}\,dv\|=\|B(1+iy,1/2)\|\le \sqrt{2\pi/(1-e^{-2})}|y|^{-1/2}$ ($|y|\ge 1$) and $\|\varphi(1+iy)\|\le C_{\mathrm{sc}}(1+|y|)^{-1/2}$. For $p_\Omega=\frac{1}{1+i\Omega}\operatorname{meanZeroPulse}(e^{i\Omega\cdot}b_0)$ ($\operatorname{supp} b_0\subseteq[-S_0,S_0]$), $\Omega\ge 1$, and $T\in\mathbb{R}$,
   $$
   0 \le \|p_\Omega\|_{L^2}^2 - E_{p_\Omega}(T) \le K_{\mathrm{trap}}(S_0)e^{2T}\Omega^{-1},\qquad \lim_{\Omega\to\infty}\|p_\Omega\|_{L^2}^2=\|b_0\|_{L^2}^2>0.
   $$
   Consequently: (a) $\lim_{\Omega\to\infty}E_{p_\Omega}(T_0+\alpha\log\Omega+L)/E_{p_\Omega}(T_0+\alpha\log\Omega)=1$ for every $\alpha<1/2$ and $L\in\mathbb{R}$; (b) superposing an escaped pulse $g$ with a scaled packet $e^{i\phi}w$ defeats every $(L>0,T_0,\eta\in(0,1),\theta<1)$ simultaneously for all relative phases $\phi\in\mathbb{R}$ while $0<E_{g+e^{i\phi}w}(T)\le \eta\|g+e^{i\phi}w\|_{L^2}^2$; and (c) inductive superpositions produce a single mean-zero pulse supported in $[-S_0,S_0]$ that sheds $>1-\eta$ of its remaining energy between $K+1$ separated late windows yet satisfies $E_h(T_i+L)/E_h(T_i)>\theta$ on every window $i$.

## No-go closure
- **Exact killing theorem/mechanism:** `exists_radiated_energy_cuspTrappingPulse_le`, `exists_two_pulse_deep_tail_contraction_falsifier`, and `exists_multi_epoch_staircase_falsifier`: on $\operatorname{Re} w=1$, the bounce Beta factor decays as $O(|y|^{-1/2})$ while imaginary-axis unitarity $|\varphi(i\xi)|=1$ conserves total $L^2$ energy, trapping $1-O(e^{2T}\Omega^{-1})$ of a carrier-$\Omega$ wavepacket past every sub-logarithmic horizon $T_0+\alpha\log\Omega$ ($\alpha<1/2$) and defeating every fixed-step contraction $\theta<1$ even deep in the escaped tail across all relative phases $\phi\in\mathbb{R}$.
- **Strongest positive survivor:** (1) Eternal tail positivity `tailEnergy_pos` ($E_h(T)>0$) and parameter-free Agmon–Sobolev local regularity `norm_pulseReflected_pow_four_le` ($|r_h(T)|^4\le 4E_h(T)E_{h'}(T)$); (2) Pulse-uniform Sobolev-cone replacement law `exists_sobolev_cone_tailEnergy_decay_of_zeroFree`, unconditional for $0<\sigma<3001/48000$ (`unconditional_sobolev_cone_tailEnergy_escape`) and equivalent across $0<\sigma<1/4$ to `RiemannHypothesis` (`riemannHypothesis_iff_tailEnergy_decay`).
- **New insight:** Pure $L^2\to L^2$ fixed-step Markovian contraction of cusp tail energy is unconditionally false on $\mathrm{PSL}_2(\mathbb{Z})\backslash\mathbb{H}$ even when asymptotic exponential decay holds; exponential cusp escape is intrinsically a derivative-losing $H^N([-S_0,S_0])\to L^2([T,\infty))$ phenomenon governed by the logarithmic cusp excursion delay $\sim\log\Omega$.
- **Status:** Unconditionally formalized and verified in `GaloisForLFunctions/BlackHoleRingdown/TailEnergy/` (`PolarizationAndPositivity.lean`, `RegularityAndReceiverEquivalence.lean`, `FixedStepContractionFalsification.lean`); axioms `[propext, Classical.choice, Quot.sound]`.
