# Complete Resolution of the Degree-One Integral Prime-Gate Scattering Question

- **ID:** review-2011-2-7-degree-one-integral-gates-resolution
- **Stage:** 3-formalized
- **Type:** FALSIFIED (general scattering axiom class and $p=2$ sector test) + THEOREM (formalized, positive pure-bounce and Selberg rigidity laws)
- **Source:** docs/reports/review-2011/obstacles-summary.md · §2.7
- **Statement:** Every causal, passive, unitary scattering axiom class with the $\zeta$ functional equation and exact degree-one integral local prime gates $g_p^\zeta(w) = (1 - p^{-(2w+1)})/(1 - p^{-2w})$ at all primes admits slow-ringdown systems violating $p=2$ sector cancellation at every positive rate $\delta > 0$; once the single-bounce kernel is globally fixed to the pure modular Beta kernel $B(w,1/2)$, passive unitary degree-one rational prime gates classify into $\{u_p g_p^\zeta, u_p G_p^{\mathrm{flip}}\}$ with poles restricted to $\operatorname{Re} w = -1/2 < -1/4$ (whereas integral-trace degree-two slow modes exist at every prime $p \ge 5$), and all-prime degree-one integral Euler factors in the extended Selberg class collapse without Ramanujan or shift hypotheses to real primitive Dirichlet $L$-functions $L(s,\chi)$ (uniquely $\zeta$ at conductor $q=1$ or with a pole at $s=1$).

## Goal
Resolve the §2.7 breakthrough question and its $p=2$ prime-sector test unconditionally, and isolate and formalize the exact positive classification and rigidity laws once the single-bounce obstruction is removed.

## Gates
- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [x] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 → 3  formalized: Lean theorems verified with `lake --old env lean`

## Formalized Lean 4 Declarations

1. `formal/GaloisForLFunctions/SelbergClass/DegreeOne/IntegralGateRigidity.lean`
   - `GaloisForLFunctions.SelbergClass.DegreeOne.integral_prime_gate_mem_signs`
   - `GaloisForLFunctions.SelbergClass.DegreeOne.exists_full_selberg_of_integral_prime_gates`
   - `GaloisForLFunctions.SelbergClass.DegreeOne.degreeOne_integral_gate_classification`
   - `GaloisForLFunctions.SelbergClass.DegreeOne.degreeOne_integral_gate_eq_zeta_iff`
2. `formal/GaloisForLFunctions/BlackHoleRingdown/DegreeOnePrimeGateRigidityAndIntegralTwins.lean`
   - `GaloisForLFunctions.BlackHoleRingdown.degree_one_rational_prime_gate_classification`
   - `GaloisForLFunctions.BlackHoleRingdown.degree_one_real_prime_gate_classification`
   - `GaloisForLFunctions.BlackHoleRingdown.finite_prime_degree_one_gate_classification`
   - `GaloisForLFunctions.BlackHoleRingdown.flippedEchoKernel_causal_and_laplace`
   - `GaloisForLFunctions.BlackHoleRingdown.finiteFlipped_passive_unitary_and_strip_rigid`
   - `GaloisForLFunctions.BlackHoleRingdown.finiteFlippedReflected_decay_iff`
   - `GaloisForLFunctions.BlackHoleRingdown.finiteFlipped_strip_and_rh_equivalence`
   - `GaloisForLFunctions.BlackHoleRingdown.no_integral_slow_trace_two_or_three`
   - `GaloisForLFunctions.BlackHoleRingdown.integral_trace_degree_two_slow_mode_of_ge_five`
3. `formal/GaloisForLFunctions/BlackHoleRingdown/CompleteResolutionOfDegreeOneIntegralGateQuestion.lean`
   - `GaloisForLFunctions.BlackHoleRingdown.quartet_bounce_euler_factorization`
   - `GaloisForLFunctions.BlackHoleRingdown.quartet_finite_return_sum`
   - `GaloisForLFunctions.BlackHoleRingdown.quartet_mobius_scattering_returns`
   - `GaloisForLFunctions.BlackHoleRingdown.quartet_erase_one_return`
   - `GaloisForLFunctions.BlackHoleRingdown.quartet_repeated_prime_sector`
   - `GaloisForLFunctions.BlackHoleRingdown.quartet_centered_sector_delay`
   - `GaloisForLFunctions.BlackHoleRingdown.quartet_prime_sector_equivalence_and_inverse`
   - `GaloisForLFunctions.BlackHoleRingdown.quartet_correlator_pole_dictionary`
   - `GaloisForLFunctions.BlackHoleRingdown.not_quartetReflected_l2_tail_decay_gt`
   - `GaloisForLFunctions.BlackHoleRingdown.not_quartet_prime_sector_and_tower_decay_gt`
   - `GaloisForLFunctions.BlackHoleRingdown.falsification_of_degree_one_integral_gate_axiom_class`
   - `GaloisForLFunctions.BlackHoleRingdown.complete_resolution_of_degree_one_integral_gate_question`

## Approach & Complete Paper Proofs `[PROVED HERE]`

### Theorem I (Bounce-Agnostic Prime-Sector Calculus and Unconditional Falsification of the General Scattering Axiom Class)
1. **Bounce-agnostic arithmetic return calculus.** For $\sigma \in (1/2, 1)$ and $\gamma > 0$, let $\xi_{\sigma,\gamma}(s) := Q_{\sigma,\gamma}(s)\xi(s)$ where
   $$Q_{\sigma,\gamma}(s) := \left(1 - \frac{s(1-s)}{\rho(1-\rho)}\right)\left(1 - \frac{s(1-s)}{\bar\rho(1-\bar\rho)}\right), \qquad \rho := \sigma + i\gamma.$$
   Its scattering phase factors as $\varphi_{\sigma,\gamma}(w) = B_{\sigma,\gamma}(w)\varphi_\zeta(w)$ with degree-4 Blaschke factor $B_{\sigma,\gamma}(w) = Q_{\sigma,\gamma}(2w)/Q_{\sigma,\gamma}(1+2w)$. On $\operatorname{Re} w > 1/2$,
   $$\int_{\mathbb{R}} e^{-w\tau} K_{\sigma,\gamma}(\tau)\,d\tau = \bigl(B_{\sigma,\gamma}(w) B(w,1/2)\bigr) \prod_{p \in \mathbb{P}} \frac{1 - p^{-(2w+1)}}{1 - p^{-2w}}.$$
   Every local prime gate is identically the degree-one integral $\zeta$ gate $g_p^\zeta(w) = (1 - p^{-(2w+1)})/(1 - p^{-2w})$ ($a_p = 1 \in \mathbb{Z}$ for all $p \in \mathbb{P}$), while the causal dressed single-bounce response of a compact pulse $h$ is
   $$b_{\sigma,\gamma}(h, u) := b(h, u) + \int_0^\infty I_{\sigma,\gamma}(v)\,b(h, u - v)\,dv,$$
   where $I_{\sigma,\gamma}$ is the retarded four-pole impulse tail of $B_{\sigma,\gamma}$ ($\operatorname{Re} p_j \in \{-(1-\sigma)/2, -\sigma/2\} < 0$). Because $I_{\sigma,\gamma}(v) = 0$ for $v \le 0$ and $\int_0^\infty e^{-wv} I_{\sigma,\gamma}(v)\,dv = B_{\sigma,\gamma}(w) - 1$ for all $\operatorname{Re} w > -(1-\sigma)/2$, Fubini's theorem on the modular finite return expansion yields for all $t \le B$ and $\operatorname{supp}(h) \subseteq [-S, S]$:
   $$\sum_{c=1}^{\lceil e^{(B+S)/2}\rceil} \frac{\varphi(c)}{c}\,b_{\sigma,\gamma}(h, t - 2\log c) = \mathcal{R}_{\sigma,\gamma}(h)(t) + B_{\sigma,\gamma}(1/2)\,m(h)\,e^{t/2}.$$
   Consequently, Möbius inversion with weights $\mu(n)/n$, repeated prime-power sector invariance, and the centered prime-sector recurrence
   $$Y_{\sigma,\gamma,p}(h, u) = \left(1 - \frac{1}{p}\right)\mathcal{R}_{\sigma,\gamma}(h)(u) + \frac{1}{p} Y_{\sigma,\gamma,p}(h, u - 2\log p)$$
   hold for every prime $p$. By bounded delay inversion, for every $0 \le \delta < 1/2$, $O(e^{-\delta u})$ decay of $Y_{\sigma,\gamma,p}(h, u)$ is equivalent to $O(e^{-\delta u})$ decay of $\mathcal{R}_{\sigma,\gamma}(h)(u)$, and $Y_{\sigma,\gamma,p}(\mathrm{inverseSectorInput}_p(h), u) = \mathcal{R}_{\sigma,\gamma}(h)(u)$ identically.
2. **Complete eternal-AdS dictionary and falsification at every rate $\delta > 0$.** Since $\xi_{\sigma,\gamma}$ is entire, $s \mapsto 1-s$ symmetric, strictly positive on $\mathbb{R}$, and nonvanishing on $\operatorname{Re} s \ge 1$, its retarded correlator $G_R(\nu) = \varphi_{\sigma,\gamma}(-i\nu)$ and two-boundary Wightman correlator $G_{RL}(\nu)$ satisfy $\operatorname{ord}_{\omega_\eta}(G_R) = \operatorname{ord}_{\omega_\eta}(G_{RL}) = -\operatorname{ord}_\eta(\xi_{\sigma,\gamma}) < 0$ at $\omega_\eta = i(\eta - 1)/2$ for every zero $\eta$ of $\xi_{\sigma,\gamma}$. Given any $\delta > 0$ (in particular $\delta = 1/4$ and $\delta = 3001/48000$), pick $\sigma \in (\max(7/8, 1 - 2\delta), 1)$ and $\gamma > 0$, so $(1-\sigma)/2 < \delta$. For $h_0 = \mathrm{excitingPulse}((\rho - 1)/2)$, bilateral Laplace analytic continuation hits the pole at $w = (\rho - 1)/2$ ($\operatorname{Re} w = (\sigma - 1)/2 > -\delta$). Hence $\mathcal{R}_{\sigma,\gamma}(h_0)$, $Y_{\sigma,\gamma,2}(h_0)$ (for $\delta < 1/2$), the $p=2$ sector $L^2$ tail energy on $g_0 = \mathrm{inverseSectorInput}_2(h_0)$, and the $2^k$ tower cancellation error all strictly fail at rate $\delta$.

### Theorem II.A (Classification and Half-Line Pole Rigidity of Passive Unitary Degree-One Rational Prime Gates on $B(w,1/2)$)
Fixing the single-bounce transform to $B(w,1/2)$, replacing $g_p^\zeta(w) = \frac{p - v}{p(1 - v)}$ ($v = p^{-2w}$) on a finite prime set $S \subset \mathbb{P}$ by locally passive degree-$\le 1$ rational functions $G_p(v) = \frac{c_{p,0} + c_{p,1} v}{d_{p,0} + d_{p,1} v}$ with unitary combined scattering on $i\mathbb{R}$ forces $d_{p,1} = -d_{p,0}$ ($d_{p,0} \ne 0$) and $G_p \in \{u_p g_p^\zeta, u_p G_p^{\mathrm{flip}}\}$ ($|u_p| = 1$, $u_p \in \{-1, +1\}$ for real/integer coefficients), where $G_p^{\mathrm{flip}}(w) = \frac{1 - p \cdot p^{-2w}}{p(1 - p^{-2w})}$. Every flipped ratio $R_p^{\mathrm{flip}}(w) = \frac{1 - p^{1-2w}}{p - p^{-2w}}$ is causal, Schur-contractive on $\operatorname{Re} w \ge 0$, unitary on $i\mathbb{R}$, and nonvanishing with no poles on $-1/2 < \operatorname{Re} w \le 0$ (poles at $\operatorname{Re} w = -1/2$, zeros at $\operatorname{Re} w = +1/2$), giving pulse-by-pulse $O(e^{-\sigma\tau})$ equivalence with `pulseReflected h` for all $0 \le \sigma < 1/2$, unconditional decay below $3001/48000$, and $\delta = 1/4 \iff \mathrm{RiemannHypothesis}$.

### Theorem II.B (Sharpness of Degree One: Integral-Trace Degree-Two Slow Modes for Every Prime $p \ge 5$)
For $p \in \{2, 3\}$, $(2\sqrt{p}, p + 1) \cap \mathbb{Z} = \emptyset$. For every integer $p \ge 5$ (in particular every prime $p \ge 5$), $r = \frac{p + \sqrt{p^2 - 4p}}{2}$ and $u = \frac{p - \sqrt{p^2 - 4p}}{2}$ satisfy $1 < u < r$, $r u = p$, and integral trace $r + u = p \in \mathbb{Z}$, yielding an integral-coefficient causal passive pure-bounce horizon `PositiveEulerHorizon p p` that unconditionally violates quarter-rate decay $\delta = 1/4$.

### Theorem II.C (Unconditional Rigidity of All-Prime Degree-One Integral Euler Products in the Extended Selberg Class)
For $F \in \mathrm{ExtendedSelbergClass}$ of degree $1$ with $a(1) = 1$, coprime multiplicativity, and $a(p^k) = a_p^k$ ($a_p \in \mathbb{Z}$) at all primes $p$ (assuming neither Ramanujan nor $\theta = 0$): conductor periodicity $\|a(n + q)\| = \|a(n)\|$ forces $|a_p| \le 1$ ($a_p \in \{-1, 0, +1\}$), automatically upgrading $F$ to `SelbergClass`; two-prime unique factorization above $q$ forces $\mathrm{internalShift}(F) = 0$ and $F(s) = L(s, \chi)$ for a primitive real/quadratic Dirichlet character $\chi \pmod q$; and $q = 1 \iff \operatorname{ord}_1(F) < 0$, under which $a_p = 1$ for all $p$ and $F = \zeta$.

## No-go closure (mandatory when falsified)
- **Exact killing theorem/mechanism:** `falsification_of_degree_one_integral_gate_axiom_class` (`CompleteResolutionOfDegreeOneIntegralGateQuestion.lean`): dressing `bounceKernel` by the retarded 4-pole impulse of `quartetGate σ γ` preserves every degree-one integral prime gate $g_p^\zeta(w) = (1 - p^{-(2w+1)})/(1 - p^{-2w})$, causality, the $\zeta$ functional equation, real-axis positivity, Schur/Herglotz passivity, axis unitarity, and the $G_R$/$G_{RL}$ pole dictionary, while its bounce-agnostic $p=2$ centered sector recurrence $Y_2(u) = \frac{1}{2}\mathcal{R}_{\sigma,\gamma}(h)(u) + \frac{1}{2}Y_2(u - 2\log 2)$ forces $Y_2$, its $L^2$ tail energy, and the $2^k$ cancellation error to fail at every rate $\delta > (1-\sigma)/2$.
- **Strongest positive survivor:** Formalized in `degree_one_rational_prime_gate_classification`, `finiteFlipped_strip_and_rh_equivalence`, `integral_trace_degree_two_slow_mode_of_ge_five`, `degreeOne_integral_gate_classification`, `degreeOne_integral_gate_eq_zeta_iff`, and `complete_resolution_of_degree_one_integral_gate_question`.
- **New insight:** Separates the bulk worldline single-bounce invariant $B(w,1/2)$ from local Euler-gate rigidity: local degree-one integral gates cannot control bulk Lax–Phillips cavity modes; on pure-bounce $B(w,1/2)$, degree-one rational gates admit a nontrivial flipped integral twin $G_p^{\mathrm{flip}}$ whose poles are trapped at $\operatorname{Re} w = -1/2$ (unlike degree-two integral-trace gates for $p \ge 5$); and in `ExtendedSelbergClass` at degree $1$, prime integrality alone forces Ramanujan, $\theta = 0$, and quadraticity of $\chi$.
- **Status:** Fully proved on paper and unconditionally formalized in Lean 4 across all three modules above.

## Log
- 2026-11-20 — created in 2-fully-proven and promoted to 3-formalized after unconditional Lean 4 verification.
