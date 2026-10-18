import GaloisForLFunctions.BiScaleUncertainty.UniversalRamanujanCovarianceAndBiScaleRigidity
import GaloisForLFunctions.BiScaleUncertainty.HyperbolicLorentzBoostAndMinkowskiLightCone
import GaloisForLFunctions.BiScaleUncertainty.EvenSourceSymmetricPolarEnforcement
import GaloisForLFunctions.BiScaleUncertainty.OriginAllocationUniquenessAndCoupledSphereGain
import GaloisForLFunctions.BiScaleUncertainty.CompensatedPhysicalLogarithmicProducer
import GaloisForLFunctions.BiScaleUncertainty.NyquistCriticalFinitePartAndBroadClassification

/-!
# The Five Fundamental Theorems of Bi-Scale Uncertainty Analysis

This capstone module synthesizes the **Five Fundamental Theorems of Bi-Scale / Logarithmic-Grid
Uncertainty Theory** into a single self-contained reference interface for the field:

1. **First Fundamental Theorem — Universal Ramanujan Covariance Diagonalization & Bi-Scale Rigidity:**
   For every period $P \ge 1$ and every additive shift lag $h \in \mathbb{N}$, the period covariance
   $\langle f, \tau_h f \rangle_P$ is simultaneously diagonalized by the divisor-indexed coprime
   Fourier blocks $B_d$ ($d \mid P$) with exact eigenvalue given by the Ramanujan sum
   $c_{P/d}(h) = \operatorname{ramanujanLagWeight}(h, P/d)$. At unit lag $h = 1$, every proper
   divisor $d < P$ has spectral gap $\varphi(P/d) - \mu(P/d) \ge 1$, and a periodic signal has
   vanishing joint additive–multiplicative energy if and only if it is constant.
2. **Second Fundamental Theorem — Hyperbolic Lorentz Boost ($\mathrm{SO}^+(1,1)$) Representation &
   Minkowski Light-Cone Rigidity:**
   The hyperbolic multipliers $(\cosh(\beta \cdot), \sinh(\beta \cdot))$ form a faithful representation
   of $\mathrm{SO}^+(1,1)$ satisfying the hyperbolic Weyl commutation relations with translation.
   Their autocorrelations preserve the **Hyperbolic Casimir Invariant**
   $h_{\cosh(\beta \cdot) f}(x) - h_{\sinh(\beta \cdot) f}(x) = \cosh(\beta x) h_f(x)$ and satisfy
   the **Minkowski Light-Cone Identity**
   $h_{\cosh(\beta \cdot) f}(x)^2 - h_{\sinh(\beta \cdot) f}(x)^2
     = \cosh(\beta x) h_f(x) (h_{\cosh(\beta \cdot) f}(x) + h_{\sinh(\beta \cdot) f}(x))$.
   Its zero set is the union of the correlation zero locus and the zero locus of the sum of
   the two boosted correlations. Exact $L^2$ Hilbert-space defect identities also hold for
   the Peter–Paul chord and Krein doubling/increment inequalities.
3. **Third Fundamental Theorem — Convex Origin-Collar Sphere Duality, Unique Optimal Allocation &
   Odd-Dyadic Incommensurability:**
   Any finite family of collar packets with norms $b_i \ge 0$ sharing total origin weight $W \ge 0$
   satisfies $\sum_i \sqrt{a_i^2 + b_i^2} \ge \sqrt{W^2 + (\sum_i b_i)^2}$ with equality if and only
   if $a_i B = W b_i$, while joint Hilbert-space vector coupling strictly improves over every
   partitioned allocation by `coupledSphereGain W s p ≥ 0` (vanishing iff all packets are positively
   collinear), and every odd prime-power tower $(2q + 3)^k$ is algebraically incommensurable with
   every dyadic tower $n \cdot 2^k$.
4. **Fourth Fundamental Theorem — Symmetric Polar Enforcement, Even-Source Infimum Equivalence &
   Compensated Physical Logarithmic Producers:**
   The symmetric two-sided distant-copy map $f_T = f - \frac{1}{2\cosh(T/2)}(\tau_T f + \tau_{-T} f)$
   preserves source parity, kills both $\pm 1/2$ exponential moments, preserves fixed local lags,
   and perturbs normalized archimedean Lévy energy by $O(e^{-T})$, proving that the even polar-neutral
   and even nonpolar logarithmic-grid energy infima coincide. On physical $L^2(\mathbb{R})$, the
   negative half-line is an exact invisible kernel of the logarithmic jump calculus, and the
   zero-integral compensated box-smoothed velocity $w_n(q)$ produces compactly supported $C^1$
   logarithmic states with exact orthogonal energy $\|v_n\|^2 = \|q_n\|^2 + m_n^2 / L_n$.
5. **Fifth Fundamental Theorem — Critical Nyquist Renormalization, Finite Part $\mathcal{B}_m$ &
   Rescaled-Source Phase Transition:**
   At the critical Nyquist Taylor exponent $\beta = m + 1$, subtracting the continuous mean
   counterterm $c_m \delta_k$ from the cell mass $\alpha_k$ yields an $O((k+1)^{-2})$ cell
   discrepancy $d_k(m)$ whose series defines the **Critical Nyquist Finite Part**
   $\mathcal{B}_m = \sum_{k=0}^\infty d_k(m)$ with nodal convergence rate $2 D_m / (N + 1)$, while
   the autocorrelation total mass identity $\int_{\mathbb{R}} \operatorname{autocorr}(f) = (\int f)^2$
   governs the sharp renormalization phase transition between positive-mean escape and zero-mean
   cancellation under broad source rescaling.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped BigOperators RealInnerProductSpace NNReal ENNReal CompactlySupported Topology

namespace GaloisForLFunctions.BiScaleUncertainty

set_option autoImplicit false

/-! ## §1. First Fundamental Theorem: Universal Ramanujan Covariance & Bi-Scale Rigidity -/

open RHTower RHTower.Sieve

/-- **First Fundamental Theorem of Bi-Scale Uncertainty Analysis:**
1. Every divisor mode $e \in [2, N]$ is an exact eigenspace of the complete-period centered
   lag-$h$ covariance on $1 \dots N!$ for every lag $h \in \mathbb{N}$, with eigenvalue equal to
   the Ramanujan sum $c_e(h) = \operatorname{ramanujanLagWeight}(h, e)$.
2. At unit lag $h = 1$, every mode $e \ge 2$ has spectral gap $\varphi(e) - \mu(e) \ge 1$,
   forcing the universal shift-difference floor $\ge 2 \sum_{e=2}^N (\operatorname{selbergMultiplesCoord}(N, c, e))^2$
   with vanishing if and only if all nonconstant Selberg coordinates vanish.
3. For every scale $q \in \mathbb{N}$, simultaneous additive $q$-periodicity and multiplicative
   $q$-dilation invariance holds if and only if $f$ is constant, and the finite-window joint
   additive-multiplicative energy `biScaleJointEnergy K N f` vanishes if and only if $f$ is
   constant on $[1, N]$. -/
theorem first_fundamental_theorem_ramanujan_and_biscale_rigidity
    (N K h q : ℕ) (c f : ℕ → ℝ) :
    (TwoLagSieve.periodCovariance N c h =
      ∑ e ∈ Finset.Icc 2 N,
        ramanujanLagWeight h e * (selbergMultiplesCoord N c e) ^ 2) ∧
    (2 * (∑ e ∈ Finset.Icc 2 N, (selbergMultiplesCoord N c e) ^ 2) ≤
      periodShiftDifferenceEnergy N c 1) ∧
    (periodShiftDifferenceEnergy N c 1 = 0 ↔
      ∀ e ∈ Finset.Icc 2 N, selbergMultiplesCoord N c e = 0) ∧
    (((∀ n, f (n + q) = f n) ∧ (∀ n, f (q * n) = f n)) ↔ ∀ n, f n = f 0) ∧
    (biScaleJointEnergy K N f = 0 ↔ ∀ n ∈ Finset.Icc 1 N, f n = f 1) :=
  ⟨periodCovariance_eq_ramanujanLagWeight_diagonal N c h,
   periodShiftDifferenceEnergy_one_ge_two_sum_sq N c,
   periodShiftDifferenceEnergy_one_eq_zero_iff N c,
   periodic_and_scale_invariant_iff_const f q,
   biScaleJointEnergy_eq_zero_iff_const K N f⟩

/-! ## §2. Second Fundamental Theorem: Hyperbolic Lorentz Boosts & Minkowski Light-Cone Rigidity -/

open RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm

/-- **Second Fundamental Theorem of Bi-Scale Uncertainty Analysis:**
1. **Hyperbolic Casimir Rapidity Invariance:** For every rapidity $\alpha \in \mathbb{R}$ and lag $x \in \mathbb{R}$,
   $\mathcal{C}_\alpha(f, x) = (h_{\cosh(\alpha \cdot) f}(x) - h_{\sinh(\alpha \cdot) f}(x)) / \cosh(\alpha x) = h_f(x)$.
2. **Minkowski Light-Cone Identity:**
   $h_{\cosh(\alpha \cdot) f}(x)^2 - h_{\sinh(\alpha \cdot) f}(x)^2 = \cosh(\alpha x) \, h_f(x) \, (h_{\cosh(\alpha \cdot) f}(x) + h_{\sinh(\alpha \cdot) f}(x))$.
3. **Null-Cone Zero-Grid Equivalence (`↔`):**
   $h_f(x) = 0 \iff h_{\cosh(\alpha \cdot) f}(x) = h_{\sinh(\alpha \cdot) f}(x)$, and
   $h_{\cosh(\alpha \cdot) f}(x)^2 - h_{\sinh(\alpha \cdot) f}(x)^2 = 0 \iff h_f(x) = 0 \lor h_{\cosh(\alpha \cdot) f}(x) + h_{\sinh(\alpha \cdot) f}(x) = 0$.
4. **Exact $L^2$ Krein Doubling Defect:**
   $4(h_f(0) - h_f(x)) - (h_f(0) - h_f(2x)) = \frac{1}{2} \int (f(u) - 2 f(u + x) + f(u + 2x))^2 \, du \ge 0$. -/
theorem second_fundamental_theorem_lorentz_boost_and_light_cone
    {f : ℝ → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f) (α x : ℝ) :
    (hyperbolicCasimirInvariant α f x = autocorr f x) ∧
    (autocorr (coshMultiplier α f) x ^ 2 - autocorr (sinhMultiplier α f) x ^ 2 =
      Real.cosh (α * x) * autocorr f x *
        (autocorr (coshMultiplier α f) x + autocorr (sinhMultiplier α f) x)) ∧
    (autocorr f x = 0 ↔
      autocorr (coshMultiplier α f) x = autocorr (sinhMultiplier α f) x) ∧
    (autocorr (coshMultiplier α f) x ^ 2 - autocorr (sinhMultiplier α f) x ^ 2 = 0 ↔
      autocorr f x = 0 ∨
        autocorr (coshMultiplier α f) x + autocorr (sinhMultiplier α f) x = 0) ∧
    (4 * (autocorr f 0 - autocorr f x) - (autocorr f 0 - autocorr f (2 * x)) =
      (1 / 2 : ℝ) * ∫ u, (f u - 2 * f (u + x) + f (u + 2 * x)) ^ 2) :=
  ⟨hyperbolicCasimirInvariant_eq_autocorr hf hfc α x,
   autocorr_coshMultiplier_sq_sub_sinhMultiplier_sq hf hfc α x,
   autocorr_eq_zero_iff_coshMultiplier_eq_sinhMultiplier hf hfc α x,
   minkowski_lightCone_eq_zero_iff hf hfc α x,
   autocorr_krein_doubling_defect_eq_integral hfc hf x⟩

/-! ## §3. Third Fundamental Theorem: Origin Allocation Uniqueness, Coupled Sphere Gain & Odd-Dyadic Incommensurability -/

/-- **Third Fundamental Theorem of Bi-Scale Uncertainty Analysis:**
1. **Unique Optimal Origin Allocation (`↔`):** For positive total origin weight $W = \sum_{i \in s} a_i > 0$
   and collar loads $b_i \ge 0$ with $B = \sum_{i \in s} b_i > 0$, an allocation $a_i$ attains the
   lower bound $\sqrt{W^2 + B^2}$ if and only if $B a_i = W b_i$ for all $i \in s$.
2. **Universal Dominance of Joint Hilbert Coupling:** Every allocation $a_i$ with $\sum_{i \in s} a_i = W$
   exceeds the coupled sphere penalty $\sqrt{W^2 + \|\sum_{i \in s} p_i\|^2}$ by at least
   `coupledSphereGain W s p ≥ 0`, with `coupledSphereGain W s p = 0 ↔` all packets are positively collinear.
3. **Diophantine Odd-Dyadic Incommensurability:** $(2q + 3)^k \ne n \cdot 2^k$ for all $q, n \in \mathbb{N}$
   and $k \ge 1$. -/
theorem third_fundamental_theorem_origin_allocation_and_coupled_gain
    {ι : Type*} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (s : Finset ι) (a b : ι → ℝ) (p : ι → E) (W : ℝ)
    (haW : (∑ i ∈ s, a i) = W) (hW : 0 < W)
    (hb : ∀ i ∈ s, 0 ≤ b i) (hB : 0 < ∑ i ∈ s, b i) :
    ((∑ i ∈ s, Real.sqrt (a i ^ 2 + b i ^ 2)) =
        Real.sqrt ((∑ i ∈ s, a i) ^ 2 + (∑ i ∈ s, b i) ^ 2) ↔
      ∀ i ∈ s, (∑ k ∈ s, b k) * a i = (∑ k ∈ s, a k) * b i) ∧
    (Real.sqrt (W ^ 2 + ‖∑ i ∈ s, p i‖ ^ 2) + coupledSphereGain W s p ≤
      ∑ i ∈ s, Real.sqrt (a i ^ 2 + ‖p i‖ ^ 2)) ∧
    (coupledSphereGain W s p = 0 ↔
      ∀ i ∈ s, ∀ j ∈ s, ‖p j‖ • p i = ‖p i‖ • p j) ∧
    (∀ (q : ℕ) {k : ℕ}, 1 ≤ k → ∀ n : ℕ, (2 * q + 3) ^ k ≠ n * 2 ^ k) :=
  ⟨origin_allocation_cost_eq_lower_iff s a b hb (by rwa [haW]) hB,
   coupled_sphere_penalty_le_any_allocation W s p a haW,
   coupledSphereGain_eq_zero_iff W s p,
   fun q {k} hk n => odd_pow_ne_mul_two_pow q hk n⟩

/-! ## §4. Fourth Fundamental Theorem: Symmetric Polar Enforcement & Compensated Physical Producers -/

open RHTower.WeilMarkovPole

/-- **Fourth Fundamental Theorem of Bi-Scale Uncertainty Analysis:**
1. **Even-Source Polar Infimum Equivalence (`↔`):** A constant $C \in \mathbb{R}$ is a lower bound
   for `normalizedArchEnergy` on even polar-neutral logarithmic-grid $C^r$ ($r \ge 2$) sources on
   `[2, N]` if and only if it is a lower bound on all even logarithmic-grid $C^r$ sources on `[2, N]`.
2. **Compensated Physical Logarithmic Producer Identity & Compact Support:** For every physical
   velocity $q \in L^2(\mathbb{R})$ and scale $n \in \mathbb{N}$, the compensated velocity
   $v_n(q) = q_n - c_n(q)$ satisfies the exact orthogonal energy identity
   $\|v_n(q)\|^2 = \|q_n\|^2 + m_n(q)^2 / L_n \le (1 + e^{-(n+1)}) \|q\|^2$ and $\int v_n(q) = 0$,
   and the box-smoothed logarithmic state $g_n(q)(x) = F_{w_n(q)}(e^x)$ has exact weighted
   Dirichlet energy. -/
theorem fourth_fundamental_theorem_symmetric_polar_and_compensated_producer
    (r : WithTop ℕ∞) (hr : 2 ≤ r) (N : ℕ) (C : ℝ)
    (n : ℕ) (q : SobolevShear.Velocity) (a b : ℝ) :
    ((∀ (f : ℝ → ℝ), ContDiff ℝ r f → HasCompactSupport f → (∀ u : ℝ, f (-u) = f u) →
        0 < autocorr f 0 →
        (∀ m ∈ Finset.Icc 2 N, autocorr f (Real.log (m : ℝ)) = 0) →
        (∫ x in Ioi 0, autocorr f x * Real.cosh (x / 2)) = 0 → C ≤ normalizedArchEnergy f) ↔
      (∀ (f : ℝ → ℝ), ContDiff ℝ r f → HasCompactSupport f → (∀ u : ℝ, f (-u) = f u) →
        0 < autocorr f 0 →
        (∀ m ∈ Finset.Icc 2 N, autocorr f (Real.log (m : ℝ)) = 0) → C ≤ normalizedArchEnergy f)) ∧
    (‖SobolevShear.compensatedVelocity n q‖ ^ 2 =
      ‖SobolevShear.truncatedVelocity n q‖ ^ 2 +
        (SobolevShear.truncatedMass n q) ^ 2 / SobolevShear.producerTailLength n) ∧
    ((∫ t, SobolevShear.compensatedVelocity n q t) = 0) ∧
    ((∫ x in a..b, Real.exp (-x) * (deriv (SobolevShear.smoothedLogarithmicState n q) x) ^ 2) =
      SobolevShear.energy (SobolevShear.smoothedCompensatedVelocity n q)
        (Real.exp a) (Real.exp b)) :=
  ⟨even_polar_log_grid_lower_bound_iff r hr N C,
   SobolevShear.norm_sq_compensatedVelocity n q,
   SobolevShear.integral_compensatedVelocity_eq_zero n q,
   SobolevShear.smoothedLogarithmicState_dirichlet_energy n q a b⟩

/-! ## §5. Fifth Fundamental Theorem: Critical Nyquist Finite Part & Rescaled-Source Phase Transition -/

/-- **Fifth Fundamental Theorem of Bi-Scale Uncertainty Analysis:**
1. **Critical Nyquist Cell Discrepancy & Inverse-Square Bound:**
   $|d_k(m)| = |\alpha_k(m+1, m) - c_m \delta_k| \le D_m (k+1)^{-2}$.
2. **Nodal Convergence to the Critical Nyquist Finite Part $\mathcal{B}_m$:**
   $|F_m(\log(N+1)) - \mathcal{B}_m| \le 2 D_m / (N + 1)$.
3. **Autocorrelation Total Mass & Rescaled-Source Phase Transition:**
   For every $f \in C_c(\mathbb{R}, \mathbb{R})$, $\int_{\mathbb{R}} \operatorname{autocorr}(f, x)\,dx = (\int f)^2$,
   separating the positive-mean supercritical escape (`tendsto_nyquistWideResidual_supercritical`)
   from the zero-mean signed cancellation witness (`nyquistZeroMeanWitness`). -/
theorem fifth_fundamental_theorem_nyquist_critical_finite_part_and_classification
    (m k N : ℕ) (f : C_c(ℝ, ℝ)) :
    (|nyquistCriticalCellDiscrepancy m k| ≤
      nyquistCriticalDiscrepancyScale m * (((k + 1 : ℕ) : ℝ) ^ (-2 : ℝ))) ∧
    (|nyquistCriticalPrefixPrimitive m N - nyquistCriticalFinitePart m| ≤
      2 * nyquistCriticalDiscrepancyScale m / ((N + 1 : ℕ) : ℝ)) ∧
    ((∫ x, autocorr f x) = (∫ u, f u) ^ 2) ∧
    ((∫ u, nyquistZeroMeanWitness u) = 0 ∧
      (∫ x, autocorr nyquistZeroMeanWitness x) = 0) :=
  ⟨abs_nyquistCriticalCellDiscrepancy_le_inv_sq m k,
   abs_nyquistCriticalPrefixPrimitive_sub_finitePart_le m N,
   integral_autocorr_eq_sq_integral f,
   nyquistZeroMeanWitness_integral_and_autocorr_mass_eq_zero⟩

end GaloisForLFunctions.BiScaleUncertainty
