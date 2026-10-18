import GaloisForLFunctions.BiScaleUncertainty.PhysicalIntervalRestriction
import GaloisForLFunctions.BiScaleUncertainty.PhysicalBoxProfile
import GaloisForLFunctions.BiScaleUncertainty.PhysicalBoxGraphControl
import GaloisForLFunctions.BiScaleUncertainty.RoughModulusGraphDecomposition

/-!
# Compensated Physical Logarithmic Producers and Compact $C^1$ States

This module formalizes the complete **Compensated Physical Logarithmic Producer Theorem**
(`docs/reports/BiScaleUncertainty/CompactLogarithmicPhysicalProducers.md`), closing the gap
between rough physical velocities $q \in L^2(\mathbb{R}, dt)$ and compactly supported $C^1$
logarithmic states $g_n(q) = F_{w_n} \circ \exp$:

1. **Exact Invisibility of the Negative Physical Half-Line (§1):**
   For every velocity $q \in L^2(\mathbb{R})$, the positive-half-line projection
   $P_+ q = \mathbf{1}_{(0, \infty)} q$ has the exact same logarithmic primitive
   $f_{P_+ q} = f_q$, hence identical edge jumps $\operatorname{jump}(P_+ q, e) = \operatorname{jump}(q, e)$,
   identical mixed graph energy $\operatorname{jumpEnergy}(D, P_+ q) = \operatorname{jumpEnergy}(D, q)$,
   and identical compact source mass $\operatorname{sourceMass}(\psi, P_+ q, c) = \operatorname{sourceMass}(\psi, q, c)$.
2. **Explicit Zero-Integral Compensator and Orthogonal Energy Identity (§2):**
   At scale $n \in \mathbb{N}$ with $r = n + 1$, $\alpha_n = e^{-r}$, $\beta_n = e^r$,
   $L_n = e^{2r}$, $h_n = e^{-2r}$, and $B_n = \beta_n + L_n$, the truncated velocity
   $q_n = R_{(\alpha_n, \beta_n)} q$ and explicit constant-tail compensator
   $c_n = (m_n / L_n) \mathbf{1}_{(\beta_n, B_n]}$ (where $m_n = \int_{\alpha_n}^{\beta_n} q$)
   have disjoint supports and satisfy the exact orthogonal energy identity
   $$\|c_n\|^2 = \frac{m_n^2}{L_n}, \qquad
     \|v_n\|^2 = \|q_n - c_n\|^2 = \|q_n\|^2 + \frac{m_n^2}{L_n} \le (1 + e^{-r}) \|q\|^2,$$
   together with exact zero total integral $\int_{\mathbb{R}} v_n = 0$ and vanishing primitive
   $F_{v_n}(t) = 0$ for all $t \le \alpha_n$ and all $t \ge B_n$.
3. **Actual Compactly Supported $C^1$ Logarithmic State (§3):**
   The box-smoothed velocity $w_n = M_{-2r} v_n$ has continuous representative $p_n$ vanishing
   outside $(\alpha_n - h_n, B_n)$, primitive $F_{w_n}(t) = 0$ for $t \le \alpha_n - h_n$ and
   $t \ge B_n$, and $C^1$ logarithmic state $g_n(q)(x) = F_{w_n}(e^x)$ supported inside the compact
   interval $[\log(\alpha_n - h_n), \log B_n]$ with exact weighted Dirichlet energy
   $$\int_a^b e^{-x} |g_n(q)'(x)|^2 \, dx = \int_{e^a}^{e^b} |w_n(t)|^2 \, dt.$$
4. **Explicit Affine Commutator and Compact Source-Graph Error Control (§4–§6):**
   Establishes the quantitative error decomposition for $\|v_n - P_+ q\|$ and
   $\|w_n - P_+ q\|$, explicit affine commutator energy bounds for $w_n$, and compact source-graph
   jump-energy stability $\operatorname{jumpEnergy}(\psi, \text{weights}, w_n - q) \le
   R(\psi, \text{weights}) \|w_n - P_+ q\|^2$.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped BigOperators RealInnerProductSpace NNReal ENNReal CompactlySupported Topology

namespace GaloisForLFunctions.BiScaleUncertainty.SobolevShear

set_option autoImplicit false

/-! ## §1. Exact Invisibility of the Negative Physical Half-Line in the Logarithmic Graph Calculus -/

namespace PathCongestionBridge

open GaloisForLFunctions.BiScaleUncertainty.PathCongestion

/-- Every multiplicative edge jump of `positivePhysicalVelocity q` is identical to that of `q`. -/
theorem jump_positivePhysicalVelocity (q : Velocity) (e : Edge) :
    jump (positivePhysicalVelocity q) e = jump q e := by
  simp only [jump, logPrimitive_positivePhysicalVelocity]

/-- The mixed multiplicative jump energy on any edge mixture `D` is invariant under
projection to the positive physical half-line `P_+ q`. -/
theorem jumpEnergy_positivePhysicalVelocity (D : EdgeMixture) (q : Velocity) :
    jumpEnergy D (positivePhysicalVelocity q) = jumpEnergy D q := by
  unfold jumpEnergy
  exact lintegral_congr (jump_positivePhysicalVelocity q)

/-- The anchored compact source mass is invariant under projection to the positive physical
half-line `P_+ q`. -/
theorem sourceMass_positivePhysicalVelocity (ψ : C_c(ℝ, ℝ)) (q : Velocity) (c : ℝ) :
    sourceMass ψ (positivePhysicalVelocity q) c = sourceMass ψ q c := by
  unfold sourceMass
  apply lintegral_congr
  intro x
  rw [logPrimitive_positivePhysicalVelocity]

/-- For any velocity `u`, `jumpEnergy D (u - q) = jumpEnergy D (u - positivePhysicalVelocity q)`. -/
theorem jumpEnergy_sub_eq_sub_positivePhysicalVelocity (D : EdgeMixture) (u q : Velocity) :
    jumpEnergy D (u - q) = jumpEnergy D (u - positivePhysicalVelocity q) := by
  unfold jumpEnergy
  apply lintegral_congr
  intro e
  have hlog : ∀ x : ℝ, logPrimitive (u - q) x = logPrimitive (u - positivePhysicalVelocity q) x := by
    intro x
    simp only [logPrimitive, primitive_sub_velocity]
    rw [primitive_positivePhysicalVelocity q (Real.exp x) (Real.exp_pos x).le]
  simp only [jump, hlog]

end PathCongestionBridge

/-! ## §2. Scale Parameters and the Constant-Tail Unit Indicator Velocity -/

/-- Scale parameter `r_n = n + 1` for `n : ℕ`. -/
def producerScale (n : ℕ) : ℝ := (n : ℝ) + 1

/-- Lower physical truncation endpoint `α_n = exp(-(n + 1))`. -/
def producerAlpha (n : ℕ) : ℝ := Real.exp (-producerScale n)

/-- Upper physical truncation endpoint `β_n = exp(n + 1)`. -/
def producerBeta (n : ℕ) : ℝ := Real.exp (producerScale n)

/-- Compensator tail length `L_n = exp(2(n + 1))`. -/
def producerTailLength (n : ℕ) : ℝ := Real.exp (2 * producerScale n)

/-- Steklov box-smoothing step `h_n = exp(-2(n + 1))`. -/
def producerStep (n : ℕ) : ℝ := Real.exp (-2 * producerScale n)

/-- Outer support endpoint `B_n = β_n + L_n`. -/
def producerUpper (n : ℕ) : ℝ := producerBeta n + producerTailLength n

theorem producerScale_pos (n : ℕ) : 0 < producerScale n := by
  unfold producerScale
  positivity

theorem producerAlpha_pos (n : ℕ) : 0 < producerAlpha n :=
  Real.exp_pos _

theorem producerBeta_pos (n : ℕ) : 0 < producerBeta n :=
  Real.exp_pos _

theorem producerTailLength_pos (n : ℕ) : 0 < producerTailLength n :=
  Real.exp_pos _

theorem producerStep_pos (n : ℕ) : 0 < producerStep n :=
  Real.exp_pos _

theorem producerStep_lt_producerAlpha (n : ℕ) :
    producerStep n < producerAlpha n := by
  unfold producerStep producerAlpha
  rw [Real.exp_lt_exp]
  have hr := producerScale_pos n
  linarith

theorem producerAlpha_sub_producerStep_pos (n : ℕ) :
    0 < producerAlpha n - producerStep n :=
  sub_pos.mpr (producerStep_lt_producerAlpha n)

theorem producerAlpha_lt_producerBeta (n : ℕ) :
    producerAlpha n < producerBeta n := by
  unfold producerAlpha producerBeta
  rw [Real.exp_lt_exp]
  have hr := producerScale_pos n
  linarith

theorem producerAlpha_le_producerBeta (n : ℕ) :
    producerAlpha n ≤ producerBeta n :=
  (producerAlpha_lt_producerBeta n).le

theorem producerBeta_lt_producerUpper (n : ℕ) :
    producerBeta n < producerUpper n := by
  unfold producerUpper
  linarith [producerTailLength_pos n]

theorem producerBeta_le_producerUpper (n : ℕ) :
    producerBeta n ≤ producerUpper n :=
  (producerBeta_lt_producerUpper n).le

theorem producerBeta_div_producerTailLength (n : ℕ) :
    producerBeta n / producerTailLength n = Real.exp (-producerScale n) := by
  unfold producerBeta producerTailLength
  rw [← Real.exp_sub]
  congr 1
  ring

/-- The constant-1 indicator velocity on `Ioc b (b + L)` in $L^2(\mathbb{R})$. -/
def tailUnitVelocity (b L : ℝ) : Velocity :=
  indicatorConstLp 2 (measurableSet_Ioc (a := b) (b := b + L)) measure_Ioc_lt_top.ne 1

theorem ae_tailUnitVelocity (b L : ℝ) :
    (tailUnitVelocity b L : ℝ → ℝ) =ᵐ[volume] (Ioc b (b + L)).indicator (fun _ => (1 : ℝ)) :=
  indicatorConstLp_coeFn

/-- `tailUnitVelocity b L` is invariant under `physicalIntervalRestriction b (b + L)`. -/
theorem physicalIntervalRestriction_tailUnitVelocity (b L : ℝ) :
    physicalIntervalRestriction b (b + L) (tailUnitVelocity b L) = tailUnitVelocity b L := by
  apply Lp.ext
  filter_upwards [ae_physicalIntervalRestriction b (b + L) (tailUnitVelocity b L),
    ae_tailUnitVelocity b L] with t hr hu
  rw [hr]
  by_cases ht : t ∈ Ioc b (b + L)
  · rw [indicator_of_mem ht, hu]
  · rw [indicator_of_notMem ht, hu, indicator_of_notMem ht]

/-- Squared $L^2$ norm of `tailUnitVelocity b L` for `0 ≤ L`. -/
theorem norm_sq_tailUnitVelocity (b L : ℝ) (hL : 0 ≤ L) :
    ‖tailUnitVelocity b L‖ ^ 2 = L := by
  rw [← real_inner_self_eq_norm_sq, tailUnitVelocity,
    L2.real_inner_indicatorConstLp_one_indicatorConstLp_one _ _
      measure_Ioc_lt_top.ne measure_Ioc_lt_top.ne,
    Set.inter_self]
  simp [Measure.real, Real.volume_Ioc, hL]

/-- Orthogonality of any velocity restricted to `(a, b]` against `tailUnitVelocity b L`. -/
theorem inner_physicalIntervalRestriction_tailUnitVelocity
    (a b L : ℝ) (q : Velocity) :
    ⟪physicalIntervalRestriction a b q, tailUnitVelocity b L⟫ = 0 := by
  rw [real_inner_comm, tailUnitVelocity, L2.inner_indicatorConstLp_one]
  apply integral_eq_zero_of_ae
  filter_upwards [ae_restrict_of_ae (ae_physicalIntervalRestriction a b q),
    ae_restrict_mem (measurableSet_Ioc (a := b) (b := b + L))] with t hq ht
  rw [hq]
  apply indicator_of_notMem
  intro hab
  exact not_lt_of_ge hab.2 ht.1

/-- Total integral of `tailUnitVelocity b L` for `0 ≤ L`. -/
theorem integral_tailUnitVelocity (b L : ℝ) (hL : 0 ≤ L) :
    (∫ t, tailUnitVelocity b L t) = L := by
  rw [← physicalIntervalRestriction_tailUnitVelocity b L,
    integral_physicalIntervalRestriction]
  calc
    (∫ t in Ioc b (b + L), tailUnitVelocity b L t) =
        ∫ _t in Ioc b (b + L), (1 : ℝ) := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_of_ae (ae_tailUnitVelocity b L),
        ae_restrict_mem (measurableSet_Ioc (a := b) (b := b + L))] with t hu ht
      rw [hu, indicator_of_mem ht]
    _ = L := by
      simp [hL]

/-- Left primitive tail of `tailUnitVelocity b L` for `0 ≤ b` and `t ≤ b`. -/
theorem primitive_tailUnitVelocity_left (b L : ℝ) (hb : 0 ≤ b) {t : ℝ} (ht : t ≤ b) :
    primitive (tailUnitVelocity b L) t = 0 := by
  rw [← physicalIntervalRestriction_tailUnitVelocity b L]
  exact primitive_physicalIntervalRestriction_left b (b + L) (tailUnitVelocity b L) hb t ht

/-- Right primitive tail of `tailUnitVelocity b L` for `0 ≤ b`, `0 ≤ L`, and `b + L ≤ t`. -/
theorem primitive_tailUnitVelocity_right (b L : ℝ) (hb : 0 ≤ b) (hL : 0 ≤ L)
    {t : ℝ} (ht : b + L ≤ t) :
    primitive (tailUnitVelocity b L) t = L := by
  rw [← physicalIntervalRestriction_tailUnitVelocity b L,
    primitive_physicalIntervalRestriction_right b (b + L) (tailUnitVelocity b L)
      hb (by linarith) t ht,
    intervalIntegral.integral_of_le (by linarith : b ≤ b + L)]
  calc
    (∫ u in Ioc b (b + L), tailUnitVelocity b L u) =
        ∫ _u in Ioc b (b + L), (1 : ℝ) := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_of_ae (ae_tailUnitVelocity b L),
        ae_restrict_mem (measurableSet_Ioc (a := b) (b := b + L))] with u hu hmem
      rw [hu, indicator_of_mem hmem]
    _ = L := by
      simp [hL]

/-! ## §3. Truncated Velocity, Zero-Integral Compensator, and Exact Energy Identity -/

/-- Truncated physical velocity $q_n = R_{(\alpha_n, \beta_n)} q = \mathbf{1}_{(\alpha_n, \beta_n]} q$. -/
def truncatedVelocity (n : ℕ) (q : Velocity) : Velocity :=
  physicalIntervalRestriction (producerAlpha n) (producerBeta n) q

/-- Truncated physical integral $m_n(q) = \int_{\alpha_n}^{\beta_n} q(t)\,dt$. -/
def truncatedMass (n : ℕ) (q : Velocity) : ℝ :=
  ∫ t in producerAlpha n..producerBeta n, q t

/-- Explicit constant-tail compensator $c_n(q) = (m_n(q) / L_n) \mathbf{1}_{(\beta_n, B_n]}$. -/
def compensatorVelocity (n : ℕ) (q : Velocity) : Velocity :=
  (truncatedMass n q / producerTailLength n) •
    tailUnitVelocity (producerBeta n) (producerTailLength n)

/-- Zero-integral compensated physical velocity $v_n(q) = q_n - c_n(q)$. -/
def compensatedVelocity (n : ℕ) (q : Velocity) : Velocity :=
  truncatedVelocity n q - compensatorVelocity n q

/-- Exact orthogonality $\langle q_n, c_n(q) \rangle = 0$ from disjoint supports. -/
theorem inner_truncatedVelocity_compensatorVelocity (n : ℕ) (q : Velocity) :
    ⟪truncatedVelocity n q, compensatorVelocity n q⟫ = 0 := by
  unfold truncatedVelocity compensatorVelocity
  rw [real_inner_smul_right,
    inner_physicalIntervalRestriction_tailUnitVelocity, mul_zero]

/-- Exact squared $L^2$ norm of the compensator:
$$\|c_n(q)\|^2 = \frac{m_n(q)^2}{L_n}.$$ -/
theorem norm_sq_compensatorVelocity (n : ℕ) (q : Velocity) :
    ‖compensatorVelocity n q‖ ^ 2 = (truncatedMass n q) ^ 2 / producerTailLength n := by
  unfold compensatorVelocity
  rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
    norm_sq_tailUnitVelocity (producerBeta n) (producerTailLength n)
      (producerTailLength_pos n).le]
  have hL : producerTailLength n ≠ 0 := (producerTailLength_pos n).ne'
  field_simp

/-- **Exact Orthogonal Energy Identity for the Compensated Velocity (`‖v_n‖² = ‖q_n‖² + m_n² / L_n`):**
Because $q_n$ and $c_n(q)$ have disjoint supports, the energy of $v_n = q_n - c_n$ splits
without cross terms. -/
theorem norm_sq_compensatedVelocity (n : ℕ) (q : Velocity) :
    ‖compensatedVelocity n q‖ ^ 2 =
      ‖truncatedVelocity n q‖ ^ 2 + (truncatedMass n q) ^ 2 / producerTailLength n := by
  unfold compensatedVelocity
  rw [norm_sub_sq_real, inner_truncatedVelocity_compensatorVelocity,
    norm_sq_compensatorVelocity]
  ring

/-- Cauchy–Schwarz bound on the truncated integral $m_n(q)$:
$$m_n(q)^2 \le (\beta_n - \alpha_n) \|q_n\|^2 \le \beta_n \|q\|^2.$$ -/
theorem truncatedMass_sq_le (n : ℕ) (q : Velocity) :
    (truncatedMass n q) ^ 2 ≤
      (producerBeta n - producerAlpha n) * ‖truncatedVelocity n q‖ ^ 2 := by
  have hab : producerAlpha n ≤ producerBeta n := producerAlpha_le_producerBeta n
  have hsub : producerAlpha n + (producerBeta n - producerAlpha n) = producerBeta n := by ring
  let r : ℝ≥0 := ⟨producerBeta n - producerAlpha n, sub_nonneg.mpr hab⟩
  have hinc := increment_sq_le_energy q (producerAlpha n) r
  have hr : (producerAlpha n : ℝ) + (r : ℝ) = producerBeta n := hsub
  rw [hr, primitive_sub] at hinc
  have hen : energy q (producerAlpha n) (producerBeta n) = ‖truncatedVelocity n q‖ ^ 2 := by
    rw [energy, intervalIntegral.integral_of_le hab, truncatedVelocity,
      norm_sq_physicalIntervalRestriction]
  rw [hen] at hinc
  exact hinc

theorem truncatedMass_sq_le_beta_mul_norm_sq (n : ℕ) (q : Velocity) :
    (truncatedMass n q) ^ 2 ≤ producerBeta n * ‖q‖ ^ 2 := by
  have h1 := truncatedMass_sq_le n q
  have h2 : ‖truncatedVelocity n q‖ ^ 2 ≤ ‖q‖ ^ 2 := by
    unfold truncatedVelocity
    have hle := norm_physicalIntervalRestriction_le (producerAlpha n) (producerBeta n) q
    nlinarith [norm_nonneg (physicalIntervalRestriction (producerAlpha n) (producerBeta n) q),
      norm_nonneg q]
  have hα : 0 < producerAlpha n := producerAlpha_pos n
  have hβ : 0 < producerBeta n := producerBeta_pos n
  calc
    (truncatedMass n q) ^ 2 ≤ (producerBeta n - producerAlpha n) * ‖truncatedVelocity n q‖ ^ 2 := h1
    _ ≤ producerBeta n * ‖truncatedVelocity n q‖ ^ 2 := by
      nlinarith [sq_nonneg ‖truncatedVelocity n q‖]
    _ ≤ producerBeta n * ‖q‖ ^ 2 := mul_le_mul_of_nonneg_left h2 hβ.le

/-- Quantitative energy bound on the compensator:
$$\|c_n(q)\|^2 \le e^{-(n+1)} \|q\|^2.$$ -/
theorem norm_sq_compensatorVelocity_le (n : ℕ) (q : Velocity) :
    ‖compensatorVelocity n q‖ ^ 2 ≤ Real.exp (-producerScale n) * ‖q‖ ^ 2 := by
  rw [norm_sq_compensatorVelocity]
  have hL : 0 < producerTailLength n := producerTailLength_pos n
  calc
    (truncatedMass n q) ^ 2 / producerTailLength n ≤
        (producerBeta n * ‖q‖ ^ 2) / producerTailLength n :=
      div_le_div_of_nonneg_right (truncatedMass_sq_le_beta_mul_norm_sq n q) hL.le
    _ = (producerBeta n / producerTailLength n) * ‖q‖ ^ 2 := by ring
    _ = Real.exp (-producerScale n) * ‖q‖ ^ 2 := by
      rw [producerBeta_div_producerTailLength]

/-- Quantitative norm bound on the compensator:
$$\|c_n(q)\| \le e^{-(n+1)/2} \|q\|.$$ -/
theorem norm_compensatorVelocity_le (n : ℕ) (q : Velocity) :
    ‖compensatorVelocity n q‖ ≤ Real.exp (-producerScale n / 2) * ‖q‖ := by
  have hsq := norm_sq_compensatorVelocity_le n q
  have hexp : (Real.exp (-producerScale n / 2) * ‖q‖) ^ 2 =
      Real.exp (-producerScale n) * ‖q‖ ^ 2 := by
    rw [mul_pow, ← Real.exp_nat_mul]
    congr 1
    congr 1
    ring
  rw [← hexp] at hsq
  have hnonneg : 0 ≤ Real.exp (-producerScale n / 2) * ‖q‖ := by positivity
  nlinarith [norm_nonneg (compensatorVelocity n q)]

/-- **Quantitative Energy Bound for the Compensated Velocity:**
$$\|v_n(q)\|^2 \le \left(1 + e^{-(n+1)}\right) \|q\|^2.$$ -/
theorem norm_sq_compensatedVelocity_le (n : ℕ) (q : Velocity) :
    ‖compensatedVelocity n q‖ ^ 2 ≤ (1 + Real.exp (-producerScale n)) * ‖q‖ ^ 2 := by
  rw [norm_sq_compensatedVelocity, ← norm_sq_compensatorVelocity]
  have hq : ‖truncatedVelocity n q‖ ^ 2 ≤ ‖q‖ ^ 2 := by
    unfold truncatedVelocity
    have hle := norm_physicalIntervalRestriction_le (producerAlpha n) (producerBeta n) q
    nlinarith [norm_nonneg (physicalIntervalRestriction (producerAlpha n) (producerBeta n) q),
      norm_nonneg q]
  have hc := norm_sq_compensatorVelocity_le n q
  linarith

/-! ## §4. Zero Total Integral and Compact Primitive Support of $v_n$ -/

/-- `truncatedVelocity n q` is integrable on $\mathbb{R}$ with integral $m_n(q)$. -/
theorem integral_truncatedVelocity (n : ℕ) (q : Velocity) :
    (∫ t, truncatedVelocity n q t) = truncatedMass n q := by
  rw [truncatedVelocity, integral_physicalIntervalRestriction, truncatedMass,
    intervalIntegral.integral_of_le (producerAlpha_le_producerBeta n)]

/-- `compensatorVelocity n q` is integrable on $\mathbb{R}$. -/
theorem integrable_compensatorVelocity (n : ℕ) (q : Velocity) :
    Integrable (compensatorVelocity n q : ℝ → ℝ) := by
  unfold compensatorVelocity
  have hi : Integrable (tailUnitVelocity (producerBeta n) (producerTailLength n) : ℝ → ℝ) := by
    rw [← physicalIntervalRestriction_tailUnitVelocity]
    exact integrable_physicalIntervalRestriction _ _ _
  exact (hi.smul (truncatedMass n q / producerTailLength n)).congr
    (Lp.coeFn_smul _ _).symm

/-- Total integral of `compensatorVelocity n q` equals $m_n(q)$. -/
theorem integral_compensatorVelocity (n : ℕ) (q : Velocity) :
    (∫ t, compensatorVelocity n q t) = truncatedMass n q := by
  unfold compensatorVelocity
  have hcongr :
      (∫ t, ((truncatedMass n q / producerTailLength n) •
        tailUnitVelocity (producerBeta n) (producerTailLength n) : Velocity) t) =
      ∫ t, (truncatedMass n q / producerTailLength n) *
        tailUnitVelocity (producerBeta n) (producerTailLength n) t := by
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_smul (truncatedMass n q / producerTailLength n)
      (tailUnitVelocity (producerBeta n) (producerTailLength n))] with t ht
    exact ht
  rw [hcongr, integral_const_mul,
    integral_tailUnitVelocity (producerBeta n) (producerTailLength n)
      (producerTailLength_pos n).le]
  have hL : producerTailLength n ≠ 0 := (producerTailLength_pos n).ne'
  field_simp

/-- **Exact Zero Total Integral of the Compensated Velocity (`∫ v_n = 0`):** -/
theorem integral_compensatedVelocity_eq_zero (n : ℕ) (q : Velocity) :
    (∫ t, compensatedVelocity n q t) = 0 := by
  unfold compensatedVelocity
  have hq : Integrable (truncatedVelocity n q : ℝ → ℝ) :=
    integrable_physicalIntervalRestriction _ _ q
  have hc : Integrable (compensatorVelocity n q : ℝ → ℝ) :=
    integrable_compensatorVelocity n q
  have hcongr :
      (∫ t, (truncatedVelocity n q - compensatorVelocity n q : Velocity) t) =
        ∫ t, (truncatedVelocity n q t - compensatorVelocity n q t) := by
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (truncatedVelocity n q) (compensatorVelocity n q)] with t ht
    exact ht
  rw [hcongr, integral_sub hq hc, integral_truncatedVelocity, integral_compensatorVelocity,
    sub_self]

/-- Primitive of `compensatorVelocity n q` at any `t : ℝ`. -/
theorem primitive_compensatorVelocity (n : ℕ) (q : Velocity) (t : ℝ) :
    primitive (compensatorVelocity n q) t =
      (truncatedMass n q / producerTailLength n) *
        primitive (tailUnitVelocity (producerBeta n) (producerTailLength n)) t := by
  unfold compensatorVelocity primitive
  calc
    (∫ u in 0..t, ((truncatedMass n q / producerTailLength n) •
        tailUnitVelocity (producerBeta n) (producerTailLength n) : Velocity) u) =
      ∫ u in 0..t, (truncatedMass n q / producerTailLength n) *
        tailUnitVelocity (producerBeta n) (producerTailLength n) u := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [Lp.coeFn_smul (truncatedMass n q / producerTailLength n)
        (tailUnitVelocity (producerBeta n) (producerTailLength n))] with u hu
      exact fun _ => hu
    _ = (truncatedMass n q / producerTailLength n) *
        ∫ u in 0..t, tailUnitVelocity (producerBeta n) (producerTailLength n) u :=
      intervalIntegral.integral_const_mul _ _

/-- **Left Primitive Support Vanishing of $v_n$:**
For every $t \le \alpha_n$ (including all $t \le 0$), $F_{v_n}(t) = 0$. -/
theorem primitive_compensatedVelocity_eq_zero_of_le_alpha
    (n : ℕ) (q : Velocity) {t : ℝ} (ht : t ≤ producerAlpha n) :
    primitive (compensatedVelocity n q) t = 0 := by
  unfold compensatedVelocity
  rw [primitive_sub_velocity]
  have h1 : primitive (truncatedVelocity n q) t = 0 :=
    primitive_physicalIntervalRestriction_left (producerAlpha n) (producerBeta n) q
      (producerAlpha_pos n).le t ht
  have h2 : primitive (compensatorVelocity n q) t = 0 := by
    rw [primitive_compensatorVelocity,
      primitive_tailUnitVelocity_left (producerBeta n) (producerTailLength n)
        (producerBeta_pos n).le (ht.trans (producerAlpha_le_producerBeta n)),
      mul_zero]
  rw [h1, h2, sub_self]

/-- **Right Primitive Support Vanishing of $v_n$:**
For every $t \ge B_n = \beta_n + L_n$, the constant primitive tail is completely removed:
$F_{v_n}(t) = 0$. -/
theorem primitive_compensatedVelocity_eq_zero_of_upper_le
    (n : ℕ) (q : Velocity) {t : ℝ} (ht : producerUpper n ≤ t) :
    primitive (compensatedVelocity n q) t = 0 := by
  unfold compensatedVelocity
  rw [primitive_sub_velocity]
  have h1 : primitive (truncatedVelocity n q) t = truncatedMass n q :=
    primitive_physicalIntervalRestriction_right (producerAlpha n) (producerBeta n) q
      (producerAlpha_pos n).le (producerAlpha_le_producerBeta n) t
      ((producerBeta_le_producerUpper n).trans ht)
  have h2 : primitive (compensatorVelocity n q) t = truncatedMass n q := by
    rw [primitive_compensatorVelocity,
      primitive_tailUnitVelocity_right (producerBeta n) (producerTailLength n)
        (producerBeta_pos n).le (producerTailLength_pos n).le ht]
    have hL : producerTailLength n ≠ 0 := (producerTailLength_pos n).ne'
    field_simp
  rw [h1, h2, sub_self]

/-! ## §5. Box-Smoothed Producer $w_n$ and Compactly Supported $C^1$ Logarithmic State -/

/-- Box-smoothed compensated velocity $w_n(q) = M_{-2(n+1)} v_n(q)$. -/
def smoothedCompensatedVelocity (n : ℕ) (q : Velocity) : Velocity :=
  physicalBoxAverage (-2 * producerScale n) (compensatedVelocity n q)

/-- Continuous representative $p_n(q)$ of $w_n(q)$. -/
def smoothedCompensatedProfile (n : ℕ) (q : Velocity) (t : ℝ) : ℝ :=
  physicalBoxProfile (-2 * producerScale n) (compensatedVelocity n q) t

/-- Smoothed $C^1$ logarithmic state $g_n(q)(x) = F_{w_n(q)}(e^x)$. -/
def smoothedLogarithmicState (n : ℕ) (q : Velocity) (x : ℝ) : ℝ :=
  logPrimitive (smoothedCompensatedVelocity n q) x

/-- Uniform energy bound on $w_n(q)$:
$$\|w_n(q)\|^2 \le (1 + e^{-(n+1)}) \|q\|^2.$$ -/
theorem norm_sq_smoothedCompensatedVelocity_le (n : ℕ) (q : Velocity) :
    ‖smoothedCompensatedVelocity n q‖ ^ 2 ≤ (1 + Real.exp (-producerScale n)) * ‖q‖ ^ 2 := by
  have h1 : ‖smoothedCompensatedVelocity n q‖ ^ 2 ≤ ‖compensatedVelocity n q‖ ^ 2 := by
    unfold smoothedCompensatedVelocity
    have hle := physicalBoxAverage_norm_le (-2 * producerScale n) (compensatedVelocity n q)
    nlinarith [norm_nonneg (physicalBoxAverage (-2 * producerScale n) (compensatedVelocity n q)),
      norm_nonneg (compensatedVelocity n q)]
  exact h1.trans (norm_sq_compensatedVelocity_le n q)

/-- The continuous profile $p_n(q)$ vanishes for $t \le \alpha_n - h_n$. -/
theorem smoothedCompensatedProfile_eq_zero_of_le (n : ℕ) (q : Velocity)
    {t : ℝ} (ht : t ≤ producerAlpha n - producerStep n) :
    smoothedCompensatedProfile n q t = 0 := by
  unfold smoothedCompensatedProfile physicalBoxProfile
  have hstep : Real.exp (-2 * producerScale n) = producerStep n := rfl
  rw [hstep]
  have h1 : primitive (compensatedVelocity n q) (t + producerStep n) = 0 :=
    primitive_compensatedVelocity_eq_zero_of_le_alpha n q (by linarith)
  have h2 : primitive (compensatedVelocity n q) t = 0 :=
    primitive_compensatedVelocity_eq_zero_of_le_alpha n q
      (by linarith [producerStep_pos n])
  rw [h1, h2, sub_self, mul_zero]

/-- The continuous profile $p_n(q)$ vanishes for $t \ge B_n$. -/
theorem smoothedCompensatedProfile_eq_zero_of_upper_le (n : ℕ) (q : Velocity)
    {t : ℝ} (ht : producerUpper n ≤ t) :
    smoothedCompensatedProfile n q t = 0 := by
  unfold smoothedCompensatedProfile physicalBoxProfile
  have hstep : Real.exp (-2 * producerScale n) = producerStep n := rfl
  rw [hstep]
  have h1 : primitive (compensatedVelocity n q) (t + producerStep n) = 0 :=
    primitive_compensatedVelocity_eq_zero_of_upper_le n q
      (by linarith [producerStep_pos n])
  have h2 : primitive (compensatedVelocity n q) t = 0 :=
    primitive_compensatedVelocity_eq_zero_of_upper_le n q ht
  rw [h1, h2, sub_self, mul_zero]

/-- `physicalSecondPrimitive (compensatedVelocity n q) t` vanishes for all $t \le \alpha_n$. -/
theorem physicalSecondPrimitive_compensatedVelocity_eq_zero_of_le_alpha
    (n : ℕ) (q : Velocity) {t : ℝ} (ht : t ≤ producerAlpha n) :
    physicalSecondPrimitive (compensatedVelocity n q) t = 0 := by
  unfold physicalSecondPrimitive
  calc
    (∫ u in 0..t, primitive (compensatedVelocity n q) u) = ∫ _u in 0..t, (0 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro u hu
      apply primitive_compensatedVelocity_eq_zero_of_le_alpha n q
      rcases Set.mem_uIcc.mp hu with ⟨_, hu2⟩ | ⟨_, hu2⟩
      · exact hu2.trans ht
      · exact hu2.trans (producerAlpha_pos n).le
    _ = 0 := by simp

/-- **Left Primitive Support Vanishing of $w_n$:**
For every $t \le \alpha_n - h_n$, $F_{w_n(q)}(t) = 0$. -/
theorem primitive_smoothedCompensatedVelocity_eq_zero_of_le
    (n : ℕ) (q : Velocity) {t : ℝ} (ht : t ≤ producerAlpha n - producerStep n) :
    primitive (smoothedCompensatedVelocity n q) t = 0 := by
  unfold smoothedCompensatedVelocity
  rw [primitive_physicalBoxAverage]
  have hstep : Real.exp (-2 * producerScale n) = producerStep n := rfl
  rw [hstep]
  have h1 : physicalSecondPrimitive (compensatedVelocity n q) (t + producerStep n) = 0 :=
    physicalSecondPrimitive_compensatedVelocity_eq_zero_of_le_alpha n q (by linarith)
  have h2 : physicalSecondPrimitive (compensatedVelocity n q) t = 0 :=
    physicalSecondPrimitive_compensatedVelocity_eq_zero_of_le_alpha n q
      (by linarith [producerStep_pos n])
  have h3 : physicalSecondPrimitive (compensatedVelocity n q) (producerStep n) = 0 :=
    physicalSecondPrimitive_compensatedVelocity_eq_zero_of_le_alpha n q
      (producerStep_lt_producerAlpha n).le
  rw [h1, h2, h3, sub_zero, sub_self, mul_zero]

/-- **Right Primitive Support Vanishing of $w_n$:**
For every $t \ge B_n$, $F_{w_n(q)}(t) = 0$. -/
theorem primitive_smoothedCompensatedVelocity_eq_zero_of_upper_le
    (n : ℕ) (q : Velocity) {t : ℝ} (ht : producerUpper n ≤ t) :
    primitive (smoothedCompensatedVelocity n q) t = 0 := by
  unfold smoothedCompensatedVelocity
  rw [primitive_physicalBoxAverage]
  have hstep : Real.exp (-2 * producerScale n) = producerStep n := rfl
  rw [hstep, physicalSecondPrimitive_sub]
  have hdiff : (∫ u in t..t + producerStep n, primitive (compensatedVelocity n q) u) = 0 := by
    calc
      (∫ u in t..t + producerStep n, primitive (compensatedVelocity n q) u) =
          ∫ _u in t..t + producerStep n, (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro u hu
        apply primitive_compensatedVelocity_eq_zero_of_upper_le n q
        have hle : t ≤ t + producerStep n := by linarith [producerStep_pos n]
        rw [Set.uIcc_of_le hle] at hu
        exact ht.trans hu.1
      _ = 0 := by simp
  have h3 : physicalSecondPrimitive (compensatedVelocity n q) (producerStep n) = 0 :=
    physicalSecondPrimitive_compensatedVelocity_eq_zero_of_le_alpha n q
      (producerStep_lt_producerAlpha n).le
  rw [hdiff, h3, sub_self, mul_zero]

/-- **Logarithmic State Compact Support Bound (Left):**
For $x \le \log(\alpha_n - h_n)$, $g_n(q)(x) = 0$. -/
theorem smoothedLogarithmicState_eq_zero_of_le (n : ℕ) (q : Velocity)
    {x : ℝ} (hx : x ≤ Real.log (producerAlpha n - producerStep n)) :
    smoothedLogarithmicState n q x = 0 := by
  unfold smoothedLogarithmicState logPrimitive
  apply primitive_smoothedCompensatedVelocity_eq_zero_of_le n q
  have hpos := producerAlpha_sub_producerStep_pos n
  calc
    Real.exp x ≤ Real.exp (Real.log (producerAlpha n - producerStep n)) :=
      Real.exp_le_exp.mpr hx
    _ = producerAlpha n - producerStep n := Real.exp_log hpos

/-- **Logarithmic State Compact Support Bound (Right):**
For $x \ge \log B_n$, $g_n(q)(x) = 0$. -/
theorem smoothedLogarithmicState_eq_zero_of_upper_le (n : ℕ) (q : Velocity)
    {x : ℝ} (hx : Real.log (producerUpper n) ≤ x) :
    smoothedLogarithmicState n q x = 0 := by
  unfold smoothedLogarithmicState logPrimitive
  apply primitive_smoothedCompensatedVelocity_eq_zero_of_upper_le n q
  have hpos : 0 < producerUpper n :=
    lt_trans (producerBeta_pos n) (producerBeta_lt_producerUpper n)
  calc
    producerUpper n = Real.exp (Real.log (producerUpper n)) := (Real.exp_log hpos).symm
    _ ≤ Real.exp x := Real.exp_le_exp.mpr hx

/-- **Everywhere Differentiability of the Smoothed Logarithmic State (`g_n(q)'(x) = e^x p_n(e^x)`):**
Unlike rough logarithmic primitives (which are differentiable only a.e.), the box-smoothed
logarithmic state $g_n(q)$ is differentiable at every point $x \in \mathbb{R}$ with continuous
derivative $x \mapsto e^x p_n(q)(e^x)$. -/
theorem hasDerivAt_smoothedLogarithmicState (n : ℕ) (q : Velocity) (x : ℝ) :
    HasDerivAt (smoothedLogarithmicState n q)
      (Real.exp x * smoothedCompensatedProfile n q (Real.exp x)) x := by
  unfold smoothedLogarithmicState logPrimitive smoothedCompensatedVelocity smoothedCompensatedProfile
  have h1 := hasDerivAt_primitive_physicalBoxAverage
    (-2 * producerScale n) (compensatedVelocity n q) (Real.exp x)
  have h2 := h1.comp x (Real.hasDerivAt_exp x)
  simpa only [Function.comp_def, mul_comm] using h2

/-- Continuity of the derivative of `smoothedLogarithmicState n q`. -/
theorem continuous_deriv_smoothedLogarithmicState (n : ℕ) (q : Velocity) :
    Continuous (deriv (smoothedLogarithmicState n q)) := by
  have hderiv : deriv (smoothedLogarithmicState n q) =
      fun x => Real.exp x * smoothedCompensatedProfile n q (Real.exp x) := by
    ext x
    exact (hasDerivAt_smoothedLogarithmicState n q x).deriv
  rw [hderiv]
  exact Real.continuous_exp.mul
    ((continuous_physicalBoxProfile (-2 * producerScale n) (compensatedVelocity n q)).comp
      Real.continuous_exp)

/-- **Exact Weighted Logarithmic Dirichlet Energy Identity:**
$$\int_a^b e^{-x} \left(g_n(q)'(x)\right)^2 dx
  = \int_{e^a}^{e^b} \left(w_n(q)(t)\right)^2 dt.$$ -/
theorem smoothedLogarithmicState_dirichlet_energy (n : ℕ) (q : Velocity) (a b : ℝ) :
    (∫ x in a..b, Real.exp (-x) * (deriv (smoothedLogarithmicState n q) x) ^ 2) =
      energy (smoothedCompensatedVelocity n q) (Real.exp a) (Real.exp b) :=
  log_energy_eq (smoothedCompensatedVelocity n q) a b

/-! ## §6. Quantitative Approximation, Affine Commutator Control, and Compact Graph Forms -/

/-- Quantitative $L^2$ error bound between the compensated velocity $v_n(q)$ and the visible
positive velocity $P_+ q$:
$$\|v_n(q) - P_+ q\| \le \|q_n - P_+ q\| + e^{-(n+1)/2} \|q\|.$$ -/
theorem norm_compensatedVelocity_sub_positive_le (n : ℕ) (q : Velocity) :
    ‖compensatedVelocity n q - positivePhysicalVelocity q‖ ≤
      ‖truncatedVelocity n q - positivePhysicalVelocity q‖ +
        Real.exp (-producerScale n / 2) * ‖q‖ := by
  have hdecomp :
      compensatedVelocity n q - positivePhysicalVelocity q =
        (truncatedVelocity n q - positivePhysicalVelocity q) - compensatorVelocity n q := by
    unfold compensatedVelocity
    abel
  rw [hdecomp]
  have h1 := norm_sub_le (truncatedVelocity n q - positivePhysicalVelocity q) (compensatorVelocity n q)
  have h2 := norm_compensatorVelocity_le n q
  linarith

/-- Quantitative $L^2$ error bound between the smoothed producer $w_n(q)$ and $P_+ q$:
$$\|w_n(q) - P_+ q\| \le \|q_n - P_+ q\| + e^{-(n+1)/2} \|q\|
  + \|M_{-2(n+1)}(P_+ q) - P_+ q\|.$$ -/
theorem norm_smoothedCompensatedVelocity_sub_positive_le (n : ℕ) (q : Velocity) :
    ‖smoothedCompensatedVelocity n q - positivePhysicalVelocity q‖ ≤
      ‖truncatedVelocity n q - positivePhysicalVelocity q‖ +
        Real.exp (-producerScale n / 2) * ‖q‖ +
        ‖physicalBoxAverage (-2 * producerScale n) (positivePhysicalVelocity q) -
          positivePhysicalVelocity q‖ := by
  have hdecomp :
      smoothedCompensatedVelocity n q - positivePhysicalVelocity q =
        physicalBoxAverage (-2 * producerScale n)
          (compensatedVelocity n q - positivePhysicalVelocity q) +
        (physicalBoxAverage (-2 * producerScale n) (positivePhysicalVelocity q) -
          positivePhysicalVelocity q) := by
    unfold smoothedCompensatedVelocity
    rw [map_sub]
    abel
  rw [hdecomp]
  have h1 := norm_add_le
    (physicalBoxAverage (-2 * producerScale n)
      (compensatedVelocity n q - positivePhysicalVelocity q))
    (physicalBoxAverage (-2 * producerScale n) (positivePhysicalVelocity q) -
      positivePhysicalVelocity q)
  have h2 :
      ‖physicalBoxAverage (-2 * producerScale n)
        (compensatedVelocity n q - positivePhysicalVelocity q)‖ ≤
      ‖truncatedVelocity n q - positivePhysicalVelocity q‖ +
        Real.exp (-producerScale n / 2) * ‖q‖ :=
    (physicalBoxAverage_norm_le (-2 * producerScale n) _).trans
      (norm_compensatedVelocity_sub_positive_le n q)
  linarith

/-- **Explicit Affine Commutator Energy Bound for the Compensated Box Producer:**
For arbitrary affine parameters $a, b \in \mathbb{R}$,
$$\|C_{a,b} w_n(q)\|^2
  \le 4 |a| \min\left(1, \frac{|b(a-1)|}{h_n}\right)^2
    \left(1 + e^{-(n+1)}\right) \|q\|^2.$$ -/
theorem smoothedCompensatedVelocity_affine_energy_le (a b : ℝ) (n : ℕ) (q : Velocity) :
    ‖physicalAffineCommutator a b (smoothedCompensatedVelocity n q)‖ ^ 2 ≤
      4 * |a| * (min 1 (|b * (a - 1)| / producerStep n)) ^ 2 *
        (1 + Real.exp (-producerScale n)) * ‖q‖ ^ 2 := by
  unfold smoothedCompensatedVelocity
  have h1 := physicalBoxAverage_affine_energy_le a b (-2 * producerScale n)
    (compensatedVelocity n q)
  have hstep : Real.exp (-2 * producerScale n) = producerStep n := rfl
  rw [hstep] at h1
  have h2 := norm_sq_compensatedVelocity_le n q
  have hcoef : 0 ≤ 4 * |a| * (min 1 (|b * (a - 1)| / producerStep n)) ^ 2 := by positivity
  calc
    ‖physicalAffineCommutator a b
        (physicalBoxAverage (-2 * producerScale n) (compensatedVelocity n q))‖ ^ 2 ≤
      4 * |a| * (min 1 (|b * (a - 1)| / producerStep n)) ^ 2 *
        ‖compensatedVelocity n q‖ ^ 2 := h1
    _ ≤ 4 * |a| * (min 1 (|b * (a - 1)| / producerStep n)) ^ 2 *
        ((1 + Real.exp (-producerScale n)) * ‖q‖ ^ 2) :=
      mul_le_mul_of_nonneg_left h2 hcoef
    _ = 4 * |a| * (min 1 (|b * (a - 1)| / producerStep n)) ^ 2 *
        (1 + Real.exp (-producerScale n)) * ‖q‖ ^ 2 := by ring

/-- **Compact Source-Graph Jump Energy Error Bound for $w_n(q) - q$:**
Because the negative physical half-line is invisible to logarithmic primitives, the mixed
jump energy of $w_n(q) - q$ is bounded by the finite resistance mass times
$\|w_n(q) - P_+ q\|^2$. -/
theorem compact_jumpEnergy_smoothedCompensatedVelocity_sub_le
    (ψ : C_c(ℝ, ℝ)) (weights : ℕ → ℝ≥0) (n : ℕ) (q : Velocity) :
    PathCongestion.jumpEnergy (PathCongestion.compactMixture ψ weights)
        (smoothedCompensatedVelocity n q - q) ≤
      PathCongestion.resistanceMass ψ weights *
        ENNReal.ofReal (‖smoothedCompensatedVelocity n q - positivePhysicalVelocity q‖ ^ 2) := by
  rw [PathCongestionBridge.jumpEnergy_sub_eq_sub_positivePhysicalVelocity]
  exact PathCongestion.compact_jumpEnergy_le_norm_sq ψ weights
    (smoothedCompensatedVelocity n q - positivePhysicalVelocity q)

end GaloisForLFunctions.BiScaleUncertainty.SobolevShear
