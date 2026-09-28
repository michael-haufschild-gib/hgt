import GaloisForLFunctions.RHTower.ThetaSurgeryControllability
import GaloisForLFunctions.RHTower.ProfileRenewalAnalyticContinuation
import GaloisForLFunctions.RHTower.XiHorizontalStripDecay
import GaloisForLFunctions.RHTower.ThetaSeamCouplingFamily

/-!
# Off-axis zero surgery inside the exact positive renewal reflection class

Fix `a = 1/4`, `c = Θ(1)`, the literal even real-analytic profile `P(t) = e^{at}Θ(e^t)` and
`0 < v < a`.  At `z_T = T + iv` the planted value `w_T = Ξ(2z_T)/(z_T² + a²)` is `O(e^{-T})`, so
the unique mass-neutral coefficients reaching it are `O(e^{-T})`, while every derivative of the
three directions grows at most like `e^{T/8}`.  The surgered profile `P_T = P + g_T` then:

* is even and real-analytic, with `P_T(0) = c` and the seam jets of `P` through order `2N+1`,
  and converges to `P` in every exponentially weighted `C^k` norm;
* has increment `ν_T = aP_T - P_T' > 0` on `t ≥ 0` with exactly the literal renewal mass `q`;
  its oriented kernel `Q_T` is positive, real-analytic, stable on `Re s ≥ -a`, and obeys the
  exact reflection `Q_T(-t) + Q_T(t) = 2 sinh(at)/t`;
* has two-ended function `X_T = Ξ(2z) - (z² + a²) E_z(g_T)` vanishing on the quartet
  `±z_T, ±conj z_T`, for a nonzero perturbation along arbitrarily large `T`;
* has full-source density `k_T(x) = k(x) + 2[g_T''(2x) - a² g_T(2x)]`, every finite literal prime
  deletion of which is positive on the right ray, uniformly in the prime set.

The scalar renewal family `D_r = c - rN` has inverse source `rP + (1 - r)ce^{at}`, whose even
extension is differentiable at the seam only for `r = 1`.
-/
open Complex Filter Topology Set MeasureTheory HurwitzZeta
open GaloisForLFunctions.HTGeometry
open scoped ContDiff ComplexConjugate

namespace RHTower

noncomputable section

local notation "Θ" => evenKernel (0 : UnitAddCircle)

/-! ## Analyticity of the literal profile -/

/-- The holomorphic profile `e^{z/4} ϑ(e^z)` on the strip `|Im z| < π/2`. -/
def thetaLogProfileC (z : ℂ) : ℂ := cexp (z / 4) * jacobiThetaSum (cexp z)

theorem differentiableOn_thetaLogProfileC : DifferentiableOn ℂ thetaLogProfileC thetaStrip := by
  intro z hz
  have h := (hasDerivAt_jacobiThetaSum (re_cexp_pos_of_mem_thetaStrip hz)).comp z
    (Complex.hasDerivAt_exp z)
  exact ((((hasDerivAt_id z).div_const (4 : ℂ)).cexp).mul h).differentiableAt.differentiableWithinAt

theorem thetaLogProfileC_ofReal (t : ℝ) : thetaLogProfileC t = (thetaLogProfile t : ℂ) := by
  rw [thetaLogProfileC, ← Complex.ofReal_exp, jacobiThetaSum_ofReal_eq_evenKernel, thetaLogProfile,
    show ((t : ℂ) / 4) = ((t / 4 : ℝ) : ℂ) by push_cast; ring, ← Complex.ofReal_exp]
  push_cast; rfl

theorem analyticAt_thetaLogProfile (t : ℝ) : AnalyticAt ℝ thetaLogProfile t := by
  have hopen : thetaStrip ∈ 𝓝 (t : ℂ) :=
    isOpen_thetaStrip.mem_nhds (by simp [thetaStrip, Real.pi_pos])
  have hC : AnalyticAt ℂ thetaLogProfileC (t : ℂ) := differentiableOn_thetaLogProfileC.analyticAt hopen
  have hR : AnalyticAt ℝ thetaLogProfileC (t : ℂ) := hC.restrictScalars
  have hcomp : AnalyticAt ℝ (fun x : ℝ => (thetaLogProfileC (x : ℂ)).re) t :=
    (Complex.reCLM.analyticAt _).comp (hR.comp (Complex.ofRealCLM.analyticAt t))
  refine hcomp.congr (Eventually.of_forall fun x => ?_)
  simp only [thetaLogProfileC_ofReal, Complex.ofReal_re]

theorem contDiff_thetaLogProfile : ContDiff ℝ ∞ thetaLogProfile :=
  AnalyticOnNhd.contDiff fun t _ => analyticAt_thetaLogProfile t

/-! ## The holomorphic surgered increment -/

theorem deriv_surgeryPerturbationC_ofReal (N : ℕ) (T : ℝ) (ε : Fin 3 → ℝ) (x : ℝ) :
    deriv (surgeryPerturbationC N T ε) (x : ℂ) = ((deriv (surgeryPerturbation N T ε) x : ℝ) : ℂ) := by
  have h1 : HasDerivAt (fun y : ℝ => surgeryPerturbationC N T ε y)
      (deriv (surgeryPerturbationC N T ε) x) x :=
    ((differentiable_surgeryPerturbationC N T ε x).hasDerivAt).comp_ofReal
  have h2 : HasDerivAt (fun y : ℝ => (surgeryPerturbation N T ε y : ℂ))
      ((deriv (surgeryPerturbation N T ε) x : ℝ) : ℂ) x :=
    (hasDerivAt_surgeryPerturbation N T ε x).ofReal_comp
  rw [funext (surgeryPerturbationC_ofReal N T ε)] at h1
  exact h1.unique h2

/-- The holomorphic surgered increment `ν(z) + g(z)/4 - g'(z)` on the strip. -/
def surgeryIncrementC (N : ℕ) (T : ℝ) (ε : Fin 3 → ℝ) (z : ℂ) : ℂ :=
  thetaRenewalIncrementC z + (1 / 4 * surgeryPerturbationC N T ε z - deriv (surgeryPerturbationC N T ε) z)

theorem differentiableOn_surgeryIncrementC (N : ℕ) (T : ℝ) (ε : Fin 3 → ℝ) :
    DifferentiableOn ℂ (surgeryIncrementC N T ε) thetaStrip := by
  have hg := (differentiable_surgeryPerturbationC N T ε).differentiableOn (s := thetaStrip)
  exact differentiableOn_thetaRenewalIncrementC.add
    ((hg.const_mul _).sub (hg.deriv isOpen_thetaStrip))

theorem surgeryIncrementC_ofReal (N : ℕ) (T : ℝ) (ε : Fin 3 → ℝ) (x : ℝ) :
    surgeryIncrementC N T ε x = (surgeryIncrement N T ε x : ℂ) := by
  rw [surgeryIncrementC, surgeryIncrement_eq, thetaRenewalIncrementC_ofReal,
    surgeryPerturbationC_ofReal, deriv_surgeryPerturbationC_ofReal]
  push_cast; ring

/-! ## Structural laws valid for every perturbation -/

theorem surgeryXi_neg (N : ℕ) (T : ℝ) (ε : Fin 3 → ℝ) (z : ℂ) :
    surgeryXi N T ε (-z) = surgeryXi N T ε z := by
  simp only [surgeryXi, mul_neg, neg_neg]
  ring

theorem surgeryTransform_conj (N : ℕ) (T : ℝ) (ε : Fin 3 → ℝ) (z : ℂ) :
    surgeryTransform N T ε (conj z) = conj (surgeryTransform N T ε z) := by
  rw [surgeryTransform, surgeryTransform, ← integral_conj,
    ← integral_neg_eq_self (fun t : ℝ => cexp (-(I * conj z * t)) * (surgeryPerturbation N T ε t : ℂ))]
  congr 1; ext t
  rw [map_mul, ← Complex.exp_conj, Complex.conj_ofReal, surgeryPerturbation_neg]
  congr 2
  simp only [map_neg, map_mul, Complex.conj_I, Complex.conj_ofReal, Complex.ofReal_neg]
  ring

theorem surgeryXi_conj (N : ℕ) {T : ℝ} (hT : 0 ≤ T) (ε : Fin 3 → ℝ) (z : ℂ) :
    surgeryXi N T ε (conj z) = conj (surgeryXi N T ε z) := by
  rw [surgeryXi_eq N hT, surgeryXi_eq N hT, surgeryTransform_conj,
    show (2 : ℂ) * conj z = conj (2 * z) by rw [map_mul, map_ofNat], XiC_conj']
  simp only [map_sub, map_mul, map_add, map_pow, map_div₀, map_one, map_ofNat]

theorem surgeryDensity_neg (N : ℕ) (T : ℝ) (ε : Fin 3 → ℝ) (x : ℝ) :
    surgeryDensity N T ε (-x) = surgeryDensity N T ε x := by
  have h2 : iteratedDeriv 2 (surgeryPerturbation N T ε) (-(2 * x)) =
      iteratedDeriv 2 (surgeryPerturbation N T ε) (2 * x) := by
    have h := iteratedDeriv_comp_neg 2 (surgeryPerturbation N T ε) (2 * x)
    rw [show (fun y => surgeryPerturbation N T ε (-y)) = surgeryPerturbation N T ε from
      funext (surgeryPerturbation_neg N T ε)] at h
    simp only [even_two, Even.neg_pow, one_pow, one_smul] at h
    exact h.symm
  rw [surgeryDensity, surgeryDensity, thetaCuspFullSource_neg, mul_neg, h2,
    surgeryPerturbation_neg]

/-- **Exact reflection (1).** For every perturbation the oriented kernel `Q_g` of the surgered
increment obeys `Q_g(-t) + Q_g(t) = 2 sinh(t/4)/t`. -/
theorem surgeryLogKernel_neg_add (N : ℕ) (T : ℝ) (ε : Fin 3 → ℝ) {t : ℝ} (ht : t ≠ 0) :
    renewalLogKernel (surgeryIncrement N T ε) (Θ 1) (-t) +
      renewalLogKernel (surgeryIncrement N T ε) (Θ 1) t = 2 * Real.sinh (1 / 4 * t) / t :=
  renewalLogKernel_neg_add (continuous_surgeryIncrement N T ε) thetaSeam_pos
    (hasDerivAt_surgeryProfile N T ε) (surgeryProfile_zero N T ε) (surgeryProfile_neg N T ε) ht

/-- The surgered oriented kernel is real-analytic on the whole axis. -/
theorem analyticAt_surgeryLogKernel (N : ℕ) (T : ℝ) (ε : Fin 3 → ℝ) (t : ℝ) :
    AnalyticAt ℝ (renewalLogKernel (surgeryIncrement N T ε) (Θ 1)) t :=
  analyticAt_renewalLogKernel (differentiableOn_surgeryIncrementC N T ε)
    (surgeryIncrementC_ofReal N T ε) thetaSeam_pos t

/-- The universal even seam jets `Q_g^{(2j)}(0) = a^{2j+1}/(2j+1)`. -/
theorem iteratedDeriv_even_surgeryLogKernel_zero (N : ℕ) (T : ℝ) (ε : Fin 3 → ℝ) (j : ℕ) :
    iteratedDeriv (2 * j) (renewalLogKernel (surgeryIncrement N T ε) (Θ 1)) 0 =
      (1 / 4) ^ (2 * j + 1) / (2 * j + 1) :=
  iteratedDeriv_even_renewalLogKernel_zero (differentiableOn_surgeryIncrementC N T ε)
    (surgeryIncrementC_ofReal N T ε) thetaSeam_pos (hasDerivAt_surgeryProfile N T ε)
    (surgeryProfile_zero N T ε) (surgeryProfile_neg N T ε) j

theorem analyticAt_surgeryProfile (N : ℕ) (T : ℝ) (ε : Fin 3 → ℝ) (t : ℝ) :
    AnalyticAt ℝ (surgeryProfile N T ε) t :=
  (analyticAt_thetaLogProfile t).add (analyticAt_surgeryPerturbation N T ε t)

/-- **Seam jets.** `P_g` has the same derivatives as `P` through order `2N + 1` at the seam. -/
theorem iteratedDeriv_surgeryProfile_zero (N : ℕ) (T : ℝ) (ε : Fin 3 → ℝ) {k : ℕ}
    (hk : k ≤ 2 * N + 1) :
    iteratedDeriv k (surgeryProfile N T ε) 0 = iteratedDeriv k thetaLogProfile 0 := by
  have h : surgeryProfile N T ε = thetaLogProfile + surgeryPerturbation N T ε := rfl
  rw [h, iteratedDeriv_add (contDiff_thetaLogProfile.contDiffAt.of_le (mod_cast le_top))
    ((contDiff_surgeryPerturbation N T ε).contDiffAt.of_le (mod_cast le_top)),
    iteratedDeriv_surgeryPerturbation_zero N T ε hk, add_zero]

theorem integrable_exp_mul_iteratedDeriv (N k : ℕ) {T : ℝ} (hT : 0 ≤ T) (ε : Fin 3 → ℝ) (σ : ℝ) :
    Integrable fun t => Real.exp (σ * t) * iteratedDeriv k (surgeryPerturbation N T ε) t := by
  have h := integrable_exp_mul_iteratedDeriv_surgeryPerturbation N k hT ε |σ|
  have hc : Continuous (iteratedDeriv k (surgeryPerturbation N T ε)) :=
    (contDiff_surgeryPerturbation N T ε).continuous_iteratedDeriv k (mod_cast le_top)
  refine h.mono' (by fun_prop) (Eventually.of_forall fun t => ?_)
  simp only [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
  refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ?_) (abs_nonneg _)
  rw [← abs_mul]; exact le_abs_self _

theorem integrableOn_exp_mul_surgeryIncrement (N : ℕ) {T : ℝ} (hT : 0 ≤ T) (ε : Fin 3 → ℝ)
    (σ : ℝ) : IntegrableOn (fun t => Real.exp (σ * t) * surgeryIncrement N T ε t) (Ioi 0) := by
  have hν : IntegrableOn (fun t => Real.exp (σ * t) * thetaRenewalIncrement t) (Ioi 0) := by
    have := integrableOn_exp_mul_thetaRenewalIncrement (-σ)
    simpa only [neg_mul, neg_neg] using this
  have h0 := (integrable_exp_mul_iteratedDeriv N 0 hT ε σ).const_mul (1 / 4)
  have h1 := integrable_exp_mul_iteratedDeriv N 1 hT ε σ
  refine (hν.add (h0.sub h1).integrableOn).congr_fun (fun t _ => ?_) measurableSet_Ioi
  simp only [Pi.add_apply, Pi.sub_apply, iteratedDeriv_zero, iteratedDeriv_one, surgeryIncrement_eq]
  ring

/-! ## The planted spectral value -/

/-- The target `w_T = Ξ(2 z_T)/(z_T² + a²)` at `z_T = T + iv`. -/
def surgeryTarget (v T : ℝ) : ℂ :=
  XiC (2 * ((T : ℂ) + v * I)) / (((T : ℂ) + v * I) ^ 2 + 1 / 16)

theorem one_le_norm_sq_add_sixteenth {v : ℝ} (hv : |v| ≤ 1 / 4) {T : ℝ} (hT : 1 ≤ T) :
    1 ≤ ‖((T : ℂ) + v * I) ^ 2 + 1 / 16‖ := by
  refine le_trans ?_ (Complex.re_le_norm _)
  have hre : (((T : ℂ) + v * I) ^ 2 + 1 / 16).re = T ^ 2 - v ^ 2 + 1 / 16 := by
    simp [sq, Complex.mul_re]
  rw [hre]
  have hv2 : v ^ 2 ≤ 1 / 16 := by
    rw [← sq_abs]; nlinarith [abs_nonneg v]
  nlinarith

theorem exists_norm_surgeryTarget_le {v : ℝ} (hv : |v| ≤ 1 / 4) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T, 1 ≤ T → ‖surgeryTarget v T‖ ≤ C * Real.exp (-T) := by
  obtain ⟨C, hC, h⟩ := exists_norm_XiC_horizontal_le (A := 1 / 2) (δ := 1 / 2) (by norm_num)
    (by norm_num) (by linarith [Real.pi_gt_three])
  refine ⟨C, hC, fun T hT => ?_⟩
  have hX := h (2 * T) (2 * v) (by rw [abs_mul]; norm_num; linarith)
  have e : (2 : ℂ) * ((T : ℂ) + v * I) = ((2 * T : ℝ) : ℂ) + ((2 * v : ℝ) : ℂ) * I := by
    push_cast; ring
  have hd := one_le_norm_sq_add_sixteenth hv hT
  rw [surgeryTarget, norm_div, e, div_le_iff₀ (by linarith)]
  calc ‖XiC (((2 * T : ℝ) : ℂ) + ((2 * v : ℝ) : ℂ) * I)‖ ≤ C * Real.exp (-(1 / 2 * |2 * T|)) := hX
    _ = C * Real.exp (-T) := by rw [abs_of_nonneg (by linarith)]; ring_nf
    _ ≤ C * Real.exp (-T) * ‖((T : ℂ) + v * I) ^ 2 + 1 / 16‖ :=
        le_mul_of_one_le_right (by positivity) hd

/-- The planted mass-neutral coefficients `ε_T` with `E_T(g) = w_T`. -/
def plantedCoeff (N : ℕ) (v T : ℝ) : Fin 3 → ℝ := surgeryCoeff N v T (surgeryTarget v T)

/-- The surgered profile `P_T = P + Σ ε_{j,T} g_{j,T}`. -/
def plantedProfile (N : ℕ) (v T : ℝ) : ℝ → ℝ := surgeryProfile N T (plantedCoeff N v T)

/-- The surgered increment `ν_T = a P_T - P_T'`. -/
def plantedIncrement (N : ℕ) (v T : ℝ) : ℝ → ℝ := surgeryIncrement N T (plantedCoeff N v T)

/-- The surgered oriented logarithmic kernel `Q_T = Σ ν_T^{⋆m}/(m c^m)`. -/
def plantedLogKernel (N : ℕ) (v T : ℝ) : ℝ → ℝ := renewalLogKernel (plantedIncrement N v T) (Θ 1)

/-- The surgered two-ended function `X_T`. -/
def plantedXi (N : ℕ) (v T : ℝ) : ℂ → ℂ := surgeryXi N T (plantedCoeff N v T)

/-- The surgered full-source density `k_T`. -/
def plantedDensity (N : ℕ) (v T : ℝ) : ℝ → ℝ := surgeryDensity N T (plantedCoeff N v T)

/-- **Exponentially small planted coefficients.** For `0 < v ≤ 1/4` the planted coefficients
solve the mass-neutral system for all large `T` and are `O(e^{-T})`. -/
theorem exists_plantedCoeff_le (N : ℕ) {v : ℝ} (hv0 : 0 < v) (hv1 : v ≤ 1 / 4) :
    ∃ C U : ℝ, 0 ≤ C ∧ 1 ≤ U ∧ ∀ T, U ≤ T →
      surgeryMass N T (plantedCoeff N v T) = 0 ∧
      surgeryTransform N T (plantedCoeff N v T) ((T : ℂ) + v * I) = surgeryTarget v T ∧
      |plantedCoeff N v T 0| + |plantedCoeff N v T 1| + |plantedCoeff N v T 2| ≤
        C * Real.exp (-T) := by
  obtain ⟨K, U, hK, hU, h⟩ := surgery_controllability N hv0
  obtain ⟨C, hC, hw⟩ := exists_norm_surgeryTarget_le (v := v) (by rw [abs_of_pos hv0]; exact hv1)
  refine ⟨K * C, max U 1, by positivity, le_max_right _ _, fun T hT => ?_⟩
  obtain ⟨⟨hm, htr⟩, -, hb⟩ := h T (le_trans (le_max_left _ _) hT) (surgeryTarget v T)
  refine ⟨hm, htr, hb.trans ?_⟩
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left (hw T (le_trans (le_max_right _ _) hT)) hK

theorem eventually_plantedCoeff_small (N : ℕ) {v : ℝ} (hv0 : 0 < v) (hv1 : v ≤ 1 / 4) {η : ℝ}
    (hη : 0 < η) : ∀ᶠ T in atTop, 1 ≤ T ∧ surgeryMass N T (plantedCoeff N v T) = 0 ∧
      surgeryTransform N T (plantedCoeff N v T) ((T : ℂ) + v * I) = surgeryTarget v T ∧
      (|plantedCoeff N v T 0| + |plantedCoeff N v T 1| + |plantedCoeff N v T 2|) *
        Real.exp (T / 8) < η := by
  obtain ⟨C, U, hC, hU, h⟩ := exists_plantedCoeff_le N hv0 hv1
  have hlim : Tendsto (fun T : ℝ => C * Real.exp (-(7 / 8 * T))) atTop (𝓝 0) := by
    have := (Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 7 / 8))).const_mul C
    rw [mul_zero] at this
    exact this
  filter_upwards [hlim.eventually (gt_mem_nhds hη), eventually_ge_atTop U] with T hT hTU
  obtain ⟨hm, htr, hb⟩ := h T hTU
  refine ⟨hU.trans hTU, hm, htr, lt_of_le_of_lt ?_ hT⟩
  calc (|plantedCoeff N v T 0| + |plantedCoeff N v T 1| + |plantedCoeff N v T 2|) *
        Real.exp (T / 8) ≤ C * Real.exp (-T) * Real.exp (T / 8) :=
        mul_le_mul_of_nonneg_right hb (Real.exp_pos _).le
    _ = C * Real.exp (-(7 / 8 * T)) := by
        rw [mul_assoc, ← Real.exp_add]; ring_nf

theorem sq_add_sixteenth_ne_zero {v : ℝ} (hv : |v| ≤ 1 / 4) {T : ℝ} (hT : 1 ≤ T) :
    ((T : ℂ) + v * I) ^ 2 + 1 / 16 ≠ 0 := by
  intro h
  have := one_le_norm_sq_add_sixteenth hv hT
  rw [h, norm_zero] at this
  linarith

/-! ## The planted zero -/

/-- **The planted off-axis zero and its quartet.** For `0 < v < 1/4` and all large `T`,
`X_T` vanishes at `z_T = T + iv`, `-z_T`, `conj z_T` and `-conj z_T`. -/
theorem eventually_plantedXi_eq_zero (N : ℕ) {v : ℝ} (hv0 : 0 < v) (hv1 : v < 1 / 4) :
    ∀ᶠ T in atTop, plantedXi N v T ((T : ℂ) + v * I) = 0 ∧
      plantedXi N v T (-((T : ℂ) + v * I)) = 0 ∧
      plantedXi N v T (conj ((T : ℂ) + v * I)) = 0 ∧
      plantedXi N v T (-conj ((T : ℂ) + v * I)) = 0 := by
  filter_upwards [eventually_plantedCoeff_small N hv0 hv1.le one_pos] with T hTsmall
  obtain ⟨hT1, -, htr, -⟩ := hTsmall
  have hT0 : 0 ≤ T := by linarith
  have hz := sq_add_sixteenth_ne_zero (v := v) (by rw [abs_of_pos hv0]; linarith) hT1
  have h0 : plantedXi N v T ((T : ℂ) + v * I) = 0 := by
    rw [plantedXi, surgeryXi_eq N hT0, htr, surgeryTarget, mul_div_cancel₀ _ hz, sub_self]
  have hc : plantedXi N v T (conj ((T : ℂ) + v * I)) = 0 := by
    rw [plantedXi, surgeryXi_conj N hT0, ← plantedXi, h0, map_zero]
  refine ⟨h0, ?_, hc, ?_⟩
  · rw [plantedXi, surgeryXi_neg, ← plantedXi, h0]
  · rw [plantedXi, surgeryXi_neg, ← plantedXi, hc]

theorem frequently_XiC_ne_zero (v : ℝ) : ∃ᶠ T : ℝ in atTop, XiC (2 * ((T : ℂ) + v * I)) ≠ 0 := by
  rw [Filter.frequently_atTop]
  intro U
  obtain ⟨u, hu, hne⟩ := exists_XiC_horizontal_ne_zero (2 * v) (2 * U)
  refine ⟨u / 2, by linarith, ?_⟩
  convert hne using 2
  push_cast; ring

/-- The planted perturbation is nonzero whenever `Ξ(2z_T) ≠ 0`. -/
theorem plantedPerturbation_ne_zero {N : ℕ} {v T : ℝ} (hv : |v| ≤ 1 / 4) (hT : 1 ≤ T)
    (htr : surgeryTransform N T (plantedCoeff N v T) ((T : ℂ) + v * I) = surgeryTarget v T)
    (hX : XiC (2 * ((T : ℂ) + v * I)) ≠ 0) : surgeryPerturbation N T (plantedCoeff N v T) ≠ 0 := by
  intro h0
  have h : surgeryTransform N T (plantedCoeff N v T) ((T : ℂ) + v * I) = 0 := by
    rw [surgeryTransform, h0]; simp
  rw [htr, surgeryTarget, div_eq_zero_iff] at h
  rcases h with h | h
  · exact hX h
  · exact sq_add_sixteenth_ne_zero hv hT h

/-! ## Positivity of the increment and the exact mass -/

/-- **Positive increments.** For all large `T`, `ν_T = aP_T - P_T' > 0` on `t ≥ 0`. -/
theorem eventually_plantedIncrement_pos (N : ℕ) {v : ℝ} (hv0 : 0 < v) (hv1 : v ≤ 1 / 4) :
    ∀ᶠ T in atTop, ∀ t, 0 ≤ t → 0 < plantedIncrement N v T t := by
  set m := 2 * N + 3
  set Km : ℝ := m.factorial * Real.exp (1 + Real.pi ^ 2 * Real.exp (1 / 4) / 2) / (2 * Real.pi)
  have hKm : 0 ≤ Km := by positivity
  filter_upwards [eventually_plantedCoeff_small N hv0 hv1 (η := 1 / (33 / 4 * Km + 1))
    (by positivity)] with T hTsmall t ht
  obtain ⟨hT1, -, -, hsmall⟩ := hTsmall
  set ε := plantedCoeff N v T
  set σ := (|ε 0| + |ε 1| + |ε 2|) * Real.exp (T / 8)
  have hσ0 : 0 ≤ σ := by positivity
  have hT0 : 0 ≤ T := by linarith
  have hg0 := abs_iteratedDeriv_surgeryPerturbation_le N 0 hT0 ε t
  have hg1 := abs_iteratedDeriv_surgeryPerturbation_le N 1 hT0 ε t
  simp only [iteratedDeriv_zero, iteratedDeriv_one, Nat.factorial_zero, Nat.factorial_one,
    Nat.cast_one, pow_zero, pow_one, one_mul, abs_of_nonneg ht] at hg0 hg1
  have hdec := pow_mul_surgeryDecay_le_increment m ht
  have hν := thetaRenewalIncrement_pos t
  set E := (t + 1) ^ m * surgeryDecay t
  have hA : |surgeryPerturbation N T ε t| ≤ σ * E := by
    calc _ ≤ _ := hg0
      _ = σ * E := by simp only [σ, E, m]; ring
  have hB : |deriv (surgeryPerturbation N T ε) t| ≤ 8 * (σ * E) := by
    calc _ ≤ _ := hg1
      _ = 8 * (σ * E) := by simp only [σ, E, m]; ring
  have hs : σ * (33 / 4 * Km + 1) < 1 := by
    rwa [lt_div_iff₀ (by positivity)] at hsmall
  have hkey : |1 / 4 * surgeryPerturbation N T ε t - deriv (surgeryPerturbation N T ε) t| <
      thetaRenewalIncrement t := by
    calc _ ≤ 1 / 4 * |surgeryPerturbation N T ε t| + |deriv (surgeryPerturbation N T ε) t| := by
          refine (abs_sub _ _).trans ?_
          rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 4)]
      _ ≤ 33 / 4 * σ * E := by linarith
      _ ≤ 33 / 4 * σ * (Km * thetaRenewalIncrement t) := by gcongr
      _ < thetaRenewalIncrement t := by nlinarith
  rw [plantedIncrement, surgeryIncrement_eq]
  linarith [neg_abs_le (1 / 4 * surgeryPerturbation N T ε t - deriv (surgeryPerturbation N T ε) t)]

/-- **Exact mass.** For all large `T`, `c⁻¹ ∫₀^∞ e^{at} ν_T = q`, the literal renewal mass. -/
theorem eventually_plantedIncrement_mass (N : ℕ) {v : ℝ} (hv0 : 0 < v) (hv1 : v ≤ 1 / 4) :
    ∀ᶠ T in atTop, (∫ t in Ioi (0 : ℝ), Real.exp (1 / 4 * t) * plantedIncrement N v T t) / Θ 1 =
      thetaRenewalMass := by
  filter_upwards [eventually_plantedCoeff_small N hv0 hv1 one_pos] with T hTsmall
  obtain ⟨hT1, hm, -, -⟩ := hTsmall
  have h := integral_exp_mul_surgeryIncrement N (T := T) (by linarith) (plantedCoeff N v T)
  rw [surgeryMass] at hm
  rw [plantedIncrement, h, show (1 / 2 : ℝ) * ∫ t in Ioi (0 : ℝ), Real.exp (1 / 4 * t) *
    surgeryPerturbation N T (plantedCoeff N v T) t = 0 from hm, add_zero, thetaRenewalMass,
    ← integral_div]
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  rw [thetaRenewalDensity]; ring_nf

theorem thetaRenewalMass_lt_one : thetaRenewalMass < 1 := by
  linarith [thetaRenewalMass_lt]

/-- **Positive, stable logarithmic kernel.** For all large `T`, `Q_T > 0` on `t > 0`, and on
`Re s ≥ -a`: `∫₀^∞ e^{-st} Q_T = -log(1 - L_T(s)/c)` and `D_T(s) = c e^{-∫e^{-st}Q_T} ≠ 0`. -/
theorem eventually_plantedLogKernel (N : ℕ) {v : ℝ} (hv0 : 0 < v) (hv1 : v ≤ 1 / 4) :
    ∀ᶠ T in atTop, (∀ t, 0 < t → 0 < plantedLogKernel N v T t) ∧
      ∀ s : ℂ, -(1 / 4) ≤ s.re →
        (∫ t in Ioi (0 : ℝ), cexp (-(s * t)) * (plantedLogKernel N v T t : ℂ)) =
          -Complex.log (1 - renewalLaplace (plantedIncrement N v T) s / (Θ 1 : ℂ)) ∧
        surgeryDenominator N T (plantedCoeff N v T) s =
          (Θ 1 : ℂ) * cexp (-∫ t in Ioi (0 : ℝ), cexp (-(s * t)) * (plantedLogKernel N v T t : ℂ)) ∧
        surgeryDenominator N T (plantedCoeff N v T) s ≠ 0 := by
  filter_upwards [eventually_plantedCoeff_small N hv0 hv1 one_pos,
    eventually_plantedIncrement_pos N hv0 hv1, eventually_plantedIncrement_mass N hv0 hv1]
    with T hTsmall hpos hmass
  obtain ⟨hT1, -, -, -⟩ := hTsmall
  have hT0 : 0 ≤ T := by linarith
  have hc := thetaSeam_pos
  have hν := continuous_surgeryIncrement N T (plantedCoeff N v T)
  have hint := integrableOn_exp_mul_surgeryIncrement N hT0 (plantedCoeff N v T) (1 / 4)
  have hlt : ∫ t in Ioi (0 : ℝ), Real.exp (1 / 4 * t) * plantedIncrement N v T t < Θ 1 := by
    rw [div_eq_iff hc.ne'] at hmass
    rw [hmass]
    nlinarith [thetaRenewalMass_lt_one]
  refine ⟨fun t ht => renewalLogKernel_pos hν hpos hc ht, fun s hs => ⟨?_, ?_, ?_⟩⟩
  · exact integral_cexp_mul_renewalLogKernel (a := 1 / 4) hν hpos hint hc hlt hs
  · exact renewalDenominator_eq_exp (a := 1 / 4) hν hpos hint hc hlt hs
  · exact renewalDenominator_ne_zero (a := 1 / 4) hν hpos hint hlt hs

/-! ## Weighted convergence and the tail inequality -/

theorem plantedProfile_sub (N : ℕ) (v T : ℝ) :
    (fun t => plantedProfile N v T t - thetaLogProfile t) =
      surgeryPerturbation N T (plantedCoeff N v T) := by
  funext t; simp [plantedProfile, surgeryProfile]

/-- **Convergence in every exponentially weighted norm.** For every order `k`, weight `B` and
`η > 0`, eventually `e^{B|t|} |(P_T - P)^{(k)}(t)| ≤ η` for all real `t`. -/
theorem eventually_plantedProfile_sub_le (N : ℕ) {v : ℝ} (hv0 : 0 < v) (hv1 : v ≤ 1 / 4)
    (k : ℕ) (B : ℝ) {η : ℝ} (hη : 0 < η) : ∀ᶠ T in atTop, ∀ t,
      Real.exp (B * |t|) * |iteratedDeriv k (fun t => plantedProfile N v T t - thetaLogProfile t) t|
        ≤ η := by
  set m := 2 * N + 3
  set MB : ℝ := m.factorial * Real.exp (1 + (|B| + 1) ^ 2 * Real.exp (1 / 4) / 2)
  set ck : ℝ := k.factorial * 8 ^ k
  have hMB : 0 ≤ MB := by positivity
  have hck : 0 ≤ ck := by positivity
  filter_upwards [eventually_plantedCoeff_small N hv0 hv1 (η := η / (ck * MB + 1))
    (by positivity)] with T hTsmall t
  obtain ⟨hT1, -, -, hsmall⟩ := hTsmall
  set ε := plantedCoeff N v T
  set σ := (|ε 0| + |ε 1| + |ε 2|) * Real.exp (T / 8)
  have hσ0 : 0 ≤ σ := by positivity
  rw [plantedProfile_sub]
  have hg := abs_iteratedDeriv_surgeryPerturbation_le N k (T := T) (by linarith) ε t
  have hw := exp_mul_pow_mul_surgeryDecay_le B m t
  have hs : σ * (ck * MB + 1) < η := by rwa [lt_div_iff₀ (by positivity)] at hsmall
  calc Real.exp (B * |t|) * |iteratedDeriv k (surgeryPerturbation N T ε) t|
      ≤ Real.exp (B * |t|) * (ck * (σ * ((|t| + 1) ^ m * surgeryDecay t))) := by
        refine mul_le_mul_of_nonneg_left (hg.trans (le_of_eq ?_)) (Real.exp_pos _).le
        simp only [ck, σ, m]; ring
    _ = ck * σ * (Real.exp (B * |t|) * ((|t| + 1) ^ m * surgeryDecay t)) := by ring
    _ ≤ ck * σ * MB := by gcongr
    _ ≤ η := by nlinarith

/-- **The source-tail inequality.** For all large `T`, `P_T(t) > e^{at}` on `t ≥ 0`. -/
theorem eventually_exp_lt_plantedProfile (N : ℕ) {v : ℝ} (hv0 : 0 < v) (hv1 : v ≤ 1 / 4) :
    ∀ᶠ T in atTop, ∀ t, 0 ≤ t → Real.exp (t / 4) < plantedProfile N v T t := by
  set m := 2 * N + 3
  set KR : ℝ := m.factorial * Real.exp (1 + (Real.pi + 1) ^ 2 * Real.exp (1 / 4) / 2) / 2
  have hKR : 0 ≤ KR := by positivity
  filter_upwards [eventually_plantedCoeff_small N hv0 hv1 (η := 1 / (KR + 1)) (by positivity)]
    with T hTsmall t ht
  obtain ⟨hT1, -, -, hsmall⟩ := hTsmall
  set ε := plantedCoeff N v T
  set σ := (|ε 0| + |ε 1| + |ε 2|) * Real.exp (T / 8)
  have hσ0 : 0 ≤ σ := by positivity
  have hg := abs_iteratedDeriv_surgeryPerturbation_le N 0 (T := T) (by linarith) ε t
  simp only [iteratedDeriv_zero, Nat.factorial_zero, Nat.cast_one, pow_zero, one_mul,
    abs_of_nonneg ht] at hg
  have hR := pow_mul_surgeryDecay_le_thetaLogTail m ht
  have hR0 := thetaLogTail_pos t
  have hs : σ * (KR + 1) < 1 := by rwa [lt_div_iff₀ (by positivity)] at hsmall
  have hgR : |surgeryPerturbation N T ε t| < thetaLogTail t := by
    calc _ ≤ _ := hg
      _ = σ * ((t + 1) ^ m * surgeryDecay t) := by simp only [σ, m]; ring
      _ ≤ σ * (KR * thetaLogTail t) := by gcongr
      _ < thetaLogTail t := by nlinarith
  rw [plantedProfile, surgeryProfile, thetaLogProfile_eq_add]
  linarith [neg_abs_le (surgeryPerturbation N T ε t)]

/-! ## The perturbed density and all finite prime deletions -/

/-- **The perturbed density (7).** `∫ e^{-iwx} k_T(x) dx = X_T(w/2)`. -/
theorem integral_cexp_mul_plantedDensity (N : ℕ) (v : ℝ) {T : ℝ} (hT : 0 ≤ T) (w : ℂ) :
    ∫ x : ℝ, cexp (-I * w * x) * (plantedDensity N v T x : ℂ) = plantedXi N v T (w / 2) :=
  integral_cexp_mul_surgeryDensity N hT _ w

theorem abs_thetaPrimeDeletion_le_sum_abs {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) (f : ℝ → ℝ)
    (x : ℝ) : |thetaPrimeDeletion S f x| ≤
      ∑ T ∈ S.powerset, |f (x + Real.log ((∏ p ∈ T, p : ℕ) : ℝ))| := by
  unfold thetaPrimeDeletion
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun T hT => ?_)
  have hd : (1 : ℝ) ≤ ((∏ p ∈ T, p : ℕ) : ℝ) := by
    have : 0 < ∏ p ∈ T, p :=
      Finset.prod_pos fun p hp => (hS p (Finset.mem_powerset.mp hT hp)).pos
    exact_mod_cast this
  rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, abs_mul,
    abs_of_nonneg (Real.rpow_nonneg (by linarith) _)]
  exact mul_le_of_le_one_left (abs_nonneg _) (Real.rpow_le_one_of_one_le_of_nonpos hd (by norm_num))

/-- **Positivity of every finite prime deletion (8).** For all large `T`, simultaneously for every
finite set `S` of primes, `D_S k_T(x) > 0` on `x ≥ 0`. -/
theorem eventually_thetaPrimeDeletion_plantedDensity_pos (N : ℕ) {v : ℝ} (hv0 : 0 < v)
    (hv1 : v ≤ 1 / 4) : ∀ᶠ T in atTop, ∀ S : Finset ℕ, (∀ p ∈ S, p.Prime) → ∀ x, 0 ≤ x →
      0 < thetaPrimeDeletion S (plantedDensity N v T) x := by
  set m := 2 * N + 3
  set W := ∑' n, deletionShiftWeight m n
  set Kd : ℝ := m.factorial * Real.exp (1 + (Real.pi + 1) ^ 2 * Real.exp (1 / 4) / 2) /
    (2 * Real.pi * (2 * Real.pi - 3))
  set C₁ : ℝ := 2 * (128 + 1 / 16)
  have hW : 0 ≤ W := tsum_nonneg fun n => deletionShiftWeight_nonneg m n
  have hpi : 0 < 2 * Real.pi - 3 := by linarith [Real.pi_gt_three]
  have hKd : 0 ≤ Kd := by positivity
  filter_upwards [eventually_plantedCoeff_small N hv0 hv1 (η := 1 / (C₁ * W * Kd + 1))
    (by positivity)] with T hTsmall S hS x hx
  obtain ⟨hT1, -, -, hsmall⟩ := hTsmall
  have hT0 : 0 ≤ T := by linarith
  set ε := plantedCoeff N v T
  set σ := (|ε 0| + |ε 1| + |ε 2|) * Real.exp (T / 8)
  have hσ0 : 0 ≤ σ := by positivity
  have hs : σ * (C₁ * W * Kd + 1) < 1 := by rwa [lt_div_iff₀ (by positivity)] at hsmall
  set δ : ℝ → ℝ := fun y => 2 * (iteratedDeriv 2 (surgeryPerturbation N T ε) (2 * y) -
    surgeryPerturbation N T ε (2 * y) / 16)
  have hδ : ∀ y, 0 ≤ y → |δ y| ≤ C₁ * σ * ((2 * y + 1) ^ m * surgeryDecay (2 * y)) := by
    intro y hy
    have h2 := abs_iteratedDeriv_surgeryPerturbation_le N 2 hT0 ε (2 * y)
    have h0 := abs_iteratedDeriv_surgeryPerturbation_le N 0 hT0 ε (2 * y)
    rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ 2 * y)] at h0 h2
    simp only [iteratedDeriv_zero, Nat.factorial_zero, Nat.cast_one, pow_zero, one_mul] at h0
    set E := (2 * y + 1) ^ m * surgeryDecay (2 * y)
    have hA : |iteratedDeriv 2 (surgeryPerturbation N T ε) (2 * y)| ≤ 128 * (σ * E) :=
      h2.trans (le_of_eq (by simp only [σ, E, m, Nat.factorial]; push_cast; ring))
    have hB : |surgeryPerturbation N T ε (2 * y)| ≤ σ * E :=
      h0.trans (le_of_eq (by simp only [σ, E, m]; ring))
    calc |δ y| = 2 * |iteratedDeriv 2 (surgeryPerturbation N T ε) (2 * y) -
          surgeryPerturbation N T ε (2 * y) / 16| := by
          simp only [δ, abs_mul, abs_two]
      _ ≤ 2 * (|iteratedDeriv 2 (surgeryPerturbation N T ε) (2 * y)| +
          |surgeryPerturbation N T ε (2 * y)| / 16) := by
          gcongr
          refine (abs_sub _ _).trans (le_of_eq ?_)
          rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 16)]
      _ ≤ C₁ * σ * E := by simp only [C₁]; nlinarith
  have hsum : |thetaPrimeDeletion S δ x| ≤ C₁ * σ * (W * Kd * thetaCuspSourceTerm x 1) := by
    refine (abs_thetaPrimeDeletion_le_sum_abs hS δ x).trans ?_
    calc ∑ T' ∈ S.powerset, |δ (x + Real.log ((∏ p ∈ T', p : ℕ) : ℝ))|
        ≤ ∑ T' ∈ S.powerset, C₁ * σ * ((2 * (x + Real.log ((∏ p ∈ T', p : ℕ) : ℝ)) + 1) ^ m *
          surgeryDecay (2 * (x + Real.log ((∏ p ∈ T', p : ℕ) : ℝ)))) := by
          refine Finset.sum_le_sum fun T' hT' => hδ _ ?_
          have hd : (1 : ℝ) ≤ ((∏ p ∈ T', p : ℕ) : ℝ) := by
            have : 0 < ∏ p ∈ T', p :=
              Finset.prod_pos fun p hp => (hS p (Finset.mem_powerset.mp hT' hp)).pos
            exact_mod_cast this
          linarith [Real.log_nonneg hd]
      _ = C₁ * σ * ∑ T' ∈ S.powerset, (2 * (x + Real.log ((∏ p ∈ T', p : ℕ) : ℝ)) + 1) ^ m *
          surgeryDecay (2 * (x + Real.log ((∏ p ∈ T', p : ℕ) : ℝ))) := by rw [Finset.mul_sum]
      _ ≤ C₁ * σ * (W * Kd * thetaCuspSourceTerm x 1) := by
          have hC₁ : 0 ≤ C₁ := by norm_num [C₁]
          exact mul_le_mul_of_nonneg_left (sum_deletionShift_le m hS hx) (by positivity)
  have hk := (thetaCuspSourceTerm_one_le_thetaPrimeDeletion S hS hx).1
  have hh := thetaCuspSourceTerm_one_pos_of_nonneg hx
  have hsplit : thetaPrimeDeletion S (plantedDensity N v T) x =
      thetaPrimeDeletion S thetaCuspFullSource x + thetaPrimeDeletion S δ x :=
    thetaPrimeDeletion_add S thetaCuspFullSource δ x
  have hC₁ : 0 ≤ C₁ := by norm_num [C₁]
  have hlt : C₁ * σ * (W * Kd * thetaCuspSourceTerm x 1) < thetaCuspSourceTerm x 1 := by
    have : C₁ * W * Kd * σ < 1 := by nlinarith
    nlinarith
  rw [hsplit]
  linarith [neg_abs_le (thetaPrimeDeletion S δ x)]

/-- **Global positivity of the perturbed density.** -/
theorem eventually_plantedDensity_pos (N : ℕ) {v : ℝ} (hv0 : 0 < v) (hv1 : v ≤ 1 / 4) :
    ∀ᶠ T in atTop, ∀ x, 0 < plantedDensity N v T x := by
  filter_upwards [eventually_thetaPrimeDeletion_plantedDensity_pos N hv0 hv1] with T h x
  have h0 : ∀ y, 0 ≤ y → 0 < plantedDensity N v T y := fun y hy => by
    have := h ∅ (by simp) y hy
    rwa [thetaPrimeDeletion_empty] at this
  rcases le_or_gt 0 x with hx | hx
  · exact h0 x hx
  · have := h0 (-x) (by linarith)
    rwa [plantedDensity, surgeryDensity_neg] at this

/-! ## The surgery theorem -/

/-- **Off-axis zero surgery inside the exact positive renewal reflection class.** Fix `N` and
`0 < v < 1/4`, `a = 1/4`, `c = Θ(1)`. For arbitrarily large `T` the even real-analytic profile
`P_T` satisfies: `P_T(0) = c` with the seam jets of `P` through order `2N+1`; `ν_T > 0` on
`t ≥ 0` with exact renewal mass `q`; the positive kernel `Q_T` is real-analytic with
`Q_T(-t) + Q_T(t) = 2 sinh(at)/t`; `X_T(T + iv) = 0` for a nonzero perturbation; and every
finite literal prime deletion of the perturbed density is positive on the right ray, as is the
density itself on the whole line. -/
theorem reflection_preserving_zero_surgery (N : ℕ) {v : ℝ} (hv0 : 0 < v) (hv1 : v < 1 / 4) :
    ∃ᶠ T in atTop,
      plantedProfile N v T 0 = Θ 1 ∧
      (∀ k ≤ 2 * N + 1,
        iteratedDeriv k (plantedProfile N v T) 0 = iteratedDeriv k thetaLogProfile 0) ∧
      (∀ t, plantedProfile N v T (-t) = plantedProfile N v T t) ∧
      (∀ t, AnalyticAt ℝ (plantedProfile N v T) t) ∧
      (∀ t, 0 ≤ t → 0 < plantedIncrement N v T t) ∧
      (∫ t in Ioi (0 : ℝ), Real.exp (1 / 4 * t) * plantedIncrement N v T t) / Θ 1 =
        thetaRenewalMass ∧
      (∀ t, 0 < t → 0 < plantedLogKernel N v T t) ∧
      (∀ t, AnalyticAt ℝ (plantedLogKernel N v T) t) ∧
      (∀ t, t ≠ 0 →
        plantedLogKernel N v T (-t) + plantedLogKernel N v T t = 2 * Real.sinh (1 / 4 * t) / t) ∧
      plantedXi N v T ((T : ℂ) + v * I) = 0 ∧
      surgeryPerturbation N T (plantedCoeff N v T) ≠ 0 ∧
      (∀ S : Finset ℕ, (∀ p ∈ S, p.Prime) → ∀ x, 0 ≤ x →
        0 < thetaPrimeDeletion S (plantedDensity N v T) x) ∧
      ∀ x, 0 < plantedDensity N v T x := by
  have hv1' : v ≤ 1 / 4 := hv1.le
  have hev := (eventually_plantedCoeff_small N hv0 hv1' one_pos).and <|
    (eventually_plantedIncrement_pos N hv0 hv1').and <|
    (eventually_plantedIncrement_mass N hv0 hv1').and <|
    (eventually_plantedLogKernel N hv0 hv1').and <|
    (eventually_plantedXi_eq_zero N hv0 hv1).and <|
    (eventually_thetaPrimeDeletion_plantedDensity_pos N hv0 hv1').and
    (eventually_plantedDensity_pos N hv0 hv1')
  refine ((frequently_XiC_ne_zero v).and_eventually hev).mono fun T hT => ?_
  obtain ⟨hX, ⟨hT1, _, htr, _⟩, hpos, hmass, hQ, hzero, hdel, hdens⟩ := hT
  exact ⟨surgeryProfile_zero N T _, fun k hk => iteratedDeriv_surgeryProfile_zero N T _ hk,
    surgeryProfile_neg N T _, analyticAt_surgeryProfile N T _, hpos, hmass, hQ.1,
    analyticAt_surgeryLogKernel N T _, fun t ht => surgeryLogKernel_neg_add N T _ ht, hzero.1,
    plantedPerturbation_ne_zero (by rw [abs_of_pos hv0]; exact hv1') hT1 htr hX, hdel, hdens⟩

/-! ## The scalar renewal family has a single smooth member -/

/-- **The scalar family misses seam smoothness.** The even extension of the inverse source
`P_r = rP + (1 - r) c e^{at}` of `D_r = c - rN` is differentiable at the seam only for `r = 1`,
where it is the smooth literal profile. -/
theorem differentiableAt_thetaCouplingProfile_abs_iff (r : ℝ) :
    DifferentiableAt ℝ (fun t => thetaCouplingProfile r |t|) 0 ↔ r = 1 := by
  constructor
  · intro h
    have h1 := (uniqueDiffWithinAt_Ici (0 : ℝ)).eq_deriv _
      (hasDerivWithinAt_thetaCouplingProfile_abs_Ici r) h.hasDerivAt.hasDerivWithinAt
    have h2 := (uniqueDiffWithinAt_Iic (0 : ℝ)).eq_deriv _
      (hasDerivWithinAt_thetaCouplingProfile_abs_Iic r) h.hasDerivAt.hasDerivWithinAt
    have hc := thetaSeam_pos
    have : (1 - r) * Θ 1 = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h
    · linarith
    · linarith
  · rintro rfl
    have : (fun t => thetaCouplingProfile 1 |t|) = thetaLogProfile := by
      funext t; simp [thetaCouplingProfile, thetaLogProfile_abs_eq]
    rw [this]
    exact contDiff_thetaLogProfile.differentiable (by simp) 0

theorem contDiff_thetaCouplingProfile_abs_iff (r : ℝ) :
    ContDiff ℝ ∞ (fun t => thetaCouplingProfile r |t|) ↔ r = 1 := by
  constructor
  · intro h
    exact (differentiableAt_thetaCouplingProfile_abs_iff r).mp (h.differentiable (by simp) 0)
  · rintro rfl
    have : (fun t => thetaCouplingProfile 1 |t|) = thetaLogProfile := by
      funext t; simp [thetaCouplingProfile, thetaLogProfile_abs_eq]
    rw [this]
    exact contDiff_thetaLogProfile

end

end RHTower
