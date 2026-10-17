import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Normalized Taylor coefficients on a disc

For a function `f` on the closed disc `D̄(c, R)` and a normalization radius `ρ > 0`,
`coeff c R ρ i f = ρ^i (2πi)⁻¹ ∮_{|z−c|=R} f(z) (z − c)^{−(i+1)} dz` is the `i`-th coefficient of `f`
in the basis `((z − c)/ρ)^i`.

* `norm_coeff_le`: `|coeff_i f| ≤ M (ρ/R)^i` when `|f| ≤ M` on the circle.
* `hasSum_coeff`: `f(z) = Σ_i coeff_i f ((z − c)/ρ)^i` on the open disc, for `f` holomorphic on the
  closed disc (Cauchy's formula and the geometric expansion of the Cauchy kernel).
* `hasSum_circleIntegral_of_dominated`: termwise integration of a series dominated on the circle.
* `hasSum_coeff_comp` (substitution): for `g` holomorphic on `D̄(c', R')` and `φ` mapping the circle
  `|z − c| = R` into `D̄(c', r')`, `r' < R'`,
  `Σ_j coeff_i(w ((φ − c')/ρ')^j) coeff'_j(g) = coeff_i(w · g∘φ)`.
-/

open Complex Metric Set Filter Topology MeasureTheory
open scoped Real

noncomputable section

namespace GaloisForLFunctions.HTGeometry.DiscCoefficients

/-- The Cauchy coefficient `(2πi)⁻¹ ∮_{|z−c|=R} f(z)/(z − c)^{i+1} dz`. -/
def cauchyCoeff (c : ℂ) (R : ℝ) (i : ℕ) (f : ℂ → ℂ) : ℂ :=
  (2 * π * I)⁻¹ * ∮ z in C(c, R), ((z - c) ^ (i + 1))⁻¹ * f z

/-- The coefficient in the basis `((z − c)/ρ)^i`. -/
def coeff (c : ℂ) (R ρ : ℝ) (i : ℕ) (f : ℂ → ℂ) : ℂ := (ρ : ℂ) ^ i * cauchyCoeff c R i f

theorem norm_sub_eq_of_mem_sphere {c z : ℂ} {R : ℝ} (hz : z ∈ sphere c R) : ‖z - c‖ = R := by
  rw [← dist_eq_norm]; exact mem_sphere.mp hz

theorem norm_cauchyCoeff_le {c : ℂ} {R M : ℝ} (hR : 0 < R) {f : ℂ → ℂ}
    (hf : ∀ z ∈ sphere c R, ‖f z‖ ≤ M) (i : ℕ) : ‖cauchyCoeff c R i f‖ ≤ M / R ^ i := by
  have hb : ∀ z ∈ sphere c R, ‖((z - c) ^ (i + 1))⁻¹ * f z‖ ≤ (R ^ (i + 1))⁻¹ * M := by
    intro z hz
    rw [norm_mul, norm_inv, norm_pow, norm_sub_eq_of_mem_sphere hz]
    exact mul_le_mul_of_nonneg_left (hf z hz) (by positivity)
  have h := circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const hR.le hb
  unfold cauchyCoeff
  rw [← smul_eq_mul]
  refine h.trans (le_of_eq ?_)
  rw [pow_succ]
  field_simp

theorem norm_coeff_le {c : ℂ} {R ρ M : ℝ} (hR : 0 < R) (hρ : 0 ≤ ρ) {f : ℂ → ℂ}
    (hf : ∀ z ∈ sphere c R, ‖f z‖ ≤ M) (i : ℕ) : ‖coeff c R ρ i f‖ ≤ M * (ρ / R) ^ i := by
  unfold coeff
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hρ, div_pow]
  calc ρ ^ i * ‖cauchyCoeff c R i f‖ ≤ ρ ^ i * (M / R ^ i) :=
        mul_le_mul_of_nonneg_left (norm_cauchyCoeff_le hR hf i) (by positivity)
    _ = M * (ρ ^ i / R ^ i) := by ring

theorem cauchyCoeff_const_mul (c : ℂ) (R : ℝ) (i : ℕ) (a : ℂ) (f : ℂ → ℂ) :
    cauchyCoeff c R i (fun z => a * f z) = a * cauchyCoeff c R i f := by
  unfold cauchyCoeff
  rw [show (fun z => ((z - c) ^ (i + 1))⁻¹ * (a * f z)) =
    fun z => a * (((z - c) ^ (i + 1))⁻¹ * f z) by funext z; ring, circleIntegral.integral_const_mul]
  ring

theorem coeff_const_mul (c : ℂ) (R ρ : ℝ) (i : ℕ) (a : ℂ) (f : ℂ → ℂ) :
    coeff c R ρ i (fun z => a * f z) = a * coeff c R ρ i f := by
  unfold coeff; rw [cauchyCoeff_const_mul]; ring

theorem differentiableAt_of_mem_ball {f : ℂ → ℂ} {c z : ℂ} {R : ℝ}
    (hf : DifferentiableOn ℂ f (closedBall c R)) (hz : z ∈ ball c R) : DifferentiableAt ℂ f z :=
  hf.differentiableAt (mem_of_superset (isOpen_ball.mem_nhds hz) ball_subset_closedBall)

/-- **Taylor expansion in the normalized basis.** -/
theorem hasSum_coeff {c : ℂ} {R ρ : ℝ} (hR : 0 < R) (hρ : 0 < ρ) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (closedBall c R)) {z : ℂ} (hz : z ∈ ball c R) :
    HasSum (fun i => coeff c R ρ i f * ((z - c) / ρ) ^ i) (f z) := by
  have hci : CircleIntegrable f c R :=
    (hf.continuousOn.mono sphere_subset_closedBall).circleIntegrable hR.le
  have hw : ‖z - c‖ < R := by rw [← dist_eq_norm]; exact mem_ball.mp hz
  have h1 := hasSum_two_pi_I_cauchyPowerSeries_integral hci hw
  have hcauchy : (∮ w in C(c, R), (w - z)⁻¹ • f w) = (2 * π * I) • f z :=
    circleIntegral_sub_inv_smul_of_differentiable_on_off_countable countable_empty hz
      hf.continuousOn fun x hx => differentiableAt_of_mem_ball hf hx.1
  rw [add_sub_cancel, hcauchy] at h1
  have h2 := h1.mul_left (2 * π * I)⁻¹
  have hρC : (ρ : ℂ) ≠ 0 := ofReal_ne_zero.mpr hρ.ne'
  have h2pi : (2 * π * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, I_ne_zero]
  have e1 : (fun n => coeff c R ρ n f * ((z - c) / ρ) ^ n) = fun n =>
      (2 * π * I)⁻¹ * ∮ w in C(c, R), ((z - c) / (w - c)) ^ n • (w - c)⁻¹ • f w := by
    funext n
    unfold coeff cauchyCoeff
    have e : (fun w => ((z - c) / (w - c)) ^ n • (w - c)⁻¹ • f w) =
        fun w => (z - c) ^ n * (((w - c) ^ (n + 1))⁻¹ * f w) := by
      funext w; simp only [smul_eq_mul, div_pow, pow_succ, mul_inv]; ring
    rw [e, circleIntegral.integral_const_mul, div_pow]
    field_simp
  have e2 : f z = (2 * π * I)⁻¹ * (2 * π * I) • f z := by
    rw [smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ h2pi, one_mul]
  rw [e1, e2]
  exact h2

/-- **Termwise integration on a circle** of a series dominated by a summable majorant. -/
theorem hasSum_circleIntegral_of_dominated {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ} {c : ℂ} {R : ℝ}
    (hR : 0 ≤ R) (hF : ∀ n, ContinuousOn (F n) (sphere c R)) {u : ℕ → ℝ} (hu : Summable u)
    (hb : ∀ n, ∀ z ∈ sphere c R, ‖F n z‖ ≤ u n)
    (hs : ∀ z ∈ sphere c R, HasSum (fun n => F n z) (f z)) :
    HasSum (fun n => ∮ z in C(c, R), F n z) (∮ z in C(c, R), f z) := by
  have hmem : ∀ θ : ℝ, circleMap c R θ ∈ sphere c R := fun θ => circleMap_mem_sphere c hR θ
  refine intervalIntegral.hasSum_integral_of_dominated_convergence (fun n _ => R * u n)
    (fun n => ?_) (fun n => ?_) ?_ ?_ ?_
  · have hc : Continuous fun θ => F n (circleMap c R θ) :=
      (hF n).comp_continuous (continuous_circleMap c R) hmem
    have hd : Continuous fun θ => deriv (circleMap c R) θ := by
      simp only [deriv_circleMap]; fun_prop
    exact (hd.smul hc).aestronglyMeasurable
  · refine Eventually.of_forall fun θ _ => ?_
    rw [norm_smul, deriv_circleMap, norm_mul, Complex.norm_I, mul_one, norm_circleMap_zero,
      abs_of_nonneg hR]
    exact mul_le_mul_of_nonneg_left (hb n _ (hmem θ)) hR
  · exact Eventually.of_forall fun θ _ => hu.mul_left R
  · exact intervalIntegrable_const
  · exact Eventually.of_forall fun θ _ => (hs _ (hmem θ)).const_smul _

/-- **Substitution**: the coefficients of `w · g∘φ` are the matrix product of the coefficients of
`w ((φ − c')/ρ')^j` with those of `g`. -/
theorem hasSum_coeff_comp {c c' : ℂ} {R R' r' ρ ρ' : ℝ} (hR : 0 < R) (hR' : 0 < R')
    (hρ' : 0 < ρ') (hr0 : 0 ≤ r') (hr' : r' < R') {g φ w : ℂ → ℂ}
    (hg : DifferentiableOn ℂ g (closedBall c' R')) (hφ : ContinuousOn φ (sphere c R))
    (hφm : MapsTo φ (sphere c R) (closedBall c' r')) (hw : ContinuousOn w (sphere c R)) (i : ℕ) :
    HasSum (fun j => coeff c R ρ i (fun z => w z * ((φ z - c') / ρ') ^ j) * coeff c' R' ρ' j g)
      (coeff c R ρ i (fun z => w z * g (φ z))) := by
  obtain ⟨W, hW⟩ := (isCompact_sphere c R).exists_bound_of_continuousOn hw
  obtain ⟨G, hG⟩ := (isCompact_sphere c' R').exists_bound_of_continuousOn
    (hg.continuousOn.mono sphere_subset_closedBall)
  have hW0 : 0 ≤ W := by
    have := hW (c + R) (by simp [abs_of_pos hR]); exact (norm_nonneg _).trans this
  have hG0 : 0 ≤ G := by
    have := hG (c' + R') (by simp [abs_of_pos hR']); exact (norm_nonneg _).trans this
  set a : ℕ → ℂ := fun j => coeff c' R' ρ' j g with ha
  have hab : ∀ j, ‖a j‖ ≤ G * (ρ' / R') ^ j := fun j => norm_coeff_le hR' hρ'.le hG j
  have hball : ∀ z ∈ sphere c R, φ z ∈ ball c' R' := fun z hz =>
    closedBall_subset_ball hr' (hφm hz)
  have hnorm : ∀ z ∈ sphere c R, ‖(φ z - c') / ρ'‖ ≤ r' / ρ' := fun z hz => by
    have h := hφm hz
    rw [mem_closedBall, dist_eq_norm] at h
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ']
    exact div_le_div_of_nonneg_right h hρ'.le
  set F : ℕ → ℂ → ℂ := fun j z => ((z - c) ^ (i + 1))⁻¹ * (w z * (a j * ((φ z - c') / ρ') ^ j))
    with hFdef
  set q : ℝ := r' / R' with hq
  have hq0 : 0 ≤ q := div_nonneg hr0 hR'.le
  have hq1 : q < 1 := (div_lt_one hR').mpr hr'
  have hFb : ∀ j, ∀ z ∈ sphere c R, ‖F j z‖ ≤ (R ^ (i + 1))⁻¹ * W * G * q ^ j := by
    intro j z hz
    simp only [hFdef]
    rw [norm_mul, norm_mul, norm_mul, norm_inv, norm_pow, norm_sub_eq_of_mem_sphere hz, norm_pow]
    have h1 := hW z hz
    have h2 := pow_le_pow_left₀ (norm_nonneg _) (hnorm z hz) j
    have h3 : ‖a j‖ * ‖(φ z - c') / ρ'‖ ^ j ≤ G * q ^ j := by
      calc ‖a j‖ * ‖(φ z - c') / ρ'‖ ^ j ≤ G * (ρ' / R') ^ j * (r' / ρ') ^ j :=
            mul_le_mul (hab j) h2 (by positivity) (by positivity)
        _ = G * q ^ j := by rw [hq, mul_assoc, ← mul_pow]; field_simp
    calc (R ^ (i + 1))⁻¹ * (‖w z‖ * (‖a j‖ * ‖(φ z - c') / ρ'‖ ^ j))
        ≤ (R ^ (i + 1))⁻¹ * (W * (G * q ^ j)) := by gcongr
      _ = (R ^ (i + 1))⁻¹ * W * G * q ^ j := by ring
  have hsum : Summable fun j => (R ^ (i + 1))⁻¹ * W * G * q ^ j :=
    (summable_geometric_of_lt_one hq0 hq1).mul_left _
  have hFc : ∀ j, ContinuousOn (F j) (sphere c R) := by
    intro j
    simp only [hFdef]
    refine ContinuousOn.mul ?_ (hw.mul (continuousOn_const.mul ((hφ.sub continuousOn_const).div_const _ |>.pow j)))
    refine (ContinuousOn.pow (continuousOn_id.sub continuousOn_const) _).inv₀ fun z hz => ?_
    have := norm_sub_eq_of_mem_sphere hz
    exact pow_ne_zero _ (show z - c ≠ 0 from fun h => by rw [h, norm_zero] at this; linarith)
  have hFs : ∀ z ∈ sphere c R, HasSum (fun j => F j z) (((z - c) ^ (i + 1))⁻¹ * (w z * g (φ z))) := by
    intro z hz
    have h := hasSum_coeff hR' hρ' hg (hball z hz)
    simp only [hFdef]
    exact (h.mul_left (w z)).mul_left _
  have hI := hasSum_circleIntegral_of_dominated hR.le hFc hsum hFb hFs
  have hI2 := hI.mul_left ((ρ : ℂ) ^ i * (2 * π * I)⁻¹)
  have e1 : (fun j => coeff c R ρ i (fun z => w z * ((φ z - c') / ρ') ^ j) * a j) =
      fun j => (ρ : ℂ) ^ i * (2 * π * I)⁻¹ * ∮ z in C(c, R), F j z := by
    funext j
    simp only [hFdef]
    have e : (fun z => ((z - c) ^ (i + 1))⁻¹ * (w z * (a j * ((φ z - c') / ρ') ^ j))) =
        fun z => a j * (((z - c) ^ (i + 1))⁻¹ * (w z * ((φ z - c') / ρ') ^ j)) := by
      funext z; ring
    rw [e, circleIntegral.integral_const_mul]
    unfold coeff cauchyCoeff
    ring
  have e2 : coeff c R ρ i (fun z => w z * g (φ z)) = (ρ : ℂ) ^ i * (2 * π * I)⁻¹ *
      ∮ z in C(c, R), ((z - c) ^ (i + 1))⁻¹ * (w z * g (φ z)) := by
    unfold coeff cauchyCoeff; ring
  rw [e2]
  simp only [ha] at e1
  rw [e1]
  exact hI2

end GaloisForLFunctions.HTGeometry.DiscCoefficients

end
