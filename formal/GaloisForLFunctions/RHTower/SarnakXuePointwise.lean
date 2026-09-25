import GaloisForLFunctions.RHTower.SarnakXueKernel
import GaloisForLFunctions.RHTower.HyperbolicBallMeanValue

open MeasureTheory UpperHalfPlane ModularGroup Set Metric
open scoped MatrixGroups Pointwise ENNReal

/-!
# Pointwise pretrace bound and invariance of the kernel sum

With `T = ∫_{B_R(i)} y^s dμ` and `s(1-s) = λ`, the mean-value property `∫_{B_R(v)} u = u(v) T` and the pretrace
inequality give `T² |u(v)|² ≤ L(v) ⟨u, u⟩` for every eigenspace vector (`pointwise_bound`), where
`L(v) = Σ_{h ∈ Γ̄(p)} μ(B_R(v) ∩ h B_R(v))`. Conjugation by `SL(2,ℤ)` permutes `Γ̄(p)` and the action is
isometric and measure-preserving, so `L(Av) = L(v)` (`kernelSum_smul`).
-/

namespace GaloisForLFunctions.RHTower.SarnakXuePointwise

open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.RHTower
open GaloisForLFunctions.RHTower.SarnakXuePretrace
open GaloisForLFunctions.RHTower.SarnakXueInner
open GaloisForLFunctions.RHTower.SarnakXueKernel
open GaloisForLFunctions.RHTower.HyperbolicPointPairCentre
open GaloisForLFunctions.RHTower.HyperbolicPowerEigen

noncomputable section

variable {N : ℕ} {lam : ℝ}

/-- The kernel sum at a point. -/
def kernelSum (p : ℕ) (v : ℍ) (R : ℝ) : ℝ≥0∞ :=
  ∑' h : gammaBar p, volume (closedBall v R ∩ h • closedBall v R)

theorem powerEigen_real (s : ℝ) (w : ℍ) : powerEigen (s : ℂ) w = ((w.im ^ s : ℝ) : ℂ) := by
  rw [powerEigen, Complex.ofReal_cpow w.im_pos.le]

/-- **Pointwise pretrace bound.** With `T = ∫_{B_R(i)} y^s dμ` and `s(1-s) = λ`,
`T² |u(v)|² ≤ L(v) ⟨u, u⟩` for every eigenspace vector `u`. -/
theorem pointwise_bound (u : V N lam) {s : ℝ} (hs : s * (1 - s) = lam) (v : ℍ) (R : ℝ)
    (hL : kernelSum (N + 1) v R ≠ ⊤) :
    (∫ w in closedBall I R, w.im ^ s) ^ 2 * ‖u.1 v‖ ^ 2 ≤
      (kernelSum (N + 1) v R).toReal * (ip u u).re := by
  set T := ∫ w in closedBall I R, w.im ^ s
  have hGe : ∀ z, positiveHyperbolicLaplacian u.1 z = (s : ℂ) * (1 - s) * u.1 z := by
    intro z
    rw [u.2.2.1.2 z]
    congr 1
    rw [← hs]; push_cast; ring
  have hmv := setIntegral_closedBall_eigen v R u.2.2.1.1 hGe
  have hT : (∫ w in closedBall I R, powerEigen (s : ℂ) w) = (T : ℂ) := by
    simp_rw [powerEigen_real]
    exact integral_ofReal
  rw [hT] at hmv
  have hpre := pretrace u v R
  set J := ∫⁻ z in closedBall v R, ‖u.1 z‖ₑ
  have hRHS : kernelSum (N + 1) v R * ENNReal.ofReal (ip u u).re ≠ ⊤ :=
    ENNReal.mul_ne_top hL ENNReal.ofReal_ne_top
  have hJ : J ≠ ⊤ := by
    intro h
    apply hRHS
    apply top_le_iff.mp
    rw [h] at hpre
    simpa [kernelSum] using hpre
  have h1 : ‖u.1 v * (T : ℂ)‖ ≤ J.toReal := by
    rw [← hmv]
    have := enorm_integral_le_lintegral_enorm (μ := volume.restrict (closedBall v R)) u.1
    rw [← ofReal_norm] at this
    exact (ENNReal.ofReal_le_iff_le_toReal hJ).mp this
  have h2 : J.toReal ^ 2 ≤ (kernelSum (N + 1) v R).toReal * (ip u u).re := by
    have := ENNReal.toReal_mono hRHS hpre
    rw [ENNReal.toReal_pow, ENNReal.toReal_mul, ENNReal.toReal_ofReal (ip_self_re_nonneg u)] at this
    exact this
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs] at h1
  calc T ^ 2 * ‖u.1 v‖ ^ 2 = (‖u.1 v‖ * |T|) ^ 2 := by rw [mul_pow, sq_abs]; ring
    _ ≤ J.toReal ^ 2 := pow_le_pow_left₀ (by positivity) h1 2
    _ ≤ _ := h2


open CongruenceSubgroup

theorem conj_mem_gammaBar {p : ℕ} (a : PSL2Z) {h : PSL2Z} (hh : h ∈ gammaBar p) :
    a⁻¹ * h * a ∈ gammaBar p := by
  obtain ⟨γ, hγ, rfl⟩ := hh
  induction a using QuotientGroup.induction_on with
  | H A =>
    refine ⟨A⁻¹ * γ * A, ?_, by simp⟩
    have := (Gamma_normal p).conj_mem γ hγ A⁻¹
    simpa using this

/-- Conjugation by `a ∈ PSL(2,ℤ)` permutes `Γ̄(p)`. -/
def conjEquiv {p : ℕ} (a : PSL2Z) : gammaBar p ≃ gammaBar p where
  toFun h := ⟨a⁻¹ * h * a, conj_mem_gammaBar a h.2⟩
  invFun h := ⟨a * h * a⁻¹, by simpa using conj_mem_gammaBar a⁻¹ h.2⟩
  left_inv h := by ext; simp [mul_assoc]
  right_inv h := by ext; simp [mul_assoc]

theorem sl_smul_closedBall (A : SL(2, ℤ)) (v : ℍ) (R : ℝ) :
    A • closedBall v R = closedBall (A • v) R := by
  ext z
  simp only [mem_smul_set_iff_inv_smul_mem, mem_closedBall]
  have := dist_sl_smul A (A⁻¹ • z) v
  rw [smul_inv_smul] at this
  rw [this]

/-- **Invariance of the kernel sum** under `SL(2,ℤ)`. -/
theorem kernelSum_smul {p : ℕ} (A : SL(2, ℤ)) (v : ℍ) (R : ℝ) :
    kernelSum p (A • v) R = kernelSum p v R := by
  unfold kernelSum
  set a : PSL2Z := QuotientGroup.mk A
  have hball : closedBall (A • v) R = a • closedBall v R := by
    rw [← sl_smul_closedBall, PSL2Z_mk_smul_set]
  rw [← (conjEquiv (p := p) a).symm.tsum_eq]
  apply tsum_congr
  intro h
  rw [hball]
  have e : ((conjEquiv (p := p) a).symm h : PSL2Z) = a * h * a⁻¹ := rfl
  rw [Subgroup.smul_def, e, show (a * (h : PSL2Z) * a⁻¹) • a • closedBall v R =
      a • ((h : PSL2Z) • closedBall v R) by rw [smul_smul, smul_smul, mul_assoc, inv_mul_cancel, mul_one],
    ← smul_set_inter, measure_smul]
  rfl

end
end GaloisForLFunctions.RHTower.SarnakXuePointwise
