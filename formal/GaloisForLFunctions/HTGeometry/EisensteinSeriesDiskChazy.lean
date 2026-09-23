import GaloisForLFunctions.Bottcher.RamanujanChazy
import GaloisForLFunctions.Bottcher.AnalyticDomain
import GaloisForLFunctions.HTGeometry.ReciprocalSubstitutionInjective

/-!
# The Eisenstein series `E₂` on the unit disk

This module transfers the upper-half-plane Chazy equation to the analytic `q`-expansion of `E₂` on
the open unit disk.  It then expands the Euler derivation `δ = q d/dq` into ordinary derivatives
and supplies an explicit nonzero multivariate differential polynomial.  Consequently the disk
function is differentially algebraic on its actual domain, without asserting a global analytic
continuation.
-/

open UpperHalfPlane hiding I
open Real Complex Filter Topology Set Metric
open ModularForm EisensteinSeries MatrixGroups SlashInvariantForm MvPolynomial
open scoped MatrixGroups Manifold

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The analytic `q`-expansion of the quasimodular Eisenstein series `E₂` on the unit disk. -/
def e2Disk : ℂ → ℂ :=
  UpperHalfPlane.cuspFunction 1 EisensteinSeries.E2

theorem e2Disk_analyticOnNhd : AnalyticOnNhd ℂ e2Disk (ball 0 1) := by
  exact (UpperHalfPlane.differentiableOn_cuspFunction_ball one_pos
    Bottcher.E2_periodic_comp_ramanujan E2_mdifferentiable
      EisensteinSeries.isBoundedAtImInfty_E2).analyticOnNhd isOpen_ball

/-- Euler derivation `δf(q) = q f'(q)`. -/
def eulerDeriv (f : ℂ → ℂ) (q : ℂ) : ℂ := q * deriv f q

theorem analyticOnNhd_eulerDeriv {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (ball 0 1)) :
    AnalyticOnNhd ℂ (eulerDeriv f) (ball 0 1) := by
  exact analyticOnNhd_id.mul (hf.deriv_of_isOpen isOpen_ball)

/-- Under `q = exp(2πiτ)`, the disk Euler derivation is the normalized `τ`-derivative. -/
theorem eulerDeriv_qParam_of_eq {f : ℂ → ℂ} {F : ℍ → ℂ}
    (hf : AnalyticOnNhd ℂ f (ball 0 1))
    (heq : ∀ τ : ℍ, f (Function.Periodic.qParam 1 τ) = F τ) (τ : ℍ) :
    eulerDeriv f (Function.Periodic.qParam 1 τ) =
      Derivative.normalizedDerivOfComplex F τ := by
  let q : ℂ → ℂ := Function.Periodic.qParam 1
  have hqnorm : ‖q τ‖ < 1 := Function.Periodic.norm_qParam_lt_one one_pos τ.im_pos
  have hqmem : q τ ∈ ball (0 : ℂ) 1 := by simpa [mem_ball] using hqnorm
  have hdisk : DifferentiableAt ℂ f (q τ) := (hf (q τ) hqmem).differentiableAt
  have hq : HasDerivAt q (q τ * (2 * Real.pi * I)) τ := by
    unfold q Function.Periodic.qParam
    simpa only [ofReal_one, div_one, id_eq, mul_one] using
      ((((hasDerivAt_id (τ : ℂ)).const_mul (2 * (Real.pi : ℂ) * I)).div_const
        (1 : ℂ)).cexp)
  have hlocal : (f ∘ q) =ᶠ[𝓝 (τ : ℂ)] (F ∘ UpperHalfPlane.ofComplex) := by
    filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds τ.im_pos] with w hw
    have hτ : (⟨w, hw⟩ : ℍ) = UpperHalfPlane.ofComplex w := by
      ext
      simp [UpperHalfPlane.ofComplex_apply_of_im_pos hw]
    simp only [Function.comp_apply]
    rw [show q w = Function.Periodic.qParam 1 (⟨w, hw⟩ : ℍ) from rfl, heq, ← hτ]
  have hderiv : deriv (F ∘ UpperHalfPlane.ofComplex) τ =
      deriv f (q τ) * (q τ * (2 * Real.pi * I)) := by
    rw [← hlocal.deriv_eq]
    exact (hdisk.hasDerivAt.comp (τ : ℂ) hq).deriv
  rw [eulerDeriv, Derivative.normalizedDerivOfComplex, hderiv]
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp [hpi, Complex.I_ne_zero]
  ring

theorem e2Disk_qParam (τ : ℍ) :
    e2Disk (Function.Periodic.qParam 1 τ) = EisensteinSeries.E2 τ := by
  exact UpperHalfPlane.eq_cuspFunction τ one_ne_zero
    Bottcher.E2_periodic_comp_ramanujan

theorem eulerDeriv_e2Disk_qParam (τ : ℍ) :
    eulerDeriv e2Disk (Function.Periodic.qParam 1 τ) =
      Derivative.normalizedDerivOfComplex EisensteinSeries.E2 τ :=
  eulerDeriv_qParam_of_eq e2Disk_analyticOnNhd e2Disk_qParam τ

theorem eulerDeriv_two_e2Disk_qParam (τ : ℍ) :
    eulerDeriv (eulerDeriv e2Disk) (Function.Periodic.qParam 1 τ) =
      Derivative.normalizedDerivOfComplex
        (Derivative.normalizedDerivOfComplex EisensteinSeries.E2) τ :=
  eulerDeriv_qParam_of_eq (analyticOnNhd_eulerDeriv e2Disk_analyticOnNhd)
    eulerDeriv_e2Disk_qParam τ

theorem eulerDeriv_three_e2Disk_qParam (τ : ℍ) :
    eulerDeriv (eulerDeriv (eulerDeriv e2Disk))
        (Function.Periodic.qParam 1 τ) =
      Derivative.normalizedDerivOfComplex
        (Derivative.normalizedDerivOfComplex
          (Derivative.normalizedDerivOfComplex EisensteinSeries.E2)) τ :=
  eulerDeriv_qParam_of_eq
    (analyticOnNhd_eulerDeriv (analyticOnNhd_eulerDeriv e2Disk_analyticOnNhd))
    eulerDeriv_two_e2Disk_qParam τ

theorem invQParam_one_im_pos {q : ℂ} (hq0 : q ≠ 0) (hqnorm : ‖q‖ < 1) :
    0 < (Function.Periodic.invQParam 1 q).im := by
  have him : (Function.Periodic.invQParam 1 q).im =
      -(1 / (2 * Real.pi)) * Real.log ‖q‖ := by
    unfold Function.Periodic.invQParam
    simp only [ofReal_one]
    rw [show (1 : ℂ) / (2 * (Real.pi : ℂ) * I) =
        -(1 / (2 * (Real.pi : ℂ))) * I by
      have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
      field_simp [hpi, Complex.I_ne_zero]
      simp [Complex.I_sq]]
    norm_num [Complex.mul_im, Complex.mul_re, Complex.log_re]
  rw [him]
  have hlog : Real.log ‖q‖ < 0 := Real.log_neg (norm_pos_iff.mpr hq0) hqnorm
  have hcoef : 0 < 1 / (2 * Real.pi) :=
    div_pos one_pos (mul_pos (by norm_num) Real.pi_pos)
  exact mul_pos_of_neg_of_neg (neg_neg_of_pos hcoef) hlog

theorem qParam_one_invQParam_one {q : ℂ} (hq0 : q ≠ 0) :
    Function.Periodic.qParam 1 (Function.Periodic.invQParam 1 q) = q := by
  unfold Function.Periodic.qParam Function.Periodic.invQParam
  simp only [ofReal_one, div_one]
  rw [show 2 * (Real.pi : ℂ) * I *
      ((1 : ℂ) / (2 * (Real.pi : ℂ) * I) * Complex.log q) =
        Complex.log q by
    have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    field_simp [hpi, Complex.I_ne_zero]]
  exact Complex.exp_log hq0

/-- Chazy defect of the disk `E₂`, expressed using the Euler derivation. -/
def e2DiskChazyDefect (q : ℂ) : ℂ :=
  2 * eulerDeriv (eulerDeriv (eulerDeriv e2Disk)) q -
    2 * e2Disk q * eulerDeriv (eulerDeriv e2Disk) q +
      3 * eulerDeriv e2Disk q ^ (2 : ℕ)

theorem e2DiskChazyDefect_analyticOnNhd :
    AnalyticOnNhd ℂ e2DiskChazyDefect (ball 0 1) := by
  have h1 := analyticOnNhd_eulerDeriv e2Disk_analyticOnNhd
  have h2 := analyticOnNhd_eulerDeriv h1
  have h3 := analyticOnNhd_eulerDeriv h2
  exact ((analyticOnNhd_const.mul h3).sub
    ((analyticOnNhd_const.mul e2Disk_analyticOnNhd).mul h2)).add
      (analyticOnNhd_const.mul (h1.pow 2))

theorem e2DiskChazyDefect_eq_zero_of_ne {q : ℂ}
    (hq : q ∈ ball 0 1) (hq0 : q ≠ 0) : e2DiskChazyDefect q = 0 := by
  have hqnorm : ‖q‖ < 1 := by simpa [mem_ball] using hq
  let τ : ℍ := ⟨Function.Periodic.invQParam 1 q, invQParam_one_im_pos hq0 hqnorm⟩
  have hqp : Function.Periodic.qParam 1 τ = q := qParam_one_invQParam_one hq0
  have hc := Bottcher.chazy_eisensteinSeries_E2 τ
  rw [← hqp]
  unfold e2DiskChazyDefect
  rw [eulerDeriv_three_e2Disk_qParam, eulerDeriv_two_e2Disk_qParam,
    e2Disk_qParam, eulerDeriv_e2Disk_qParam]
  exact hc

theorem e2DiskChazyDefect_eq_zero : EqOn e2DiskChazyDefect 0 (ball 0 1) := by
  let V : Set ℂ := ball (1 / 2 : ℂ) (1 / 4)
  have hVU : V ⊆ ball (0 : ℂ) 1 := by
    intro q hq
    rw [mem_ball] at hq ⊢
    have htri : ‖q‖ ≤ ‖q - (1 / 2 : ℂ)‖ + ‖(1 / 2 : ℂ)‖ := by
      calc
        ‖q‖ = ‖(q - (1 / 2 : ℂ)) + (1 / 2 : ℂ)‖ := by ring_nf
        _ ≤ _ := norm_add_le _ _
    have hdist : ‖q - (1 / 2 : ℂ)‖ < 1 / 4 := by
      simpa [Complex.dist_eq] using hq
    have hhalf : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
    rw [hhalf] at htri
    norm_num at hdist ⊢
    linarith
  have hVne : V.Nonempty := ⟨(1 / 2 : ℂ), by simp [V]⟩
  apply Bottcher.analyticOnNhd_eqOn_of_eqOn_isOpen e2DiskChazyDefect_analyticOnNhd
    analyticOnNhd_const (convex_ball (0 : ℂ) 1).isPreconnected hVU isOpen_ball hVne
  intro q hq
  apply e2DiskChazyDefect_eq_zero_of_ne (hVU hq)
  intro hq0
  subst q
  have : ‖(1 / 2 : ℂ)‖ < 1 / 4 := by
    simpa [V, mem_ball, Complex.dist_eq] using hq
  norm_num at this

/-- Expansion `δ²f = qf' + q²f''` on an analytic domain. -/
theorem eulerDeriv_two_eq {f : ℂ → ℂ} {U : Set ℂ}
    (hf : AnalyticOnNhd ℂ f U) {q : ℂ} (hq : q ∈ U) :
    eulerDeriv (eulerDeriv f) q =
      q * iteratedDeriv 1 f q + q ^ (2 : ℕ) * iteratedDeriv 2 f q := by
  have h1 := hasDerivAt_iteratedDeriv_of_analyticOnNhd hf 1 hq
  have hfun : iteratedDeriv 1 f = deriv f := by
    simp [iteratedDeriv_succ, iteratedDeriv_zero]
  rw [hfun] at h1
  have hd : deriv (eulerDeriv f) q =
      deriv f q + q * iteratedDeriv 2 f q := by
    unfold eulerDeriv
    change deriv (id * deriv f) q = deriv f q + q * iteratedDeriv 2 f q
    simpa only [id_eq, one_mul, Nat.reduceAdd] using
      ((hasDerivAt_id q).mul h1).deriv
  rw [eulerDeriv, hd]
  simp only [iteratedDeriv_succ, iteratedDeriv_zero]
  ring

/-- Expansion `δ³f = qf' + 3q²f'' + q³f'''` on an open analytic domain. -/
theorem eulerDeriv_three_eq {f : ℂ → ℂ} {U : Set ℂ}
    (hf : AnalyticOnNhd ℂ f U) (hU : IsOpen U) {q : ℂ} (hq : q ∈ U) :
    eulerDeriv (eulerDeriv (eulerDeriv f)) q =
      q * iteratedDeriv 1 f q + 3 * q ^ (2 : ℕ) * iteratedDeriv 2 f q +
        q ^ (3 : ℕ) * iteratedDeriv 3 f q := by
  let rhs : ℂ → ℂ := fun z =>
    z * iteratedDeriv 1 f z + z ^ (2 : ℕ) * iteratedDeriv 2 f z
  have heq : eulerDeriv (eulerDeriv f) =ᶠ[𝓝 q] rhs := by
    filter_upwards [hU.mem_nhds hq] with z hz
    exact eulerDeriv_two_eq hf hz
  have h1 := hasDerivAt_iteratedDeriv_of_analyticOnNhd hf 1 hq
  have h2 := hasDerivAt_iteratedDeriv_of_analyticOnNhd hf 2 hq
  have hrhs := ((hasDerivAt_id q).mul h1).add
    (((hasDerivAt_id q).pow 2).mul h2)
  have hrhs_eq : rhs =
      id * iteratedDeriv 1 f + id ^ (2 : ℕ) * iteratedDeriv 2 f := by
    funext z
    simp [rhs]
  have hd : deriv (eulerDeriv (eulerDeriv f)) q =
      iteratedDeriv 1 f q + q * iteratedDeriv 2 f q +
        (2 * q) * iteratedDeriv 2 f q + q ^ (2 : ℕ) * iteratedDeriv 3 f q := by
    rw [heq.deriv_eq, hrhs_eq]
    have h := hrhs.deriv
    simp only [id_eq, one_mul, Nat.reduceAdd, Nat.cast_ofNat, Nat.reduceSub,
      pow_one, mul_one, Pi.pow_apply] at h
    rw [h]
    ring
  rw [eulerDeriv, hd]
  ring

/-- Ordinary differential polynomial obtained by expanding the disk Chazy equation. -/
def e2ChazyJetPolynomial : MvPolynomial (Fin 5) ℂ :=
  let x0 := X (0 : Fin 5)
  let x1 := X (Fin.succ (0 : Fin 4))
  let x2 := X (Fin.succ (Fin.succ (0 : Fin 3)))
  let x3 := X (Fin.succ (Fin.succ (Fin.succ (0 : Fin 2))))
  let x4 := X (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 1)))))
  2 * (x0 * x2 + 3 * x0 ^ (2 : ℕ) * x3 + x0 ^ (3 : ℕ) * x4) -
    2 * x1 * (x0 * x2 + x0 ^ (2 : ℕ) * x3) + 3 * (x0 * x2) ^ (2 : ℕ)

theorem e2ChazyJetPolynomial_ne_zero : e2ChazyJetPolynomial ≠ 0 := by
  intro h
  have he := congrArg (MvPolynomial.eval (fun _ : Fin 5 => (1 : ℂ))) h
  norm_num [e2ChazyJetPolynomial] at he

theorem e2ChazyJetPolynomial_eval (f : ℂ → ℂ) (q : ℂ) :
    MvPolynomial.eval
      (Fin.cons q (fun j : Fin 4 => iteratedDeriv (j : ℕ) f q))
        e2ChazyJetPolynomial =
      2 * (q * iteratedDeriv 1 f q + 3 * q ^ (2 : ℕ) * iteratedDeriv 2 f q +
        q ^ (3 : ℕ) * iteratedDeriv 3 f q) -
      2 * f q * (q * iteratedDeriv 1 f q + q ^ (2 : ℕ) * iteratedDeriv 2 f q) +
        3 * (q * iteratedDeriv 1 f q) ^ (2 : ℕ) := by
  simp only [e2ChazyJetPolynomial, map_sub, map_add, map_mul, map_pow, map_ofNat,
    eval_X]
  change
    2 * (q * iteratedDeriv 1 f q + 3 * q ^ (2 : ℕ) * iteratedDeriv 2 f q +
      q ^ (3 : ℕ) * iteratedDeriv 3 f q) -
        2 * f q * (q * iteratedDeriv 1 f q + q ^ (2 : ℕ) * iteratedDeriv 2 f q) +
      3 * (q * iteratedDeriv 1 f q) ^ (2 : ℕ) = _
  rfl

/-- The unit-disk `q`-expansion of `E₂` satisfies an explicit nonzero order-three ADE. -/
theorem e2Disk_differentiallyAlgebraicOn :
    DifferentiallyAlgebraicOn e2Disk (ball 0 1) := by
  refine ⟨3, e2ChazyJetPolynomial, e2ChazyJetPolynomial_ne_zero, ?_⟩
  intro q hq
  have h2 := eulerDeriv_two_eq e2Disk_analyticOnNhd hq
  have h3 := eulerDeriv_three_eq e2Disk_analyticOnNhd isOpen_ball hq
  have hc := e2DiskChazyDefect_eq_zero hq
  rw [e2ChazyJetPolynomial_eval]
  unfold e2DiskChazyDefect at hc
  rw [h2, h3] at hc
  have h1 : eulerDeriv e2Disk q = q * iteratedDeriv 1 e2Disk q := by
    simp [eulerDeriv, iteratedDeriv_succ, iteratedDeriv_zero]
  rw [h1] at hc
  exact hc

end

end GaloisForLFunctions.HTGeometry
