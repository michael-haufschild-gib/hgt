import GaloisForLFunctions.HTGeometry.EulerQGammaLanding
import GaloisForLFunctions.HTGeometry.ConstitutiveQGammaProcess

/-!
# The arithmetic observable and its compact resolvent

The global logarithmic observable of the Euler q-Gamma process is
`X_σ(m) = log ζ(σ) − σ·log m`, whose exponential response is exactly `ζ(σ)^s · m^{-σs}` — the
factor that turns the arithmetic Dirichlet series into the exponential response of the
random-integer law.  Its spectral values run off to `−∞`, so the diagonal operator inverting
`X_σ − i` on `ℓ²` is compact: this is the operator clause of the recurrent-observer theorem, in the
only form mathlib can state it, since mathlib has no unbounded self-adjoint operator theory.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter Topology

set_option maxHeartbeats 1000000

noncomputable section

/-! ## The real zeta value -/

/-- The real value `ζ(σ)` of the zeta function at the real point `σ > 1`. -/
def eqgZetaReal (σ : EulerSigma) : ℝ := Real.exp (-eqgLogUnit σ)

theorem eqgZetaReal_pos (σ : EulerSigma) : 0 < eqgZetaReal σ := Real.exp_pos _

theorem ofReal_eqgZetaReal (σ : EulerSigma) :
    ((eqgZetaReal σ : ℝ) : ℂ) = riemannZeta (σ.val : ℂ) := (zeta_eq_exp σ).symm

theorem log_eqgZetaReal (σ : EulerSigma) : Real.log (eqgZetaReal σ) = -eqgLogUnit σ := by
  rw [eqgZetaReal, Real.log_exp]

/-! ## The global observable -/

/-- **Equation (EQG.8).**  The global logarithmic observable `X_σ = log ζ(σ) − σ·log M`. -/
def eqgObservable (σ : EulerSigma) (m : ℕ) : ℝ :=
  Real.log (eqgZetaReal σ) - σ.val * Real.log m

theorem eqgObservable_eq (σ : EulerSigma) (m : ℕ) :
    eqgObservable σ m = -eqgLogUnit σ - σ.val * Real.log m := by
  rw [eqgObservable, log_eqgZetaReal]

/-- **The exponential response of the observable** is `ζ(σ)^s·m^{-σs}`. -/
theorem exp_eqgObservable (σ : EulerSigma) (s : ℂ) {m : ℕ} (hm : m ≠ 0) :
    Complex.exp (s * ((eqgObservable σ m : ℝ) : ℂ))
      = riemannZeta (σ.val : ℂ) ^ s * ((m : ℂ) ^ (-((σ.val : ℂ) * s))) := by
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hm
  have hmC : ((m : ℕ) : ℂ) ≠ 0 := by
    simp only [ne_eq, Nat.cast_eq_zero]
    exact hm
  have hzeta : riemannZeta (σ.val : ℂ) ^ s
      = Complex.exp (((Real.log (eqgZetaReal σ) : ℝ) : ℂ) * s) := by
    rw [← ofReal_eqgZetaReal,
      Complex.cpow_def_of_ne_zero (by
        simp only [ne_eq, Complex.ofReal_eq_zero]
        exact (eqgZetaReal_pos σ).ne'),
      ← Complex.ofReal_log (eqgZetaReal_pos σ).le]
  have hpow : ((m : ℂ)) ^ (-((σ.val : ℂ) * s))
      = Complex.exp (((Real.log (m : ℝ) : ℝ) : ℂ) * (-((σ.val : ℂ) * s))) := by
    rw [Complex.cpow_def_of_ne_zero hmC, ← Complex.ofReal_natCast,
      ← Complex.ofReal_log (le_of_lt hmR)]
  rw [hzeta, hpow, ← Complex.exp_add, eqgObservable]
  congr 1
  push_cast
  ring

/-! ## The spectral values run off to infinity -/

theorem tendsto_eqgObservable_atBot (σ : EulerSigma) :
    Tendsto (eqgObservable σ) atTop atBot := by
  have hlog : Tendsto (fun m : ℕ => Real.log (m : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hscale : Tendsto (fun m : ℕ => σ.val * Real.log (m : ℝ)) atTop atTop :=
    Filter.Tendsto.const_mul_atTop σ.pos hlog
  have hneg : Tendsto (fun m : ℕ => -(σ.val * Real.log (m : ℝ))) atTop atBot :=
    tendsto_neg_atTop_atBot.comp hscale
  have hadd : Tendsto (fun m : ℕ =>
      Real.log (eqgZetaReal σ) + -(σ.val * Real.log (m : ℝ))) atTop atBot :=
    Filter.tendsto_atBot_add_const_left _ (Real.log (eqgZetaReal σ)) hneg
  refine hadd.congr fun m => ?_
  rw [eqgObservable]
  ring

/-! ## The compact resolvent -/

/-- The resolvent entry `(X_σ(m) − i)⁻¹`. -/
def eqgResolventEntry (σ : EulerSigma) (m : ℕ) : ℂ :=
  (((eqgObservable σ m : ℝ) : ℂ) - Complex.I)⁻¹

theorem one_le_norm_eqgObservable_sub_I (σ : EulerSigma) (m : ℕ) :
    1 ≤ ‖((eqgObservable σ m : ℝ) : ℂ) - Complex.I‖ := by
  have him : (((eqgObservable σ m : ℝ) : ℂ) - Complex.I).im = -1 := by simp
  have h := Complex.abs_im_le_norm (((eqgObservable σ m : ℝ) : ℂ) - Complex.I)
  rw [him] at h
  simpa using h

theorem eqgResolventEntry_bound (σ : EulerSigma) (m : ℕ) : ‖eqgResolventEntry σ m‖ ≤ 1 := by
  rw [eqgResolventEntry, norm_inv, inv_le_one_iff₀]
  right
  exact one_le_norm_eqgObservable_sub_I σ m

/-- **The resolvent inverts `X_σ − i` coordinatewise.** -/
theorem eqgResolventEntry_mul (σ : EulerSigma) (m : ℕ) :
    (((eqgObservable σ m : ℝ) : ℂ) - Complex.I) * eqgResolventEntry σ m = 1 := by
  rw [eqgResolventEntry, mul_inv_cancel₀]
  intro h0
  have h := one_le_norm_eqgObservable_sub_I σ m
  rw [h0, norm_zero] at h
  linarith

theorem tendsto_norm_eqgResolventEntry (σ : EulerSigma) :
    Tendsto (fun m => ‖eqgResolventEntry σ m‖) atTop (𝓝 0) := by
  have habs : Tendsto (fun m : ℕ => |eqgObservable σ m|) atTop atTop :=
    tendsto_abs_atBot_atTop.comp (tendsto_eqgObservable_atBot σ)
  have hnorm : Tendsto (fun m : ℕ => ‖((eqgObservable σ m : ℝ) : ℂ) - Complex.I‖)
      atTop atTop := by
    refine Filter.tendsto_atTop_mono (fun m => ?_) habs
    have h := Complex.abs_re_le_norm (((eqgObservable σ m : ℝ) : ℂ) - Complex.I)
    have hre : (((eqgObservable σ m : ℝ) : ℂ) - Complex.I).re = eqgObservable σ m := by simp
    rw [hre] at h
    exact h
  have hinv := hnorm.inv_tendsto_atTop
  refine hinv.congr fun m => ?_
  rw [eqgResolventEntry, norm_inv]
  rfl

/-- The resolvent of the arithmetic observable, as a diagonal operator on `ℓ²`. -/
def eqgResolvent (σ : EulerSigma) : QGammaSpace →L[ℂ] QGammaSpace :=
  lpDiagCLM (eqgResolventEntry σ) (eqgResolventEntry_bound σ)

/-- **Theorem 8.1, the compact-resolvent clause.**  The spectral values of the arithmetic
observable run off to infinity, so the diagonal operator inverting `X_σ − i` is compact. -/
theorem isCompactOperator_eqgResolvent (σ : EulerSigma) :
    IsCompactOperator (eqgResolvent σ) :=
  isCompactOperator_lpDiagCLM _ (tendsto_norm_eqgResolventEntry σ)

end

end GaloisForLFunctions.HTGeometry
