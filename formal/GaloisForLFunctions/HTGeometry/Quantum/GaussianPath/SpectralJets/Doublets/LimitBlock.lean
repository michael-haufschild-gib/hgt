import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.Doublets.WalshWords
import GaloisForLFunctions.HTGeometry.EvenReciprocalTotalPositivity
import Mathlib.Analysis.Analytic.Binomial

/-! # Exponential derivative rank of spin-reversal doublets -/
open Polynomial Matrix Complex
namespace GaloisForLFunctions.HTGeometry.SpectralJets.Doublets
noncomputable section

/-- Upper branch of the normalized two-level matrix with diagonal ±1
and longitudinal off-diagonal entry z, near zero field. -/
def doubletRoot (z : ℂ) : ℂ := (1+z^2)^(1/2:ℂ)

private theorem half_pochhammer (k : ℕ) :
    (descPochhammer ℤ k).smeval (1/2:ℂ) ≠ 0 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [descPochhammer_succ_right,Polynomial.smeval_mul]
    apply mul_ne_zero ih
    have hk : (1/2:ℂ) ≠ k := by
      intro he
      have h := congrArg Complex.re he
      cases k with
      | zero => norm_num at h
      | succ k => push_cast at h; norm_num at h; linarith only [h,Nat.cast_nonneg (α := ℝ) k]
    simpa using sub_ne_zero.mpr hk

private theorem half_choose (k : ℕ) : Ring.choose (1/2:ℂ) k ≠ 0 := by
  rw [Ring.choose_eq_smul,smul_eq_mul]
  exact mul_ne_zero (inv_ne_zero (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k))) (half_pochhammer k)

private theorem root_series :
    HasFPowerSeriesAt doubletRoot (FormalMultilinearSeries.ofScalars ℂ
      (fun j => if Even j then Ring.choose (1/2:ℂ) (j/2) else 0)) 0 :=
  hasFPowerSeriesAt_comp_sq (g := fun z : ℂ => (1+z)^(1/2:ℂ))
    Complex.one_add_cpow_hasFPowerSeriesOnBall_zero.hasFPowerSeriesAt

/-- Every even-order scalar response survives at the avoided crossing. -/
theorem even_root_derivative {m : ℕ} (hm : Even m) : iteratedDeriv m doubletRoot 0 ≠ 0 := by
  rw [iteratedDeriv_eq_of_hasFPowerSeriesAt root_series,if_pos hm]
  exact mul_ne_zero (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero m)) (half_choose _)

/-- On 2ⁿ spin-reversal classes the even-order longitudinal jet of the
normalized doublet has a nonsingular square minor at order n+n%2. -/
theorem doublet_jet_det_ne_zero (n : ℕ) :
    (Matrix.of fun a s : Fin n → Bool =>
      mixed (maskWord a) (fun h => doubletRoot (fieldEnergy (orientedSpin s) h)) 0).det ≠ 0 := by
  let c := iteratedDeriv (n+n%2) doubletRoot 0
  have hc : c ≠ 0 := even_root_derivative ⟨(n+1)/2,by omega⟩
  let W := Walsh.walshMatrix n
  have hdet : W.det ≠ 0 := by
    have h := congrArg Matrix.det (Walsh.walshMatrix_mul_self n)
    rw [Matrix.det_mul,Matrix.det_one] at h
    exact fun he => one_ne_zero (h.symm.trans (by change W.det*W.det=0; rw [he,zero_mul]))
  let r : ℂ := (Walsh.cubeNorm n:ℂ)
  have hr : r ≠ 0 := Complex.ofReal_ne_zero.mpr (Walsh.cubeNorm_pos n).ne'
  have he : (Matrix.of fun a s : Fin n → Bool =>
      mixed (maskWord a) (fun h => doubletRoot (fieldEnergy (orientedSpin s) h)) 0) = (c/r) • W := by
    ext a s
    rw [Matrix.of_apply,mixed_mask_zero _ root_series.analyticAt,Matrix.smul_apply,smul_eq_mul]
    change c * _ = c/r*(r*_)
    field_simp
  rw [he,Matrix.det_smul]
  exact mul_ne_zero (pow_ne_zero _ (div_ne_zero hc hr)) hdet

#print axioms doublet_jet_det_ne_zero
end
end GaloisForLFunctions.HTGeometry.SpectralJets.Doublets
