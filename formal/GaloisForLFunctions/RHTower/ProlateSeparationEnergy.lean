import GaloisForLFunctions.RHTower.SlepianKernelScaledFubini

/-!
# Energy sign of the prolate separation parameter

Integration by parts has no boundary contribution because `1-x²` vanishes at both aperture
endpoints.  Consequently the prolate action has a nonpositive quadratic form.  Every nonzero
joint band/prolate mode therefore has nonpositive angular separation eigenvalue, equivalently a
nonnegative radial separation ratio.
-/

noncomputable section

open MeasureTheory Set intervalIntegral

namespace GaloisForLFunctions.RHTower

open _root_.RHTower

/-- Exact Dirichlet-form identity for the prolate action on `[-1,1]`. -/
theorem integral_mul_prolateSLAction_eq_neg_energy
    {c : ℝ} {Phi : ℝ → ℝ}
    (h1 : Differentiable ℝ Phi)
    (h2 : Differentiable ℝ (deriv Phi))
    (h2c : Continuous (deriv (deriv Phi))) :
    (∫ x in (-1 : ℝ)..1, Phi x * prolateSLAction c Phi x) =
      -(∫ x in (-1 : ℝ)..1, (1 - x ^ (2 : ℕ)) * (deriv Phi x) ^ (2 : ℕ))
        - ∫ x in (-1 : ℝ)..1, c ^ (2 : ℕ) * x ^ (2 : ℕ) * Phi x ^ (2 : ℕ) := by
  have hflux := _root_.RHTower.band_flux_integral_by_parts h2 h2c h1 h2.continuous
  have hA : IntervalIntegrable
      (fun x : ℝ => Phi x * (-(2 * x) * deriv Phi x
        + (1 - x ^ (2 : ℕ)) * deriv (deriv Phi) x)) volume (-1) 1 := by
    exact (h1.continuous.mul
      (((continuous_const.mul continuous_id).neg.mul h2.continuous).add
        ((continuous_const.sub (continuous_id.pow 2)).mul h2c))).intervalIntegrable _ _
  have hB : IntervalIntegrable
      (fun x : ℝ => Phi x * (c ^ (2 : ℕ) * x ^ (2 : ℕ) * Phi x)) volume (-1) 1 := by
    exact (h1.continuous.mul
      ((continuous_const.mul (continuous_id.pow 2)).mul h1.continuous)).intervalIntegrable _ _
  have hgradEq :
      (∫ x in (-1 : ℝ)..1, deriv Phi x * ((1 - x ^ (2 : ℕ)) * deriv Phi x)) =
        ∫ x in (-1 : ℝ)..1, (1 - x ^ (2 : ℕ)) * (deriv Phi x) ^ (2 : ℕ) := by
    refine intervalIntegral.integral_congr fun x _ => ?_
    ring
  have hpotEq :
      (∫ x in (-1 : ℝ)..1, Phi x * (c ^ (2 : ℕ) * x ^ (2 : ℕ) * Phi x)) =
        ∫ x in (-1 : ℝ)..1, c ^ (2 : ℕ) * x ^ (2 : ℕ) * Phi x ^ (2 : ℕ) := by
    refine intervalIntegral.integral_congr fun x _ => ?_
    ring
  calc
    (∫ x in (-1 : ℝ)..1, Phi x * prolateSLAction c Phi x)
        = (∫ x in (-1 : ℝ)..1, Phi x * (-(2 * x) * deriv Phi x
            + (1 - x ^ (2 : ℕ)) * deriv (deriv Phi) x))
          - ∫ x in (-1 : ℝ)..1, Phi x * (c ^ (2 : ℕ) * x ^ (2 : ℕ) * Phi x) := by
              rw [← intervalIntegral.integral_sub hA hB]
              refine intervalIntegral.integral_congr fun x _ => ?_
              simp only [prolateSLAction]
              ring
    _ = -(∫ x in (-1 : ℝ)..1, deriv Phi x * ((1 - x ^ (2 : ℕ)) * deriv Phi x))
          - ∫ x in (-1 : ℝ)..1, Phi x * (c ^ (2 : ℕ) * x ^ (2 : ℕ) * Phi x) := by rw [hflux]
    _ = -(∫ x in (-1 : ℝ)..1, (1 - x ^ (2 : ℕ)) * (deriv Phi x) ^ (2 : ℕ))
          - ∫ x in (-1 : ℝ)..1, c ^ (2 : ℕ) * x ^ (2 : ℕ) * Phi x ^ (2 : ℕ) := by
            rw [hgradEq, hpotEq]

/-- The prolate quadratic form is nonpositive. -/
theorem integral_mul_prolateSLAction_nonpos
    {c : ℝ} {Phi : ℝ → ℝ}
    (h1 : Differentiable ℝ Phi)
    (h2 : Differentiable ℝ (deriv Phi))
    (h2c : Continuous (deriv (deriv Phi))) :
    (∫ x in (-1 : ℝ)..1, Phi x * prolateSLAction c Phi x) ≤ 0 := by
  rw [integral_mul_prolateSLAction_eq_neg_energy h1 h2 h2c]
  have hgrad : 0 ≤ ∫ x in (-1 : ℝ)..1, (1 - x ^ (2 : ℕ)) * (deriv Phi x) ^ (2 : ℕ) := by
    refine intervalIntegral.integral_nonneg (by norm_num) fun x hx => ?_
    have hx1 : x ^ (2 : ℕ) ≤ 1 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hx.1) (sub_nonneg.mpr hx.2)]
    positivity
  have hpot : 0 ≤ ∫ x in (-1 : ℝ)..1, c ^ (2 : ℕ) * x ^ (2 : ℕ) * Phi x ^ (2 : ℕ) := by
    exact intervalIntegral.integral_nonneg (by norm_num) fun _ _ => by positivity
  linarith

/-- Every nonzero regular prolate eigenfunction on the aperture has nonpositive separation
eigenvalue.  Nonzeroness is stated in the exact `L²[-1,1]` class used by the band operator. -/
theorem prolateSeparation_nonpos
    {c chi : ℝ} {Phi : ℝ → ℝ}
    (hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Phi)
    (hclass : bandClass Phi hsm.continuous ≠ 0)
    (heig : ∀ x ∈ Icc (-1 : ℝ) 1, prolateSLAction c Phi x = chi * Phi x) :
    chi ≤ 0 := by
  have h1 : Differentiable ℝ Phi := (contDiff_infty_iff_deriv.mp hsm).1
  have hd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (deriv Phi) :=
    (contDiff_infty_iff_deriv.mp hsm).2
  have h2 : Differentiable ℝ (deriv Phi) := (contDiff_infty_iff_deriv.mp hd).1
  have h2c : Continuous (deriv (deriv Phi)) :=
    (contDiff_infty_iff_deriv.mp hd).2.continuous
  have hquad := integral_mul_prolateSLAction_nonpos (c := c) h1 h2 h2c
  have heq : (∫ x in (-1 : ℝ)..1, Phi x * prolateSLAction c Phi x)
      = chi * ∫ x in (-1 : ℝ)..1, Phi x ^ (2 : ℕ) := by
    calc
      (∫ x in (-1 : ℝ)..1, Phi x * prolateSLAction c Phi x)
          = ∫ x in (-1 : ℝ)..1, chi * Phi x ^ (2 : ℕ) := by
              refine intervalIntegral.integral_congr fun x hx => ?_
              rw [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at hx
              rw [heig x hx]
              ring
      _ = chi * ∫ x in (-1 : ℝ)..1, Phi x ^ (2 : ℕ) :=
        by rw [intervalIntegral.integral_const_mul]
  have hsq : 0 < ∫ x in (-1 : ℝ)..1, Phi x ^ (2 : ℕ) := by
    have hinner := inner_bandClass_eq Phi Phi hsm.continuous hsm.continuous
    have hinnerPos : 0 < (inner ℝ (bandClass Phi hsm.continuous)
        (bandClass Phi hsm.continuous) : ℝ) := real_inner_self_pos.mpr hclass
    rw [hinner] at hinnerPos
    simpa [sq] using hinnerPos
  rw [heq] at hquad
  exact nonpos_of_mul_nonpos_left hquad hsq

/-- A nonzero continuous global eigenfunction for a nonzero band eigenvalue cannot represent the
zero class on the aperture. -/
theorem bandClass_ne_zero_of_global_band_eigen
    {c lam : ℝ} {Phi : ℝ → ℝ}
    (hPhi : Continuous Phi) (hlam : lam ≠ 0) (hne : Phi ≠ 0)
    (hband : ∀ x : ℝ, bandTransform c Phi x = lam * Phi x) :
    bandClass Phi hPhi ≠ 0 := by
  intro hclass
  have hclassZero : bandClass Phi hPhi =
      bandClass (fun _ : ℝ => 0) continuous_const := by
    rw [hclass, bandClass_zero]
  have hEq : Set.EqOn Phi (fun _ : ℝ => 0) (Icc (-1 : ℝ) 1) :=
    eqOn_of_bandClass_eq hPhi continuous_const hclassZero
  have htransformZero : ∀ x : ℝ, bandTransform c Phi x = 0 := by
    intro x
    unfold bandTransform
    calc
      (∫ y in (-1 : ℝ)..1, sincKernelSmooth c x y * Phi y)
          = ∫ y in (-1 : ℝ)..1, sincKernelSmooth c x y * 0 := by
              refine intervalIntegral.integral_congr fun y hy => ?_
              rw [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at hy
              rw [hEq hy]
      _ = 0 := by simp
  apply hne
  funext x
  have hx := hband x
  rw [htransformZero x] at hx
  exact (mul_eq_zero.mp hx.symm).resolve_left hlam

/-- Global joint band/prolate modes have nonpositive angular separation value. -/
theorem prolateSeparation_nonpos_of_global_joint
    {c lam chi : ℝ} {Phi : ℝ → ℝ}
    (hlam : lam ≠ 0)
    (hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Phi)
    (hne : Phi ≠ 0)
    (hband : ∀ x : ℝ, bandTransform c Phi x = lam * Phi x)
    (heig : ∀ x : ℝ, prolateSLAction c Phi x = chi * Phi x) :
    chi ≤ 0 :=
  prolateSeparation_nonpos hsm
    (bandClass_ne_zero_of_global_band_eigen hsm.continuous hlam hne hband)
    (fun x _ => heig x)

/-- Exact Rayleigh identity for the radial separation ratio `-chi/c²`. -/
theorem neg_separation_div_sq_mul_integral_sq_eq
    {c chi : ℝ} (hc : c ≠ 0) {Phi : ℝ → ℝ}
    (hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Phi)
    (heig : ∀ x ∈ Icc (-1 : ℝ) 1, prolateSLAction c Phi x = chi * Phi x) :
    (-chi / c ^ (2 : ℕ)) * (∫ x in (-1 : ℝ)..1, Phi x ^ (2 : ℕ)) =
      (∫ x in (-1 : ℝ)..1, (1 - x ^ (2 : ℕ)) * (deriv Phi x) ^ (2 : ℕ)) / c ^ (2 : ℕ)
        + ∫ x in (-1 : ℝ)..1, x ^ (2 : ℕ) * Phi x ^ (2 : ℕ) := by
  have h1 : Differentiable ℝ Phi := (contDiff_infty_iff_deriv.mp hsm).1
  have hd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (deriv Phi) :=
    (contDiff_infty_iff_deriv.mp hsm).2
  have h2 : Differentiable ℝ (deriv Phi) := (contDiff_infty_iff_deriv.mp hd).1
  have h2c : Continuous (deriv (deriv Phi)) :=
    (contDiff_infty_iff_deriv.mp hd).2.continuous
  have henergy := integral_mul_prolateSLAction_eq_neg_energy (c := c) h1 h2 h2c
  have heigen : (∫ x in (-1 : ℝ)..1, Phi x * prolateSLAction c Phi x)
      = chi * ∫ x in (-1 : ℝ)..1, Phi x ^ (2 : ℕ) := by
    calc
      (∫ x in (-1 : ℝ)..1, Phi x * prolateSLAction c Phi x)
          = ∫ x in (-1 : ℝ)..1, chi * Phi x ^ (2 : ℕ) := by
              refine intervalIntegral.integral_congr fun x hx => ?_
              rw [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at hx
              rw [heig x hx]
              ring
      _ = chi * ∫ x in (-1 : ℝ)..1, Phi x ^ (2 : ℕ) := by
        rw [intervalIntegral.integral_const_mul]
  have hpotential :
      (∫ x in (-1 : ℝ)..1, c ^ (2 : ℕ) * x ^ (2 : ℕ) * Phi x ^ (2 : ℕ)) =
        c ^ (2 : ℕ) * ∫ x in (-1 : ℝ)..1, x ^ (2 : ℕ) * Phi x ^ (2 : ℕ) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun x _ => ?_
    ring
  rw [heigen, hpotential] at henergy
  field_simp [hc]
  nlinarith

end GaloisForLFunctions.RHTower

end
