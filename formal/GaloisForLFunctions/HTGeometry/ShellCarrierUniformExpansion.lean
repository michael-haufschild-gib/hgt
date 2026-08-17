import GaloisForLFunctions.HTGeometry.UniformDiscExpansion
import GaloisForLFunctions.HTGeometry.ShellCarrierExpansion

/-!
# The carrier expansion, uniform over a shell of frequencies

Every constant in the carrier assembly is bounded independently of the shell frequency once the
product of the squared frequency and the radius is bounded -- which is exactly the hypothesis that
makes the root defect small.  The single exception is the linear rate of the root defect, which
enters the exponential factor to the power of the order, and that is the growth the shell asymptotic
needs.
-/

open Polynomial Complex

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

noncomputable section

section Factors

/-- The shell-free constant of a shell-power factor. -/
def shellPowConst (α c : ℝ) (m : ℕ) : ℝ := 1 + cbinomAbsCoeff α m * c ^ m + (2 : ℝ) ^ (-α)

theorem one_le_shellPowConst {α c : ℝ} (hc : 0 ≤ c) (m : ℕ) : 1 ≤ shellPowConst α c m := by
  rw [shellPowConst]
  have h1 : (0 : ℝ) ≤ cbinomAbsCoeff α m * c ^ m :=
    mul_nonneg (cbinomAbsCoeff_nonneg α m) (pow_nonneg hc m)
  have h2 : (0 : ℝ) < (2 : ℝ) ^ (-α) := Real.rpow_pos_of_pos (by norm_num) _
  linarith

theorem bddExpS_shellPow {α : ℝ} (hα : α ≤ 0) {x r c : ℝ} (hr0 : 0 ≤ r)
    (hxr : x ^ 2 * r ^ 2 ≤ 1 / 2) (hxc : x ^ 2 * r ≤ c) (m : ℕ) :
    BddExpS r m (shellPowConst α c m)
      (fun w : ℂ => (1 + (x : ℂ) ^ 2 * w ^ 2) ^ ((α : ℝ) : ℂ)) (shellBinomPoly α m x) := by
  have hcb : (0 : ℝ) ≤ cbinomAbsCoeff α m := cbinomAbsCoeff_nonneg α m
  have hxr0 : (0 : ℝ) ≤ x ^ 2 * r := mul_nonneg (sq_nonneg x) hr0
  have hc0 : (0 : ℝ) ≤ c := le_trans hxr0 hxc
  have hcm : (0 : ℝ) ≤ c ^ m := pow_nonneg hc0 m
  have h2 : (0 : ℝ) < (2 : ℝ) ^ (-α) := Real.rpow_pos_of_pos (by norm_num) _
  have hkey : cbinomAbsCoeff α m * |x| ^ (2 * m) * r ^ (2 * m - m)
      ≤ cbinomAbsCoeff α m * c ^ m := by
    rw [show 2 * m - m = m from by omega, pow_mul, sq_abs, mul_assoc, ← mul_pow]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hxr0 hxc m) hcb
  rw [shellPowConst]
  refine ⟨by nlinarith [mul_nonneg hcb hcm], fun w hw => ?_, ?_⟩
  · exact le_trans (norm_shellPow_le hα hxr hw) (by nlinarith [mul_nonneg hcb hcm])
  · exact ((hasPolyExpansion_shellBinom hα m x hxr).mono
      (mul_nonneg hcb (pow_nonneg (abs_nonneg x) _)) (by omega)).weaken (by nlinarith)

theorem bddExpS_monomial {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (m k : ℕ) :
    BddExpS r m 1 (fun w : ℂ => w ^ k) (Polynomial.X ^ k) := by
  refine ⟨le_rfl, fun w hw => ?_, (hasPolyExpansion_monomial r m k).weaken (by norm_num)⟩
  rw [norm_pow]
  exact le_trans (pow_le_pow_left₀ (norm_nonneg w) hw k) (pow_le_one₀ hr0 hr1)

/-- The shell-free constant of the root-defect factor. -/
def defectFactorConst (a c : ℝ) (m : ℕ) : ℝ :=
  max 1 |a| * (1 + cbinomAbsCoeff ((1 : ℝ) / 2) (m + 1) * c ^ (m + 1)
    + cbinomAbsCoeff ((1 : ℝ) / 2) 1 * c)

theorem one_le_defectFactorConst {a c : ℝ} (hc : 0 ≤ c) (m : ℕ) : 1 ≤ defectFactorConst a c m := by
  rw [defectFactorConst]
  have h1 : (0 : ℝ) ≤ cbinomAbsCoeff ((1 : ℝ) / 2) (m + 1) * c ^ (m + 1) :=
    mul_nonneg (cbinomAbsCoeff_nonneg _ _) (pow_nonneg hc _)
  have h2 : (0 : ℝ) ≤ cbinomAbsCoeff ((1 : ℝ) / 2) 1 * c :=
    mul_nonneg (cbinomAbsCoeff_nonneg _ _) hc
  have h3 : (1 : ℝ) ≤ max 1 |a| := le_max_left _ _
  nlinarith

theorem bddExpS_scaledDefect {a x r c : ℝ} (hr0 : 0 ≤ r)
    (hxr : x ^ 2 * r ^ 2 ≤ 1 / 2) (hxc : x ^ 2 * r ≤ c) (m : ℕ) :
    BddExpS r m (defectFactorConst a c m) (fun w : ℂ => (-(a : ℂ)) * shellDefect x w)
      (Polynomial.C (-(a : ℂ)) * shellDefectPoly m x) := by
  have hxr0 : (0 : ℝ) ≤ x ^ 2 * r := mul_nonneg (sq_nonneg x) hr0
  have hc0 : (0 : ℝ) ≤ c := le_trans hxr0 hxc
  have hcb1 : (0 : ℝ) ≤ cbinomAbsCoeff ((1 : ℝ) / 2) 1 := cbinomAbsCoeff_nonneg _ _
  have hcbm : (0 : ℝ) ≤ cbinomAbsCoeff ((1 : ℝ) / 2) (m + 1) := cbinomAbsCoeff_nonneg _ _
  have hbase : BddExpS r m (1 + cbinomAbsCoeff ((1 : ℝ) / 2) (m + 1) * c ^ (m + 1)
      + cbinomAbsCoeff ((1 : ℝ) / 2) 1 * c) (shellDefect x) (shellDefectPoly m x) := by
    have hkeyC : cbinomAbsCoeff ((1 : ℝ) / 2) (m + 1) * |x| ^ (2 * (m + 1))
        * r ^ (2 * m + 1 - m) ≤ cbinomAbsCoeff ((1 : ℝ) / 2) (m + 1) * c ^ (m + 1) := by
      rw [show 2 * m + 1 - m = m + 1 from by omega, pow_mul, sq_abs, mul_assoc, ← mul_pow]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hxr0 hxc (m + 1)) hcbm
    refine ⟨by nlinarith [mul_nonneg hcbm (pow_nonneg hc0 (m + 1)), mul_nonneg hcb1 hc0],
      fun w hw => ?_, ?_⟩
    · have h1 := norm_shellDefect_le hxr hw
      have h2 : shellDefectRate x * ‖w‖ ≤ cbinomAbsCoeff ((1 : ℝ) / 2) 1 * c := by
        rw [shellDefectRate, sq_abs]
        calc cbinomAbsCoeff ((1 : ℝ) / 2) 1 * x ^ 2 * ‖w‖
            ≤ cbinomAbsCoeff ((1 : ℝ) / 2) 1 * x ^ 2 * r := by
              nlinarith [mul_nonneg hcb1 (sq_nonneg x), norm_nonneg w]
          _ = cbinomAbsCoeff ((1 : ℝ) / 2) 1 * (x ^ 2 * r) := by ring
          _ ≤ cbinomAbsCoeff ((1 : ℝ) / 2) 1 * c := mul_le_mul_of_nonneg_left hxc hcb1
      nlinarith [mul_nonneg hcbm (pow_nonneg hc0 (m + 1))]
    · exact ((hasPolyExpansion_shellDefect m x hxr).mono
        (mul_nonneg hcbm (pow_nonneg (abs_nonneg x) _)) (by omega)).weaken (by nlinarith)
  have hna : ‖(-(a : ℂ))‖ = |a| := by
    rw [norm_neg, Complex.norm_real, Real.norm_eq_abs]
  have := hbase.const_mul (-(a : ℂ))
  rw [hna] at this
  exact this

/-- The shell-free part of the exponential factor's constant. -/
def defectExpConst (a c : ℝ) (m : ℕ) : ℝ :=
  (m : ℝ) ^ 2 * 2 ^ m * defectFactorConst a c m ^ (m + 1)
    + Real.exp (2 * defectFactorConst a c m) + 1

theorem bddExpS_defectExp {a x r c : ℝ} (ha : 0 ≤ a) (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (hxr : x ^ 2 * r ^ 2 ≤ 1 / 2) (hxc : x ^ 2 * r ≤ c)
    (hdef : a * shellDefectRate x * r ≤ 1 / 2) (m : ℕ) :
    BddExpS r m (2 * (a * shellDefectRate x) ^ m + defectExpConst a c m)
      (fun w : ℂ => Complex.exp (-((a : ℂ) * shellDefect x w)))
      (defectExpPoly a x m) := by
  have hrate := shellDefectRate_nonneg x
  have hna : ‖(-(a : ℂ))‖ = a := by
    rw [norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ha]
  have hD := bddExpS_scaledDefect (a := a) (x := x) (c := c) hr0 hxr hxc m
  have hsmall : ∀ w : ℂ, ‖w‖ ≤ r → ‖(-(a : ℂ)) * shellDefect x w‖
      ≤ (a * shellDefectRate x) * ‖w‖ := by
    intro w hw
    rw [norm_mul, hna]
    have h1 := norm_shellDefect_le hxr hw
    nlinarith [mul_nonneg ha (sub_nonneg.mpr h1)]
  have htiny : ∀ w : ℂ, ‖w‖ ≤ r →
      ‖(-(a : ℂ)) * shellDefect x w‖ / ((m : ℝ) + 1) ≤ 1 / 2 := by
    intro w hw
    have hpos : (0 : ℝ) < (m : ℝ) + 1 := by positivity
    rw [div_le_iff₀ hpos]
    have h1 := hsmall w hw
    have h2 : (a * shellDefectRate x) * ‖w‖ ≤ 1 / 2 := by
      nlinarith [mul_nonneg ha hrate, norm_nonneg w]
    have h3 : (1 : ℝ) ≤ (m : ℝ) + 1 := by
      have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      linarith
    nlinarith
  have hres := bddExpS_cexp hr0 hr1 hD (mul_nonneg ha hrate) hsmall htiny
  have hfun : (fun w : ℂ => Complex.exp ((-(a : ℂ)) * shellDefect x w))
      = fun w : ℂ => Complex.exp (-((a : ℂ) * shellDefect x w)) := by
    funext w
    rw [neg_mul]
  rw [hfun] at hres
  rw [defectExpPoly, defectExpConst]
  refine hres.weaken (le_of_eq ?_)
  ring

/-- The shell-free constant of the Poincaré factor. -/
def poincareFactorConst (a c : ℝ) (n m : ℕ) : ℝ :=
  1 + ∑ k ∈ Finset.range n,
    3 * (max 1 ‖((besselK1Coeff k : ℝ) : ℂ) * ((a : ℂ)⁻¹) ^ k‖ * 1)
      * shellPowConst (-(k : ℝ) / 2) c m

theorem bddExpS_shellPoincare {a x r c : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (hxr : x ^ 2 * r ^ 2 ≤ 1 / 2) (hxc : x ^ 2 * r ≤ c) (n m : ℕ) :
    BddExpS r m (poincareFactorConst a c n m)
      (fun w : ℂ => ∑ k ∈ Finset.range n, ((besselK1Coeff k : ℝ) : ℂ) * ((a : ℂ)⁻¹) ^ k * w ^ k
        * (1 + (x : ℂ) ^ 2 * w ^ 2) ^ (((-(k : ℝ) / 2 : ℝ)) : ℂ))
      (shellPoincarePoly a x n m) := by
  rw [poincareFactorConst, shellPoincarePoly]
  refine BddExpS.finsetSum _ fun k _ => ?_
  have hk0 : (-(k : ℝ) / 2 : ℝ) ≤ 0 := by
    have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    linarith
  exact ((bddExpS_monomial hr0 hr1 m k).const_mul
    (((besselK1Coeff k : ℝ) : ℂ) * ((a : ℂ)⁻¹) ^ k)).mul hr0 hr1
    (bddExpS_shellPow hk0 hr0 hxr hxc m)

end Factors

section Assembly

/-- The shell-free part of the carrier's error constant. -/
def carrierShellConst (a c : ℝ) (n m : ℕ) : ℝ :=
  27 * (max 1 ‖((Real.sqrt 2 : ℝ) : ℂ)‖ * shellPowConst (-1 / 2) c m)
    * shellPowConst (-1 / 4) c m * poincareFactorConst a c n m
    * max 2 (defectExpConst a c m)

theorem chainConst_le {M SB SS G Km : ℝ} (h1 : 1 ≤ M) (hB : 1 ≤ SB) (hS : 1 ≤ SS)
    (hK : 0 ≤ Km) :
    3 * (3 * (3 * M * SB) * (2 * Km + G)) * SS
      ≤ 27 * M * SB * SS * max 2 G * (1 + Km) := by
  have h2D : (2 : ℝ) ≤ max 2 G := le_max_left _ _
  have hGD : G ≤ max 2 G := le_max_right _ _
  have hstep : 2 * Km + G ≤ max 2 G * (1 + Km) := by nlinarith
  have hP : (0 : ℝ) ≤ 27 * M * SB * SS := by
    have hM0 : (0 : ℝ) ≤ M := by linarith
    have hB0 : (0 : ℝ) ≤ SB := by linarith
    have hS0 : (0 : ℝ) ≤ SS := by linarith
    exact mul_nonneg (mul_nonneg (by linarith) hB0) hS0
  calc 3 * (3 * (3 * M * SB) * (2 * Km + G)) * SS
      = (27 * M * SB * SS) * (2 * Km + G) := by ring
    _ ≤ (27 * M * SB * SS) * (max 2 G * (1 + Km)) := mul_le_mul_of_nonneg_left hstep hP
    _ = 27 * M * SB * SS * max 2 G * (1 + Km) := by ring

/-- **The carrier profile expands with a constant uniform over the shell**, apart from the linear
rate of the root defect raised to the order. -/
theorem bddExpS_shellCarrierProfile {a x r c : ℝ} (ha : 0 ≤ a) (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (hxr : x ^ 2 * r ^ 2 ≤ 1 / 2) (hxc : x ^ 2 * r ≤ c)
    (hdef : a * shellDefectRate x * r ≤ 1 / 2) (n m : ℕ) :
    BddExpS r m (carrierShellConst a c n m * (1 + (a * shellDefectRate x) ^ m))
      (shellCarrierProfile a x n) (carrierProductPoly a x n m) := by
  have hxr0 : (0 : ℝ) ≤ x ^ 2 * r := mul_nonneg (sq_nonneg x) hr0
  have hc0 : (0 : ℝ) ≤ c := le_trans hxr0 hxc
  have hA := bddExpS_shellPow (α := (-1 / 2 : ℝ)) (by norm_num) hr0 hxr hxc m
  have hB := bddExpS_shellPow (α := (-1 / 4 : ℝ)) (by norm_num) hr0 hxr hxc m
  have hE := bddExpS_defectExp (a := a) (x := x) (c := c) ha hr0 hr1 hxr hxc hdef m
  have hS := bddExpS_shellPoincare (a := a) (x := x) (c := c) hr0 hr1 hxr hxc n m
  have hchain :=
    (((hA.const_mul ((Real.sqrt 2 : ℝ) : ℂ)).mul hr0 hr1 hB).mul hr0 hr1 hE).mul hr0 hr1 hS
  refine hchain.weaken ?_
  rw [carrierShellConst]
  exact chainConst_le (hA.const_mul ((Real.sqrt 2 : ℝ) : ℂ)).one_le
    (one_le_shellPowConst hc0 m) hS.one_le
    (pow_nonneg (mul_nonneg ha (shellDefectRate_nonneg x)) m)

end Assembly

end

end GaloisForLFunctions.HTGeometry
