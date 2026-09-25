import GaloisForLFunctions.RHTower.SelbergMaassSelbergCuspStep

open MeasureTheory UpperHalfPlane ModularGroup Set Complex
open scoped MatrixGroups Pointwise

/-!
# Bounds and integrability for the `Γ(N)` Maass–Selberg relation

The constant-term coefficients `count₀(σ_c)` and `φ_c(s)` are invariant under the right `T`-shift (`coeff_sh`, by
comparing `CT_{cT} = CT_c` at `y = 1, 2`). With `CT_c = a_c y^s + b_c(s) y^{1-s}` (`CT_eq`) and the decay
`|E_s(R_c z) − CT_c| ≤ Q_s y^{-3-Re s}` (`norm_Estar_le`): `|E_s(R_c z)|` is bounded on `1/2 ≤ y ≤ Y`
(`norm_E_le_D`) and at most `C y^{Re s}` for `y ≥ 1` (`norm_E_le_pow`). The truncated series
`Λ^Y_c E_s = E_s(R_c ·) − [y > Y] CT_c(s, y)` (`Lc`) is bounded on `𝒟` (`norm_Lc_le`), and the four integrands of the
Maass–Selberg computation are integrable on `𝒟` for `1 < Re v < Re u`, `Y ≥ 1` (`integrableOn_Lc_mul_Lc`,
`integrableOn_Lc_mul_E`, `integrableOn_above_estar_mul_CT`, `integrableOn_above_pow_mul_E`).
-/

namespace GaloisForLFunctions.RHTower.SelbergMaassSelbergBounds
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.RHTower.SarnakXuePretrace GaloisForLFunctions.RHTower.SelbergCellCosetShift
  GaloisForLFunctions.RHTower.SelbergCuspConstantTerm GaloisForLFunctions.RHTower.SelbergEisensteinScatteringEntry
  GaloisForLFunctions.RHTower.SelbergEisensteinCuspConstant GaloisForLFunctions.RHTower.SelbergCuspZeroMean
  GaloisForLFunctions.RHTower.SelbergMaassSelbergCuspStep GaloisForLFunctions.RHTower.SelbergPoincareKernel

local notation "𝐄" => GaloisForLFunctions.RHTower.SelbergPoincare.poincare

variable (N : ℕ) [NeZero N]

/-- The two coefficients of `CT_c` are invariant under the right `T`-shift. -/
theorem coeff_sh (c : Cosets N) {s : ℂ} (hs : 1 < s.re) :
    count0 N (lift N (sh N c)) = count0 N (lift N c) ∧
      phiσ N (lift N (sh N c)) s = phiσ N (lift N c) s := by
  have h1 := CT_sh N c hs (y := 1) one_pos
  have h2 := CT_sh N c hs (y := 2) two_pos
  unfold CT at h1 h2
  set a' : ℂ := (count0 N (lift N (sh N c)) : ℂ)
  set a : ℂ := (count0 N (lift N c) : ℂ)
  set b' := phiσ N (lift N (sh N c)) s
  set b := phiσ N (lift N c) s
  simp only [Complex.ofReal_one, Complex.one_cpow, mul_one] at h1
  have hN : (N : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne N
  have h2c : ((2 : ℝ) : ℂ) ^ s ≠ ((2 : ℝ) : ℂ) ^ (1 - s) := by
    intro h
    have := congrArg norm h
    rw [Complex.norm_cpow_eq_rpow_re_of_pos two_pos, Complex.norm_cpow_eq_rpow_re_of_pos two_pos] at this
    have hlt : (2 : ℝ) ^ (1 - s).re < 2 ^ s.re :=
      Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by simp; linarith)
    linarith
  have hA : a' = a := by
    have e : (a' - a) * (((2 : ℝ) : ℂ) ^ s - ((2 : ℝ) : ℂ) ^ (1 - s)) = 0 := by
      push_cast at h1 h2 ⊢
      linear_combination h2 - ((2 : ℂ) ^ (1 - s)) * h1
    have := (mul_eq_zero.mp e).resolve_right (sub_ne_zero.mpr h2c)
    exact sub_eq_zero.mp this
  refine ⟨by simp only [a', a] at hA; exact_mod_cast hA, ?_⟩
  rw [hA] at h1
  have := add_left_cancel h1
  exact mul_left_cancel₀ (inv_ne_zero hN) this

/-- The decay constant of the non-constant part. -/
noncomputable def Qc (s : ℂ) : ℝ :=
  S1 s.re * (S2 * (109 * ((1 + ‖s‖) * N) ^ 4 * (2 * (N : ℝ) ^ (s.re - 1) * cst s.re) * (N : ℝ) ^ 2 /
    (2 * Real.pi) ^ 4))

omit [NeZero N] in
theorem Qc_nonneg (s : ℂ) : 0 ≤ Qc N s := by
  unfold Qc
  have := cst_nonneg s.re
  have h1 : 0 ≤ S1 s.re := tsum_nonneg (fun c => by split_ifs <;> positivity)
  have h2 : 0 ≤ S2 := tsum_nonneg (fun c => by split_ifs <;> positivity)
  positivity

theorem norm_Estar_le (c : Cosets N) {s : ℂ} (hs : 1 < s.re) (z : ℍ) :
    ‖𝐄 N 0 s ((Quotient.out c : PSL2Z) • z) - CT N c s z.im‖ ≤ Qc N s * z.im ^ (-(3 + s.re)) := by
  rw [poincare_sub_CT N c hs z]
  refine (norm_Estarσ_le N _ (by linarith) z).trans (le_of_eq ?_)
  rw [econst_eq N _ _ z.im_pos, Qc]; ring

/-- The coefficients `a_c = count₀`, `b_c(s) = N^{-1} φ_c(s)`. -/
noncomputable def bC (c : Cosets N) (s : ℂ) : ℂ := (N : ℂ)⁻¹ * phiσ N (lift N c) s

theorem CT_eq (c : Cosets N) (s : ℂ) (y : ℝ) :
    CT N c s y = (count0 N (lift N c) : ℂ) * ((y : ℝ) : ℂ) ^ s + bC N c s * ((y : ℝ) : ℂ) ^ (1 - s) := rfl

theorem norm_CT_le (c : Cosets N) (s : ℂ) {y : ℝ} (hy : 0 < y) :
    ‖CT N c s y‖ ≤ (count0 N (lift N c) : ℝ) * y ^ s.re + ‖bC N c s‖ * y ^ (1 - s.re) := by
  rw [CT_eq]
  refine (norm_add_le _ _).trans (le_of_eq ?_)
  rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hy, Complex.norm_cpow_eq_rpow_re_of_pos hy]
  simp

theorem norm_E_le (c : Cosets N) {s : ℂ} (hs : 1 < s.re) (z : ℍ) :
    ‖𝐄 N 0 s ((Quotient.out c : PSL2Z) • z)‖ ≤ (count0 N (lift N c) : ℝ) * z.im ^ s.re +
      ‖bC N c s‖ * z.im ^ (1 - s.re) + Qc N s * z.im ^ (-(3 + s.re)) := by
  have h := norm_Estar_le N c hs z
  have h2 := norm_CT_le N c s z.im_pos
  calc ‖𝐄 N 0 s ((Quotient.out c : PSL2Z) • z)‖
      = ‖CT N c s z.im + (𝐄 N 0 s ((Quotient.out c : PSL2Z) • z) - CT N c s z.im)‖ := by ring_nf
    _ ≤ ‖CT N c s z.im‖ + ‖𝐄 N 0 s ((Quotient.out c : PSL2Z) • z) - CT N c s z.im‖ := norm_add_le _ _
    _ ≤ _ := by linarith

/-- On `1/2 ≤ y ≤ Y`: `|E_s(R_c z)| ≤ D`. -/
noncomputable def Dc (c : Cosets N) (s : ℂ) (Y : ℝ) : ℝ :=
  (count0 N (lift N c) : ℝ) * Y ^ s.re + ‖bC N c s‖ * (1 / 2) ^ (1 - s.re) + Qc N s * (1 / 2) ^ (-(3 + s.re))

theorem norm_E_le_D (c : Cosets N) {s : ℂ} (hs : 1 < s.re) {Y : ℝ} {z : ℍ} (h1 : 1 / 2 ≤ z.im)
    (h2 : z.im ≤ Y) : ‖𝐄 N 0 s ((Quotient.out c : PSL2Z) • z)‖ ≤ Dc N c s Y := by
  refine (norm_E_le N c hs z).trans ?_
  unfold Dc
  have hy := z.im_pos
  have e1 : z.im ^ s.re ≤ Y ^ s.re := Real.rpow_le_rpow hy.le h2 (by linarith)
  have e2 : z.im ^ (1 - s.re) ≤ (1 / 2) ^ (1 - s.re) := Real.rpow_le_rpow_of_nonpos (by norm_num) h1 (by linarith)
  have e3 : z.im ^ (-(3 + s.re)) ≤ (1 / 2) ^ (-(3 + s.re)) :=
    Real.rpow_le_rpow_of_nonpos (by norm_num) h1 (by linarith)
  have := Qc_nonneg N s
  gcongr

/-- On `y ≥ 1`: `|E_s(R_c z)| ≤ (a + |b| + Q) y^{Re s}`. -/
theorem norm_E_le_pow (c : Cosets N) {s : ℂ} (hs : 1 < s.re) {z : ℍ} (h1 : 1 ≤ z.im) :
    ‖𝐄 N 0 s ((Quotient.out c : PSL2Z) • z)‖ ≤
      ((count0 N (lift N c) : ℝ) + ‖bC N c s‖ + Qc N s) * z.im ^ s.re := by
  refine (norm_E_le N c hs z).trans ?_
  have hy := z.im_pos
  have e2 : z.im ^ (1 - s.re) ≤ z.im ^ s.re := Real.rpow_le_rpow_of_exponent_le h1 (by linarith)
  have e3 : z.im ^ (-(3 + s.re)) ≤ z.im ^ s.re := Real.rpow_le_rpow_of_exponent_le h1 (by linarith)
  have := Qc_nonneg N s
  have : 0 ≤ ‖bC N c s‖ := norm_nonneg _
  nlinarith

/-- The truncated Eisenstein series on the coset piece `R_c 𝒟`:
`Λ^Y_c E_s(z) = E_s(R_c z) − [Im z > Y] CT_c(s, Im z)`. -/
noncomputable def Lc (c : Cosets N) (s : ℂ) (Y : ℝ) (z : ℍ) : ℂ :=
  𝐄 N 0 s ((Quotient.out c : PSL2Z) • z) - if Y < z.im then CT N c s z.im else 0

theorem continuous_E (c : Cosets N) {s : ℂ} (hs : 1 < s.re) :
    Continuous (fun z : ℍ => 𝐄 N 0 s ((Quotient.out c : PSL2Z) • z)) :=
  (GaloisForLFunctions.RHTower.SelbergPoincareBounded.continuous_poincare N 0 hs).comp (continuous_const_smul _)

theorem continuous_CT_im (c : Cosets N) (s : ℂ) : Continuous (fun z : ℍ => CT N c s z.im) :=
  (continuousOn_CT N c s).comp_continuous UpperHalfPlane.continuous_im (fun z => z.im_pos)

theorem measurableSet_above (Y : ℝ) : MeasurableSet {z : ℍ | Y < z.im} :=
  measurableSet_lt measurable_const UpperHalfPlane.continuous_im.measurable

theorem measurable_ite_above {f : ℍ → ℂ} (hf : Measurable f) (Y : ℝ) :
    Measurable (fun z : ℍ => if Y < z.im then f z else 0) :=
  Measurable.ite (measurableSet_above Y) hf measurable_const

theorem measurable_Lc (c : Cosets N) {s : ℂ} (hs : 1 < s.re) (Y : ℝ) : Measurable (Lc N c s Y) :=
  (continuous_E N c hs).measurable.sub (measurable_ite_above (continuous_CT_im N c s).measurable Y)

theorem Dc_nonneg (c : Cosets N) (s : ℂ) {Y : ℝ} (hY : 0 ≤ Y) : 0 ≤ Dc N c s Y := by
  unfold Dc; have := Qc_nonneg N s; positivity

theorem norm_Lc_le (c : Cosets N) {s : ℂ} (hs : 1 < s.re) {Y : ℝ} (hY : 1 ≤ Y) {z : ℍ} (hz : z ∈ fd) :
    ‖Lc N c s Y z‖ ≤ Dc N c s Y + Qc N s := by
  have hy := RHTower.half_lt_im_of_mem_fd' hz
  have hQ := Qc_nonneg N s
  have hD := Dc_nonneg N c s (by linarith : (0 : ℝ) ≤ Y)
  unfold Lc
  split_ifs with h
  · have h1 : 1 ≤ z.im := by linarith
    refine (norm_Estar_le N c hs z).trans ?_
    have : z.im ^ (-(3 + s.re)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos h1 (by linarith)
    nlinarith
  · rw [sub_zero]
    exact (norm_E_le_D N c hs hy.le (not_lt.mp h)).trans (by linarith)

theorem integrableOn_Lc_mul_Lc (c : Cosets N) {u v : ℂ} (hu : 1 < u.re) (hv : 1 < v.re) {Y : ℝ} (hY : 1 ≤ Y) :
    IntegrableOn (fun z => Lc N c u Y z * Lc N c v Y z) fd volume := by
  refine RHTower.integrableOn_fd_of_norm_le ((measurable_Lc N c hu Y).mul (measurable_Lc N c hv Y)).aestronglyMeasurable
    (β := 0) (by norm_num) (C := (Dc N c u Y + Qc N u) * (Dc N c v Y + Qc N v)) (fun z hz => ?_)
  rw [Real.rpow_zero, mul_one, norm_mul]
  have := Dc_nonneg N c u (by linarith : (0 : ℝ) ≤ Y); have := Qc_nonneg N u
  exact mul_le_mul (norm_Lc_le N c hu hY hz) (norm_Lc_le N c hv hY hz) (norm_nonneg _) (by positivity)

theorem integrableOn_Lc_mul_E (c : Cosets N) {u v : ℂ} (hu : 1 < u.re) (hv : 1 < v.re) (huv : v.re < u.re)
    {Y : ℝ} (hY : 1 ≤ Y) :
    IntegrableOn (fun z => Lc N c u Y z * 𝐄 N 0 v ((Quotient.out c : PSL2Z) • z)) fd volume := by
  set C := (Dc N c u Y + Qc N u) * Dc N c v Y +
    Qc N u * ((count0 N (lift N c) : ℝ) + ‖bC N c v‖ + Qc N v)
  refine RHTower.integrableOn_fd_of_norm_le ((measurable_Lc N c hu Y).mul (continuous_E N c hv).measurable).aestronglyMeasurable
    (β := 0) (by norm_num) (C := C) (fun z hz => ?_)
  have hy := RHTower.half_lt_im_of_mem_fd' hz
  have hQu := Qc_nonneg N u; have hQv := Qc_nonneg N v
  have hDu := Dc_nonneg N c u (by linarith : (0 : ℝ) ≤ Y); have hDv := Dc_nonneg N c v (by linarith : (0 : ℝ) ≤ Y)
  have hb : 0 ≤ ‖bC N c v‖ := norm_nonneg _
  rw [Real.rpow_zero, mul_one, norm_mul]
  by_cases h : Y < z.im
  · have h1 : 1 ≤ z.im := by linarith
    have hL : ‖Lc N c u Y z‖ ≤ Qc N u * z.im ^ (-(3 + u.re)) := by
      unfold Lc; rw [if_pos h]; exact norm_Estar_le N c hu z
    have hE := norm_E_le_pow N c hv h1
    have hp : z.im ^ (-(3 + u.re)) * z.im ^ v.re ≤ 1 := by
      rw [← Real.rpow_add z.im_pos]; exact Real.rpow_le_one_of_one_le_of_nonpos h1 (by linarith)
    have hp0 : 0 ≤ z.im ^ v.re := Real.rpow_nonneg z.im_pos.le _
    have hp1 : 0 ≤ z.im ^ (-(3 + u.re)) := Real.rpow_nonneg z.im_pos.le _
    calc ‖Lc N c u Y z‖ * ‖𝐄 N 0 v ((Quotient.out c : PSL2Z) • z)‖
        ≤ (Qc N u * z.im ^ (-(3 + u.re))) *
            (((count0 N (lift N c) : ℝ) + ‖bC N c v‖ + Qc N v) * z.im ^ v.re) :=
          mul_le_mul hL hE (norm_nonneg _) (by positivity)
      _ = Qc N u * ((count0 N (lift N c) : ℝ) + ‖bC N c v‖ + Qc N v) *
            (z.im ^ (-(3 + u.re)) * z.im ^ v.re) := by ring
      _ ≤ Qc N u * ((count0 N (lift N c) : ℝ) + ‖bC N c v‖ + Qc N v) * 1 :=
          mul_le_mul_of_nonneg_left hp (by positivity)
      _ ≤ C := by simp only [C]; nlinarith
  · have hE := norm_E_le_D N c hv hy.le (not_lt.mp h)
    calc ‖Lc N c u Y z‖ * ‖𝐄 N 0 v ((Quotient.out c : PSL2Z) • z)‖
        ≤ (Dc N c u Y + Qc N u) * Dc N c v Y :=
          mul_le_mul (norm_Lc_le N c hu hY hz) hE (norm_nonneg _) (by positivity)
      _ ≤ C := by simp only [C]; nlinarith

theorem integrableOn_above_estar_mul_CT (c : Cosets N) {u v : ℂ} (hu : 1 < u.re) (hv : 1 < v.re)
    (huv : v.re < u.re) {Y : ℝ} (hY : 1 ≤ Y) :
    IntegrableOn (fun z => if Y < z.im then
      (𝐄 N 0 u ((Quotient.out c : PSL2Z) • z) - CT N c u z.im) * CT N c v z.im else 0) fd volume := by
  set C := Qc N u * ((count0 N (lift N c) : ℝ) + ‖bC N c v‖)
  refine RHTower.integrableOn_fd_of_norm_le (measurable_ite_above
    (((continuous_E N c hu).sub (continuous_CT_im N c u)).mul (continuous_CT_im N c v)).measurable Y).aestronglyMeasurable
    (β := 0) (by norm_num) (C := C) (fun z hz => ?_)
  have hQu := Qc_nonneg N u
  have hb : 0 ≤ ‖bC N c v‖ := norm_nonneg _
  rw [Real.rpow_zero, mul_one]
  split_ifs with h
  · have h1 : 1 ≤ z.im := by linarith
    rw [norm_mul]
    have hCT := norm_CT_le N c v z.im_pos
    have hp : z.im ^ (-(3 + u.re)) * z.im ^ v.re ≤ 1 := by
      rw [← Real.rpow_add z.im_pos]; exact Real.rpow_le_one_of_one_le_of_nonpos h1 (by linarith)
    have hp' : z.im ^ (-(3 + u.re)) * z.im ^ (1 - v.re) ≤ 1 := by
      rw [← Real.rpow_add z.im_pos]; exact Real.rpow_le_one_of_one_le_of_nonpos h1 (by linarith)
    have hp1 : 0 ≤ z.im ^ (-(3 + u.re)) := Real.rpow_nonneg z.im_pos.le _
    have hp2 : 0 ≤ z.im ^ v.re := Real.rpow_nonneg z.im_pos.le _
    have hp3 : 0 ≤ z.im ^ (1 - v.re) := Real.rpow_nonneg z.im_pos.le _
    calc ‖𝐄 N 0 u ((Quotient.out c : PSL2Z) • z) - CT N c u z.im‖ * ‖CT N c v z.im‖
        ≤ (Qc N u * z.im ^ (-(3 + u.re))) *
            ((count0 N (lift N c) : ℝ) * z.im ^ v.re + ‖bC N c v‖ * z.im ^ (1 - v.re)) :=
          mul_le_mul (norm_Estar_le N c hu z) hCT (norm_nonneg _) (by positivity)
      _ = Qc N u * ((count0 N (lift N c) : ℝ) * (z.im ^ (-(3 + u.re)) * z.im ^ v.re) +
            ‖bC N c v‖ * (z.im ^ (-(3 + u.re)) * z.im ^ (1 - v.re))) := by ring
      _ ≤ C := by
          simp only [C]
          have := (Nat.cast_nonneg (count0 N (lift N c)) : (0 : ℝ) ≤ _)
          gcongr
          · nlinarith
          · nlinarith
  · rw [norm_zero]; positivity

theorem integrableOn_above_pow_mul_E (c : Cosets N) {u v : ℂ} (hv : 1 < v.re)
    (huv : v.re < u.re) {Y : ℝ} (hY : 1 ≤ Y) :
    IntegrableOn (fun z => if Y < z.im then
      ((z.im : ℝ) : ℂ) ^ (1 - u) * 𝐄 N 0 v ((Quotient.out c : PSL2Z) • z) else 0) fd volume := by
  set C := (count0 N (lift N c) : ℝ) + ‖bC N c v‖ + Qc N v
  have hcont : Continuous (fun z : ℍ => ((z.im : ℝ) : ℂ) ^ (1 - u)) :=
    continuous_iff_continuousAt.mpr (fun z =>
      ((Complex.continuous_ofReal.comp UpperHalfPlane.continuous_im).continuousAt).cpow continuousAt_const
        (Complex.ofReal_mem_slitPlane.mpr z.im_pos))
  refine RHTower.integrableOn_fd_of_norm_le (measurable_ite_above
    (hcont.mul (continuous_E N c hv)).measurable Y).aestronglyMeasurable
    (β := 1 - u.re + v.re) (by linarith) (C := C) (fun z hz => ?_)
  have hC : 0 ≤ C := by have := Qc_nonneg N v; have := norm_nonneg (bC N c v); simp only [C]; positivity
  split_ifs with h
  · have h1 : 1 ≤ z.im := by linarith
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos z.im_pos]
    have hE := norm_E_le_pow N c hv h1
    have hre : (1 - u).re = 1 - u.re := by simp
    rw [hre]
    calc z.im ^ (1 - u.re) * ‖𝐄 N 0 v ((Quotient.out c : PSL2Z) • z)‖
        ≤ z.im ^ (1 - u.re) * (C * z.im ^ v.re) :=
          mul_le_mul_of_nonneg_left hE (Real.rpow_nonneg z.im_pos.le _)
      _ = C * z.im ^ (1 - u.re + v.re) := by rw [Real.rpow_add z.im_pos]; ring
  · rw [norm_zero]; exact mul_nonneg hC (Real.rpow_nonneg z.im_pos.le _)

end GaloisForLFunctions.RHTower.SelbergMaassSelbergBounds
