import GaloisForLFunctions.HTGeometry.ComplexShiftLerch
import GaloisForLFunctions.RHTower.CCM.CCMConnesConsaniCircleDirac

/-!
# ζ-regularized determinant of the logarithmic circle Dirac operator

On `L²([λ⁻¹, λ], d*u)` with periodic boundary conditions the logarithmic Dirac operator `D₀` has
simple spectrum `d_n = πn/a`, `n ∈ ℤ`, where `a = log λ` (`ccmCircleDirac (2a)`).  For `Im z < 0`
write `w = az/π`; then `d_n - z = (π/a)(n - w)` and, with principal powers,

`Z(s) = ∑_{n ∈ ℤ} (d_n - z)^{-s} = (π/a)^{-s} [ζ_H(s, -w) + e^{-iπs} ζ_H(s, 1 + w)]`   (`Re s > 1`),

because `-(k + 1 + w)` lies in the upper half plane when `k + 1 + w` lies in the lower one.  The
right side is holomorphic on `Re s > -1/2`, `s ≠ 1`, vanishes at `s = 0`, and complex-shift Lerch
plus the reflection formula give

`det_ζ(D₀ - z) = exp(-Z'(0)) = 2π e^{iπ(-1/2-w)} / (Γ(-w) Γ(1+w)) = 1 - e^{-2iaz} = 1 - λ^{-2iz}`.
-/

noncomputable section

open Complex Filter Topology
open GaloisForLFunctions.HTGeometry

namespace RHTower

/-- The spectrum `d_n = πn/a` of the logarithmic circle Dirac operator on `[λ⁻¹, λ]`,
`a = log λ`. -/
def ccmLogDiracFrequency (a : ℝ) (n : ℤ) : ℝ := Real.pi * (n : ℝ) / a

theorem ccmCircleFrequency_two_mul (a : ℝ) (n : ℤ) :
    ccmCircleFrequency (2 * a) n = ccmLogDiracFrequency a n := by
  unfold ccmCircleFrequency ccmLogDiracFrequency
  by_cases ha : a = 0
  · simp [ha]
  · field_simp

/-- The dimensionless spectral variable `w = az/π`. -/
def ccmLogDiracShift (a : ℝ) (z : ℂ) : ℂ := (a : ℂ) * z / Real.pi

theorem ccmLogDiracShift_im_neg {a : ℝ} (ha : 0 < a) {z : ℂ} (hz : z.im < 0) :
    (ccmLogDiracShift a z).im < 0 := by
  have hπ : 0 < Real.pi := Real.pi_pos
  have h : (ccmLogDiracShift a z).im = a * z.im / Real.pi := by
    simp [ccmLogDiracShift, Complex.div_ofReal_im]
  rw [h]
  exact div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg ha hz) hπ

theorem neg_ccmLogDiracShift_mem_slitPlane {a : ℝ} (ha : 0 < a) {z : ℂ} (hz : z.im < 0) :
    -ccmLogDiracShift a z ∈ slitPlane :=
  mem_slitPlane_iff.mpr (Or.inr (by simp; exact (ccmLogDiracShift_im_neg ha hz).ne))

theorem one_add_ccmLogDiracShift_mem_slitPlane {a : ℝ} (ha : 0 < a) {z : ℂ} (hz : z.im < 0) :
    1 + ccmLogDiracShift a z ∈ slitPlane :=
  mem_slitPlane_iff.mpr (Or.inr (by simp; exact (ccmLogDiracShift_im_neg ha hz).ne))

/-- Analytic continuation of the spectral zeta function `∑_n (d_n - z)^{-s}`. -/
def ccmLogDiracZeta (a : ℝ) (z s : ℂ) : ℂ :=
  ((Real.pi / a : ℝ) : ℂ) ^ (-s) *
    (hurwitzZetaEMC (-ccmLogDiracShift a z) s +
      Complex.exp (-(Real.pi : ℂ) * I * s) * hurwitzZetaEMC (1 + ccmLogDiracShift a z) s)

/-! ## Branch bookkeeping -/

/-- A positive real factor leaves principal powers multiplicative. -/
theorem ofReal_mul_cpow_of_pos {r : ℝ} (hr : 0 < r) {u : ℂ} (hu : u ≠ 0) (c : ℂ) :
    ((r : ℂ) * u) ^ c = (r : ℂ) ^ c * u ^ c := by
  have hru : (r : ℂ) * u ≠ 0 := mul_ne_zero (Complex.ofReal_ne_zero.mpr hr.ne') hu
  rw [Complex.cpow_def_of_ne_zero hru, Complex.cpow_def_of_ne_zero
    (Complex.ofReal_ne_zero.mpr hr.ne'), Complex.cpow_def_of_ne_zero hu,
    Complex.log_ofReal_mul hr hu, ← Complex.exp_add, Complex.ofReal_log hr.le]
  congr 1
  ring

/-- Reflecting a point of the lower half plane into the upper one adds `π` to the argument. -/
theorem neg_cpow_of_im_neg {u : ℂ} (hu : u.im < 0) (c : ℂ) :
    (-u) ^ c = Complex.exp ((Real.pi : ℂ) * I * c) * u ^ c := by
  have hu0 : u ≠ 0 := fun h => by rw [h] at hu; simp at hu
  have hnu0 : -u ≠ 0 := neg_ne_zero.mpr hu0
  have hlog : Complex.log (-u) = Complex.log u + (Real.pi : ℂ) * I := by
    apply Complex.ext
    · simp [Complex.log_re]
    · simp [Complex.log_im, Complex.arg_neg_eq_arg_add_pi_of_im_neg hu]
  rw [Complex.cpow_def_of_ne_zero hnu0, Complex.cpow_def_of_ne_zero hu0, hlog, ← Complex.exp_add]
  congr 1
  ring

theorem ccmLogDiracFrequency_sub_nat {a : ℝ} (ha : 0 < a) (z : ℂ) (k : ℕ) :
    ((ccmLogDiracFrequency a (k : ℤ) : ℝ) : ℂ) - z =
      ((Real.pi / a : ℝ) : ℂ) * (((k : ℝ) : ℂ) + -ccmLogDiracShift a z) := by
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have ha' : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha.ne'
  unfold ccmLogDiracFrequency ccmLogDiracShift
  push_cast
  field_simp
  ring

theorem ccmLogDiracFrequency_sub_neg {a : ℝ} (ha : 0 < a) (z : ℂ) (k : ℕ) :
    ((ccmLogDiracFrequency a (-((k : ℤ) + 1)) : ℝ) : ℂ) - z =
      ((Real.pi / a : ℝ) : ℂ) * -(((k : ℝ) : ℂ) + (1 + ccmLogDiracShift a z)) := by
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have ha' : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha.ne'
  unfold ccmLogDiracFrequency ccmLogDiracShift
  push_cast
  field_simp
  ring

/-! ## The spectral zeta function -/

theorem ccmLogDiracSpectrum_pos_cpow {a : ℝ} (ha : 0 < a) {z : ℂ} (hz : z.im < 0) (s : ℂ)
    (k : ℕ) :
    (((ccmLogDiracFrequency a (k : ℤ) : ℝ) : ℂ) - z) ^ (-s) =
      ((Real.pi / a : ℝ) : ℂ) ^ (-s) * (((k : ℝ) : ℂ) + -ccmLogDiracShift a z) ^ (-s) := by
  rw [ccmLogDiracFrequency_sub_nat ha z k, ofReal_mul_cpow_of_pos (div_pos Real.pi_pos ha)
    (ofReal_add_ne_zero (neg_ccmLogDiracShift_mem_slitPlane ha hz) (Nat.cast_nonneg k))]

theorem ccmLogDiracSpectrum_neg_cpow {a : ℝ} (ha : 0 < a) {z : ℂ} (hz : z.im < 0) (s : ℂ)
    (k : ℕ) :
    (((ccmLogDiracFrequency a (-((k : ℤ) + 1)) : ℝ) : ℂ) - z) ^ (-s) =
      ((Real.pi / a : ℝ) : ℂ) ^ (-s) *
        (Complex.exp (-(Real.pi : ℂ) * I * s) *
          (((k : ℝ) : ℂ) + (1 + ccmLogDiracShift a z)) ^ (-s)) := by
  have hkw : (((k : ℝ) : ℂ) + (1 + ccmLogDiracShift a z)).im < 0 := by
    have := ccmLogDiracShift_im_neg ha hz
    simpa using this
  have hne : -(((k : ℝ) : ℂ) + (1 + ccmLogDiracShift a z)) ≠ 0 :=
    neg_ne_zero.mpr fun h => by rw [h] at hkw; simp at hkw
  rw [ccmLogDiracFrequency_sub_neg ha z k, ofReal_mul_cpow_of_pos (div_pos Real.pi_pos ha) hne,
    neg_cpow_of_im_neg hkw]
  congr 2
  ring_nf

/-- The spectral series `∑_n (d_n - z)^{-s}` converges for `Re s > 1`. -/
theorem summable_ccmLogDiracSpectrum {a : ℝ} (ha : 0 < a) {z : ℂ} (hz : z.im < 0) {s : ℂ}
    (hs : 1 < s.re) :
    Summable fun n : ℤ => (((ccmLogDiracFrequency a n : ℝ) : ℂ) - z) ^ (-s) := by
  refine Summable.of_nat_of_neg_add_one ?_ ?_
  · simp_rw [ccmLogDiracSpectrum_pos_cpow ha hz s]
    exact (summable_shiftCpowC (neg_ccmLogDiracShift_mem_slitPlane ha hz) hs).mul_left _
  · simp_rw [ccmLogDiracSpectrum_neg_cpow ha hz s]
    exact ((summable_shiftCpowC (one_add_ccmLogDiracShift_mem_slitPlane ha hz) hs).mul_left
      _).mul_left _

/-- **The continuation is the spectral zeta function** for `Re s > 1`. -/
theorem ccmLogDiracZeta_eq_tsum {a : ℝ} (ha : 0 < a) {z : ℂ} (hz : z.im < 0) {s : ℂ}
    (hs : 1 < s.re) :
    ccmLogDiracZeta a z s = ∑' n : ℤ, (((ccmLogDiracFrequency a n : ℝ) : ℂ) - z) ^ (-s) := by
  have hb₁ := neg_ccmLogDiracShift_mem_slitPlane ha hz
  have hb₂ := one_add_ccmLogDiracShift_mem_slitPlane ha hz
  have hsum₁ := summable_shiftCpowC hb₁ hs
  have hsum₂ := summable_shiftCpowC hb₂ hs
  rw [tsum_of_nat_of_neg_add_one]
  · simp_rw [ccmLogDiracSpectrum_pos_cpow ha hz s, ccmLogDiracSpectrum_neg_cpow ha hz s]
    rw [tsum_mul_left, tsum_mul_left, tsum_mul_left, ← hurwitzZetaEMC_eq_tsum hb₁ hs,
      ← hurwitzZetaEMC_eq_tsum hb₂ hs, ccmLogDiracZeta, mul_add]
  · simp_rw [ccmLogDiracSpectrum_pos_cpow ha hz s]
    exact hsum₁.mul_left _
  · simp_rw [ccmLogDiracSpectrum_neg_cpow ha hz s]
    exact (hsum₂.mul_left _).mul_left _

/-- The continuation is holomorphic on `Re s > -1/2`, `s ≠ 1`. -/
theorem differentiableAt_ccmLogDiracZeta {a : ℝ} (ha : 0 < a) {z : ℂ} (hz : z.im < 0) {s : ℂ}
    (hs : -(1 / 2 : ℝ) < s.re) (hs1 : s ≠ 1) : DifferentiableAt ℂ (ccmLogDiracZeta a z) s := by
  have hπa : ((Real.pi / a : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (div_pos Real.pi_pos ha).ne'
  unfold ccmLogDiracZeta
  refine DifferentiableAt.mul ((differentiableAt_id.neg).const_cpow (Or.inl hπa)) ?_
  refine DifferentiableAt.add
    (differentiableAt_hurwitzZetaEMC (neg_ccmLogDiracShift_mem_slitPlane ha hz) hs hs1) ?_
  refine DifferentiableAt.mul ?_
    (differentiableAt_hurwitzZetaEMC (one_add_ccmLogDiracShift_mem_slitPlane ha hz) hs hs1)
  exact (differentiableAt_const _ |>.mul differentiableAt_id).cexp

/-- `Z(0) = 0`: the regularized dimension of the circle Dirac spectrum vanishes. -/
theorem ccmLogDiracZeta_zero (a : ℝ) (z : ℂ) : ccmLogDiracZeta a z 0 = 0 := by
  simp only [ccmLogDiracZeta, hurwitzZetaEMC_zero, neg_zero, Complex.cpow_zero, mul_zero,
    Complex.exp_zero, one_mul]
  ring

/-- The derivative at `s = 0` of the spectral zeta function. -/
theorem hasDerivAt_ccmLogDiracZeta_zero {a : ℝ} (ha : 0 < a) {z : ℂ} (hz : z.im < 0) :
    HasDerivAt (ccmLogDiracZeta a z)
      (((-ccmLogDiracShift a z) - 1 / 2) * Complex.log (-ccmLogDiracShift a z) -
          (-ccmLogDiracShift a z) - binetKernelC (-ccmLogDiracShift a z) +
        (((1 + ccmLogDiracShift a z) - 1 / 2) * Complex.log (1 + ccmLogDiracShift a z) -
          (1 + ccmLogDiracShift a z) - binetKernelC (1 + ccmLogDiracShift a z)) -
        (Real.pi : ℂ) * I * (1 / 2 - (1 + ccmLogDiracShift a z))) 0 := by
  set w := ccmLogDiracShift a z
  have hπa : ((Real.pi / a : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (div_pos Real.pi_pos ha).ne'
  have h₁ := hasDerivAt_hurwitzZetaEMC_zero (neg_ccmLogDiracShift_mem_slitPlane ha hz)
  have h₂ := hasDerivAt_hurwitzZetaEMC_zero (one_add_ccmLogDiracShift_mem_slitPlane ha hz)
  have hR : HasDerivAt (fun s : ℂ => ((Real.pi / a : ℝ) : ℂ) ^ (-s))
      (((Real.pi / a : ℝ) : ℂ) ^ (-(0 : ℂ)) * Complex.log ((Real.pi / a : ℝ) : ℂ) * (-1)) 0 :=
    (hasDerivAt_neg 0).const_cpow (Or.inl hπa)
  have hE : HasDerivAt (fun s : ℂ => Complex.exp (-(Real.pi : ℂ) * I * s))
      (Complex.exp (-(Real.pi : ℂ) * I * 0) * (-(Real.pi : ℂ) * I)) 0 := by
    have := ((hasDerivAt_id (0 : ℂ)).const_mul (-(Real.pi : ℂ) * I)).cexp
    simpa using this
  have hG := h₁.add (hE.mul h₂)
  have hZ := hR.mul hG
  have hfun : ccmLogDiracZeta a z = (fun s : ℂ => ((Real.pi / a : ℝ) : ℂ) ^ (-s)) *
      (hurwitzZetaEMC (-w) + (fun s : ℂ => Complex.exp (-(Real.pi : ℂ) * I * s)) *
        hurwitzZetaEMC (1 + w)) := by
    funext s
    rfl
  rw [hfun]
  refine hZ.congr_deriv ?_
  simp only [Pi.add_apply, Pi.mul_apply, hurwitzZetaEMC_zero, neg_zero, Complex.cpow_zero,
    mul_zero, Complex.exp_zero, one_mul]
  ring

/-- **The ζ-regularized determinant of `D₀ - z`.**  For `Im z < 0`,
`exp(-Z'(0)) = 1 - e^{-2iaz}`, i.e. `det_ζ(D₀ - z) = 1 - λ^{-2iz}` with `λ = e^a`. -/
theorem exp_neg_deriv_ccmLogDiracZeta_zero {a : ℝ} (ha : 0 < a) {z : ℂ} (hz : z.im < 0) :
    Complex.exp (-deriv (ccmLogDiracZeta a z) 0) =
      1 - Complex.exp (-2 * I * (a : ℂ) * z) := by
  set w := ccmLogDiracShift a z with hw
  have hb₁ := neg_ccmLogDiracShift_mem_slitPlane ha hz
  have hb₂ := one_add_ccmLogDiracShift_mem_slitPlane ha hz
  rw [(hasDerivAt_ccmLogDiracZeta_zero ha hz).deriv]
  -- split the exponential into the two Lerch factors and the phase
  have hL₁ := exp_neg_deriv_hurwitzZetaEMC_zero hb₁
  have hL₂ := exp_neg_deriv_hurwitzZetaEMC_zero hb₂
  rw [(hasDerivAt_hurwitzZetaEMC_zero hb₁).deriv] at hL₁
  rw [(hasDerivAt_hurwitzZetaEMC_zero hb₂).deriv] at hL₂
  set X₁ := (-w - 1 / 2) * Complex.log (-w) - -w - binetKernelC (-w)
  set X₂ := ((1 + w) - 1 / 2) * Complex.log (1 + w) - (1 + w) - binetKernelC (1 + w)
  have hsplit : -(X₁ + X₂ - (Real.pi : ℂ) * I * (1 / 2 - (1 + w))) =
      -X₁ + -X₂ + (Real.pi : ℂ) * I * (1 / 2 - (1 + w)) := by ring
  rw [hsplit, Complex.exp_add, Complex.exp_add, hL₁, hL₂]
  -- the reflection formula
  have hnotint : ∀ m : ℤ, w ≠ m := by
    intro m h
    have := ccmLogDiracShift_im_neg ha hz
    rw [← hw, h] at this
    simp at this
  have hrefl := Complex.Gamma_mul_Gamma_one_sub (1 + w)
  rw [show (1 : ℂ) - (1 + w) = -w by ring] at hrefl
  have hsin : Complex.sin ((Real.pi : ℂ) * (1 + w)) = -Complex.sin ((Real.pi : ℂ) * w) := by
    rw [show (Real.pi : ℂ) * (1 + w) = (Real.pi : ℂ) * w + Real.pi by ring, Complex.sin_add_pi]
  have hsin0 : Complex.sin ((Real.pi : ℂ) * w) ≠ 0 := by
    intro h0
    obtain ⟨m, hm⟩ := Complex.sin_eq_zero_iff.mp h0
    apply hnotint m
    have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    have : (Real.pi : ℂ) * w = (Real.pi : ℂ) * m := by rw [hm]; ring
    exact mul_left_cancel₀ hπ this
  have hΓ₁ : Complex.Gamma (-w) ≠ 0 := Complex.Gamma_ne_zero fun m hm => by
    have := hb₁; rw [hm] at this
    rcases mem_slitPlane_iff.mp this with h | h
    · simp at h; linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
    · simp at h
  have hΓ₂ : Complex.Gamma (1 + w) ≠ 0 := Complex.Gamma_ne_zero fun m hm => by
    have := hb₂; rw [hm] at this
    rcases mem_slitPlane_iff.mp this with h | h
    · simp at h; linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
    · simp at h
  have hsq : ((Real.sqrt (2 * Real.pi) : ℝ) : ℂ) * ((Real.sqrt (2 * Real.pi) : ℝ) : ℂ) =
      2 * Real.pi := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by positivity)]
    push_cast
    ring
  have hprod : (Real.sqrt (2 * Real.pi) : ℂ) / Complex.Gamma (-w) *
      ((Real.sqrt (2 * Real.pi) : ℂ) / Complex.Gamma (1 + w)) =
        -2 * Complex.sin ((Real.pi : ℂ) * w) := by
    rw [div_mul_div_comm, hsq, mul_comm (Complex.Gamma (-w)), hrefl, hsin]
    have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    field_simp
  rw [hprod]
  -- the phase and the sine
  have hwz : (Real.pi : ℂ) * w = (a : ℂ) * z := by
    have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    rw [hw, ccmLogDiracShift]
    field_simp
  have hphase : (Real.pi : ℂ) * I * (1 / 2 - (1 + w)) =
      -((Real.pi : ℂ) / 2 * I) + -((a : ℂ) * z * I) := by
    rw [← hwz]; ring
  rw [hphase, Complex.exp_add]
  have hi : Complex.exp (-((Real.pi : ℂ) / 2 * I)) = -I := by
    rw [Complex.exp_neg, Complex.exp_pi_div_two_mul_I, Complex.inv_I]
  rw [hi, hwz]
  have hexp2 : Complex.exp (-2 * I * (a : ℂ) * z) =
      Complex.exp (-((a : ℂ) * z * I)) * Complex.exp (-((a : ℂ) * z * I)) := by
    rw [← Complex.exp_add]; congr 1; ring
  have hinv : Complex.exp ((a : ℂ) * z * I) * Complex.exp (-((a : ℂ) * z * I)) = 1 := by
    rw [← Complex.exp_add]; simp
  rw [hexp2, Complex.sin]
  have hneg : -((a : ℂ) * z) * I = -((a : ℂ) * z * I) := by ring
  rw [hneg]
  set u := Complex.exp ((a : ℂ) * z * I)
  set v := Complex.exp (-((a : ℂ) * z * I))
  linear_combination ((v - u) * v) * Complex.I_mul_I + hinv

end RHTower
