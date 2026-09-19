import GaloisForLFunctions.RHTower.EisensteinHeckeMaassSelberg
import GaloisForLFunctions.RHTower.EisensteinResonantStateNorm

/-!
# The exact Hecke moment of a truncated resonant state

For a parameter `u` with `Λ(1 + 2u) = 0` (a resonant state: `1 + 2u` is a zero of the completed
zeta function) and `Re u < 0`, the Hermitian Hecke moment of the truncation `Λ^Y E_u` is

`∫_𝒟 (T_pΛ^Y E_u)·conj(Λ^Y E_u) = (p^u + p^{ū}) · ∫_𝒟 |Λ^Y E_u|²`

for every prime `p` and every height `Y ≥ p`.  The band integral of the Hecke–Maass–Selberg
relation collapses because `Λ(2v) = conj Λ(1+2u) = 0` for the partner `v = −ū`, and the
remaining power integral is `Y^{-2 Re u}(1 − p^{2 Re u})/(−2 Re u)`; the truncation exactly
replaces the untruncated Hecke eigenvalue `p^u + p^{-u}` by the real number `p^u + p^{ū}`.
-/

open Complex MeasureTheory Set UpperHalfPlane ModularGroup
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

/-- The Hermitian Hecke moment `∫_𝒟 (T_pΛ^Y E_u)·conj(Λ^Y E_u)`. -/
def heckeHermitianMoment (p : ℕ) (u : ℂ) (Y : ℝ) : ℂ :=
  ∫ z in fd, heckeTruncated p u Y z * (starRingEnd ℂ) (truncatedLineModel u Y z)

theorem heckeHermitianMoment_eq {u : ℂ} (hu : u ∈ eisensteinLineDomain) (p : ℕ) (Y : ℝ) :
    heckeHermitianMoment p u Y =
      ∫ z in fd, heckeTruncated p u Y z * truncatedLineModel (-(starRingEnd ℂ) u) Y z := by
  unfold heckeHermitianMoment
  refine setIntegral_congr_fun isClosed_fd.measurableSet fun z _ => ?_
  have him : ((starRingEnd ℂ) u).im ≠ 0 := by simp; exact hu.2.ne'
  rw [truncatedLineModel_conj, truncatedLineModel_neg him]

theorem constantCoefficient_false (u : ℂ) :
    d4BMCompletedEisensteinCuspConstantCoefficient u false = msB u := by
  simp [d4BMCompletedEisensteinCuspConstantCoefficient, msB]

theorem constantCoefficient_true (u : ℂ) :
    d4BMCompletedEisensteinCuspConstantCoefficient u true = msA u := by
  simp [d4BMCompletedEisensteinCuspConstantCoefficient, msA]

theorem weylExponent_false (u : ℂ) :
    d4BMCompletedEisensteinCuspWeylExponent u false = 1 / 2 - u := by
  simp only [d4BMCompletedEisensteinCuspWeylExponent, d4BMCuspSign, Bool.false_eq_true, if_false,
    Int.cast_neg, Int.cast_one]
  ring

theorem lowerBandRemainder_of_msA_eq_zero (p : ℕ) {u : ℂ} (hA : msA u = 0) (y : ℝ) :
    lowerBandRemainder p u y =
      -(msB u * (y : ℂ) ^ (1 / 2 - u) * ((((Real.sqrt p)⁻¹ : ℝ) : ℂ) * (p : ℂ) ^ (1 / 2 - u))) := by
  unfold lowerBandRemainder
  rw [constantCoefficient_false, constantCoefficient_true, weylExponent_false, hA]
  ring

/-- The band integral of the Hecke–Maass–Selberg relation for a resonant state and its
Hermitian partner. -/
theorem resonant_band_integral {p : ℕ} (hp : 0 < p) {u : ℂ} (hu : u ∈ eisensteinLineDomain)
    (hre : u.re < 0) (hA : msA u = 0) {Y : ℝ} (hY : (p : ℝ) ≤ Y) :
    ∫ y in Ioc (Y / p) Y, lowerBandRemainder p u y *
        d4BMCompletedEisensteinCuspConstantPart .scalar (-(starRingEnd ℂ) u) y /
          ((y : ℝ) : ℂ) ^ 2 =
      -((((Real.sqrt p)⁻¹ : ℝ) : ℂ) * (p : ℂ) ^ (1 / 2 - u)) * ((‖msB u‖ ^ 2 : ℝ) : ℂ) *
        ((((Y ^ (-2 * u.re) : ℝ) : ℂ) - (((Y / p) ^ (-2 * u.re) : ℝ) : ℂ)) /
          ((-2 * u.re : ℝ) : ℂ)) := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hY0 : 0 < Y := lt_of_lt_of_le hpR hY
  have hYp : 0 < Y / p := by positivity
  have hYpY : Y / p ≤ Y := by
    rw [div_le_iff₀ hpR]
    have : (1 : ℝ) ≤ p := by exact_mod_cast hp
    nlinarith
  have him : u.im ≠ 0 := hu.2.ne'
  set K : ℂ := -((((Real.sqrt p)⁻¹ : ℝ) : ℂ) * (p : ℂ) ^ (1 / 2 - u)) * ((‖msB u‖ ^ 2 : ℝ) : ℂ)
    with hK
  set r : ℂ := ((-2 * u.re - 1 : ℝ) : ℂ) with hr
  have hpt : ∀ y ∈ Ioc (Y / p) Y, lowerBandRemainder p u y *
      d4BMCompletedEisensteinCuspConstantPart .scalar (-(starRingEnd ℂ) u) y /
        ((y : ℝ) : ℂ) ^ 2 = K * ((y : ℝ) : ℂ) ^ r := by
    intro y hy
    have hy0 : 0 < y := lt_trans hYp hy.1
    rw [lowerBandRemainder_of_msA_eq_zero p hA, cuspConstantPart_eq_msAB, msB_neg_conj him,
      msA_neg_conj him, hA, map_zero, zero_mul, zero_add]
    have hexp : (1 / 2 - u) + (1 / 2 + -(starRingEnd ℂ) u) - 2 = r := by
      rw [hr]
      apply Complex.ext
      · simp; ring
      · simp
    have hmul := cpow_mul_cpow_div_sq hy0 (1 / 2 - u) (1 / 2 + -(starRingEnd ℂ) u)
    rw [hexp] at hmul
    have hBB : msB u * (starRingEnd ℂ) (msB u) = ((‖msB u‖ ^ 2 : ℝ) : ℂ) := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    rw [hK, ← hmul, ← hBB]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioc hpt, integral_const_mul,
    ← intervalIntegral.integral_of_le hYpY]
  have hre' : -1 < r.re := by
    rw [hr]
    simp
    linarith
  rw [integral_cpow (Or.inl hre')]
  have h1 : r + 1 = ((-2 * u.re : ℝ) : ℂ) := by
    rw [hr]
    push_cast
    ring
  rw [h1, ← Complex.ofReal_cpow hY0.le, ← Complex.ofReal_cpow hYp.le]

/-- **The Hecke moment of a truncated resonant state.**  For `Λ(1+2u) = 0`, `Re u < 0`,
`Im u > 0`, every prime `p` and every height `Y ≥ p`,
`∫_𝒟 (T_pΛ^Y E_u)·conj(Λ^Y E_u) = (p^u + p^{ū})·∫_𝒟 |Λ^Y E_u|²`. -/
theorem heckeHermitianMoment_resonant {p : ℕ} (hp : p.Prime) {u : ℂ}
    (hu : u ∈ eisensteinLineDomain) (hre : u.re < 0) (hA : msA u = 0) {Y : ℝ}
    (hY : (p : ℝ) ≤ Y) :
    heckeHermitianMoment p u Y =
      ((p : ℂ) ^ u + (p : ℂ) ^ ((starRingEnd ℂ) u)) *
        ((∫ z in fd, ‖truncatedLineModel u Y z‖ ^ 2 : ℝ) : ℂ) := by
  have hp0 : 0 < p := hp.pos
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp0
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast hp0.ne'
  have hY0 : 0 < Y := lt_of_lt_of_le hpR hY
  have hY1 : 1 ≤ Y := by
    have : (1 : ℝ) ≤ p := by exact_mod_cast hp0
    linarith
  rw [heckeHermitianMoment_eq hu, heckeMaassSelberg hp u _ hY, resonant_band_integral hp0 hu hre hA hY,
    ← integral_norm_sq_eq_truncatedPairing hu Y, integral_norm_sq_of_msA_eq_zero hu hre hA hY1]
  -- the scalar identities
  have hs : (((Real.sqrt p)⁻¹ : ℝ) : ℂ) * (p : ℂ) ^ (1 / 2 - u) = (p : ℂ) ^ (-u) := by
    rw [sub_eq_add_neg, Complex.cpow_add _ _ hpC, ← sqrt_eq_cpow_half p]
    have hsq : (Real.sqrt p : ℂ) ≠ 0 := by
      have : 0 < Real.sqrt p := Real.sqrt_pos.mpr hpR
      exact_mod_cast this.ne'
    push_cast
    field_simp
  have hdiv : (Y / p) ^ (-2 * u.re) = Y ^ (-2 * u.re) / (p : ℝ) ^ (-2 * u.re) :=
    Real.div_rpow hY0.le hpR.le _
  have hQ : (((p : ℝ) ^ (-2 * u.re) : ℝ) : ℂ) = (p : ℂ) ^ (-u - (starRingEnd ℂ) u) := by
    rw [Complex.ofReal_cpow hpR.le]
    push_cast
    congr 1
    apply Complex.ext
    · simp; ring
    · simp
  have hQinv : ((p : ℂ) ^ (-u - (starRingEnd ℂ) u))⁻¹ = (p : ℂ) ^ (u + (starRingEnd ℂ) u) := by
    rw [show -u - (starRingEnd ℂ) u = -(u + (starRingEnd ℂ) u) by ring, Complex.cpow_neg, inv_inv]
  have hpu : (p : ℂ) ^ (-u) * (p : ℂ) ^ (u + (starRingEnd ℂ) u) = (p : ℂ) ^ ((starRingEnd ℂ) u) := by
    rw [← Complex.cpow_add _ _ hpC]
    congr 1
    ring
  have hQne : (p : ℂ) ^ (-u - (starRingEnd ℂ) u) ≠ 0 := by
    intro h
    exact hpC ((Complex.cpow_eq_zero_iff _ _).mp h).1
  have hre2 : ((-2 * u.re : ℝ) : ℂ) ≠ 0 := by
    have : (-2 * u.re : ℝ) ≠ 0 := by linarith
    exact_mod_cast this
  rw [hdiv, hs]
  push_cast
  rw [hQ]
  field_simp
  rw [← hpu, ← hQinv]
  field_simp
  ring

/-- The resonant Hecke moment is real: it equals `2 Re(p^u)` times the truncated norm. -/
theorem heckeHermitianMoment_resonant_re {p : ℕ} (hp : p.Prime) {u : ℂ}
    (hu : u ∈ eisensteinLineDomain) (hre : u.re < 0) (hA : msA u = 0) {Y : ℝ}
    (hY : (p : ℝ) ≤ Y) :
    heckeHermitianMoment p u Y =
      ((2 * ((p : ℂ) ^ u).re * ∫ z in fd, ‖truncatedLineModel u Y z‖ ^ 2 : ℝ) : ℂ) := by
  rw [heckeHermitianMoment_resonant hp hu hre hA hY]
  have hconj : (p : ℂ) ^ ((starRingEnd ℂ) u) = (starRingEnd ℂ) ((p : ℂ) ^ u) := by
    rw [Complex.cpow_conj _ _ (by rw [Complex.natCast_arg]; exact Real.pi_ne_zero.symm),
      Complex.conj_natCast]
  rw [hconj, Complex.add_conj]
  push_cast
  ring

end

end RHTower
