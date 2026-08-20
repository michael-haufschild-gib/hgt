/-
The finite Hardy identity for the certificate carrier on the critical line.

On the line `s = ½+iτ` one has `1 − s = conj s`, so the χ-factor is unimodular (`‖zetaChi s‖ = 1`) and
the carrier reflects onto its own conjugate: `zetaChi·conj(gN) = gN` (the finite analog of `ξ`'s
reality). Writing `D = dirichletPoly N(½+iτ)`, the carrier is `gN = D + zetaChi·conj D`, i.e. a
unimodular phase `w` (a square root of `zetaChi`) times a REAL amplitude:
`conj(w)·gN = 2·Re(conj(w)·D) =: H_N(τ)`, the finite Hardy carrier. Hence `‖gN(½+iτ)‖ = |H_N(τ)|`, so
the on-line zeros of `gN` are exactly the zeros of the real function `H_N`.  Its principal-log
phase can jump by sign, so this module only uses its square continuously; `HardyZ.lean` later
constructs the branch-free continuous Gamma-oriented amplitude for sign arguments.  This is the
honest correction to the impossible on-line modulus floor
(the two AFE halves have equal modulus on the line, `‖zetaChi·conj D‖ = ‖D‖`, so no single term
dominates).
-/
import GaloisForLFunctions.RHTower.ZetaCarrier
import GaloisForLFunctions.HTGeometry.UnitaryReflectionPhaseHalving
open Complex
namespace RHTower

open GaloisForLFunctions.HTGeometry

noncomputable def linePt (τ : ℝ) : ℂ := ((1/2 : ℝ) : ℂ) + (τ : ℂ) * I

theorem conj_linePt (τ : ℝ) : (starRingEnd ℂ) (linePt τ) = 1 - linePt τ := by
  unfold linePt; apply Complex.ext
  · simp; norm_num
  · simp

theorem linePt_re (τ : ℝ) : (linePt τ).re = 1/2 := by unfold linePt; simp
theorem linePt_re_pos (τ : ℝ) : 0 < (linePt τ).re := by rw [linePt_re]; norm_num
theorem linePt_re_lt_one (τ : ℝ) : (linePt τ).re < 1 := by rw [linePt_re]; norm_num
theorem linePt_im (τ : ℝ) : (linePt τ).im = τ := by unfold linePt; simp

theorem norm_zetaChi_line (τ : ℝ) : ‖zetaChi (linePt τ)‖ = 1 := by
  have hstrip : zetaChi (linePt τ) * zetaChi (1 - linePt τ) = 1 :=
    zetaChi_mul_one_sub_of_mem_strip (linePt_re_pos τ) (linePt_re_lt_one τ)
  rw [← conj_linePt, zetaChi_conj, Complex.mul_conj] at hstrip
  have hns : normSq (zetaChi (linePt τ)) = 1 := by exact_mod_cast hstrip
  have h1 : ‖zetaChi (linePt τ)‖ ^ 2 = 1 := (Complex.normSq_eq_norm_sq _).symm.trans hns
  rw [← Real.sqrt_one, ← h1, Real.sqrt_sq (norm_nonneg _)]

theorem zetaChi_line_ne_zero (τ : ℝ) : zetaChi (linePt τ) ≠ 0 := by
  rw [← norm_ne_zero_iff, norm_zetaChi_line]; norm_num

theorem gN_line_conjForm (N : ℕ) (τ : ℝ) :
    gN N (linePt τ)
      = dirichletPoly N (linePt τ)
        + zetaChi (linePt τ) * (starRingEnd ℂ) (dirichletPoly N (linePt τ)) := by
  unfold gN chiSymmetrize; rw [← conj_linePt, dirichletPoly_conj]

/-- **The finite functional equation of the carrier on the line.** `gN` satisfies
`zetaChi·conj(gN) = gN` on the critical line: Schwarz reflection `conj(gN s) = gN(1−s)` combined with
the carrier FE `gN(1−s) = zetaChi(1−s)·gN s` and the χ-identity `zetaChi s·zetaChi(1−s) = 1`. This is
the finite analog of `ξ`'s reality on the line, and it forces `gN(½+iτ)` onto the ray at angle
`½·arg(zetaChi)`. -/
theorem zetaChi_mul_conj_gN_line (N : ℕ) (τ : ℝ) :
    zetaChi (linePt τ) * (starRingEnd ℂ) (gN N (linePt τ)) = gN N (linePt τ) := by
  have hconj : (starRingEnd ℂ) (gN N (linePt τ)) = gN N (1 - linePt τ) := by
    rw [← conj_linePt, gN_conj]
  rw [hconj, gN_one_sub (linePt_re_pos τ) (linePt_re_lt_one τ), ← mul_assoc,
    zetaChi_mul_one_sub_of_mem_strip (linePt_re_pos τ) (linePt_re_lt_one τ), one_mul]

/-- The unimodular square-root of the χ-phase: `w = exp(½ log zetaChi)`, so `w² = zetaChi` and
`‖w‖ = 1` on the line. -/
noncomputable def hardyPhase (τ : ℝ) : ℂ := Complex.exp (Complex.log (zetaChi (linePt τ)) / 2)

theorem hardyPhase_sq (τ : ℝ) : hardyPhase τ * hardyPhase τ = zetaChi (linePt τ) := by
  rw [hardyPhase, ← Complex.exp_add,
    show Complex.log (zetaChi (linePt τ)) / 2 + Complex.log (zetaChi (linePt τ)) / 2
      = Complex.log (zetaChi (linePt τ)) by ring,
    Complex.exp_log (zetaChi_line_ne_zero τ)]

theorem norm_hardyPhase (τ : ℝ) : ‖hardyPhase τ‖ = 1 := by
  rw [hardyPhase, Complex.norm_exp]
  have hre : (Complex.log (zetaChi (linePt τ)) / 2).re = 0 := by
    rw [Complex.div_re]
    simp only [Complex.log_re, norm_zetaChi_line, Real.log_one]
    norm_num
  rw [hre, Real.exp_zero]

theorem conj_hardyPhase_mul_self (τ : ℝ) : (starRingEnd ℂ) (hardyPhase τ) * hardyPhase τ = 1 := by
  rw [mul_comm, Complex.mul_conj]
  have hns : normSq (hardyPhase τ) = 1 := by
    rw [Complex.normSq_eq_norm_sq, norm_hardyPhase]; norm_num
  rw [hns]; norm_num

/-- The chosen square root of the zeta reflection factor is a unitary phase. -/
theorem hardyPhase_isUnitary (τ : ℝ) : IsUnitaryPhase (hardyPhase τ) :=
  conj_hardyPhase_mul_self τ

/-- The finite carrier is reflected by the square of its Hardy phase.  This is the exact Prop
interface connecting its functional equation to unitary phase halving. -/
theorem gN_line_isPhaseReflected (N : ℕ) (τ : ℝ) :
    IsPhaseReflected (hardyPhase τ) (gN N (linePt τ)) := by
  unfold IsPhaseReflected
  rw [hardyPhase_sq]
  exact zetaChi_mul_conj_gN_line N τ

/-- **The finite Hardy carrier** `H_N(τ) := Re(conj(w)·gN(½+iτ))`, the real amplitude whose sign
changes are the on-line zeros of `gN`. -/
noncomputable def hardyCarrier (N : ℕ) (τ : ℝ) : ℝ :=
  ((starRingEnd ℂ) (hardyPhase τ) * gN N (linePt τ)).re

/-- **Reality + amplitude of the carrier on the line.** `conj(w)·gN(½+iτ) = 2·Re(conj(w)·D)`, a real
number: the carrier is a unimodular phase times the real Hardy amplitude `H_N(τ) = 2 Re(conj(w)·D)`. -/
theorem conj_hardyPhase_mul_gN_eq (N : ℕ) (τ : ℝ) :
    (starRingEnd ℂ) (hardyPhase τ) * gN N (linePt τ)
      = ((2 * ((starRingEnd ℂ) (hardyPhase τ) * dirichletPoly N (linePt τ)).re : ℝ) : ℂ) := by
  set w := hardyPhase τ with hw
  set D := dirichletPoly N (linePt τ) with hD
  have hcw : (starRingEnd ℂ) w * w = 1 := conj_hardyPhase_mul_self τ
  have hw2 : w * w = zetaChi (linePt τ) := hardyPhase_sq τ
  have key : (starRingEnd ℂ) w * gN N (linePt τ)
      = ((starRingEnd ℂ) w * D) + (starRingEnd ℂ) ((starRingEnd ℂ) w * D) := by
    rw [gN_line_conjForm, ← hw2]
    rw [map_mul, Complex.conj_conj]
    ring_nf
    linear_combination ((starRingEnd ℂ) D * w) * hcw
  rw [key, Complex.add_conj]

/-- **The carrier modulus is the Hardy amplitude.** `‖gN(½+iτ)‖ = |H_N(τ)|`. In particular the
on-line zeros of `gN` are exactly the zeros of the real Hardy carrier `H_N`; continuity of an
oriented sign representative is supplied downstream by the normalized Gamma phase. -/
theorem norm_gN_line_eq_abs_hardyCarrier (N : ℕ) (τ : ℝ) :
    ‖gN N (linePt τ)‖ = |hardyCarrier N τ| := by
  change ‖gN N (linePt τ)‖ =
    |phaseHalvedAmplitude (hardyPhase τ) (gN N (linePt τ))|
  exact (gN_line_isPhaseReflected N τ).norm_eq_abs_amplitude (hardyPhase_isUnitary τ)

theorem gN_line_eq_zero_iff (N : ℕ) (τ : ℝ) :
    gN N (linePt τ) = 0 ↔ hardyCarrier N τ = 0 := by
  change gN N (linePt τ) = 0 ↔
    phaseHalvedAmplitude (hardyPhase τ) (gN N (linePt τ)) = 0
  exact (gN_line_isPhaseReflected N τ).eq_zero_iff_amplitude_eq_zero
    (hardyPhase_isUnitary τ)

end RHTower


namespace RHTower

/-- Squaring removes the harmless Hardy-phase sign ambiguity: the square of the real Hardy
amplitude is the squared norm of the critical-line finite carrier. -/
theorem hardyCarrier_sq_eq_norm_gN_line_sq (N : ℕ) (τ : ℝ) :
    (hardyCarrier N τ) ^ 2 = ‖gN N (linePt τ)‖ ^ 2 := by
  calc
    (hardyCarrier N τ) ^ 2 = |hardyCarrier N τ| ^ 2 := by rw [sq_abs]
    _ = ‖gN N (linePt τ)‖ ^ 2 := by rw [← norm_gN_line_eq_abs_hardyCarrier]

/-- The concrete finite carrier is differentiable along the whole critical line. -/
theorem differentiable_gN_line (N : ℕ) :
    Differentiable ℝ fun τ : ℝ => gN N (linePt τ) := by
  intro τ
  have h1 : DifferentiableAt ℝ (gN N) (linePt τ) := by
    apply (gN_analyticAt (N := N) ?_).differentiableAt.restrictScalars ℝ
    have hre : (1 - linePt τ).re = 1 / 2 := by
      unfold linePt
      simp
      norm_num
    exact Gammaℝ_ne_zero_of_re_pos (by rw [hre]; norm_num)
  have hline : HasDerivAt linePt I τ := by
    unfold linePt
    simpa using
      (((Complex.ofRealCLM.hasDerivAt (x := τ)).mul_const I).const_add
        (((1 / 2 : ℝ) : ℂ)))
  exact h1.comp τ hline.differentiableAt

/-- The concrete finite carrier is continuous along the critical line. -/
theorem continuous_gN_line (N : ℕ) :
    Continuous fun τ : ℝ => gN N (linePt τ) :=
  (differentiable_gN_line N).continuous

/-- The squared Hardy amplitude is continuous, even though the chosen square-root phase itself may
jump by sign. -/
theorem continuous_hardyCarrier_sq (N : ℕ) :
    Continuous fun τ : ℝ => (hardyCarrier N τ) ^ 2 := by
  have hcont : Continuous fun τ : ℝ => ‖gN N (linePt τ)‖ ^ 2 :=
    (continuous_gN_line N).norm.pow 2
  have heq : (fun τ : ℝ => (hardyCarrier N τ) ^ 2)
      = fun τ : ℝ => ‖gN N (linePt τ)‖ ^ 2 := by
    funext τ
    exact hardyCarrier_sq_eq_norm_gN_line_sq N τ
  rw [heq]
  exact hcont

/-- The squared Hardy amplitude is interval-integrable on every finite window. -/
theorem intervalIntegrable_hardyCarrier_sq (N : ℕ) (T U : ℝ) :
    IntervalIntegrable (fun τ : ℝ => (hardyCarrier N τ) ^ 2)
      MeasureTheory.volume T (T + U) := by
  exact (continuous_hardyCarrier_sq N).intervalIntegrable T (T + U)

end RHTower

namespace RHTower

/-- Real expansion of the norm square of a sum in `Complex`. -/
theorem norm_add_sq_complex (u v : ℂ) :
    ‖u + v‖ ^ 2 = ‖u‖ ^ 2 + ‖v‖ ^ 2 + 2 * ((starRingEnd ℂ) u * v).re := by
  have h : ∀ z : ℂ, ‖z‖ ^ 2 = (z * (starRingEnd ℂ) z).re := by
    intro z
    rw [Complex.mul_conj']
    rw [show ((‖z‖ : ℂ)) ^ 2 = ((‖z‖ ^ 2 : ℝ) : ℂ) by push_cast; ring]
    rw [Complex.ofReal_re]
  rw [h, h, h]
  have hexpand : (u + v) * (starRingEnd ℂ) (u + v)
      = u * (starRingEnd ℂ) u + v * (starRingEnd ℂ) v
        + ((starRingEnd ℂ) u * v
          + (starRingEnd ℂ) ((starRingEnd ℂ) u * v)) := by
    rw [map_add, map_mul, Complex.conj_conj]
    ring
  rw [hexpand]
  simp only [Complex.add_re, Complex.conj_re]
  ring

/-- Exact finite functional-equation interference expansion of the line carrier norm. -/
theorem norm_gN_line_sq_eq_dirichlet_cross (N : ℕ) (τ : ℝ) :
    ‖gN N (linePt τ)‖ ^ 2 =
      2 * ‖dirichletPoly N (linePt τ)‖ ^ 2
        + 2 * (zetaChi (linePt τ)
          * ((starRingEnd ℂ) (dirichletPoly N (linePt τ))) ^ 2).re := by
  set D := dirichletPoly N (linePt τ)
  set χ := zetaChi (linePt τ)
  have hχnorm : ‖χ‖ = 1 := by
    simpa [χ] using norm_zetaChi_line τ
  rw [gN_line_conjForm]
  change ‖D + χ * (starRingEnd ℂ) D‖ ^ 2 =
    2 * ‖D‖ ^ 2 + 2 * (χ * ((starRingEnd ℂ) D) ^ 2).re
  rw [norm_add_sq_complex]
  have hvnorm : ‖χ * (starRingEnd ℂ) D‖ ^ 2 = ‖D‖ ^ 2 := by
    rw [norm_mul, Complex.norm_conj, hχnorm, one_mul]
  rw [hvnorm]
  have hcross : ((starRingEnd ℂ) D * (χ * (starRingEnd ℂ) D)).re =
      (χ * ((starRingEnd ℂ) D) ^ 2).re := by
    ring_nf
  rw [hcross]
  ring

end RHTower

namespace RHTower

/-- The functional-equation interference density in the split line norm is continuous. -/
theorem continuous_gN_line_crossTerm (N : ℕ) :
    Continuous fun τ : ℝ =>
      2 * (zetaChi (linePt τ)
        * ((starRingEnd ℂ) (dirichletPoly N (linePt τ))) ^ 2).re := by
  have hline : Continuous linePt := by
    unfold linePt
    fun_prop
  have hDline : Continuous fun τ : ℝ => dirichletPoly N (linePt τ) := by
    exact (dirichletPoly_differentiable N).continuous.comp hline
  have hmainCont : Continuous fun τ : ℝ => 2 * ‖dirichletPoly N (linePt τ)‖ ^ 2 := by
    exact ((hDline.norm.pow 2).const_mul 2)
  have hgnCont : Continuous fun τ : ℝ => ‖gN N (linePt τ)‖ ^ 2 :=
    (continuous_gN_line N).norm.pow 2
  have heq : (fun τ : ℝ =>
      2 * (zetaChi (linePt τ)
        * ((starRingEnd ℂ) (dirichletPoly N (linePt τ))) ^ 2).re)
      = fun τ : ℝ => ‖gN N (linePt τ)‖ ^ 2
        - 2 * ‖dirichletPoly N (linePt τ)‖ ^ 2 := by
    funext τ
    rw [norm_gN_line_sq_eq_dirichlet_cross N τ]
    ring
  rw [heq]
  exact hgnCont.sub hmainCont

end RHTower

namespace RHTower

/-- Pointwise lower bound for the split FE-interference term from a norm-square bound on `D_N`. -/
theorem gN_line_crossTerm_lower_bound_of_dirichlet_norm_sq_le
    (N : ℕ) (τ : ℝ) {Dsup : ℝ}
    (hDsup : ‖dirichletPoly N (linePt τ)‖ ^ 2 ≤ Dsup) :
    -(2 * Dsup) ≤ 2 * (zetaChi (linePt τ)
      * ((starRingEnd ℂ) (dirichletPoly N (linePt τ))) ^ 2).re := by
  set D := dirichletPoly N (linePt τ)
  set χ := zetaChi (linePt τ)
  let z : ℂ := χ * ((starRingEnd ℂ) D) ^ 2
  have hz_norm : ‖z‖ = ‖D‖ ^ 2 := by
    dsimp [z]
    rw [norm_mul, norm_zetaChi_line, norm_pow, Complex.norm_conj, one_mul]
  have hz_re : -‖D‖ ^ 2 ≤ z.re := by
    have hre_abs : |z.re| ≤ ‖z‖ := Complex.abs_re_le_norm z
    have hlo : -‖z‖ ≤ z.re := (abs_le.mp hre_abs).1
    rwa [hz_norm] at hlo
  change -(2 * Dsup) ≤ 2 * z.re
  nlinarith

end RHTower

namespace RHTower

/-- Pointwise FE-interference loss from a scalar norm bound on `D_N(1/2+iτ)`. -/
theorem gN_line_crossTerm_lower_bound_of_dirichlet_norm_le
    (N : ℕ) (τ : ℝ) {Dnorm : ℝ}
    (hDnorm : ‖dirichletPoly N (linePt τ)‖ ≤ Dnorm) :
    -(2 * Dnorm ^ 2) ≤ 2 * (zetaChi (linePt τ)
      * ((starRingEnd ℂ) (dirichletPoly N (linePt τ))) ^ 2).re := by
  apply gN_line_crossTerm_lower_bound_of_dirichlet_norm_sq_le (N := N) (τ := τ)
    (Dsup := Dnorm ^ 2)
  exact pow_le_pow_left₀ (norm_nonneg _) hDnorm 2

end RHTower

namespace RHTower

/-- The Hardy-phase quadrature component of the one-sided Dirichlet carrier.  The Hardy carrier is
`2 * Re(conj(w) * D_N)`, while this scalar is `Im(conj(w) * D_N)`; it is the line component not seen
by the symmetrized carrier amplitude. -/
noncomputable def hardyOrthogonalCarrier (N : ℕ) (τ : ℝ) : ℝ :=
  ((starRingEnd ℂ) (hardyPhase τ) * dirichletPoly N (linePt τ)).im

/-- Exact FE-interference decomposition in Hardy phase coordinates.  The negative part of the split
cross term is governed by the quadrature component of `conj(w) * D_N`, not by the full Dirichlet norm. -/
theorem gN_line_crossTerm_eq_hardy_components (N : ℕ) (τ : ℝ) :
    2 * (zetaChi (linePt τ)
      * ((starRingEnd ℂ) (dirichletPoly N (linePt τ))) ^ 2).re
      = (hardyCarrier N τ) ^ 2 / 2 - 2 * (hardyOrthogonalCarrier N τ) ^ 2 := by
  set w := hardyPhase τ with hw
  set D := dirichletPoly N (linePt τ) with hD
  set A : ℂ := (starRingEnd ℂ) w * D with hA
  have hcw : (starRingEnd ℂ) w * w = 1 := by
    simpa [hw] using conj_hardyPhase_mul_self τ
  have hwc : w * (starRingEnd ℂ) w = 1 := by
    rw [mul_comm]
    exact hcw
  have hD_eq : D = w * A := by
    rw [hA, ← mul_assoc, hwc, one_mul]
  have hconjD : (starRingEnd ℂ) D = (starRingEnd ℂ) w * (starRingEnd ℂ) A := by
    rw [hD_eq, map_mul]
  have hχA : zetaChi (linePt τ) * ((starRingEnd ℂ) D) ^ 2 = ((starRingEnd ℂ) A) ^ 2 := by
    calc
      zetaChi (linePt τ) * ((starRingEnd ℂ) D) ^ 2
          = (w * w) * (((starRingEnd ℂ) w * (starRingEnd ℂ) A) ^ 2) := by
              rw [← hardyPhase_sq τ]
              rw [← hw, hconjD]
      _ = (w * (starRingEnd ℂ) w) ^ 2 * ((starRingEnd ℂ) A) ^ 2 := by ring
      _ = ((starRingEnd ℂ) A) ^ 2 := by rw [hwc]; ring
  have hAeq : (starRingEnd ℂ) (hardyPhase τ) * dirichletPoly N (linePt τ) = A := by
    rw [← hw, ← hD, hA]
  have hHC : hardyCarrier N τ = 2 * A.re := by
    rw [hardyCarrier]
    rw [conj_hardyPhase_mul_gN_eq N τ]
    rw [hAeq]
    simp
  have hO : hardyOrthogonalCarrier N τ = A.im := by
    simp [hardyOrthogonalCarrier, hAeq]
  have hre : (((starRingEnd ℂ) A) ^ 2).re = A.re ^ 2 - A.im ^ 2 := by
    simp [sq, Complex.mul_re]
  rw [hD, hχA, hre, hHC, hO]
  ring

/-- Pointwise FE-interference loss from a scalar envelope on the Hardy-phase quadrature component. -/
theorem gN_line_crossTerm_lower_bound_of_hardyOrthogonal_le
    (N : ℕ) (τ : ℝ) {Ysup : ℝ}
    (hY : |hardyOrthogonalCarrier N τ| ≤ Ysup) :
    -(2 * Ysup ^ 2) ≤ 2 * (zetaChi (linePt τ)
      * ((starRingEnd ℂ) (dirichletPoly N (linePt τ))) ^ 2).re := by
  have hsq_abs : |hardyOrthogonalCarrier N τ| ^ 2 ≤ Ysup ^ 2 := by
    exact pow_le_pow_left₀ (abs_nonneg _) hY 2
  have hsq : (hardyOrthogonalCarrier N τ) ^ 2 ≤ Ysup ^ 2 := by
    rwa [sq_abs] at hsq_abs
  have hmain0 : 0 ≤ (hardyCarrier N τ) ^ 2 / 2 := by positivity
  rw [gN_line_crossTerm_eq_hardy_components]
  nlinarith

end RHTower

namespace RHTower

/-- The one-sided critical-line Dirichlet carrier splits into the in-phase Hardy amplitude and the
quadrature component after rotating by the Hardy phase. -/
theorem dirichlet_norm_sq_eq_hardy_components (N : ℕ) (τ : ℝ) :
    ‖dirichletPoly N (linePt τ)‖ ^ 2 =
      (hardyCarrier N τ) ^ 2 / 4 + (hardyOrthogonalCarrier N τ) ^ 2 := by
  set w := hardyPhase τ with hw
  set D := dirichletPoly N (linePt τ) with hD
  set A : ℂ := (starRingEnd ℂ) w * D with hA
  have hAeq : (starRingEnd ℂ) (hardyPhase τ) * dirichletPoly N (linePt τ) = A := by
    rw [← hw, ← hD, hA]
  have hHC : hardyCarrier N τ = 2 * A.re := by
    rw [hardyCarrier]
    rw [conj_hardyPhase_mul_gN_eq N τ]
    rw [hAeq]
    simp
  have hO : hardyOrthogonalCarrier N τ = A.im := by
    simp [hardyOrthogonalCarrier, hAeq]
  have hnorm : ‖D‖ = ‖A‖ := by
    rw [hA, norm_mul, Complex.norm_conj, norm_hardyPhase, one_mul]
  have hA_norm : ‖A‖ ^ 2 = A.re ^ 2 + A.im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    ring
  calc
    ‖dirichletPoly N (linePt τ)‖ ^ 2 = ‖D‖ ^ 2 := by rw [hD]
    _ = ‖A‖ ^ 2 := by rw [hnorm]
    _ = A.re ^ 2 + A.im ^ 2 := hA_norm
    _ = (hardyCarrier N τ) ^ 2 / 4 + (hardyOrthogonalCarrier N τ) ^ 2 := by
        rw [hHC, hO]
        ring

/-- The banked Dirichlet second-moment density in Hardy phase coordinates. -/
theorem dirichlet_main_eq_hardy_components (N : ℕ) (τ : ℝ) :
    2 * ‖dirichletPoly N (linePt τ)‖ ^ 2 =
      (hardyCarrier N τ) ^ 2 / 2 + 2 * (hardyOrthogonalCarrier N τ) ^ 2 := by
  rw [dirichlet_norm_sq_eq_hardy_components]
  ring

end RHTower

namespace RHTower

/-- The Hardy-phase quadrature component is pointwise bounded by the one-sided critical-line carrier
norm. -/
theorem hardyOrthogonalCarrier_sq_le_dirichlet_norm_sq (N : ℕ) (τ : ℝ) :
    (hardyOrthogonalCarrier N τ) ^ 2 ≤ ‖dirichletPoly N (linePt τ)‖ ^ 2 := by
  rw [dirichlet_norm_sq_eq_hardy_components]
  have hnonneg : 0 ≤ (hardyCarrier N τ) ^ 2 / 4 := by positivity
  nlinarith

end RHTower
