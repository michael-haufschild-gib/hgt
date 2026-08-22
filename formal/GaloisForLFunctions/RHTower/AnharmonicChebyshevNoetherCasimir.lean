import GaloisForLFunctions.RHTower.AnharmonicChebyshevMovingFiber
import GaloisForLFunctions.RHTower.SuzukiCoalescingXiCayleyTarget
import GaloisForLFunctions.RHTower.SuzukiV2CharacteristicTarget

/-!
# Strict Xi information loss on a moving anharmonic fiber

The cyclic three-sheet current has an exact center-of-mass/relative-energy decomposition: its
total squared amplitude is the squared descended trace plus the Hermitian Casimir of the standard
sector.  This is the finite Jacobi-coordinate form of the Noether split between a quotient-visible
current and a fibre current.

For the actual completed Xi current the fibre term is not merely nonnegative.  On every real scan
sheet `s > 2`, positivity of the centered Xi logarithmic derivative and the functional equation give
the sign pattern `(+,+,-)` on the three cyclic sheets.  Division by the positive quotient Jacobian
preserves those signs.  Consequently the standard-sector Casimir is strictly positive everywhere
on that sheet: scalar quotient descent provably discards nonzero Xi information at every scan point.

This is unconditional and does not imply RH.  It rules out collapse of the moving standard sector;
the remaining frontier is a source-level law controlling that sector rather than its positivity.
-/

open Complex Real Filter Topology

namespace RHTower

noncomputable section

/-- Three-body/Jacobi Parseval law: total energy is visible trace energy plus fibre Casimir. -/
theorem three_mul_anharmonicOrbit_totalEnergy_eq_trace_add_casimir (a b c : ℂ) :
    3 * (‖a‖ ^ 2 + ‖b‖ ^ 2 + ‖c‖ ^ 2) =
      ‖a + b + c‖ ^ 2 + anharmonicOrbitHermitianEnergy a b c := by
  simp only [anharmonicOrbitHermitianEnergy, Complex.sq_norm, Complex.normSq_apply,
    Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im]
  ring

/-- Xi logarithmic derivative has positive real part at every real point right of the centre. -/
theorem logDeriv_xi_ofReal_re_pos {x : ℝ} (hx : 1 / 2 < x) :
    0 < (logDeriv xi (x : ℂ)).re := by
  have hw : 0 < x - 1 / 2 := by linarith
  have h := xiRealLogDeriv_pos hw
  have harg : (1 / 2 : ℂ) + ((x - 1 / 2 : ℝ) : ℂ) = (x : ℂ) := by
    push_cast
    ring
  simpa only [xiRealLogDeriv, harg] using h

/-- Functional-equation reflection gives the opposite sign left of the centre. -/
theorem logDeriv_xi_ofReal_re_neg {x : ℝ} (hx : x < 1 / 2) :
    (logDeriv xi (x : ℂ)).re < 0 := by
  have hpos : 0 < (logDeriv xi ((1 - x : ℝ) : ℂ)).re :=
    logDeriv_xi_ofReal_re_pos (by linarith)
  have hreflect := re_logDeriv_xi_reflect_line (1 - x) 0
  norm_num only [ofReal_zero, zero_mul, add_zero] at hreflect
  have hleft : ((1 - (1 - x) : ℝ) : ℂ) = (x : ℂ) := by
    push_cast
    ring
  rw [hleft] at hreflect
  linarith

/-- Real part of the invariant-coordinate current is ordinary Xi response divided by the positive
real quotient Jacobian. -/
theorem chebyshevXiQLogDeriv_ofReal_re (x : ℝ) :
    (chebyshevXiQLogDeriv (x : ℂ)).re =
      (logDeriv xi (x : ℂ)).re / chebyshevAnharmonicQPrimeReal x := by
  rw [chebyshevXiQLogDeriv, chebyshevAnharmonicQPrime_ofReal]
  have hq : chebyshevAnharmonicQPrimeReal x ≠ 0 :=
    ne_of_gt (chebyshevAnharmonicQPrimeReal_pos x)
  simp only [div_eq_mul_inv, Complex.mul_re, Complex.inv_re, Complex.inv_im,
    Complex.ofReal_re, Complex.ofReal_im, neg_zero,
    Complex.normSq_ofReal]
  field_simp [hq]
  ring

/-- Positive side of the q-covariant Xi current. -/
theorem chebyshevXiQLogDeriv_ofReal_re_pos {x : ℝ} (hx : 1 / 2 < x) :
    0 < (chebyshevXiQLogDeriv (x : ℂ)).re := by
  rw [chebyshevXiQLogDeriv_ofReal_re]
  exact div_pos (logDeriv_xi_ofReal_re_pos hx)
    (chebyshevAnharmonicQPrimeReal_pos x)

/-- Negative side of the q-covariant Xi current. -/
theorem chebyshevXiQLogDeriv_ofReal_re_neg {x : ℝ} (hx : x < 1 / 2) :
    (chebyshevXiQLogDeriv (x : ℂ)).re < 0 := by
  rw [chebyshevXiQLogDeriv_ofReal_re]
  exact div_neg_of_neg_of_pos (logDeriv_xi_ofReal_re_neg hx)
    (chebyshevAnharmonicQPrimeReal_pos x)

/-- The actual three-sheet q-current has sign pattern `(+,+,-)` on every real scan sheet. -/
theorem chebyshevXiQLogDeriv_realOrbit_signs {s : ℝ} (hs : 2 < s) :
    0 < (chebyshevXiQLogDeriv (s : ℂ)).re ∧
      0 < (chebyshevXiQLogDeriv (chebyshevAnharmonicW (s : ℂ))).re ∧
      (chebyshevXiQLogDeriv (chebyshevAnharmonicWTwo (s : ℂ))).re < 0 := by
  obtain ⟨hwlo, hwhi, hw2lo, hw2hi⟩ := chebyshevAnharmonic_realOrbit_ranges hs
  have hwCast : chebyshevAnharmonicW (s : ℂ) = (((s - 1) / s : ℝ) : ℂ) := by
    simp only [chebyshevAnharmonicW]
    norm_cast
  have hw2Cast : chebyshevAnharmonicWTwo (s : ℂ) = ((1 / (1 - s) : ℝ) : ℂ) := by
    simp only [chebyshevAnharmonicWTwo]
    norm_cast
  refine ⟨chebyshevXiQLogDeriv_ofReal_re_pos (by linarith), ?_, ?_⟩
  · rw [hwCast]
    exact chebyshevXiQLogDeriv_ofReal_re_pos hwlo
  · rw [hw2Cast]
    exact chebyshevXiQLogDeriv_ofReal_re_neg (by linarith)

/-- **Strict moving-fibre information law.**  Scalar `q` descent discards a nonzero Xi standard
sector at every real Chebyshev scan point beyond `2`. -/
theorem chebyshevXiQOrientationEnergy_pos_of_two_lt {s : ℝ} (hs : 2 < s) :
    0 < chebyshevXiQOrientationEnergy (s : ℂ) := by
  obtain ⟨hfirst, _, hthird⟩ := chebyshevXiQLogDeriv_realOrbit_signs hs
  have hne : chebyshevXiQOrientationEnergy (s : ℂ) ≠ 0 := by
    intro hzero
    have heq := (chebyshevXiQOrientationEnergy_eq_zero_iff (s : ℂ)).mp hzero
    have hac := heq.1.trans heq.2
    have hre := congrArg Complex.re hac
    linarith
  exact lt_of_le_of_ne (chebyshevXiQOrientationEnergy_nonneg (s : ℂ)) hne.symm

/-- Specialized Noether/Jacobi split for the actual q-covariant Xi orbit current. -/
theorem three_mul_chebyshevXiQ_totalEnergy_eq_trace_add_orientationEnergy (s : ℂ) :
    3 * (‖chebyshevXiQLogDeriv s‖ ^ 2 +
        ‖chebyshevXiQLogDeriv (chebyshevAnharmonicW s)‖ ^ 2 +
        ‖chebyshevXiQLogDeriv (chebyshevAnharmonicWTwo s)‖ ^ 2) =
      ‖chebyshevXiQLogDeriv s +
          chebyshevXiQLogDeriv (chebyshevAnharmonicW s) +
          chebyshevXiQLogDeriv (chebyshevAnharmonicWTwo s)‖ ^ 2 +
        chebyshevXiQOrientationEnergy s :=
  three_mul_anharmonicOrbit_totalEnergy_eq_trace_add_casimir _ _ _

/-! ## Cofinal one-sheet concentration -/

/-- Real q-covariant Xi current. -/
def chebyshevXiQRealCurrent (x : ℝ) : ℝ :=
  (chebyshevXiQLogDeriv (x : ℂ)).re

theorem chebyshevXiQRealCurrent_eq (x : ℝ) :
    chebyshevXiQRealCurrent x =
      xiRayLogDeriv x / chebyshevAnharmonicQPrimeReal x := by
  rw [chebyshevXiQRealCurrent, chebyshevXiQLogDeriv_ofReal_re,
    xiRayLogDeriv, xiLogDeriv, logDeriv_apply]

/-- Quotient Jacobian tends to one on the exterior real sheet. -/
theorem tendsto_chebyshevAnharmonicQPrimeReal_atTop :
    Tendsto chebyshevAnharmonicQPrimeReal atTop (nhds 1) := by
  have hinv : Tendsto (fun x : ℝ => x⁻¹) atTop (nhds 0) := tendsto_inv_atTop_zero
  have hshift : Tendsto (fun x : ℝ => (x - 1)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp
      (tendsto_atTop_add_const_right atTop (-1) tendsto_id)
  have hconst : Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (nhds 1) := tendsto_const_nhds
  have h := (hconst.add (hinv.pow 2)).add (hshift.pow 2)
  change Tendsto (fun x : ℝ => 1 + 1 / x ^ 2 + 1 / (x - 1) ^ 2) atTop (nhds 1)
  simpa [one_div, inv_pow] using h

/-- Cyclic quotient Jacobian in real coordinates. -/
theorem chebyshevAnharmonicQPrimeReal_w
    {s : ℝ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    chebyshevAnharmonicQPrimeReal ((s - 1) / s) =
      chebyshevAnharmonicQPrimeReal s * s ^ 2 := by
  simp only [chebyshevAnharmonicQPrimeReal]
  field_simp [hs0, hs1]
  ring

/-- Second cyclic quotient Jacobian in real coordinates. -/
theorem chebyshevAnharmonicQPrimeReal_wTwo
    {s : ℝ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    chebyshevAnharmonicQPrimeReal (1 / (1 - s)) =
      chebyshevAnharmonicQPrimeReal s * (1 - s) ^ 2 := by
  simp only [chebyshevAnharmonicQPrimeReal]
  field_simp [hs0, hs1]
  ring

theorem chebyshevXiQRealCurrent_w
    {s : ℝ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    chebyshevXiQRealCurrent ((s - 1) / s) =
      xiRayLogDeriv ((s - 1) / s) /
        (chebyshevAnharmonicQPrimeReal s * s ^ 2) := by
  rw [chebyshevXiQRealCurrent_eq, chebyshevAnharmonicQPrimeReal_w hs0 hs1]

theorem chebyshevXiQRealCurrent_wTwo
    {s : ℝ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    chebyshevXiQRealCurrent (1 / (1 - s)) =
      xiRayLogDeriv (1 / (1 - s)) /
        (chebyshevAnharmonicQPrimeReal s * (1 - s) ^ 2) := by
  rw [chebyshevXiQRealCurrent_eq, chebyshevAnharmonicQPrimeReal_wTwo hs0 hs1]

theorem tendsto_chebyshevAnharmonicWReal_atTop :
    Tendsto (fun s : ℝ => (s - 1) / s) atTop (nhds 1) := by
  have hinv : Tendsto (fun s : ℝ => s⁻¹) atTop (nhds 0) := tendsto_inv_atTop_zero
  have h := (tendsto_const_nhds.sub hinv :
    Tendsto (fun s : ℝ => 1 - s⁻¹) atTop (nhds (1 - 0)))
  have h' : Tendsto (fun s : ℝ => (s - 1) / s) atTop (nhds (1 - 0)) := by
    refine h.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with s hs
    field_simp [hs.ne']
  simpa using h'

theorem tendsto_chebyshevAnharmonicWTwoReal_atTop :
    Tendsto (fun s : ℝ => 1 / (1 - s)) atTop (nhds 0) := by
  have hshift : Tendsto (fun s : ℝ => (s - 1)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp
      (tendsto_atTop_add_const_right atTop (-1) tendsto_id)
  have h := hshift.neg
  have h' : Tendsto (fun s : ℝ => 1 / (1 - s)) atTop (nhds (-0)) := by
    refine h.congr' ?_
    filter_upwards with s
    rw [show 1 - s = -(s - 1) by ring, one_div, inv_neg]
  simpa using h'

theorem tendsto_inv_chebyshevQPrime_mul_sq_atTop :
    Tendsto (fun s : ℝ => 1 /
      (chebyshevAnharmonicQPrimeReal s * s ^ 2)) atTop (nhds 0) := by
  have hq := tendsto_chebyshevAnharmonicQPrimeReal_atTop.inv₀ one_ne_zero
  have hinv : Tendsto (fun s : ℝ => s⁻¹) atTop (nhds 0) := tendsto_inv_atTop_zero
  have h := hq.mul (hinv.pow 2)
  simpa [one_div, mul_inv, inv_pow, mul_comm] using h

theorem tendsto_inv_chebyshevQPrime_mul_one_sub_sq_atTop :
    Tendsto (fun s : ℝ => 1 /
      (chebyshevAnharmonicQPrimeReal s * (1 - s) ^ 2)) atTop (nhds 0) := by
  have hq := tendsto_chebyshevAnharmonicQPrimeReal_atTop.inv₀ one_ne_zero
  have hinv := tendsto_chebyshevAnharmonicWTwoReal_atTop
  have h := hq.mul (hinv.pow 2)
  simpa [one_div, mul_inv, inv_pow, mul_comm] using h

/-- Exterior q-current diverges: quotient Jacobian becomes asymptotically transparent. -/
theorem tendsto_chebyshevXiQRealCurrent_atTop :
    Tendsto chebyshevXiQRealCurrent atTop atTop := by
  apply tendsto_atTop.2
  intro R
  have hL := tendsto_xiRayLogDeriv_atTop.eventually_gt_atTop (2 * max R 1)
  have hq := tendsto_chebyshevAnharmonicQPrimeReal_atTop.eventually
    (eventually_lt_nhds (by norm_num : (1 : ℝ) < 2))
  filter_upwards [hL, hq] with s hLs hqs
  rw [chebyshevXiQRealCurrent_eq]
  have hqpos := chebyshevAnharmonicQPrimeReal_pos s
  rw [le_div_iff₀ hqpos]
  have hmaxpos : 0 < max R 1 := lt_of_lt_of_le zero_lt_one (le_max_right R 1)
  exact (calc
    R * chebyshevAnharmonicQPrimeReal s ≤
        max R 1 * chebyshevAnharmonicQPrimeReal s :=
      mul_le_mul_of_nonneg_right (le_max_left R 1) hqpos.le
    _ < max R 1 * 2 := mul_lt_mul_of_pos_left hqs hmaxpos
    _ = 2 * max R 1 := by ring
    _ < xiRayLogDeriv s := hLs).le

/-- First return-sheet q-current vanishes cofinally. -/
theorem tendsto_chebyshevXiQRealCurrent_w_atTop :
    Tendsto (fun s : ℝ => chebyshevXiQRealCurrent ((s - 1) / s))
      atTop (nhds 0) := by
  have hnum : Tendsto (fun s : ℝ => xiRayLogDeriv ((s - 1) / s))
      atTop (nhds (xiRayLogDeriv 1)) :=
    (contDiff_xiRayLogDeriv 0).continuous.continuousAt.tendsto.comp
      tendsto_chebyshevAnharmonicWReal_atTop
  have hprod := hnum.mul tendsto_inv_chebyshevQPrime_mul_sq_atTop
  simp only [mul_zero] at hprod
  refine hprod.congr' ?_
  filter_upwards [eventually_gt_atTop (2 : ℝ)] with s hs
  have hs0 : s ≠ 0 := by linarith
  have hs1 : s ≠ 1 := by linarith
  rw [chebyshevXiQRealCurrent_w hs0 hs1]
  simp only [div_eq_mul_inv, one_mul]

/-- Second return-sheet q-current vanishes cofinally. -/
theorem tendsto_chebyshevXiQRealCurrent_wTwo_atTop :
    Tendsto (fun s : ℝ => chebyshevXiQRealCurrent (1 / (1 - s)))
      atTop (nhds 0) := by
  have hnum : Tendsto (fun s : ℝ => xiRayLogDeriv (1 / (1 - s)))
      atTop (nhds (xiRayLogDeriv 0)) :=
    (contDiff_xiRayLogDeriv 0).continuous.continuousAt.tendsto.comp
      tendsto_chebyshevAnharmonicWTwoReal_atTop
  have hprod := hnum.mul tendsto_inv_chebyshevQPrime_mul_one_sub_sq_atTop
  simp only [mul_zero] at hprod
  refine hprod.congr' ?_
  filter_upwards [eventually_gt_atTop (2 : ℝ)] with s hs
  have hs0 : s ≠ 0 := by linarith
  have hs1 : s ≠ 1 := by linarith
  rw [chebyshevXiQRealCurrent_wTwo hs0 hs1]
  simp only [div_eq_mul_inv, one_mul]

/-- **Cofinal one-sheet concentration.**  Exterior q-current diverges while both cyclic return
currents vanish. -/
theorem chebyshevXiQRealCurrent_cofinal_concentration :
    Tendsto chebyshevXiQRealCurrent atTop atTop ∧
      Tendsto (fun s : ℝ => chebyshevXiQRealCurrent ((s - 1) / s)) atTop (nhds 0) ∧
      Tendsto (fun s : ℝ => chebyshevXiQRealCurrent (1 / (1 - s))) atTop (nhds 0) :=
  ⟨tendsto_chebyshevXiQRealCurrent_atTop,
    tendsto_chebyshevXiQRealCurrent_w_atTop,
    tendsto_chebyshevXiQRealCurrent_wTwo_atTop⟩

/-! ## Universal cofinal Casimir ratio -/

/-- Real Jacobi energy of the three q-current components. -/
def chebyshevXiQRealOrientationEnergy (s : ℝ) : ℝ :=
  (chebyshevXiQRealCurrent s - chebyshevXiQRealCurrent ((s - 1) / s)) ^ 2 +
    (chebyshevXiQRealCurrent ((s - 1) / s) -
      chebyshevXiQRealCurrent (1 / (1 - s))) ^ 2 +
    (chebyshevXiQRealCurrent (1 / (1 - s)) - chebyshevXiQRealCurrent s) ^ 2

theorem chebyshevXiQLogDeriv_ofReal_im (x : ℝ) :
    (chebyshevXiQLogDeriv (x : ℂ)).im = 0 := by
  rw [chebyshevXiQLogDeriv, chebyshevAnharmonicQPrime_ofReal]
  simp only [Complex.div_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero]
  rw [logDeriv_xi_ofReal_im]
  simp

/-- Complex Hermitian energy on a real orbit is exactly its real Jacobi energy. -/
theorem chebyshevXiQOrientationEnergy_ofReal_eq_realEnergy (s : ℝ) :
    chebyshevXiQOrientationEnergy (s : ℂ) =
      chebyshevXiQRealOrientationEnergy s := by
  have hwCast : chebyshevAnharmonicW (s : ℂ) = (((s - 1) / s : ℝ) : ℂ) := by
    simp only [chebyshevAnharmonicW]
    norm_cast
  have hw2Cast : chebyshevAnharmonicWTwo (s : ℂ) = ((1 / (1 - s) : ℝ) : ℂ) := by
    simp only [chebyshevAnharmonicWTwo]
    norm_cast
  rw [chebyshevXiQOrientationEnergy, anharmonicOrbitHermitianEnergy, hwCast, hw2Cast]
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    chebyshevXiQLogDeriv_ofReal_im, sub_zero,
    chebyshevXiQRealOrientationEnergy, chebyshevXiQRealCurrent]
  ring

theorem real_threeBodyEnergy_div_outer_sq {a : ℝ} (ha : a ≠ 0) (b c : ℝ) :
    ((a - b) ^ 2 + (b - c) ^ 2 + (c - a) ^ 2) / a ^ 2 =
      (1 - b / a) ^ 2 + (b / a - c / a) ^ 2 + (c / a - 1) ^ 2 := by
  field_simp [ha]

/-- **Universal far-sheet ratio.**  The quotient-invisible Casimir carries asymptotically twice
the squared exterior current. -/
theorem tendsto_chebyshevXiQRealOrientationEnergy_div_outer_sq :
    Tendsto (fun s : ℝ => chebyshevXiQRealOrientationEnergy s /
      chebyshevXiQRealCurrent s ^ 2) atTop (nhds 2) := by
  let a : ℝ → ℝ := chebyshevXiQRealCurrent
  let b : ℝ → ℝ := fun s => chebyshevXiQRealCurrent ((s - 1) / s)
  let c : ℝ → ℝ := fun s => chebyshevXiQRealCurrent (1 / (1 - s))
  have ha : Tendsto a atTop atTop := tendsto_chebyshevXiQRealCurrent_atTop
  have hb : Tendsto b atTop (nhds 0) := tendsto_chebyshevXiQRealCurrent_w_atTop
  have hc : Tendsto c atTop (nhds 0) := tendsto_chebyshevXiQRealCurrent_wTwo_atTop
  have hainv : Tendsto (fun s => (a s)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp ha
  have hba : Tendsto (fun s => b s / a s) atTop (nhds 0) := by
    simpa only [div_eq_mul_inv, zero_mul] using hb.mul hainv
  have hca : Tendsto (fun s => c s / a s) atTop (nhds 0) := by
    simpa only [div_eq_mul_inv, zero_mul] using hc.mul hainv
  have hone : Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (nhds 1) := tendsto_const_nhds
  have hlimit := ((hone.sub hba).pow 2).add ((hba.sub hca).pow 2) |>.add
    ((hca.sub hone).pow 2)
  norm_num at hlimit
  refine hlimit.congr' ?_
  filter_upwards [eventually_gt_atTop (2 : ℝ)] with s hs
  have haPos : 0 < a s := by
    dsimp only [a]
    exact chebyshevXiQLogDeriv_ofReal_re_pos (by linarith)
  have ha0 : a s ≠ 0 := ne_of_gt haPos
  change (1 - b s / a s) ^ 2 + (b s / a s - c s / a s) ^ 2 +
      (c s / a s - 1) ^ 2 = chebyshevXiQRealOrientationEnergy s / a s ^ 2
  rw [chebyshevXiQRealOrientationEnergy]
  exact (real_threeBodyEnergy_div_outer_sq ha0 (b s) (c s)).symm

/-- Same ratio for the actual complex Hermitian orientation energy on the real scan sheet. -/
theorem tendsto_chebyshevXiQOrientationEnergy_ofReal_div_outer_sq :
    Tendsto (fun s : ℝ => chebyshevXiQOrientationEnergy (s : ℂ) /
      chebyshevXiQRealCurrent s ^ 2) atTop (nhds 2) := by
  apply tendsto_chebyshevXiQRealOrientationEnergy_div_outer_sq.congr'
  filter_upwards with s
  rw [chebyshevXiQOrientationEnergy_ofReal_eq_realEnergy]

/-- Quotient-visible real trace of the three cyclic q-current components. -/
def chebyshevXiQRealTrace (s : ℝ) : ℝ :=
  chebyshevXiQRealCurrent s + chebyshevXiQRealCurrent ((s - 1) / s) +
    chebyshevXiQRealCurrent (1 / (1 - s))

theorem chebyshevXiQRealTrace_eq_re_sum (s : ℝ) :
    chebyshevXiQRealTrace s =
      (chebyshevXiQLogDeriv (s : ℂ) +
        chebyshevXiQLogDeriv (chebyshevAnharmonicW (s : ℂ)) +
        chebyshevXiQLogDeriv (chebyshevAnharmonicWTwo (s : ℂ))).re := by
  have hwCast : chebyshevAnharmonicW (s : ℂ) = (((s - 1) / s : ℝ) : ℂ) := by
    simp only [chebyshevAnharmonicW]
    norm_cast
  have hw2Cast : chebyshevAnharmonicWTwo (s : ℂ) = ((1 / (1 - s) : ℝ) : ℂ) := by
    simp only [chebyshevAnharmonicWTwo]
    norm_cast
  rw [chebyshevXiQRealTrace, chebyshevXiQRealCurrent, hwCast, hw2Cast]
  simp only [chebyshevXiQRealCurrent, Complex.add_re]

/-- Real visible trace is the invariant-coordinate logarithmic derivative of the descended cyclic
Xi product. -/
theorem chebyshevXiQRealTrace_eq_re_logDeriv_product {s : ℝ} (hs : 2 < s) :
    chebyshevXiQRealTrace s =
      (logDeriv chebyshevXiCyclicOrbitProduct (s : ℂ) /
        chebyshevAnharmonicQPrime (s : ℂ)).re := by
  rw [chebyshevXiQRealTrace_eq_re_sum]
  exact congrArg Complex.re
    (logDeriv_chebyshevXiCyclicOrbitProduct_div_qPrime_of_two_lt hs).symm

/-- Descended trace is asymptotic to the exterior component. -/
theorem tendsto_chebyshevXiQRealTrace_div_outer :
    Tendsto (fun s : ℝ => chebyshevXiQRealTrace s / chebyshevXiQRealCurrent s)
      atTop (nhds 1) := by
  let a : ℝ → ℝ := chebyshevXiQRealCurrent
  let b : ℝ → ℝ := fun s => chebyshevXiQRealCurrent ((s - 1) / s)
  let c : ℝ → ℝ := fun s => chebyshevXiQRealCurrent (1 / (1 - s))
  have ha : Tendsto a atTop atTop := tendsto_chebyshevXiQRealCurrent_atTop
  have hb : Tendsto b atTop (nhds 0) := tendsto_chebyshevXiQRealCurrent_w_atTop
  have hc : Tendsto c atTop (nhds 0) := tendsto_chebyshevXiQRealCurrent_wTwo_atTop
  have hainv : Tendsto (fun s => (a s)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp ha
  have hba : Tendsto (fun s => b s / a s) atTop (nhds 0) := by
    simpa only [div_eq_mul_inv, zero_mul] using hb.mul hainv
  have hca : Tendsto (fun s => c s / a s) atTop (nhds 0) := by
    simpa only [div_eq_mul_inv, zero_mul] using hc.mul hainv
  have hone : Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (nhds 1) := tendsto_const_nhds
  have hlimit := (hone.add hba).add hca
  simp only [add_zero] at hlimit
  refine hlimit.congr' ?_
  filter_upwards [eventually_gt_atTop (2 : ℝ)] with s hs
  have ha0 : a s ≠ 0 := by
    dsimp only [a]
    exact ne_of_gt (chebyshevXiQLogDeriv_ofReal_re_pos (by linarith))
  change 1 + b s / a s + c s / a s = chebyshevXiQRealTrace s / a s
  rw [chebyshevXiQRealTrace]
  field_simp [ha0]
  ring

/-- **Invariant invisible/visible ratio.**  On the far real sheet, standard-sector Casimir divided
by squared descended trace tends to exactly `2`. -/
theorem tendsto_chebyshevXiQOrientationEnergy_div_trace_sq :
    Tendsto (fun s : ℝ => chebyshevXiQOrientationEnergy (s : ℂ) /
      chebyshevXiQRealTrace s ^ 2) atTop (nhds 2) := by
  have hE := tendsto_chebyshevXiQOrientationEnergy_ofReal_div_outer_sq
  have hT := tendsto_chebyshevXiQRealTrace_div_outer
  have hratio := hE.div (hT.pow 2) (by norm_num : (1 : ℝ) ^ 2 ≠ 0)
  norm_num at hratio
  refine hratio.congr' ?_
  have hTne : ∀ᶠ s : ℝ in atTop,
      chebyshevXiQRealTrace s / chebyshevXiQRealCurrent s ≠ 0 :=
    hT.eventually (eventually_ne_nhds one_ne_zero)
  filter_upwards [eventually_gt_atTop (2 : ℝ), hTne] with s hs htraceRatio
  have houter0 : chebyshevXiQRealCurrent s ≠ 0 :=
    ne_of_gt (chebyshevXiQLogDeriv_ofReal_re_pos (by linarith))
  have htrace0 : chebyshevXiQRealTrace s ≠ 0 := (div_ne_zero_iff.mp htraceRatio).1
  change (chebyshevXiQOrientationEnergy (s : ℂ) / chebyshevXiQRealCurrent s ^ 2) /
      (chebyshevXiQRealTrace s / chebyshevXiQRealCurrent s) ^ 2 =
    chebyshevXiQOrientationEnergy (s : ℂ) / chebyshevXiQRealTrace s ^ 2
  field_simp [houter0, htrace0]

end

end RHTower
