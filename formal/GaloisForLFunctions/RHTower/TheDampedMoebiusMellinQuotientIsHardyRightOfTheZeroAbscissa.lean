import GaloisForLFunctions.RHTower.InvZetaAbscissaSubpolynomial
import GaloisForLFunctions.RHTower.ZetaConvexityBound
import GaloisForLFunctions.RHTower.MellinHardyClasses
import GaloisForLFunctions.RHTower.DeningerZetaLowerBound
import GaloisForLFunctions.RHTower.ZetaZeroAbscissa

/-!
# The damped Möbius Mellin quotient is Hardy right of the zero abscissa

The Mellin transform of the power-damped Möbius Fermi source at damping `ε` is, on its initial
strip, the quotient `(1 − 2^{1−s}) ζ(s) / (s ζ(s+ε))`. This module studies that quotient as a
function on the half-plane `Re s > ½`, written with the entire residue unit `(s − 1)ζ(s)` and the
regular reciprocal `invZeta` so that the pole of `ζ` at `1` and the pole of `ζ(s + ε)` at
`s = 1 − ε` are cleared:

`etaZetaQuotient ε s = etaSlope s · zetaResidueUnit s · invZeta (s + ε) / s`,

where `etaSlope` is the difference quotient of `s ↦ 1 − 2^{1−s}` at `1`, an entire function with
`(s − 1) · etaSlope s = 1 − 2^{1−s}` (`etaSlope_mul_sub`, `etaZetaQuotient_eq`).

Let `Θ = zetaZeroAbscissa`. When `Θ < ½ + ε`:

* `differentiableAt_etaZetaQuotient`: the quotient is holomorphic on `Re s ≥ ½`.
* `exists_norm_etaZetaQuotient_le`: `‖etaZetaQuotient ε s‖ ≤ K (1 + |Im s|)^{−9/16}` on
  `Re s ≥ ½`, from the convexity bound `‖ζ(σ+it)‖ ≤ C t^{(9/8−σ)/2}` (exponent `≤ 5/16` for
  `σ ≥ ½`), the subpolynomial reciprocal-zeta datum `‖invZeta w‖ ≤ K' (2 + |Im w|)^{1/8}` right of
  `Θ + δ`, the trivial bounds right of `9/8` and of `2`, and `|s| ≥ (1 + |Im s|)/4`.
* `isMellinTailHardy_etaZetaQuotient`: the quotient lies in Burnol's class `A^s H²` at aperture
  `1`, i.e. `w ↦ etaZetaQuotient ε (w + ½)` is a Hardy function of the right half-plane with
  line masses bounded by `∫ K² (1 + |ξ|)^{−9/8} dξ`.

By the Paley–Wiener identification (`exists_memLp_of_isMellinTailHardy`) the quotient is therefore
the right Mellin transform of a square-integrable tail datum; identifying that datum with the
inverted Fermi source is the admission of the source below half damping.
-/

open Complex Set Filter Topology MeasureTheory
open GaloisForLFunctions.HTGeometry
open scoped ComplexConjugate

noncomputable section
set_option autoImplicit false

namespace RHTower

open Sieve

/-! ### The pole-clearing eta factor -/

/-- The difference quotient of `s ↦ 1 − 2^{1−s}` at `s = 1`: `(1 − 2^{1−s})/(s − 1)` off `1`,
extended by the derivative `log 2` at `1`. -/
def etaSlope : ℂ → ℂ := dslope (fun s : ℂ => 1 - (2 : ℂ) ^ (1 - s)) 1

theorem differentiable_etaBase : Differentiable ℂ (fun s : ℂ => 1 - (2 : ℂ) ^ (1 - s)) := by
  intro s
  have h : DifferentiableAt ℂ (fun s : ℂ => (2 : ℂ) ^ (1 - s)) s :=
    ((differentiableAt_const _).sub differentiableAt_id).const_cpow (Or.inl (by norm_num))
  exact (differentiableAt_const _).sub h

theorem differentiable_etaSlope : Differentiable ℂ etaSlope := by
  rw [← differentiableOn_univ]
  exact (Complex.differentiableOn_dslope Filter.univ_mem).mpr
    differentiable_etaBase.differentiableOn

/-- `(s − 1) · etaSlope s = 1 − 2^{1−s}`. -/
theorem etaSlope_mul_sub (s : ℂ) : (s - 1) * etaSlope s = 1 - (2 : ℂ) ^ (1 - s) := by
  have h := sub_smul_dslope (fun s : ℂ => 1 - (2 : ℂ) ^ (1 - s)) 1 s
  simpa [etaSlope, smul_eq_mul] using h

/-- `‖1 − 2^{1−s}‖ ≤ 3` on `Re s ≥ ½`. -/
theorem norm_one_sub_two_cpow_le {s : ℂ} (hs : 1 / 2 ≤ s.re) :
    ‖1 - (2 : ℂ) ^ (1 - s)‖ ≤ 3 := by
  have h2 : ((2 : ℝ) : ℂ) = (2 : ℂ) := by norm_num
  have hn : ‖(2 : ℂ) ^ (1 - s)‖ = (2 : ℝ) ^ (1 - s).re := by
    rw [← h2, norm_cpow_eq_rpow_re_of_pos (by norm_num)]
  have hre : (1 - s).re ≤ 1 / 2 := by simp only [sub_re, one_re]; linarith
  have hpow : (2 : ℝ) ^ (1 - s).re ≤ 2 := by
    calc (2 : ℝ) ^ (1 - s).re ≤ (2 : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = 2 := Real.rpow_one 2
  calc ‖1 - (2 : ℂ) ^ (1 - s)‖ ≤ ‖(1 : ℂ)‖ + ‖(2 : ℂ) ^ (1 - s)‖ := norm_sub_le _ _
    _ ≤ 1 + 2 := by rw [norm_one, hn]; linarith
    _ = 3 := by norm_num

/-! ### The quotient -/

/-- The pole-cleared Mellin quotient `(1 − 2^{1−s}) ζ(s) / (s ζ(s+ε))`. -/
def etaZetaQuotient (ε : ℝ) (s : ℂ) : ℂ :=
  etaSlope s * zetaResidueUnit s * invZeta (s + (ε : ℂ)) / s

/-- Off the two poles the quotient is the literal Mellin value. -/
theorem etaZetaQuotient_eq {ε : ℝ} {s : ℂ} (hs1 : s ≠ 1) (hsε : s + (ε : ℂ) ≠ 1) :
    etaZetaQuotient ε s =
      (1 - (2 : ℂ) ^ (1 - s)) * riemannZeta s / (s * riemannZeta (s + (ε : ℂ))) := by
  rw [etaZetaQuotient, invZeta_eq_inv hsε, zetaResidueUnit, Function.update_of_ne hs1,
    ← mul_assoc, mul_comm (etaSlope s) (s - 1), etaSlope_mul_sub, div_eq_mul_inv,
    div_eq_mul_inv, mul_inv]
  ring

/-- The entire factor `etaSlope · zetaResidueUnit` is `(1 − 2^{1−s}) ζ(s)` off `1`. -/
theorem etaSlope_mul_zetaResidueUnit {s : ℂ} (hs1 : s ≠ 1) :
    etaSlope s * zetaResidueUnit s = (1 - (2 : ℂ) ^ (1 - s)) * riemannZeta s := by
  rw [zetaResidueUnit, Function.update_of_ne hs1, ← mul_assoc, mul_comm (etaSlope s) (s - 1),
    etaSlope_mul_sub]

theorem differentiable_etaSlope_mul_zetaResidueUnit :
    Differentiable ℂ (fun s => etaSlope s * zetaResidueUnit s) := fun s =>
  (differentiable_etaSlope s).mul (analyticAt_zetaResidueUnit s).differentiableAt

/-- The quotient is holomorphic at every point of `Re s ≥ ½` once `Θ < ½ + ε`. -/
theorem differentiableAt_etaZetaQuotient {ε : ℝ} (hΘ : zetaZeroAbscissa < 1 / 2 + ε) {s : ℂ}
    (hs : 1 / 2 ≤ s.re) : DifferentiableAt ℂ (etaZetaQuotient ε) s := by
  have hs0 : s ≠ 0 := by
    intro h
    rw [h, zero_re] at hs
    linarith
  have hunit : zetaResidueUnit (s + (ε : ℂ)) ≠ 0 :=
    zetaResidueUnit_ne_zero_of_zeroFree (Θ := zetaZeroAbscissa)
      (fun z hz => riemannZeta_ne_zero_of_zetaZeroAbscissa_lt hz)
      (by simp only [add_re, ofReal_re]; linarith)
  have hinv : DifferentiableAt ℂ (fun s : ℂ => invZeta (s + (ε : ℂ))) s := by
    have h1 : DifferentiableAt ℂ (fun w : ℂ => (w - 1) * (zetaResidueUnit w)⁻¹) (s + (ε : ℂ)) :=
      (differentiableAt_id.sub_const 1).mul
        ((analyticAt_zetaResidueUnit _).differentiableAt.inv hunit)
    exact h1.comp s (differentiableAt_id.add_const _)
  exact ((differentiable_etaSlope_mul_zetaResidueUnit s).mul hinv).div differentiableAt_id hs0

/-! ### Line bounds -/

/-- The entire factor is bounded by `A (1 + |Im s|)^{5/16}` on `Re s ≥ ½`: convexity for
`½ ≤ Re s ≤ 9/8` and `|Im s| ≥ 8`, the trivial bound right of `9/8`, continuity on the rest. -/
theorem exists_norm_etaSlope_mul_zetaResidueUnit_le :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ s : ℂ, 1 / 2 ≤ s.re →
      ‖etaSlope s * zetaResidueUnit s‖ ≤ A * (1 + |s.im|) ^ ((5 : ℝ) / 16) := by
  obtain ⟨C₁, hC₁, hconv⟩ :=
    exists_norm_riemannZeta_le_convexity (η := 1 / 8) (by norm_num) (by norm_num)
  obtain ⟨C₂, hC₂⟩ := (isCompact_closedBall (0 : ℂ) 10).exists_bound_of_continuousOn
    differentiable_etaSlope_mul_zetaResidueUnit.continuous.continuousOn
  refine ⟨3 * C₁ + 27 + max C₂ 0, by positivity, fun s hs => ?_⟩
  have hpow1 : (1 : ℝ) ≤ (1 + |s.im|) ^ ((5 : ℝ) / 16) := by
    have h := Real.rpow_le_rpow zero_le_one
      (by linarith [abs_nonneg s.im] : (1 : ℝ) ≤ 1 + |s.im|) (by norm_num : (0 : ℝ) ≤ 5 / 16)
    rwa [Real.one_rpow] at h
  -- the convexity regime
  have hconv' : ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ 9 / 8 → 8 ≤ |s.im| →
      ‖riemannZeta s‖ ≤ C₁ * (1 + |s.im|) ^ ((5 : ℝ) / 16) := by
    intro s hs hs' ht
    have hkey : ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ 9 / 8 → 8 ≤ s.im →
        ‖riemannZeta s‖ ≤ C₁ * (1 + |s.im|) ^ ((5 : ℝ) / 16) := by
      intro s hs hs' ht
      have hsplit : s = (s.re : ℂ) + (s.im : ℂ) * I := (re_add_im s).symm
      have h := hconv s.re s.im (by linarith) (by linarith) ht
      rw [← hsplit] at h
      refine h.trans (mul_le_mul_of_nonneg_left ?_ hC₁.le)
      have ht0 : 0 ≤ s.im := by linarith
      have hexp : (1 + 1 / 8 - s.re) / 2 ≤ (5 : ℝ) / 16 := by linarith
      calc s.im ^ ((1 + 1 / 8 - s.re) / 2) ≤ s.im ^ ((5 : ℝ) / 16) :=
            Real.rpow_le_rpow_of_exponent_le (by linarith) hexp
        _ ≤ (1 + |s.im|) ^ ((5 : ℝ) / 16) :=
            Real.rpow_le_rpow ht0 (by rw [abs_of_nonneg ht0]; linarith) (by norm_num)
    rcases le_abs.mp ht with h | h
    · exact hkey s hs hs' h
    · -- reflect through conjugation
      have hconj : ‖riemannZeta s‖ = ‖riemannZeta (conj s)‖ := by
        rw [riemannZeta_conj, Complex.norm_conj]
      rw [hconj]
      have := hkey (conj s) (by rwa [conj_re]) (by rwa [conj_re]) (by rw [conj_im]; linarith)
      rwa [conj_im, abs_neg] at this
  -- the trivial regime right of `9/8`
  have hright : ∀ s : ℂ, 9 / 8 ≤ s.re → ‖riemannZeta s‖ ≤ 9 := by
    intro s hs
    have h := Sieve.norm_riemannZeta_le (s := s) (by linarith)
    refine h.trans ?_
    have h8 : 1 / (s.re - 1) ≤ 8 := by
      rw [div_le_iff₀ (by linarith)]; linarith
    linarith
  -- assemble
  by_cases hbig : 8 ≤ |s.im|
  · have hs1 : s ≠ 1 := by
      intro h; rw [h] at hbig; simp at hbig; linarith
    rw [etaSlope_mul_zetaResidueUnit hs1, norm_mul]
    have h3 := norm_one_sub_two_cpow_le hs
    rcases le_or_gt s.re (9 / 8) with hle | hgt
    · calc ‖1 - (2 : ℂ) ^ (1 - s)‖ * ‖riemannZeta s‖
          ≤ 3 * (C₁ * (1 + |s.im|) ^ ((5 : ℝ) / 16)) :=
            mul_le_mul h3 (hconv' s hs hle hbig) (norm_nonneg _) (by norm_num)
        _ ≤ (3 * C₁ + 27 + max C₂ 0) * (1 + |s.im|) ^ ((5 : ℝ) / 16) := by
            have := le_max_right C₂ 0
            nlinarith [Real.rpow_nonneg (by linarith [abs_nonneg s.im] : (0:ℝ) ≤ 1 + |s.im|)
              ((5 : ℝ) / 16)]
    · calc ‖1 - (2 : ℂ) ^ (1 - s)‖ * ‖riemannZeta s‖ ≤ 3 * 9 :=
            mul_le_mul h3 (hright s hgt.le) (norm_nonneg _) (by norm_num)
        _ = 27 * 1 := by norm_num
        _ ≤ (3 * C₁ + 27 + max C₂ 0) * (1 + |s.im|) ^ ((5 : ℝ) / 16) := by
            have := le_max_right C₂ 0
            exact mul_le_mul (by linarith) hpow1 zero_le_one (by positivity)
  · rw [not_le] at hbig
    rcases le_or_gt s.re (9 / 8) with hle | hgt
    · -- the compact rectangle lies in the ball of radius `10`
      have hmem : s ∈ Metric.closedBall (0 : ℂ) 10 := by
        rw [Metric.mem_closedBall, dist_zero_right]
        calc ‖s‖ ≤ |s.re| + |s.im| := Complex.norm_le_abs_re_add_abs_im s
          _ ≤ 10 := by
            rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ s.re)]
            linarith
      have h := hC₂ s hmem
      calc ‖etaSlope s * zetaResidueUnit s‖ ≤ C₂ := h
        _ ≤ (3 * C₁ + 27 + max C₂ 0) * 1 := by
            have := le_max_left C₂ 0; linarith
        _ ≤ (3 * C₁ + 27 + max C₂ 0) * (1 + |s.im|) ^ ((5 : ℝ) / 16) :=
            mul_le_mul_of_nonneg_left hpow1 (by positivity)
    · have hs1 : s ≠ 1 := by
        intro h; rw [h] at hgt; simp at hgt; linarith
      rw [etaSlope_mul_zetaResidueUnit hs1, norm_mul]
      calc ‖1 - (2 : ℂ) ^ (1 - s)‖ * ‖riemannZeta s‖ ≤ 3 * 9 :=
            mul_le_mul (norm_one_sub_two_cpow_le hs) (hright s hgt.le) (norm_nonneg _)
              (by norm_num)
        _ = 27 * 1 := by norm_num
        _ ≤ (3 * C₁ + 27 + max C₂ 0) * (1 + |s.im|) ^ ((5 : ℝ) / 16) := by
            have := le_max_right C₂ 0
            exact mul_le_mul (by linarith) hpow1 zero_le_one (by positivity)

/-- The regular reciprocal is bounded by `B (2 + |Im w|)^{1/8}` on `Re w ≥ ½ + ε` once
`Θ < ½ + ε`: the subpolynomial datum up to `Re w = 2`, the first Dirichlet term beyond. -/
theorem exists_norm_invZeta_le_of_zetaZeroAbscissa_lt {ε : ℝ} (hΘ : zetaZeroAbscissa < 1 / 2 + ε) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ w : ℂ, 1 / 2 + ε ≤ w.re →
      ‖invZeta w‖ ≤ B * (2 + |w.im|) ^ ((1 : ℝ) / 8) := by
  set δ : ℝ := min ((1 / 2 + ε - zetaZeroAbscissa) / 2) (1 / 2) with hδdef
  have hδ : 0 < δ := lt_min (by linarith) (by norm_num)
  have hδ1 : δ < 1 := (min_le_right _ _).trans_lt (by norm_num)
  have hδle : zetaZeroAbscissa + δ ≤ 1 / 2 + ε := by
    have := min_le_left ((1 / 2 + ε - zetaZeroAbscissa) / 2) (1 / 2)
    linarith
  obtain ⟨Kb, hKb, -, hbound⟩ := exists_invZeta_shift_data_of_zeroFree (Θ := zetaZeroAbscissa)
    half_le_zetaZeroAbscissa zetaZeroAbscissa_le_one
    (fun z hz => riemannZeta_ne_zero_of_zetaZeroAbscissa_lt hz) hδ hδ1
    (ε := 1 / 8) (by norm_num) 2
  refine ⟨max Kb 4, by positivity, fun w hw => ?_⟩
  have hpow1 : (1 : ℝ) ≤ (2 + |w.im|) ^ ((1 : ℝ) / 8) := by
    have h := Real.rpow_le_rpow zero_le_one
      (by linarith [abs_nonneg w.im] : (1 : ℝ) ≤ 2 + |w.im|) (by norm_num : (0 : ℝ) ≤ 1 / 8)
    rwa [Real.one_rpow] at h
  rcases le_or_gt w.re 2 with hle | hgt
  · have hmem : w ∈ verticalStrip (zetaZeroAbscissa + δ) 2 := ⟨by linarith, hle⟩
    calc ‖invZeta w‖ ≤ Kb * (2 + |w.im|) ^ ((1 : ℝ) / 8) := hbound w hmem
      _ ≤ max Kb 4 * (2 + |w.im|) ^ ((1 : ℝ) / 8) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
  · have hw1 : w ≠ 1 := by
      intro h; rw [h] at hgt; simp at hgt
    rw [invZeta_eq_inv hw1, norm_inv]
    have hlow := norm_riemannZeta_ge_of_two_le_re hgt.le
    calc ‖riemannZeta w‖⁻¹ ≤ (1 / 4 : ℝ)⁻¹ := inv_anti₀ (by norm_num) hlow
      _ = 4 * 1 := by norm_num
      _ ≤ max Kb 4 * (2 + |w.im|) ^ ((1 : ℝ) / 8) :=
          mul_le_mul (le_max_right _ _) hpow1 zero_le_one (by positivity)

/-- `1 + |Im s| ≤ 4 ‖s‖` on `Re s ≥ ½`. -/
theorem one_add_abs_im_le_four_mul_norm {s : ℂ} (hs : 1 / 2 ≤ s.re) :
    1 + |s.im| ≤ 4 * ‖s‖ := by
  have h1 : |s.im| ≤ ‖s‖ := Complex.abs_im_le_norm s
  have h2 : s.re ≤ ‖s‖ := Complex.re_le_norm s
  linarith

/-- **The line bound.** On `Re s ≥ ½`, `‖etaZetaQuotient ε s‖ ≤ K (1 + |Im s|)^{−9/16}`. -/
theorem exists_norm_etaZetaQuotient_le {ε : ℝ} (hΘ : zetaZeroAbscissa < 1 / 2 + ε) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ s : ℂ, 1 / 2 ≤ s.re →
      ‖etaZetaQuotient ε s‖ ≤ K * (1 + |s.im|) ^ (-(9 / 16 : ℝ)) := by
  obtain ⟨A, hA, hE⟩ := exists_norm_etaSlope_mul_zetaResidueUnit_le
  obtain ⟨B, hB, hI⟩ := exists_norm_invZeta_le_of_zetaZeroAbscissa_lt hΘ
  refine ⟨4 * A * B * 2 ^ ((1 : ℝ) / 8), by positivity, fun s hs => ?_⟩
  have hu : (0 : ℝ) < 1 + |s.im| := by linarith [abs_nonneg s.im]
  have hs0 : (0 : ℝ) < ‖s‖ := by
    have := one_add_abs_im_le_four_mul_norm hs; linarith [abs_nonneg s.im]
  have hw : 1 / 2 + ε ≤ (s + (ε : ℂ)).re := by simp only [add_re, ofReal_re]; linarith
  have hwim : (s + (ε : ℂ)).im = s.im := by simp
  have hI' : ‖invZeta (s + (ε : ℂ))‖ ≤ B * 2 ^ ((1 : ℝ) / 8) * (1 + |s.im|) ^ ((1 : ℝ) / 8) := by
    have h := hI _ hw
    rw [hwim] at h
    refine h.trans ?_
    rw [mul_assoc, ← Real.mul_rpow (x := 2) (y := 1 + |s.im|) (by norm_num) hu.le]
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (by linarith [abs_nonneg s.im]) (by linarith) (by norm_num)) hB
  have hinv : ‖s‖⁻¹ ≤ 4 * (1 + |s.im|)⁻¹ := by
    rw [← one_div, ← one_div, div_le_iff₀ hs0, mul_comm, ← mul_assoc, mul_one_div,
      div_le_iff₀ hu, one_mul]
    linarith [one_add_abs_im_le_four_mul_norm hs]
  rw [etaZetaQuotient, norm_div, norm_mul, div_eq_mul_inv]
  calc ‖etaSlope s * zetaResidueUnit s‖ * ‖invZeta (s + (ε : ℂ))‖ * ‖s‖⁻¹
      ≤ (A * (1 + |s.im|) ^ ((5 : ℝ) / 16)) *
          (B * 2 ^ ((1 : ℝ) / 8) * (1 + |s.im|) ^ ((1 : ℝ) / 8)) * (4 * (1 + |s.im|)⁻¹) := by
        gcongr
        · exact hE s hs
        · exact hI'
    _ = 4 * A * B * 2 ^ ((1 : ℝ) / 8) *
          ((1 + |s.im|) ^ ((5 : ℝ) / 16) * (1 + |s.im|) ^ ((1 : ℝ) / 8) * (1 + |s.im|)⁻¹) := by
        ring
    _ = 4 * A * B * 2 ^ ((1 : ℝ) / 8) * (1 + |s.im|) ^ (-(9 / 16 : ℝ)) := by
        congr 1
        rw [← Real.rpow_add hu, ← Real.rpow_neg_one, ← Real.rpow_add hu]
        try norm_num

/-! ### Hardy membership -/

/-- The majorant `K (1 + |ξ|)^{−9/16}` of the line values. -/
def lineMajorant (K : ℝ) (ξ : ℝ) : ℝ := K * (1 + |ξ|) ^ (-(9 / 16 : ℝ))

theorem continuous_lineMajorant (K : ℝ) : Continuous (lineMajorant K) :=
  continuous_const.mul ((continuous_const.add continuous_abs).rpow_const
    fun x => Or.inl (by show (1 + |x|) ≠ 0; positivity))

/-- The square of the majorant is integrable. -/
theorem integrable_sq_lineMajorant (K : ℝ) :
    Integrable (fun ξ : ℝ => ‖lineMajorant K ξ‖ ^ (2 : ℕ)) volume := by
  have hint : Integrable (fun ξ : ℝ => (1 + ‖ξ‖) ^ (-(9 / 8 : ℝ))) volume :=
    integrable_one_add_norm (E := ℝ) (r := 9 / 8) (by rw [Module.finrank_self]; norm_num)
  refine (hint.const_mul (K ^ 2)).congr (Filter.Eventually.of_forall fun ξ => ?_)
  have hu : (0 : ℝ) < 1 + |ξ| := by linarith [abs_nonneg ξ]
  have hy : ((1 + |ξ|) ^ (-(9 / 16 : ℝ))) ^ (2 : ℕ) = (1 + |ξ|) ^ (-(9 / 8 : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hu.le]
    norm_num
  simp only [lineMajorant, Real.norm_eq_abs]
  rw [sq_abs, mul_pow, hy]

/-- The majorant is square-integrable. -/
theorem memLp_two_lineMajorant (K : ℝ) : MemLp (lineMajorant K) 2 volume :=
  (memLp_two_iff_integrable_sq_norm (continuous_lineMajorant K).aestronglyMeasurable).mpr
    (integrable_sq_lineMajorant K)

/-- **The quotient is Mellin–Hardy at aperture `1`.** -/
theorem isMellinTailHardy_etaZetaQuotient {ε : ℝ} (hΘ : zetaZeroAbscissa < 1 / 2 + ε) :
    IsMellinTailHardy 1 (etaZetaQuotient ε) := by
  obtain ⟨K, hK, hbound⟩ := exists_norm_etaZetaQuotient_le hΘ
  -- the Hardy function is `w ↦ etaZetaQuotient ε (w + ½)`
  have hfun : (fun w : ℂ => ((1 : ℝ) : ℂ) ^ w * etaZetaQuotient ε (w + 1 / 2)) =
      fun w : ℂ => etaZetaQuotient ε (w + 1 / 2) := by
    funext w; simp
  -- pointwise bound on the line `Re w = σ`
  have hline : ∀ σ : ℝ, 0 ≤ σ → ∀ ξ : ℝ,
      ‖etaZetaQuotient ε (rayLine σ ξ + 1 / 2)‖ ≤ ‖lineMajorant K ξ‖ := by
    intro σ hσ ξ
    have hre : 1 / 2 ≤ (rayLine σ ξ + 1 / 2).re := by
      simp only [add_re, rayLine_re]
      norm_num; linarith
    have him : (rayLine σ ξ + 1 / 2).im = 2 * Real.pi * ξ := by
      simp [rayLine]
    have h := hbound _ hre
    rw [him] at h
    refine h.trans ?_
    rw [lineMajorant, Real.norm_eq_abs, abs_mul, abs_of_nonneg hK,
      abs_of_nonneg (Real.rpow_nonneg (x := 1 + |ξ|) (by linarith [abs_nonneg ξ]) _)]
    refine mul_le_mul_of_nonneg_left ?_ hK
    -- `(1 + |2πξ|)^{−9/16} ≤ (1 + |ξ|)^{−9/16}` since `|ξ| ≤ |2πξ|`
    have h1 : 1 + |ξ| ≤ 1 + |2 * Real.pi * ξ| := by
      rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
      nlinarith [abs_nonneg ξ, Real.pi_gt_three]
    rw [Real.rpow_neg (by linarith [abs_nonneg ξ]), Real.rpow_neg (by linarith [abs_nonneg ξ])]
    exact inv_anti₀ (Real.rpow_pos_of_pos (by linarith [abs_nonneg ξ]) _)
      (Real.rpow_le_rpow (by linarith [abs_nonneg ξ]) h1 (by norm_num))
  have hcont : ∀ σ : ℝ, 0 ≤ σ →
      Continuous (fun ξ : ℝ => etaZetaQuotient ε (rayLine σ ξ + 1 / 2)) := by
    intro σ hσ
    refine continuous_iff_continuousAt.mpr fun ξ => ?_
    have hre : 1 / 2 ≤ (rayLine σ ξ + 1 / 2).re := by
      simp only [add_re, rayLine_re]; norm_num; linarith
    exact (differentiableAt_etaZetaQuotient hΘ hre).continuousAt.comp
      (((continuous_const.mul continuous_ofReal).mul continuous_const).add
        continuous_const |>.continuousAt)
  refine ⟨∫ ξ : ℝ, ‖lineMajorant K ξ‖ ^ (2 : ℕ), ?_⟩
  rw [hfun]
  refine ⟨?_, fun σ hσ => ?_, fun σ hσ => ?_⟩
  · intro w hw
    have hre : 1 / 2 ≤ (w + 1 / 2).re := by
      simp only [add_re]; norm_num; exact le_of_lt hw
    exact ((differentiableAt_etaZetaQuotient hΘ hre).comp w
      (differentiableAt_id.add_const _)).differentiableWithinAt
  · exact (memLp_two_lineMajorant K).of_le (hcont σ hσ.le).aestronglyMeasurable
      (Filter.Eventually.of_forall (hline σ hσ.le))
  · refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun ξ => by positivity)
      (integrable_sq_lineMajorant K) (Filter.Eventually.of_forall fun ξ => ?_)
    exact pow_le_pow_left₀ (norm_nonneg _) (hline σ hσ.le ξ) 2

end RHTower
