/-
# Chen--Gupta--Li tail coefficients and uniform bounds

The Mellin zero-detection step needs infinite character-twisted detector tail,
not only finite slice. This module proves all-index coefficient formula and a
uniform right-half-plane bound from literal Möbius divisor sum and existing
divisor-growth theorem. No zero-density estimate, RH/GRH, or caller-supplied
analytic bound is used.
-/

import GaloisForLFunctions.RHTower.ChenGuptaLiDetectorTail
import GaloisForLFunctions.RHTower.Sieve.InghamExponentialMellinInversion

open Complex LSeries DirichletCharacter

noncomputable section

namespace RHTower

/-- At every natural index, full finite-Möbius/character convolution is literal
truncated Möbius divisor coefficient times character value. -/
theorem cglTruncatedMobiusTwist_convolution_character_eq_mobiusCoefficient_all
    (X q : ℕ) (χ : DirichletCharacter ℂ (q + 1)) (n : ℕ) :
    LSeries.convolution (cglTruncatedMobiusTwist X (q + 1) χ) (fun m : ℕ => χ m) n =
      (zeroDetectionMobiusCoefficient X n : ℂ) * χ n := by
  by_cases hn : n = 0
  · subst n
    rw [LSeries.convolution_map_zero]
    simp [zeroDetectionMobiusCoefficient]
  rw [LSeries.convolution_def]
  calc
    (∑ p ∈ n.divisorsAntidiagonal,
        cglTruncatedMobiusTwist X (q + 1) χ p.1 * χ p.2) =
        ∑ p ∈ n.divisorsAntidiagonal,
          (if p.1 ≤ X + 1 then (ArithmeticFunction.moebius p.1 : ℂ) else 0) * χ n := by
      apply Finset.sum_congr rfl
      intro p hp
      have hpdata := Nat.mem_divisorsAntidiagonal.mp hp
      have hp1pos : 0 < p.1 :=
        Nat.pos_of_ne_zero (Nat.ne_zero_of_mem_divisorsAntidiagonal hp).1
      by_cases hcut : p.1 ≤ X + 1
      · have hp1mem : p.1 ∈ Finset.Icc 1 (X + 1) :=
          Finset.mem_Icc.mpr ⟨hp1pos, hcut⟩
        rw [cglTruncatedMobiusTwist, if_pos hp1mem, if_pos hcut]
        have hχ : χ ((p.1 : ZMod (q + 1)) * (p.2 : ZMod (q + 1))) = χ (n : ZMod (q + 1)) := by
          rw [← Nat.cast_mul, hpdata.1]
        calc
          (ArithmeticFunction.moebius p.1 : ℂ) * χ p.1 * χ p.2 =
              (ArithmeticFunction.moebius p.1 : ℂ) * (χ p.1 * χ p.2) := by ring
          _ = (ArithmeticFunction.moebius p.1 : ℂ) * χ (p.1 * p.2) := by rw [← map_mul]
          _ = _ := by rw [hχ]
      · have hp1notmem : p.1 ∉ Finset.Icc 1 (X + 1) := by
          simp [hcut]
        rw [cglTruncatedMobiusTwist, if_neg hp1notmem, if_neg hcut]
        ring
    _ = (∑ p ∈ n.divisorsAntidiagonal,
        if p.1 ≤ X + 1 then (ArithmeticFunction.moebius p.1 : ℂ) else 0) * χ n := by
      rw [Finset.sum_mul]
    _ = (zeroDetectionMobiusCoefficient X n : ℂ) * χ n := by
      congr 1
      unfold zeroDetectionMobiusCoefficient
      rw [Nat.sum_divisorsAntidiagonal (fun d _ =>
        if d ≤ X + 1 then (ArithmeticFunction.moebius d : ℂ) else 0)]
      rw [Finset.sum_filter]
      norm_cast

/-- Literal truncated Möbius divisor coefficient is bounded by divisor count,
uniformly in cutoff. -/
theorem norm_zeroDetectionMobiusCoefficient_le_card_divisors (X n : ℕ) :
    ‖(zeroDetectionMobiusCoefficient X n : ℂ)‖ ≤ n.divisors.card := by
  calc
    ‖(zeroDetectionMobiusCoefficient X n : ℂ)‖ =
        ‖∑ d ∈ n.divisors.filter (fun d => d ≤ X + 1),
          (ArithmeticFunction.moebius d : ℂ)‖ := by
      simp [zeroDetectionMobiusCoefficient]
    _ ≤ ∑ d ∈ n.divisors.filter (fun d => d ≤ X + 1),
          ‖(ArithmeticFunction.moebius d : ℂ)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _d ∈ n.divisors.filter (fun d => d ≤ X + 1), (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro d hd
      rw [Complex.norm_intCast]
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one
    _ = (n.divisors.filter (fun d => d ≤ X + 1)).card := by simp
    _ ≤ n.divisors.card := by
      exact_mod_cast Finset.card_filter_le n.divisors (fun d => d ≤ X + 1)

/-- Full detector-tail coefficient is bounded by divisor count. -/
theorem norm_cglDetectorTailCoefficient_le_card_divisors (X q : ℕ)
    (χ : DirichletCharacter ℂ (q + 1)) (n : ℕ) :
    ‖cglDetectorTailCoefficient X q χ n‖ ≤ n.divisors.card := by
  by_cases hn0 : n = 0
  · subst n
    simp [cglDetectorTailCoefficient, cglUnitCoefficient]
  by_cases hn1 : n = 1
  · subst n
    rw [cglDetectorTailCoefficient_one]
    simp
  unfold cglDetectorTailCoefficient cglUnitCoefficient
  rw [cglTruncatedMobiusTwist_convolution_character_eq_mobiusCoefficient_all,
    if_neg hn1, sub_zero, norm_mul]
  calc
    ‖(zeroDetectionMobiusCoefficient X n : ℂ)‖ * ‖χ n‖ ≤
        (n.divisors.card : ℝ) * 1 := by
      exact mul_le_mul (norm_zeroDetectionMobiusCoefficient_le_card_divisors X n)
        (χ.norm_le_one n) (norm_nonneg _) (by positivity)
    _ = n.divisors.card := by simp

/-- Complex point on or right of critical line. Real-part certificate is data,
so uniform-bound theorem has no incoming inequality premise. -/
def CGLRightHalfPlanePoint := {s : ℂ // (1 / 2 : ℝ) ≤ s.re}

/-- Detector-tail coefficients shifted by closed-right-half-plane point. -/
def cglShiftedDetectorTailCoefficient (X q : ℕ) (χ : DirichletCharacter ℂ (q + 1))
    (s : CGLRightHalfPlanePoint) (n : ℕ) : ℂ :=
  cglDetectorTailCoefficient X q χ n * (n : ℂ) ^ (-s.1)

/-- Single positive constant bounds every shifted detector-tail coefficient on
`Re(s) ≥ 1/2`, uniformly in cutoff, modulus, character, and index. -/
theorem exists_cglShiftedDetectorTailCoefficient_uniformBound :
    ∃ C : ℝ, 0 < C ∧ ∀ X q : ℕ, ∀ χ : DirichletCharacter ℂ (q + 1),
      ∀ s : CGLRightHalfPlanePoint, ∀ n : ℕ,
        ‖cglShiftedDetectorTailCoefficient X q χ s n‖ ≤ C := by
  obtain ⟨C, hC, hdiv⟩ := card_divisors_le_const_mul_rpow (ε := (1 / 4 : ℝ)) (by norm_num)
  refine ⟨C, hC, ?_⟩
  intro X q χ s n
  by_cases hn : n = 0
  · subst n
    simpa [cglShiftedDetectorTailCoefficient, cglDetectorTailCoefficient, cglUnitCoefficient] using hC.le
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
  unfold cglShiftedDetectorTailCoefficient
  rw [norm_mul, Complex.norm_natCast_cpow_of_pos hnpos, Complex.neg_re]
  calc
    ‖cglDetectorTailCoefficient X q χ n‖ * (n : ℝ) ^ (-s.1.re) ≤
        (n.divisors.card : ℝ) * (n : ℝ) ^ (-s.1.re) :=
      mul_le_mul_of_nonneg_right (norm_cglDetectorTailCoefficient_le_card_divisors X q χ n)
        (Real.rpow_nonneg hnR.le _)
    _ ≤ (C * (n : ℝ) ^ (1 / 4 : ℝ)) * (n : ℝ) ^ (-s.1.re) :=
      mul_le_mul_of_nonneg_right (hdiv n hnpos) (Real.rpow_nonneg hnR.le _)
    _ = C * ((n : ℝ) ^ (1 / 4 : ℝ) * (n : ℝ) ^ (-s.1.re)) := by ring
    _ = C * (n : ℝ) ^ ((1 / 4 : ℝ) + (-s.1.re)) := by
      rw [← Real.rpow_add hnR]
    _ ≤ C * 1 := by
      gcongr
      apply Real.rpow_le_one_of_one_le_of_nonpos
      · exact_mod_cast (Nat.succ_le_iff.mpr hnpos)
      · linarith [s.2]
    _ = C := by ring

end RHTower
