import GaloisForLFunctions.ArithmeticPositiveDuality.ApproximateFunctionalEquationDeterminesThePrimes

/-!
# Small integrable defects bound the pole residue

The two unique atoms near 1 and 2 exhaust the support of the unit tent at 1. Their tent mass is
at most 9/8. The defective theta identity therefore bounds the pole residue by 19/16.
-/

open Complex MeasureTheory Filter Topology Set
open GaloisForLFunctions.HTGeometry

noncomputable section
namespace GaloisForLFunctions.ArithmeticPositiveDuality

/-- The first unit tent sees at most the unit atom and an eighth of the unique atom near 2. -/
private theorem first_tent_le_of_two_unique_atoms
    (B : RHTower.BeurlingSystem) [Countable B.Label]
    (hnear : ∀ x : B.Integer, B.intNorm x ≤ 2 →
      |B.intNorm x - round (B.intNorm x)| ≤ 1 / 8)
    (hU : ∀ m : ℕ, 1 ≤ m → m ≤ 2 → ∃! x : B.Integer, |B.intNorm x - m| ≤ 1 / 8) :
    ∫ u, unitTent 1 u ∂beurlingSystemIntegerMeasure B ≤ 9 / 8 := by
  classical
  obtain ⟨x₁, hx₁, hu₁⟩ := hU 1 (by omega) (by omega)
  have hzero : (0 : B.Integer) = x₁ := hu₁ 0 (by simp [B.intNorm_zero])
  have hone : ∀ x : B.Integer, |B.intNorm x - 1| ≤ 1 / 8 → x = 0 := by
    intro x hx
    exact (hu₁ x hx).trans hzero.symm
  obtain ⟨x₂, hx₂, hu₂⟩ := hU 2 (by omega) (by omega)
  have hx₂0 : x₂ ≠ 0 := by
    intro h
    subst x₂
    norm_num [B.intNorm_zero] at hx₂
  have hS : ∀ x : B.Integer, x ∉ ({0, x₂} : Finset B.Integer) → 2 < B.intNorm x := by
    intro x hx
    by_contra! hle
    have hn := hnear x hle
    have hr1 := one_le_round_intNorm x
    have hr3 : (round (B.intNorm x) : ℝ) < 3 := by linarith only [(abs_le.mp hn).1, hle]
    have hr3' : round (B.intNorm x) < 3 := by exact_mod_cast hr3
    have hr : round (B.intNorm x) = 1 ∨ round (B.intNorm x) = 2 := by omega
    rcases hr with hr | hr
    · have he : x = 0 := hone x (by simpa only [hr, Int.cast_one] using hn)
      exact hx (by simp [he])
    · have he : x = x₂ := hu₂ x (by simpa only [hr, Int.cast_ofNat, Nat.cast_ofNat] using hn)
      exact hx (by simp [he])
  rw [integral_unitTent_eq_sum_of_le B hS (by norm_num : (1 : ℝ) + 1 ≤ 2)]
  have ht : unitTent 1 (B.intNorm x₂) ≤ 1 / 8 := by
    have hl : 15 / 8 ≤ B.intNorm x₂ := by linarith only [(abs_le.mp hx₂).1]
    unfold unitTent
    apply max_le (by norm_num)
    rw [abs_of_nonneg (by linarith only [hl])]
    linarith only [hl]
  simp only [Finset.sum_insert (by simpa using hx₂0.symm), Finset.sum_singleton,
    B.intNorm_zero]
  have ht1 : unitTent 1 1 = 1 := by simp [unitTent]
  rw [ht1]
  linarith only [ht]

/-- An integrable FE defect of norm at most `1/6400` forces the pole residue below `√2`. -/
theorem pole_residue_le_of_small_critical_line_defect
    (B : RHTower.BeurlingSystem) [Countable B.Label]
    (hBsum : Summable fun x : B.Integer => B.intNorm x ^ (-(3 / 2 : ℝ)))
    {E : ℂ → ℂ} {β : ℂ} {C : ℝ} {g : ℝ → ℂ} {Cg : ℝ} {Ng : ℕ}
    (hEc : ContinuousOn E (verticalStrip (1 / 2) (3 / 2)))
    (hEd : DifferentiableOn ℂ E {s : ℂ | 1 / 2 < s.re ∧ s.re < 3 / 2})
    (hdecay : ∀ s ∈ verticalStrip (1 / 2) (3 / 2), ‖E s‖ ≤ C / (1 + s.im ^ 2))
    (hR : ∀ s : ℂ, s.re = 3 / 2 →
      Complex.Gammaℝ s * beurlingZeta B s = E s + β * Complex.Gammaℝ (s - 1))
    (hC : ∀ s : ℂ, s.re = 1 / 2 → E s - E (1 - s) =
      -(β * (Complex.Gammaℝ (s - 1) - Complex.Gammaℝ (-s))) + Complex.Gammaℝ s * g (s.im / 2))
    (hgm : Measurable g) (hgb : ∀ t : ℝ, ‖g t‖ ≤ Cg * (1 + |t|) ^ Ng) (hgi : Integrable g)
    (hsmall : 6400 * ∫ t, ‖g t‖ ≤ 1) :
    2 * β.re ≤ 19 / 16 := by
  have hM0 : 0 ≤ ∫ t, ‖g t‖ := integral_nonneg fun _ => norm_nonneg _
  have hsmall4 : 400 * (4 : ℝ) ^ 2 * ∫ t, ‖g t‖ ≤ 1 := by
    convert hsmall using 1 <;> norm_num
  obtain ⟨hnear, hU, -⟩ := beurling_primes_of_critical_line_defect B hBsum hEc hEd hdecay hR hC
    hgm hgb hgi (N := 4) (by omega) hsmall4
  have hroot : Real.sqrt (3 * Real.pi / 2 * ∫ t, ‖g t‖) ≤ 1 / 16 := by
    have hpi : Real.pi < 4 := by linarith only [Real.pi_lt_d2]
    have hsq : 3 * Real.pi / 2 * (∫ t, ‖g t‖) ≤ (1 / 16) ^ 2 := by
      have hh := mul_le_mul_of_nonneg_right hpi.le hM0
      nlinarith only [hsmall, hh, hM0]
    calc Real.sqrt (3 * Real.pi / 2 * ∫ t, ‖g t‖) ≤ Real.sqrt ((1 / 16) ^ 2) :=
          Real.sqrt_le_sqrt hsq
      _ = 1 / 16 := Real.sqrt_sq (by norm_num)
  have ht : ∫ u, unitTent 1 u ∂beurlingSystemIntegerMeasure B ≤ 9 / 8 :=
    first_tent_le_of_two_unique_atoms B (fun x hx => (hnear x).trans (by
      calc Real.sqrt (3 * Real.pi / 2 * ∫ t, ‖g t‖) * B.intNorm x ≤ (1 / 16) * 2 :=
            mul_le_mul hroot hx (B.intNorm_pos x).le (by norm_num)
        _ = 1 / 8 := by norm_num)) (fun m hm hm2 => hU m hm (by omega))
  have hsupp := beurlingSystemIntegerMeasure_Iio_one_eq_zero B
  have hmom := integrable_rpow_beurlingSystemIntegerMeasure B hBsum
  have hR' : ∀ s : ℂ, s.re = 3 / 2 → Complex.Gammaℝ s *
      measureDirichlet (beurlingSystemIntegerMeasure B) s = E s + β * Complex.Gammaℝ (s - 1) :=
    fun s hs => by rw [measureDirichlet_beurlingSystemIntegerMeasure]; exact hR s hs
  have htent := abs_integral_unitTent_sub_le_of_critical_line_defect hsupp hmom hEc hEd hdecay
    hR' hC hgm hgb hgi (by norm_num : (1 : ℝ) ≤ 1)
  have herr : (18 / Real.pi + 4 * defectKernelConst / Real.pi ^ 2) * (∫ t, ‖g t‖) ≤ 1 / 16 := by
    have hh := mul_le_mul_of_nonneg_right tentConst_le_eight hM0
    linarith only [hh, hsmall]
  linarith only [(abs_le.mp htent).1, ht, herr]

end GaloisForLFunctions.ArithmeticPositiveDuality
