import GaloisForLFunctions.HTGeometry.LabeledCosineMobius

/-!
# Exact reflection coincidences of the descended cosine

The complete coincidence locus is an integral quartic equation. Multiplicative reciprocal
symmetrization of the associated Mobius map therefore creates an actual off-real 1-fiber.
-/

namespace GaloisForLFunctions.HTGeometry.CosineReflectionCoincidence

open Complex LabeledCosineDescent LabeledCosineMobius
open scoped ComplexConjugate

noncomputable section

theorem coincidence_iff (w : ℂ) : source w = source (-w) ↔
    ∃ n : ℤ, 4 * w ^ 2 = 9 * (n : ℂ) ^ 2 * (1 - 81 * (n : ℂ) ^ 2) := by
  have hp : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  constructor
  · intro h
    let u := Complex.sqrt ((2 * (Real.pi : ℂ)) ^ 2 * ((w + 1 / 12) / 27))
    let v := Complex.sqrt ((2 * (Real.pi : ℂ)) ^ 2 * ((-w + 1 / 12) / 27))
    have hu : u ^ 2 = (2 * (Real.pi : ℂ)) ^ 2 * ((w + 1 / 12) / 27) := sqrt_square _
    have hv : v ^ 2 = (2 * (Real.pi : ℂ)) ^ 2 * ((-w + 1 / 12) / 27) := sqrt_square _
    obtain ⟨n, hn⟩ := Complex.cos_eq_cos_iff.mp (show Complex.cos u = Complex.cos v from h)
    have hkey : (u ^ 2 - v ^ 2) ^ 2 - 8 * (Real.pi : ℂ) ^ 2 * (n : ℂ) ^ 2 *
        (u ^ 2 + v ^ 2) + 16 * (Real.pi : ℂ) ^ 4 * (n : ℂ) ^ 4 = 0 := by
      rcases hn with hn | hn <;> rw [hn] <;> ring
    rw [hu, hv] at hkey
    refine ⟨n, ?_⟩
    apply mul_left_cancel₀ (pow_ne_zero 4 hp)
    linear_combination (729 / 16 : ℂ) * hkey
  · rintro ⟨n, hn⟩
    by_cases hn0 : n = 0
    · subst n
      have hw : w = 0 := by
        have : w ^ 2 = 0 := by linear_combination hn / 4
        exact (pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0)).mp this
      simp [hw]
    have hnc : (n : ℂ) ≠ 0 := by exact_mod_cast hn0
    have hdiv : 4 * w ^ 2 / (729 * (n : ℂ) ^ 2) = 1 / 81 - (n : ℂ) ^ 2 := by
      apply (div_eq_iff (mul_ne_zero (by norm_num) (pow_ne_zero 2 hnc))).mpr
      linear_combination hn
    let u : ℂ := Real.pi * n + 2 * Real.pi * w / (27 * n)
    let v : ℂ := -Real.pi * n + 2 * Real.pi * w / (27 * n)
    have hu : u ^ 2 = (2 * (Real.pi : ℂ)) ^ 2 * ((w + 1 / 12) / 27) := by
      calc u ^ 2 = (Real.pi : ℂ) ^ 2 * ((n : ℂ) ^ 2 + 4 * w / 27 +
          4 * w ^ 2 / (729 * (n : ℂ) ^ 2)) := by dsimp [u]; field_simp; ring
        _ = _ := by rw [hdiv]; ring
    have hv : v ^ 2 = (2 * (Real.pi : ℂ)) ^ 2 * ((-w + 1 / 12) / 27) := by
      calc v ^ 2 = (Real.pi : ℂ) ^ 2 * ((n : ℂ) ^ 2 - 4 * w / 27 +
          4 * w ^ 2 / (729 * (n : ℂ) ^ 2)) := by dsimp [v]; field_simp; ring
        _ = _ := by rw [hdiv]; ring
    rw [source, source, descendedCos_of_square hu, descendedCos_of_square hv]
    apply Complex.cos_eq_cos_iff.mpr
    refine ⟨-n, Or.inl ?_⟩
    dsimp [u, v]
    push_cast
    ring

def witness : ℂ := 6 * Complex.I * (Real.sqrt 5 : ℂ)

theorem witness_sq : witness ^ 2 = -180 := by
  have hs : (Real.sqrt 5 : ℂ) ^ 2 = 5 := by
    exact_mod_cast Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)
  norm_num [witness, mul_pow, hs, Complex.I_sq]

theorem witness_im_ne_zero : witness.im ≠ 0 := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)
  intro h
  have hz : Real.sqrt 5 = 0 := by
    have hc : witness.im = 6 * Real.sqrt 5 := by simp [witness]
    rw [hc] at h
    linear_combination h / 6
  rw [hz] at hs
  norm_num at hs

theorem witness_conj : conj witness = -witness := by
  simp [witness, map_ofNat, mul_assoc]

theorem witness_coincidence : source witness = source (-witness) := by
  apply (coincidence_iff witness).mpr
  exact ⟨1, by norm_num [witness_sq]⟩

def repairNumerator (w : ℂ) : ℂ := N w * D (-w)
def repairDenominator (w : ℂ) : ℂ := D w * N (-w)
def repair (w : ℂ) : ℂ := repairNumerator w / repairDenominator w

theorem repair_reciprocal (w : ℂ) : repair (-w) = (repair w)⁻¹ := by
  simp [repair, repairNumerator, repairDenominator, mul_comm]

theorem repair_conjugate (w : ℂ) : repair (conj w) = (conj (repair w))⁻¹ := by
  have h := conjugate_coordinates w
  have hm := conjugate_coordinates (-w)
  simp only [map_neg] at hm
  simp [repair, repairNumerator, repairDenominator, h.1, h.2, hm.1, hm.2, mul_comm]

theorem witness_coordinates : N (-witness) = N witness ∧ D (-witness) = D witness := by
  simp [N, D, ← witness_coincidence]

theorem witness_denominator_ne_zero : repairDenominator witness ≠ 0 := by
  have hn := witness_coordinates.1
  have hd := witness_coordinates.2
  have hconj := (conjugate_coordinates witness).1
  rw [witness_conj, hn] at hconj
  have hDz : D witness ≠ 0 := by
    intro hz
    have hNz : N witness = 0 := by simpa [hz] using hconj
    exact no_common_zero (source witness) ⟨hNz, hz⟩
  have hNz : N witness ≠ 0 := by
    rw [hconj]
    simpa using hDz
  exact mul_ne_zero hDz (hn ▸ hNz)

theorem repair_witness : repair witness = 1 := by
  rw [repair, div_eq_one_iff_eq witness_denominator_ne_zero]
  simp [repairNumerator, repairDenominator, witness_coordinates.1, witness_coordinates.2, mul_comm]

theorem repair_analyticAt_witness : AnalyticAt ℂ repair witness := by
  have hnum : Differentiable ℂ repairNumerator := by
    unfold repairNumerator
    exact numerator_entire.mul (denominator_entire.comp (by fun_prop))
  have hden : Differentiable ℂ repairDenominator := by
    unfold repairDenominator
    exact denominator_entire.mul (numerator_entire.comp (by fun_prop))
  exact (hnum.analyticAt witness).div (hden.analyticAt witness) witness_denominator_ne_zero

theorem reciprocal_repair_has_off_real_one_fiber :
    (∀ w, repair (-w) = (repair w)⁻¹) ∧
    (∀ w, repair (conj w) = (conj (repair w))⁻¹) ∧
    ∃ w : ℂ, w.im ≠ 0 ∧ AnalyticAt ℂ repair w ∧ repair w = 1 :=
  ⟨repair_reciprocal, repair_conjugate, witness, witness_im_ne_zero,
    repair_analyticAt_witness, repair_witness⟩

end

end GaloisForLFunctions.HTGeometry.CosineReflectionCoincidence
