import GaloisForLFunctions.RHTower.ZetaChiDualGrowingResonatorMean
import GaloisForLFunctions.HTGeometry.GeneralizedDirichletMeanValue
import GaloisForLFunctions.RHTower.Sieve.LogSeparation

open Complex Set Filter Topology MeasureTheory
open scoped BigOperators ComplexConjugate
noncomputable section
namespace RHTower


private theorem zetaChiDualResonator_eq_genPoly (S : Finset ℕ) (c : ℕ → ℂ) (t : ℝ) :
    zetaChiDualResonator S c t = HTGeometry.genPoly c (fun a => Real.log a) S t := by
  unfold zetaChiDualResonator HTGeometry.genPoly
  apply Finset.sum_congr rfl
  intro a _
  congr 1
  unfold bourgainOscillation
  congr 1
  push_cast
  ring

/-- The actual physical mass of every finite positive-frequency resonator has
its diagonal energy with an explicit interval-independent error. -/
theorem norm_integral_zetaChiDualResonator_sq_sub_energy_le
    {R : ℕ} (hR : 0 < R) (S : Finset ℕ) (c : ℕ → ℂ)
    (hS : ∀ a ∈ S, 0 < a ∧ a ≤ R) (T U : ℝ) :
    ‖(∫ t in T..(T + U), ((‖zetaChiDualResonator S c t‖ ^ 2 : ℝ) : ℂ)) -
      (U : ℂ) * (((∑ a ∈ S, ‖c a‖ ^ 2 : ℝ)) : ℂ)‖ ≤
      2 * (R : ℝ) * S.card * ∑ a ∈ S, ‖c a‖ ^ 2 := by
  have hR0 : (0 : ℝ) < R := by exact_mod_cast hR
  have hb := HTGeometry.genPoly_meanValue_error_of_gap c (fun a => Real.log a) S T U
    (1 / (R : ℝ)) (by positivity) (by
      intro a ha q hq hne
      exact Sieve.one_div_nat_upper_le_abs_log_sub (hS q hq).1 (hS a ha).1
        (hS q hq).2 (hS a ha).2 hne)
  have hint : (∫ t in T..(T + U), ((‖zetaChiDualResonator S c t‖ ^ 2 : ℝ) : ℂ)) =
      (∫ t in T..(T + U), HTGeometry.genPoly c (fun a => Real.log a) S t *
        conj (HTGeometry.genPoly c (fun a => Real.log a) S t)) := by
    apply intervalIntegral.integral_congr
    intro t _
    dsimp only
    rw [zetaChiDualResonator_eq_genPoly, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hdiag : (∑ a ∈ S, c a * conj (c a)) =
      (((∑ a ∈ S, ‖c a‖ ^ 2 : ℝ)) : ℂ) := by
    simp_rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast
    rfl
  rw [hdiag] at hb
  have hfactor : (2 : ℝ) / (1 / (R : ℝ)) = 2 * R := by field_simp
  rw [hfactor] at hb
  have hcs : (∑ a ∈ S, ‖c a‖) ^ 2 ≤ (S.card : ℝ) * ∑ a ∈ S, ‖c a‖ ^ 2 := by
    simpa only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] using
      Finset.sum_mul_sq_le_sq_mul_sq S (fun _ => (1 : ℝ)) (fun a => ‖c a‖)
  rw [hint]
  calc
    _ ≤ 2 * (R : ℝ) * (∑ a ∈ S, ‖c a‖) ^ 2 := hb
    _ ≤ 2 * (R : ℝ) * ((S.card : ℝ) * ∑ a ∈ S, ‖c a‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hcs (by positivity)
    _ = _ := by ring

/-- The growing narrow family has physical mass error at most404*k² times
coefficient energy, uniformly in the interval and every coefficient. -/
theorem norm_integral_zetaChiDualNarrowResonator_sq_sub_energy_le
    {k : ℕ} (hk : 0 < k) (S : Finset ℕ) (c : ℕ → ℂ)
    (hS : ∀ a ∈ S, 100 * k ≤ a ∧ a ≤ 101 * k) (T U : ℝ) :
    ‖(∫ t in T..(T + U), ((‖zetaChiDualResonator S c t‖ ^ 2 : ℝ) : ℂ)) -
      (U : ℂ) * (((∑ a ∈ S, ‖c a‖ ^ 2 : ℝ)) : ℂ)‖ ≤
      404 * (k : ℝ) ^ 2 * ∑ a ∈ S, ‖c a‖ ^ 2 := by
  have hpos (a : ℕ) (ha : a ∈ S) : 0 < a ∧ a ≤ 101 * k := by
    have := hS a ha
    omega
  have hb := norm_integral_zetaChiDualResonator_sq_sub_energy_le (by positivity : 0 < 101 * k)
    S c hpos T U
  have hsub : S ⊆ Finset.Icc (100 * k) (101 * k) := fun a ha => Finset.mem_Icc.mpr (hS a ha)
  have hcard := Finset.card_le_card hsub
  rw [Nat.card_Icc] at hcard
  have hc : (S.card : ℝ) ≤ 2 * (k : ℝ) := by exact_mod_cast (by omega : S.card ≤ 2 * k)
  norm_num only [Nat.cast_mul, Nat.cast_ofNat] at hb
  apply hb.trans
  calc
    _ ≤ 2 * (101 * (k : ℝ)) * (2 * (k : ℝ)) * ∑ a ∈ S, ‖c a‖ ^ 2 := by gcongr
    _ = _ := by ring

end RHTower
