import GaloisForLFunctions.BezoutValuationIncidence.VaughanPacketsHaveAnExactResidualEnergyDensity
import GaloisForLFunctions.BezoutValuationIncidence.TheAdmittedVaughanCoefficientSpace
import GaloisForLFunctions.BezoutValuationIncidence.TheReceiverEquivalenceAndZeroWidthLaw
import GaloisForLFunctions.TransHorizonIncidenceMechanics.CriticalWienerConvolutionsPreserveTheReceiver

/-!
At half damping the actual receiver has bounded pronic norm, while the smooth
square-root direction has divergent harmonic energy. Admission therefore removes
both explicit drifts and gives a three-dimensional space at positive cutoffs.
-/

open Finset Filter RHTower
open GaloisForLFunctions.TransHorizonIncidenceMechanics
open scoped BigOperators Topology
noncomputable section
namespace GaloisForLFunctions.BezoutValuationIncidence
set_option autoImplicit false

/-- The actual interior norm is paid from half damping onward. -/
theorem exists_pronicNorm_pmBezoutInteriorPrefix_le_of_half_le {ε : ℝ}
    (hε : 1 / 2 ≤ ε) :
    ∃ B : ℝ, ∀ T : ℕ, pronicNorm (pmBezoutInteriorPrefix ε) T ≤ B := by
  have hε0 : 0 ≤ ε := by linarith only [hε]
  obtain ⟨B, hB⟩ := (exists_pmBezoutInteriorPronicEnergy_budget_iff hε0).mpr
    (exists_pmPowerDampedDivisorDiscreteEnergy_budget_of_half_le hε)
  refine ⟨Real.sqrt B, fun T => ?_⟩
  have h := Real.sqrt_le_sqrt (hB T)
  simpa only [pronicNorm, pmBezoutInteriorPronicEnergy, pronicSeq,
    Nat.cast_mul, Nat.cast_add, Nat.cast_one] using h

/-- At half damping the smooth-power energy is exactly a shifted harmonic sum. -/
theorem sq_pronicNorm_smooth_half (T : ℕ) :
    pronicNorm (fun n : ℕ => (n : ℝ) ^ (1 / 2 : ℝ)) T ^ 2 =
      ∑ n ∈ Icc 1 T, 1 / ((n : ℝ) + 1) := by
  rw [pronicNorm, Real.sq_sqrt (sum_nonneg fun n _ => by positivity)]
  apply sum_congr rfl
  intro n hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
  rw [← Real.sqrt_eq_rpow, Real.sq_sqrt hn0.le]
  field_simp [hn0.ne']

/-- The smooth square-root sequence is not admitted at the endpoint. -/
theorem not_exists_pronicNorm_smooth_half_bound :
    ¬ ∃ B : ℝ, ∀ T : ℕ, pronicNorm (fun n : ℕ => (n : ℝ) ^ (1 / 2 : ℝ)) T ≤ B := by
  rintro ⟨B, hB⟩
  have hB0 : 0 ≤ B := (pronicNorm_nonneg _ 0).trans (hB 0)
  have hbound (T : ℕ) : (∑ n ∈ range (T + 1), 1 / ((n : ℝ) + 1)) ≤ B ^ 2 + 1 := by
    have hsq := pow_le_pow_left₀ (pronicNorm_nonneg _ T) (hB T) 2
    rw [sq_pronicNorm_smooth_half] at hsq
    have hset : range (T + 1) = insert 0 (Icc 1 T) := by
      ext n
      simp only [mem_range, mem_insert, mem_Icc]
      omega
    rw [hset, sum_insert (by simp)]
    norm_num only [Nat.cast_zero, zero_add, div_one]
    linarith only [hsq]
  obtain ⟨T, hT⟩ := (Real.tendsto_sum_range_one_div_nat_succ_atTop.eventually_ge_atTop
    (B ^ 2 + 2)).exists
  rcases T with _ | T
  · simp only [range_zero, sum_empty] at hT
    nlinarith only [hT, sq_nonneg B]
  · have h := hbound T
    linarith only [hT, h]

/-- At half damping admission still forces the smooth coefficient to vanish. -/
theorem pmPronicVaughanPacketSmoothMean_half_eq_zero_of_admitted (U V : ℕ)
    (w : Fin 5 → ℝ) (hw : pmPronicVaughanPacketAdmitted (1 / 2) U V w) :
    pmPronicVaughanPacketSmoothMean (1 / 2) U V w = 0 := by
  have hlinear := pmPronicVaughanPacketLinearMean_eq_zero_of_admitted (by norm_num) U V w hw
  obtain ⟨B, hB⟩ := hw
  obtain ⟨D, hD⟩ := exists_pronicNorm_pmBezoutInteriorPrefix_le_of_half_le
    (ε := (1 / 2 : ℝ)) le_rfl
  obtain ⟨C, hC⟩ := exists_pronicNorm_pmPronicVaughanPacket_normal_form_bound
    (ε := (1 / 2 : ℝ)) (by norm_num) (by norm_num) U V w
  simp only [hlinear, zero_mul, sub_zero, show (1 : ℝ) - 1 / 2 = 1 / 2 by ring] at hC
  let Q := pmPronicVaughanPacketSmoothMean (1 / 2) U V w
  let P := pmPronicVaughanPacket (1 / 2) U V w
  let I := pmBezoutInteriorPrefix (1 / 2)
  let r : ℕ → ℝ := fun n => P n - w 3 * I n - Q * (n : ℝ) ^ (1 / 2 : ℝ)
  change ∀ T : ℕ, pronicNorm r T ≤ C at hC
  by_contra hQ
  have hQpos : 0 < |Q| := abs_pos.mpr hQ
  apply not_exists_pronicNorm_smooth_half_bound
  refine ⟨(C + B + |w 3| * D) / |Q|, fun T => ?_⟩
  apply (le_div_iff₀ hQpos).mpr
  have hfirst : pronicNorm (fun n => P n + (-w 3) * I n) T ≤ B + |w 3| * D := by
    have h := pronicNorm_add_le P (fun n => (-w 3) * I n) T
    rw [pronicNorm_smul (-w 3) I T, abs_neg] at h
    exact h.trans (add_le_add (hB T)
      (mul_le_mul_of_nonneg_left (hD T) (abs_nonneg _)))
  have hsecond : pronicNorm (fun n => (-1 : ℝ) * r n) T ≤ C := by
    simpa only [pronicNorm_smul, abs_neg, abs_one, one_mul] using hC T
  have heq : (fun n : ℕ => Q * (n : ℝ) ^ (1 / 2 : ℝ)) =
      fun n => (-1 : ℝ) * r n + (P n + (-w 3) * I n) := by
    funext n
    dsimp only [r]
    ring
  have h := (pronicNorm_add_le (fun n => (-1 : ℝ) * r n)
    (fun n => P n + (-w 3) * I n) T).trans (add_le_add hsecond hfirst)
  rw [← heq, pronicNorm_smul] at h
  linarith only [h]

/-- The endpoint admits exactly the packets with both explicit drifts removed. -/
theorem pmPronicVaughanPacketAdmitted_half_iff (U V : ℕ) (w : Fin 5 → ℝ) :
    pmPronicVaughanPacketAdmitted (1 / 2) U V w ↔
      pmPronicVaughanPacketLinearMean (1 / 2) U V w = 0 ∧
        pmPronicVaughanPacketSmoothMean (1 / 2) U V w = 0 := by
  constructor
  · intro hw
    exact ⟨pmPronicVaughanPacketLinearMean_eq_zero_of_admitted (by norm_num) U V w hw,
      pmPronicVaughanPacketSmoothMean_half_eq_zero_of_admitted U V w hw⟩
  · rintro ⟨hlinear, hsmooth⟩
    apply (pmPronicVaughanPacketAdmitted_iff_of_two_means_zero
      (by norm_num) (by norm_num) U V w hlinear hsmooth).mpr
    exact Or.inr (exists_pronicNorm_pmBezoutInteriorPrefix_le_of_half_le le_rfl)

/-- At positive cutoffs the endpoint has two explicit linear coefficient constraints. -/
theorem pmPronicVaughanPacketAdmitted_half_iff_of_pos_cutoffs
    {U V : ℕ} (hU : 1 ≤ U) (hV : 1 ≤ V) (w : Fin 5 → ℝ) :
    pmPronicVaughanPacketAdmitted (1 / 2) U V w ↔
      pmPronicVaughanPacketLinearMean (1 / 2) U V w = 0 ∧ w 2 = w 3 := by
  rw [pmPronicVaughanPacketAdmitted_half_iff,
    pmPronicVaughanPacketSmoothMean_eq_zero_iff (by norm_num) (by norm_num) hU hV]

/-- At half damping the receiver joins the two paid directions and fills their three-dimensional span. -/
theorem pmPronicVaughanAdmittedSubmodule_half_eq_full_span
    {U V : ℕ} (hU : 1 ≤ U) (hV : 1 ≤ V) :
    pmPronicVaughanAdmittedSubmodule (1 / 2) U V =
      Submodule.span ℝ (Set.range (pmPronicVaughanFullFrame (1 / 2) U V)) := by
  apply le_antisymm
  · intro w hw
    obtain ⟨hlinear, hconv⟩ :=
      (pmPronicVaughanPacketAdmitted_half_iff_of_pos_cutoffs hU hV w).mp hw
    have heq : w = ((w 0 - w 3) • pmPronicVaughanFirstPaidCoefficients (1 / 2) U +
        (w 1 - w 3) • pmPronicVaughanSecondPaidCoefficients (1 / 2) V) +
          w 3 • (fun _ => 1) := by
      funext i
      simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_one] using
        pmPronicVaughan_coefficients_eq_paid_add_receiver (by norm_num) U V w hconv hlinear i
    rw [heq]
    exact Submodule.add_mem _
      (Submodule.add_mem _
        (Submodule.smul_mem _ _ (Submodule.subset_span ⟨(0 : Fin 3), rfl⟩))
        (Submodule.smul_mem _ _ (Submodule.subset_span ⟨(1 : Fin 3), rfl⟩)))
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨(2 : Fin 3), rfl⟩))
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · exact pmPronicVaughanPacketAdmitted_firstPaid (by norm_num) U V
    · exact pmPronicVaughanPacketAdmitted_secondPaid (by norm_num) U V
    · obtain ⟨B, hB⟩ := exists_pronicNorm_pmBezoutInteriorPrefix_le_of_half_le
        (ε := (1 / 2 : ℝ)) le_rfl
      refine ⟨B, fun T => ?_⟩
      change pronicNorm (pmPronicVaughanPacket (1 / 2) U V (fun _ => 1)) T ≤ B
      rw [show pmPronicVaughanPacket (1 / 2) U V (fun _ => 1) =
        pmBezoutInteriorPrefix (1 / 2) from funext (pmPronicVaughanPacket_one (1 / 2) U V)]
      exact hB T

/-- Positive cutoffs have admitted coefficient dimension three at half damping. -/
theorem finrank_pmPronicVaughanAdmittedSubmodule_half {U V : ℕ}
    (hU : 1 ≤ U) (hV : 1 ≤ V) :
    Module.finrank ℝ (pmPronicVaughanAdmittedSubmodule (1 / 2) U V) = 3 := by
  rw [pmPronicVaughanAdmittedSubmodule_half_eq_full_span hU hV,
    finrank_span_eq_card (pmPronicVaughanFullFrame_linearIndependent (1 / 2) U V),
    Fintype.card_fin]

/-- The endpoint quotient retains precisely the two explicit drift directions. -/
theorem finrank_pmPronicVaughanAdmittedQuotient_half {U V : ℕ}
    (hU : 1 ≤ U) (hV : 1 ≤ V) :
    Module.finrank ℝ ((Fin 5 → ℝ) ⧸ pmPronicVaughanAdmittedSubmodule (1 / 2) U V) = 2 := by
  have h := Submodule.finrank_quotient_add_finrank (pmPronicVaughanAdmittedSubmodule (1 / 2) U V)
  rw [finrank_pmPronicVaughanAdmittedSubmodule_half hU hV] at h
  have hdim : Module.finrank ℝ (Fin 5 → ℝ) = 5 := by simp
  rw [hdim] at h
  omega

#print axioms pmPronicVaughanAdmittedSubmodule_half_eq_full_span
#print axioms finrank_pmPronicVaughanAdmittedSubmodule_half
#print axioms finrank_pmPronicVaughanAdmittedQuotient_half
#print axioms pmPronicVaughanPacketSmoothMean_half_eq_zero_of_admitted
#print axioms pmPronicVaughanPacketAdmitted_half_iff
#print axioms pmPronicVaughanPacketAdmitted_half_iff_of_pos_cutoffs
#print axioms exists_pronicNorm_pmBezoutInteriorPrefix_le_of_half_le
#print axioms sq_pronicNorm_smooth_half
#print axioms not_exists_pronicNorm_smooth_half_bound
end GaloisForLFunctions.BezoutValuationIncidence
