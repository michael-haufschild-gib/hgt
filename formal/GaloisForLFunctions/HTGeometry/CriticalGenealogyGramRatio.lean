import GaloisForLFunctions.HTGeometry.CriticalCertificatePerturbation
import GaloisForLFunctions.HTGeometry.ScalarCertificateFredholmRecovery

/-! # Exact growth threshold for critical-relative genealogy determinants

The positive transfer system and its discrete Wronskian give two-sided energy
bounds. The literal critical-relative Gram quotient has a finite limit exactly
for Hilbert--Schmidt input weights; otherwise it diverges to positive infinity.
-/

namespace GaloisForLFunctions.HTGeometry
noncomputable section
open _root_.ContinuousLinearMap Filter Topology

private abbrev gramValue (a : CertStream) (N : ℕ) :=
  finiteGenealogyGramValue (fun n => (a.c n : ℂ)) N

private abbrev baseValue (N : ℕ) := gramValue CertStream.stationaryCritical N

private abbrev perturbedValue (a : CertStream) (N : ℕ) :=
  gramValue (criticalCertificatePerturbation a) N

def criticalGenealogyGramRatio (a : CertStream) (N : ℕ) : ℝ :=
  perturbedValue a N / baseValue N

@[simp] theorem criticalGenealogyGramRatio_zero (a : CertStream) :
    criticalGenealogyGramRatio a 0 = 1 := by simp [criticalGenealogyGramRatio]

@[simp] theorem criticalGenealogyGramRatio_one (a : CertStream) :
    criticalGenealogyGramRatio a 1 = 1 := by norm_num [criticalGenealogyGramRatio]

theorem criticalGenealogyGramRatio_eq_actual (a : CertStream) (N : ℕ) :
    (criticalGenealogyGramRatio a N : ℂ) =
      scalarCertificateGramDet (criticalCertificatePerturbation a) N /
        scalarCertificateGramDet CertStream.stationaryCritical N := by
  simp only [criticalGenealogyGramRatio, scalarCertificateGramDet_eq, Complex.ofReal_div]

private theorem base_recurrence (N : ℕ) :
    baseValue (N + 2) = 3 * baseValue (N + 1) - baseValue N := by
  dsimp only [baseValue, gramValue]
  rw [finiteGenealogyGramValue_succ_succ]
  norm_num [CertStream.stationaryCritical]
  ring

private theorem perturbed_recurrence (a : CertStream) (N : ℕ) :
    perturbedValue a (N + 2) = 2 * perturbedValue a (N + 1) +
      (1 + a.c N ^ 2) * (perturbedValue a (N + 1) - perturbedValue a N) := by
  dsimp only [perturbedValue, gramValue]
  rw [finiteGenealogyGramValue_succ_succ, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos ((criticalCertificatePerturbation a).pos N), criticalCertificatePerturbation_sq]

private theorem wronskian_step (a : CertStream) (N : ℕ) :
    perturbedValue a (N + 2) * baseValue (N + 1) -
      perturbedValue a (N + 1) * baseValue (N + 2) =
    perturbedValue a (N + 1) * baseValue N - perturbedValue a N * baseValue (N + 1) +
      a.c N ^ 2 * (perturbedValue a (N + 1) - perturbedValue a N) * baseValue (N + 1) := by
  rw [perturbed_recurrence, base_recurrence]
  ring

private theorem wronskian_nonneg (a : CertStream) (N : ℕ) :
    0 ≤ perturbedValue a (N + 1) * baseValue N - perturbedValue a N * baseValue (N + 1) := by
  induction N with
  | zero => norm_num
  | succ N ih =>
      rw [wronskian_step]
      exact add_nonneg ih (mul_nonneg
        (mul_nonneg (sq_nonneg _) (finiteGenealogyGramValue_increment_pos _ _).le)
        (finiteGenealogyGramValue_pos _ _).le)

theorem criticalGenealogyGramRatio_monotone (a : CertStream) :
    Monotone (criticalGenealogyGramRatio a) := by
  apply monotone_nat_of_le_succ
  intro N
  apply (div_le_div_iff₀ (finiteGenealogyGramValue_pos _ N)
    (finiteGenealogyGramValue_pos _ (N + 1))).mpr
  linarith [wronskian_nonneg a N]

theorem one_le_criticalGenealogyGramRatio (a : CertStream) (N : ℕ) :
    1 ≤ criticalGenealogyGramRatio a N := by
  simpa only [criticalGenealogyGramRatio_zero] using criticalGenealogyGramRatio_monotone a (Nat.zero_le N)

private theorem base_le_perturbed (a : CertStream) (N : ℕ) : baseValue N ≤ perturbedValue a N := by
  have h := one_le_criticalGenealogyGramRatio a N
  exact (one_le_div (finiteGenealogyGramValue_pos _ N)).mp h

theorem criticalGenealogyGramRatio_increment_lower (a : CertStream) (N : ℕ) :
    a.c N ^ 2 / 6 ≤ criticalGenealogyGramRatio a (N + 2) - criticalGenealogyGramRatio a (N + 1) := by
  have hb1 : 0 < baseValue (N + 1) := finiteGenealogyGramValue_pos _ _
  have hb2 : 0 < baseValue (N + 2) := finiteGenealogyGramValue_pos _ _
  have hbase : baseValue (N + 2) ≤ 3 * baseValue (N + 1) := by
    rw [base_recurrence]
    linarith [finiteGenealogyGramValue_pos (fun n => (CertStream.stationaryCritical.c n : ℂ)) N]
  have hinc : baseValue (N + 2) ≤ 6 * (perturbedValue a (N + 1) - perturbedValue a N) := by
    have hd := finiteGenealogyGramValue_two_mul_le_succ
      (fun n => ((criticalCertificatePerturbation a).c n : ℂ)) N
    linarith [base_le_perturbed a (N + 1)]
  have hr := mul_le_mul_of_nonneg_left hinc (sq_nonneg (a.c N))
  have hrB := mul_le_mul_of_nonneg_right hr hb1.le
  have hW := wronskian_nonneg a N
  have he := wronskian_step a N
  rw [criticalGenealogyGramRatio, criticalGenealogyGramRatio,
    div_sub_div _ _ hb2.ne' hb1.ne']
  apply (le_div_iff₀ (mul_pos hb2 hb1)).mpr
  nlinarith

theorem criticalGenealogyGramRatio_energy_lower (a : CertStream) (N : ℕ) :
    1 + (∑ n ∈ Finset.range N, a.c n ^ 2) / 6 ≤ criticalGenealogyGramRatio a (N + 1) := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ]
      linarith [criticalGenealogyGramRatio_increment_lower a N]

private theorem positive_transfer_bound (a : CertStream) (N : ℕ) :
    perturbedValue a (N + 1) ≤ baseValue (N + 1) * ∏ n ∈ Finset.range N, (1 + a.c n ^ 2) ∧
    perturbedValue a (N + 1) - perturbedValue a N ≤
      (baseValue (N + 1) - baseValue N) * ∏ n ∈ Finset.range N, (1 + a.c n ^ 2) := by
  induction N with
  | zero => norm_num
  | succ N ih =>
      let M := ∏ n ∈ Finset.range N, (1 + a.c n ^ 2)
      have hM : 0 ≤ M := Finset.prod_nonneg fun n _ => by positivity
      have hr : 0 ≤ 1 + a.c N ^ 2 := by positivity
      have hinc := mul_le_mul_of_nonneg_left ih.2 hr
      have hD := mul_le_mul_of_nonneg_left ih.1 (show (0 : ℝ) ≤ 2 by norm_num)
      have hgain := mul_nonneg (sq_nonneg (a.c N))
        (mul_nonneg (finiteGenealogyGramValue_pos
          (fun n => (CertStream.stationaryCritical.c n : ℂ)) (N + 1)).le hM)
      change perturbedValue a (N + 2) ≤ baseValue (N + 2) *
          ∏ n ∈ Finset.range (N + 1), (1 + a.c n ^ 2) ∧
        perturbedValue a (N + 2) - perturbedValue a (N + 1) ≤
          (baseValue (N + 2) - baseValue (N + 1)) *
            ∏ n ∈ Finset.range (N + 1), (1 + a.c n ^ 2)
      rw [perturbed_recurrence, base_recurrence, Finset.prod_range_succ]
      change _ ≤ (3 * baseValue (N + 1) - baseValue N) * (M * (1 + a.c N ^ 2)) ∧
        _ ≤ (3 * baseValue (N + 1) - baseValue N - baseValue (N + 1)) * (M * (1 + a.c N ^ 2))
      constructor <;> nlinarith [ih.1]

theorem criticalGenealogyGramRatio_energy_upper (a : CertStream) (N : ℕ) :
    criticalGenealogyGramRatio a (N + 1) ≤ Real.exp (∑ n ∈ Finset.range N, a.c n ^ 2) := by
  apply le_trans ?_ (Real.prod_one_add_le_exp_sum (Finset.range N) (fun n => sq_nonneg (a.c n)))
  apply (div_le_iff₀ (finiteGenealogyGramValue_pos _ _)).mpr
  simpa only [mul_comm] using (positive_transfer_bound a N).1

theorem criticalGenealogyGramRatio_bddAbove_iff (a : CertStream) :
    BddAbove (Set.range (criticalGenealogyGramRatio a)) ↔ IsHilbertSchmidt a.weight := by
  rw [scalarCertificate_weight_isHilbertSchmidt_iff]
  constructor
  · rintro ⟨B, hB⟩
    apply summable_of_sum_range_le (c := 6 * (B - 1)) (fun n => sq_nonneg (a.c n))
    intro N
    have hl := criticalGenealogyGramRatio_energy_lower a N
    have hu := hB (Set.mem_range_self (N + 1))
    linarith
  · intro hs
    refine ⟨Real.exp (∑' n, a.c n ^ 2), ?_⟩
    rintro _ ⟨N, rfl⟩
    cases N with
    | zero =>
        rw [criticalGenealogyGramRatio_zero]
        exact Real.one_le_exp (tsum_nonneg fun n => sq_nonneg _)
    | succ N =>
        exact (criticalGenealogyGramRatio_energy_upper a N).trans (Real.exp_le_exp.mpr
          (hs.sum_le_tsum (Finset.range N) (fun n _ => sq_nonneg _)))

theorem criticalGenealogyGramRatio_finite_limit_iff (a : CertStream) :
    (∃ L : ℝ, 1 ≤ L ∧ Tendsto (criticalGenealogyGramRatio a) atTop (𝓝 L)) ↔
      IsHilbertSchmidt a.weight := by
  constructor
  · rintro ⟨L, _, hL⟩
    exact (criticalGenealogyGramRatio_bddAbove_iff a).mp hL.bddAbove_range
  · intro ha
    have hb := (criticalGenealogyGramRatio_bddAbove_iff a).mpr ha
    refine ⟨⨆ N, criticalGenealogyGramRatio a N, ?_,
      tendsto_atTop_ciSup (criticalGenealogyGramRatio_monotone a) hb⟩
    simpa only [criticalGenealogyGramRatio_zero] using le_ciSup hb 0

theorem criticalGenealogyGramRatio_tendsto_atTop_iff (a : CertStream) :
    Tendsto (criticalGenealogyGramRatio a) atTop atTop ↔ ¬ IsHilbertSchmidt a.weight := by
  constructor
  · intro hi ha
    obtain ⟨L, _, hL⟩ := (criticalGenealogyGramRatio_finite_limit_iff a).mpr ha
    exact not_tendsto_nhds_of_tendsto_atTop hi L hL
  · intro ha
    apply tendsto_atTop_atTop_of_monotone' (criticalGenealogyGramRatio_monotone a)
    exact fun hb => ha ((criticalGenealogyGramRatio_bddAbove_iff a).mp hb)

end
end GaloisForLFunctions.HTGeometry
