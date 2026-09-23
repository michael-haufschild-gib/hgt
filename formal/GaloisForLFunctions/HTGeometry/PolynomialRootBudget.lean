import GaloisForLFunctions.HTGeometry.OrderedPositiveMomentDetermination

/-!
# Finite polynomial recovery of nuclear root mass

The classical square-root recursion, divided by its zero at the origin, gives a fixed
sequence of finite linear moment probes. On nonnegative contractive root sequences their
traces increase to the root mass, including divergence when that mass is infinite. Each
stage is dominated by a constant times the square energy, so no infinite-rank uniform-error
interchange is used. Coefficient-weighted perturbation bounds retain degree dependence.

The scalar approximation is classical: Rudin, Principles of Mathematical Analysis,
Chapter 7, Exercise 23. No novelty is claimed for that recursion or monotone convergence.
-/

open Filter Topology
open scoped BigOperators
noncomputable section
namespace GaloisForLFunctions.HTGeometry

/-- Quotient by `X` of the classical increasing square-root approximant. -/
def rootBudgetQuotient : ℕ → Polynomial ℝ
  | 0 => 0
  | n + 1 => rootBudgetQuotient n + Polynomial.C (1 / 2) *
      (1 - Polynomial.X * rootBudgetQuotient n ^ (2 : ℕ))

/-- Polynomial response to one nonnegative root amplitude. -/
def rootBudgetResponse (n : ℕ) (a : ℝ) : ℝ :=
  a ^ (2 : ℕ) * (rootBudgetQuotient n).eval (a ^ (2 : ℕ))

@[simp] theorem rootBudgetResponse_zero (a : ℝ) : rootBudgetResponse 0 a = 0 := by
  simp [rootBudgetResponse, rootBudgetQuotient]

theorem rootBudgetResponse_succ (n : ℕ) (a : ℝ) :
    rootBudgetResponse (n + 1) a =
      rootBudgetResponse n a + (a ^ (2 : ℕ) - rootBudgetResponse n a ^ (2 : ℕ)) / 2 := by
  simp [rootBudgetResponse, rootBudgetQuotient]
  ring

theorem rootBudgetResponse_bounds {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (n : ℕ) :
    0 ≤ rootBudgetResponse n a ∧ rootBudgetResponse n a ≤ a := by
  induction n with
  | zero => simp [ha0]
  | succ n ih =>
    rw [rootBudgetResponse_succ]
    have hs : rootBudgetResponse n a ^ (2 : ℕ) ≤ a ^ (2 : ℕ) :=
      pow_le_pow_left₀ ih.1 ih.2 2
    have hp : 0 ≤ (a - rootBudgetResponse n a) *
        (1 - (a + rootBudgetResponse n a) / 2) :=
      mul_nonneg (sub_nonneg.mpr ih.2) (by linarith)
    constructor <;> nlinarith

theorem rootBudgetResponse_monotone {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    Monotone (fun n => rootBudgetResponse n a) := by
  apply monotone_nat_of_le_succ
  intro n
  rw [rootBudgetResponse_succ]
  have h := rootBudgetResponse_bounds ha0 ha1 n
  nlinarith [pow_le_pow_left₀ h.1 h.2 2]

theorem rootBudgetResponse_le_energy (n : ℕ) (a : ℝ) :
    rootBudgetResponse n a ≤ (n : ℝ) / 2 * a ^ (2 : ℕ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [rootBudgetResponse_succ]
    push_cast
    nlinarith [sq_nonneg (rootBudgetResponse n a)]

theorem rootBudgetResponse_error {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (n : ℕ) :
    a - rootBudgetResponse n a ≤ a * (1 - a / 2) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hb := rootBudgetResponse_bounds ha0 ha1 n
    have hf : 0 ≤ 1 - a / 2 := by linarith
    have hm := mul_le_mul_of_nonneg_right ih hf
    have hp := mul_nonneg (sub_nonneg.mpr hb.2) hb.1
    rw [rootBudgetResponse_succ, pow_succ (1 - a / 2) n]
    nlinarith

theorem tendsto_rootBudgetResponse {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    Tendsto (fun n => rootBudgetResponse n a) atTop (nhds a) := by
  by_cases hz : a = 0
  · subst a
    simp [rootBudgetResponse]
  have hapos : 0 < a := lt_of_le_of_ne ha0 (Ne.symm hz)
  have hgeom := (tendsto_pow_atTop_nhds_zero_of_lt_one
    (show 0 ≤ 1 - a / 2 by linarith) (show 1 - a / 2 < 1 by linarith)).const_mul a
  have hl : Tendsto (fun n : ℕ => a - a * (1 - a / 2) ^ n) atTop (nhds a) := by
    simpa using tendsto_const_nhds.sub hgeom
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hl tendsto_const_nhds
    (fun n => by linarith [rootBudgetResponse_error ha0 ha1 n])
    (fun n => (rootBudgetResponse_bounds ha0 ha1 n).2)

/-- A finite, explicit linear functional of positive energy moments. -/
def rootMomentCertificate (n : ℕ) (M : ℕ → ℝ) : ℝ :=
  ∑ r ∈ Finset.range ((rootBudgetQuotient n).natDegree + 1),
    (rootBudgetQuotient n).coeff r * M r

theorem summable_rootBudgetResponse {a : ℕ → ℝ}
    (ha : Summable (fun k => a k ^ (2 : ℕ))) (ha0 : ∀ k, 0 ≤ a k)
    (ha1 : ∀ k, a k ≤ 1) (n : ℕ) :
    Summable (fun k => rootBudgetResponse n (a k)) :=
  (ha.mul_left ((n : ℝ) / 2)).of_nonneg_of_le
    (fun k => (rootBudgetResponse_bounds (ha0 k) (ha1 k) n).1)
    (fun k => rootBudgetResponse_le_energy n (a k))

theorem rootMomentCertificate_eq_tsum {a : ℕ → ℝ}
    (ha : Summable (fun k => a k ^ (2 : ℕ))) (ha0 : ∀ k, 0 ≤ a k)
    (haa : Antitone a) (n : ℕ) :
    rootMomentCertificate n (fun r => ∑' k, (a k ^ (2 : ℕ)) ^ (r + 1)) =
      ∑' k, rootBudgetResponse n (a k) := by
  have hs (r : ℕ) : Summable (fun k =>
      (rootBudgetQuotient n).coeff r * (a k ^ (2 : ℕ)) ^ (r + 1)) :=
    (summable_pow_succ_of_nonneg_antitone ha (fun k => sq_nonneg (a k))
      (fun i j h => pow_le_pow_left₀ (ha0 j) (haa h) 2) r).mul_left _
  simp only [rootMomentCertificate, ← tsum_mul_left]
  rw [← Summable.tsum_finsetSum (fun r _ => hs r)]
  apply tsum_congr
  intro k
  rw [rootBudgetResponse, Polynomial.eval_eq_sum_range, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  rw [pow_succ]
  ring

/-- Summable roots are recovered without a rank factor or uniform-error interchange. -/
theorem tendsto_tsum_rootBudgetResponse {a : ℕ → ℝ}
    (ha : Summable a) (ha0 : ∀ k, 0 ≤ a k) (ha1 : ∀ k, a k ≤ 1) :
    Tendsto (fun n => ∑' k, rootBudgetResponse n (a k)) atTop (nhds (∑' k, a k)) := by
  apply tendsto_tsum_of_dominated_convergence ha
    (fun k => tendsto_rootBudgetResponse (ha0 k) (ha1 k))
  apply Eventually.of_forall
  intro n k
  have hb := rootBudgetResponse_bounds (ha0 k) (ha1 k) n
  simpa only [Real.norm_eq_abs, abs_of_nonneg hb.1] using hb.2

/-- Bounded polynomial responses force summability of the full root sequence. -/
theorem summable_of_rootBudgetResponse_bounded {a : ℕ → ℝ} {C : ℝ}
    (ha : Summable (fun k => a k ^ (2 : ℕ))) (ha0 : ∀ k, 0 ≤ a k)
    (ha1 : ∀ k, a k ≤ 1)
    (hC : ∀ n, (∑' k, rootBudgetResponse n (a k)) ≤ C) : Summable a := by
  apply summable_of_sum_range_le ha0
  intro K
  apply le_of_tendsto (tendsto_finsetSum (Finset.range K)
    (fun k _ => tendsto_rootBudgetResponse (ha0 k) (ha1 k)))
  exact Eventually.of_forall fun n =>
    ((summable_rootBudgetResponse ha ha0 ha1 n).sum_le_tsum _
      (fun k _ => (rootBudgetResponse_bounds (ha0 k) (ha1 k) n).1)).trans (hC n)

/-- Infinite root cost is visible as monotone divergence of finite polynomial traces. -/
theorem tendsto_rootBudgetResponse_atTop_of_not_summable {a : ℕ → ℝ}
    (ha : Summable (fun k => a k ^ (2 : ℕ))) (ha0 : ∀ k, 0 ≤ a k)
    (ha1 : ∀ k, a k ≤ 1) (hns : ¬ Summable a) :
    Tendsto (fun n => ∑' k, rootBudgetResponse n (a k)) atTop atTop := by
  have hm : Monotone (fun n => ∑' k, rootBudgetResponse n (a k)) := by
    intro n m hnm
    exact (summable_rootBudgetResponse ha ha0 ha1 n).tsum_le_tsum
      (fun k => rootBudgetResponse_monotone (ha0 k) (ha1 k) hnm)
      (summable_rootBudgetResponse ha ha0 ha1 m)
  rw [tendsto_atTop]
  intro C
  have hex : ∃ n, C ≤ ∑' k, rootBudgetResponse n (a k) := by
    by_contra hn
    push Not at hn
    exact hns (summable_of_rootBudgetResponse_bounded ha ha0 ha1 (fun n => (hn n).le))
  obtain ⟨n, hn⟩ := hex
  exact (eventually_ge_atTop n).mono fun m hnm => hn.trans (hm hnm)


/-- Exact coefficient sensitivity; no uniform-in-degree error is silently assumed. -/
theorem rootMomentCertificate_error (n : ℕ) (M T : ℕ → ℝ) :
    |rootMomentCertificate n M - rootMomentCertificate n T| ≤
      ∑ r ∈ Finset.range ((rootBudgetQuotient n).natDegree + 1),
        |(rootBudgetQuotient n).coeff r| * |M r - T r| := by
  rw [rootMomentCertificate, rootMomentCertificate, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ r ∈ Finset.range ((rootBudgetQuotient n).natDegree + 1),
        |(rootBudgetQuotient n).coeff r * M r -
          (rootBudgetQuotient n).coeff r * T r| := Finset.abs_sum_le_sum_abs _ _
    _ = _ := Finset.sum_congr rfl fun r _ => by rw [← mul_sub, abs_mul]

/-- A root-budget ceiling imposes an explicit finite moment/error inequality. -/
theorem rootMomentCertificate_le_rootBudget_add_error {a : ℕ → ℝ}
    (ha : Summable a) (ha0 : ∀ k, 0 ≤ a k) (ha1 : ∀ k, a k ≤ 1)
    (haa : Antitone a) (n : ℕ) (M : ℕ → ℝ) :
    rootMomentCertificate n M ≤ (∑' k, a k) +
      ∑ r ∈ Finset.range ((rootBudgetQuotient n).natDegree + 1),
        |(rootBudgetQuotient n).coeff r| *
          |M r - ∑' k, (a k ^ (2 : ℕ)) ^ (r + 1)| := by
  have hasq : Summable (fun k => a k ^ (2 : ℕ)) := by
    simpa using summable_pow_succ_of_nonneg_antitone ha ha0 haa 1
  have he := rootMomentCertificate_error n M (fun r => ∑' k, (a k ^ (2 : ℕ)) ^ (r + 1))
  have hb : rootMomentCertificate n (fun r => ∑' k, (a k ^ (2 : ℕ)) ^ (r + 1)) ≤ ∑' k, a k := by
    rw [rootMomentCertificate_eq_tsum hasq ha0 haa]
    exact (summable_rootBudgetResponse hasq ha0 ha1 n).tsum_le_tsum
      (fun k => (rootBudgetResponse_bounds (ha0 k) (ha1 k) n).2) ha
  have hd := le_abs_self (rootMomentCertificate n M -
    rootMomentCertificate n (fun r => ∑' k, (a k ^ (2 : ℕ)) ^ (r + 1)))
  linarith

/-- Root summability is exactly boundedness of these fixed finite-moment probes. -/
theorem rootMomentCertificate_bounded_iff_summable {a : ℕ → ℝ}
    (ha : Summable (fun k => a k ^ (2 : ℕ))) (ha0 : ∀ k, 0 ≤ a k)
    (ha1 : ∀ k, a k ≤ 1) (haa : Antitone a) :
    (∃ C : ℝ, ∀ n, rootMomentCertificate n
      (fun r => ∑' k, (a k ^ (2 : ℕ)) ^ (r + 1)) ≤ C) ↔ Summable a := by
  simp_rw [rootMomentCertificate_eq_tsum ha ha0 haa]
  constructor
  · rintro ⟨C, hC⟩
    exact summable_of_rootBudgetResponse_bounded ha ha0 ha1 hC
  · intro hs
    refine ⟨∑' k, a k, fun n => ?_⟩
    exact (summable_rootBudgetResponse ha ha0 ha1 n).tsum_le_tsum
      (fun k => (rootBudgetResponse_bounds (ha0 k) (ha1 k) n).2) hs


/-- Uniform scalar error, used only on a finite spectral prefix. -/
theorem rootBudgetResponse_uniform_error {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (n : ℕ) : a - rootBudgetResponse n a ≤ 2 / ((n : ℝ) + 2) := by
  induction n with
  | zero => simpa using ha1
  | succ n ih =>
    have hb := rootBudgetResponse_bounds ha0 ha1 n
    have he0 : 0 ≤ a - rootBudgetResponse n a := sub_nonneg.mpr hb.2
    have he1 : a - rootBudgetResponse n a ≤ 1 := by linarith
    have hd : 0 < (n : ℝ) + 2 := by positivity
    have hd' : 0 < (n : ℝ) + 3 := by positivity
    have hu : 2 / ((n : ℝ) + 2) ≤ 1 := (div_le_one hd).2 (by linarith [Nat.cast_nonneg (α := ℝ) n])
    have hp := mul_nonneg (sub_nonneg.mpr ih)
      (show 0 ≤ 1 - (2 / ((n : ℝ) + 2) + (a - rootBudgetResponse n a)) / 2 by linarith)
    have hrec : 2 / ((n : ℝ) + 2) - (2 / ((n : ℝ) + 2)) ^ (2 : ℕ) / 2 ≤
        2 / ((n : ℝ) + 3) := by
      field_simp
      nlinarith [sq_nonneg (n : ℝ)]
    rw [rootBudgetResponse_succ]
    push_cast
    rw [show (n : ℝ) + 1 + 2 = (n : ℝ) + 3 by ring]
    nlinarith [mul_nonneg he0 hb.1]

/-- Prefix resolution costs at most two divided by the iteration depth per retained root. -/
theorem finite_rootPrefix_le_certificate_add_resolution {a : ℕ → ℝ}
    (ha : Summable (fun k => a k ^ (2 : ℕ))) (ha0 : ∀ k, 0 ≤ a k)
    (ha1 : ∀ k, a k ≤ 1) (haa : Antitone a) (n K : ℕ) :
    (∑ k ∈ Finset.range K, a k) ≤
      rootMomentCertificate n (fun r => ∑' k, (a k ^ (2 : ℕ)) ^ (r + 1)) +
        2 * (K : ℝ) / ((n : ℝ) + 2) := by
  rw [rootMomentCertificate_eq_tsum ha ha0 haa]
  have he : (∑ k ∈ Finset.range K, (a k - rootBudgetResponse n (a k))) ≤
      ∑ _k ∈ Finset.range K, 2 / ((n : ℝ) + 2) :=
    Finset.sum_le_sum fun k _ => rootBudgetResponse_uniform_error (ha0 k) (ha1 k) n
  rw [Finset.sum_sub_distrib] at he
  have hb := (summable_rootBudgetResponse ha ha0 ha1 n).sum_le_tsum (Finset.range K)
    (fun k _ => (rootBudgetResponse_bounds (ha0 k) (ha1 k) n).1)
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at he
  rw [show (K : ℝ) * (2 / ((n : ℝ) + 2)) = 2 * (K : ℝ) / ((n : ℝ) + 2) by ring] at he
  linarith

/-- The unresolved tail is charged at square-energy rate, not by its infinite rank. -/
theorem certificate_le_rootPrefix_add_energyTail {a : ℕ → ℝ}
    (ha : Summable (fun k => a k ^ (2 : ℕ))) (ha0 : ∀ k, 0 ≤ a k)
    (ha1 : ∀ k, a k ≤ 1) (haa : Antitone a) (n K : ℕ) :
    rootMomentCertificate n (fun r => ∑' k, (a k ^ (2 : ℕ)) ^ (r + 1)) ≤
      (∑ k ∈ Finset.range K, a k) +
        (n : ℝ) / 2 * ∑' k, a (k + K) ^ (2 : ℕ) := by
  have hs := summable_rootBudgetResponse ha ha0 ha1 n
  have hat : Summable (fun k => a (k + K) ^ (2 : ℕ)) := ha.comp_injective (fun _ _ h => by omega)
  have hst : Summable (fun k => rootBudgetResponse n (a (k + K))) :=
    hs.comp_injective (fun _ _ h => by omega)
  rw [rootMomentCertificate_eq_tsum ha ha0 haa, ← hs.sum_add_tsum_nat_add K]
  apply add_le_add
  · exact Finset.sum_le_sum fun k _ => (rootBudgetResponse_bounds (ha0 k) (ha1 k) n).2
  · rw [← tsum_mul_left]
    exact hst.tsum_le_tsum (fun k => rootBudgetResponse_le_energy n (a (k + K)))
      (hat.mul_left _)

end GaloisForLFunctions.HTGeometry


