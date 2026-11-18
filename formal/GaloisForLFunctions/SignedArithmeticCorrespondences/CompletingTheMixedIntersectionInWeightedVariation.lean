import GaloisForLFunctions.SignedArithmeticCorrespondences.GluingIntegerGraphsAtTheirQuotientEndpoints
import GaloisForLFunctions.RHTower.QuasiRHQuotientHeadAndFiniteContactAbscissaLaw
import GaloisForLFunctions.RHTower.ChebyshevPsiErrorInputs

/-!
# Completion of the mixed finite part

Once integral endpoints at the same quotient have been combined, the prime-counting
error acts on their weighted variation. Finite truncations approach the resulting
pairing with an explicit bound on the distance.
-/

noncomputable section
namespace GaloisForLFunctions.SignedArithmeticCorrespondences
open ArithmeticCastelnuovoSeveri Finset _root_.RHTower Filter
open scoped ArithmeticFunction.vonMangoldt NNReal

/-- A sublinear error bound on every support, independent of any fixed zero-free
strip. The prime number theorem is applied after the two divisors have been glued. -/
theorem mixed_height_de_la_vallee_poussin :
    ∃ c C : ℝ, 0 < c ∧ 0 ≤ C ∧ ∀ (X N : ℕ) (u b : ℕ → ℤ),
      |signedDivisorHeight 1 X N u (upperDivisor N b) - poleProduct X N u b +
        fractionalBoundary X N u b| ≤ C * ∑ k ∈ range (N+1),
        |quotientCoefficient X N u b k| * ((k : ℝ)*Real.exp (-c*Real.sqrt (Real.log k))) := by
  obtain ⟨A,c,hc,hA,he⟩ := exists_psi_error_eventually
  obtain ⟨L,hL⟩ := eventually_atTop.mp (tendsto_natCast_atTop_atTop.eventually he)
  let W (k : ℕ) : ℝ≥0 := ⟨(k:ℝ)*Real.exp (-c*Real.sqrt (Real.log k)), by positivity⟩
  let B := ∑ k ∈ range L, |psiRemainder k| / (W k : ℝ)
  have hB : 0 ≤ B := sum_nonneg fun k _ => div_nonneg (abs_nonneg _) (W k).coe_nonneg
  have h : ∀ k : ℕ, 1 ≤ k → |psiRemainder k| ≤ (A+B)*(W k : ℝ) := by
    intro k hk
    by_cases hlarge : L ≤ k
    · have hr := hL k hlarge
      rw [psiRemainder,chebyshevPsi_eq_psi]
      exact hr.trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hB) (W k).coe_nonneg)
    · have hw : 0 < (W k : ℝ) :=
        mul_pos (Nat.cast_pos.mpr hk) (Real.exp_pos _)
      have hsmall : |psiRemainder k|/(W k : ℝ) ≤ B :=
        single_le_sum (f := fun j => |psiRemainder j|/(W j : ℝ))
          (fun j _ => div_nonneg (abs_nonneg _) (W j).coe_nonneg) (mem_range.mpr (lt_of_not_ge hlarge))
      exact ((div_le_iff₀ hw).mp hsmall).trans
        (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hA) hw.le)
  exact ⟨c,A+B,hc,add_nonneg hA hB,(mixed_height_budget_iff W ⟨A+B,add_nonneg hA hB⟩).2 h⟩

/-- One constant works for every support and both integer divisors. The variation
is measured after cancellation between all pairs sharing a quotient. -/
theorem mixed_height_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (X N : ℕ) (u b : ℕ → ℤ),
      |signedDivisorHeight 1 X N u (upperDivisor N b) - poleProduct X N u b +
        fractionalBoundary X N u b| ≤
      C * ∑ k ∈ range (N+1), |quotientCoefficient X N u b k| * (k : ℝ)^(zetaZeroAbscissa+ε) := by
  obtain ⟨C,hC,hbound⟩ := exists_psiRemainder_le_rpow_zetaZeroAbscissa ε hε
  exact ⟨C,hC,(mixed_height_budget_iff
    (fun k => ⟨_, Real.rpow_nonneg (Nat.cast_nonneg k) _⟩) ⟨C,hC⟩).2 hbound⟩

/-- A completed endpoint profile can have infinitely many signed jumps.
The same constant controls its pairing with the Chebyshev error at every
cutoff. The resulting series is absolutely convergent in weighted variation. -/
theorem completed_endpoint_budget (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a : ℕ → ℝ,
      Summable (fun k => |a k| * (k : ℝ)^(zetaZeroAbscissa+ε)) →
      Summable (fun k => a k*psiRemainder k) ∧
      |∑' k, a k*psiRemainder k| ≤ C * ∑' k, |a k| * (k : ℝ)^(zetaZeroAbscissa+ε) := by
  obtain ⟨C,hC,hbound⟩ := exists_psiRemainder_le_rpow_zetaZeroAbscissa ε hε
  refine ⟨C,hC,fun a ha => ?_⟩
  have hterm (k : ℕ) : ‖a k*psiRemainder k‖ ≤ C * (|a k| * (k : ℝ)^(zetaZeroAbscissa+ε)) := by
    rw [Real.norm_eq_abs, abs_mul, mul_left_comm]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · rw [psiRemainder, chebyshevPsi]
      simp only [Icc_eq_empty_of_lt Nat.zero_lt_one, sum_empty, Nat.cast_zero, sub_zero, abs_zero]
      exact mul_nonneg hC (Real.rpow_nonneg (by norm_num) _)
    · exact hbound _ hk
  have hmajor := ha.mul_left C
  have hsum : Summable (fun k => a k*psiRemainder k) := Summable.of_norm_bounded hmajor hterm
  refine ⟨hsum, ?_⟩
  rw [← Real.norm_eq_abs, ← tsum_mul_left]
  exact (norm_tsum_le_tsum_norm hsum.norm).trans (hsum.norm.tsum_le_tsum hterm hmajor)

/-- Distance from a finite integral intersection to a prescribed infinite
endpoint profile. The right side prices only the variation left after gluing.
This gives convergence along every exhaustion approaching the same profile
in weighted variation, with one constant for both supports. -/
theorem distance_to_completed_intersection (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (X N : ℕ) (u b : ℕ → ℤ) (a : ℕ → ℝ),
      Summable (fun k => |a k| * (k : ℝ)^(zetaZeroAbscissa+ε)) →
      let c := quotientCoefficient X N u b
      |signedDivisorHeight 1 X N u (upperDivisor N b) - poleProduct X N u b +
        fractionalBoundary X N u b - ∑' k, a k*psiRemainder k| ≤
        C * ∑' k, |c k-a k| * (k : ℝ)^(zetaZeroAbscissa+ε) := by
  obtain ⟨C,hC,hpair⟩ := completed_endpoint_budget ε hε
  refine ⟨C,hC,fun X N u b a ha => ?_⟩
  let c := quotientCoefficient X N u b
  have hc {k : ℕ} (hk : k ∉ range (N+1)) : c k = 0 :=
    quotientCoefficient_eq_zero (by simpa only [mem_range,not_lt,Nat.succ_le_iff] using hk) X u b
  have hcw : Summable (fun k => |c k| * (k : ℝ)^(zetaZeroAbscissa+ε)) :=
    summable_of_ne_finset_zero (s := range (N+1)) fun k hk => by simp [hc hk]
  have hce := (hpair c hcw).1
  have hae := (hpair a ha).1
  have hdiff : Summable (fun k => |c k-a k| * (k : ℝ)^(zetaZeroAbscissa+ε)) := by
    refine Summable.of_nonneg_of_le (fun k => mul_nonneg (abs_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)) ?_ (hcw.add ha)
    intro k
    simpa only [Pi.add_apply, ← add_mul] using
      mul_le_mul_of_nonneg_right (abs_sub (c k) (a k)) (Real.rpow_nonneg (Nat.cast_nonneg k) (zetaZeroAbscissa+ε))
  have h := (hpair (fun k => c k-a k) hdiff).2
  have he : (∑' k, c k*psiRemainder k) = ∑ k ∈ range (N+1), c k*psiRemainder k :=
    tsum_eq_sum fun k hk => by simp only [hc hk,zero_mul]
  rw [mixed_height_finite_part]
  change |(∑ k ∈ range (N+1), c k*psiRemainder k) - _| ≤ _
  rw [← he,← hce.tsum_sub hae]
  simpa only [sub_mul] using h

#print axioms mixed_height_de_la_vallee_poussin
#print axioms mixed_height_bound
#print axioms completed_endpoint_budget
#print axioms distance_to_completed_intersection

end GaloisForLFunctions.SignedArithmeticCorrespondences
