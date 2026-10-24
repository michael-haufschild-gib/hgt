import GaloisForLFunctions.ArithmeticDefectRigidity.ThePoleTraceDefinesALinearCofactorRenormalization

/-!
# Fixed cofactors preserve the trace domain and have harmonic boundary weights

Finite Mellin-cell blocks telescope. Applied to absolute values, this proves that every fixed
floor dilation preserves the absolute trace domain; no second summability premise is needed.
The existing Mellin dilation identity then gives its trace. At the cofactor pole, damping and
trace exponents sum to one, so each weighted cofactor contributes exactly `1/j` of the trace.
-/

open Finset Filter Topology RHTower
open GaloisForLFunctions.TransHorizonIncidenceMechanics
  (mellinCell mellinCell_nonneg sum_range_mellinCell tsum_comp_div_mul_mellinCell)

noncomputable section
set_option autoImplicit false

namespace GaloisForLFunctions.ArithmeticDefectRigidity

private theorem sum_mellin_dilation_blocks (σ : ℝ) (f : ℕ → ℝ) (hf0 : f 0 = 0)
    (j : ℕ+) (T : ℕ) :
    (∑ n ∈ range (T * j), f (n / j) * mellinCell σ n) =
      (j : ℝ) ^ (-σ) * ∑ m ∈ range T, f m * mellinCell σ m := by
  induction T with
  | zero => simp
  | succ T ih =>
    rw [Nat.succ_eq_add_one, add_mul, one_mul, Finset.sum_range_add, ih,
      Finset.sum_range_succ, mul_add]
    congr 1
    have hdiv : ∀ r ∈ range (j : ℕ),
        f ((T * j + r) / j) * mellinCell σ (T * j + r) =
          f T * mellinCell σ (T * j + r) := by
      intro r hr
      rw [show (T * j + r) / j = T by
        rw [Nat.add_comm, Nat.add_mul_div_right _ _ j.property,
          Nat.div_eq_of_lt (mem_range.mp hr), zero_add]]
    rw [sum_congr rfl hdiv, ← mul_sum, sum_range_mellinCell]
    rcases Nat.eq_zero_or_pos T with rfl | hT
    · simp only [hf0, zero_mul]
    · rw [mellinCell]
      push_cast
      rw [show (T : ℝ) * j + j = ((T : ℝ) + 1) * j by ring,
        Real.mul_rpow (Nat.cast_nonneg T) (by positivity),
        Real.mul_rpow (by positivity) (by positivity)]
      ring

private theorem abs_mul_poleCell (ε : SubcriticalDamping) (v : poleTraceDomain ε) (n : ℕ) :
    |v n * mellinCell (1 - (ε : ℝ)) n| = |v n| * mellinCell (1 - (ε : ℝ)) n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [v.property.1, zero_mul, abs_zero, zero_mul]
  · rw [abs_mul, abs_of_nonneg (mellinCell_nonneg (by linarith [ε.property.2]) hn)]

/-- Every fixed floor dilation preserves absolute trace summability. -/
theorem summable_dilated_poleTrace (ε : SubcriticalDamping) (v : poleTraceDomain ε)
    (j : ℕ+) :
    Summable (fun n => v (n / j) * mellinCell (1 - (ε : ℝ)) n) := by
  have hα : 0 < 1 - (ε : ℝ) := by linarith [ε.property.2]
  have habs : Summable (fun n => |v n| * mellinCell (1 - (ε : ℝ)) n) :=
    v.property.2.abs.congr (abs_mul_poleCell ε v)
  have hnonneg : ∀ n, 0 ≤ |v n| * mellinCell (1 - (ε : ℝ)) n := by
    intro n
    rw [← abs_mul_poleCell ε v]
    exact abs_nonneg _
  have hdn : ∀ n, 0 ≤ |v (n / j)| * mellinCell (1 - (ε : ℝ)) n := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp only [Nat.zero_div, v.property.1, abs_zero, zero_mul, le_refl]
    · exact mul_nonneg (abs_nonneg _) (mellinCell_nonneg hα hn)
  have heq : ∀ n, |v (n / j) * mellinCell (1 - (ε : ℝ)) n| =
      |v (n / j)| * mellinCell (1 - (ε : ℝ)) n := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp only [Nat.zero_div, v.property.1, zero_mul, abs_zero]
    · rw [abs_mul, abs_of_nonneg (mellinCell_nonneg hα hn)]
  apply Summable.of_abs
  refine summable_of_sum_range_le
    (c := (j : ℝ) ^ (-(1 - (ε : ℝ))) *
      ∑' n, |v n| * mellinCell (1 - (ε : ℝ)) n) (fun n => abs_nonneg _) fun N => ?_
  simp_rw [heq]
  calc
    _ ≤ ∑ n ∈ range (N * j), |v (n / j)| * mellinCell (1 - (ε : ℝ)) n :=
      sum_le_sum_of_subset_of_nonneg
        (range_mono (Nat.le_mul_of_pos_right N j.property)) (fun n _ _ => hdn n)
    _ = (j : ℝ) ^ (-(1 - (ε : ℝ))) *
        ∑ n ∈ range N, |v n| * mellinCell (1 - (ε : ℝ)) n :=
      sum_mellin_dilation_blocks _ (fun n => |v n|) (by rw [v.property.1, abs_zero]) j N
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (habs.sum_le_tsum _ (fun n _ => hnonneg n)) (Real.rpow_nonneg (by positivity) _)

/-- A fixed floor dilation is an endomorphism of the absolute pole-trace domain. -/
def traceDilation (ε : SubcriticalDamping) (j : ℕ+) : poleTraceDomain ε →ₗ[ℝ] poleTraceDomain ε where
  toFun v := ⟨fun n => v (n / j), by simpa only [Nat.zero_div] using v.property.1,
    summable_dilated_poleTrace ε v j⟩
  map_add' := by intro v w; apply Subtype.ext; funext n; rfl
  map_smul' := by intro c v; apply Subtype.ext; funext n; rfl

/-- The absolute Mellin-cell mass of a row in the pole-trace domain. -/
def absolutePoleMass (ε : SubcriticalDamping) (v : poleTraceDomain ε) : ℝ :=
  ∑' n, |v n * mellinCell (1 - (ε : ℝ)) n|

/-- Fixed dilation has an exact absolute norm cost, not merely a signed trace identity. -/
theorem absolutePoleMass_traceDilation (ε : SubcriticalDamping) (j : ℕ+)
    (v : poleTraceDomain ε) :
    absolutePoleMass ε (traceDilation ε j v) =
      (j : ℝ) ^ (-(1 - (ε : ℝ))) * absolutePoleMass ε v := by
  have hs : Summable (fun n => |v n| * mellinCell (1 - (ε : ℝ)) n) :=
    v.property.2.abs.congr (abs_mul_poleCell ε v)
  have hsj : Summable (fun n => |v (n / j)| * mellinCell (1 - (ε : ℝ)) n) :=
    (traceDilation ε j v).property.2.abs.congr (abs_mul_poleCell ε (traceDilation ε j v))
  have h := tsum_comp_div_mul_mellinCell
    (show |v 0| = 0 by rw [v.property.1, abs_zero]) j.property hs hsj
  unfold absolutePoleMass
  simp_rw [abs_mul_poleCell]
  exact h

/-- The Mellin dilation law now applies on a proved invariant domain. -/
theorem poleTrace_traceDilation (ε : SubcriticalDamping) (j : ℕ+) (v : poleTraceDomain ε) :
    poleTrace ε (traceDilation ε j v) = (j : ℝ) ^ (-(1 - (ε : ℝ))) * poleTrace ε v := by
  change (∑' n, v (n / j) * mellinCell (1 - (ε : ℝ)) n) / (1 - (ε : ℝ)) =
    (j : ℝ) ^ (-(1 - (ε : ℝ))) *
      ((∑' n, v n * mellinCell (1 - (ε : ℝ)) n) / (1 - (ε : ℝ)))
  rw [tsum_comp_div_mul_mellinCell v.property.1 j.property v.property.2
    (summable_dilated_poleTrace ε v j)]
  ring

/-- At the cofactor pole, a damped cofactor has exactly the harmonic trace weight `1/j`. -/
theorem poleTrace_weighted_dilation (ε : SubcriticalDamping) (j : ℕ+) (v : poleTraceDomain ε) :
    poleTrace ε ((j : ℝ) ^ (-(ε : ℝ)) • traceDilation ε j v) = (1 / (j : ℝ)) * poleTrace ε v := by
  rw [map_smul, poleTrace_traceDilation]
  change (j : ℝ) ^ (-(ε : ℝ)) * ((j : ℝ) ^ (-(1 - (ε : ℝ))) * poleTrace ε v) = _
  rw [← mul_assoc, ← Real.rpow_add (by positivity),
    show -(ε : ℝ) + -(1 - (ε : ℝ)) = -1 by ring, Real.rpow_neg_one, one_div]

/-- A finite cofactor packet acts within the absolute trace domain. -/
def traceCofactorPacket (ε : SubcriticalDamping) (S : Finset ℕ+) (v : poleTraceDomain ε) :
    poleTraceDomain ε := ∑ j ∈ S, (j : ℝ) ^ (-(ε : ℝ)) • traceDilation ε j v

/-- Every finite packet has an exact harmonic boundary budget. -/
theorem poleTrace_traceCofactorPacket (ε : SubcriticalDamping) (S : Finset ℕ+)
    (v : poleTraceDomain ε) :
    poleTrace ε (traceCofactorPacket ε S v) = (∑ j ∈ S, 1 / (j : ℝ)) * poleTrace ε v := by
  simp only [traceCofactorPacket, map_sum, poleTrace_weighted_dilation, sum_mul]

/-- The actual arithmetic trace fixes the value of every finite cofactor packet. -/
theorem actual_traceCofactorPacket (ε : SubcriticalDamping) (S : Finset ℕ+) :
    poleTrace ε (traceCofactorPacket ε S (actualTraceVector ε)) =
      (∑ j ∈ S, 1 / (j : ℝ)) * forcingPowerCoefficient ε := by
  rw [poleTrace_traceCofactorPacket, poleTrace_actualTraceVector]

end GaloisForLFunctions.ArithmeticDefectRigidity
