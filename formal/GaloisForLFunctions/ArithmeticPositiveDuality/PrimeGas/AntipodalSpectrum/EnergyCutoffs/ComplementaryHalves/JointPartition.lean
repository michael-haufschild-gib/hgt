import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum.EnergyCutoffs.ComplementaryHalves.PhysicalSpectrum
import GaloisForLFunctions.RHTower.BornSectorExchange

/-!
# The Gibbs trace on complementary balanced pairs

Taking the logarithm of each joint level produces the half-integer
Dirichlet spectrum. Its diagonal Gibbs operator factors through two
Hilbert–Schmidt propagators precisely on the physical trace half-plane.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum.ComplementaryHalves

def energyLevel (t : ExceptionalTime) (j : ℕ) (p : Pair t j) := Real.log (centeredLevel t j p)

def jointEntry (t : ExceptionalTime) (j : ℕ) (s : ℂ) (p : Pair t j) :=
  Complex.exp (-s*(energyLevel t j p:ℂ))

private def halfEntry (s : ℂ) (n : ℕ) := ((n:ℂ)+1/2)^(-s)

private theorem half_pos (n : ℕ) : 0 < (n:ℝ)+1/2 := by positivity

theorem entry_eq (t : ExceptionalTime) (j : ℕ) (s : ℂ) (p : Pair t j) :
    jointEntry t j s p = halfEntry s (pairIndex t j p) := by
  let n := pairIndex t j p
  have hcast : (n:ℂ)+1/2 = (((n:ℝ)+1/2:ℝ):ℂ) := by push_cast; rfl
  rw [jointEntry,energyLevel,centeredLevel_eq]
  change Complex.exp (-s*((Real.log ((n:ℝ)+1/2):ℝ):ℂ)) = halfEntry s n
  rw [halfEntry,hcast,Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (half_pos n).ne'),
    ← Complex.ofReal_log (half_pos n).le,mul_comm]

private theorem norm_halfEntry (s : ℂ) (n : ℕ) : ‖halfEntry s n‖ = ((n:ℝ)+1/2)^(-s.re) := by
  have hcast : (n:ℂ)+1/2 = (((n:ℝ)+1/2:ℝ):ℂ) := by push_cast; rfl
  rw [halfEntry,hcast,Complex.norm_cpow_eq_rpow_re_of_pos (half_pos n),Complex.neg_re]

/-- The extra half-unit in the ground level preserves the ordinary trace abscissa. -/
theorem absolute_iff (t : ExceptionalTime) (j : ℕ) (s : ℂ) :
    Summable (fun p => ‖jointEntry t j s p‖) ↔ 1 < s.re := by
  simp_rw [entry_eq]
  change Summable ((fun n => ‖halfEntry s n‖) ∘ (pairIndex t j)) ↔ _
  rw [(pairIndex t j).summable_iff (f := fun n => ‖halfEntry s n‖)]
  constructor
  · intro hs
    by_contra! hle
    have hh := (summable_nat_add_iff (f := fun n => ‖halfEntry s n‖) 1).mpr hs
    have hharm : Summable (fun n : ℕ => (((n+2:ℕ):ℝ))^(-(1:ℝ))) := by
      apply hh.of_nonneg_of_le (fun n => Real.rpow_nonneg (Nat.cast_nonneg _) _) (fun n => ?_)
      rw [norm_halfEntry,Nat.cast_add,Nat.cast_two,Nat.cast_add,Nat.cast_one]
      have hn := Nat.cast_nonneg (α := ℝ) n
      calc
        ((n:ℝ)+2)^(-(1:ℝ)) ≤ ((n:ℝ)+1+1/2)^(-(1:ℝ)) := by
          rw [Real.rpow_neg_one,Real.rpow_neg_one]
          exact inv_anti₀ (by linarith only [hn]) (by linarith)
        _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by linarith only [hn]) (by linarith only [hle])
    have hbad := Real.summable_nat_rpow.mp ((summable_nat_add_iff (f := fun n : ℕ => (n:ℝ)^(-(1:ℝ))) 2).mp hharm)
    exact hbad.false
  · exact fun hs => (HurwitzZetaShift.summable_hurwitzSeries hs (1/2)).norm

def partition (t : ExceptionalTime) (j : ℕ) (s : ℂ) := ∑' p : Pair t j, jointEntry t j s p

/-- Meromorphic candidate given by the odd-integer Dirichlet factor. -/
def continued (s : ℂ) := ((2:ℂ)^s-1)*riemannZeta s

theorem partition_agrees (t : ExceptionalTime) (j : ℕ) (s : {z : ℂ // 1 < z.re}) :
    partition t j s.val = continued s.val := by
  unfold partition
  simp_rw [entry_eq]
  rw [(pairIndex t j).tsum_eq (halfEntry s.val)]
  exact _root_.RHTower.hzeta_one_half s.property

private theorem half_time_square (t : ExceptionalTime) (j : ℕ) (s : ℂ) (p : Pair t j) :
    jointEntry t j (s/2) p * jointEntry t j (s/2) p = jointEntry t j s p := by
  rw [jointEntry,jointEntry,← Complex.exp_add]
  congr 1
  ring

private theorem half_time_summable (t : ExceptionalTime) (j : ℕ) (s : {z : ℂ // 1 < z.re}) :
    Summable (fun p : Pair t j => ‖jointEntry t j (s.val/2) p‖^2) := by
  apply ((absolute_iff t j s.val).mpr s.property).congr
  intro p
  rw [← half_time_square t j s.val p,norm_mul,pow_two]

abbrev PairedGas (t : ExceptionalTime) (j : ℕ) := lp (fun _ : Pair t j => ℂ) 2

def gibbs (t : ExceptionalTime) (j : ℕ) (s : {z : ℂ // 1 < z.re}) : PairedGas t j →L[ℂ] PairedGas t j :=
  let H := HilbertSchmidt.diagOp (jointEntry t j (s.val/2)) (half_time_summable t j s)
  H ∘L H

theorem gibbs_apply (t : ExceptionalTime) (j : ℕ) (s : {z : ℂ // 1 < z.re}) (f : PairedGas t j) (p : Pair t j) :
    gibbs t j s f p = jointEntry t j s.val p*f p := by
  simp only [gibbs,ContinuousLinearMap.comp_apply,HilbertSchmidt.diagOp_apply,← mul_assoc,half_time_square]

/-- The actual two-copy operator trace is the odd-integer factor times the full prime-gas trace. -/
theorem gibbs_trace (t : ExceptionalTime) (j : ℕ) (s : {z : ℂ // 1 < z.re}) :
    ContinuousLinearMap.opTrace (gibbs t j s) = ((2:ℂ)^s.val-1)*ContinuousLinearMap.opTrace (gibbsOperator s) := by
  rw [partition_eq_zeta,gibbs,HilbertSchmidt.opTrace_diagOp_comp]
  simp_rw [half_time_square]
  exact partition_agrees t j s

#print axioms absolute_iff
#print axioms partition_agrees
#print axioms gibbs_apply
#print axioms gibbs_trace

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum.ComplementaryHalves
