import GaloisForLFunctions.ArithmeticOrientationTheory.TheCalculusOfTheObstructionHull

/-!
# Paid source perturbations preserve repairing ideals

Critical Wiener convolution preserves every paid source. Adding such a source therefore
does not change any repairing kernel. The critical Wiener prefix estimate supplies payment
for the perturbations needed when isolating a geometric tower.
-/

noncomputable section
open GaloisForLFunctions
open BezoutValuationIncidence TransHorizonIncidenceMechanics ArithmeticOrientationTheory
open WienerAlgebraAt

namespace GaloisForLFunctions.BiarithmeticGeometry

/-- A critical Wiener source has a uniformly bounded receiver. -/
theorem receiverBounded_of_criticalWiener (d : ℕ → ℝ) (hd : CriticalWiener d) :
    ReceiverBounded d := by
  refine ⟨((Real.sqrt 2 + 1) * ∑' n : ℕ, |d n| * (n : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2,
    fun T => ?_⟩
  rw [weightPronicEnergy_eq_sq_pronicNorm]
  exact pow_le_pow_left₀ (pronicNorm_nonneg _ T)
    (pronicNorm_weightCenteredPrefix_le_critical hd T) 2

/-- Every kernel repairs a paid source, including its two complex components. -/
theorem mem_paidIdeal_of_receiverBounded (d : ℕ → ℝ)
    (hd : Summable fun n : ℕ => |d n / n|) (hpaid : ReceiverBounded d)
    (k : WienerAlgebraAt (1 / 2)) : k ∈ paidIdeal d hd :=
  ⟨receiverBounded_dirichletConv (criticalWiener_rePart k) hd hpaid,
    receiverBounded_dirichletConv (criticalWiener_imPart k) hd hpaid⟩

/-- Adding a paid source preserves the complete repairing ideal. -/
theorem paidIdeal_add_paid (c d : ℕ → ℝ)
    (hc : Summable fun n : ℕ => |c n / n|)
    (hd : Summable fun n : ℕ => |d n / n|) (hpaid : ReceiverBounded d) :
    paidIdeal (fun n => c n + d n) (summable_abs_add_div hc hd) = paidIdeal c hc := by
  apply le_antisymm
  · intro k hk
    have hdmem := mem_paidIdeal_of_receiverBounded d hd hpaid k
    have hneg : k ∈ paidIdeal (fun n => -1 * d n) (summable_abs_smul_div hd (-1)) := by
      rw [paidIdeal_smul hd (by norm_num : (-1 : ℝ) ≠ 0)]
      exact hdmem
    have h := paidIdeal_inf_le_add (summable_abs_add_div hc hd)
      (summable_abs_smul_div hd (-1)) ⟨hk, hneg⟩
    exact (mem_paidIdeal_congr (funext fun n => by ring) _ hc k).mp h
  · intro k hk
    exact paidIdeal_inf_le_add hc hd ⟨hk, mem_paidIdeal_of_receiverBounded d hd hpaid k⟩

/-- A critical Wiener perturbation leaves the actual ideal unchanged. -/
theorem paidIdeal_add_criticalWiener (c d : ℕ → ℝ)
    (hc : Summable fun n : ℕ => |c n / n|) (hd : CriticalWiener d) :
    paidIdeal (fun n => c n + d n) (summable_abs_add_div hc hd.summable_abs_div) =
      paidIdeal c hc :=
  paidIdeal_add_paid c d hc hd.summable_abs_div (receiverBounded_of_criticalWiener d hd)

/-- Isolating a nonzero leading source preserves every repair and every obstruction. -/
theorem paidIdeal_smul_add_criticalWiener (c d : ℕ → ℝ)
    (hc : Summable fun n : ℕ => |c n / n|) (hd : CriticalWiener d)
    (t : ℝ) (ht : t ≠ 0) :
    paidIdeal (fun n => t * c n + d n)
      (summable_abs_add_div (summable_abs_smul_div hc t) hd.summable_abs_div) =
      paidIdeal c hc := by
  rw [paidIdeal_add_criticalWiener _ _ (summable_abs_smul_div hc t) hd, paidIdeal_smul hc ht]

end GaloisForLFunctions.BiarithmeticGeometry
