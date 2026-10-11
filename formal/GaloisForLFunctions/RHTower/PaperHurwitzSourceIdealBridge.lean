import GaloisForLFunctions.RHTower.PaperHurwitzEnergyDomain
import GaloisForLFunctions.RHTower.PaperHurwitzWallApproach
import GaloisForLFunctions.RHTower.HardyTheorem

/-!
# Paper ideal cost expressed through literal Hurwitz source packets

At every actual Xi support point, the complete operator uses exactly the pre-existing rational
Hurwitz reflection energies. Its compactness and paper cost are equivalent to the original
finite packet mismatch/equality. This identifies the remaining HJ source requirement precisely;
no proof of that requirement or of RH is asserted.
-/

namespace RHTower

noncomputable section
open GaloisForLFunctions.HTGeometry
open scoped ENNReal

/-- The actual operator coefficient is the reciprocal of one plus the original source energy. -/
theorem paperHurwitzResolvent_actual_source_apply (rho : XiDivisorSupport)
    (f : PaperHurwitzHistory) (k : ℕ) :
    paperHurwitzResolvent (rho : ℂ) f k =
      (((1 + normalizedRationalHurwitzReflectionEnergy (2 ^ k) (rho : ℂ))⁻¹ : ℝ) : ℂ) * f k := by
  rw [paperHurwitzResolvent_apply, paperHurwitzRegularizer, paperHurwitzPowerEnergy_eq_source]

/-- Compactness detects literal two-point source-packet mismatch on each actual Xi fibre. -/
theorem paperHurwitzResolvent_actual_compact_iff_packet_ne (rho : XiDivisorSupport) :
    IsCompactOperator (paperHurwitzResolvent (rho : ℂ)) ↔
      rationalHurwitzFiberResponse 2 ((starRingEnd ℂ) (rho : ℂ)) ≠
        rationalHurwitzFiberResponse 2 (1 - (rho : ℂ)) := by
  rw [paperHurwitzResolvent_compact_iff]
  exact (not_congr (rationalHurwitzFiberResponse_reflection_fixed_iff
    (n := 2) (by norm_num) (xi_divisor_support_re_mem_open_unit rho))).symm

/-- The proven paper trace is infinite exactly when the native reflected packets agree. -/
theorem paperHurwitzResolvent_actual_traceCost_top_iff_packet_eq (rho : XiDivisorSupport) :
    compactOperatorTraceCost PaperHurwitzHistory (paperHurwitzResolvent (rho : ℂ)) = ∞ ↔
      rationalHurwitzFiberResponse 2 ((starRingEnd ℂ) (rho : ℂ)) =
        rationalHurwitzFiberResponse 2 (1 - (rho : ℂ)) := by
  rw [compactOperatorTraceCost_eq_top_iff, paperHurwitzResolvent_actual_compact_iff_packet_ne]
  exact not_not

/-- The all-fibre ideal-cost assertion is the exact existing HJ receiver, still requiring a source proof. -/
theorem riemannHypothesis_iff_paperHurwitzResolvent_traceCost_top :
    RiemannHypothesis ↔ ∀ rho : XiDivisorSupport,
      compactOperatorTraceCost PaperHurwitzHistory (paperHurwitzResolvent (rho : ℂ)) = ∞ := by
  rw [← xiRationalHurwitzFiberTwoReflectionFixed_iff_riemannHypothesis]
  change (∀ rho : XiDivisorSupport,
    rationalHurwitzFiberResponse 2 ((starRingEnd ℂ) (rho : ℂ)) =
      rationalHurwitzFiberResponse 2 (1 - (rho : ℂ))) ↔ _
  exact forall_congr' fun rho =>
    (paperHurwitzResolvent_actual_traceCost_top_iff_packet_eq rho).symm

/-- Hardy's unconditional zeros supply actual identity resolvents and infinite paper cost above
every height, without any premise about the remaining Xi divisor. -/
theorem exists_paperHurwitzResolvent_actual_identity_above (T : ℝ) :
    ∃ rho : XiDivisorSupport, T < (rho : ℂ).im ∧
      paperHurwitzResolvent (rho : ℂ) = 1 ∧
      compactOperatorTraceCost PaperHurwitzHistory (paperHurwitzResolvent (rho : ℂ)) = ∞ := by
  obtain ⟨t, ht, hXi⟩ := exists_Xi_zero_gt T
  have hzero : xi ((1 / 2 : ℂ) + (t : ℂ) * Complex.I) = 0 := by
    change XiC (t : ℂ) = 0
    rw [XiC_ofReal, hXi, Complex.ofReal_zero]
  let rho : XiDivisorSupport :=
    ⟨(1 / 2 : ℂ) + (t : ℂ) * Complex.I, mem_xi_divisor_support_of_eq_zero hzero⟩
  have hr : (rho : ℂ).re = 1 / 2 := by simp [rho]
  have hi : (rho : ℂ).im = t := by simp [rho]
  refine ⟨rho, ?_, paperHurwitzResolvent_of_wall hr, ?_⟩
  · simpa only [hi] using ht
  · rw [paperHurwitzResolvent_traceCost, if_pos hr]

/-- Requiring compactness on every actual fibre already contradicts unconditional Hardy zeros. -/
theorem not_forall_paperHurwitzResolvent_actual_compact :
    ¬ ∀ rho : XiDivisorSupport, IsCompactOperator (paperHurwitzResolvent (rho : ℂ)) := by
  intro h
  obtain ⟨rho, _, _, hc⟩ := exists_paperHurwitzResolvent_actual_identity_above 0
  have hz := (compactOperatorTraceCost_eq_zero_iff _).mpr (h rho)
  rw [hc] at hz
  exact ENNReal.top_ne_zero hz

end
end RHTower
